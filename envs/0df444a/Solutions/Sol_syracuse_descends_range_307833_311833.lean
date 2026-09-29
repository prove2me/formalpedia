-- Prove2me | solution 1 for syracuse_descends_range_307833_311833
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:44:22.111099+00:00
-- url     : https://prove2.me/submissions/32356fb7-33e5-4155-bc8b-db397ba180dd

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


theorem B589837 : Blo 307833 589837 := bbase (se 3 (by rfl) ⟨110594, by rfl⟩ : syracuseStep 589837 = 221189) (by norm_num)
theorem B786469 : Blo 307833 786469 := bbase (se 4 (by rfl) ⟨73731, by rfl⟩ : syracuseStep 786469 = 147463) (by norm_num)
theorem B524333 : Blo 307833 524333 := bbase (se 3 (by rfl) ⟨98312, by rfl⟩ : syracuseStep 524333 = 196625) (by norm_num)
theorem B393265 : Blo 307833 393265 := bbase (se 2 (by rfl) ⟨147474, by rfl⟩ : syracuseStep 393265 = 294949) (by norm_num)
theorem B786581 : Blo 307833 786581 := bbase (se 6 (by rfl) ⟨18435, by rfl⟩ : syracuseStep 786581 = 36871) (by norm_num)
theorem B589997 : Blo 307833 589997 := bbase (se 3 (by rfl) ⟨110624, by rfl⟩ : syracuseStep 589997 = 221249) (by norm_num)
theorem B524461 : Blo 307833 524461 := bbase (se 3 (by rfl) ⟨98336, by rfl⟩ : syracuseStep 524461 = 196673) (by norm_num)
theorem B393437 : Blo 307833 393437 := bbase (se 3 (by rfl) ⟨73769, by rfl⟩ : syracuseStep 393437 = 147539) (by norm_num)
theorem B524549 : Blo 307833 524549 := bbase (se 4 (by rfl) ⟨49176, by rfl⟩ : syracuseStep 524549 = 98353) (by norm_num)
theorem B393493 : Blo 307833 393493 := bbase (se 6 (by rfl) ⟨9222, by rfl⟩ : syracuseStep 393493 = 18445) (by norm_num)
theorem B590141 : Blo 307833 590141 := bbase (se 3 (by rfl) ⟨110651, by rfl⟩ : syracuseStep 590141 = 221303) (by norm_num)
theorem B786773 : Blo 307833 786773 := bbase (se 10 (by rfl) ⟨1152, by rfl⟩ : syracuseStep 786773 = 2305) (by norm_num)
theorem B1048949 : Blo 307833 1048949 := bbase (se 5 (by rfl) ⟨49169, by rfl⟩ : syracuseStep 1048949 = 98339) (by norm_num)
theorem B393589 : Blo 307833 393589 := bbase (se 5 (by rfl) ⟨18449, by rfl⟩ : syracuseStep 393589 = 36899) (by norm_num)
theorem B524677 : Blo 307833 524677 := bbase (se 4 (by rfl) ⟨49188, by rfl⟩ : syracuseStep 524677 = 98377) (by norm_num)
theorem B524765 : Blo 307833 524765 := bbase (se 3 (by rfl) ⟨98393, by rfl⟩ : syracuseStep 524765 = 196787) (by norm_num)
theorem B885269 : Blo 307833 885269 := bbase (se 6 (by rfl) ⟨20748, by rfl⟩ : syracuseStep 885269 = 41497) (by norm_num)
theorem B393761 : Blo 307833 393761 := bbase (se 2 (by rfl) ⟨147660, by rfl⟩ : syracuseStep 393761 = 295321) (by norm_num)
theorem B7111253 : Blo 307833 7111253 := bbase (se 8 (by rfl) ⟨41667, by rfl⟩ : syracuseStep 7111253 = 83335) (by norm_num)
theorem B393817 : Blo 307833 393817 := bbase (se 2 (by rfl) ⟨147681, by rfl⟩ : syracuseStep 393817 = 295363) (by norm_num)
theorem B590429 : Blo 307833 590429 := bbase (se 3 (by rfl) ⟨110705, by rfl⟩ : syracuseStep 590429 = 221411) (by norm_num)
theorem B524893 : Blo 307833 524893 := bbase (se 3 (by rfl) ⟨98417, by rfl⟩ : syracuseStep 524893 = 196835) (by norm_num)
theorem B787117 : Blo 307833 787117 := bbase (se 3 (by rfl) ⟨147584, by rfl⟩ : syracuseStep 787117 = 295169) (by norm_num)
theorem B524981 : Blo 307833 524981 := bbase (se 5 (by rfl) ⟨24608, by rfl⟩ : syracuseStep 524981 = 49217) (by norm_num)
theorem B393913 : Blo 307833 393913 := bbase (se 2 (by rfl) ⟨147717, by rfl⟩ : syracuseStep 393913 = 295435) (by norm_num)
theorem B3572437 : Blo 307833 3572437 := bbase (se 7 (by rfl) ⟨41864, by rfl⟩ : syracuseStep 3572437 = 83729) (by norm_num)
theorem B590581 : Blo 307833 590581 := bbase (se 5 (by rfl) ⟨27683, by rfl⟩ : syracuseStep 590581 = 55367) (by norm_num)
theorem B787229 : Blo 307833 787229 := bbase (se 3 (by rfl) ⟨147605, by rfl⟩ : syracuseStep 787229 = 295211) (by norm_num)
theorem B1049381 : Blo 307833 1049381 := bbase (se 4 (by rfl) ⟨98379, by rfl⟩ : syracuseStep 1049381 = 196759) (by norm_num)
theorem B525109 : Blo 307833 525109 := bbase (se 5 (by rfl) ⟨24614, by rfl⟩ : syracuseStep 525109 = 49229) (by norm_num)
theorem B394085 : Blo 307833 394085 := bbase (se 4 (by rfl) ⟨36945, by rfl⟩ : syracuseStep 394085 = 73891) (by norm_num)
theorem B525197 : Blo 307833 525197 := bbase (se 3 (by rfl) ⟨98474, by rfl⟩ : syracuseStep 525197 = 196949) (by norm_num)
theorem B394141 : Blo 307833 394141 := bbase (se 3 (by rfl) ⟨73901, by rfl⟩ : syracuseStep 394141 = 147803) (by norm_num)
theorem B1573829 : Blo 307833 1573829 := bbase (se 4 (by rfl) ⟨147546, by rfl⟩ : syracuseStep 1573829 = 295093) (by norm_num)
theorem B787421 : Blo 307833 787421 := bbase (se 3 (by rfl) ⟨147641, by rfl⟩ : syracuseStep 787421 = 295283) (by norm_num)
theorem B2556917 : Blo 307833 2556917 := bbase (se 5 (by rfl) ⟨119855, by rfl⟩ : syracuseStep 2556917 = 239711) (by norm_num)
theorem B394237 : Blo 307833 394237 := bbase (se 3 (by rfl) ⟨73919, by rfl⟩ : syracuseStep 394237 = 147839) (by norm_num)
theorem B525325 : Blo 307833 525325 := bbase (se 3 (by rfl) ⟨98498, by rfl⟩ : syracuseStep 525325 = 196997) (by norm_num)
theorem B590885 : Blo 307833 590885 := bbase (se 4 (by rfl) ⟨55395, by rfl⟩ : syracuseStep 590885 = 110791) (by norm_num)
theorem B525413 : Blo 307833 525413 := bbase (se 4 (by rfl) ⟨49257, by rfl⟩ : syracuseStep 525413 = 98515) (by norm_num)
theorem B394409 : Blo 307833 394409 := bbase (se 2 (by rfl) ⟨147903, by rfl⟩ : syracuseStep 394409 = 295807) (by norm_num)
theorem B2360501 : Blo 307833 2360501 := bbase (se 5 (by rfl) ⟨110648, by rfl⟩ : syracuseStep 2360501 = 221297) (by norm_num)
theorem B885941 : Blo 307833 885941 := bbase (se 5 (by rfl) ⟨41528, by rfl⟩ : syracuseStep 885941 = 83057) (by norm_num)
theorem B1049813 : Blo 307833 1049813 := bbase (se 7 (by rfl) ⟨12302, by rfl⟩ : syracuseStep 1049813 = 24605) (by norm_num)
theorem B394465 : Blo 307833 394465 := bbase (se 2 (by rfl) ⟨147924, by rfl⟩ : syracuseStep 394465 = 295849) (by norm_num)
theorem B525541 : Blo 307833 525541 := bbase (se 4 (by rfl) ⟨49269, by rfl⟩ : syracuseStep 525541 = 98539) (by norm_num)
theorem B328969 : Blo 307833 328969 := bbase (se 2 (by rfl) ⟨123363, by rfl⟩ : syracuseStep 328969 = 246727) (by norm_num)
theorem B787765 : Blo 307833 787765 := bbase (se 5 (by rfl) ⟨36926, by rfl⟩ : syracuseStep 787765 = 73853) (by norm_num)
theorem B525629 : Blo 307833 525629 := bbase (se 3 (by rfl) ⟨98555, by rfl⟩ : syracuseStep 525629 = 197111) (by norm_num)
theorem B394561 : Blo 307833 394561 := bbase (se 2 (by rfl) ⟨147960, by rfl⟩ : syracuseStep 394561 = 295921) (by norm_num)
theorem B1115461 : Blo 307833 1115461 := bbase (se 4 (by rfl) ⟨104574, by rfl⟩ : syracuseStep 1115461 = 209149) (by norm_num)
theorem B329041 : Blo 307833 329041 := bbase (se 2 (by rfl) ⟨123390, by rfl⟩ : syracuseStep 329041 = 246781) (by norm_num)
theorem B1901909 : Blo 307833 1901909 := bbase (se 12 (by rfl) ⟨696, by rfl⟩ : syracuseStep 1901909 = 1393) (by norm_num)
theorem B787877 : Blo 307833 787877 := bbase (se 4 (by rfl) ⟨73863, by rfl⟩ : syracuseStep 787877 = 147727) (by norm_num)
theorem B525757 : Blo 307833 525757 := bbase (se 3 (by rfl) ⟨98579, by rfl⟩ : syracuseStep 525757 = 197159) (by norm_num)
theorem B329221 : Blo 307833 329221 := bbase (se 4 (by rfl) ⟨30864, by rfl⟩ : syracuseStep 329221 = 61729) (by norm_num)
theorem B525845 : Blo 307833 525845 := bbase (se 6 (by rfl) ⟨12324, by rfl⟩ : syracuseStep 525845 = 24649) (by norm_num)
theorem B886373 : Blo 307833 886373 := bbase (se 4 (by rfl) ⟨83097, by rfl⟩ : syracuseStep 886373 = 166195) (by norm_num)
theorem B788069 : Blo 307833 788069 := bbase (se 4 (by rfl) ⟨73881, by rfl⟩ : syracuseStep 788069 = 147763) (by norm_num)
theorem B493165 : Blo 307833 493165 := bbase (se 3 (by rfl) ⟨92468, by rfl⟩ : syracuseStep 493165 = 184937) (by norm_num)
theorem B1050245 : Blo 307833 1050245 := bbase (se 4 (by rfl) ⟨98460, by rfl⟩ : syracuseStep 1050245 = 196921) (by norm_num)
theorem B525973 : Blo 307833 525973 := bbase (se 6 (by rfl) ⟨12327, by rfl⟩ : syracuseStep 525973 = 24655) (by norm_num)
theorem B493229 : Blo 307833 493229 := bbase (se 3 (by rfl) ⟨92480, by rfl⟩ : syracuseStep 493229 = 184961) (by norm_num)
theorem B526061 : Blo 307833 526061 := bbase (se 3 (by rfl) ⟨98636, by rfl⟩ : syracuseStep 526061 = 197273) (by norm_num)
theorem B591637 : Blo 307833 591637 := bbase (se 6 (by rfl) ⟨13866, by rfl⟩ : syracuseStep 591637 = 27733) (by norm_num)
theorem B493357 : Blo 307833 493357 := bbase (se 3 (by rfl) ⟨92504, by rfl⟩ : syracuseStep 493357 = 185009) (by norm_num)
theorem B526189 : Blo 307833 526189 := bbase (se 3 (by rfl) ⟨98660, by rfl⟩ : syracuseStep 526189 = 197321) (by norm_num)
theorem B1181573 : Blo 307833 1181573 := bbase (se 4 (by rfl) ⟨110772, by rfl⟩ : syracuseStep 1181573 = 221545) (by norm_num)
theorem B591781 : Blo 307833 591781 := bbase (se 4 (by rfl) ⟨55479, by rfl⟩ : syracuseStep 591781 = 110959) (by norm_num)
theorem B788413 : Blo 307833 788413 := bbase (se 3 (by rfl) ⟨147827, by rfl⟩ : syracuseStep 788413 = 295655) (by norm_num)
theorem B329665 : Blo 307833 329665 := bbase (se 2 (by rfl) ⟨123624, by rfl⟩ : syracuseStep 329665 = 247249) (by norm_num)
theorem B788525 : Blo 307833 788525 := bbase (se 3 (by rfl) ⟨147848, by rfl⟩ : syracuseStep 788525 = 295697) (by norm_num)
theorem B1050677 : Blo 307833 1050677 := bbase (se 5 (by rfl) ⟨49250, by rfl⟩ : syracuseStep 1050677 = 98501) (by norm_num)
theorem B329789 : Blo 307833 329789 := bbase (se 3 (by rfl) ⟨61835, by rfl⟩ : syracuseStep 329789 = 123671) (by norm_num)
theorem B591941 : Blo 307833 591941 := bbase (se 4 (by rfl) ⟨55494, by rfl⟩ : syracuseStep 591941 = 110989) (by norm_num)
theorem B559237 : Blo 307833 559237 := bbase (se 4 (by rfl) ⟨52428, by rfl⟩ : syracuseStep 559237 = 104857) (by norm_num)
theorem B1181861 : Blo 307833 1181861 := bbase (se 4 (by rfl) ⟨110799, by rfl⟩ : syracuseStep 1181861 = 221599) (by norm_num)
theorem B1575125 : Blo 307833 1575125 := bbase (se 7 (by rfl) ⟨18458, by rfl⟩ : syracuseStep 1575125 = 36917) (by norm_num)
theorem B788717 : Blo 307833 788717 := bbase (se 3 (by rfl) ⟨147884, by rfl⟩ : syracuseStep 788717 = 295769) (by norm_num)
theorem B624917 : Blo 307833 624917 := bbase (se 6 (by rfl) ⟨14646, by rfl⟩ : syracuseStep 624917 = 29293) (by norm_num)
theorem B330041 : Blo 307833 330041 := bbase (se 2 (by rfl) ⟨123765, by rfl⟩ : syracuseStep 330041 = 247531) (by norm_num)
theorem B657733 : Blo 307833 657733 := bbase (se 4 (by rfl) ⟨61662, by rfl⟩ : syracuseStep 657733 = 123325) (by norm_num)
theorem B887125 : Blo 307833 887125 := bbase (se 10 (by rfl) ⟨1299, by rfl⟩ : syracuseStep 887125 = 2599) (by norm_num)
theorem B657877 : Blo 307833 657877 := bbase (se 7 (by rfl) ⟨7709, by rfl⟩ : syracuseStep 657877 = 15419) (by norm_num)
theorem B1051109 : Blo 307833 1051109 := bbase (se 4 (by rfl) ⟨98541, by rfl⟩ : syracuseStep 1051109 = 197083) (by norm_num)
theorem B789061 : Blo 307833 789061 := bbase (se 4 (by rfl) ⟨73974, by rfl⟩ : syracuseStep 789061 = 147949) (by norm_num)
theorem B1116773 : Blo 307833 1116773 := bbase (se 4 (by rfl) ⟨104697, by rfl⟩ : syracuseStep 1116773 = 209395) (by norm_num)
theorem B789173 : Blo 307833 789173 := bbase (se 5 (by rfl) ⟨36992, by rfl⟩ : syracuseStep 789173 = 73985) (by norm_num)
theorem B559813 : Blo 307833 559813 := bbase (se 4 (by rfl) ⟨52482, by rfl⟩ : syracuseStep 559813 = 104965) (by norm_num)
theorem B330485 : Blo 307833 330485 := bbase (se 5 (by rfl) ⟨15491, by rfl⟩ : syracuseStep 330485 = 30983) (by norm_num)
theorem B625477 : Blo 307833 625477 := bbase (se 4 (by rfl) ⟨58638, by rfl⟩ : syracuseStep 625477 = 117277) (by norm_num)
theorem B658253 : Blo 307833 658253 := bbase (se 3 (by rfl) ⟨123422, by rfl⟩ : syracuseStep 658253 = 246845) (by norm_num)
theorem B1051541 : Blo 307833 1051541 := bbase (se 6 (by rfl) ⟨24645, by rfl⟩ : syracuseStep 1051541 = 49291) (by norm_num)
theorem B461765 : Blo 307833 461765 := bbase (se 4 (by rfl) ⟨43290, by rfl⟩ : syracuseStep 461765 = 86581) (by norm_num)
theorem B461789 : Blo 307833 461789 := bbase (se 3 (by rfl) ⟨86585, by rfl⟩ : syracuseStep 461789 = 173171) (by norm_num)
theorem B330733 : Blo 307833 330733 := bbase (se 3 (by rfl) ⟨62012, by rfl⟩ : syracuseStep 330733 = 124025) (by norm_num)
theorem B461813 : Blo 307833 461813 := bbase (se 5 (by rfl) ⟨21647, by rfl⟩ : syracuseStep 461813 = 43295) (by norm_num)
theorem B494581 : Blo 307833 494581 := bbase (se 5 (by rfl) ⟨23183, by rfl⟩ : syracuseStep 494581 = 46367) (by norm_num)
theorem B461837 : Blo 307833 461837 := bbase (se 3 (by rfl) ⟨86594, by rfl⟩ : syracuseStep 461837 = 173189) (by norm_num)
theorem B461861 : Blo 307833 461861 := bbase (se 4 (by rfl) ⟨43299, by rfl⟩ : syracuseStep 461861 = 86599) (by norm_num)
theorem B461885 : Blo 307833 461885 := bbase (se 3 (by rfl) ⟨86603, by rfl⟩ : syracuseStep 461885 = 173207) (by norm_num)
theorem B461909 : Blo 307833 461909 := bbase (se 8 (by rfl) ⟨2706, by rfl⟩ : syracuseStep 461909 = 5413) (by norm_num)
theorem B2821205 : Blo 307833 2821205 := bbase (se 8 (by rfl) ⟨16530, by rfl⟩ : syracuseStep 2821205 = 33061) (by norm_num)
theorem B461933 : Blo 307833 461933 := bbase (se 3 (by rfl) ⟨86612, by rfl⟩ : syracuseStep 461933 = 173225) (by norm_num)
theorem B461957 : Blo 307833 461957 := bbase (se 4 (by rfl) ⟨43308, by rfl⟩ : syracuseStep 461957 = 86617) (by norm_num)
theorem B461981 : Blo 307833 461981 := bbase (se 3 (by rfl) ⟨86621, by rfl⟩ : syracuseStep 461981 = 173243) (by norm_num)
theorem B462005 : Blo 307833 462005 := bbase (se 5 (by rfl) ⟨21656, by rfl⟩ : syracuseStep 462005 = 43313) (by norm_num)
theorem B658621 : Blo 307833 658621 := bbase (se 3 (by rfl) ⟨123491, by rfl⟩ : syracuseStep 658621 = 246983) (by norm_num)
theorem B462029 : Blo 307833 462029 := bbase (se 3 (by rfl) ⟨86630, by rfl⟩ : syracuseStep 462029 = 173261) (by norm_num)
theorem B462053 : Blo 307833 462053 := bbase (se 4 (by rfl) ⟨43317, by rfl⟩ : syracuseStep 462053 = 86635) (by norm_num)
theorem B462077 : Blo 307833 462077 := bbase (se 3 (by rfl) ⟨86639, by rfl⟩ : syracuseStep 462077 = 173279) (by norm_num)
theorem B462101 : Blo 307833 462101 := bbase (se 6 (by rfl) ⟨10830, by rfl⟩ : syracuseStep 462101 = 21661) (by norm_num)
theorem B462125 : Blo 307833 462125 := bbase (se 3 (by rfl) ⟨86648, by rfl⟩ : syracuseStep 462125 = 173297) (by norm_num)
theorem B462149 : Blo 307833 462149 := bbase (se 4 (by rfl) ⟨43326, by rfl⟩ : syracuseStep 462149 = 86653) (by norm_num)
theorem B1183045 : Blo 307833 1183045 := bbase (se 4 (by rfl) ⟨110910, by rfl⟩ : syracuseStep 1183045 = 221821) (by norm_num)
theorem B1051973 : Blo 307833 1051973 := bbase (se 4 (by rfl) ⟨98622, by rfl⟩ : syracuseStep 1051973 = 197245) (by norm_num)
theorem B462173 : Blo 307833 462173 := bbase (se 3 (by rfl) ⟨86657, by rfl⟩ : syracuseStep 462173 = 173315) (by norm_num)
theorem B462197 : Blo 307833 462197 := bbase (se 5 (by rfl) ⟨21665, by rfl⟩ : syracuseStep 462197 = 43331) (by norm_num)
theorem B462221 : Blo 307833 462221 := bbase (se 3 (by rfl) ⟨86666, by rfl⟩ : syracuseStep 462221 = 173333) (by norm_num)
theorem B462245 : Blo 307833 462245 := bbase (se 4 (by rfl) ⟨43335, by rfl⟩ : syracuseStep 462245 = 86671) (by norm_num)
theorem B331177 : Blo 307833 331177 := bbase (se 2 (by rfl) ⟨124191, by rfl⟩ : syracuseStep 331177 = 248383) (by norm_num)
theorem B462269 : Blo 307833 462269 := bbase (se 3 (by rfl) ⟨86675, by rfl⟩ : syracuseStep 462269 = 173351) (by norm_num)
theorem B462293 : Blo 307833 462293 := bbase (se 7 (by rfl) ⟨5417, by rfl⟩ : syracuseStep 462293 = 10835) (by norm_num)
theorem B331237 : Blo 307833 331237 := bbase (se 4 (by rfl) ⟨31053, by rfl⟩ : syracuseStep 331237 = 62107) (by norm_num)
theorem B1576421 : Blo 307833 1576421 := bbase (se 4 (by rfl) ⟨147789, by rfl⟩ : syracuseStep 1576421 = 295579) (by norm_num)
theorem B462317 : Blo 307833 462317 := bbase (se 3 (by rfl) ⟨86684, by rfl⟩ : syracuseStep 462317 = 173369) (by norm_num)
theorem B560621 : Blo 307833 560621 := bbase (se 3 (by rfl) ⟨105116, by rfl⟩ : syracuseStep 560621 = 210233) (by norm_num)
theorem B462341 : Blo 307833 462341 := bbase (se 4 (by rfl) ⟨43344, by rfl⟩ : syracuseStep 462341 = 86689) (by norm_num)
theorem B462365 : Blo 307833 462365 := bbase (se 3 (by rfl) ⟨86693, by rfl⟩ : syracuseStep 462365 = 173387) (by norm_num)
theorem B462389 : Blo 307833 462389 := bbase (se 5 (by rfl) ⟨21674, by rfl⟩ : syracuseStep 462389 = 43349) (by norm_num)
theorem B462413 : Blo 307833 462413 := bbase (se 3 (by rfl) ⟨86702, by rfl⟩ : syracuseStep 462413 = 173405) (by norm_num)
theorem B462437 : Blo 307833 462437 := bbase (se 4 (by rfl) ⟨43353, by rfl⟩ : syracuseStep 462437 = 86707) (by norm_num)
theorem B1183349 : Blo 307833 1183349 := bbase (se 5 (by rfl) ⟨55469, by rfl⟩ : syracuseStep 1183349 = 110939) (by norm_num)
theorem B462461 : Blo 307833 462461 := bbase (se 3 (by rfl) ⟨86711, by rfl⟩ : syracuseStep 462461 = 173423) (by norm_num)
theorem B462485 : Blo 307833 462485 := bbase (se 6 (by rfl) ⟨10839, by rfl⟩ : syracuseStep 462485 = 21679) (by norm_num)
theorem B495253 : Blo 307833 495253 := bbase (se 6 (by rfl) ⟨11607, by rfl⟩ : syracuseStep 495253 = 23215) (by norm_num)
theorem B462509 : Blo 307833 462509 := bbase (se 3 (by rfl) ⟨86720, by rfl⟩ : syracuseStep 462509 = 173441) (by norm_num)
theorem B462533 : Blo 307833 462533 := bbase (se 4 (by rfl) ⟨43362, by rfl⟩ : syracuseStep 462533 = 86725) (by norm_num)
theorem B397001 : Blo 307833 397001 := bbase (se 2 (by rfl) ⟨148875, by rfl⟩ : syracuseStep 397001 = 297751) (by norm_num)
theorem B462557 : Blo 307833 462557 := bbase (se 3 (by rfl) ⟨86729, by rfl⟩ : syracuseStep 462557 = 173459) (by norm_num)
theorem B462581 : Blo 307833 462581 := bbase (se 5 (by rfl) ⟨21683, by rfl⟩ : syracuseStep 462581 = 43367) (by norm_num)
theorem B1052405 : Blo 307833 1052405 := bbase (se 5 (by rfl) ⟨49331, by rfl⟩ : syracuseStep 1052405 = 98663) (by norm_num)
theorem B462605 : Blo 307833 462605 := bbase (se 3 (by rfl) ⟨86738, by rfl⟩ : syracuseStep 462605 = 173477) (by norm_num)
theorem B528157 : Blo 307833 528157 := bbase (se 3 (by rfl) ⟨99029, by rfl⟩ : syracuseStep 528157 = 198059) (by norm_num)
theorem B331553 : Blo 307833 331553 := bbase (se 2 (by rfl) ⟨124332, by rfl⟩ : syracuseStep 331553 = 248665) (by norm_num)
theorem B462629 : Blo 307833 462629 := bbase (se 4 (by rfl) ⟨43371, by rfl⟩ : syracuseStep 462629 = 86743) (by norm_num)
theorem B462653 : Blo 307833 462653 := bbase (se 3 (by rfl) ⟨86747, by rfl⟩ : syracuseStep 462653 = 173495) (by norm_num)
theorem B462677 : Blo 307833 462677 := bbase (se 9 (by rfl) ⟨1355, by rfl⟩ : syracuseStep 462677 = 2711) (by norm_num)
theorem B462701 : Blo 307833 462701 := bbase (se 3 (by rfl) ⟨86756, by rfl⟩ : syracuseStep 462701 = 173513) (by norm_num)
theorem B462725 : Blo 307833 462725 := bbase (se 4 (by rfl) ⟨43380, by rfl⟩ : syracuseStep 462725 = 86761) (by norm_num)
theorem B462749 : Blo 307833 462749 := bbase (se 3 (by rfl) ⟨86765, by rfl⟩ : syracuseStep 462749 = 173531) (by norm_num)
theorem B561053 : Blo 307833 561053 := bbase (se 3 (by rfl) ⟨105197, by rfl⟩ : syracuseStep 561053 = 210395) (by norm_num)
theorem B462773 : Blo 307833 462773 := bbase (se 5 (by rfl) ⟨21692, by rfl⟩ : syracuseStep 462773 = 43385) (by norm_num)
theorem B462797 : Blo 307833 462797 := bbase (se 3 (by rfl) ⟨86774, by rfl⟩ : syracuseStep 462797 = 173549) (by norm_num)
theorem B462821 : Blo 307833 462821 := bbase (se 4 (by rfl) ⟨43389, by rfl⟩ : syracuseStep 462821 = 86779) (by norm_num)
theorem B462845 : Blo 307833 462845 := bbase (se 3 (by rfl) ⟨86783, by rfl⟩ : syracuseStep 462845 = 173567) (by norm_num)
theorem B462869 : Blo 307833 462869 := bbase (se 6 (by rfl) ⟨10848, by rfl⟩ : syracuseStep 462869 = 21697) (by norm_num)
theorem B462893 : Blo 307833 462893 := bbase (se 3 (by rfl) ⟨86792, by rfl⟩ : syracuseStep 462893 = 173585) (by norm_num)
theorem B561197 : Blo 307833 561197 := bbase (se 3 (by rfl) ⟨105224, by rfl⟩ : syracuseStep 561197 = 210449) (by norm_num)
theorem B462917 : Blo 307833 462917 := bbase (se 4 (by rfl) ⟨43398, by rfl⟩ : syracuseStep 462917 = 86797) (by norm_num)
theorem B462941 : Blo 307833 462941 := bbase (se 3 (by rfl) ⟨86801, by rfl⟩ : syracuseStep 462941 = 173603) (by norm_num)
theorem B462965 : Blo 307833 462965 := bbase (se 5 (by rfl) ⟨21701, by rfl⟩ : syracuseStep 462965 = 43403) (by norm_num)
theorem B462989 : Blo 307833 462989 := bbase (se 3 (by rfl) ⟨86810, by rfl⟩ : syracuseStep 462989 = 173621) (by norm_num)
theorem B1118357 : Blo 307833 1118357 := bbase (se 6 (by rfl) ⟨26211, by rfl⟩ : syracuseStep 1118357 = 52423) (by norm_num)
theorem B463013 : Blo 307833 463013 := bbase (se 4 (by rfl) ⟨43407, by rfl⟩ : syracuseStep 463013 = 86815) (by norm_num)
theorem B463037 : Blo 307833 463037 := bbase (se 3 (by rfl) ⟨86819, by rfl⟩ : syracuseStep 463037 = 173639) (by norm_num)
theorem B463061 : Blo 307833 463061 := bbase (se 7 (by rfl) ⟨5426, by rfl⟩ : syracuseStep 463061 = 10853) (by norm_num)
theorem B331997 : Blo 307833 331997 := bbase (se 3 (by rfl) ⟨62249, by rfl⟩ : syracuseStep 331997 = 124499) (by norm_num)
theorem B463085 : Blo 307833 463085 := bbase (se 3 (by rfl) ⟨86828, by rfl⟩ : syracuseStep 463085 = 173657) (by norm_num)
theorem B463109 : Blo 307833 463109 := bbase (se 4 (by rfl) ⟨43416, by rfl⟩ : syracuseStep 463109 = 86833) (by norm_num)
theorem B561421 : Blo 307833 561421 := bbase (se 3 (by rfl) ⟨105266, by rfl⟩ : syracuseStep 561421 = 210533) (by norm_num)
theorem B2265365 : Blo 307833 2265365 := bbase (se 6 (by rfl) ⟨53094, by rfl⟩ : syracuseStep 2265365 = 106189) (by norm_num)
theorem B332057 : Blo 307833 332057 := bbase (se 2 (by rfl) ⟨124521, by rfl⟩ : syracuseStep 332057 = 249043) (by norm_num)
theorem B463133 : Blo 307833 463133 := bbase (se 3 (by rfl) ⟨86837, by rfl⟩ : syracuseStep 463133 = 173675) (by norm_num)
theorem B463157 : Blo 307833 463157 := bbase (se 5 (by rfl) ⟨21710, by rfl⟩ : syracuseStep 463157 = 43421) (by norm_num)
theorem B463181 : Blo 307833 463181 := bbase (se 3 (by rfl) ⟨86846, by rfl⟩ : syracuseStep 463181 = 173693) (by norm_num)
theorem B397657 : Blo 307833 397657 := bbase (se 2 (by rfl) ⟨149121, by rfl⟩ : syracuseStep 397657 = 298243) (by norm_num)
theorem B463205 : Blo 307833 463205 := bbase (se 4 (by rfl) ⟨43425, by rfl⟩ : syracuseStep 463205 = 86851) (by norm_num)
theorem B463229 : Blo 307833 463229 := bbase (se 3 (by rfl) ⟨86855, by rfl⟩ : syracuseStep 463229 = 173711) (by norm_num)
theorem B463253 : Blo 307833 463253 := bbase (se 6 (by rfl) ⟨10857, by rfl⟩ : syracuseStep 463253 = 21715) (by norm_num)
theorem B332185 : Blo 307833 332185 := bbase (se 2 (by rfl) ⟨124569, by rfl⟩ : syracuseStep 332185 = 249139) (by norm_num)
theorem B463277 : Blo 307833 463277 := bbase (se 3 (by rfl) ⟨86864, by rfl⟩ : syracuseStep 463277 = 173729) (by norm_num)
theorem B1249717 : Blo 307833 1249717 := bbase (se 5 (by rfl) ⟨58580, by rfl⟩ : syracuseStep 1249717 = 117161) (by norm_num)
theorem B463301 : Blo 307833 463301 := bbase (se 4 (by rfl) ⟨43434, by rfl⟩ : syracuseStep 463301 = 86869) (by norm_num)
theorem B692693 : Blo 307833 692693 := bbase (se 7 (by rfl) ⟨8117, by rfl⟩ : syracuseStep 692693 = 16235) (by norm_num)
theorem B463325 : Blo 307833 463325 := bbase (se 3 (by rfl) ⟨86873, by rfl⟩ : syracuseStep 463325 = 173747) (by norm_num)
theorem B397801 : Blo 307833 397801 := bbase (se 2 (by rfl) ⟨149175, by rfl⟩ : syracuseStep 397801 = 298351) (by norm_num)
theorem B594421 : Blo 307833 594421 := bbase (se 5 (by rfl) ⟨27863, by rfl⟩ : syracuseStep 594421 = 55727) (by norm_num)
theorem B463349 : Blo 307833 463349 := bbase (se 5 (by rfl) ⟨21719, by rfl⟩ : syracuseStep 463349 = 43439) (by norm_num)
theorem B463373 : Blo 307833 463373 := bbase (se 3 (by rfl) ⟨86882, by rfl⟩ : syracuseStep 463373 = 173765) (by norm_num)
theorem B692765 : Blo 307833 692765 := bbase (se 3 (by rfl) ⟨129893, by rfl⟩ : syracuseStep 692765 = 259787) (by norm_num)
theorem B463397 : Blo 307833 463397 := bbase (se 4 (by rfl) ⟨43443, by rfl⟩ : syracuseStep 463397 = 86887) (by norm_num)
theorem B463421 : Blo 307833 463421 := bbase (se 3 (by rfl) ⟨86891, by rfl⟩ : syracuseStep 463421 = 173783) (by norm_num)
theorem B627277 : Blo 307833 627277 := bbase (se 3 (by rfl) ⟨117614, by rfl⟩ : syracuseStep 627277 = 235229) (by norm_num)
theorem B463445 : Blo 307833 463445 := bbase (se 8 (by rfl) ⟨2715, by rfl⟩ : syracuseStep 463445 = 5431) (by norm_num)
theorem B692837 : Blo 307833 692837 := bbase (se 4 (by rfl) ⟨64953, by rfl⟩ : syracuseStep 692837 = 129907) (by norm_num)
theorem B463469 : Blo 307833 463469 := bbase (se 3 (by rfl) ⟨86900, by rfl⟩ : syracuseStep 463469 = 173801) (by norm_num)
theorem B561773 : Blo 307833 561773 := bbase (se 3 (by rfl) ⟨105332, by rfl⟩ : syracuseStep 561773 = 210665) (by norm_num)
theorem B496253 : Blo 307833 496253 := bbase (se 3 (by rfl) ⟨93047, by rfl⟩ : syracuseStep 496253 = 186095) (by norm_num)
theorem B463493 : Blo 307833 463493 := bbase (se 4 (by rfl) ⟨43452, by rfl⟩ : syracuseStep 463493 = 86905) (by norm_num)
theorem B463517 : Blo 307833 463517 := bbase (se 3 (by rfl) ⟨86909, by rfl⟩ : syracuseStep 463517 = 173819) (by norm_num)
theorem B660125 : Blo 307833 660125 := bbase (se 3 (by rfl) ⟨123773, by rfl⟩ : syracuseStep 660125 = 247547) (by norm_num)
theorem B692909 : Blo 307833 692909 := bbase (se 3 (by rfl) ⟨129920, by rfl⟩ : syracuseStep 692909 = 259841) (by norm_num)
theorem B463541 : Blo 307833 463541 := bbase (se 5 (by rfl) ⟨21728, by rfl⟩ : syracuseStep 463541 = 43457) (by norm_num)
theorem B463565 : Blo 307833 463565 := bbase (se 3 (by rfl) ⟨86918, by rfl⟩ : syracuseStep 463565 = 173837) (by norm_num)
theorem B463589 : Blo 307833 463589 := bbase (se 4 (by rfl) ⟨43461, by rfl⟩ : syracuseStep 463589 = 86923) (by norm_num)
theorem B692981 : Blo 307833 692981 := bbase (se 5 (by rfl) ⟨32483, by rfl⟩ : syracuseStep 692981 = 64967) (by norm_num)
theorem B1577717 : Blo 307833 1577717 := bbase (se 5 (by rfl) ⟨73955, by rfl⟩ : syracuseStep 1577717 = 147911) (by norm_num)
theorem B463613 : Blo 307833 463613 := bbase (se 3 (by rfl) ⟨86927, by rfl⟩ : syracuseStep 463613 = 173855) (by norm_num)
theorem B463637 : Blo 307833 463637 := bbase (se 6 (by rfl) ⟨10866, by rfl⟩ : syracuseStep 463637 = 21733) (by norm_num)
theorem B791333 : Blo 307833 791333 := bbase (se 4 (by rfl) ⟨74187, by rfl⟩ : syracuseStep 791333 = 148375) (by norm_num)
theorem B463661 : Blo 307833 463661 := bbase (se 3 (by rfl) ⟨86936, by rfl⟩ : syracuseStep 463661 = 173873) (by norm_num)
theorem B660269 : Blo 307833 660269 := bbase (se 3 (by rfl) ⟨123800, by rfl⟩ : syracuseStep 660269 = 247601) (by norm_num)
theorem B693053 : Blo 307833 693053 := bbase (se 3 (by rfl) ⟨129947, by rfl⟩ : syracuseStep 693053 = 259895) (by norm_num)
theorem B463685 : Blo 307833 463685 := bbase (se 4 (by rfl) ⟨43470, by rfl⟩ : syracuseStep 463685 = 86941) (by norm_num)
theorem B332629 : Blo 307833 332629 := bbase (se 9 (by rfl) ⟨974, by rfl⟩ : syracuseStep 332629 = 1949) (by norm_num)
theorem B463709 : Blo 307833 463709 := bbase (se 3 (by rfl) ⟨86945, by rfl⟩ : syracuseStep 463709 = 173891) (by norm_num)
theorem B463733 : Blo 307833 463733 := bbase (se 5 (by rfl) ⟨21737, by rfl⟩ : syracuseStep 463733 = 43475) (by norm_num)
theorem B693125 : Blo 307833 693125 := bbase (se 4 (by rfl) ⟨64980, by rfl⟩ : syracuseStep 693125 = 129961) (by norm_num)
theorem B463757 : Blo 307833 463757 := bbase (se 3 (by rfl) ⟨86954, by rfl⟩ : syracuseStep 463757 = 173909) (by norm_num)
theorem B463781 : Blo 307833 463781 := bbase (se 4 (by rfl) ⟨43479, by rfl⟩ : syracuseStep 463781 = 86959) (by norm_num)
theorem B463805 : Blo 307833 463805 := bbase (se 3 (by rfl) ⟨86963, by rfl⟩ : syracuseStep 463805 = 173927) (by norm_num)
theorem B693197 : Blo 307833 693197 := bbase (se 3 (by rfl) ⟨129974, by rfl⟩ : syracuseStep 693197 = 259949) (by norm_num)
theorem B332749 : Blo 307833 332749 := bbase (se 3 (by rfl) ⟨62390, by rfl⟩ : syracuseStep 332749 = 124781) (by norm_num)
theorem B463829 : Blo 307833 463829 := bbase (se 7 (by rfl) ⟨5435, by rfl⟩ : syracuseStep 463829 = 10871) (by norm_num)
theorem B463853 : Blo 307833 463853 := bbase (se 3 (by rfl) ⟨86972, by rfl⟩ : syracuseStep 463853 = 173945) (by norm_num)
theorem B463877 : Blo 307833 463877 := bbase (se 4 (by rfl) ⟨43488, by rfl⟩ : syracuseStep 463877 = 86977) (by norm_num)
theorem B693269 : Blo 307833 693269 := bbase (se 6 (by rfl) ⟨16248, by rfl⟩ : syracuseStep 693269 = 32497) (by norm_num)
theorem B463901 : Blo 307833 463901 := bbase (se 3 (by rfl) ⟨86981, by rfl⟩ : syracuseStep 463901 = 173963) (by norm_num)
theorem B463925 : Blo 307833 463925 := bbase (se 5 (by rfl) ⟨21746, by rfl⟩ : syracuseStep 463925 = 43493) (by norm_num)
theorem B463949 : Blo 307833 463949 := bbase (se 3 (by rfl) ⟨86990, by rfl⟩ : syracuseStep 463949 = 173981) (by norm_num)
theorem B693341 : Blo 307833 693341 := bbase (se 3 (by rfl) ⟨130001, by rfl⟩ : syracuseStep 693341 = 260003) (by norm_num)
theorem B463973 : Blo 307833 463973 := bbase (se 4 (by rfl) ⟨43497, by rfl⟩ : syracuseStep 463973 = 86995) (by norm_num)
theorem B463997 : Blo 307833 463997 := bbase (se 3 (by rfl) ⟨86999, by rfl⟩ : syracuseStep 463997 = 173999) (by norm_num)
theorem B660629 : Blo 307833 660629 := bbase (se 6 (by rfl) ⟨15483, by rfl⟩ : syracuseStep 660629 = 30967) (by norm_num)
theorem B464021 : Blo 307833 464021 := bbase (se 6 (by rfl) ⟨10875, by rfl⟩ : syracuseStep 464021 = 21751) (by norm_num)
theorem B693413 : Blo 307833 693413 := bbase (se 4 (by rfl) ⟨65007, by rfl⟩ : syracuseStep 693413 = 130015) (by norm_num)
theorem B464045 : Blo 307833 464045 := bbase (se 3 (by rfl) ⟨87008, by rfl⟩ : syracuseStep 464045 = 174017) (by norm_num)
theorem B464069 : Blo 307833 464069 := bbase (se 4 (by rfl) ⟨43506, by rfl⟩ : syracuseStep 464069 = 87013) (by norm_num)
theorem B464093 : Blo 307833 464093 := bbase (se 3 (by rfl) ⟨87017, by rfl⟩ : syracuseStep 464093 = 174035) (by norm_num)
theorem B627941 : Blo 307833 627941 := bbase (se 4 (by rfl) ⟨58869, by rfl⟩ : syracuseStep 627941 = 117739) (by norm_num)
theorem B693485 : Blo 307833 693485 := bbase (se 3 (by rfl) ⟨130028, by rfl⟩ : syracuseStep 693485 = 260057) (by norm_num)
theorem B464117 : Blo 307833 464117 := bbase (se 5 (by rfl) ⟨21755, by rfl⟩ : syracuseStep 464117 = 43511) (by norm_num)
theorem B464141 : Blo 307833 464141 := bbase (se 3 (by rfl) ⟨87026, by rfl⟩ : syracuseStep 464141 = 174053) (by norm_num)
theorem B464165 : Blo 307833 464165 := bbase (se 4 (by rfl) ⟨43515, by rfl⟩ : syracuseStep 464165 = 87031) (by norm_num)
theorem B693557 : Blo 307833 693557 := bbase (se 5 (by rfl) ⟨32510, by rfl⟩ : syracuseStep 693557 = 65021) (by norm_num)
theorem B464189 : Blo 307833 464189 := bbase (se 3 (by rfl) ⟨87035, by rfl⟩ : syracuseStep 464189 = 174071) (by norm_num)
theorem B595277 : Blo 307833 595277 := bbase (se 3 (by rfl) ⟨111614, by rfl⟩ : syracuseStep 595277 = 223229) (by norm_num)
theorem B464213 : Blo 307833 464213 := bbase (se 14 (by rfl) ⟨42, by rfl⟩ : syracuseStep 464213 = 85) (by norm_num)
theorem B464237 : Blo 307833 464237 := bbase (se 3 (by rfl) ⟨87044, by rfl⟩ : syracuseStep 464237 = 174089) (by norm_num)
theorem B693629 : Blo 307833 693629 := bbase (se 3 (by rfl) ⟨130055, by rfl⟩ : syracuseStep 693629 = 260111) (by norm_num)
theorem B464261 : Blo 307833 464261 := bbase (se 4 (by rfl) ⟨43524, by rfl⟩ : syracuseStep 464261 = 87049) (by norm_num)
theorem B464285 : Blo 307833 464285 := bbase (se 3 (by rfl) ⟨87053, by rfl⟩ : syracuseStep 464285 = 174107) (by norm_num)
theorem B464309 : Blo 307833 464309 := bbase (se 5 (by rfl) ⟨21764, by rfl⟩ : syracuseStep 464309 = 43529) (by norm_num)
theorem B693701 : Blo 307833 693701 := bbase (se 4 (by rfl) ⟨65034, by rfl⟩ : syracuseStep 693701 = 130069) (by norm_num)
theorem B464333 : Blo 307833 464333 := bbase (se 3 (by rfl) ⟨87062, by rfl⟩ : syracuseStep 464333 = 174125) (by norm_num)
theorem B464357 : Blo 307833 464357 := bbase (se 4 (by rfl) ⟨43533, by rfl⟩ : syracuseStep 464357 = 87067) (by norm_num)
theorem B988661 : Blo 307833 988661 := bbase (se 5 (by rfl) ⟨46343, by rfl⟩ : syracuseStep 988661 = 92687) (by norm_num)
theorem B464381 : Blo 307833 464381 := bbase (se 3 (by rfl) ⟨87071, by rfl⟩ : syracuseStep 464381 = 174143) (by norm_num)
theorem B693773 : Blo 307833 693773 := bbase (se 3 (by rfl) ⟨130082, by rfl⟩ : syracuseStep 693773 = 260165) (by norm_num)
theorem B464405 : Blo 307833 464405 := bbase (se 6 (by rfl) ⟨10884, by rfl⟩ : syracuseStep 464405 = 21769) (by norm_num)
theorem B464429 : Blo 307833 464429 := bbase (se 3 (by rfl) ⟨87080, by rfl⟩ : syracuseStep 464429 = 174161) (by norm_num)
theorem B464453 : Blo 307833 464453 := bbase (se 4 (by rfl) ⟨43542, by rfl⟩ : syracuseStep 464453 = 87085) (by norm_num)
theorem B693845 : Blo 307833 693845 := bbase (se 8 (by rfl) ⟨4065, by rfl⟩ : syracuseStep 693845 = 8131) (by norm_num)
theorem B464477 : Blo 307833 464477 := bbase (se 3 (by rfl) ⟨87089, by rfl⟩ : syracuseStep 464477 = 174179) (by norm_num)
theorem B464501 : Blo 307833 464501 := bbase (se 5 (by rfl) ⟨21773, by rfl⟩ : syracuseStep 464501 = 43547) (by norm_num)
theorem B530045 : Blo 307833 530045 := bbase (se 3 (by rfl) ⟨99383, by rfl⟩ : syracuseStep 530045 = 198767) (by norm_num)
theorem B464525 : Blo 307833 464525 := bbase (se 3 (by rfl) ⟨87098, by rfl⟩ : syracuseStep 464525 = 174197) (by norm_num)
theorem B693917 : Blo 307833 693917 := bbase (se 3 (by rfl) ⟨130109, by rfl⟩ : syracuseStep 693917 = 260219) (by norm_num)
theorem B464549 : Blo 307833 464549 := bbase (se 4 (by rfl) ⟨43551, by rfl⟩ : syracuseStep 464549 = 87103) (by norm_num)
theorem B464573 : Blo 307833 464573 := bbase (se 3 (by rfl) ⟨87107, by rfl⟩ : syracuseStep 464573 = 174215) (by norm_num)
theorem B464597 : Blo 307833 464597 := bbase (se 7 (by rfl) ⟨5444, by rfl⟩ : syracuseStep 464597 = 10889) (by norm_num)
theorem B693989 : Blo 307833 693989 := bbase (se 4 (by rfl) ⟨65061, by rfl⟩ : syracuseStep 693989 = 130123) (by norm_num)
theorem B464621 : Blo 307833 464621 := bbase (se 3 (by rfl) ⟨87116, by rfl⟩ : syracuseStep 464621 = 174233) (by norm_num)
theorem B464645 : Blo 307833 464645 := bbase (se 4 (by rfl) ⟨43560, by rfl⟩ : syracuseStep 464645 = 87121) (by norm_num)
theorem B464669 : Blo 307833 464669 := bbase (se 3 (by rfl) ⟨87125, by rfl⟩ : syracuseStep 464669 = 174251) (by norm_num)
theorem B694061 : Blo 307833 694061 := bbase (se 3 (by rfl) ⟨130136, by rfl⟩ : syracuseStep 694061 = 260273) (by norm_num)
theorem B464693 : Blo 307833 464693 := bbase (se 5 (by rfl) ⟨21782, by rfl⟩ : syracuseStep 464693 = 43565) (by norm_num)
theorem B628549 : Blo 307833 628549 := bbase (se 4 (by rfl) ⟨58926, by rfl⟩ : syracuseStep 628549 = 117853) (by norm_num)
theorem B464717 : Blo 307833 464717 := bbase (se 3 (by rfl) ⟨87134, by rfl⟩ : syracuseStep 464717 = 174269) (by norm_num)
theorem B464741 : Blo 307833 464741 := bbase (se 4 (by rfl) ⟨43569, by rfl⟩ : syracuseStep 464741 = 87139) (by norm_num)
theorem B530285 : Blo 307833 530285 := bbase (se 3 (by rfl) ⟨99428, by rfl⟩ : syracuseStep 530285 = 198857) (by norm_num)
theorem B694133 : Blo 307833 694133 := bbase (se 5 (by rfl) ⟨32537, by rfl⟩ : syracuseStep 694133 = 65075) (by norm_num)
theorem B464765 : Blo 307833 464765 := bbase (se 3 (by rfl) ⟨87143, by rfl⟩ : syracuseStep 464765 = 174287) (by norm_num)
theorem B464789 : Blo 307833 464789 := bbase (se 6 (by rfl) ⟨10893, by rfl⟩ : syracuseStep 464789 = 21787) (by norm_num)
theorem B464813 : Blo 307833 464813 := bbase (se 3 (by rfl) ⟨87152, by rfl⟩ : syracuseStep 464813 = 174305) (by norm_num)
theorem B694205 : Blo 307833 694205 := bbase (se 3 (by rfl) ⟨130163, by rfl⟩ : syracuseStep 694205 = 260327) (by norm_num)
theorem B464837 : Blo 307833 464837 := bbase (se 4 (by rfl) ⟨43578, by rfl⟩ : syracuseStep 464837 = 87157) (by norm_num)
theorem B464861 : Blo 307833 464861 := bbase (se 3 (by rfl) ⟨87161, by rfl⟩ : syracuseStep 464861 = 174323) (by norm_num)
theorem B464885 : Blo 307833 464885 := bbase (se 5 (by rfl) ⟨21791, by rfl⟩ : syracuseStep 464885 = 43583) (by norm_num)
theorem B694277 : Blo 307833 694277 := bbase (se 4 (by rfl) ⟨65088, by rfl⟩ : syracuseStep 694277 = 130177) (by norm_num)
theorem B661517 : Blo 307833 661517 := bbase (se 3 (by rfl) ⟨124034, by rfl⟩ : syracuseStep 661517 = 248069) (by norm_num)
theorem B464909 : Blo 307833 464909 := bbase (se 3 (by rfl) ⟨87170, by rfl⟩ : syracuseStep 464909 = 174341) (by norm_num)
theorem B464933 : Blo 307833 464933 := bbase (se 4 (by rfl) ⟨43587, by rfl⟩ : syracuseStep 464933 = 87175) (by norm_num)
theorem B464957 : Blo 307833 464957 := bbase (se 3 (by rfl) ⟨87179, by rfl⟩ : syracuseStep 464957 = 174359) (by norm_num)
theorem B694349 : Blo 307833 694349 := bbase (se 3 (by rfl) ⟨130190, by rfl⟩ : syracuseStep 694349 = 260381) (by norm_num)
theorem B464981 : Blo 307833 464981 := bbase (se 8 (by rfl) ⟨2724, by rfl⟩ : syracuseStep 464981 = 5449) (by norm_num)
theorem B497765 : Blo 307833 497765 := bbase (se 4 (by rfl) ⟨46665, by rfl⟩ : syracuseStep 497765 = 93331) (by norm_num)
theorem B465005 : Blo 307833 465005 := bbase (se 3 (by rfl) ⟨87188, by rfl⟩ : syracuseStep 465005 = 174377) (by norm_num)
theorem B465029 : Blo 307833 465029 := bbase (se 4 (by rfl) ⟨43596, by rfl⟩ : syracuseStep 465029 = 87193) (by norm_num)
theorem B694421 : Blo 307833 694421 := bbase (se 6 (by rfl) ⟨16275, by rfl⟩ : syracuseStep 694421 = 32551) (by norm_num)
theorem B465053 : Blo 307833 465053 := bbase (se 3 (by rfl) ⟨87197, by rfl⟩ : syracuseStep 465053 = 174395) (by norm_num)
theorem B465077 : Blo 307833 465077 := bbase (se 5 (by rfl) ⟨21800, by rfl⟩ : syracuseStep 465077 = 43601) (by norm_num)
theorem B465101 : Blo 307833 465101 := bbase (se 3 (by rfl) ⟨87206, by rfl⟩ : syracuseStep 465101 = 174413) (by norm_num)
theorem B694493 : Blo 307833 694493 := bbase (se 3 (by rfl) ⟨130217, by rfl⟩ : syracuseStep 694493 = 260435) (by norm_num)
theorem B465125 : Blo 307833 465125 := bbase (se 4 (by rfl) ⟨43605, by rfl⟩ : syracuseStep 465125 = 87211) (by norm_num)
theorem B465149 : Blo 307833 465149 := bbase (se 3 (by rfl) ⟨87215, by rfl⟩ : syracuseStep 465149 = 174431) (by norm_num)
theorem B661765 : Blo 307833 661765 := bbase (se 4 (by rfl) ⟨62040, by rfl⟩ : syracuseStep 661765 = 124081) (by norm_num)
theorem B465173 : Blo 307833 465173 := bbase (se 6 (by rfl) ⟨10902, by rfl⟩ : syracuseStep 465173 = 21805) (by norm_num)
theorem B694565 : Blo 307833 694565 := bbase (se 4 (by rfl) ⟨65115, by rfl⟩ : syracuseStep 694565 = 130231) (by norm_num)
theorem B465197 : Blo 307833 465197 := bbase (se 3 (by rfl) ⟨87224, by rfl⟩ : syracuseStep 465197 = 174449) (by norm_num)
theorem B465221 : Blo 307833 465221 := bbase (se 4 (by rfl) ⟨43614, by rfl⟩ : syracuseStep 465221 = 87229) (by norm_num)
theorem B465245 : Blo 307833 465245 := bbase (se 3 (by rfl) ⟨87233, by rfl⟩ : syracuseStep 465245 = 174467) (by norm_num)
theorem B694637 : Blo 307833 694637 := bbase (se 3 (by rfl) ⟨130244, by rfl⟩ : syracuseStep 694637 = 260489) (by norm_num)
theorem B465269 : Blo 307833 465269 := bbase (se 5 (by rfl) ⟨21809, by rfl⟩ : syracuseStep 465269 = 43619) (by norm_num)
theorem B465293 : Blo 307833 465293 := bbase (se 3 (by rfl) ⟨87242, by rfl⟩ : syracuseStep 465293 = 174485) (by norm_num)
theorem B465317 : Blo 307833 465317 := bbase (se 4 (by rfl) ⟨43623, by rfl⟩ : syracuseStep 465317 = 87247) (by norm_num)
theorem B694709 : Blo 307833 694709 := bbase (se 5 (by rfl) ⟨32564, by rfl⟩ : syracuseStep 694709 = 65129) (by norm_num)
theorem B465341 : Blo 307833 465341 := bbase (se 3 (by rfl) ⟨87251, by rfl⟩ : syracuseStep 465341 = 174503) (by norm_num)
theorem B465365 : Blo 307833 465365 := bbase (se 7 (by rfl) ⟨5453, by rfl⟩ : syracuseStep 465365 = 10907) (by norm_num)
theorem B465389 : Blo 307833 465389 := bbase (se 3 (by rfl) ⟨87260, by rfl⟩ : syracuseStep 465389 = 174521) (by norm_num)
theorem B694781 : Blo 307833 694781 := bbase (se 3 (by rfl) ⟨130271, by rfl⟩ : syracuseStep 694781 = 260543) (by norm_num)
theorem B465413 : Blo 307833 465413 := bbase (se 4 (by rfl) ⟨43632, by rfl⟩ : syracuseStep 465413 = 87265) (by norm_num)
theorem B465437 : Blo 307833 465437 := bbase (se 3 (by rfl) ⟨87269, by rfl⟩ : syracuseStep 465437 = 174539) (by norm_num)
theorem B498221 : Blo 307833 498221 := bbase (se 3 (by rfl) ⟨93416, by rfl⟩ : syracuseStep 498221 = 186833) (by norm_num)
theorem B465461 : Blo 307833 465461 := bbase (se 5 (by rfl) ⟨21818, by rfl⟩ : syracuseStep 465461 = 43637) (by norm_num)
theorem B694853 : Blo 307833 694853 := bbase (se 4 (by rfl) ⟨65142, by rfl⟩ : syracuseStep 694853 = 130285) (by norm_num)
theorem B465485 : Blo 307833 465485 := bbase (se 3 (by rfl) ⟨87278, by rfl⟩ : syracuseStep 465485 = 174557) (by norm_num)
theorem B465509 : Blo 307833 465509 := bbase (se 4 (by rfl) ⟨43641, by rfl⟩ : syracuseStep 465509 = 87283) (by norm_num)
theorem B465533 : Blo 307833 465533 := bbase (se 3 (by rfl) ⟨87287, by rfl⟩ : syracuseStep 465533 = 174575) (by norm_num)
theorem B694925 : Blo 307833 694925 := bbase (se 3 (by rfl) ⟨130298, by rfl⟩ : syracuseStep 694925 = 260597) (by norm_num)
theorem B465557 : Blo 307833 465557 := bbase (se 6 (by rfl) ⟨10911, by rfl⟩ : syracuseStep 465557 = 21823) (by norm_num)
theorem B465581 : Blo 307833 465581 := bbase (se 3 (by rfl) ⟨87296, by rfl⟩ : syracuseStep 465581 = 174593) (by norm_num)
theorem B465605 : Blo 307833 465605 := bbase (se 4 (by rfl) ⟨43650, by rfl⟩ : syracuseStep 465605 = 87301) (by norm_num)
theorem B694997 : Blo 307833 694997 := bbase (se 7 (by rfl) ⟨8144, by rfl⟩ : syracuseStep 694997 = 16289) (by norm_num)
theorem B465629 : Blo 307833 465629 := bbase (se 3 (by rfl) ⟨87305, by rfl⟩ : syracuseStep 465629 = 174611) (by norm_num)
theorem B465653 : Blo 307833 465653 := bbase (se 5 (by rfl) ⟨21827, by rfl⟩ : syracuseStep 465653 = 43655) (by norm_num)
theorem B662269 : Blo 307833 662269 := bbase (se 3 (by rfl) ⟨124175, by rfl⟩ : syracuseStep 662269 = 248351) (by norm_num)
theorem B465677 : Blo 307833 465677 := bbase (se 3 (by rfl) ⟨87314, by rfl⟩ : syracuseStep 465677 = 174629) (by norm_num)
theorem B1317653 : Blo 307833 1317653 := bbase (se 6 (by rfl) ⟨30882, by rfl⟩ : syracuseStep 1317653 = 61765) (by norm_num)
theorem B695069 : Blo 307833 695069 := bbase (se 3 (by rfl) ⟨130325, by rfl⟩ : syracuseStep 695069 = 260651) (by norm_num)
theorem B465701 : Blo 307833 465701 := bbase (se 4 (by rfl) ⟨43659, by rfl⟩ : syracuseStep 465701 = 87319) (by norm_num)
theorem B334649 : Blo 307833 334649 := bbase (se 2 (by rfl) ⟨125493, by rfl⟩ : syracuseStep 334649 = 250987) (by norm_num)
theorem B465725 : Blo 307833 465725 := bbase (se 3 (by rfl) ⟨87323, by rfl⟩ : syracuseStep 465725 = 174647) (by norm_num)
theorem B1416005 : Blo 307833 1416005 := bbase (se 4 (by rfl) ⟨132750, by rfl⟩ : syracuseStep 1416005 = 265501) (by norm_num)
theorem B465749 : Blo 307833 465749 := bbase (se 9 (by rfl) ⟨1364, by rfl⟩ : syracuseStep 465749 = 2729) (by norm_num)
theorem B695141 : Blo 307833 695141 := bbase (se 4 (by rfl) ⟨65169, by rfl⟩ : syracuseStep 695141 = 130339) (by norm_num)
theorem B465773 : Blo 307833 465773 := bbase (se 3 (by rfl) ⟨87332, by rfl⟩ : syracuseStep 465773 = 174665) (by norm_num)
theorem B465797 : Blo 307833 465797 := bbase (se 4 (by rfl) ⟨43668, by rfl⟩ : syracuseStep 465797 = 87337) (by norm_num)
theorem B465821 : Blo 307833 465821 := bbase (se 3 (by rfl) ⟨87341, by rfl⟩ : syracuseStep 465821 = 174683) (by norm_num)
theorem B695213 : Blo 307833 695213 := bbase (se 3 (by rfl) ⟨130352, by rfl⟩ : syracuseStep 695213 = 260705) (by norm_num)
theorem B465845 : Blo 307833 465845 := bbase (se 5 (by rfl) ⟨21836, by rfl⟩ : syracuseStep 465845 = 43673) (by norm_num)
theorem B465869 : Blo 307833 465869 := bbase (se 3 (by rfl) ⟨87350, by rfl⟩ : syracuseStep 465869 = 174701) (by norm_num)
theorem B465893 : Blo 307833 465893 := bbase (se 4 (by rfl) ⟨43677, by rfl⟩ : syracuseStep 465893 = 87355) (by norm_num)
theorem B629741 : Blo 307833 629741 := bbase (se 3 (by rfl) ⟨118076, by rfl⟩ : syracuseStep 629741 = 236153) (by norm_num)
theorem B695285 : Blo 307833 695285 := bbase (se 5 (by rfl) ⟨32591, by rfl⟩ : syracuseStep 695285 = 65183) (by norm_num)
theorem B465917 : Blo 307833 465917 := bbase (se 3 (by rfl) ⟨87359, by rfl⟩ : syracuseStep 465917 = 174719) (by norm_num)
theorem B465941 : Blo 307833 465941 := bbase (se 6 (by rfl) ⟨10920, by rfl⟩ : syracuseStep 465941 = 21841) (by norm_num)
theorem B465965 : Blo 307833 465965 := bbase (se 3 (by rfl) ⟨87368, by rfl⟩ : syracuseStep 465965 = 174737) (by norm_num)
theorem B1317941 : Blo 307833 1317941 := bbase (se 5 (by rfl) ⟨61778, by rfl⟩ : syracuseStep 1317941 = 123557) (by norm_num)
theorem B695357 : Blo 307833 695357 := bbase (se 3 (by rfl) ⟨130379, by rfl⟩ : syracuseStep 695357 = 260759) (by norm_num)
theorem B465989 : Blo 307833 465989 := bbase (se 4 (by rfl) ⟨43686, by rfl⟩ : syracuseStep 465989 = 87373) (by norm_num)
theorem B466013 : Blo 307833 466013 := bbase (se 3 (by rfl) ⟨87377, by rfl⟩ : syracuseStep 466013 = 174755) (by norm_num)
theorem B466037 : Blo 307833 466037 := bbase (se 5 (by rfl) ⟨21845, by rfl⟩ : syracuseStep 466037 = 43691) (by norm_num)
theorem B695429 : Blo 307833 695429 := bbase (se 4 (by rfl) ⟨65196, by rfl⟩ : syracuseStep 695429 = 130393) (by norm_num)
theorem B466061 : Blo 307833 466061 := bbase (se 3 (by rfl) ⟨87386, by rfl⟩ : syracuseStep 466061 = 174773) (by norm_num)
theorem B466085 : Blo 307833 466085 := bbase (se 4 (by rfl) ⟨43695, by rfl⟩ : syracuseStep 466085 = 87391) (by norm_num)
theorem B335021 : Blo 307833 335021 := bbase (se 3 (by rfl) ⟨62816, by rfl⟩ : syracuseStep 335021 = 125633) (by norm_num)
theorem B466109 : Blo 307833 466109 := bbase (se 3 (by rfl) ⟨87395, by rfl⟩ : syracuseStep 466109 = 174791) (by norm_num)
theorem B695501 : Blo 307833 695501 := bbase (se 3 (by rfl) ⟨130406, by rfl⟩ : syracuseStep 695501 = 260813) (by norm_num)
theorem B466133 : Blo 307833 466133 := bbase (se 7 (by rfl) ⟨5462, by rfl⟩ : syracuseStep 466133 = 10925) (by norm_num)
theorem B466157 : Blo 307833 466157 := bbase (se 3 (by rfl) ⟨87404, by rfl⟩ : syracuseStep 466157 = 174809) (by norm_num)
theorem B466181 : Blo 307833 466181 := bbase (se 4 (by rfl) ⟨43704, by rfl⟩ : syracuseStep 466181 = 87409) (by norm_num)
theorem B695573 : Blo 307833 695573 := bbase (se 6 (by rfl) ⟨16302, by rfl⟩ : syracuseStep 695573 = 32605) (by norm_num)
theorem B466205 : Blo 307833 466205 := bbase (se 3 (by rfl) ⟨87413, by rfl⟩ : syracuseStep 466205 = 174827) (by norm_num)
theorem B466229 : Blo 307833 466229 := bbase (se 5 (by rfl) ⟨21854, by rfl⟩ : syracuseStep 466229 = 43709) (by norm_num)
theorem B466253 : Blo 307833 466253 := bbase (se 3 (by rfl) ⟨87422, by rfl⟩ : syracuseStep 466253 = 174845) (by norm_num)
theorem B695645 : Blo 307833 695645 := bbase (se 3 (by rfl) ⟨130433, by rfl⟩ : syracuseStep 695645 = 260867) (by norm_num)
theorem B466277 : Blo 307833 466277 := bbase (se 4 (by rfl) ⟨43713, by rfl⟩ : syracuseStep 466277 = 87427) (by norm_num)
theorem B466301 : Blo 307833 466301 := bbase (se 3 (by rfl) ⟨87431, by rfl⟩ : syracuseStep 466301 = 174863) (by norm_num)
theorem B466325 : Blo 307833 466325 := bbase (se 6 (by rfl) ⟨10929, by rfl⟩ : syracuseStep 466325 = 21859) (by norm_num)
theorem B695717 : Blo 307833 695717 := bbase (se 4 (by rfl) ⟨65223, by rfl⟩ : syracuseStep 695717 = 130447) (by norm_num)
theorem B1121701 : Blo 307833 1121701 := bbase (se 4 (by rfl) ⟨105159, by rfl⟩ : syracuseStep 1121701 = 210319) (by norm_num)
theorem B466349 : Blo 307833 466349 := bbase (se 3 (by rfl) ⟨87440, by rfl⟩ : syracuseStep 466349 = 174881) (by norm_num)
theorem B466373 : Blo 307833 466373 := bbase (se 4 (by rfl) ⟨43722, by rfl⟩ : syracuseStep 466373 = 87445) (by norm_num)
theorem B466397 : Blo 307833 466397 := bbase (se 3 (by rfl) ⟨87449, by rfl⟩ : syracuseStep 466397 = 174899) (by norm_num)
theorem B695789 : Blo 307833 695789 := bbase (se 3 (by rfl) ⟨130460, by rfl⟩ : syracuseStep 695789 = 260921) (by norm_num)
theorem B466421 : Blo 307833 466421 := bbase (se 5 (by rfl) ⟨21863, by rfl⟩ : syracuseStep 466421 = 43727) (by norm_num)
theorem B466445 : Blo 307833 466445 := bbase (se 3 (by rfl) ⟨87458, by rfl⟩ : syracuseStep 466445 = 174917) (by norm_num)
theorem B499213 : Blo 307833 499213 := bbase (se 3 (by rfl) ⟨93602, by rfl⟩ : syracuseStep 499213 = 187205) (by norm_num)
theorem B466469 : Blo 307833 466469 := bbase (se 4 (by rfl) ⟨43731, by rfl⟩ : syracuseStep 466469 = 87463) (by norm_num)
theorem B695861 : Blo 307833 695861 := bbase (se 5 (by rfl) ⟨32618, by rfl⟩ : syracuseStep 695861 = 65237) (by norm_num)
theorem B466493 : Blo 307833 466493 := bbase (se 3 (by rfl) ⟨87467, by rfl⟩ : syracuseStep 466493 = 174935) (by norm_num)
theorem B466517 : Blo 307833 466517 := bbase (se 8 (by rfl) ⟨2733, by rfl⟩ : syracuseStep 466517 = 5467) (by norm_num)
theorem B466541 : Blo 307833 466541 := bbase (se 3 (by rfl) ⟨87476, by rfl⟩ : syracuseStep 466541 = 174953) (by norm_num)
theorem B663157 : Blo 307833 663157 := bbase (se 5 (by rfl) ⟨31085, by rfl⟩ : syracuseStep 663157 = 62171) (by norm_num)
theorem B695933 : Blo 307833 695933 := bbase (se 3 (by rfl) ⟨130487, by rfl⟩ : syracuseStep 695933 = 260975) (by norm_num)
theorem B466565 : Blo 307833 466565 := bbase (se 4 (by rfl) ⟨43740, by rfl⟩ : syracuseStep 466565 = 87481) (by norm_num)
theorem B466589 : Blo 307833 466589 := bbase (se 3 (by rfl) ⟨87485, by rfl⟩ : syracuseStep 466589 = 174971) (by norm_num)
theorem B466613 : Blo 307833 466613 := bbase (se 5 (by rfl) ⟨21872, by rfl⟩ : syracuseStep 466613 = 43745) (by norm_num)
theorem B335549 : Blo 307833 335549 := bbase (se 3 (by rfl) ⟨62915, by rfl⟩ : syracuseStep 335549 = 125831) (by norm_num)
theorem B990917 : Blo 307833 990917 := bbase (se 4 (by rfl) ⟨92898, by rfl⟩ : syracuseStep 990917 = 185797) (by norm_num)
theorem B696005 : Blo 307833 696005 := bbase (se 4 (by rfl) ⟨65250, by rfl⟩ : syracuseStep 696005 = 130501) (by norm_num)
theorem B466637 : Blo 307833 466637 := bbase (se 3 (by rfl) ⟨87494, by rfl⟩ : syracuseStep 466637 = 174989) (by norm_num)
theorem B466661 : Blo 307833 466661 := bbase (se 4 (by rfl) ⟨43749, by rfl⟩ : syracuseStep 466661 = 87499) (by norm_num)
theorem B1679093 : Blo 307833 1679093 := bbase (se 5 (by rfl) ⟨78707, by rfl⟩ : syracuseStep 1679093 = 157415) (by norm_num)
theorem B466685 : Blo 307833 466685 := bbase (se 3 (by rfl) ⟨87503, by rfl⟩ : syracuseStep 466685 = 175007) (by norm_num)
theorem B696077 : Blo 307833 696077 := bbase (se 3 (by rfl) ⟨130514, by rfl⟩ : syracuseStep 696077 = 261029) (by norm_num)
theorem B466709 : Blo 307833 466709 := bbase (se 6 (by rfl) ⟨10938, by rfl⟩ : syracuseStep 466709 = 21877) (by norm_num)
theorem B1318693 : Blo 307833 1318693 := bbase (se 4 (by rfl) ⟨123627, by rfl⟩ : syracuseStep 1318693 = 247255) (by norm_num)
theorem B466733 : Blo 307833 466733 := bbase (se 3 (by rfl) ⟨87512, by rfl⟩ : syracuseStep 466733 = 175025) (by norm_num)
theorem B991045 : Blo 307833 991045 := bbase (se 4 (by rfl) ⟨92910, by rfl⟩ : syracuseStep 991045 = 185821) (by norm_num)
theorem B466757 : Blo 307833 466757 := bbase (se 4 (by rfl) ⟨43758, by rfl⟩ : syracuseStep 466757 = 87517) (by norm_num)
theorem B696149 : Blo 307833 696149 := bbase (se 9 (by rfl) ⟨2039, by rfl⟩ : syracuseStep 696149 = 4079) (by norm_num)
theorem B466781 : Blo 307833 466781 := bbase (se 3 (by rfl) ⟨87521, by rfl⟩ : syracuseStep 466781 = 175043) (by norm_num)
theorem B466805 : Blo 307833 466805 := bbase (se 5 (by rfl) ⟨21881, by rfl⟩ : syracuseStep 466805 = 43763) (by norm_num)
theorem B466829 : Blo 307833 466829 := bbase (se 3 (by rfl) ⟨87530, by rfl⟩ : syracuseStep 466829 = 175061) (by norm_num)
theorem B696221 : Blo 307833 696221 := bbase (se 3 (by rfl) ⟨130541, by rfl⟩ : syracuseStep 696221 = 261083) (by norm_num)
theorem B466853 : Blo 307833 466853 := bbase (se 4 (by rfl) ⟨43767, by rfl⟩ : syracuseStep 466853 = 87535) (by norm_num)
theorem B466877 : Blo 307833 466877 := bbase (se 3 (by rfl) ⟨87539, by rfl⟩ : syracuseStep 466877 = 175079) (by norm_num)
theorem B466901 : Blo 307833 466901 := bbase (se 7 (by rfl) ⟨5471, by rfl⟩ : syracuseStep 466901 = 10943) (by norm_num)
theorem B1482725 : Blo 307833 1482725 := bbase (se 4 (by rfl) ⟨139005, by rfl⟩ : syracuseStep 1482725 = 278011) (by norm_num)
theorem B696293 : Blo 307833 696293 := bbase (se 4 (by rfl) ⟨65277, by rfl⟩ : syracuseStep 696293 = 130555) (by norm_num)
theorem B466925 : Blo 307833 466925 := bbase (se 3 (by rfl) ⟨87548, by rfl⟩ : syracuseStep 466925 = 175097) (by norm_num)
theorem B466949 : Blo 307833 466949 := bbase (se 4 (by rfl) ⟨43776, by rfl⟩ : syracuseStep 466949 = 87553) (by norm_num)
theorem B466973 : Blo 307833 466973 := bbase (se 3 (by rfl) ⟨87557, by rfl⟩ : syracuseStep 466973 = 175115) (by norm_num)
theorem B696365 : Blo 307833 696365 := bbase (se 3 (by rfl) ⟨130568, by rfl⟩ : syracuseStep 696365 = 261137) (by norm_num)
theorem B466997 : Blo 307833 466997 := bbase (se 5 (by rfl) ⟨21890, by rfl⟩ : syracuseStep 466997 = 43781) (by norm_num)
theorem B467021 : Blo 307833 467021 := bbase (se 3 (by rfl) ⟨87566, by rfl⟩ : syracuseStep 467021 = 175133) (by norm_num)
theorem B663653 : Blo 307833 663653 := bbase (se 4 (by rfl) ⟨62217, by rfl⟩ : syracuseStep 663653 = 124435) (by norm_num)
theorem B467045 : Blo 307833 467045 := bbase (se 4 (by rfl) ⟨43785, by rfl⟩ : syracuseStep 467045 = 87571) (by norm_num)
theorem B696437 : Blo 307833 696437 := bbase (se 5 (by rfl) ⟨32645, by rfl⟩ : syracuseStep 696437 = 65291) (by norm_num)
theorem B467069 : Blo 307833 467069 := bbase (se 3 (by rfl) ⟨87575, by rfl⟩ : syracuseStep 467069 = 175151) (by norm_num)
theorem B467093 : Blo 307833 467093 := bbase (se 6 (by rfl) ⟨10947, by rfl⟩ : syracuseStep 467093 = 21895) (by norm_num)
theorem B467117 : Blo 307833 467117 := bbase (se 3 (by rfl) ⟨87584, by rfl⟩ : syracuseStep 467117 = 175169) (by norm_num)
theorem B696509 : Blo 307833 696509 := bbase (se 3 (by rfl) ⟨130595, by rfl⟩ : syracuseStep 696509 = 261191) (by norm_num)
theorem B467141 : Blo 307833 467141 := bbase (se 4 (by rfl) ⟨43794, by rfl⟩ : syracuseStep 467141 = 87589) (by norm_num)
theorem B467165 : Blo 307833 467165 := bbase (se 3 (by rfl) ⟨87593, by rfl⟩ : syracuseStep 467165 = 175187) (by norm_num)
theorem B467189 : Blo 307833 467189 := bbase (se 5 (by rfl) ⟨21899, by rfl⟩ : syracuseStep 467189 = 43799) (by norm_num)
theorem B696581 : Blo 307833 696581 := bbase (se 4 (by rfl) ⟨65304, by rfl⟩ : syracuseStep 696581 = 130609) (by norm_num)
theorem B467213 : Blo 307833 467213 := bbase (se 3 (by rfl) ⟨87602, by rfl⟩ : syracuseStep 467213 = 175205) (by norm_num)
theorem B467237 : Blo 307833 467237 := bbase (se 4 (by rfl) ⟨43803, by rfl⟩ : syracuseStep 467237 = 87607) (by norm_num)
theorem B467261 : Blo 307833 467261 := bbase (se 3 (by rfl) ⟨87611, by rfl⟩ : syracuseStep 467261 = 175223) (by norm_num)
theorem B696653 : Blo 307833 696653 := bbase (se 3 (by rfl) ⟨130622, by rfl⟩ : syracuseStep 696653 = 261245) (by norm_num)
theorem B467285 : Blo 307833 467285 := bbase (se 10 (by rfl) ⟨684, by rfl⟩ : syracuseStep 467285 = 1369) (by norm_num)
theorem B467309 : Blo 307833 467309 := bbase (se 3 (by rfl) ⟨87620, by rfl⟩ : syracuseStep 467309 = 175241) (by norm_num)
theorem B1188229 : Blo 307833 1188229 := bbase (se 4 (by rfl) ⟨111396, by rfl⟩ : syracuseStep 1188229 = 222793) (by norm_num)
theorem B467333 : Blo 307833 467333 := bbase (se 4 (by rfl) ⟨43812, by rfl⟩ : syracuseStep 467333 = 87625) (by norm_num)
theorem B696725 : Blo 307833 696725 := bbase (se 6 (by rfl) ⟨16329, by rfl⟩ : syracuseStep 696725 = 32659) (by norm_num)
theorem B467357 : Blo 307833 467357 := bbase (se 3 (by rfl) ⟨87629, by rfl⟩ : syracuseStep 467357 = 175259) (by norm_num)
theorem B467381 : Blo 307833 467381 := bbase (se 5 (by rfl) ⟨21908, by rfl⟩ : syracuseStep 467381 = 43817) (by norm_num)
theorem B467405 : Blo 307833 467405 := bbase (se 3 (by rfl) ⟨87638, by rfl⟩ : syracuseStep 467405 = 175277) (by norm_num)
theorem B696797 : Blo 307833 696797 := bbase (se 3 (by rfl) ⟨130649, by rfl⟩ : syracuseStep 696797 = 261299) (by norm_num)
theorem B467429 : Blo 307833 467429 := bbase (se 4 (by rfl) ⟨43821, by rfl⟩ : syracuseStep 467429 = 87643) (by norm_num)
theorem B467453 : Blo 307833 467453 := bbase (se 3 (by rfl) ⟨87647, by rfl⟩ : syracuseStep 467453 = 175295) (by norm_num)
theorem B1319429 : Blo 307833 1319429 := bbase (se 4 (by rfl) ⟨123696, by rfl⟩ : syracuseStep 1319429 = 247393) (by norm_num)
theorem B467477 : Blo 307833 467477 := bbase (se 6 (by rfl) ⟨10956, by rfl⟩ : syracuseStep 467477 = 21913) (by norm_num)
theorem B696869 : Blo 307833 696869 := bbase (se 4 (by rfl) ⟨65331, by rfl⟩ : syracuseStep 696869 = 130663) (by norm_num)
theorem B467501 : Blo 307833 467501 := bbase (se 3 (by rfl) ⟨87656, by rfl⟩ : syracuseStep 467501 = 175313) (by norm_num)
theorem B467525 : Blo 307833 467525 := bbase (se 4 (by rfl) ⟨43830, by rfl⟩ : syracuseStep 467525 = 87661) (by norm_num)
theorem B467549 : Blo 307833 467549 := bbase (se 3 (by rfl) ⟨87665, by rfl⟩ : syracuseStep 467549 = 175331) (by norm_num)
theorem B696941 : Blo 307833 696941 := bbase (se 3 (by rfl) ⟨130676, by rfl⟩ : syracuseStep 696941 = 261353) (by norm_num)
theorem B631405 : Blo 307833 631405 := bbase (se 3 (by rfl) ⟨118388, by rfl⟩ : syracuseStep 631405 = 236777) (by norm_num)
theorem B467573 : Blo 307833 467573 := bbase (se 5 (by rfl) ⟨21917, by rfl⟩ : syracuseStep 467573 = 43835) (by norm_num)
theorem B467597 : Blo 307833 467597 := bbase (se 3 (by rfl) ⟨87674, by rfl⟩ : syracuseStep 467597 = 175349) (by norm_num)
theorem B467621 : Blo 307833 467621 := bbase (se 4 (by rfl) ⟨43839, by rfl⟩ : syracuseStep 467621 = 87679) (by norm_num)
theorem B697013 : Blo 307833 697013 := bbase (se 5 (by rfl) ⟨32672, by rfl⟩ : syracuseStep 697013 = 65345) (by norm_num)
theorem B467645 : Blo 307833 467645 := bbase (se 3 (by rfl) ⟨87683, by rfl⟩ : syracuseStep 467645 = 175367) (by norm_num)
theorem B467669 : Blo 307833 467669 := bbase (se 7 (by rfl) ⟨5480, by rfl⟩ : syracuseStep 467669 = 10961) (by norm_num)
theorem B467693 : Blo 307833 467693 := bbase (se 3 (by rfl) ⟨87692, by rfl⟩ : syracuseStep 467693 = 175385) (by norm_num)
theorem B697085 : Blo 307833 697085 := bbase (se 3 (by rfl) ⟨130703, by rfl⟩ : syracuseStep 697085 = 261407) (by norm_num)
theorem B467717 : Blo 307833 467717 := bbase (se 4 (by rfl) ⟨43848, by rfl⟩ : syracuseStep 467717 = 87697) (by norm_num)
theorem B467741 : Blo 307833 467741 := bbase (se 3 (by rfl) ⟨87701, by rfl⟩ : syracuseStep 467741 = 175403) (by norm_num)
theorem B697157 : Blo 307833 697157 := bbase (se 4 (by rfl) ⟨65358, by rfl⟩ : syracuseStep 697157 = 130717) (by norm_num)
theorem B697229 : Blo 307833 697229 := bbase (se 3 (by rfl) ⟨130730, by rfl⟩ : syracuseStep 697229 = 261461) (by norm_num)
theorem B1254325 : Blo 307833 1254325 := bbase (se 5 (by rfl) ⟨58796, by rfl⟩ : syracuseStep 1254325 = 117593) (by norm_num)
theorem B697301 : Blo 307833 697301 := bbase (se 7 (by rfl) ⟨8171, by rfl⟩ : syracuseStep 697301 = 16343) (by norm_num)
theorem B664541 : Blo 307833 664541 := bbase (se 3 (by rfl) ⟨124601, by rfl⟩ : syracuseStep 664541 = 249203) (by norm_num)
theorem B697373 : Blo 307833 697373 := bbase (se 3 (by rfl) ⟨130757, by rfl⟩ : syracuseStep 697373 = 261515) (by norm_num)
theorem B664661 : Blo 307833 664661 := bbase (se 8 (by rfl) ⟨3894, by rfl⟩ : syracuseStep 664661 = 7789) (by norm_num)
theorem B697445 : Blo 307833 697445 := bbase (se 4 (by rfl) ⟨65385, by rfl⟩ : syracuseStep 697445 = 130771) (by norm_num)
theorem B697517 : Blo 307833 697517 := bbase (se 3 (by rfl) ⟨130784, by rfl⟩ : syracuseStep 697517 = 261569) (by norm_num)
theorem B337081 : Blo 307833 337081 := bbase (se 2 (by rfl) ⟨126405, by rfl⟩ : syracuseStep 337081 = 252811) (by norm_num)
theorem B697589 : Blo 307833 697589 := bbase (se 5 (by rfl) ⟨32699, by rfl⟩ : syracuseStep 697589 = 65399) (by norm_num)
theorem B697661 : Blo 307833 697661 := bbase (se 3 (by rfl) ⟨130811, by rfl⟩ : syracuseStep 697661 = 261623) (by norm_num)
theorem B370013 : Blo 307833 370013 := bbase (se 3 (by rfl) ⟨69377, by rfl⟩ : syracuseStep 370013 = 138755) (by norm_num)
theorem B697733 : Blo 307833 697733 := bbase (se 4 (by rfl) ⟨65412, by rfl⟩ : syracuseStep 697733 = 130825) (by norm_num)
theorem B697805 : Blo 307833 697805 := bbase (se 3 (by rfl) ⟨130838, by rfl⟩ : syracuseStep 697805 = 261677) (by norm_num)
theorem B697877 : Blo 307833 697877 := bbase (se 6 (by rfl) ⟨16356, by rfl⟩ : syracuseStep 697877 = 32713) (by norm_num)
theorem B534101 : Blo 307833 534101 := bbase (se 8 (by rfl) ⟨3129, by rfl⟩ : syracuseStep 534101 = 6259) (by norm_num)
theorem B697949 : Blo 307833 697949 := bbase (se 3 (by rfl) ⟨130865, by rfl⟩ : syracuseStep 697949 = 261731) (by norm_num)
theorem B698021 : Blo 307833 698021 := bbase (se 4 (by rfl) ⟨65439, by rfl⟩ : syracuseStep 698021 = 130879) (by norm_num)
theorem B370345 : Blo 307833 370345 := bbase (se 2 (by rfl) ⟨138879, by rfl⟩ : syracuseStep 370345 = 277759) (by norm_num)
theorem B665293 : Blo 307833 665293 := bbase (se 3 (by rfl) ⟨124742, by rfl⟩ : syracuseStep 665293 = 249485) (by norm_num)
theorem B698093 : Blo 307833 698093 := bbase (se 3 (by rfl) ⟨130892, by rfl⟩ : syracuseStep 698093 = 261785) (by norm_num)
theorem B698165 : Blo 307833 698165 := bbase (se 5 (by rfl) ⟨32726, by rfl⟩ : syracuseStep 698165 = 65453) (by norm_num)
theorem B370489 : Blo 307833 370489 := bbase (se 2 (by rfl) ⟨138933, by rfl⟩ : syracuseStep 370489 = 277867) (by norm_num)
theorem B698237 : Blo 307833 698237 := bbase (se 3 (by rfl) ⟨130919, by rfl⟩ : syracuseStep 698237 = 261839) (by norm_num)
theorem B698309 : Blo 307833 698309 := bbase (se 4 (by rfl) ⟨65466, by rfl⟩ : syracuseStep 698309 = 130933) (by norm_num)
theorem B698381 : Blo 307833 698381 := bbase (se 3 (by rfl) ⟨130946, by rfl⟩ : syracuseStep 698381 = 261893) (by norm_num)
theorem B698453 : Blo 307833 698453 := bbase (se 8 (by rfl) ⟨4092, by rfl⟩ : syracuseStep 698453 = 8185) (by norm_num)
theorem B698525 : Blo 307833 698525 := bbase (se 3 (by rfl) ⟨130973, by rfl⟩ : syracuseStep 698525 = 261947) (by norm_num)
theorem B1976501 : Blo 307833 1976501 := bbase (se 5 (by rfl) ⟨92648, by rfl⟩ : syracuseStep 1976501 = 185297) (by norm_num)
theorem B2238677 : Blo 307833 2238677 := bbase (se 7 (by rfl) ⟨26234, by rfl⟩ : syracuseStep 2238677 = 52469) (by norm_num)
theorem B698597 : Blo 307833 698597 := bbase (se 4 (by rfl) ⟨65493, by rfl⟩ : syracuseStep 698597 = 130987) (by norm_num)
theorem B1059077 : Blo 307833 1059077 := bbase (se 4 (by rfl) ⟨99288, by rfl⟩ : syracuseStep 1059077 = 198577) (by norm_num)
theorem B698669 : Blo 307833 698669 := bbase (se 3 (by rfl) ⟨131000, by rfl⟩ : syracuseStep 698669 = 262001) (by norm_num)
theorem B698741 : Blo 307833 698741 := bbase (se 5 (by rfl) ⟨32753, by rfl⟩ : syracuseStep 698741 = 65507) (by norm_num)
theorem B567685 : Blo 307833 567685 := bbase (se 4 (by rfl) ⟨53220, by rfl⟩ : syracuseStep 567685 = 106441) (by norm_num)
theorem B1583525 : Blo 307833 1583525 := bbase (se 4 (by rfl) ⟨148455, by rfl⟩ : syracuseStep 1583525 = 296911) (by norm_num)
theorem B698813 : Blo 307833 698813 := bbase (se 3 (by rfl) ⟨131027, by rfl⟩ : syracuseStep 698813 = 262055) (by norm_num)
theorem B698885 : Blo 307833 698885 := bbase (se 4 (by rfl) ⟨65520, by rfl⟩ : syracuseStep 698885 = 131041) (by norm_num)
theorem B698957 : Blo 307833 698957 := bbase (se 3 (by rfl) ⟨131054, by rfl⟩ : syracuseStep 698957 = 262109) (by norm_num)
theorem B1780309 : Blo 307833 1780309 := bbase (se 8 (by rfl) ⟨10431, by rfl⟩ : syracuseStep 1780309 = 20863) (by norm_num)
theorem B993941 : Blo 307833 993941 := bbase (se 6 (by rfl) ⟨23295, by rfl⟩ : syracuseStep 993941 = 46591) (by norm_num)
theorem B699029 : Blo 307833 699029 := bbase (se 6 (by rfl) ⟨16383, by rfl⟩ : syracuseStep 699029 = 32767) (by norm_num)
theorem B699101 : Blo 307833 699101 := bbase (se 3 (by rfl) ⟨131081, by rfl⟩ : syracuseStep 699101 = 262163) (by norm_num)
theorem B699173 : Blo 307833 699173 := bbase (se 4 (by rfl) ⟨65547, by rfl⟩ : syracuseStep 699173 = 131095) (by norm_num)
theorem B371513 : Blo 307833 371513 := bbase (se 2 (by rfl) ⟨139317, by rfl⟩ : syracuseStep 371513 = 278635) (by norm_num)
theorem B699245 : Blo 307833 699245 := bbase (se 3 (by rfl) ⟨131108, by rfl⟩ : syracuseStep 699245 = 262217) (by norm_num)
theorem B699317 : Blo 307833 699317 := bbase (se 5 (by rfl) ⟨32780, by rfl⟩ : syracuseStep 699317 = 65561) (by norm_num)
theorem B699389 : Blo 307833 699389 := bbase (se 3 (by rfl) ⟨131135, by rfl⟩ : syracuseStep 699389 = 262271) (by norm_num)
theorem B3550229 : Blo 307833 3550229 := bbase (se 6 (by rfl) ⟨83208, by rfl⟩ : syracuseStep 3550229 = 166417) (by norm_num)
theorem B699461 : Blo 307833 699461 := bbase (se 4 (by rfl) ⟨65574, by rfl⟩ : syracuseStep 699461 = 131149) (by norm_num)
theorem B699533 : Blo 307833 699533 := bbase (se 3 (by rfl) ⟨131162, by rfl⟩ : syracuseStep 699533 = 262325) (by norm_num)
theorem B1256629 : Blo 307833 1256629 := bbase (se 5 (by rfl) ⟨58904, by rfl⟩ : syracuseStep 1256629 = 117809) (by norm_num)
theorem B699605 : Blo 307833 699605 := bbase (se 7 (by rfl) ⟨8198, by rfl⟩ : syracuseStep 699605 = 16397) (by norm_num)
theorem B699677 : Blo 307833 699677 := bbase (se 3 (by rfl) ⟨131189, by rfl⟩ : syracuseStep 699677 = 262379) (by norm_num)
theorem B699749 : Blo 307833 699749 := bbase (se 4 (by rfl) ⟨65601, by rfl⟩ : syracuseStep 699749 = 131203) (by norm_num)
theorem B699821 : Blo 307833 699821 := bbase (se 3 (by rfl) ⟨131216, by rfl⟩ : syracuseStep 699821 = 262433) (by norm_num)
theorem B699893 : Blo 307833 699893 := bbase (se 5 (by rfl) ⟨32807, by rfl⟩ : syracuseStep 699893 = 65615) (by norm_num)
theorem B699965 : Blo 307833 699965 := bbase (se 3 (by rfl) ⟨131243, by rfl⟩ : syracuseStep 699965 = 262487) (by norm_num)
theorem B700037 : Blo 307833 700037 := bbase (se 4 (by rfl) ⟨65628, by rfl⟩ : syracuseStep 700037 = 131257) (by norm_num)
theorem B700109 : Blo 307833 700109 := bbase (se 3 (by rfl) ⟨131270, by rfl⟩ : syracuseStep 700109 = 262541) (by norm_num)
theorem B1322725 : Blo 307833 1322725 := bbase (se 4 (by rfl) ⟨124005, by rfl⟩ : syracuseStep 1322725 = 248011) (by norm_num)
theorem B700181 : Blo 307833 700181 := bbase (se 6 (by rfl) ⟨16410, by rfl⟩ : syracuseStep 700181 = 32821) (by norm_num)
theorem B700253 : Blo 307833 700253 := bbase (se 3 (by rfl) ⟨131297, by rfl⟩ : syracuseStep 700253 = 262595) (by norm_num)
theorem B2240405 : Blo 307833 2240405 := bbase (se 6 (by rfl) ⟨52509, by rfl⟩ : syracuseStep 2240405 = 105019) (by norm_num)
theorem B700325 : Blo 307833 700325 := bbase (se 4 (by rfl) ⟨65655, by rfl⟩ : syracuseStep 700325 = 131311) (by norm_num)
theorem B372709 : Blo 307833 372709 := bbase (se 4 (by rfl) ⟨34941, by rfl⟩ : syracuseStep 372709 = 69883) (by norm_num)
theorem B700397 : Blo 307833 700397 := bbase (se 3 (by rfl) ⟨131324, by rfl⟩ : syracuseStep 700397 = 262649) (by norm_num)
theorem B372781 : Blo 307833 372781 := bbase (se 3 (by rfl) ⟨69896, by rfl⟩ : syracuseStep 372781 = 139793) (by norm_num)
theorem B700469 : Blo 307833 700469 := bbase (se 5 (by rfl) ⟨32834, by rfl⟩ : syracuseStep 700469 = 65669) (by norm_num)
theorem B2535509 : Blo 307833 2535509 := bbase (se 8 (by rfl) ⟨14856, by rfl⟩ : syracuseStep 2535509 = 29713) (by norm_num)
theorem B700541 : Blo 307833 700541 := bbase (se 3 (by rfl) ⟨131351, by rfl⟩ : syracuseStep 700541 = 262703) (by norm_num)
theorem B700613 : Blo 307833 700613 := bbase (se 4 (by rfl) ⟨65682, by rfl⟩ : syracuseStep 700613 = 131365) (by norm_num)
theorem B700685 : Blo 307833 700685 := bbase (se 3 (by rfl) ⟨131378, by rfl⟩ : syracuseStep 700685 = 262757) (by norm_num)
theorem B700757 : Blo 307833 700757 := bbase (se 10 (by rfl) ⟨1026, by rfl⟩ : syracuseStep 700757 = 2053) (by norm_num)
theorem B438653 : Blo 307833 438653 := bbase (se 3 (by rfl) ⟨82247, by rfl⟩ : syracuseStep 438653 = 164495) (by norm_num)
theorem B700829 : Blo 307833 700829 := bbase (se 3 (by rfl) ⟨131405, by rfl⟩ : syracuseStep 700829 = 262811) (by norm_num)
theorem B438733 : Blo 307833 438733 := bbase (se 3 (by rfl) ⟨82262, by rfl⟩ : syracuseStep 438733 = 164525) (by norm_num)
theorem B700901 : Blo 307833 700901 := bbase (se 4 (by rfl) ⟨65709, by rfl⟩ : syracuseStep 700901 = 131419) (by norm_num)
theorem B700973 : Blo 307833 700973 := bbase (se 3 (by rfl) ⟨131432, by rfl⟩ : syracuseStep 700973 = 262865) (by norm_num)
theorem B438853 : Blo 307833 438853 := bbase (se 4 (by rfl) ⟨41142, by rfl⟩ : syracuseStep 438853 = 82285) (by norm_num)
theorem B701045 : Blo 307833 701045 := bbase (se 5 (by rfl) ⟨32861, by rfl⟩ : syracuseStep 701045 = 65723) (by norm_num)
theorem B438949 : Blo 307833 438949 := bbase (se 4 (by rfl) ⟨41151, by rfl⟩ : syracuseStep 438949 = 82303) (by norm_num)
theorem B701117 : Blo 307833 701117 := bbase (se 3 (by rfl) ⟨131459, by rfl⟩ : syracuseStep 701117 = 262919) (by norm_num)
theorem B1487605 : Blo 307833 1487605 := bbase (se 5 (by rfl) ⟨69731, by rfl⟩ : syracuseStep 1487605 = 139463) (by norm_num)
theorem B701189 : Blo 307833 701189 := bbase (se 4 (by rfl) ⟨65736, by rfl⟩ : syracuseStep 701189 = 131473) (by norm_num)
theorem B996133 : Blo 307833 996133 := bbase (se 4 (by rfl) ⟨93387, by rfl⟩ : syracuseStep 996133 = 186775) (by norm_num)
theorem B701261 : Blo 307833 701261 := bbase (se 3 (by rfl) ⟨131486, by rfl⟩ : syracuseStep 701261 = 262973) (by norm_num)
theorem B471917 : Blo 307833 471917 := bbase (se 3 (by rfl) ⟨88484, by rfl⟩ : syracuseStep 471917 = 176969) (by norm_num)
theorem B1880981 : Blo 307833 1880981 := bbase (se 6 (by rfl) ⟨44085, by rfl⟩ : syracuseStep 1880981 = 88171) (by norm_num)
theorem B701333 : Blo 307833 701333 := bbase (se 6 (by rfl) ⟨16437, by rfl⟩ : syracuseStep 701333 = 32875) (by norm_num)
theorem B471997 : Blo 307833 471997 := bbase (se 3 (by rfl) ⟨88499, by rfl⟩ : syracuseStep 471997 = 176999) (by norm_num)
theorem B701405 : Blo 307833 701405 := bbase (se 3 (by rfl) ⟨131513, by rfl⟩ : syracuseStep 701405 = 263027) (by norm_num)
theorem B2241557 : Blo 307833 2241557 := bbase (se 6 (by rfl) ⟨52536, by rfl⟩ : syracuseStep 2241557 = 105073) (by norm_num)
theorem B373781 : Blo 307833 373781 := bbase (se 6 (by rfl) ⟨8760, by rfl⟩ : syracuseStep 373781 = 17521) (by norm_num)
theorem B701477 : Blo 307833 701477 := bbase (se 4 (by rfl) ⟨65763, by rfl⟩ : syracuseStep 701477 = 131527) (by norm_num)
theorem B1979477 : Blo 307833 1979477 := bbase (se 8 (by rfl) ⟨11598, by rfl⟩ : syracuseStep 1979477 = 23197) (by norm_num)
theorem B701549 : Blo 307833 701549 := bbase (se 3 (by rfl) ⟨131540, by rfl⟩ : syracuseStep 701549 = 263081) (by norm_num)
theorem B439445 : Blo 307833 439445 := bbase (se 6 (by rfl) ⟨10299, by rfl⟩ : syracuseStep 439445 = 20599) (by norm_num)
theorem B701621 : Blo 307833 701621 := bbase (se 5 (by rfl) ⟨32888, by rfl⟩ : syracuseStep 701621 = 65777) (by norm_num)
theorem B2831573 : Blo 307833 2831573 := bbase (se 7 (by rfl) ⟨33182, by rfl⟩ : syracuseStep 2831573 = 66365) (by norm_num)
theorem B996965 : Blo 307833 996965 := bbase (se 4 (by rfl) ⟨93465, by rfl⟩ : syracuseStep 996965 = 186931) (by norm_num)
theorem B439997 : Blo 307833 439997 := bbase (se 3 (by rfl) ⟨82499, by rfl⟩ : syracuseStep 439997 = 164999) (by norm_num)
theorem B374473 : Blo 307833 374473 := bbase (se 2 (by rfl) ⟨140427, by rfl⟩ : syracuseStep 374473 = 280855) (by norm_num)
theorem B374477 : Blo 307833 374477 := bbase (se 3 (by rfl) ⟨70214, by rfl⟩ : syracuseStep 374477 = 140429) (by norm_num)
theorem B2537365 : Blo 307833 2537365 := bbase (se 6 (by rfl) ⟨59469, by rfl⟩ : syracuseStep 2537365 = 118939) (by norm_num)
theorem B604157 : Blo 307833 604157 := bbase (se 3 (by rfl) ⟨113279, by rfl⟩ : syracuseStep 604157 = 226559) (by norm_num)
theorem B899381 : Blo 307833 899381 := bbase (se 5 (by rfl) ⟨42158, by rfl⟩ : syracuseStep 899381 = 84317) (by norm_num)
theorem B5323157 : Blo 307833 5323157 := bbase (se 6 (by rfl) ⟨124761, by rfl⟩ : syracuseStep 5323157 = 249523) (by norm_num)
theorem B440749 : Blo 307833 440749 := bbase (se 3 (by rfl) ⟨82640, by rfl⟩ : syracuseStep 440749 = 165281) (by norm_num)
theorem B3750421 : Blo 307833 3750421 := bbase (se 6 (by rfl) ⟨87900, by rfl⟩ : syracuseStep 3750421 = 175801) (by norm_num)
theorem B1325717 : Blo 307833 1325717 := bbase (se 6 (by rfl) ⟨31071, by rfl⟩ : syracuseStep 1325717 = 62143) (by norm_num)
theorem B1882997 : Blo 307833 1882997 := bbase (se 5 (by rfl) ⟨88265, by rfl⟩ : syracuseStep 1882997 = 176531) (by norm_num)
theorem B375925 : Blo 307833 375925 := bbase (se 5 (by rfl) ⟨17621, by rfl⟩ : syracuseStep 375925 = 35243) (by norm_num)
theorem B441541 : Blo 307833 441541 := bbase (se 4 (by rfl) ⟨41394, by rfl⟩ : syracuseStep 441541 = 82789) (by norm_num)
theorem B670933 : Blo 307833 670933 := bbase (se 7 (by rfl) ⟨7862, by rfl⟩ : syracuseStep 670933 = 15725) (by norm_num)
theorem B7585109 : Blo 307833 7585109 := bbase (se 11 (by rfl) ⟨5555, by rfl⟩ : syracuseStep 7585109 = 11111) (by norm_num)
theorem B998837 : Blo 307833 998837 := bbase (se 5 (by rfl) ⟨46820, by rfl⟩ : syracuseStep 998837 = 93641) (by norm_num)
theorem B441877 : Blo 307833 441877 := bbase (se 6 (by rfl) ⟨10356, by rfl⟩ : syracuseStep 441877 = 20713) (by norm_num)
theorem B835157 : Blo 307833 835157 := bbase (se 8 (by rfl) ⟨4893, by rfl⟩ : syracuseStep 835157 = 9787) (by norm_num)
theorem B1326725 : Blo 307833 1326725 := bbase (se 4 (by rfl) ⟨124380, by rfl⟩ : syracuseStep 1326725 = 248761) (by norm_num)
theorem B442093 : Blo 307833 442093 := bbase (se 3 (by rfl) ⟨82892, by rfl⟩ : syracuseStep 442093 = 165785) (by norm_num)
theorem B2703253 : Blo 307833 2703253 := bbase (se 6 (by rfl) ⟨63357, by rfl⟩ : syracuseStep 2703253 = 126715) (by norm_num)
theorem B3162037 : Blo 307833 3162037 := bbase (se 5 (by rfl) ⟨148220, by rfl⟩ : syracuseStep 3162037 = 296441) (by norm_num)
theorem B835525 : Blo 307833 835525 := bbase (se 4 (by rfl) ⟨78330, by rfl⟩ : syracuseStep 835525 = 156661) (by norm_num)
theorem B475213 : Blo 307833 475213 := bbase (se 3 (by rfl) ⟨89102, by rfl⟩ : syracuseStep 475213 = 178205) (by norm_num)
theorem B442469 : Blo 307833 442469 := bbase (se 4 (by rfl) ⟨41481, by rfl⟩ : syracuseStep 442469 = 82963) (by norm_num)
theorem B835829 : Blo 307833 835829 := bbase (se 5 (by rfl) ⟨39179, by rfl⟩ : syracuseStep 835829 = 78359) (by norm_num)
theorem B999749 : Blo 307833 999749 := bbase (se 4 (by rfl) ⟨93726, by rfl⟩ : syracuseStep 999749 = 187453) (by norm_num)
theorem B1491797 : Blo 307833 1491797 := bbase (se 9 (by rfl) ⟨4370, by rfl⟩ : syracuseStep 1491797 = 8741) (by norm_num)
theorem B1262549 : Blo 307833 1262549 := bbase (se 7 (by rfl) ⟨14795, by rfl⟩ : syracuseStep 1262549 = 29591) (by norm_num)
theorem B377833 : Blo 307833 377833 := bbase (se 2 (by rfl) ⟨141687, by rfl⟩ : syracuseStep 377833 = 283375) (by norm_num)
theorem B607541 : Blo 307833 607541 := bbase (se 5 (by rfl) ⟨28478, by rfl⟩ : syracuseStep 607541 = 56957) (by norm_num)
theorem B312665 : Blo 307833 312665 := bbase (se 2 (by rfl) ⟨117249, by rfl⟩ : syracuseStep 312665 = 234499) (by norm_num)
theorem B1328501 : Blo 307833 1328501 := bbase (se 5 (by rfl) ⟨62273, by rfl⟩ : syracuseStep 1328501 = 124547) (by norm_num)
theorem B837029 : Blo 307833 837029 := bbase (se 4 (by rfl) ⟨78471, by rfl⟩ : syracuseStep 837029 = 156943) (by norm_num)
theorem B443893 : Blo 307833 443893 := bbase (se 5 (by rfl) ⟨20807, by rfl⟩ : syracuseStep 443893 = 41615) (by norm_num)
theorem B2639573 : Blo 307833 2639573 := bbase (se 7 (by rfl) ⟨30932, by rfl⟩ : syracuseStep 2639573 = 61865) (by norm_num)
theorem B378769 : Blo 307833 378769 := bbase (se 2 (by rfl) ⟨142038, by rfl⟩ : syracuseStep 378769 = 284077) (by norm_num)
theorem B706469 : Blo 307833 706469 := bbase (se 4 (by rfl) ⟨66231, by rfl⟩ : syracuseStep 706469 = 132463) (by norm_num)
theorem B2344949 : Blo 307833 2344949 := bbase (se 5 (by rfl) ⟨109919, by rfl⟩ : syracuseStep 2344949 = 219839) (by norm_num)
theorem B804917 : Blo 307833 804917 := bbase (se 5 (by rfl) ⟨37730, by rfl⟩ : syracuseStep 804917 = 75461) (by norm_num)
theorem B1230997 : Blo 307833 1230997 := bbase (se 6 (by rfl) ⟨28851, by rfl⟩ : syracuseStep 1230997 = 57703) (by norm_num)
theorem B313517 : Blo 307833 313517 := bbase (se 3 (by rfl) ⟨58784, by rfl⟩ : syracuseStep 313517 = 117569) (by norm_num)
theorem B346333 : Blo 307833 346333 := bbase (se 3 (by rfl) ⟨64937, by rfl⟩ : syracuseStep 346333 = 129875) (by norm_num)
theorem B346369 : Blo 307833 346369 := bbase (se 2 (by rfl) ⟨129888, by rfl⟩ : syracuseStep 346369 = 259777) (by norm_num)
theorem B346405 : Blo 307833 346405 := bbase (se 4 (by rfl) ⟨32475, by rfl⟩ : syracuseStep 346405 = 64951) (by norm_num)
theorem B346441 : Blo 307833 346441 := bbase (se 2 (by rfl) ⟨129915, by rfl⟩ : syracuseStep 346441 = 259831) (by norm_num)
theorem B837989 : Blo 307833 837989 := bbase (se 4 (by rfl) ⟨78561, by rfl⟩ : syracuseStep 837989 = 157123) (by norm_num)
theorem B346477 : Blo 307833 346477 := bbase (se 3 (by rfl) ⟨64964, by rfl⟩ : syracuseStep 346477 = 129929) (by norm_num)
theorem B346513 : Blo 307833 346513 := bbase (se 2 (by rfl) ⟨129942, by rfl⟩ : syracuseStep 346513 = 259885) (by norm_num)
theorem B346549 : Blo 307833 346549 := bbase (se 5 (by rfl) ⟨16244, by rfl⟩ : syracuseStep 346549 = 32489) (by norm_num)
theorem B346585 : Blo 307833 346585 := bbase (se 2 (by rfl) ⟨129969, by rfl⟩ : syracuseStep 346585 = 259939) (by norm_num)
theorem B346621 : Blo 307833 346621 := bbase (se 3 (by rfl) ⟨64991, by rfl⟩ : syracuseStep 346621 = 129983) (by norm_num)
theorem B346657 : Blo 307833 346657 := bbase (se 2 (by rfl) ⟨129996, by rfl⟩ : syracuseStep 346657 = 259993) (by norm_num)
theorem B739901 : Blo 307833 739901 := bbase (se 3 (by rfl) ⟨138731, by rfl⟩ : syracuseStep 739901 = 277463) (by norm_num)
theorem B346693 : Blo 307833 346693 := bbase (se 4 (by rfl) ⟨32502, by rfl⟩ : syracuseStep 346693 = 65005) (by norm_num)
theorem B346729 : Blo 307833 346729 := bbase (se 2 (by rfl) ⟨130023, by rfl⟩ : syracuseStep 346729 = 260047) (by norm_num)
theorem B346765 : Blo 307833 346765 := bbase (se 3 (by rfl) ⟨65018, by rfl⟩ : syracuseStep 346765 = 130037) (by norm_num)
theorem B346801 : Blo 307833 346801 := bbase (se 2 (by rfl) ⟨130050, by rfl⟩ : syracuseStep 346801 = 260101) (by norm_num)
theorem B346837 : Blo 307833 346837 := bbase (se 7 (by rfl) ⟨4064, by rfl⟩ : syracuseStep 346837 = 8129) (by norm_num)
theorem B346873 : Blo 307833 346873 := bbase (se 2 (by rfl) ⟨130077, by rfl⟩ : syracuseStep 346873 = 260155) (by norm_num)
theorem B346909 : Blo 307833 346909 := bbase (se 3 (by rfl) ⟨65045, by rfl⟩ : syracuseStep 346909 = 130091) (by norm_num)
theorem B346945 : Blo 307833 346945 := bbase (se 2 (by rfl) ⟨130104, by rfl⟩ : syracuseStep 346945 = 260209) (by norm_num)
theorem B346981 : Blo 307833 346981 := bbase (se 4 (by rfl) ⟨32529, by rfl⟩ : syracuseStep 346981 = 65059) (by norm_num)
theorem B347017 : Blo 307833 347017 := bbase (se 2 (by rfl) ⟨130131, by rfl⟩ : syracuseStep 347017 = 260263) (by norm_num)
theorem B2378645 : Blo 307833 2378645 := bbase (se 6 (by rfl) ⟨55749, by rfl⟩ : syracuseStep 2378645 = 111499) (by norm_num)
theorem B347053 : Blo 307833 347053 := bbase (se 3 (by rfl) ⟨65072, by rfl⟩ : syracuseStep 347053 = 130145) (by norm_num)
theorem B576437 : Blo 307833 576437 := bbase (se 5 (by rfl) ⟨27020, by rfl⟩ : syracuseStep 576437 = 54041) (by norm_num)
theorem B347089 : Blo 307833 347089 := bbase (se 2 (by rfl) ⟨130158, by rfl⟩ : syracuseStep 347089 = 260317) (by norm_num)
theorem B347125 : Blo 307833 347125 := bbase (se 5 (by rfl) ⟨16271, by rfl⟩ : syracuseStep 347125 = 32543) (by norm_num)
theorem B1559573 : Blo 307833 1559573 := bbase (se 6 (by rfl) ⟨36552, by rfl⟩ : syracuseStep 1559573 = 73105) (by norm_num)
theorem B347161 : Blo 307833 347161 := bbase (se 2 (by rfl) ⟨130185, by rfl⟩ : syracuseStep 347161 = 260371) (by norm_num)
theorem B347197 : Blo 307833 347197 := bbase (se 3 (by rfl) ⟨65099, by rfl⟩ : syracuseStep 347197 = 130199) (by norm_num)
theorem B347233 : Blo 307833 347233 := bbase (se 2 (by rfl) ⟨130212, by rfl⟩ : syracuseStep 347233 = 260425) (by norm_num)
theorem B347269 : Blo 307833 347269 := bbase (se 4 (by rfl) ⟨32556, by rfl⟩ : syracuseStep 347269 = 65113) (by norm_num)
theorem B347305 : Blo 307833 347305 := bbase (se 2 (by rfl) ⟨130239, by rfl⟩ : syracuseStep 347305 = 260479) (by norm_num)
theorem B347341 : Blo 307833 347341 := bbase (se 3 (by rfl) ⟨65126, by rfl⟩ : syracuseStep 347341 = 130253) (by norm_num)
theorem B1002725 : Blo 307833 1002725 := bbase (se 4 (by rfl) ⟨94005, by rfl⟩ : syracuseStep 1002725 = 188011) (by norm_num)
theorem B347377 : Blo 307833 347377 := bbase (se 2 (by rfl) ⟨130266, by rfl⟩ : syracuseStep 347377 = 260533) (by norm_num)
theorem B347413 : Blo 307833 347413 := bbase (se 6 (by rfl) ⟨8142, by rfl⟩ : syracuseStep 347413 = 16285) (by norm_num)
theorem B347449 : Blo 307833 347449 := bbase (se 2 (by rfl) ⟨130293, by rfl⟩ : syracuseStep 347449 = 260587) (by norm_num)
theorem B347485 : Blo 307833 347485 := bbase (se 3 (by rfl) ⟨65153, by rfl⟩ : syracuseStep 347485 = 130307) (by norm_num)
theorem B314749 : Blo 307833 314749 := bbase (se 3 (by rfl) ⟨59015, by rfl⟩ : syracuseStep 314749 = 118031) (by norm_num)
theorem B347521 : Blo 307833 347521 := bbase (se 2 (by rfl) ⟨130320, by rfl⟩ : syracuseStep 347521 = 260641) (by norm_num)
theorem B347557 : Blo 307833 347557 := bbase (se 4 (by rfl) ⟨32583, by rfl⟩ : syracuseStep 347557 = 65167) (by norm_num)
theorem B347593 : Blo 307833 347593 := bbase (se 2 (by rfl) ⟨130347, by rfl⟩ : syracuseStep 347593 = 260695) (by norm_num)
theorem B347629 : Blo 307833 347629 := bbase (se 3 (by rfl) ⟨65180, by rfl⟩ : syracuseStep 347629 = 130361) (by norm_num)
theorem B347665 : Blo 307833 347665 := bbase (se 2 (by rfl) ⟨130374, by rfl⟩ : syracuseStep 347665 = 260749) (by norm_num)
theorem B347701 : Blo 307833 347701 := bbase (se 5 (by rfl) ⟨16298, by rfl⟩ : syracuseStep 347701 = 32597) (by norm_num)
theorem B347737 : Blo 307833 347737 := bbase (se 2 (by rfl) ⟨130401, by rfl⟩ : syracuseStep 347737 = 260803) (by norm_num)
theorem B347773 : Blo 307833 347773 := bbase (se 3 (by rfl) ⟨65207, by rfl⟩ : syracuseStep 347773 = 130415) (by norm_num)
theorem B708221 : Blo 307833 708221 := bbase (se 3 (by rfl) ⟨132791, by rfl⟩ : syracuseStep 708221 = 265583) (by norm_num)
theorem B347809 : Blo 307833 347809 := bbase (se 2 (by rfl) ⟨130428, by rfl⟩ : syracuseStep 347809 = 260857) (by norm_num)
theorem B347845 : Blo 307833 347845 := bbase (se 4 (by rfl) ⟨32610, by rfl⟩ : syracuseStep 347845 = 65221) (by norm_num)
theorem B675533 : Blo 307833 675533 := bbase (se 3 (by rfl) ⟨126662, by rfl⟩ : syracuseStep 675533 = 253325) (by norm_num)
theorem B347881 : Blo 307833 347881 := bbase (se 2 (by rfl) ⟨130455, by rfl⟩ : syracuseStep 347881 = 260911) (by norm_num)
theorem B347917 : Blo 307833 347917 := bbase (se 3 (by rfl) ⟨65234, by rfl⟩ : syracuseStep 347917 = 130469) (by norm_num)
theorem B347953 : Blo 307833 347953 := bbase (se 2 (by rfl) ⟨130482, by rfl⟩ : syracuseStep 347953 = 260965) (by norm_num)
theorem B347989 : Blo 307833 347989 := bbase (se 9 (by rfl) ⟨1019, by rfl⟩ : syracuseStep 347989 = 2039) (by norm_num)
theorem B5820245 : Blo 307833 5820245 := bbase (se 9 (by rfl) ⟨17051, by rfl⟩ : syracuseStep 5820245 = 34103) (by norm_num)
theorem B348025 : Blo 307833 348025 := bbase (se 2 (by rfl) ⟨130509, by rfl⟩ : syracuseStep 348025 = 261019) (by norm_num)
theorem B348061 : Blo 307833 348061 := bbase (se 3 (by rfl) ⟨65261, by rfl⟩ : syracuseStep 348061 = 130523) (by norm_num)
theorem B348097 : Blo 307833 348097 := bbase (se 2 (by rfl) ⟨130536, by rfl⟩ : syracuseStep 348097 = 261073) (by norm_num)
theorem B348133 : Blo 307833 348133 := bbase (se 4 (by rfl) ⟨32637, by rfl⟩ : syracuseStep 348133 = 65275) (by norm_num)
theorem B708581 : Blo 307833 708581 := bbase (se 4 (by rfl) ⟨66429, by rfl⟩ : syracuseStep 708581 = 132859) (by norm_num)
theorem B937973 : Blo 307833 937973 := bbase (se 5 (by rfl) ⟨43967, by rfl⟩ : syracuseStep 937973 = 87935) (by norm_num)
theorem B348169 : Blo 307833 348169 := bbase (se 2 (by rfl) ⟨130563, by rfl⟩ : syracuseStep 348169 = 261127) (by norm_num)
theorem B348205 : Blo 307833 348205 := bbase (se 3 (by rfl) ⟨65288, by rfl⟩ : syracuseStep 348205 = 130577) (by norm_num)
theorem B348241 : Blo 307833 348241 := bbase (se 2 (by rfl) ⟨130590, by rfl⟩ : syracuseStep 348241 = 261181) (by norm_num)
theorem B348277 : Blo 307833 348277 := bbase (se 5 (by rfl) ⟨16325, by rfl⟩ : syracuseStep 348277 = 32651) (by norm_num)
theorem B348313 : Blo 307833 348313 := bbase (se 2 (by rfl) ⟨130617, by rfl⟩ : syracuseStep 348313 = 261235) (by norm_num)
theorem B348349 : Blo 307833 348349 := bbase (se 3 (by rfl) ⟨65315, by rfl⟩ : syracuseStep 348349 = 130631) (by norm_num)
theorem B348385 : Blo 307833 348385 := bbase (se 2 (by rfl) ⟨130644, by rfl⟩ : syracuseStep 348385 = 261289) (by norm_num)
theorem B348421 : Blo 307833 348421 := bbase (se 4 (by rfl) ⟨32664, by rfl⟩ : syracuseStep 348421 = 65329) (by norm_num)
theorem B1560869 : Blo 307833 1560869 := bbase (se 4 (by rfl) ⟨146331, by rfl⟩ : syracuseStep 1560869 = 292663) (by norm_num)
theorem B348457 : Blo 307833 348457 := bbase (se 2 (by rfl) ⟨130671, by rfl⟩ : syracuseStep 348457 = 261343) (by norm_num)
theorem B348493 : Blo 307833 348493 := bbase (se 3 (by rfl) ⟨65342, by rfl⟩ : syracuseStep 348493 = 130685) (by norm_num)
theorem B348529 : Blo 307833 348529 := bbase (se 2 (by rfl) ⟨130698, by rfl⟩ : syracuseStep 348529 = 261397) (by norm_num)
theorem B348565 : Blo 307833 348565 := bbase (se 6 (by rfl) ⟨8169, by rfl⟩ : syracuseStep 348565 = 16339) (by norm_num)
theorem B348601 : Blo 307833 348601 := bbase (se 2 (by rfl) ⟨130725, by rfl⟩ : syracuseStep 348601 = 261451) (by norm_num)
theorem B348637 : Blo 307833 348637 := bbase (se 3 (by rfl) ⟨65369, by rfl⟩ : syracuseStep 348637 = 130739) (by norm_num)
theorem B348673 : Blo 307833 348673 := bbase (se 2 (by rfl) ⟨130752, by rfl⟩ : syracuseStep 348673 = 261505) (by norm_num)
theorem B348709 : Blo 307833 348709 := bbase (se 4 (by rfl) ⟨32691, by rfl⟩ : syracuseStep 348709 = 65383) (by norm_num)
theorem B348745 : Blo 307833 348745 := bbase (se 2 (by rfl) ⟨130779, by rfl⟩ : syracuseStep 348745 = 261559) (by norm_num)
theorem B348781 : Blo 307833 348781 := bbase (se 3 (by rfl) ⟨65396, by rfl⟩ : syracuseStep 348781 = 130793) (by norm_num)
theorem B348817 : Blo 307833 348817 := bbase (se 2 (by rfl) ⟨130806, by rfl⟩ : syracuseStep 348817 = 261613) (by norm_num)
theorem B348853 : Blo 307833 348853 := bbase (se 5 (by rfl) ⟨16352, by rfl⟩ : syracuseStep 348853 = 32705) (by norm_num)
theorem B348889 : Blo 307833 348889 := bbase (se 2 (by rfl) ⟨130833, by rfl⟩ : syracuseStep 348889 = 261667) (by norm_num)
theorem B348925 : Blo 307833 348925 := bbase (se 3 (by rfl) ⟨65423, by rfl⟩ : syracuseStep 348925 = 130847) (by norm_num)
theorem B348961 : Blo 307833 348961 := bbase (se 2 (by rfl) ⟨130860, by rfl⟩ : syracuseStep 348961 = 261721) (by norm_num)
theorem B348997 : Blo 307833 348997 := bbase (se 4 (by rfl) ⟨32718, by rfl⟩ : syracuseStep 348997 = 65437) (by norm_num)
theorem B349033 : Blo 307833 349033 := bbase (se 2 (by rfl) ⟨130887, by rfl⟩ : syracuseStep 349033 = 261775) (by norm_num)
theorem B349069 : Blo 307833 349069 := bbase (se 3 (by rfl) ⟨65450, by rfl⟩ : syracuseStep 349069 = 130901) (by norm_num)
theorem B349105 : Blo 307833 349105 := bbase (se 2 (by rfl) ⟨130914, by rfl⟩ : syracuseStep 349105 = 261829) (by norm_num)
theorem B349141 : Blo 307833 349141 := bbase (se 7 (by rfl) ⟨4091, by rfl⟩ : syracuseStep 349141 = 8183) (by norm_num)
theorem B1987573 : Blo 307833 1987573 := bbase (se 5 (by rfl) ⟨93167, by rfl⟩ : syracuseStep 1987573 = 186335) (by norm_num)
theorem B349177 : Blo 307833 349177 := bbase (se 2 (by rfl) ⟨130941, by rfl⟩ : syracuseStep 349177 = 261883) (by norm_num)
theorem B349213 : Blo 307833 349213 := bbase (se 3 (by rfl) ⟨65477, by rfl⟩ : syracuseStep 349213 = 130955) (by norm_num)
theorem B349249 : Blo 307833 349249 := bbase (se 2 (by rfl) ⟨130968, by rfl⟩ : syracuseStep 349249 = 261937) (by norm_num)
theorem B349285 : Blo 307833 349285 := bbase (se 4 (by rfl) ⟨32745, by rfl⟩ : syracuseStep 349285 = 65491) (by norm_num)
theorem B316537 : Blo 307833 316537 := bbase (se 2 (by rfl) ⟨118701, by rfl⟩ : syracuseStep 316537 = 237403) (by norm_num)
theorem B349321 : Blo 307833 349321 := bbase (se 2 (by rfl) ⟨130995, by rfl⟩ : syracuseStep 349321 = 261991) (by norm_num)
theorem B349357 : Blo 307833 349357 := bbase (se 3 (by rfl) ⟨65504, by rfl⟩ : syracuseStep 349357 = 131009) (by norm_num)
theorem B349393 : Blo 307833 349393 := bbase (se 2 (by rfl) ⟨131022, by rfl⟩ : syracuseStep 349393 = 262045) (by norm_num)
theorem B349429 : Blo 307833 349429 := bbase (se 5 (by rfl) ⟨16379, by rfl⟩ : syracuseStep 349429 = 32759) (by norm_num)
theorem B349465 : Blo 307833 349465 := bbase (se 2 (by rfl) ⟨131049, by rfl⟩ : syracuseStep 349465 = 262099) (by norm_num)
theorem B349501 : Blo 307833 349501 := bbase (se 3 (by rfl) ⟨65531, by rfl⟩ : syracuseStep 349501 = 131063) (by norm_num)
theorem B349537 : Blo 307833 349537 := bbase (se 2 (by rfl) ⟨131076, by rfl⟩ : syracuseStep 349537 = 262153) (by norm_num)
theorem B349573 : Blo 307833 349573 := bbase (se 4 (by rfl) ⟨32772, by rfl⟩ : syracuseStep 349573 = 65545) (by norm_num)
theorem B349609 : Blo 307833 349609 := bbase (se 2 (by rfl) ⟨131103, by rfl⟩ : syracuseStep 349609 = 262207) (by norm_num)
theorem B349645 : Blo 307833 349645 := bbase (se 3 (by rfl) ⟨65558, by rfl⟩ : syracuseStep 349645 = 131117) (by norm_num)
theorem B349681 : Blo 307833 349681 := bbase (se 2 (by rfl) ⟨131130, by rfl⟩ : syracuseStep 349681 = 262261) (by norm_num)
theorem B349717 : Blo 307833 349717 := bbase (se 6 (by rfl) ⟨8196, by rfl⟩ : syracuseStep 349717 = 16393) (by norm_num)
theorem B1562165 : Blo 307833 1562165 := bbase (se 5 (by rfl) ⟨73226, by rfl⟩ : syracuseStep 1562165 = 146453) (by norm_num)
theorem B349753 : Blo 307833 349753 := bbase (se 2 (by rfl) ⟨131157, by rfl⟩ : syracuseStep 349753 = 262315) (by norm_num)
theorem B349789 : Blo 307833 349789 := bbase (se 3 (by rfl) ⟨65585, by rfl⟩ : syracuseStep 349789 = 131171) (by norm_num)
theorem B349825 : Blo 307833 349825 := bbase (se 2 (by rfl) ⟨131184, by rfl⟩ : syracuseStep 349825 = 262369) (by norm_num)
theorem B349861 : Blo 307833 349861 := bbase (se 4 (by rfl) ⟨32799, by rfl⟩ : syracuseStep 349861 = 65599) (by norm_num)
theorem B349897 : Blo 307833 349897 := bbase (se 2 (by rfl) ⟨131211, by rfl⟩ : syracuseStep 349897 = 262423) (by norm_num)
theorem B317153 : Blo 307833 317153 := bbase (se 2 (by rfl) ⟨118932, by rfl⟩ : syracuseStep 317153 = 237865) (by norm_num)
theorem B349933 : Blo 307833 349933 := bbase (se 3 (by rfl) ⟨65612, by rfl⟩ : syracuseStep 349933 = 131225) (by norm_num)
theorem B349969 : Blo 307833 349969 := bbase (se 2 (by rfl) ⟨131238, by rfl⟩ : syracuseStep 349969 = 262477) (by norm_num)
theorem B350005 : Blo 307833 350005 := bbase (se 5 (by rfl) ⟨16406, by rfl⟩ : syracuseStep 350005 = 32813) (by norm_num)
theorem B350041 : Blo 307833 350041 := bbase (se 2 (by rfl) ⟨131265, by rfl⟩ : syracuseStep 350041 = 262531) (by norm_num)
theorem B350077 : Blo 307833 350077 := bbase (se 3 (by rfl) ⟨65639, by rfl⟩ : syracuseStep 350077 = 131279) (by norm_num)
theorem B350113 : Blo 307833 350113 := bbase (se 2 (by rfl) ⟨131292, by rfl⟩ : syracuseStep 350113 = 262585) (by norm_num)
theorem B939941 : Blo 307833 939941 := bbase (se 4 (by rfl) ⟨88119, by rfl⟩ : syracuseStep 939941 = 176239) (by norm_num)
theorem B743341 : Blo 307833 743341 := bbase (se 3 (by rfl) ⟨139376, by rfl⟩ : syracuseStep 743341 = 278753) (by norm_num)
theorem B350149 : Blo 307833 350149 := bbase (se 4 (by rfl) ⟨32826, by rfl⟩ : syracuseStep 350149 = 65653) (by norm_num)
theorem B317417 : Blo 307833 317417 := bbase (se 2 (by rfl) ⟨119031, by rfl⟩ : syracuseStep 317417 = 238063) (by norm_num)
theorem B350185 : Blo 307833 350185 := bbase (se 2 (by rfl) ⟨131319, by rfl⟩ : syracuseStep 350185 = 262639) (by norm_num)
theorem B350221 : Blo 307833 350221 := bbase (se 3 (by rfl) ⟨65666, by rfl⟩ : syracuseStep 350221 = 131333) (by norm_num)
theorem B350257 : Blo 307833 350257 := bbase (se 2 (by rfl) ⟨131346, by rfl⟩ : syracuseStep 350257 = 262693) (by norm_num)
theorem B350293 : Blo 307833 350293 := bbase (se 8 (by rfl) ⟨2052, by rfl⟩ : syracuseStep 350293 = 4105) (by norm_num)
theorem B350329 : Blo 307833 350329 := bbase (se 2 (by rfl) ⟨131373, by rfl⟩ : syracuseStep 350329 = 262747) (by norm_num)
theorem B1136773 : Blo 307833 1136773 := bbase (se 4 (by rfl) ⟨106572, by rfl⟩ : syracuseStep 1136773 = 213145) (by norm_num)
theorem B743573 : Blo 307833 743573 := bbase (se 6 (by rfl) ⟨17427, by rfl⟩ : syracuseStep 743573 = 34855) (by norm_num)
theorem B350365 : Blo 307833 350365 := bbase (se 3 (by rfl) ⟨65693, by rfl⟩ : syracuseStep 350365 = 131387) (by norm_num)
theorem B678061 : Blo 307833 678061 := bbase (se 3 (by rfl) ⟨127136, by rfl⟩ : syracuseStep 678061 = 254273) (by norm_num)
theorem B350401 : Blo 307833 350401 := bbase (se 2 (by rfl) ⟨131400, by rfl⟩ : syracuseStep 350401 = 262801) (by norm_num)
theorem B350437 : Blo 307833 350437 := bbase (se 4 (by rfl) ⟨32853, by rfl⟩ : syracuseStep 350437 = 65707) (by norm_num)
theorem B350473 : Blo 307833 350473 := bbase (se 2 (by rfl) ⟨131427, by rfl⟩ : syracuseStep 350473 = 262855) (by norm_num)
theorem B743717 : Blo 307833 743717 := bbase (se 4 (by rfl) ⟨69723, by rfl⟩ : syracuseStep 743717 = 139447) (by norm_num)
theorem B350509 : Blo 307833 350509 := bbase (se 3 (by rfl) ⟨65720, by rfl⟩ : syracuseStep 350509 = 131441) (by norm_num)
theorem B350545 : Blo 307833 350545 := bbase (se 2 (by rfl) ⟨131454, by rfl⟩ : syracuseStep 350545 = 262909) (by norm_num)
theorem B350581 : Blo 307833 350581 := bbase (se 5 (by rfl) ⟨16433, by rfl⟩ : syracuseStep 350581 = 32867) (by norm_num)
theorem B5986709 : Blo 307833 5986709 := bbase (se 6 (by rfl) ⟨140313, by rfl⟩ : syracuseStep 5986709 = 280627) (by norm_num)
theorem B350617 : Blo 307833 350617 := bbase (se 2 (by rfl) ⟨131481, by rfl⟩ : syracuseStep 350617 = 262963) (by norm_num)
theorem B350653 : Blo 307833 350653 := bbase (se 3 (by rfl) ⟨65747, by rfl⟩ : syracuseStep 350653 = 131495) (by norm_num)
theorem B940501 : Blo 307833 940501 := bbase (se 7 (by rfl) ⟨11021, by rfl⟩ : syracuseStep 940501 = 22043) (by norm_num)
theorem B350689 : Blo 307833 350689 := bbase (se 2 (by rfl) ⟨131508, by rfl⟩ : syracuseStep 350689 = 263017) (by norm_num)
theorem B1169909 : Blo 307833 1169909 := bbase (se 5 (by rfl) ⟨54839, by rfl⟩ : syracuseStep 1169909 = 109679) (by norm_num)
theorem B350725 : Blo 307833 350725 := bbase (se 4 (by rfl) ⟨32880, by rfl⟩ : syracuseStep 350725 = 65761) (by norm_num)
theorem B743957 : Blo 307833 743957 := bbase (se 6 (by rfl) ⟨17436, by rfl⟩ : syracuseStep 743957 = 34873) (by norm_num)
theorem B350761 : Blo 307833 350761 := bbase (se 2 (by rfl) ⟨131535, by rfl⟩ : syracuseStep 350761 = 263071) (by norm_num)
theorem B350797 : Blo 307833 350797 := bbase (se 3 (by rfl) ⟨65774, by rfl⟩ : syracuseStep 350797 = 131549) (by norm_num)
theorem B1039013 : Blo 307833 1039013 := bbase (se 4 (by rfl) ⟨97407, by rfl⟩ : syracuseStep 1039013 = 194815) (by norm_num)
theorem B1170197 : Blo 307833 1170197 := bbase (se 6 (by rfl) ⟨27426, by rfl⟩ : syracuseStep 1170197 = 54853) (by norm_num)
theorem B1563461 : Blo 307833 1563461 := bbase (se 4 (by rfl) ⟨146574, by rfl⟩ : syracuseStep 1563461 = 293149) (by norm_num)
theorem B1039445 : Blo 307833 1039445 := bbase (se 8 (by rfl) ⟨6090, by rfl⟩ : syracuseStep 1039445 = 12181) (by norm_num)
theorem B318641 : Blo 307833 318641 := bbase (se 2 (by rfl) ⟨119490, by rfl⟩ : syracuseStep 318641 = 238981) (by norm_num)
theorem B318665 : Blo 307833 318665 := bbase (se 2 (by rfl) ⟨119499, by rfl⟩ : syracuseStep 318665 = 238999) (by norm_num)
theorem B744725 : Blo 307833 744725 := bbase (se 6 (by rfl) ⟨17454, by rfl⟩ : syracuseStep 744725 = 34909) (by norm_num)
theorem B351589 : Blo 307833 351589 := bbase (se 4 (by rfl) ⟨32961, by rfl⟩ : syracuseStep 351589 = 65923) (by norm_num)
theorem B2219413 : Blo 307833 2219413 := bbase (se 6 (by rfl) ⟨52017, by rfl⟩ : syracuseStep 2219413 = 104035) (by norm_num)
theorem B1039877 : Blo 307833 1039877 := bbase (se 4 (by rfl) ⟨97488, by rfl⟩ : syracuseStep 1039877 = 194977) (by norm_num)
theorem B1761173 : Blo 307833 1761173 := bbase (se 6 (by rfl) ⟨41277, by rfl⟩ : syracuseStep 1761173 = 82555) (by norm_num)
theorem B1040309 : Blo 307833 1040309 := bbase (se 5 (by rfl) ⟨48764, by rfl⟩ : syracuseStep 1040309 = 97529) (by norm_num)
theorem B1171381 : Blo 307833 1171381 := bbase (se 5 (by rfl) ⟨54908, by rfl⟩ : syracuseStep 1171381 = 109817) (by norm_num)
theorem B1564757 : Blo 307833 1564757 := bbase (se 8 (by rfl) ⟨9168, by rfl⟩ : syracuseStep 1564757 = 18337) (by norm_num)
theorem B1597589 : Blo 307833 1597589 := bbase (se 6 (by rfl) ⟨37443, by rfl⟩ : syracuseStep 1597589 = 74887) (by norm_num)
theorem B1171685 : Blo 307833 1171685 := bbase (se 4 (by rfl) ⟨109845, by rfl⟩ : syracuseStep 1171685 = 219691) (by norm_num)
theorem B1040741 : Blo 307833 1040741 := bbase (se 4 (by rfl) ⟨97569, by rfl⟩ : syracuseStep 1040741 = 195139) (by norm_num)
theorem B746101 : Blo 307833 746101 := bbase (se 5 (by rfl) ⟨34973, by rfl⟩ : syracuseStep 746101 = 69947) (by norm_num)
theorem B1041173 : Blo 307833 1041173 := bbase (se 6 (by rfl) ⟨24402, by rfl⟩ : syracuseStep 1041173 = 48805) (by norm_num)
theorem B1794901 : Blo 307833 1794901 := bbase (se 9 (by rfl) ⟨5258, by rfl⟩ : syracuseStep 1794901 = 10517) (by norm_num)
theorem B1991573 : Blo 307833 1991573 := bbase (se 6 (by rfl) ⟨46677, by rfl⟩ : syracuseStep 1991573 = 93355) (by norm_num)
theorem B1762357 : Blo 307833 1762357 := bbase (se 5 (by rfl) ⟨82610, by rfl⟩ : syracuseStep 1762357 = 165221) (by norm_num)
theorem B2516021 : Blo 307833 2516021 := bbase (se 5 (by rfl) ⟨117938, by rfl⟩ : syracuseStep 2516021 = 235877) (by norm_num)
theorem B779341 : Blo 307833 779341 := bbase (se 3 (by rfl) ⟨146126, by rfl⟩ : syracuseStep 779341 = 292253) (by norm_num)
theorem B353381 : Blo 307833 353381 := bbase (se 4 (by rfl) ⟨33129, by rfl⟩ : syracuseStep 353381 = 66259) (by norm_num)
theorem B418973 : Blo 307833 418973 := bbase (se 3 (by rfl) ⟨78557, by rfl⟩ : syracuseStep 418973 = 157115) (by norm_num)
theorem B779453 : Blo 307833 779453 := bbase (se 3 (by rfl) ⟨146147, by rfl⟩ : syracuseStep 779453 = 292295) (by norm_num)
theorem B1041605 : Blo 307833 1041605 := bbase (se 4 (by rfl) ⟨97650, by rfl⟩ : syracuseStep 1041605 = 195301) (by norm_num)
theorem B1566053 : Blo 307833 1566053 := bbase (se 4 (by rfl) ⟨146817, by rfl⟩ : syracuseStep 1566053 = 293635) (by norm_num)
theorem B779645 : Blo 307833 779645 := bbase (se 3 (by rfl) ⟨146183, by rfl⟩ : syracuseStep 779645 = 292367) (by norm_num)
theorem B2352725 : Blo 307833 2352725 := bbase (se 8 (by rfl) ⟨13785, by rfl⟩ : syracuseStep 2352725 = 27571) (by norm_num)
theorem B2647637 : Blo 307833 2647637 := bbase (se 8 (by rfl) ⟨15513, by rfl⟩ : syracuseStep 2647637 = 31027) (by norm_num)
theorem B1042037 : Blo 307833 1042037 := bbase (se 5 (by rfl) ⟨48845, by rfl⟩ : syracuseStep 1042037 = 97691) (by norm_num)
theorem B353965 : Blo 307833 353965 := bbase (se 3 (by rfl) ⟨66368, by rfl⟩ : syracuseStep 353965 = 132737) (by norm_num)
theorem B779989 : Blo 307833 779989 := bbase (se 7 (by rfl) ⟨9140, by rfl⟩ : syracuseStep 779989 = 18281) (by norm_num)
theorem B878309 : Blo 307833 878309 := bbase (se 4 (by rfl) ⟨82341, by rfl⟩ : syracuseStep 878309 = 164683) (by norm_num)
theorem B747301 : Blo 307833 747301 := bbase (se 4 (by rfl) ⟨70059, by rfl⟩ : syracuseStep 747301 = 140119) (by norm_num)
theorem B681781 : Blo 307833 681781 := bbase (se 5 (by rfl) ⟨31958, by rfl⟩ : syracuseStep 681781 = 63917) (by norm_num)
theorem B780101 : Blo 307833 780101 := bbase (se 4 (by rfl) ⟨73134, by rfl⟩ : syracuseStep 780101 = 146269) (by norm_num)
theorem B419725 : Blo 307833 419725 := bbase (se 3 (by rfl) ⟨78698, by rfl⟩ : syracuseStep 419725 = 157397) (by norm_num)
theorem B780293 : Blo 307833 780293 := bbase (se 4 (by rfl) ⟨73152, by rfl⟩ : syracuseStep 780293 = 146305) (by norm_num)
theorem B1042469 : Blo 307833 1042469 := bbase (se 4 (by rfl) ⟨97731, by rfl⟩ : syracuseStep 1042469 = 195463) (by norm_num)
theorem B354385 : Blo 307833 354385 := bbase (se 2 (by rfl) ⟨132894, by rfl⟩ : syracuseStep 354385 = 265789) (by norm_num)
theorem B911477 : Blo 307833 911477 := bbase (se 5 (by rfl) ⟨42725, by rfl⟩ : syracuseStep 911477 = 85451) (by norm_num)
theorem B4483349 : Blo 307833 4483349 := bbase (se 6 (by rfl) ⟨105078, by rfl⟩ : syracuseStep 4483349 = 210157) (by norm_num)
theorem B1173797 : Blo 307833 1173797 := bbase (se 4 (by rfl) ⟨110043, by rfl⟩ : syracuseStep 1173797 = 220087) (by norm_num)
theorem B780637 : Blo 307833 780637 := bbase (se 3 (by rfl) ⟨146369, by rfl⟩ : syracuseStep 780637 = 292739) (by norm_num)
theorem B747917 : Blo 307833 747917 := bbase (se 3 (by rfl) ⟨140234, by rfl⟩ : syracuseStep 747917 = 280469) (by norm_num)
theorem B780749 : Blo 307833 780749 := bbase (se 3 (by rfl) ⟨146390, by rfl⟩ : syracuseStep 780749 = 292781) (by norm_num)
theorem B1042901 : Blo 307833 1042901 := bbase (se 7 (by rfl) ⟨12221, by rfl⟩ : syracuseStep 1042901 = 24443) (by norm_num)
theorem B1174085 : Blo 307833 1174085 := bbase (se 4 (by rfl) ⟨110070, by rfl⟩ : syracuseStep 1174085 = 220141) (by norm_num)
theorem B748109 : Blo 307833 748109 := bbase (se 3 (by rfl) ⟨140270, by rfl⟩ : syracuseStep 748109 = 280541) (by norm_num)
theorem B1567349 : Blo 307833 1567349 := bbase (se 5 (by rfl) ⟨73469, by rfl⟩ : syracuseStep 1567349 = 146939) (by norm_num)
theorem B780941 : Blo 307833 780941 := bbase (se 3 (by rfl) ⟨146426, by rfl⟩ : syracuseStep 780941 = 292853) (by norm_num)
theorem B748205 : Blo 307833 748205 := bbase (se 3 (by rfl) ⟨140288, by rfl⟩ : syracuseStep 748205 = 280577) (by norm_num)
theorem B879493 : Blo 307833 879493 := bbase (se 4 (by rfl) ⟨82452, by rfl⟩ : syracuseStep 879493 = 164905) (by norm_num)
theorem B1043333 : Blo 307833 1043333 := bbase (se 4 (by rfl) ⟨97812, by rfl⟩ : syracuseStep 1043333 = 195625) (by norm_num)
theorem B584597 : Blo 307833 584597 := bbase (se 6 (by rfl) ⟨13701, by rfl⟩ : syracuseStep 584597 = 27403) (by norm_num)
theorem B355261 : Blo 307833 355261 := bbase (se 3 (by rfl) ⟨66611, by rfl⟩ : syracuseStep 355261 = 133223) (by norm_num)
theorem B781285 : Blo 307833 781285 := bbase (se 4 (by rfl) ⟨73245, by rfl⟩ : syracuseStep 781285 = 146491) (by norm_num)
theorem B1764341 : Blo 307833 1764341 := bbase (se 5 (by rfl) ⟨82703, by rfl⟩ : syracuseStep 1764341 = 165407) (by norm_num)
theorem B1534997 : Blo 307833 1534997 := bbase (se 6 (by rfl) ⟨35976, by rfl⟩ : syracuseStep 1534997 = 71953) (by norm_num)
theorem B355361 : Blo 307833 355361 := bbase (se 2 (by rfl) ⟨133260, by rfl⟩ : syracuseStep 355361 = 266521) (by norm_num)
theorem B879653 : Blo 307833 879653 := bbase (se 4 (by rfl) ⟨82467, by rfl⟩ : syracuseStep 879653 = 164935) (by norm_num)
theorem B584749 : Blo 307833 584749 := bbase (se 3 (by rfl) ⟨109640, by rfl⟩ : syracuseStep 584749 = 219281) (by norm_num)
theorem B781397 : Blo 307833 781397 := bbase (se 8 (by rfl) ⟨4578, by rfl⟩ : syracuseStep 781397 = 9157) (by norm_num)
theorem B781589 : Blo 307833 781589 := bbase (se 6 (by rfl) ⟨18318, by rfl⟩ : syracuseStep 781589 = 36637) (by norm_num)
theorem B879893 : Blo 307833 879893 := bbase (se 6 (by rfl) ⟨20622, by rfl⟩ : syracuseStep 879893 = 41245) (by norm_num)
theorem B421157 : Blo 307833 421157 := bbase (se 4 (by rfl) ⟨39483, by rfl⟩ : syracuseStep 421157 = 78967) (by norm_num)
theorem B1043765 : Blo 307833 1043765 := bbase (se 5 (by rfl) ⟨48926, by rfl⟩ : syracuseStep 1043765 = 97853) (by norm_num)
theorem B519493 : Blo 307833 519493 := bbase (se 4 (by rfl) ⟨48702, by rfl⟩ : syracuseStep 519493 = 97405) (by norm_num)
theorem B585053 : Blo 307833 585053 := bbase (se 3 (by rfl) ⟨109697, by rfl⟩ : syracuseStep 585053 = 219395) (by norm_num)
theorem B519581 : Blo 307833 519581 := bbase (se 3 (by rfl) ⟨97421, by rfl⟩ : syracuseStep 519581 = 194843) (by norm_num)
theorem B880085 : Blo 307833 880085 := bbase (se 7 (by rfl) ⟨10313, by rfl⟩ : syracuseStep 880085 = 20627) (by norm_num)
theorem B519709 : Blo 307833 519709 := bbase (se 3 (by rfl) ⟨97445, by rfl⟩ : syracuseStep 519709 = 194891) (by norm_num)
theorem B781933 : Blo 307833 781933 := bbase (se 3 (by rfl) ⟨146612, by rfl⟩ : syracuseStep 781933 = 293225) (by norm_num)
theorem B519797 : Blo 307833 519797 := bbase (se 5 (by rfl) ⟨24365, by rfl⟩ : syracuseStep 519797 = 48731) (by norm_num)
theorem B782045 : Blo 307833 782045 := bbase (se 3 (by rfl) ⟨146633, by rfl⟩ : syracuseStep 782045 = 293267) (by norm_num)
theorem B1044197 : Blo 307833 1044197 := bbase (se 4 (by rfl) ⟨97893, by rfl⟩ : syracuseStep 1044197 = 195787) (by norm_num)
theorem B1175269 : Blo 307833 1175269 := bbase (se 4 (by rfl) ⟨110181, by rfl⟩ : syracuseStep 1175269 = 220363) (by norm_num)
theorem B519925 : Blo 307833 519925 := bbase (se 5 (by rfl) ⟨24371, by rfl⟩ : syracuseStep 519925 = 48743) (by norm_num)
theorem B520013 : Blo 307833 520013 := bbase (se 3 (by rfl) ⟨97502, by rfl⟩ : syracuseStep 520013 = 195005) (by norm_num)
theorem B1568645 : Blo 307833 1568645 := bbase (se 4 (by rfl) ⟨147060, by rfl⟩ : syracuseStep 1568645 = 294121) (by norm_num)
theorem B782237 : Blo 307833 782237 := bbase (se 3 (by rfl) ⟨146669, by rfl⟩ : syracuseStep 782237 = 293339) (by norm_num)
theorem B1896373 : Blo 307833 1896373 := bbase (se 5 (by rfl) ⟨88892, by rfl⟩ : syracuseStep 1896373 = 177785) (by norm_num)
theorem B520141 : Blo 307833 520141 := bbase (se 3 (by rfl) ⟨97526, by rfl⟩ : syracuseStep 520141 = 195053) (by norm_num)
theorem B1175573 : Blo 307833 1175573 := bbase (se 6 (by rfl) ⟨27552, by rfl⟩ : syracuseStep 1175573 = 55105) (by norm_num)
theorem B520229 : Blo 307833 520229 := bbase (se 4 (by rfl) ⟨48771, by rfl⟩ : syracuseStep 520229 = 97543) (by norm_num)
theorem B585805 : Blo 307833 585805 := bbase (se 3 (by rfl) ⟨109838, by rfl⟩ : syracuseStep 585805 = 219677) (by norm_num)
theorem B1044629 : Blo 307833 1044629 := bbase (se 6 (by rfl) ⟨24483, by rfl⟩ : syracuseStep 1044629 = 48967) (by norm_num)
theorem B520357 : Blo 307833 520357 := bbase (se 4 (by rfl) ⟨48783, by rfl⟩ : syracuseStep 520357 = 97567) (by norm_num)
theorem B585949 : Blo 307833 585949 := bbase (se 3 (by rfl) ⟨109865, by rfl⟩ : syracuseStep 585949 = 219731) (by norm_num)
theorem B782581 : Blo 307833 782581 := bbase (se 5 (by rfl) ⟨36683, by rfl⟩ : syracuseStep 782581 = 73367) (by norm_num)
theorem B749821 : Blo 307833 749821 := bbase (se 3 (by rfl) ⟨140591, by rfl⟩ : syracuseStep 749821 = 281183) (by norm_num)
theorem B520445 : Blo 307833 520445 := bbase (se 3 (by rfl) ⟨97583, by rfl⟩ : syracuseStep 520445 = 195167) (by norm_num)
theorem B782693 : Blo 307833 782693 := bbase (se 4 (by rfl) ⟨73377, by rfl⟩ : syracuseStep 782693 = 146755) (by norm_num)
theorem B520573 : Blo 307833 520573 := bbase (se 3 (by rfl) ⟨97607, by rfl⟩ : syracuseStep 520573 = 195215) (by norm_num)
theorem B586109 : Blo 307833 586109 := bbase (se 3 (by rfl) ⟨109895, by rfl⟩ : syracuseStep 586109 = 219791) (by norm_num)
theorem B881077 : Blo 307833 881077 := bbase (se 5 (by rfl) ⟨41300, by rfl⟩ : syracuseStep 881077 = 82601) (by norm_num)
theorem B520661 : Blo 307833 520661 := bbase (se 7 (by rfl) ⟨6101, by rfl⟩ : syracuseStep 520661 = 12203) (by norm_num)
theorem B389605 : Blo 307833 389605 := bbase (se 4 (by rfl) ⟨36525, by rfl⟩ : syracuseStep 389605 = 73051) (by norm_num)
theorem B586253 : Blo 307833 586253 := bbase (se 3 (by rfl) ⟨109922, by rfl⟩ : syracuseStep 586253 = 219845) (by norm_num)
theorem B782885 : Blo 307833 782885 := bbase (se 4 (by rfl) ⟨73395, by rfl⟩ : syracuseStep 782885 = 146791) (by norm_num)
theorem B389701 : Blo 307833 389701 := bbase (se 4 (by rfl) ⟨36534, by rfl⟩ : syracuseStep 389701 = 73069) (by norm_num)
theorem B1045061 : Blo 307833 1045061 := bbase (se 4 (by rfl) ⟨97974, by rfl⟩ : syracuseStep 1045061 = 195949) (by norm_num)
theorem B520789 : Blo 307833 520789 := bbase (se 8 (by rfl) ⟨3051, by rfl⟩ : syracuseStep 520789 = 6103) (by norm_num)
theorem B1110629 : Blo 307833 1110629 := bbase (se 4 (by rfl) ⟨104121, by rfl⟩ : syracuseStep 1110629 = 208243) (by norm_num)
theorem B848549 : Blo 307833 848549 := bbase (se 4 (by rfl) ⟨79551, by rfl⟩ : syracuseStep 848549 = 159103) (by norm_num)
theorem B946853 : Blo 307833 946853 := bbase (se 4 (by rfl) ⟨88767, by rfl⟩ : syracuseStep 946853 = 177535) (by norm_num)
theorem B520877 : Blo 307833 520877 := bbase (se 3 (by rfl) ⟨97664, by rfl⟩ : syracuseStep 520877 = 195329) (by norm_num)
theorem B488141 : Blo 307833 488141 := bbase (se 3 (by rfl) ⟨91526, by rfl⟩ : syracuseStep 488141 = 183053) (by norm_num)
theorem B389873 : Blo 307833 389873 := bbase (se 2 (by rfl) ⟨146202, by rfl⟩ : syracuseStep 389873 = 292405) (by norm_num)
theorem B389929 : Blo 307833 389929 := bbase (se 2 (by rfl) ⟨146223, by rfl⟩ : syracuseStep 389929 = 292447) (by norm_num)
theorem B521005 : Blo 307833 521005 := bbase (se 3 (by rfl) ⟨97688, by rfl⟩ : syracuseStep 521005 = 195377) (by norm_num)
theorem B586541 : Blo 307833 586541 := bbase (se 3 (by rfl) ⟨109976, by rfl⟩ : syracuseStep 586541 = 219953) (by norm_num)
theorem B783229 : Blo 307833 783229 := bbase (se 3 (by rfl) ⟨146855, by rfl⟩ : syracuseStep 783229 = 293711) (by norm_num)
theorem B521093 : Blo 307833 521093 := bbase (se 4 (by rfl) ⟨48852, by rfl⟩ : syracuseStep 521093 = 97705) (by norm_num)
theorem B390025 : Blo 307833 390025 := bbase (se 2 (by rfl) ⟨146259, by rfl⟩ : syracuseStep 390025 = 292519) (by norm_num)
theorem B586693 : Blo 307833 586693 := bbase (se 4 (by rfl) ⟨55002, by rfl⟩ : syracuseStep 586693 = 110005) (by norm_num)
theorem B783341 : Blo 307833 783341 := bbase (se 3 (by rfl) ⟨146876, by rfl⟩ : syracuseStep 783341 = 293753) (by norm_num)
theorem B1045493 : Blo 307833 1045493 := bbase (se 5 (by rfl) ⟨49007, by rfl⟩ : syracuseStep 1045493 = 98015) (by norm_num)
theorem B521221 : Blo 307833 521221 := bbase (se 4 (by rfl) ⟨48864, by rfl⟩ : syracuseStep 521221 = 97729) (by norm_num)
theorem B390197 : Blo 307833 390197 := bbase (se 5 (by rfl) ⟨18290, by rfl⟩ : syracuseStep 390197 = 36581) (by norm_num)
theorem B521309 : Blo 307833 521309 := bbase (se 3 (by rfl) ⟨97745, by rfl⟩ : syracuseStep 521309 = 195491) (by norm_num)
theorem B390253 : Blo 307833 390253 := bbase (se 3 (by rfl) ⟨73172, by rfl⟩ : syracuseStep 390253 = 146345) (by norm_num)
theorem B1569941 : Blo 307833 1569941 := bbase (se 6 (by rfl) ⟨36795, by rfl⟩ : syracuseStep 1569941 = 73591) (by norm_num)
theorem B1766549 : Blo 307833 1766549 := bbase (se 6 (by rfl) ⟨41403, by rfl⟩ : syracuseStep 1766549 = 82807) (by norm_num)
theorem B783533 : Blo 307833 783533 := bbase (se 3 (by rfl) ⟨146912, by rfl⟩ : syracuseStep 783533 = 293825) (by norm_num)
theorem B390349 : Blo 307833 390349 := bbase (se 3 (by rfl) ⟨73190, by rfl⟩ : syracuseStep 390349 = 146381) (by norm_num)
theorem B521437 : Blo 307833 521437 := bbase (se 3 (by rfl) ⟨97769, by rfl⟩ : syracuseStep 521437 = 195539) (by norm_num)
theorem B586997 : Blo 307833 586997 := bbase (se 5 (by rfl) ⟨27515, by rfl⟩ : syracuseStep 586997 = 55031) (by norm_num)
theorem B521525 : Blo 307833 521525 := bbase (se 5 (by rfl) ⟨24446, by rfl⟩ : syracuseStep 521525 = 48893) (by norm_num)
theorem B390521 : Blo 307833 390521 := bbase (se 2 (by rfl) ⟨146445, by rfl⟩ : syracuseStep 390521 = 292891) (by norm_num)
theorem B1045925 : Blo 307833 1045925 := bbase (se 4 (by rfl) ⟨98055, by rfl⟩ : syracuseStep 1045925 = 196111) (by norm_num)
theorem B390577 : Blo 307833 390577 := bbase (se 2 (by rfl) ⟨146466, by rfl⟩ : syracuseStep 390577 = 292933) (by norm_num)
theorem B521653 : Blo 307833 521653 := bbase (se 5 (by rfl) ⟨24452, by rfl⟩ : syracuseStep 521653 = 48905) (by norm_num)
theorem B783877 : Blo 307833 783877 := bbase (se 4 (by rfl) ⟨73488, by rfl⟩ : syracuseStep 783877 = 146977) (by norm_num)
theorem B882181 : Blo 307833 882181 := bbase (se 4 (by rfl) ⟨82704, by rfl⟩ : syracuseStep 882181 = 165409) (by norm_num)
theorem B521741 : Blo 307833 521741 := bbase (se 3 (by rfl) ⟨97826, by rfl⟩ : syracuseStep 521741 = 195653) (by norm_num)
theorem B390673 : Blo 307833 390673 := bbase (se 2 (by rfl) ⟨146502, by rfl⟩ : syracuseStep 390673 = 293005) (by norm_num)
theorem B783989 : Blo 307833 783989 := bbase (se 5 (by rfl) ⟨36749, by rfl⟩ : syracuseStep 783989 = 73499) (by norm_num)
theorem B521869 : Blo 307833 521869 := bbase (se 3 (by rfl) ⟨97850, by rfl⟩ : syracuseStep 521869 = 195701) (by norm_num)
theorem B390845 : Blo 307833 390845 := bbase (se 3 (by rfl) ⟨73283, by rfl⟩ : syracuseStep 390845 = 146567) (by norm_num)
theorem B521957 : Blo 307833 521957 := bbase (se 4 (by rfl) ⟨48933, by rfl⟩ : syracuseStep 521957 = 97867) (by norm_num)
theorem B390901 : Blo 307833 390901 := bbase (se 5 (by rfl) ⟨18323, by rfl⟩ : syracuseStep 390901 = 36647) (by norm_num)
theorem B784181 : Blo 307833 784181 := bbase (se 5 (by rfl) ⟨36758, by rfl⟩ : syracuseStep 784181 = 73517) (by norm_num)
theorem B390997 : Blo 307833 390997 := bbase (se 9 (by rfl) ⟨1145, by rfl⟩ : syracuseStep 390997 = 2291) (by norm_num)
theorem B1046357 : Blo 307833 1046357 := bbase (se 9 (by rfl) ⟨3065, by rfl⟩ : syracuseStep 1046357 = 6131) (by norm_num)
theorem B522085 : Blo 307833 522085 := bbase (se 4 (by rfl) ⟨48945, by rfl⟩ : syracuseStep 522085 = 97891) (by norm_num)
theorem B522173 : Blo 307833 522173 := bbase (se 3 (by rfl) ⟨97907, by rfl⟩ : syracuseStep 522173 = 195815) (by norm_num)
theorem B587749 : Blo 307833 587749 := bbase (se 4 (by rfl) ⟨55101, by rfl⟩ : syracuseStep 587749 = 110203) (by norm_num)
theorem B391169 : Blo 307833 391169 := bbase (se 2 (by rfl) ⟨146688, by rfl⟩ : syracuseStep 391169 = 293377) (by norm_num)
theorem B391225 : Blo 307833 391225 := bbase (se 2 (by rfl) ⟨146709, by rfl⟩ : syracuseStep 391225 = 293419) (by norm_num)
theorem B522301 : Blo 307833 522301 := bbase (se 3 (by rfl) ⟨97931, by rfl⟩ : syracuseStep 522301 = 195863) (by norm_num)
theorem B751693 : Blo 307833 751693 := bbase (se 3 (by rfl) ⟨140942, by rfl⟩ : syracuseStep 751693 = 281885) (by norm_num)
theorem B1177685 : Blo 307833 1177685 := bbase (se 8 (by rfl) ⟨6900, by rfl⟩ : syracuseStep 1177685 = 13801) (by norm_num)
theorem B587893 : Blo 307833 587893 := bbase (se 5 (by rfl) ⟨27557, by rfl⟩ : syracuseStep 587893 = 55115) (by norm_num)
theorem B784525 : Blo 307833 784525 := bbase (se 3 (by rfl) ⟨147098, by rfl⟩ : syracuseStep 784525 = 294197) (by norm_num)
theorem B522389 : Blo 307833 522389 := bbase (se 6 (by rfl) ⟨12243, by rfl⟩ : syracuseStep 522389 = 24487) (by norm_num)
theorem B391321 : Blo 307833 391321 := bbase (se 2 (by rfl) ⟨146745, by rfl⟩ : syracuseStep 391321 = 293491) (by norm_num)
theorem B784637 : Blo 307833 784637 := bbase (se 3 (by rfl) ⟨147119, by rfl⟩ : syracuseStep 784637 = 294239) (by norm_num)
theorem B1046789 : Blo 307833 1046789 := bbase (se 4 (by rfl) ⟨98136, by rfl⟩ : syracuseStep 1046789 = 196273) (by norm_num)
theorem B522517 : Blo 307833 522517 := bbase (se 6 (by rfl) ⟨12246, by rfl⟩ : syracuseStep 522517 = 24493) (by norm_num)
theorem B588053 : Blo 307833 588053 := bbase (se 6 (by rfl) ⟨13782, by rfl⟩ : syracuseStep 588053 = 27565) (by norm_num)
theorem B391493 : Blo 307833 391493 := bbase (se 4 (by rfl) ⟨36702, by rfl⟩ : syracuseStep 391493 = 73405) (by norm_num)
theorem B1603925 : Blo 307833 1603925 := bbase (se 10 (by rfl) ⟨2349, by rfl⟩ : syracuseStep 1603925 = 4699) (by norm_num)
theorem B555373 : Blo 307833 555373 := bbase (se 3 (by rfl) ⟨104132, by rfl⟩ : syracuseStep 555373 = 208265) (by norm_num)
theorem B522605 : Blo 307833 522605 := bbase (se 3 (by rfl) ⟨97988, by rfl⟩ : syracuseStep 522605 = 195977) (by norm_num)
theorem B1177973 : Blo 307833 1177973 := bbase (se 5 (by rfl) ⟨55217, by rfl⟩ : syracuseStep 1177973 = 110435) (by norm_num)
theorem B391549 : Blo 307833 391549 := bbase (se 3 (by rfl) ⟨73415, by rfl⟩ : syracuseStep 391549 = 146831) (by norm_num)
theorem B2521493 : Blo 307833 2521493 := bbase (se 6 (by rfl) ⟨59097, by rfl⟩ : syracuseStep 2521493 = 118195) (by norm_num)
theorem B1571237 : Blo 307833 1571237 := bbase (se 4 (by rfl) ⟨147303, by rfl⟩ : syracuseStep 1571237 = 294607) (by norm_num)
theorem B588197 : Blo 307833 588197 := bbase (se 4 (by rfl) ⟨55143, by rfl⟩ : syracuseStep 588197 = 110287) (by norm_num)
theorem B784829 : Blo 307833 784829 := bbase (se 3 (by rfl) ⟨147155, by rfl⟩ : syracuseStep 784829 = 294311) (by norm_num)
theorem B391645 : Blo 307833 391645 := bbase (se 3 (by rfl) ⟨73433, by rfl⟩ : syracuseStep 391645 = 146867) (by norm_num)
theorem B522733 : Blo 307833 522733 := bbase (se 3 (by rfl) ⟨98012, by rfl⟩ : syracuseStep 522733 = 196025) (by norm_num)
theorem B522821 : Blo 307833 522821 := bbase (se 4 (by rfl) ⟨49014, by rfl⟩ : syracuseStep 522821 = 98029) (by norm_num)
theorem B391817 : Blo 307833 391817 := bbase (se 2 (by rfl) ⟨146931, by rfl⟩ : syracuseStep 391817 = 293863) (by norm_num)
theorem B1047221 : Blo 307833 1047221 := bbase (se 5 (by rfl) ⟨49088, by rfl⟩ : syracuseStep 1047221 = 98177) (by norm_num)
theorem B391873 : Blo 307833 391873 := bbase (se 2 (by rfl) ⟨146952, by rfl⟩ : syracuseStep 391873 = 293905) (by norm_num)
theorem B522949 : Blo 307833 522949 := bbase (se 4 (by rfl) ⟨49026, by rfl⟩ : syracuseStep 522949 = 98053) (by norm_num)
theorem B588485 : Blo 307833 588485 := bbase (se 4 (by rfl) ⟨55170, by rfl⟩ : syracuseStep 588485 = 110341) (by norm_num)
theorem B785173 : Blo 307833 785173 := bbase (se 6 (by rfl) ⟨18402, by rfl⟩ : syracuseStep 785173 = 36805) (by norm_num)
theorem B523037 : Blo 307833 523037 := bbase (se 3 (by rfl) ⟨98069, by rfl⟩ : syracuseStep 523037 = 196139) (by norm_num)
theorem B391969 : Blo 307833 391969 := bbase (se 2 (by rfl) ⟨146988, by rfl⟩ : syracuseStep 391969 = 293977) (by norm_num)
theorem B1997621 : Blo 307833 1997621 := bbase (se 5 (by rfl) ⟨93638, by rfl⟩ : syracuseStep 1997621 = 187277) (by norm_num)
theorem B588637 : Blo 307833 588637 := bbase (se 3 (by rfl) ⟨110369, by rfl⟩ : syracuseStep 588637 = 220739) (by norm_num)
theorem B359273 : Blo 307833 359273 := bbase (se 2 (by rfl) ⟨134727, by rfl⟩ : syracuseStep 359273 = 269455) (by norm_num)
theorem B785285 : Blo 307833 785285 := bbase (se 4 (by rfl) ⟨73620, by rfl⟩ : syracuseStep 785285 = 147241) (by norm_num)
theorem B523165 : Blo 307833 523165 := bbase (se 3 (by rfl) ⟨98093, by rfl⟩ : syracuseStep 523165 = 196187) (by norm_num)
theorem B392141 : Blo 307833 392141 := bbase (se 3 (by rfl) ⟨73526, by rfl⟩ : syracuseStep 392141 = 147053) (by norm_num)
theorem B883685 : Blo 307833 883685 := bbase (se 4 (by rfl) ⟨82845, by rfl⟩ : syracuseStep 883685 = 165691) (by norm_num)
theorem B523253 : Blo 307833 523253 := bbase (se 5 (by rfl) ⟨24527, by rfl⟩ : syracuseStep 523253 = 49055) (by norm_num)
theorem B392197 : Blo 307833 392197 := bbase (se 4 (by rfl) ⟨36768, by rfl⟩ : syracuseStep 392197 = 73537) (by norm_num)
theorem B785477 : Blo 307833 785477 := bbase (se 4 (by rfl) ⟨73638, by rfl⟩ : syracuseStep 785477 = 147277) (by norm_num)
theorem B392293 : Blo 307833 392293 := bbase (se 4 (by rfl) ⟨36777, by rfl⟩ : syracuseStep 392293 = 73555) (by norm_num)
theorem B1047653 : Blo 307833 1047653 := bbase (se 4 (by rfl) ⟨98217, by rfl⟩ : syracuseStep 1047653 = 196435) (by norm_num)
theorem B523381 : Blo 307833 523381 := bbase (se 5 (by rfl) ⟨24533, by rfl⟩ : syracuseStep 523381 = 49067) (by norm_num)
theorem B588941 : Blo 307833 588941 := bbase (se 3 (by rfl) ⟨110426, by rfl⟩ : syracuseStep 588941 = 220853) (by norm_num)
theorem B523469 : Blo 307833 523469 := bbase (se 3 (by rfl) ⟨98150, by rfl⟩ : syracuseStep 523469 = 196301) (by norm_num)
theorem B392465 : Blo 307833 392465 := bbase (se 2 (by rfl) ⟨147174, by rfl⟩ : syracuseStep 392465 = 294349) (by norm_num)
theorem B392521 : Blo 307833 392521 := bbase (se 2 (by rfl) ⟨147195, by rfl⟩ : syracuseStep 392521 = 294391) (by norm_num)
theorem B523597 : Blo 307833 523597 := bbase (se 3 (by rfl) ⟨98174, by rfl⟩ : syracuseStep 523597 = 196349) (by norm_num)
theorem B785821 : Blo 307833 785821 := bbase (se 3 (by rfl) ⟨147341, by rfl⟩ : syracuseStep 785821 = 294683) (by norm_num)
theorem B523685 : Blo 307833 523685 := bbase (se 4 (by rfl) ⟨49095, by rfl⟩ : syracuseStep 523685 = 98191) (by norm_num)
theorem B392617 : Blo 307833 392617 := bbase (se 2 (by rfl) ⟨147231, by rfl⟩ : syracuseStep 392617 = 294463) (by norm_num)
theorem B556541 : Blo 307833 556541 := bbase (se 3 (by rfl) ⟨104351, by rfl⟩ : syracuseStep 556541 = 208703) (by norm_num)
theorem B785933 : Blo 307833 785933 := bbase (se 3 (by rfl) ⟨147362, by rfl⟩ : syracuseStep 785933 = 294725) (by norm_num)
theorem B1048085 : Blo 307833 1048085 := bbase (se 6 (by rfl) ⟨24564, by rfl⟩ : syracuseStep 1048085 = 49129) (by norm_num)
theorem B1179157 : Blo 307833 1179157 := bbase (se 6 (by rfl) ⟨27636, by rfl⟩ : syracuseStep 1179157 = 55273) (by norm_num)
theorem B523813 : Blo 307833 523813 := bbase (se 4 (by rfl) ⟨49107, by rfl⟩ : syracuseStep 523813 = 98215) (by norm_num)
theorem B392789 : Blo 307833 392789 := bbase (se 8 (by rfl) ⟨2301, by rfl⟩ : syracuseStep 392789 = 4603) (by norm_num)
theorem B523901 : Blo 307833 523901 := bbase (se 3 (by rfl) ⟨98231, by rfl⟩ : syracuseStep 523901 = 196463) (by norm_num)
theorem B392845 : Blo 307833 392845 := bbase (se 3 (by rfl) ⟨73658, by rfl⟩ : syracuseStep 392845 = 147317) (by norm_num)
theorem B1572533 : Blo 307833 1572533 := bbase (se 5 (by rfl) ⟨73712, by rfl⟩ : syracuseStep 1572533 = 147425) (by norm_num)
theorem B786125 : Blo 307833 786125 := bbase (se 3 (by rfl) ⟨147398, by rfl⟩ : syracuseStep 786125 = 294797) (by norm_num)
theorem B425677 : Blo 307833 425677 := bbase (se 3 (by rfl) ⟨79814, by rfl⟩ : syracuseStep 425677 = 159629) (by norm_num)
theorem B392941 : Blo 307833 392941 := bbase (se 3 (by rfl) ⟨73676, by rfl⟩ : syracuseStep 392941 = 147353) (by norm_num)
theorem B524029 : Blo 307833 524029 := bbase (se 3 (by rfl) ⟨98255, by rfl⟩ : syracuseStep 524029 = 196511) (by norm_num)
theorem B1179461 : Blo 307833 1179461 := bbase (se 4 (by rfl) ⟨110574, by rfl⟩ : syracuseStep 1179461 = 221149) (by norm_num)
theorem B1408853 : Blo 307833 1408853 := bbase (se 9 (by rfl) ⟨4127, by rfl⟩ : syracuseStep 1408853 = 8255) (by norm_num)
theorem B524117 : Blo 307833 524117 := bbase (se 9 (by rfl) ⟨1535, by rfl⟩ : syracuseStep 524117 = 3071) (by norm_num)
theorem B589693 : Blo 307833 589693 := bbase (se 3 (by rfl) ⟨110567, by rfl⟩ : syracuseStep 589693 = 221135) (by norm_num)
theorem B393113 : Blo 307833 393113 := bbase (se 2 (by rfl) ⟨147417, by rfl⟩ : syracuseStep 393113 = 294835) (by norm_num)
theorem B1048517 : Blo 307833 1048517 := bbase (se 4 (by rfl) ⟨98298, by rfl⟩ : syracuseStep 1048517 = 196597) (by norm_num)
theorem B393169 : Blo 307833 393169 := bbase (se 2 (by rfl) ⟨147438, by rfl⟩ : syracuseStep 393169 = 294877) (by norm_num)
theorem B524245 : Blo 307833 524245 := bbase (se 7 (by rfl) ⟨6143, by rfl⟩ : syracuseStep 524245 = 12287) (by norm_num)
theorem B5046229 : Blo 307833 5046229 := bbase (se 7 (by rfl) ⟨59135, by rfl⟩ : syracuseStep 5046229 = 118271) (by norm_num)
theorem B557045 : Blo 307833 557045 := bbase (se 5 (by rfl) ⟨26111, by rfl⟩ : syracuseStep 557045 = 52223) (by norm_num)
theorem B786449 : Blo 307833 786449 := bstep (se 2 (by rfl) ⟨294918, by rfl⟩ : syracuseStep 786449 = 589837) B589837
theorem B1048625 : Blo 307833 1048625 := bstep (se 2 (by rfl) ⟨393234, by rfl⟩ : syracuseStep 1048625 = 786469) B786469
theorem B524353 : Blo 307833 524353 := bstep (se 2 (by rfl) ⟨196632, by rfl⟩ : syracuseStep 524353 = 393265) B393265
theorem B524387 : Blo 307833 524387 := bstep (se 1 (by rfl) ⟨393290, by rfl⟩ : syracuseStep 524387 = 786581) B786581
theorem B393331 : Blo 307833 393331 := bstep (se 1 (by rfl) ⟨294998, by rfl⟩ : syracuseStep 393331 = 589997) B589997
theorem B557219 : Blo 307833 557219 := bstep (se 1 (by rfl) ⟨417914, by rfl⟩ : syracuseStep 557219 = 835829) B835829
theorem B393427 : Blo 307833 393427 := bstep (se 1 (by rfl) ⟨295070, by rfl⟩ : syracuseStep 393427 = 590141) B590141
theorem B524515 : Blo 307833 524515 := bstep (se 1 (by rfl) ⟨393386, by rfl⟩ : syracuseStep 524515 = 786773) B786773
theorem B1179917 : Blo 307833 1179917 := bstep (se 3 (by rfl) ⟨221234, by rfl⟩ : syracuseStep 1179917 = 442469) B442469
theorem B590179 : Blo 307833 590179 := bstep (se 1 (by rfl) ⟨442634, by rfl⟩ : syracuseStep 590179 = 885269) B885269
theorem B524657 : Blo 307833 524657 := bstep (se 2 (by rfl) ⟨196746, by rfl⟩ : syracuseStep 524657 = 393493) B393493
theorem B524785 : Blo 307833 524785 := bstep (se 2 (by rfl) ⟨196794, by rfl⟩ : syracuseStep 524785 = 393589) B393589
theorem B524819 : Blo 307833 524819 := bstep (se 1 (by rfl) ⟨393614, by rfl⟩ : syracuseStep 524819 = 787229) B787229
theorem B1049165 : Blo 307833 1049165 := bstep (se 3 (by rfl) ⟨196718, by rfl⟩ : syracuseStep 1049165 = 393437) B393437
theorem B885325 : Blo 307833 885325 := bstep (se 3 (by rfl) ⟨165998, by rfl⟩ : syracuseStep 885325 = 331997) B331997
theorem B1049219 : Blo 307833 1049219 := bstep (se 1 (by rfl) ⟨786914, by rfl⟩ : syracuseStep 1049219 = 1573829) B1573829
theorem B524947 : Blo 307833 524947 := bstep (se 1 (by rfl) ⟨393710, by rfl⟩ : syracuseStep 524947 = 787421) B787421
theorem B1704611 : Blo 307833 1704611 := bstep (se 1 (by rfl) ⟨1278458, by rfl⟩ : syracuseStep 1704611 = 2556917) B2556917
theorem B393923 : Blo 307833 393923 := bstep (se 1 (by rfl) ⟨295442, by rfl⟩ : syracuseStep 393923 = 590885) B590885
theorem B6062789 : Blo 307833 6062789 := bstep (se 4 (by rfl) ⟨568386, by rfl⟩ : syracuseStep 6062789 = 1136773) B1136773
theorem B885485 : Blo 307833 885485 := bstep (se 3 (by rfl) ⟨166028, by rfl⟩ : syracuseStep 885485 = 332057) B332057
theorem B525089 : Blo 307833 525089 := bstep (se 2 (by rfl) ⟨196908, by rfl⟩ : syracuseStep 525089 = 393817) B393817
theorem B1573667 : Blo 307833 1573667 := bstep (se 1 (by rfl) ⟨1180250, by rfl⟩ : syracuseStep 1573667 = 2360501) B2360501
theorem B590627 : Blo 307833 590627 := bstep (se 1 (by rfl) ⟨442970, by rfl⟩ : syracuseStep 590627 = 885941) B885941
theorem B1049489 : Blo 307833 1049489 := bstep (se 2 (by rfl) ⟨393558, by rfl⟩ : syracuseStep 1049489 = 787117) B787117
theorem B525217 : Blo 307833 525217 := bstep (se 2 (by rfl) ⟨196956, by rfl⟩ : syracuseStep 525217 = 393913) B393913
theorem B885667 : Blo 307833 885667 := bstep (se 1 (by rfl) ⟨664250, by rfl⟩ : syracuseStep 885667 = 1328501) B1328501
theorem B558019 : Blo 307833 558019 := bstep (se 1 (by rfl) ⟨418514, by rfl⟩ : syracuseStep 558019 = 837029) B837029
theorem B525251 : Blo 307833 525251 := bstep (se 1 (by rfl) ⟨393938, by rfl⟩ : syracuseStep 525251 = 787877) B787877
theorem B787441 : Blo 307833 787441 := bstep (se 2 (by rfl) ⟨295290, by rfl⟩ : syracuseStep 787441 = 590581) B590581
theorem B590915 : Blo 307833 590915 := bstep (se 1 (by rfl) ⟨443186, by rfl⟩ : syracuseStep 590915 = 886373) B886373
theorem B525379 : Blo 307833 525379 := bstep (se 1 (by rfl) ⟨394034, by rfl⟩ : syracuseStep 525379 = 788069) B788069
theorem B2393201 : Blo 307833 2393201 := bstep (se 2 (by rfl) ⟨897450, by rfl⟩ : syracuseStep 2393201 = 1794901) B1794901
theorem B525521 : Blo 307833 525521 := bstep (se 2 (by rfl) ⟨197070, by rfl⟩ : syracuseStep 525521 = 394141) B394141
theorem B1672433 : Blo 307833 1672433 := bstep (se 2 (by rfl) ⟨627162, by rfl⟩ : syracuseStep 1672433 = 1254325) B1254325
theorem B787715 : Blo 307833 787715 := bstep (se 1 (by rfl) ⟨590786, by rfl⟩ : syracuseStep 787715 = 1181573) B1181573
theorem B525649 : Blo 307833 525649 := bstep (se 2 (by rfl) ⟨197118, by rfl⟩ : syracuseStep 525649 = 394237) B394237
theorem B525683 : Blo 307833 525683 := bstep (se 1 (by rfl) ⟨394262, by rfl⟩ : syracuseStep 525683 = 788525) B788525
theorem B394627 : Blo 307833 394627 := bstep (se 1 (by rfl) ⟨295970, by rfl⟩ : syracuseStep 394627 = 591941) B591941
theorem B1050029 : Blo 307833 1050029 := bstep (se 3 (by rfl) ⟨196880, by rfl⟩ : syracuseStep 1050029 = 393761) B393761
theorem B787907 : Blo 307833 787907 := bstep (se 1 (by rfl) ⟨590930, by rfl⟩ : syracuseStep 787907 = 1181861) B1181861
theorem B1050083 : Blo 307833 1050083 := bstep (se 1 (by rfl) ⟨787562, by rfl⟩ : syracuseStep 1050083 = 1575125) B1575125
theorem B525811 : Blo 307833 525811 := bstep (se 1 (by rfl) ⟨394358, by rfl⟩ : syracuseStep 525811 = 788717) B788717
theorem B558659 : Blo 307833 558659 := bstep (se 1 (by rfl) ⟨418994, by rfl⟩ : syracuseStep 558659 = 837989) B837989
theorem B1574477 : Blo 307833 1574477 := bstep (se 3 (by rfl) ⟨295214, by rfl⟩ : syracuseStep 1574477 = 590429) B590429
theorem B525953 : Blo 307833 525953 := bstep (se 2 (by rfl) ⟨197232, by rfl⟩ : syracuseStep 525953 = 394465) B394465
theorem B1050353 : Blo 307833 1050353 := bstep (se 2 (by rfl) ⟨393882, by rfl⟩ : syracuseStep 1050353 = 787765) B787765
theorem B526081 : Blo 307833 526081 := bstep (se 2 (by rfl) ⟨197280, by rfl⟩ : syracuseStep 526081 = 394561) B394561
theorem B526115 : Blo 307833 526115 := bstep (se 1 (by rfl) ⟨394586, by rfl⟩ : syracuseStep 526115 = 789173) B789173
theorem B3573557 : Blo 307833 3573557 := bstep (se 5 (by rfl) ⟨167510, by rfl⟩ : syracuseStep 3573557 = 335021) B335021
theorem B591857 : Blo 307833 591857 := bstep (se 2 (by rfl) ⟨221946, by rfl⟩ : syracuseStep 591857 = 443893) B443893
theorem B657553 : Blo 307833 657553 := bstep (se 2 (by rfl) ⟨246582, by rfl⟩ : syracuseStep 657553 = 493165) B493165
theorem B493793 : Blo 307833 493793 := bstep (se 2 (by rfl) ⟨185172, by rfl⟩ : syracuseStep 493793 = 370345) B370345
theorem B1050893 : Blo 307833 1050893 := bstep (se 3 (by rfl) ⟨197042, by rfl⟩ : syracuseStep 1050893 = 394085) B394085
theorem B887057 : Blo 307833 887057 := bstep (se 2 (by rfl) ⟨332646, by rfl⟩ : syracuseStep 887057 = 665293) B665293
theorem B1050947 : Blo 307833 1050947 := bstep (se 1 (by rfl) ⟨788210, by rfl⟩ : syracuseStep 1050947 = 1576421) B1576421
theorem B788849 : Blo 307833 788849 := bstep (se 2 (by rfl) ⟨295818, by rfl⟩ : syracuseStep 788849 = 591637) B591637
theorem B657809 : Blo 307833 657809 := bstep (se 2 (by rfl) ⟨246678, by rfl⟩ : syracuseStep 657809 = 493357) B493357
theorem B493985 : Blo 307833 493985 := bstep (se 2 (by rfl) ⟨185244, by rfl⟩ : syracuseStep 493985 = 370489) B370489
theorem B788899 : Blo 307833 788899 := bstep (se 1 (by rfl) ⟨591674, by rfl⟩ : syracuseStep 788899 = 1183349) B1183349
theorem B559633 : Blo 307833 559633 := bstep (se 2 (by rfl) ⟨209862, by rfl⟩ : syracuseStep 559633 = 419725) B419725
theorem B789041 : Blo 307833 789041 := bstep (se 2 (by rfl) ⟨295890, by rfl⟩ : syracuseStep 789041 = 591781) B591781
theorem B1051217 : Blo 307833 1051217 := bstep (se 2 (by rfl) ⟨394206, by rfl⟩ : syracuseStep 1051217 = 788413) B788413
theorem B625315 : Blo 307833 625315 := bstep (se 1 (by rfl) ⟨468986, by rfl⟩ : syracuseStep 625315 = 937973) B937973
theorem B1641329 : Blo 307833 1641329 := bstep (se 2 (by rfl) ⟨615498, by rfl⟩ : syracuseStep 1641329 = 1230997) B1230997
theorem B461777 : Blo 307833 461777 := bstep (se 2 (by rfl) ⟨173166, by rfl⟩ : syracuseStep 461777 = 346333) B346333
theorem B461795 : Blo 307833 461795 := bstep (se 1 (by rfl) ⟨346346, by rfl⟩ : syracuseStep 461795 = 692693) B692693
theorem B461825 : Blo 307833 461825 := bstep (se 2 (by rfl) ⟨173184, by rfl⟩ : syracuseStep 461825 = 346369) B346369
theorem B461843 : Blo 307833 461843 := bstep (se 1 (by rfl) ⟨346382, by rfl⟩ : syracuseStep 461843 = 692765) B692765
theorem B461873 : Blo 307833 461873 := bstep (se 2 (by rfl) ⟨173202, by rfl⟩ : syracuseStep 461873 = 346405) B346405
theorem B461891 : Blo 307833 461891 := bstep (se 1 (by rfl) ⟨346418, by rfl⟩ : syracuseStep 461891 = 692837) B692837
theorem B1117261 : Blo 307833 1117261 := bstep (se 3 (by rfl) ⟨209486, by rfl⟩ : syracuseStep 1117261 = 418973) B418973
theorem B461921 : Blo 307833 461921 := bstep (se 2 (by rfl) ⟨173220, by rfl⟩ : syracuseStep 461921 = 346441) B346441
theorem B1051757 : Blo 307833 1051757 := bstep (se 3 (by rfl) ⟨197204, by rfl⟩ : syracuseStep 1051757 = 394409) B394409
theorem B1182833 : Blo 307833 1182833 := bstep (se 2 (by rfl) ⟨443562, by rfl⟩ : syracuseStep 1182833 = 887125) B887125
theorem B461939 : Blo 307833 461939 := bstep (se 1 (by rfl) ⟨346454, by rfl⟩ : syracuseStep 461939 = 692909) B692909
theorem B461969 : Blo 307833 461969 := bstep (se 2 (by rfl) ⟨173238, by rfl⟩ : syracuseStep 461969 = 346477) B346477
theorem B461987 : Blo 307833 461987 := bstep (se 1 (by rfl) ⟨346490, by rfl⟩ : syracuseStep 461987 = 692981) B692981
theorem B1051811 : Blo 307833 1051811 := bstep (se 1 (by rfl) ⟨788858, by rfl⟩ : syracuseStep 1051811 = 1577717) B1577717
theorem B756913 : Blo 307833 756913 := bstep (se 2 (by rfl) ⟨283842, by rfl⟩ : syracuseStep 756913 = 567685) B567685
theorem B462017 : Blo 307833 462017 := bstep (se 2 (by rfl) ⟨173256, by rfl⟩ : syracuseStep 462017 = 346513) B346513
theorem B527555 : Blo 307833 527555 := bstep (se 1 (by rfl) ⟨395666, by rfl⟩ : syracuseStep 527555 = 791333) B791333
theorem B462035 : Blo 307833 462035 := bstep (se 1 (by rfl) ⟨346526, by rfl⟩ : syracuseStep 462035 = 693053) B693053
theorem B462065 : Blo 307833 462065 := bstep (se 2 (by rfl) ⟨173274, by rfl⟩ : syracuseStep 462065 = 346549) B346549
theorem B462083 : Blo 307833 462083 := bstep (se 1 (by rfl) ⟨346562, by rfl⟩ : syracuseStep 462083 = 693125) B693125
theorem B462113 : Blo 307833 462113 := bstep (se 2 (by rfl) ⟨173292, by rfl⟩ : syracuseStep 462113 = 346585) B346585
theorem B462131 : Blo 307833 462131 := bstep (se 1 (by rfl) ⟨346598, by rfl⟩ : syracuseStep 462131 = 693197) B693197
theorem B462161 : Blo 307833 462161 := bstep (se 2 (by rfl) ⟨173310, by rfl⟩ : syracuseStep 462161 = 346621) B346621
theorem B462179 : Blo 307833 462179 := bstep (se 1 (by rfl) ⟨346634, by rfl⟩ : syracuseStep 462179 = 693269) B693269
theorem B462209 : Blo 307833 462209 := bstep (se 2 (by rfl) ⟨173328, by rfl⟩ : syracuseStep 462209 = 346657) B346657
theorem B462227 : Blo 307833 462227 := bstep (se 1 (by rfl) ⟨346670, by rfl⟩ : syracuseStep 462227 = 693341) B693341
theorem B462257 : Blo 307833 462257 := bstep (se 2 (by rfl) ⟨173346, by rfl⟩ : syracuseStep 462257 = 346693) B346693
theorem B1052081 : Blo 307833 1052081 := bstep (se 2 (by rfl) ⟨394530, by rfl⟩ : syracuseStep 1052081 = 789061) B789061
theorem B462275 : Blo 307833 462275 := bstep (se 1 (by rfl) ⟨346706, by rfl⟩ : syracuseStep 462275 = 693413) B693413
theorem B462305 : Blo 307833 462305 := bstep (se 2 (by rfl) ⟨173364, by rfl⟩ : syracuseStep 462305 = 346729) B346729
theorem B462323 : Blo 307833 462323 := bstep (se 1 (by rfl) ⟨346742, by rfl⟩ : syracuseStep 462323 = 693485) B693485
theorem B462353 : Blo 307833 462353 := bstep (se 2 (by rfl) ⟨173382, by rfl⟩ : syracuseStep 462353 = 346765) B346765
theorem B462371 : Blo 307833 462371 := bstep (se 1 (by rfl) ⟨346778, by rfl⟩ : syracuseStep 462371 = 693557) B693557
theorem B396851 : Blo 307833 396851 := bstep (se 1 (by rfl) ⟨297638, by rfl⟩ : syracuseStep 396851 = 595277) B595277
theorem B462401 : Blo 307833 462401 := bstep (se 2 (by rfl) ⟨173400, by rfl⟩ : syracuseStep 462401 = 346801) B346801
theorem B462419 : Blo 307833 462419 := bstep (se 1 (by rfl) ⟨346814, by rfl⟩ : syracuseStep 462419 = 693629) B693629
theorem B462449 : Blo 307833 462449 := bstep (se 2 (by rfl) ⟨173418, by rfl⟩ : syracuseStep 462449 = 346837) B346837
theorem B462467 : Blo 307833 462467 := bstep (se 1 (by rfl) ⟨346850, by rfl⟩ : syracuseStep 462467 = 693701) B693701
theorem B462497 : Blo 307833 462497 := bstep (se 2 (by rfl) ⟨173436, by rfl⟩ : syracuseStep 462497 = 346873) B346873
theorem B659107 : Blo 307833 659107 := bstep (se 1 (by rfl) ⟨494330, by rfl⟩ : syracuseStep 659107 = 988661) B988661
theorem B462515 : Blo 307833 462515 := bstep (se 1 (by rfl) ⟨346886, by rfl⟩ : syracuseStep 462515 = 693773) B693773
theorem B462545 : Blo 307833 462545 := bstep (se 2 (by rfl) ⟨173454, by rfl⟩ : syracuseStep 462545 = 346909) B346909
theorem B462563 : Blo 307833 462563 := bstep (se 1 (by rfl) ⟨346922, by rfl⟩ : syracuseStep 462563 = 693845) B693845
theorem B462593 : Blo 307833 462593 := bstep (se 2 (by rfl) ⟨173472, by rfl⟩ : syracuseStep 462593 = 346945) B346945
theorem B462611 : Blo 307833 462611 := bstep (se 1 (by rfl) ⟨346958, by rfl⟩ : syracuseStep 462611 = 693917) B693917
theorem B462641 : Blo 307833 462641 := bstep (se 2 (by rfl) ⟨173490, by rfl⟩ : syracuseStep 462641 = 346981) B346981
theorem B462659 : Blo 307833 462659 := bstep (se 1 (by rfl) ⟨346994, by rfl⟩ : syracuseStep 462659 = 693989) B693989
theorem B462689 : Blo 307833 462689 := bstep (se 2 (by rfl) ⟨173508, by rfl⟩ : syracuseStep 462689 = 347017) B347017
theorem B462707 : Blo 307833 462707 := bstep (se 1 (by rfl) ⟨347030, by rfl⟩ : syracuseStep 462707 = 694061) B694061
theorem B462737 : Blo 307833 462737 := bstep (se 2 (by rfl) ⟨173526, by rfl⟩ : syracuseStep 462737 = 347053) B347053
theorem B462755 : Blo 307833 462755 := bstep (se 1 (by rfl) ⟨347066, by rfl⟩ : syracuseStep 462755 = 694133) B694133
theorem B462785 : Blo 307833 462785 := bstep (se 2 (by rfl) ⟨173544, by rfl⟩ : syracuseStep 462785 = 347089) B347089
theorem B626627 : Blo 307833 626627 := bstep (se 1 (by rfl) ⟨469970, by rfl⟩ : syracuseStep 626627 = 939941) B939941
theorem B462803 : Blo 307833 462803 := bstep (se 1 (by rfl) ⟨347102, by rfl⟩ : syracuseStep 462803 = 694205) B694205
theorem B462833 : Blo 307833 462833 := bstep (se 2 (by rfl) ⟨173562, by rfl⟩ : syracuseStep 462833 = 347125) B347125
theorem B659441 : Blo 307833 659441 := bstep (se 2 (by rfl) ⟨247290, by rfl⟩ : syracuseStep 659441 = 494581) B494581
theorem B462851 : Blo 307833 462851 := bstep (se 1 (by rfl) ⟨347138, by rfl⟩ : syracuseStep 462851 = 694277) B694277
theorem B462881 : Blo 307833 462881 := bstep (se 2 (by rfl) ⟨173580, by rfl⟩ : syracuseStep 462881 = 347161) B347161
theorem B462899 : Blo 307833 462899 := bstep (se 1 (by rfl) ⟨347174, by rfl⟩ : syracuseStep 462899 = 694349) B694349
theorem B462929 : Blo 307833 462929 := bstep (se 2 (by rfl) ⟨173598, by rfl⟩ : syracuseStep 462929 = 347197) B347197
theorem B462947 : Blo 307833 462947 := bstep (se 1 (by rfl) ⟨347210, by rfl⟩ : syracuseStep 462947 = 694421) B694421
theorem B495715 : Blo 307833 495715 := bstep (se 1 (by rfl) ⟨371786, by rfl⟩ : syracuseStep 495715 = 743573) B743573
theorem B462977 : Blo 307833 462977 := bstep (se 2 (by rfl) ⟨173616, by rfl⟩ : syracuseStep 462977 = 347233) B347233
theorem B462995 : Blo 307833 462995 := bstep (se 1 (by rfl) ⟨347246, by rfl⟩ : syracuseStep 462995 = 694493) B694493
theorem B463025 : Blo 307833 463025 := bstep (se 2 (by rfl) ⟨173634, by rfl⟩ : syracuseStep 463025 = 347269) B347269
theorem B463043 : Blo 307833 463043 := bstep (se 1 (by rfl) ⟨347282, by rfl⟩ : syracuseStep 463043 = 694565) B694565
theorem B495811 : Blo 307833 495811 := bstep (se 1 (by rfl) ⟨371858, by rfl⟩ : syracuseStep 495811 = 743717) B743717
theorem B463073 : Blo 307833 463073 := bstep (se 2 (by rfl) ⟨173652, by rfl⟩ : syracuseStep 463073 = 347305) B347305
theorem B1675505 : Blo 307833 1675505 := bstep (se 2 (by rfl) ⟨628314, by rfl⟩ : syracuseStep 1675505 = 1256629) B1256629
theorem B463091 : Blo 307833 463091 := bstep (se 1 (by rfl) ⟨347318, by rfl⟩ : syracuseStep 463091 = 694637) B694637
theorem B463121 : Blo 307833 463121 := bstep (se 2 (by rfl) ⟨173670, by rfl⟩ : syracuseStep 463121 = 347341) B347341
theorem B463139 : Blo 307833 463139 := bstep (se 1 (by rfl) ⟨347354, by rfl⟩ : syracuseStep 463139 = 694709) B694709
theorem B463169 : Blo 307833 463169 := bstep (se 2 (by rfl) ⟨173688, by rfl⟩ : syracuseStep 463169 = 347377) B347377
theorem B463187 : Blo 307833 463187 := bstep (se 1 (by rfl) ⟨347390, by rfl⟩ : syracuseStep 463187 = 694781) B694781
theorem B495971 : Blo 307833 495971 := bstep (se 1 (by rfl) ⟨371978, by rfl⟩ : syracuseStep 495971 = 743957) B743957
theorem B463217 : Blo 307833 463217 := bstep (se 2 (by rfl) ⟨173706, by rfl⟩ : syracuseStep 463217 = 347413) B347413
theorem B332147 : Blo 307833 332147 := bstep (se 1 (by rfl) ⟨249110, by rfl⟩ : syracuseStep 332147 = 498221) B498221
theorem B463235 : Blo 307833 463235 := bstep (se 1 (by rfl) ⟨347426, by rfl⟩ : syracuseStep 463235 = 694853) B694853
theorem B463265 : Blo 307833 463265 := bstep (se 2 (by rfl) ⟨173724, by rfl⟩ : syracuseStep 463265 = 347449) B347449
theorem B692657 : Blo 307833 692657 := bstep (se 2 (by rfl) ⟨259746, by rfl⟩ : syracuseStep 692657 = 519493) B519493
theorem B1577393 : Blo 307833 1577393 := bstep (se 2 (by rfl) ⟨591522, by rfl⟩ : syracuseStep 1577393 = 1183045) B1183045
theorem B463283 : Blo 307833 463283 := bstep (se 1 (by rfl) ⟨347462, by rfl⟩ : syracuseStep 463283 = 694925) B694925
theorem B692675 : Blo 307833 692675 := bstep (se 1 (by rfl) ⟨519506, by rfl⟩ : syracuseStep 692675 = 1039013) B1039013
theorem B1774021 : Blo 307833 1774021 := bstep (se 4 (by rfl) ⟨166314, by rfl⟩ : syracuseStep 1774021 = 332629) B332629
theorem B1315277 : Blo 307833 1315277 := bstep (se 3 (by rfl) ⟨246614, by rfl⟩ : syracuseStep 1315277 = 493229) B493229
theorem B463313 : Blo 307833 463313 := bstep (se 2 (by rfl) ⟨173742, by rfl⟩ : syracuseStep 463313 = 347485) B347485
theorem B463331 : Blo 307833 463331 := bstep (se 1 (by rfl) ⟨347498, by rfl⟩ : syracuseStep 463331 = 694997) B694997
theorem B463361 : Blo 307833 463361 := bstep (se 2 (by rfl) ⟨173760, by rfl⟩ : syracuseStep 463361 = 347521) B347521
theorem B463379 : Blo 307833 463379 := bstep (se 1 (by rfl) ⟨347534, by rfl⟩ : syracuseStep 463379 = 695069) B695069
theorem B463409 : Blo 307833 463409 := bstep (se 2 (by rfl) ⟨173778, by rfl⟩ : syracuseStep 463409 = 347557) B347557
theorem B463427 : Blo 307833 463427 := bstep (se 1 (by rfl) ⟨347570, by rfl⟩ : syracuseStep 463427 = 695141) B695141
theorem B463457 : Blo 307833 463457 := bstep (se 2 (by rfl) ⟨173796, by rfl⟩ : syracuseStep 463457 = 347593) B347593
theorem B463475 : Blo 307833 463475 := bstep (se 1 (by rfl) ⟨347606, by rfl⟩ : syracuseStep 463475 = 695213) B695213
theorem B463505 : Blo 307833 463505 := bstep (se 2 (by rfl) ⟨173814, by rfl⟩ : syracuseStep 463505 = 347629) B347629
theorem B463523 : Blo 307833 463523 := bstep (se 1 (by rfl) ⟨347642, by rfl⟩ : syracuseStep 463523 = 695285) B695285
theorem B463553 : Blo 307833 463553 := bstep (se 2 (by rfl) ⟨173832, by rfl⟩ : syracuseStep 463553 = 347665) B347665
theorem B692945 : Blo 307833 692945 := bstep (se 2 (by rfl) ⟨259854, by rfl⟩ : syracuseStep 692945 = 519709) B519709
theorem B463571 : Blo 307833 463571 := bstep (se 1 (by rfl) ⟨347678, by rfl⟩ : syracuseStep 463571 = 695357) B695357
theorem B692963 : Blo 307833 692963 := bstep (se 1 (by rfl) ⟨519722, by rfl⟩ : syracuseStep 692963 = 1039445) B1039445
theorem B463601 : Blo 307833 463601 := bstep (se 2 (by rfl) ⟨173850, by rfl⟩ : syracuseStep 463601 = 347701) B347701
theorem B463619 : Blo 307833 463619 := bstep (se 1 (by rfl) ⟨347714, by rfl⟩ : syracuseStep 463619 = 695429) B695429
theorem B463649 : Blo 307833 463649 := bstep (se 2 (by rfl) ⟨173868, by rfl⟩ : syracuseStep 463649 = 347737) B347737
theorem B463667 : Blo 307833 463667 := bstep (se 1 (by rfl) ⟨347750, by rfl⟩ : syracuseStep 463667 = 695501) B695501
theorem B463697 : Blo 307833 463697 := bstep (se 2 (by rfl) ⟨173886, by rfl⟩ : syracuseStep 463697 = 347773) B347773
theorem B463715 : Blo 307833 463715 := bstep (se 1 (by rfl) ⟨347786, by rfl⟩ : syracuseStep 463715 = 695573) B695573
theorem B463745 : Blo 307833 463745 := bstep (se 2 (by rfl) ⟨173904, by rfl⟩ : syracuseStep 463745 = 347809) B347809
theorem B463763 : Blo 307833 463763 := bstep (se 1 (by rfl) ⟨347822, by rfl⟩ : syracuseStep 463763 = 695645) B695645
theorem B463793 : Blo 307833 463793 := bstep (se 2 (by rfl) ⟨173922, by rfl⟩ : syracuseStep 463793 = 347845) B347845
theorem B463811 : Blo 307833 463811 := bstep (se 1 (by rfl) ⟨347858, by rfl⟩ : syracuseStep 463811 = 695717) B695717
theorem B1414093 : Blo 307833 1414093 := bstep (se 3 (by rfl) ⟨265142, by rfl⟩ : syracuseStep 1414093 = 530285) B530285
theorem B463841 : Blo 307833 463841 := bstep (se 2 (by rfl) ⟨173940, by rfl⟩ : syracuseStep 463841 = 347881) B347881
theorem B693233 : Blo 307833 693233 := bstep (se 2 (by rfl) ⟨259962, by rfl⟩ : syracuseStep 693233 = 519925) B519925
theorem B463859 : Blo 307833 463859 := bstep (se 1 (by rfl) ⟨347894, by rfl⟩ : syracuseStep 463859 = 695789) B695789
theorem B693251 : Blo 307833 693251 := bstep (se 1 (by rfl) ⟨519938, by rfl⟩ : syracuseStep 693251 = 1039877) B1039877
theorem B463889 : Blo 307833 463889 := bstep (se 2 (by rfl) ⟨173958, by rfl⟩ : syracuseStep 463889 = 347917) B347917
theorem B463907 : Blo 307833 463907 := bstep (se 1 (by rfl) ⟨347930, by rfl⟩ : syracuseStep 463907 = 695861) B695861
theorem B463937 : Blo 307833 463937 := bstep (se 2 (by rfl) ⟨173976, by rfl⟩ : syracuseStep 463937 = 347953) B347953
theorem B463955 : Blo 307833 463955 := bstep (se 1 (by rfl) ⟨347966, by rfl⟩ : syracuseStep 463955 = 695933) B695933
theorem B463985 : Blo 307833 463985 := bstep (se 2 (by rfl) ⟨173994, by rfl⟩ : syracuseStep 463985 = 347989) B347989
theorem B660611 : Blo 307833 660611 := bstep (se 1 (by rfl) ⟨495458, by rfl⟩ : syracuseStep 660611 = 990917) B990917
theorem B464003 : Blo 307833 464003 := bstep (se 1 (by rfl) ⟨348002, by rfl⟩ : syracuseStep 464003 = 696005) B696005
theorem B464033 : Blo 307833 464033 := bstep (se 2 (by rfl) ⟨174012, by rfl⟩ : syracuseStep 464033 = 348025) B348025
theorem B1119395 : Blo 307833 1119395 := bstep (se 1 (by rfl) ⟨839546, by rfl⟩ : syracuseStep 1119395 = 1679093) B1679093
theorem B464051 : Blo 307833 464051 := bstep (se 1 (by rfl) ⟨348038, by rfl⟩ : syracuseStep 464051 = 696077) B696077
theorem B464081 : Blo 307833 464081 := bstep (se 2 (by rfl) ⟨174030, by rfl⟩ : syracuseStep 464081 = 348061) B348061
theorem B464099 : Blo 307833 464099 := bstep (se 1 (by rfl) ⟨348074, by rfl⟩ : syracuseStep 464099 = 696149) B696149
theorem B2528497 : Blo 307833 2528497 := bstep (se 2 (by rfl) ⟨948186, by rfl⟩ : syracuseStep 2528497 = 1896373) B1896373
theorem B464129 : Blo 307833 464129 := bstep (se 2 (by rfl) ⟨174048, by rfl⟩ : syracuseStep 464129 = 348097) B348097
theorem B693521 : Blo 307833 693521 := bstep (se 2 (by rfl) ⟨260070, by rfl⟩ : syracuseStep 693521 = 520141) B520141
theorem B464147 : Blo 307833 464147 := bstep (se 1 (by rfl) ⟨348110, by rfl⟩ : syracuseStep 464147 = 696221) B696221
theorem B693539 : Blo 307833 693539 := bstep (se 1 (by rfl) ⟨520154, by rfl⟩ : syracuseStep 693539 = 1040309) B1040309
theorem B464177 : Blo 307833 464177 := bstep (se 2 (by rfl) ⟨174066, by rfl⟩ : syracuseStep 464177 = 348133) B348133
theorem B496945 : Blo 307833 496945 := bstep (se 2 (by rfl) ⟨186354, by rfl⟩ : syracuseStep 496945 = 372709) B372709
theorem B988483 : Blo 307833 988483 := bstep (se 1 (by rfl) ⟨741362, by rfl⟩ : syracuseStep 988483 = 1482725) B1482725
theorem B464195 : Blo 307833 464195 := bstep (se 1 (by rfl) ⟨348146, by rfl⟩ : syracuseStep 464195 = 696293) B696293
theorem B1611085 : Blo 307833 1611085 := bstep (se 3 (by rfl) ⟨302078, by rfl⟩ : syracuseStep 1611085 = 604157) B604157
theorem B464225 : Blo 307833 464225 := bstep (se 2 (by rfl) ⟨174084, by rfl⟩ : syracuseStep 464225 = 348169) B348169
theorem B464243 : Blo 307833 464243 := bstep (se 1 (by rfl) ⟨348182, by rfl⟩ : syracuseStep 464243 = 696365) B696365
theorem B464273 : Blo 307833 464273 := bstep (se 2 (by rfl) ⟨174102, by rfl⟩ : syracuseStep 464273 = 348205) B348205
theorem B464291 : Blo 307833 464291 := bstep (se 1 (by rfl) ⟨348218, by rfl⟩ : syracuseStep 464291 = 696437) B696437
theorem B464321 : Blo 307833 464321 := bstep (se 2 (by rfl) ⟨174120, by rfl⟩ : syracuseStep 464321 = 348241) B348241
theorem B464339 : Blo 307833 464339 := bstep (se 1 (by rfl) ⟨348254, by rfl⟩ : syracuseStep 464339 = 696509) B696509
theorem B464369 : Blo 307833 464369 := bstep (se 2 (by rfl) ⟨174138, by rfl⟩ : syracuseStep 464369 = 348277) B348277
theorem B464387 : Blo 307833 464387 := bstep (se 1 (by rfl) ⟨348290, by rfl⟩ : syracuseStep 464387 = 696581) B696581
theorem B464417 : Blo 307833 464417 := bstep (se 2 (by rfl) ⟨174156, by rfl⟩ : syracuseStep 464417 = 348313) B348313
theorem B693809 : Blo 307833 693809 := bstep (se 2 (by rfl) ⟨260178, by rfl⟩ : syracuseStep 693809 = 520357) B520357
theorem B464435 : Blo 307833 464435 := bstep (se 1 (by rfl) ⟨348326, by rfl⟩ : syracuseStep 464435 = 696653) B696653
theorem B693827 : Blo 307833 693827 := bstep (se 1 (by rfl) ⟨520370, by rfl⟩ : syracuseStep 693827 = 1040741) B1040741
theorem B464465 : Blo 307833 464465 := bstep (se 2 (by rfl) ⟨174174, by rfl⟩ : syracuseStep 464465 = 348349) B348349
theorem B464483 : Blo 307833 464483 := bstep (se 1 (by rfl) ⟨348362, by rfl⟩ : syracuseStep 464483 = 696725) B696725
theorem B464513 : Blo 307833 464513 := bstep (se 2 (by rfl) ⟨174192, by rfl⟩ : syracuseStep 464513 = 348385) B348385
theorem B464531 : Blo 307833 464531 := bstep (se 1 (by rfl) ⟨348398, by rfl⟩ : syracuseStep 464531 = 696797) B696797
theorem B464561 : Blo 307833 464561 := bstep (se 2 (by rfl) ⟨174210, by rfl⟩ : syracuseStep 464561 = 348421) B348421
theorem B464579 : Blo 307833 464579 := bstep (se 1 (by rfl) ⟨348434, by rfl⟩ : syracuseStep 464579 = 696869) B696869
theorem B464609 : Blo 307833 464609 := bstep (se 2 (by rfl) ⟨174228, by rfl⟩ : syracuseStep 464609 = 348457) B348457
theorem B464627 : Blo 307833 464627 := bstep (se 1 (by rfl) ⟨348470, by rfl⟩ : syracuseStep 464627 = 696941) B696941
theorem B464657 : Blo 307833 464657 := bstep (se 2 (by rfl) ⟨174246, by rfl⟩ : syracuseStep 464657 = 348493) B348493
theorem B530209 : Blo 307833 530209 := bstep (se 2 (by rfl) ⟨198828, by rfl⟩ : syracuseStep 530209 = 397657) B397657
theorem B464675 : Blo 307833 464675 := bstep (se 1 (by rfl) ⟨348506, by rfl⟩ : syracuseStep 464675 = 697013) B697013
theorem B464705 : Blo 307833 464705 := bstep (se 2 (by rfl) ⟨174264, by rfl⟩ : syracuseStep 464705 = 348529) B348529
theorem B694097 : Blo 307833 694097 := bstep (se 2 (by rfl) ⟨260286, by rfl⟩ : syracuseStep 694097 = 520573) B520573
theorem B464723 : Blo 307833 464723 := bstep (se 1 (by rfl) ⟨348542, by rfl⟩ : syracuseStep 464723 = 697085) B697085
theorem B694115 : Blo 307833 694115 := bstep (se 1 (by rfl) ⟨520586, by rfl⟩ : syracuseStep 694115 = 1041173) B1041173
theorem B464753 : Blo 307833 464753 := bstep (se 2 (by rfl) ⟨174282, by rfl⟩ : syracuseStep 464753 = 348565) B348565
theorem B464771 : Blo 307833 464771 := bstep (se 1 (by rfl) ⟨348578, by rfl⟩ : syracuseStep 464771 = 697157) B697157
theorem B464801 : Blo 307833 464801 := bstep (se 2 (by rfl) ⟨174300, by rfl⟩ : syracuseStep 464801 = 348601) B348601
theorem B464819 : Blo 307833 464819 := bstep (se 1 (by rfl) ⟨348614, by rfl⟩ : syracuseStep 464819 = 697229) B697229
theorem B464849 : Blo 307833 464849 := bstep (se 2 (by rfl) ⟨174318, by rfl⟩ : syracuseStep 464849 = 348637) B348637
theorem B530401 : Blo 307833 530401 := bstep (se 2 (by rfl) ⟨198900, by rfl⟩ : syracuseStep 530401 = 397801) B397801
theorem B464867 : Blo 307833 464867 := bstep (se 1 (by rfl) ⟨348650, by rfl⟩ : syracuseStep 464867 = 697301) B697301
theorem B464897 : Blo 307833 464897 := bstep (se 2 (by rfl) ⟨174336, by rfl⟩ : syracuseStep 464897 = 348673) B348673
theorem B464915 : Blo 307833 464915 := bstep (se 1 (by rfl) ⟨348686, by rfl⟩ : syracuseStep 464915 = 697373) B697373
theorem B1677347 : Blo 307833 1677347 := bstep (se 1 (by rfl) ⟨1258010, by rfl⟩ : syracuseStep 1677347 = 2516021) B2516021
theorem B464945 : Blo 307833 464945 := bstep (se 2 (by rfl) ⟨174354, by rfl⟩ : syracuseStep 464945 = 348709) B348709
theorem B464963 : Blo 307833 464963 := bstep (se 1 (by rfl) ⟨348722, by rfl⟩ : syracuseStep 464963 = 697445) B697445
theorem B464993 : Blo 307833 464993 := bstep (se 2 (by rfl) ⟨174372, by rfl⟩ : syracuseStep 464993 = 348745) B348745
theorem B694385 : Blo 307833 694385 := bstep (se 2 (by rfl) ⟨260394, by rfl⟩ : syracuseStep 694385 = 520789) B520789
theorem B465011 : Blo 307833 465011 := bstep (se 1 (by rfl) ⟨348758, by rfl⟩ : syracuseStep 465011 = 697517) B697517
theorem B694403 : Blo 307833 694403 := bstep (se 1 (by rfl) ⟨520802, by rfl⟩ : syracuseStep 694403 = 1041605) B1041605
theorem B2398349 : Blo 307833 2398349 := bstep (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) B899381
theorem B465041 : Blo 307833 465041 := bstep (se 2 (by rfl) ⟨174390, by rfl⟩ : syracuseStep 465041 = 348781) B348781
theorem B465059 : Blo 307833 465059 := bstep (se 1 (by rfl) ⟨348794, by rfl⟩ : syracuseStep 465059 = 697589) B697589
theorem B465089 : Blo 307833 465089 := bstep (se 2 (by rfl) ⟨174408, by rfl⟩ : syracuseStep 465089 = 348817) B348817
theorem B465107 : Blo 307833 465107 := bstep (se 1 (by rfl) ⟨348830, by rfl⟩ : syracuseStep 465107 = 697661) B697661
theorem B465137 : Blo 307833 465137 := bstep (se 2 (by rfl) ⟨174426, by rfl⟩ : syracuseStep 465137 = 348853) B348853
theorem B465155 : Blo 307833 465155 := bstep (se 1 (by rfl) ⟨348866, by rfl⟩ : syracuseStep 465155 = 697733) B697733
theorem B465185 : Blo 307833 465185 := bstep (se 2 (by rfl) ⟨174444, by rfl⟩ : syracuseStep 465185 = 348889) B348889
theorem B465203 : Blo 307833 465203 := bstep (se 1 (by rfl) ⟨348902, by rfl⟩ : syracuseStep 465203 = 697805) B697805
theorem B465233 : Blo 307833 465233 := bstep (se 2 (by rfl) ⟨174462, by rfl⟩ : syracuseStep 465233 = 348925) B348925
theorem B465251 : Blo 307833 465251 := bstep (se 1 (by rfl) ⟨348938, by rfl⟩ : syracuseStep 465251 = 697877) B697877
theorem B465281 : Blo 307833 465281 := bstep (se 2 (by rfl) ⟨174480, by rfl⟩ : syracuseStep 465281 = 348961) B348961
theorem B694673 : Blo 307833 694673 := bstep (se 2 (by rfl) ⟨260502, by rfl⟩ : syracuseStep 694673 = 521005) B521005
theorem B465299 : Blo 307833 465299 := bstep (se 1 (by rfl) ⟨348974, by rfl⟩ : syracuseStep 465299 = 697949) B697949
theorem B694691 : Blo 307833 694691 := bstep (se 1 (by rfl) ⟨521018, by rfl⟩ : syracuseStep 694691 = 1042037) B1042037
theorem B465329 : Blo 307833 465329 := bstep (se 2 (by rfl) ⟨174498, by rfl⟩ : syracuseStep 465329 = 348997) B348997
theorem B465347 : Blo 307833 465347 := bstep (se 1 (by rfl) ⟨349010, by rfl⟩ : syracuseStep 465347 = 698021) B698021
theorem B3578309 : Blo 307833 3578309 := bstep (se 4 (by rfl) ⟨335466, by rfl⟩ : syracuseStep 3578309 = 670933) B670933
theorem B465377 : Blo 307833 465377 := bstep (se 2 (by rfl) ⟨174516, by rfl⟩ : syracuseStep 465377 = 349033) B349033
theorem B465395 : Blo 307833 465395 := bstep (se 1 (by rfl) ⟨349046, by rfl⟩ : syracuseStep 465395 = 698093) B698093
theorem B465425 : Blo 307833 465425 := bstep (se 2 (by rfl) ⟨174534, by rfl⟩ : syracuseStep 465425 = 349069) B349069
theorem B465443 : Blo 307833 465443 := bstep (se 1 (by rfl) ⟨349082, by rfl⟩ : syracuseStep 465443 = 698165) B698165
theorem B465473 : Blo 307833 465473 := bstep (se 2 (by rfl) ⟨174552, by rfl⟩ : syracuseStep 465473 = 349105) B349105
theorem B629329 : Blo 307833 629329 := bstep (se 2 (by rfl) ⟨235998, by rfl⟩ : syracuseStep 629329 = 471997) B471997
theorem B465491 : Blo 307833 465491 := bstep (se 1 (by rfl) ⟨349118, by rfl⟩ : syracuseStep 465491 = 698237) B698237
theorem B465521 : Blo 307833 465521 := bstep (se 2 (by rfl) ⟨174570, by rfl⟩ : syracuseStep 465521 = 349141) B349141
theorem B465539 : Blo 307833 465539 := bstep (se 1 (by rfl) ⟨349154, by rfl⟩ : syracuseStep 465539 = 698309) B698309
theorem B465569 : Blo 307833 465569 := bstep (se 2 (by rfl) ⟨174588, by rfl⟩ : syracuseStep 465569 = 349177) B349177
theorem B694961 : Blo 307833 694961 := bstep (se 2 (by rfl) ⟨260610, by rfl⟩ : syracuseStep 694961 = 521221) B521221
theorem B465587 : Blo 307833 465587 := bstep (se 1 (by rfl) ⟨349190, by rfl⟩ : syracuseStep 465587 = 698381) B698381
theorem B694979 : Blo 307833 694979 := bstep (se 1 (by rfl) ⟨521234, by rfl⟩ : syracuseStep 694979 = 1042469) B1042469
theorem B465617 : Blo 307833 465617 := bstep (se 2 (by rfl) ⟨174606, by rfl⟩ : syracuseStep 465617 = 349213) B349213
theorem B465635 : Blo 307833 465635 := bstep (se 1 (by rfl) ⟨349226, by rfl⟩ : syracuseStep 465635 = 698453) B698453
theorem B465665 : Blo 307833 465665 := bstep (se 2 (by rfl) ⟨174624, by rfl⟩ : syracuseStep 465665 = 349249) B349249
theorem B465683 : Blo 307833 465683 := bstep (se 1 (by rfl) ⟨349262, by rfl⟩ : syracuseStep 465683 = 698525) B698525
theorem B465713 : Blo 307833 465713 := bstep (se 2 (by rfl) ⟨174642, by rfl⟩ : syracuseStep 465713 = 349285) B349285
theorem B465731 : Blo 307833 465731 := bstep (se 1 (by rfl) ⟨349298, by rfl⟩ : syracuseStep 465731 = 698597) B698597
theorem B1973069 : Blo 307833 1973069 := bstep (se 3 (by rfl) ⟨369950, by rfl⟩ : syracuseStep 1973069 = 739901) B739901
theorem B465761 : Blo 307833 465761 := bstep (se 2 (by rfl) ⟨174660, by rfl⟩ : syracuseStep 465761 = 349321) B349321
theorem B2988899 : Blo 307833 2988899 := bstep (se 1 (by rfl) ⟨2241674, by rfl⟩ : syracuseStep 2988899 = 4483349) B4483349
theorem B465779 : Blo 307833 465779 := bstep (se 1 (by rfl) ⟨349334, by rfl⟩ : syracuseStep 465779 = 698669) B698669
theorem B465809 : Blo 307833 465809 := bstep (se 2 (by rfl) ⟨174678, by rfl⟩ : syracuseStep 465809 = 349357) B349357
theorem B465827 : Blo 307833 465827 := bstep (se 1 (by rfl) ⟨349370, by rfl⟩ : syracuseStep 465827 = 698741) B698741
theorem B498611 : Blo 307833 498611 := bstep (se 1 (by rfl) ⟨373958, by rfl⟩ : syracuseStep 498611 = 747917) B747917
theorem B465857 : Blo 307833 465857 := bstep (se 2 (by rfl) ⟨174696, by rfl⟩ : syracuseStep 465857 = 349393) B349393
theorem B1055683 : Blo 307833 1055683 := bstep (se 1 (by rfl) ⟨791762, by rfl⟩ : syracuseStep 1055683 = 1583525) B1583525
theorem B695249 : Blo 307833 695249 := bstep (se 2 (by rfl) ⟨260718, by rfl⟩ : syracuseStep 695249 = 521437) B521437
theorem B465875 : Blo 307833 465875 := bstep (se 1 (by rfl) ⟨349406, by rfl⟩ : syracuseStep 465875 = 698813) B698813
theorem B695267 : Blo 307833 695267 := bstep (se 1 (by rfl) ⟨521450, by rfl⟩ : syracuseStep 695267 = 1042901) B1042901
theorem B465905 : Blo 307833 465905 := bstep (se 2 (by rfl) ⟨174714, by rfl⟩ : syracuseStep 465905 = 349429) B349429
theorem B465923 : Blo 307833 465923 := bstep (se 1 (by rfl) ⟨349442, by rfl⟩ : syracuseStep 465923 = 698885) B698885
theorem B465953 : Blo 307833 465953 := bstep (se 2 (by rfl) ⟨174732, by rfl⟩ : syracuseStep 465953 = 349465) B349465
theorem B465971 : Blo 307833 465971 := bstep (se 1 (by rfl) ⟨349478, by rfl⟩ : syracuseStep 465971 = 698957) B698957
theorem B498739 : Blo 307833 498739 := bstep (se 1 (by rfl) ⟨374054, by rfl⟩ : syracuseStep 498739 = 748109) B748109
theorem B466001 : Blo 307833 466001 := bstep (se 2 (by rfl) ⟨174750, by rfl⟩ : syracuseStep 466001 = 349501) B349501
theorem B662627 : Blo 307833 662627 := bstep (se 1 (by rfl) ⟨496970, by rfl⟩ : syracuseStep 662627 = 993941) B993941
theorem B466019 : Blo 307833 466019 := bstep (se 1 (by rfl) ⟨349514, by rfl⟩ : syracuseStep 466019 = 699029) B699029
theorem B498803 : Blo 307833 498803 := bstep (se 1 (by rfl) ⟨374102, by rfl⟩ : syracuseStep 498803 = 748205) B748205
theorem B466049 : Blo 307833 466049 := bstep (se 2 (by rfl) ⟨174768, by rfl⟩ : syracuseStep 466049 = 349537) B349537
theorem B466067 : Blo 307833 466067 := bstep (se 1 (by rfl) ⟨349550, by rfl⟩ : syracuseStep 466067 = 699101) B699101
theorem B466097 : Blo 307833 466097 := bstep (se 2 (by rfl) ⟨174786, by rfl⟩ : syracuseStep 466097 = 349573) B349573
theorem B466115 : Blo 307833 466115 := bstep (se 1 (by rfl) ⟨349586, by rfl⟩ : syracuseStep 466115 = 699173) B699173
theorem B466145 : Blo 307833 466145 := bstep (se 2 (by rfl) ⟨174804, by rfl⟩ : syracuseStep 466145 = 349609) B349609
theorem B695537 : Blo 307833 695537 := bstep (se 2 (by rfl) ⟨260826, by rfl⟩ : syracuseStep 695537 = 521653) B521653
theorem B466163 : Blo 307833 466163 := bstep (se 1 (by rfl) ⟨349622, by rfl⟩ : syracuseStep 466163 = 699245) B699245
theorem B695555 : Blo 307833 695555 := bstep (se 1 (by rfl) ⟨521666, by rfl⟩ : syracuseStep 695555 = 1043333) B1043333
theorem B466193 : Blo 307833 466193 := bstep (se 2 (by rfl) ⟨174822, by rfl⟩ : syracuseStep 466193 = 349645) B349645
theorem B466211 : Blo 307833 466211 := bstep (se 1 (by rfl) ⟨349658, by rfl⟩ : syracuseStep 466211 = 699317) B699317
theorem B466241 : Blo 307833 466241 := bstep (se 2 (by rfl) ⟨174840, by rfl⟩ : syracuseStep 466241 = 349681) B349681
theorem B466259 : Blo 307833 466259 := bstep (se 1 (by rfl) ⟨349694, by rfl⟩ : syracuseStep 466259 = 699389) B699389
theorem B1023331 : Blo 307833 1023331 := bstep (se 1 (by rfl) ⟨767498, by rfl⟩ : syracuseStep 1023331 = 1534997) B1534997
theorem B2366819 : Blo 307833 2366819 := bstep (se 1 (by rfl) ⟨1775114, by rfl⟩ : syracuseStep 2366819 = 3550229) B3550229
theorem B466289 : Blo 307833 466289 := bstep (se 2 (by rfl) ⟨174858, by rfl⟩ : syracuseStep 466289 = 349717) B349717
theorem B466307 : Blo 307833 466307 := bstep (se 1 (by rfl) ⟨349730, by rfl⟩ : syracuseStep 466307 = 699461) B699461
theorem B466337 : Blo 307833 466337 := bstep (se 2 (by rfl) ⟨174876, by rfl⟩ : syracuseStep 466337 = 349753) B349753
theorem B466355 : Blo 307833 466355 := bstep (se 1 (by rfl) ⟨349766, by rfl⟩ : syracuseStep 466355 = 699533) B699533
theorem B466385 : Blo 307833 466385 := bstep (se 2 (by rfl) ⟨174894, by rfl⟩ : syracuseStep 466385 = 349789) B349789
theorem B466403 : Blo 307833 466403 := bstep (se 1 (by rfl) ⟨349802, by rfl⟩ : syracuseStep 466403 = 699605) B699605
theorem B892397 : Blo 307833 892397 := bstep (se 3 (by rfl) ⟨167324, by rfl⟩ : syracuseStep 892397 = 334649) B334649
theorem B990701 : Blo 307833 990701 := bstep (se 3 (by rfl) ⟨185756, by rfl⟩ : syracuseStep 990701 = 371513) B371513
theorem B466433 : Blo 307833 466433 := bstep (se 2 (by rfl) ⟨174912, by rfl⟩ : syracuseStep 466433 = 349825) B349825
theorem B695825 : Blo 307833 695825 := bstep (se 2 (by rfl) ⟨260934, by rfl⟩ : syracuseStep 695825 = 521869) B521869
theorem B466451 : Blo 307833 466451 := bstep (se 1 (by rfl) ⟨349838, by rfl⟩ : syracuseStep 466451 = 699677) B699677
theorem B695843 : Blo 307833 695843 := bstep (se 1 (by rfl) ⟨521882, by rfl⟩ : syracuseStep 695843 = 1043765) B1043765
theorem B466481 : Blo 307833 466481 := bstep (se 2 (by rfl) ⟨174930, by rfl⟩ : syracuseStep 466481 = 349861) B349861
theorem B466499 : Blo 307833 466499 := bstep (se 1 (by rfl) ⟨349874, by rfl⟩ : syracuseStep 466499 = 699749) B699749
theorem B466529 : Blo 307833 466529 := bstep (se 2 (by rfl) ⟨174948, by rfl⟩ : syracuseStep 466529 = 349897) B349897
theorem B499297 : Blo 307833 499297 := bstep (se 2 (by rfl) ⟨187236, by rfl⟩ : syracuseStep 499297 = 374473) B374473
theorem B958061 : Blo 307833 958061 := bstep (se 3 (by rfl) ⟨179636, by rfl⟩ : syracuseStep 958061 = 359273) B359273
theorem B466547 : Blo 307833 466547 := bstep (se 1 (by rfl) ⟨349910, by rfl⟩ : syracuseStep 466547 = 699821) B699821
theorem B466577 : Blo 307833 466577 := bstep (se 2 (by rfl) ⟨174966, by rfl⟩ : syracuseStep 466577 = 349933) B349933
theorem B466595 : Blo 307833 466595 := bstep (se 1 (by rfl) ⟨349946, by rfl⟩ : syracuseStep 466595 = 699893) B699893
theorem B466625 : Blo 307833 466625 := bstep (se 2 (by rfl) ⟨174984, by rfl⟩ : syracuseStep 466625 = 349969) B349969
theorem B466643 : Blo 307833 466643 := bstep (se 1 (by rfl) ⟨349982, by rfl⟩ : syracuseStep 466643 = 699965) B699965
theorem B466673 : Blo 307833 466673 := bstep (se 2 (by rfl) ⟨175002, by rfl⟩ : syracuseStep 466673 = 350005) B350005
theorem B466691 : Blo 307833 466691 := bstep (se 1 (by rfl) ⟨350018, by rfl⟩ : syracuseStep 466691 = 700037) B700037
theorem B466721 : Blo 307833 466721 := bstep (se 2 (by rfl) ⟨175020, by rfl⟩ : syracuseStep 466721 = 350041) B350041
theorem B696113 : Blo 307833 696113 := bstep (se 2 (by rfl) ⟨261042, by rfl⟩ : syracuseStep 696113 = 522085) B522085
theorem B466739 : Blo 307833 466739 := bstep (se 1 (by rfl) ⟨350054, by rfl⟩ : syracuseStep 466739 = 700109) B700109
theorem B696131 : Blo 307833 696131 := bstep (se 1 (by rfl) ⟨522098, by rfl⟩ : syracuseStep 696131 = 1044197) B1044197
theorem B466769 : Blo 307833 466769 := bstep (se 2 (by rfl) ⟨175038, by rfl⟩ : syracuseStep 466769 = 350077) B350077
theorem B466787 : Blo 307833 466787 := bstep (se 1 (by rfl) ⟨350090, by rfl⟩ : syracuseStep 466787 = 700181) B700181
theorem B3383153 : Blo 307833 3383153 := bstep (se 2 (by rfl) ⟨1268682, by rfl⟩ : syracuseStep 3383153 = 2537365) B2537365
theorem B466817 : Blo 307833 466817 := bstep (se 2 (by rfl) ⟨175056, by rfl⟩ : syracuseStep 466817 = 350113) B350113
theorem B991121 : Blo 307833 991121 := bstep (se 2 (by rfl) ⟨371670, by rfl⟩ : syracuseStep 991121 = 743341) B743341
theorem B466835 : Blo 307833 466835 := bstep (se 1 (by rfl) ⟨350126, by rfl⟩ : syracuseStep 466835 = 700253) B700253
theorem B466865 : Blo 307833 466865 := bstep (se 2 (by rfl) ⟨175074, by rfl⟩ : syracuseStep 466865 = 350149) B350149
theorem B466883 : Blo 307833 466883 := bstep (se 1 (by rfl) ⟨350162, by rfl⟩ : syracuseStep 466883 = 700325) B700325
theorem B1679309 : Blo 307833 1679309 := bstep (se 3 (by rfl) ⟨314870, by rfl⟩ : syracuseStep 1679309 = 629741) B629741
theorem B466913 : Blo 307833 466913 := bstep (se 2 (by rfl) ⟨175092, by rfl⟩ : syracuseStep 466913 = 350185) B350185
theorem B466931 : Blo 307833 466931 := bstep (se 1 (by rfl) ⟨350198, by rfl⟩ : syracuseStep 466931 = 700397) B700397
theorem B466961 : Blo 307833 466961 := bstep (se 2 (by rfl) ⟨175110, by rfl⟩ : syracuseStep 466961 = 350221) B350221
theorem B466979 : Blo 307833 466979 := bstep (se 1 (by rfl) ⟨350234, by rfl⟩ : syracuseStep 466979 = 700469) B700469
theorem B467009 : Blo 307833 467009 := bstep (se 2 (by rfl) ⟨175128, by rfl⟩ : syracuseStep 467009 = 350257) B350257
theorem B2662469 : Blo 307833 2662469 := bstep (se 4 (by rfl) ⟨249606, by rfl⟩ : syracuseStep 2662469 = 499213) B499213
theorem B696401 : Blo 307833 696401 := bstep (se 2 (by rfl) ⟨261150, by rfl⟩ : syracuseStep 696401 = 522301) B522301
theorem B467027 : Blo 307833 467027 := bstep (se 1 (by rfl) ⟨350270, by rfl⟩ : syracuseStep 467027 = 700541) B700541
theorem B696419 : Blo 307833 696419 := bstep (se 1 (by rfl) ⟨522314, by rfl⟩ : syracuseStep 696419 = 1044629) B1044629
theorem B467057 : Blo 307833 467057 := bstep (se 2 (by rfl) ⟨175146, by rfl⟩ : syracuseStep 467057 = 350293) B350293
theorem B467075 : Blo 307833 467075 := bstep (se 1 (by rfl) ⟨350306, by rfl⟩ : syracuseStep 467075 = 700613) B700613
theorem B467105 : Blo 307833 467105 := bstep (se 2 (by rfl) ⟨175164, by rfl⟩ : syracuseStep 467105 = 350329) B350329
theorem B467123 : Blo 307833 467123 := bstep (se 1 (by rfl) ⟨350342, by rfl⟩ : syracuseStep 467123 = 700685) B700685
theorem B467153 : Blo 307833 467153 := bstep (se 2 (by rfl) ⟨175182, by rfl⟩ : syracuseStep 467153 = 350365) B350365
theorem B467171 : Blo 307833 467171 := bstep (se 1 (by rfl) ⟨350378, by rfl⟩ : syracuseStep 467171 = 700757) B700757
theorem B467201 : Blo 307833 467201 := bstep (se 2 (by rfl) ⟨175200, by rfl⟩ : syracuseStep 467201 = 350401) B350401
theorem B467219 : Blo 307833 467219 := bstep (se 1 (by rfl) ⟨350414, by rfl⟩ : syracuseStep 467219 = 700829) B700829
theorem B467249 : Blo 307833 467249 := bstep (se 2 (by rfl) ⟨175218, by rfl⟩ : syracuseStep 467249 = 350437) B350437
theorem B467267 : Blo 307833 467267 := bstep (se 1 (by rfl) ⟨350450, by rfl⟩ : syracuseStep 467267 = 700901) B700901
theorem B467297 : Blo 307833 467297 := bstep (se 2 (by rfl) ⟨175236, by rfl⟩ : syracuseStep 467297 = 350473) B350473
theorem B696689 : Blo 307833 696689 := bstep (se 2 (by rfl) ⟨261258, by rfl⟩ : syracuseStep 696689 = 522517) B522517
theorem B467315 : Blo 307833 467315 := bstep (se 1 (by rfl) ⟨350486, by rfl⟩ : syracuseStep 467315 = 700973) B700973
theorem B696707 : Blo 307833 696707 := bstep (se 1 (by rfl) ⟨522530, by rfl⟩ : syracuseStep 696707 = 1045061) B1045061
theorem B467345 : Blo 307833 467345 := bstep (se 2 (by rfl) ⟨175254, by rfl⟩ : syracuseStep 467345 = 350509) B350509
theorem B467363 : Blo 307833 467363 := bstep (se 1 (by rfl) ⟨350522, by rfl⟩ : syracuseStep 467363 = 701045) B701045
theorem B467393 : Blo 307833 467393 := bstep (se 2 (by rfl) ⟨175272, by rfl⟩ : syracuseStep 467393 = 350545) B350545
theorem B565699 : Blo 307833 565699 := bstep (se 1 (by rfl) ⟨424274, by rfl⟩ : syracuseStep 565699 = 848549) B848549
theorem B631235 : Blo 307833 631235 := bstep (se 1 (by rfl) ⟨473426, by rfl⟩ : syracuseStep 631235 = 946853) B946853
theorem B467411 : Blo 307833 467411 := bstep (se 1 (by rfl) ⟨350558, by rfl⟩ : syracuseStep 467411 = 701117) B701117
theorem B467441 : Blo 307833 467441 := bstep (se 2 (by rfl) ⟨175290, by rfl⟩ : syracuseStep 467441 = 350581) B350581
theorem B467459 : Blo 307833 467459 := bstep (se 1 (by rfl) ⟨350594, by rfl⟩ : syracuseStep 467459 = 701189) B701189
theorem B467489 : Blo 307833 467489 := bstep (se 2 (by rfl) ⟨175308, by rfl⟩ : syracuseStep 467489 = 350617) B350617
theorem B467507 : Blo 307833 467507 := bstep (se 1 (by rfl) ⟨350630, by rfl⟩ : syracuseStep 467507 = 701261) B701261
theorem B467537 : Blo 307833 467537 := bstep (se 2 (by rfl) ⟨175326, by rfl⟩ : syracuseStep 467537 = 350653) B350653
theorem B1253987 : Blo 307833 1253987 := bstep (se 1 (by rfl) ⟨940490, by rfl⟩ : syracuseStep 1253987 = 1880981) B1880981
theorem B467555 : Blo 307833 467555 := bstep (se 1 (by rfl) ⟨350666, by rfl⟩ : syracuseStep 467555 = 701333) B701333
theorem B1254001 : Blo 307833 1254001 := bstep (se 2 (by rfl) ⟨470250, by rfl⟩ : syracuseStep 1254001 = 940501) B940501
theorem B467585 : Blo 307833 467585 := bstep (se 2 (by rfl) ⟨175344, by rfl⟩ : syracuseStep 467585 = 350689) B350689
theorem B696977 : Blo 307833 696977 := bstep (se 2 (by rfl) ⟨261366, by rfl⟩ : syracuseStep 696977 = 522733) B522733
theorem B467603 : Blo 307833 467603 := bstep (se 1 (by rfl) ⟨350702, by rfl⟩ : syracuseStep 467603 = 701405) B701405
theorem B696995 : Blo 307833 696995 := bstep (se 1 (by rfl) ⟨522746, by rfl⟩ : syracuseStep 696995 = 1045493) B1045493
theorem B467633 : Blo 307833 467633 := bstep (se 2 (by rfl) ⟨175362, by rfl⟩ : syracuseStep 467633 = 350725) B350725
theorem B467651 : Blo 307833 467651 := bstep (se 1 (by rfl) ⟨350738, by rfl⟩ : syracuseStep 467651 = 701477) B701477
theorem B467681 : Blo 307833 467681 := bstep (se 2 (by rfl) ⟨175380, by rfl⟩ : syracuseStep 467681 = 350761) B350761
theorem B1319651 : Blo 307833 1319651 := bstep (se 1 (by rfl) ⟨989738, by rfl⟩ : syracuseStep 1319651 = 1979477) B1979477
theorem B467699 : Blo 307833 467699 := bstep (se 1 (by rfl) ⟨350774, by rfl⟩ : syracuseStep 467699 = 701549) B701549
theorem B1123085 : Blo 307833 1123085 := bstep (se 3 (by rfl) ⟨210578, by rfl⟩ : syracuseStep 1123085 = 421157) B421157
theorem B467729 : Blo 307833 467729 := bstep (se 2 (by rfl) ⟨175398, by rfl⟩ : syracuseStep 467729 = 350797) B350797
theorem B467747 : Blo 307833 467747 := bstep (se 1 (by rfl) ⟨350810, by rfl⟩ : syracuseStep 467747 = 701621) B701621
theorem B697265 : Blo 307833 697265 := bstep (se 2 (by rfl) ⟨261474, by rfl⟩ : syracuseStep 697265 = 522949) B522949
theorem B697283 : Blo 307833 697283 := bstep (se 1 (by rfl) ⟨522962, by rfl⟩ : syracuseStep 697283 = 1045925) B1045925
theorem B664643 : Blo 307833 664643 := bstep (se 1 (by rfl) ⟨498482, by rfl⟩ : syracuseStep 664643 = 996965) B996965
theorem B697553 : Blo 307833 697553 := bstep (se 2 (by rfl) ⟨261582, by rfl⟩ : syracuseStep 697553 = 523165) B523165
theorem B697571 : Blo 307833 697571 := bstep (se 1 (by rfl) ⟨523178, by rfl⟩ : syracuseStep 697571 = 1046357) B1046357
theorem B501233 : Blo 307833 501233 := bstep (se 2 (by rfl) ⟨187962, by rfl⟩ : syracuseStep 501233 = 375925) B375925
theorem B697841 : Blo 307833 697841 := bstep (se 2 (by rfl) ⟨261690, by rfl⟩ : syracuseStep 697841 = 523381) B523381
theorem B697859 : Blo 307833 697859 := bstep (se 1 (by rfl) ⟨523394, by rfl⟩ : syracuseStep 697859 = 1046789) B1046789
theorem B1680995 : Blo 307833 1680995 := bstep (se 1 (by rfl) ⟨1260746, by rfl⟩ : syracuseStep 1680995 = 2521493) B2521493
theorem B3548771 : Blo 307833 3548771 := bstep (se 1 (by rfl) ⟨2661578, by rfl⟩ : syracuseStep 3548771 = 5323157) B5323157
theorem B3352261 : Blo 307833 3352261 := bstep (se 4 (by rfl) ⟨314274, by rfl⟩ : syracuseStep 3352261 = 628549) B628549
theorem B698129 : Blo 307833 698129 := bstep (se 2 (by rfl) ⟨261798, by rfl⟩ : syracuseStep 698129 = 523597) B523597
theorem B698147 : Blo 307833 698147 := bstep (se 1 (by rfl) ⟨523610, by rfl⟩ : syracuseStep 698147 = 1047221) B1047221
theorem B468785 : Blo 307833 468785 := bstep (se 2 (by rfl) ⟨175794, by rfl⟩ : syracuseStep 468785 = 351589) B351589
theorem B894797 : Blo 307833 894797 := bstep (se 3 (by rfl) ⟨167774, by rfl⟩ : syracuseStep 894797 = 335549) B335549
theorem B1058669 : Blo 307833 1058669 := bstep (se 3 (by rfl) ⟨198500, by rfl⟩ : syracuseStep 1058669 = 397001) B397001
theorem B2959217 : Blo 307833 2959217 := bstep (se 2 (by rfl) ⟨1109706, by rfl⟩ : syracuseStep 2959217 = 2219413) B2219413
theorem B1255331 : Blo 307833 1255331 := bstep (se 1 (by rfl) ⟨941498, by rfl⟩ : syracuseStep 1255331 = 1882997) B1882997
theorem B698417 : Blo 307833 698417 := bstep (se 2 (by rfl) ⟨261906, by rfl⟩ : syracuseStep 698417 = 523813) B523813
theorem B698435 : Blo 307833 698435 := bstep (se 1 (by rfl) ⟨523826, by rfl⟩ : syracuseStep 698435 = 1047653) B1047653
theorem B5056739 : Blo 307833 5056739 := bstep (se 1 (by rfl) ⟨3792554, by rfl⟩ : syracuseStep 5056739 = 7585109) B7585109
theorem B567569 : Blo 307833 567569 := bstep (se 2 (by rfl) ⟨212838, by rfl⟩ : syracuseStep 567569 = 425677) B425677
theorem B665891 : Blo 307833 665891 := bstep (se 1 (by rfl) ⟨499418, by rfl⟩ : syracuseStep 665891 = 998837) B998837
theorem B698705 : Blo 307833 698705 := bstep (se 2 (by rfl) ⟨262014, by rfl⟩ : syracuseStep 698705 = 524029) B524029
theorem B371027 : Blo 307833 371027 := bstep (se 1 (by rfl) ⟨278270, by rfl⟩ : syracuseStep 371027 = 556541) B556541
theorem B698723 : Blo 307833 698723 := bstep (se 1 (by rfl) ⟨524042, by rfl⟩ : syracuseStep 698723 = 1048085) B1048085
theorem B1321393 : Blo 307833 1321393 := bstep (se 2 (by rfl) ⟨495522, by rfl⟩ : syracuseStep 1321393 = 991045) B991045
theorem B698993 : Blo 307833 698993 := bstep (se 2 (by rfl) ⟨262122, by rfl⟩ : syracuseStep 698993 = 524245) B524245
theorem B6728305 : Blo 307833 6728305 := bstep (se 2 (by rfl) ⟨2523114, by rfl⟩ : syracuseStep 6728305 = 5046229) B5046229
theorem B699011 : Blo 307833 699011 := bstep (se 1 (by rfl) ⟨524258, by rfl⟩ : syracuseStep 699011 = 1048517) B1048517
theorem B371363 : Blo 307833 371363 := bstep (se 1 (by rfl) ⟨278522, by rfl⟩ : syracuseStep 371363 = 557045) B557045
theorem B633617 : Blo 307833 633617 := bstep (se 2 (by rfl) ⟨237606, by rfl⟩ : syracuseStep 633617 = 475213) B475213
theorem B6761357 : Blo 307833 6761357 := bstep (se 3 (by rfl) ⟨1267754, by rfl⟩ : syracuseStep 6761357 = 2535509) B2535509
theorem B699281 : Blo 307833 699281 := bstep (se 2 (by rfl) ⟨262230, by rfl⟩ : syracuseStep 699281 = 524461) B524461
theorem B699299 : Blo 307833 699299 := bstep (se 1 (by rfl) ⟨524474, by rfl⟩ : syracuseStep 699299 = 1048949) B1048949
theorem B1584305 : Blo 307833 1584305 := bstep (se 2 (by rfl) ⟨594114, by rfl⟩ : syracuseStep 1584305 = 1188229) B1188229
theorem B699569 : Blo 307833 699569 := bstep (se 2 (by rfl) ⟨262338, by rfl⟩ : syracuseStep 699569 = 524677) B524677
theorem B699587 : Blo 307833 699587 := bstep (se 1 (by rfl) ⟨524690, by rfl⟩ : syracuseStep 699587 = 1049381) B1049381
theorem B994531 : Blo 307833 994531 := bstep (se 1 (by rfl) ⟨745898, by rfl⟩ : syracuseStep 994531 = 1491797) B1491797
theorem B6040973 : Blo 307833 6040973 := bstep (se 3 (by rfl) ⟨1132682, by rfl⟩ : syracuseStep 6040973 = 2265365) B2265365
theorem B699857 : Blo 307833 699857 := bstep (se 2 (by rfl) ⟨262446, by rfl⟩ : syracuseStep 699857 = 524893) B524893
theorem B699875 : Blo 307833 699875 := bstep (se 1 (by rfl) ⟨524906, by rfl⟩ : syracuseStep 699875 = 1049813) B1049813
theorem B994801 : Blo 307833 994801 := bstep (se 2 (by rfl) ⟨373050, by rfl⟩ : syracuseStep 994801 = 746101) B746101
theorem B2665997 : Blo 307833 2665997 := bstep (se 3 (by rfl) ⟨499874, by rfl⟩ : syracuseStep 2665997 = 999749) B999749
theorem B4763249 : Blo 307833 4763249 := bstep (se 2 (by rfl) ⟨1786218, by rfl⟩ : syracuseStep 4763249 = 3572437) B3572437
theorem B700145 : Blo 307833 700145 := bstep (se 2 (by rfl) ⟨262554, by rfl⟩ : syracuseStep 700145 = 525109) B525109
theorem B700163 : Blo 307833 700163 := bstep (se 1 (by rfl) ⟨525122, by rfl⟩ : syracuseStep 700163 = 1050245) B1050245
theorem B503777 : Blo 307833 503777 := bstep (se 2 (by rfl) ⟨188916, by rfl⟩ : syracuseStep 503777 = 377833) B377833
theorem B700433 : Blo 307833 700433 := bstep (se 2 (by rfl) ⟨262662, by rfl⟩ : syracuseStep 700433 = 525325) B525325
theorem B536611 : Blo 307833 536611 := bstep (se 1 (by rfl) ⟨402458, by rfl⟩ : syracuseStep 536611 = 804917) B804917
theorem B700451 : Blo 307833 700451 := bstep (se 1 (by rfl) ⟨525338, by rfl⟩ : syracuseStep 700451 = 1050677) B1050677
theorem B2994245 : Blo 307833 2994245 := bstep (se 4 (by rfl) ⟨280710, by rfl⟩ : syracuseStep 2994245 = 561421) B561421
theorem B2961677 : Blo 307833 2961677 := bstep (se 3 (by rfl) ⟨555314, by rfl⟩ : syracuseStep 2961677 = 1110629) B1110629
theorem B700721 : Blo 307833 700721 := bstep (se 2 (by rfl) ⟨262770, by rfl⟩ : syracuseStep 700721 = 525541) B525541
theorem B700739 : Blo 307833 700739 := bstep (se 1 (by rfl) ⟨525554, by rfl⟩ : syracuseStep 700739 = 1051109) B1051109
theorem B1323341 : Blo 307833 1323341 := bstep (se 3 (by rfl) ⟨248126, by rfl⟩ : syracuseStep 1323341 = 496253) B496253
theorem B438625 : Blo 307833 438625 := bstep (se 2 (by rfl) ⟨164484, by rfl⟩ : syracuseStep 438625 = 328969) B328969
theorem B1487281 : Blo 307833 1487281 := bstep (se 2 (by rfl) ⟨557730, by rfl⟩ : syracuseStep 1487281 = 1115461) B1115461
theorem B701009 : Blo 307833 701009 := bstep (se 2 (by rfl) ⟨262878, by rfl⟩ : syracuseStep 701009 = 525757) B525757
theorem B1585763 : Blo 307833 1585763 := bstep (se 1 (by rfl) ⟨1189322, by rfl⟩ : syracuseStep 1585763 = 2378645) B2378645
theorem B701027 : Blo 307833 701027 := bstep (se 1 (by rfl) ⟨525770, by rfl⟩ : syracuseStep 701027 = 1051541) B1051541
theorem B307843 : Blo 307833 307843 := bstep (se 1 (by rfl) ⟨230882, by rfl⟩ : syracuseStep 307843 = 461765) B461765
theorem B307859 : Blo 307833 307859 := bstep (se 1 (by rfl) ⟨230894, by rfl⟩ : syracuseStep 307859 = 461789) B461789
theorem B307875 : Blo 307833 307875 := bstep (se 1 (by rfl) ⟨230906, by rfl⟩ : syracuseStep 307875 = 461813) B461813
theorem B438961 : Blo 307833 438961 := bstep (se 2 (by rfl) ⟨164610, by rfl⟩ : syracuseStep 438961 = 329221) B329221
theorem B307891 : Blo 307833 307891 := bstep (se 1 (by rfl) ⟨230918, by rfl⟩ : syracuseStep 307891 = 461837) B461837
theorem B307907 : Blo 307833 307907 := bstep (se 1 (by rfl) ⟨230930, by rfl⟩ : syracuseStep 307907 = 461861) B461861
theorem B307923 : Blo 307833 307923 := bstep (se 1 (by rfl) ⟨230942, by rfl⟩ : syracuseStep 307923 = 461885) B461885
theorem B307939 : Blo 307833 307939 := bstep (se 1 (by rfl) ⟨230954, by rfl⟩ : syracuseStep 307939 = 461909) B461909
theorem B1880803 : Blo 307833 1880803 := bstep (se 1 (by rfl) ⟨1410602, by rfl⟩ : syracuseStep 1880803 = 2821205) B2821205
theorem B307955 : Blo 307833 307955 := bstep (se 1 (by rfl) ⟨230966, by rfl⟩ : syracuseStep 307955 = 461933) B461933
theorem B307971 : Blo 307833 307971 := bstep (se 1 (by rfl) ⟨230978, by rfl⟩ : syracuseStep 307971 = 461957) B461957
theorem B307987 : Blo 307833 307987 := bstep (se 1 (by rfl) ⟨230990, by rfl⟩ : syracuseStep 307987 = 461981) B461981
theorem B308003 : Blo 307833 308003 := bstep (se 1 (by rfl) ⟨231002, by rfl⟩ : syracuseStep 308003 = 462005) B462005
theorem B308019 : Blo 307833 308019 := bstep (se 1 (by rfl) ⟨231014, by rfl⟩ : syracuseStep 308019 = 462029) B462029
theorem B308035 : Blo 307833 308035 := bstep (se 1 (by rfl) ⟨231026, by rfl⟩ : syracuseStep 308035 = 462053) B462053
theorem B668483 : Blo 307833 668483 := bstep (se 1 (by rfl) ⟨501362, by rfl⟩ : syracuseStep 668483 = 1002725) B1002725
theorem B308051 : Blo 307833 308051 := bstep (se 1 (by rfl) ⟨231038, by rfl⟩ : syracuseStep 308051 = 462077) B462077
theorem B308067 : Blo 307833 308067 := bstep (se 1 (by rfl) ⟨231050, by rfl⟩ : syracuseStep 308067 = 462101) B462101
theorem B701297 : Blo 307833 701297 := bstep (se 2 (by rfl) ⟨262986, by rfl⟩ : syracuseStep 701297 = 525973) B525973
theorem B308083 : Blo 307833 308083 := bstep (se 1 (by rfl) ⟨231062, by rfl⟩ : syracuseStep 308083 = 462125) B462125
theorem B308099 : Blo 307833 308099 := bstep (se 1 (by rfl) ⟨231074, by rfl⟩ : syracuseStep 308099 = 462149) B462149
theorem B701315 : Blo 307833 701315 := bstep (se 1 (by rfl) ⟨525986, by rfl⟩ : syracuseStep 701315 = 1051973) B1051973
theorem B471953 : Blo 307833 471953 := bstep (se 2 (by rfl) ⟨176982, by rfl⟩ : syracuseStep 471953 = 353965) B353965
theorem B308115 : Blo 307833 308115 := bstep (se 1 (by rfl) ⟨231086, by rfl⟩ : syracuseStep 308115 = 462173) B462173
theorem B308131 : Blo 307833 308131 := bstep (se 1 (by rfl) ⟨231098, by rfl⟩ : syracuseStep 308131 = 462197) B462197
theorem B308147 : Blo 307833 308147 := bstep (se 1 (by rfl) ⟨231110, by rfl⟩ : syracuseStep 308147 = 462221) B462221
theorem B308163 : Blo 307833 308163 := bstep (se 1 (by rfl) ⟨231122, by rfl⟩ : syracuseStep 308163 = 462245) B462245
theorem B308179 : Blo 307833 308179 := bstep (se 1 (by rfl) ⟨231134, by rfl⟩ : syracuseStep 308179 = 462269) B462269
theorem B308195 : Blo 307833 308195 := bstep (se 1 (by rfl) ⟨231146, by rfl⟩ : syracuseStep 308195 = 462293) B462293
theorem B373747 : Blo 307833 373747 := bstep (se 1 (by rfl) ⟨280310, by rfl⟩ : syracuseStep 373747 = 560621) B560621
theorem B308211 : Blo 307833 308211 := bstep (se 1 (by rfl) ⟨231158, by rfl⟩ : syracuseStep 308211 = 462317) B462317
theorem B308227 : Blo 307833 308227 := bstep (se 1 (by rfl) ⟨231170, by rfl⟩ : syracuseStep 308227 = 462341) B462341
theorem B308243 : Blo 307833 308243 := bstep (se 1 (by rfl) ⟨231182, by rfl⟩ : syracuseStep 308243 = 462365) B462365
theorem B308259 : Blo 307833 308259 := bstep (se 1 (by rfl) ⟨231194, by rfl⟩ : syracuseStep 308259 = 462389) B462389
theorem B996401 : Blo 307833 996401 := bstep (se 2 (by rfl) ⟨373650, by rfl⟩ : syracuseStep 996401 = 747301) B747301
theorem B308275 : Blo 307833 308275 := bstep (se 1 (by rfl) ⟨231206, by rfl⟩ : syracuseStep 308275 = 462413) B462413
theorem B308291 : Blo 307833 308291 := bstep (se 1 (by rfl) ⟨231218, by rfl⟩ : syracuseStep 308291 = 462437) B462437
theorem B308307 : Blo 307833 308307 := bstep (se 1 (by rfl) ⟨231230, by rfl⟩ : syracuseStep 308307 = 462461) B462461
theorem B308323 : Blo 307833 308323 := bstep (se 1 (by rfl) ⟨231242, by rfl⟩ : syracuseStep 308323 = 462485) B462485
theorem B308339 : Blo 307833 308339 := bstep (se 1 (by rfl) ⟨231254, by rfl⟩ : syracuseStep 308339 = 462509) B462509
theorem B308355 : Blo 307833 308355 := bstep (se 1 (by rfl) ⟨231266, by rfl⟩ : syracuseStep 308355 = 462533) B462533
theorem B701585 : Blo 307833 701585 := bstep (se 2 (by rfl) ⟨263094, by rfl⟩ : syracuseStep 701585 = 526189) B526189
theorem B308371 : Blo 307833 308371 := bstep (se 1 (by rfl) ⟨231278, by rfl⟩ : syracuseStep 308371 = 462557) B462557
theorem B308387 : Blo 307833 308387 := bstep (se 1 (by rfl) ⟨231290, by rfl⟩ : syracuseStep 308387 = 462581) B462581
theorem B701603 : Blo 307833 701603 := bstep (se 1 (by rfl) ⟨526202, by rfl⟩ : syracuseStep 701603 = 1052405) B1052405
theorem B308403 : Blo 307833 308403 := bstep (se 1 (by rfl) ⟨231302, by rfl⟩ : syracuseStep 308403 = 462605) B462605
theorem B505025 : Blo 307833 505025 := bstep (se 2 (by rfl) ⟨189384, by rfl⟩ : syracuseStep 505025 = 378769) B378769
theorem B308419 : Blo 307833 308419 := bstep (se 1 (by rfl) ⟨231314, by rfl⟩ : syracuseStep 308419 = 462629) B462629
theorem B308435 : Blo 307833 308435 := bstep (se 1 (by rfl) ⟨231326, by rfl⟩ : syracuseStep 308435 = 462653) B462653
theorem B308451 : Blo 307833 308451 := bstep (se 1 (by rfl) ⟨231338, by rfl⟩ : syracuseStep 308451 = 462677) B462677
theorem B3880163 : Blo 307833 3880163 := bstep (se 1 (by rfl) ⟨2910122, by rfl⟩ : syracuseStep 3880163 = 5820245) B5820245
theorem B308467 : Blo 307833 308467 := bstep (se 1 (by rfl) ⟨231350, by rfl⟩ : syracuseStep 308467 = 462701) B462701
theorem B439553 : Blo 307833 439553 := bstep (se 2 (by rfl) ⟨164832, by rfl⟩ : syracuseStep 439553 = 329665) B329665
theorem B308483 : Blo 307833 308483 := bstep (se 1 (by rfl) ⟨231362, by rfl⟩ : syracuseStep 308483 = 462725) B462725
theorem B308499 : Blo 307833 308499 := bstep (se 1 (by rfl) ⟨231374, by rfl⟩ : syracuseStep 308499 = 462749) B462749
theorem B308515 : Blo 307833 308515 := bstep (se 1 (by rfl) ⟨231386, by rfl⟩ : syracuseStep 308515 = 462773) B462773
theorem B308531 : Blo 307833 308531 := bstep (se 1 (by rfl) ⟨231398, by rfl⟩ : syracuseStep 308531 = 462797) B462797
theorem B308547 : Blo 307833 308547 := bstep (se 1 (by rfl) ⟨231410, by rfl⟩ : syracuseStep 308547 = 462821) B462821
theorem B472387 : Blo 307833 472387 := bstep (se 1 (by rfl) ⟨354290, by rfl⟩ : syracuseStep 472387 = 708581) B708581
theorem B308563 : Blo 307833 308563 := bstep (se 1 (by rfl) ⟨231422, by rfl⟩ : syracuseStep 308563 = 462845) B462845
theorem B308579 : Blo 307833 308579 := bstep (se 1 (by rfl) ⟨231434, by rfl⟩ : syracuseStep 308579 = 462869) B462869
theorem B308595 : Blo 307833 308595 := bstep (se 1 (by rfl) ⟨231446, by rfl⟩ : syracuseStep 308595 = 462893) B462893
theorem B374131 : Blo 307833 374131 := bstep (se 1 (by rfl) ⟨280598, by rfl⟩ : syracuseStep 374131 = 561197) B561197
theorem B308611 : Blo 307833 308611 := bstep (se 1 (by rfl) ⟨231458, by rfl⟩ : syracuseStep 308611 = 462917) B462917
theorem B996749 : Blo 307833 996749 := bstep (se 3 (by rfl) ⟨186890, by rfl⟩ : syracuseStep 996749 = 373781) B373781
theorem B308627 : Blo 307833 308627 := bstep (se 1 (by rfl) ⟨231470, by rfl⟩ : syracuseStep 308627 = 462941) B462941
theorem B308643 : Blo 307833 308643 := bstep (se 1 (by rfl) ⟨231482, by rfl⟩ : syracuseStep 308643 = 462965) B462965
theorem B308659 : Blo 307833 308659 := bstep (se 1 (by rfl) ⟨231494, by rfl⟩ : syracuseStep 308659 = 462989) B462989
theorem B308675 : Blo 307833 308675 := bstep (se 1 (by rfl) ⟨231506, by rfl⟩ : syracuseStep 308675 = 463013) B463013
theorem B308691 : Blo 307833 308691 := bstep (se 1 (by rfl) ⟨231518, by rfl⟩ : syracuseStep 308691 = 463037) B463037
theorem B308707 : Blo 307833 308707 := bstep (se 1 (by rfl) ⟨231530, by rfl⟩ : syracuseStep 308707 = 463061) B463061
theorem B308723 : Blo 307833 308723 := bstep (se 1 (by rfl) ⟨231542, by rfl⟩ : syracuseStep 308723 = 463085) B463085
theorem B308739 : Blo 307833 308739 := bstep (se 1 (by rfl) ⟨231554, by rfl⟩ : syracuseStep 308739 = 463109) B463109
theorem B308755 : Blo 307833 308755 := bstep (se 1 (by rfl) ⟨231566, by rfl⟩ : syracuseStep 308755 = 463133) B463133
theorem B308771 : Blo 307833 308771 := bstep (se 1 (by rfl) ⟨231578, by rfl⟩ : syracuseStep 308771 = 463157) B463157
theorem B308787 : Blo 307833 308787 := bstep (se 1 (by rfl) ⟨231590, by rfl⟩ : syracuseStep 308787 = 463181) B463181
theorem B308803 : Blo 307833 308803 := bstep (se 1 (by rfl) ⟨231602, by rfl⟩ : syracuseStep 308803 = 463205) B463205
theorem B308819 : Blo 307833 308819 := bstep (se 1 (by rfl) ⟨231614, by rfl⟩ : syracuseStep 308819 = 463229) B463229
theorem B308835 : Blo 307833 308835 := bstep (se 1 (by rfl) ⟨231626, by rfl⟩ : syracuseStep 308835 = 463253) B463253
theorem B308851 : Blo 307833 308851 := bstep (se 1 (by rfl) ⟨231638, by rfl⟩ : syracuseStep 308851 = 463277) B463277
theorem B308867 : Blo 307833 308867 := bstep (se 1 (by rfl) ⟨231650, by rfl⟩ : syracuseStep 308867 = 463301) B463301
theorem B308883 : Blo 307833 308883 := bstep (se 1 (by rfl) ⟨231662, by rfl⟩ : syracuseStep 308883 = 463325) B463325
theorem B308899 : Blo 307833 308899 := bstep (se 1 (by rfl) ⟨231674, by rfl⟩ : syracuseStep 308899 = 463349) B463349
theorem B308915 : Blo 307833 308915 := bstep (se 1 (by rfl) ⟨231686, by rfl⟩ : syracuseStep 308915 = 463373) B463373
theorem B308931 : Blo 307833 308931 := bstep (se 1 (by rfl) ⟨231698, by rfl⟩ : syracuseStep 308931 = 463397) B463397
theorem B308947 : Blo 307833 308947 := bstep (se 1 (by rfl) ⟨231710, by rfl⟩ : syracuseStep 308947 = 463421) B463421
theorem B308963 : Blo 307833 308963 := bstep (se 1 (by rfl) ⟨231722, by rfl⟩ : syracuseStep 308963 = 463445) B463445
theorem B308979 : Blo 307833 308979 := bstep (se 1 (by rfl) ⟨231734, by rfl⟩ : syracuseStep 308979 = 463469) B463469
theorem B308995 : Blo 307833 308995 := bstep (se 1 (by rfl) ⟨231746, by rfl⟩ : syracuseStep 308995 = 463493) B463493
theorem B309011 : Blo 307833 309011 := bstep (se 1 (by rfl) ⟨231758, by rfl⟩ : syracuseStep 309011 = 463517) B463517
theorem B440083 : Blo 307833 440083 := bstep (se 1 (by rfl) ⟨330062, by rfl⟩ : syracuseStep 440083 = 660125) B660125
theorem B309027 : Blo 307833 309027 := bstep (se 1 (by rfl) ⟨231770, by rfl⟩ : syracuseStep 309027 = 463541) B463541
theorem B309043 : Blo 307833 309043 := bstep (se 1 (by rfl) ⟨231782, by rfl⟩ : syracuseStep 309043 = 463565) B463565
theorem B309059 : Blo 307833 309059 := bstep (se 1 (by rfl) ⟨231794, by rfl⟩ : syracuseStep 309059 = 463589) B463589
theorem B309075 : Blo 307833 309075 := bstep (se 1 (by rfl) ⟨231806, by rfl⟩ : syracuseStep 309075 = 463613) B463613
theorem B309091 : Blo 307833 309091 := bstep (se 1 (by rfl) ⟨231818, by rfl⟩ : syracuseStep 309091 = 463637) B463637
theorem B309107 : Blo 307833 309107 := bstep (se 1 (by rfl) ⟨231830, by rfl⟩ : syracuseStep 309107 = 463661) B463661
theorem B309123 : Blo 307833 309123 := bstep (se 1 (by rfl) ⟨231842, by rfl⟩ : syracuseStep 309123 = 463685) B463685
theorem B309139 : Blo 307833 309139 := bstep (se 1 (by rfl) ⟨231854, by rfl⟩ : syracuseStep 309139 = 463709) B463709
theorem B309155 : Blo 307833 309155 := bstep (se 1 (by rfl) ⟨231866, by rfl⟩ : syracuseStep 309155 = 463733) B463733
theorem B309171 : Blo 307833 309171 := bstep (se 1 (by rfl) ⟨231878, by rfl⟩ : syracuseStep 309171 = 463757) B463757
theorem B309187 : Blo 307833 309187 := bstep (se 1 (by rfl) ⟨231890, by rfl⟩ : syracuseStep 309187 = 463781) B463781
theorem B309203 : Blo 307833 309203 := bstep (se 1 (by rfl) ⟨231902, by rfl⟩ : syracuseStep 309203 = 463805) B463805
theorem B309219 : Blo 307833 309219 := bstep (se 1 (by rfl) ⟨231914, by rfl⟩ : syracuseStep 309219 = 463829) B463829
theorem B309235 : Blo 307833 309235 := bstep (se 1 (by rfl) ⟨231926, by rfl⟩ : syracuseStep 309235 = 463853) B463853
theorem B309251 : Blo 307833 309251 := bstep (se 1 (by rfl) ⟨231938, by rfl⟩ : syracuseStep 309251 = 463877) B463877
theorem B309267 : Blo 307833 309267 := bstep (se 1 (by rfl) ⟨231950, by rfl⟩ : syracuseStep 309267 = 463901) B463901
theorem B309283 : Blo 307833 309283 := bstep (se 1 (by rfl) ⟨231962, by rfl⟩ : syracuseStep 309283 = 463925) B463925
theorem B309299 : Blo 307833 309299 := bstep (se 1 (by rfl) ⟨231974, by rfl⟩ : syracuseStep 309299 = 463949) B463949
theorem B309315 : Blo 307833 309315 := bstep (se 1 (by rfl) ⟨231986, by rfl⟩ : syracuseStep 309315 = 463973) B463973
theorem B309331 : Blo 307833 309331 := bstep (se 1 (by rfl) ⟨231998, by rfl⟩ : syracuseStep 309331 = 463997) B463997
theorem B440419 : Blo 307833 440419 := bstep (se 1 (by rfl) ⟨330314, by rfl⟩ : syracuseStep 440419 = 660629) B660629
theorem B309347 : Blo 307833 309347 := bstep (se 1 (by rfl) ⟨232010, by rfl⟩ : syracuseStep 309347 = 464021) B464021
theorem B2373745 : Blo 307833 2373745 := bstep (se 2 (by rfl) ⟨890154, by rfl⟩ : syracuseStep 2373745 = 1780309) B1780309
theorem B309363 : Blo 307833 309363 := bstep (se 1 (by rfl) ⟨232022, by rfl⟩ : syracuseStep 309363 = 464045) B464045
theorem B309379 : Blo 307833 309379 := bstep (se 1 (by rfl) ⟨232034, by rfl⟩ : syracuseStep 309379 = 464069) B464069
theorem B1620109 : Blo 307833 1620109 := bstep (se 3 (by rfl) ⟨303770, by rfl⟩ : syracuseStep 1620109 = 607541) B607541
theorem B309395 : Blo 307833 309395 := bstep (se 1 (by rfl) ⟨232046, by rfl⟩ : syracuseStep 309395 = 464093) B464093
theorem B309411 : Blo 307833 309411 := bstep (se 1 (by rfl) ⟨232058, by rfl⟩ : syracuseStep 309411 = 464117) B464117
theorem B309427 : Blo 307833 309427 := bstep (se 1 (by rfl) ⟨232070, by rfl⟩ : syracuseStep 309427 = 464141) B464141
theorem B309443 : Blo 307833 309443 := bstep (se 1 (by rfl) ⟨232082, by rfl⟩ : syracuseStep 309443 = 464165) B464165
theorem B2341061 : Blo 307833 2341061 := bstep (se 4 (by rfl) ⟨219474, by rfl⟩ : syracuseStep 2341061 = 438949) B438949
theorem B309459 : Blo 307833 309459 := bstep (se 1 (by rfl) ⟨232094, by rfl⟩ : syracuseStep 309459 = 464189) B464189
theorem B309475 : Blo 307833 309475 := bstep (se 1 (by rfl) ⟨232106, by rfl⟩ : syracuseStep 309475 = 464213) B464213
theorem B309491 : Blo 307833 309491 := bstep (se 1 (by rfl) ⟨232118, by rfl⟩ : syracuseStep 309491 = 464237) B464237
theorem B309507 : Blo 307833 309507 := bstep (se 1 (by rfl) ⟨232130, by rfl⟩ : syracuseStep 309507 = 464261) B464261
theorem B309523 : Blo 307833 309523 := bstep (se 1 (by rfl) ⟨232142, by rfl⟩ : syracuseStep 309523 = 464285) B464285
theorem B309539 : Blo 307833 309539 := bstep (se 1 (by rfl) ⟨232154, by rfl⟩ : syracuseStep 309539 = 464309) B464309
theorem B309555 : Blo 307833 309555 := bstep (se 1 (by rfl) ⟨232166, by rfl⟩ : syracuseStep 309555 = 464333) B464333
theorem B3946805 : Blo 307833 3946805 := bstep (se 5 (by rfl) ⟨185006, by rfl⟩ : syracuseStep 3946805 = 370013) B370013
theorem B309571 : Blo 307833 309571 := bstep (se 1 (by rfl) ⟨232178, by rfl⟩ : syracuseStep 309571 = 464357) B464357
theorem B309587 : Blo 307833 309587 := bstep (se 1 (by rfl) ⟨232190, by rfl⟩ : syracuseStep 309587 = 464381) B464381
theorem B309603 : Blo 307833 309603 := bstep (se 1 (by rfl) ⟨232202, by rfl⟩ : syracuseStep 309603 = 464405) B464405
theorem B309619 : Blo 307833 309619 := bstep (se 1 (by rfl) ⟨232214, by rfl⟩ : syracuseStep 309619 = 464429) B464429
theorem B309635 : Blo 307833 309635 := bstep (se 1 (by rfl) ⟨232226, by rfl⟩ : syracuseStep 309635 = 464453) B464453
theorem B309651 : Blo 307833 309651 := bstep (se 1 (by rfl) ⟨232238, by rfl⟩ : syracuseStep 309651 = 464477) B464477
theorem B309667 : Blo 307833 309667 := bstep (se 1 (by rfl) ⟨232250, by rfl⟩ : syracuseStep 309667 = 464501) B464501
theorem B833969 : Blo 307833 833969 := bstep (se 2 (by rfl) ⟨312738, by rfl⟩ : syracuseStep 833969 = 625477) B625477
theorem B309683 : Blo 307833 309683 := bstep (se 1 (by rfl) ⟨232262, by rfl⟩ : syracuseStep 309683 = 464525) B464525
theorem B309699 : Blo 307833 309699 := bstep (se 1 (by rfl) ⟨232274, by rfl⟩ : syracuseStep 309699 = 464549) B464549
theorem B309715 : Blo 307833 309715 := bstep (se 1 (by rfl) ⟨232286, by rfl⟩ : syracuseStep 309715 = 464573) B464573
theorem B309731 : Blo 307833 309731 := bstep (se 1 (by rfl) ⟨232298, by rfl⟩ : syracuseStep 309731 = 464597) B464597
theorem B309747 : Blo 307833 309747 := bstep (se 1 (by rfl) ⟨232310, by rfl⟩ : syracuseStep 309747 = 464621) B464621
theorem B309763 : Blo 307833 309763 := bstep (se 1 (by rfl) ⟨232322, by rfl⟩ : syracuseStep 309763 = 464645) B464645
theorem B309779 : Blo 307833 309779 := bstep (se 1 (by rfl) ⟨232334, by rfl⟩ : syracuseStep 309779 = 464669) B464669
theorem B7191061 : Blo 307833 7191061 := bstep (se 6 (by rfl) ⟨168540, by rfl⟩ : syracuseStep 7191061 = 337081) B337081
theorem B309795 : Blo 307833 309795 := bstep (se 1 (by rfl) ⟨232346, by rfl⟩ : syracuseStep 309795 = 464693) B464693
theorem B309811 : Blo 307833 309811 := bstep (se 1 (by rfl) ⟨232358, by rfl⟩ : syracuseStep 309811 = 464717) B464717
theorem B309827 : Blo 307833 309827 := bstep (se 1 (by rfl) ⟨232370, by rfl⟩ : syracuseStep 309827 = 464741) B464741
theorem B473681 : Blo 307833 473681 := bstep (se 2 (by rfl) ⟨177630, by rfl⟩ : syracuseStep 473681 = 355261) B355261
theorem B309843 : Blo 307833 309843 := bstep (se 1 (by rfl) ⟨232382, by rfl⟩ : syracuseStep 309843 = 464765) B464765
theorem B309859 : Blo 307833 309859 := bstep (se 1 (by rfl) ⟨232394, by rfl⟩ : syracuseStep 309859 = 464789) B464789
theorem B309875 : Blo 307833 309875 := bstep (se 1 (by rfl) ⟨232406, by rfl⟩ : syracuseStep 309875 = 464813) B464813
theorem B309891 : Blo 307833 309891 := bstep (se 1 (by rfl) ⟨232418, by rfl⟩ : syracuseStep 309891 = 464837) B464837
theorem B440977 : Blo 307833 440977 := bstep (se 2 (by rfl) ⟨165366, by rfl⟩ : syracuseStep 440977 = 330733) B330733
theorem B309907 : Blo 307833 309907 := bstep (se 1 (by rfl) ⟨232430, by rfl⟩ : syracuseStep 309907 = 464861) B464861
theorem B309923 : Blo 307833 309923 := bstep (se 1 (by rfl) ⟨232442, by rfl⟩ : syracuseStep 309923 = 464885) B464885
theorem B441011 : Blo 307833 441011 := bstep (se 1 (by rfl) ⟨330758, by rfl⟩ : syracuseStep 441011 = 661517) B661517
theorem B309939 : Blo 307833 309939 := bstep (se 1 (by rfl) ⟨232454, by rfl⟩ : syracuseStep 309939 = 464909) B464909
theorem B309955 : Blo 307833 309955 := bstep (se 1 (by rfl) ⟨232466, by rfl⟩ : syracuseStep 309955 = 464933) B464933
theorem B309971 : Blo 307833 309971 := bstep (se 1 (by rfl) ⟨232478, by rfl⟩ : syracuseStep 309971 = 464957) B464957
theorem B309987 : Blo 307833 309987 := bstep (se 1 (by rfl) ⟨232490, by rfl⟩ : syracuseStep 309987 = 464981) B464981
theorem B310003 : Blo 307833 310003 := bstep (se 1 (by rfl) ⟨232502, by rfl⟩ : syracuseStep 310003 = 465005) B465005
theorem B310019 : Blo 307833 310019 := bstep (se 1 (by rfl) ⟨232514, by rfl⟩ : syracuseStep 310019 = 465029) B465029
theorem B310035 : Blo 307833 310035 := bstep (se 1 (by rfl) ⟨232526, by rfl⟩ : syracuseStep 310035 = 465053) B465053
theorem B310051 : Blo 307833 310051 := bstep (se 1 (by rfl) ⟨232538, by rfl⟩ : syracuseStep 310051 = 465077) B465077
theorem B310067 : Blo 307833 310067 := bstep (se 1 (by rfl) ⟨232550, by rfl⟩ : syracuseStep 310067 = 465101) B465101
theorem B310083 : Blo 307833 310083 := bstep (se 1 (by rfl) ⟨232562, by rfl⟩ : syracuseStep 310083 = 465125) B465125
theorem B310099 : Blo 307833 310099 := bstep (se 1 (by rfl) ⟨232574, by rfl⟩ : syracuseStep 310099 = 465149) B465149
theorem B310115 : Blo 307833 310115 := bstep (se 1 (by rfl) ⟨232586, by rfl⟩ : syracuseStep 310115 = 465173) B465173
theorem B310131 : Blo 307833 310131 := bstep (se 1 (by rfl) ⟨232598, by rfl⟩ : syracuseStep 310131 = 465197) B465197
theorem B310147 : Blo 307833 310147 := bstep (se 1 (by rfl) ⟨232610, by rfl⟩ : syracuseStep 310147 = 465221) B465221
theorem B1424269 : Blo 307833 1424269 := bstep (se 3 (by rfl) ⟨267050, by rfl⟩ : syracuseStep 1424269 = 534101) B534101
theorem B310163 : Blo 307833 310163 := bstep (se 1 (by rfl) ⟨232622, by rfl⟩ : syracuseStep 310163 = 465245) B465245
theorem B310179 : Blo 307833 310179 := bstep (se 1 (by rfl) ⟨232634, by rfl⟩ : syracuseStep 310179 = 465269) B465269
theorem B310195 : Blo 307833 310195 := bstep (se 1 (by rfl) ⟨232646, by rfl⟩ : syracuseStep 310195 = 465293) B465293
theorem B310211 : Blo 307833 310211 := bstep (se 1 (by rfl) ⟨232658, by rfl⟩ : syracuseStep 310211 = 465317) B465317
theorem B310227 : Blo 307833 310227 := bstep (se 1 (by rfl) ⟨232670, by rfl⟩ : syracuseStep 310227 = 465341) B465341
theorem B310243 : Blo 307833 310243 := bstep (se 1 (by rfl) ⟨232682, by rfl⟩ : syracuseStep 310243 = 465365) B465365
theorem B310259 : Blo 307833 310259 := bstep (se 1 (by rfl) ⟨232694, by rfl⟩ : syracuseStep 310259 = 465389) B465389
theorem B310275 : Blo 307833 310275 := bstep (se 1 (by rfl) ⟨232706, by rfl⟩ : syracuseStep 310275 = 465413) B465413
theorem B310291 : Blo 307833 310291 := bstep (se 1 (by rfl) ⟨232718, by rfl⟩ : syracuseStep 310291 = 465437) B465437
theorem B310307 : Blo 307833 310307 := bstep (se 1 (by rfl) ⟨232730, by rfl⟩ : syracuseStep 310307 = 465461) B465461
theorem B310323 : Blo 307833 310323 := bstep (se 1 (by rfl) ⟨232742, by rfl⟩ : syracuseStep 310323 = 465485) B465485
theorem B310339 : Blo 307833 310339 := bstep (se 1 (by rfl) ⟨232754, by rfl⟩ : syracuseStep 310339 = 465509) B465509
theorem B310355 : Blo 307833 310355 := bstep (se 1 (by rfl) ⟨232766, by rfl⟩ : syracuseStep 310355 = 465533) B465533
theorem B310371 : Blo 307833 310371 := bstep (se 1 (by rfl) ⟨232778, by rfl⟩ : syracuseStep 310371 = 465557) B465557
theorem B310387 : Blo 307833 310387 := bstep (se 1 (by rfl) ⟨232790, by rfl⟩ : syracuseStep 310387 = 465581) B465581
theorem B310403 : Blo 307833 310403 := bstep (se 1 (by rfl) ⟨232802, by rfl⟩ : syracuseStep 310403 = 465605) B465605
theorem B310419 : Blo 307833 310419 := bstep (se 1 (by rfl) ⟨232814, by rfl⟩ : syracuseStep 310419 = 465629) B465629
theorem B310435 : Blo 307833 310435 := bstep (se 1 (by rfl) ⟨232826, by rfl⟩ : syracuseStep 310435 = 465653) B465653
theorem B310451 : Blo 307833 310451 := bstep (se 1 (by rfl) ⟨232838, by rfl⟩ : syracuseStep 310451 = 465677) B465677
theorem B310467 : Blo 307833 310467 := bstep (se 1 (by rfl) ⟨232850, by rfl⟩ : syracuseStep 310467 = 465701) B465701
theorem B998605 : Blo 307833 998605 := bstep (se 3 (by rfl) ⟨187238, by rfl⟩ : syracuseStep 998605 = 374477) B374477
theorem B310483 : Blo 307833 310483 := bstep (se 1 (by rfl) ⟨232862, by rfl⟩ : syracuseStep 310483 = 465725) B465725
theorem B441569 : Blo 307833 441569 := bstep (se 2 (by rfl) ⟨165588, by rfl⟩ : syracuseStep 441569 = 331177) B331177
theorem B310499 : Blo 307833 310499 := bstep (se 1 (by rfl) ⟨232874, by rfl⟩ : syracuseStep 310499 = 465749) B465749
theorem B310515 : Blo 307833 310515 := bstep (se 1 (by rfl) ⟨232886, by rfl⟩ : syracuseStep 310515 = 465773) B465773
theorem B310531 : Blo 307833 310531 := bstep (se 1 (by rfl) ⟨232898, by rfl⟩ : syracuseStep 310531 = 465797) B465797
theorem B310547 : Blo 307833 310547 := bstep (se 1 (by rfl) ⟨232910, by rfl⟩ : syracuseStep 310547 = 465821) B465821
theorem B310563 : Blo 307833 310563 := bstep (se 1 (by rfl) ⟨232922, by rfl⟩ : syracuseStep 310563 = 465845) B465845
theorem B441649 : Blo 307833 441649 := bstep (se 2 (by rfl) ⟨165618, by rfl⟩ : syracuseStep 441649 = 331237) B331237
theorem B310579 : Blo 307833 310579 := bstep (se 1 (by rfl) ⟨232934, by rfl⟩ : syracuseStep 310579 = 465869) B465869
theorem B310595 : Blo 307833 310595 := bstep (se 1 (by rfl) ⟨232946, by rfl⟩ : syracuseStep 310595 = 465893) B465893
theorem B310611 : Blo 307833 310611 := bstep (se 1 (by rfl) ⟨232958, by rfl⟩ : syracuseStep 310611 = 465917) B465917
theorem B310627 : Blo 307833 310627 := bstep (se 1 (by rfl) ⟨232970, by rfl⟩ : syracuseStep 310627 = 465941) B465941
theorem B310643 : Blo 307833 310643 := bstep (se 1 (by rfl) ⟨232982, by rfl⟩ : syracuseStep 310643 = 465965) B465965
theorem B310659 : Blo 307833 310659 := bstep (se 1 (by rfl) ⟨232994, by rfl⟩ : syracuseStep 310659 = 465989) B465989
theorem B310675 : Blo 307833 310675 := bstep (se 1 (by rfl) ⟨233006, by rfl⟩ : syracuseStep 310675 = 466013) B466013
theorem B310691 : Blo 307833 310691 := bstep (se 1 (by rfl) ⟨233018, by rfl⟩ : syracuseStep 310691 = 466037) B466037
theorem B310707 : Blo 307833 310707 := bstep (se 1 (by rfl) ⟨233030, by rfl⟩ : syracuseStep 310707 = 466061) B466061
theorem B310723 : Blo 307833 310723 := bstep (se 1 (by rfl) ⟨233042, by rfl⟩ : syracuseStep 310723 = 466085) B466085
theorem B310739 : Blo 307833 310739 := bstep (se 1 (by rfl) ⟨233054, by rfl⟩ : syracuseStep 310739 = 466109) B466109
theorem B310755 : Blo 307833 310755 := bstep (se 1 (by rfl) ⟨233066, by rfl⟩ : syracuseStep 310755 = 466133) B466133
theorem B310771 : Blo 307833 310771 := bstep (se 1 (by rfl) ⟨233078, by rfl⟩ : syracuseStep 310771 = 466157) B466157
theorem B310787 : Blo 307833 310787 := bstep (se 1 (by rfl) ⟨233090, by rfl⟩ : syracuseStep 310787 = 466181) B466181
theorem B310803 : Blo 307833 310803 := bstep (se 1 (by rfl) ⟨233102, by rfl⟩ : syracuseStep 310803 = 466205) B466205
theorem B310819 : Blo 307833 310819 := bstep (se 1 (by rfl) ⟨233114, by rfl⟩ : syracuseStep 310819 = 466229) B466229
theorem B310835 : Blo 307833 310835 := bstep (se 1 (by rfl) ⟨233126, by rfl⟩ : syracuseStep 310835 = 466253) B466253
theorem B310851 : Blo 307833 310851 := bstep (se 1 (by rfl) ⟨233138, by rfl⟩ : syracuseStep 310851 = 466277) B466277
theorem B310867 : Blo 307833 310867 := bstep (se 1 (by rfl) ⟨233150, by rfl⟩ : syracuseStep 310867 = 466301) B466301
theorem B310883 : Blo 307833 310883 := bstep (se 1 (by rfl) ⟨233162, by rfl⟩ : syracuseStep 310883 = 466325) B466325
theorem B310899 : Blo 307833 310899 := bstep (se 1 (by rfl) ⟨233174, by rfl⟩ : syracuseStep 310899 = 466349) B466349
theorem B310915 : Blo 307833 310915 := bstep (se 1 (by rfl) ⟨233186, by rfl⟩ : syracuseStep 310915 = 466373) B466373
theorem B310931 : Blo 307833 310931 := bstep (se 1 (by rfl) ⟨233198, by rfl⟩ : syracuseStep 310931 = 466397) B466397
theorem B310947 : Blo 307833 310947 := bstep (se 1 (by rfl) ⟨233210, by rfl⟩ : syracuseStep 310947 = 466421) B466421
theorem B310963 : Blo 307833 310963 := bstep (se 1 (by rfl) ⟨233222, by rfl⟩ : syracuseStep 310963 = 466445) B466445
theorem B310979 : Blo 307833 310979 := bstep (se 1 (by rfl) ⟨233234, by rfl⟩ : syracuseStep 310979 = 466469) B466469
theorem B704209 : Blo 307833 704209 := bstep (se 2 (by rfl) ⟨264078, by rfl⟩ : syracuseStep 704209 = 528157) B528157
theorem B310995 : Blo 307833 310995 := bstep (se 1 (by rfl) ⟨233246, by rfl⟩ : syracuseStep 310995 = 466493) B466493
theorem B311011 : Blo 307833 311011 := bstep (se 1 (by rfl) ⟨233258, by rfl⟩ : syracuseStep 311011 = 466517) B466517
theorem B311027 : Blo 307833 311027 := bstep (se 1 (by rfl) ⟨233270, by rfl⟩ : syracuseStep 311027 = 466541) B466541
theorem B311043 : Blo 307833 311043 := bstep (se 1 (by rfl) ⟨233282, by rfl⟩ : syracuseStep 311043 = 466565) B466565
theorem B1883917 : Blo 307833 1883917 := bstep (se 3 (by rfl) ⟨353234, by rfl⟩ : syracuseStep 1883917 = 706469) B706469
theorem B311059 : Blo 307833 311059 := bstep (se 1 (by rfl) ⟨233294, by rfl⟩ : syracuseStep 311059 = 466589) B466589
theorem B311075 : Blo 307833 311075 := bstep (se 1 (by rfl) ⟨233306, by rfl⟩ : syracuseStep 311075 = 466613) B466613
theorem B311091 : Blo 307833 311091 := bstep (se 1 (by rfl) ⟨233318, by rfl⟩ : syracuseStep 311091 = 466637) B466637
theorem B311107 : Blo 307833 311107 := bstep (se 1 (by rfl) ⟨233330, by rfl⟩ : syracuseStep 311107 = 466661) B466661
theorem B311123 : Blo 307833 311123 := bstep (se 1 (by rfl) ⟨233342, by rfl⟩ : syracuseStep 311123 = 466685) B466685
theorem B311139 : Blo 307833 311139 := bstep (se 1 (by rfl) ⟨233354, by rfl⟩ : syracuseStep 311139 = 466709) B466709
theorem B311155 : Blo 307833 311155 := bstep (se 1 (by rfl) ⟨233366, by rfl⟩ : syracuseStep 311155 = 466733) B466733
theorem B311171 : Blo 307833 311171 := bstep (se 1 (by rfl) ⟨233378, by rfl⟩ : syracuseStep 311171 = 466757) B466757
theorem B311187 : Blo 307833 311187 := bstep (se 1 (by rfl) ⟨233390, by rfl⟩ : syracuseStep 311187 = 466781) B466781
theorem B311203 : Blo 307833 311203 := bstep (se 1 (by rfl) ⟨233402, by rfl⟩ : syracuseStep 311203 = 466805) B466805
theorem B311219 : Blo 307833 311219 := bstep (se 1 (by rfl) ⟨233414, by rfl⟩ : syracuseStep 311219 = 466829) B466829
theorem B311235 : Blo 307833 311235 := bstep (se 1 (by rfl) ⟨233426, by rfl⟩ : syracuseStep 311235 = 466853) B466853
theorem B311251 : Blo 307833 311251 := bstep (se 1 (by rfl) ⟨233438, by rfl⟩ : syracuseStep 311251 = 466877) B466877
theorem B311267 : Blo 307833 311267 := bstep (se 1 (by rfl) ⟨233450, by rfl⟩ : syracuseStep 311267 = 466901) B466901
theorem B311283 : Blo 307833 311283 := bstep (se 1 (by rfl) ⟨233462, by rfl⟩ : syracuseStep 311283 = 466925) B466925
theorem B311299 : Blo 307833 311299 := bstep (se 1 (by rfl) ⟨233474, by rfl⟩ : syracuseStep 311299 = 466949) B466949
theorem B311315 : Blo 307833 311315 := bstep (se 1 (by rfl) ⟨233486, by rfl⟩ : syracuseStep 311315 = 466973) B466973
theorem B311331 : Blo 307833 311331 := bstep (se 1 (by rfl) ⟨233498, by rfl⟩ : syracuseStep 311331 = 466997) B466997
theorem B311347 : Blo 307833 311347 := bstep (se 1 (by rfl) ⟨233510, by rfl⟩ : syracuseStep 311347 = 467021) B467021
theorem B442435 : Blo 307833 442435 := bstep (se 1 (by rfl) ⟨331826, by rfl⟩ : syracuseStep 442435 = 663653) B663653
theorem B311363 : Blo 307833 311363 := bstep (se 1 (by rfl) ⟨233522, by rfl⟩ : syracuseStep 311363 = 467045) B467045
theorem B311379 : Blo 307833 311379 := bstep (se 1 (by rfl) ⟨233534, by rfl⟩ : syracuseStep 311379 = 467069) B467069
theorem B1065059 : Blo 307833 1065059 := bstep (se 1 (by rfl) ⟨798794, by rfl⟩ : syracuseStep 1065059 = 1597589) B1597589
theorem B311395 : Blo 307833 311395 := bstep (se 1 (by rfl) ⟨233546, by rfl⟩ : syracuseStep 311395 = 467093) B467093
theorem B311411 : Blo 307833 311411 := bstep (se 1 (by rfl) ⟨233558, by rfl⟩ : syracuseStep 311411 = 467117) B467117
theorem B311427 : Blo 307833 311427 := bstep (se 1 (by rfl) ⟨233570, by rfl⟩ : syracuseStep 311427 = 467141) B467141
theorem B311443 : Blo 307833 311443 := bstep (se 1 (by rfl) ⟨233582, by rfl⟩ : syracuseStep 311443 = 467165) B467165
theorem B311459 : Blo 307833 311459 := bstep (se 1 (by rfl) ⟨233594, by rfl⟩ : syracuseStep 311459 = 467189) B467189
theorem B311475 : Blo 307833 311475 := bstep (se 1 (by rfl) ⟨233606, by rfl⟩ : syracuseStep 311475 = 467213) B467213
theorem B311491 : Blo 307833 311491 := bstep (se 1 (by rfl) ⟨233618, by rfl⟩ : syracuseStep 311491 = 467237) B467237
theorem B311507 : Blo 307833 311507 := bstep (se 1 (by rfl) ⟨233630, by rfl⟩ : syracuseStep 311507 = 467261) B467261
theorem B311523 : Blo 307833 311523 := bstep (se 1 (by rfl) ⟨233642, by rfl⟩ : syracuseStep 311523 = 467285) B467285
theorem B311539 : Blo 307833 311539 := bstep (se 1 (by rfl) ⟨233654, by rfl⟩ : syracuseStep 311539 = 467309) B467309
theorem B311555 : Blo 307833 311555 := bstep (se 1 (by rfl) ⟨233666, by rfl⟩ : syracuseStep 311555 = 467333) B467333
theorem B1327373 : Blo 307833 1327373 := bstep (se 3 (by rfl) ⟨248882, by rfl⟩ : syracuseStep 1327373 = 497765) B497765
theorem B311571 : Blo 307833 311571 := bstep (se 1 (by rfl) ⟨233678, by rfl⟩ : syracuseStep 311571 = 467357) B467357
theorem B311587 : Blo 307833 311587 := bstep (se 1 (by rfl) ⟨233690, by rfl⟩ : syracuseStep 311587 = 467381) B467381
theorem B311603 : Blo 307833 311603 := bstep (se 1 (by rfl) ⟨233702, by rfl⟩ : syracuseStep 311603 = 467405) B467405
theorem B311619 : Blo 307833 311619 := bstep (se 1 (by rfl) ⟨233714, by rfl⟩ : syracuseStep 311619 = 467429) B467429
theorem B999761 : Blo 307833 999761 := bstep (se 2 (by rfl) ⟨374910, by rfl⟩ : syracuseStep 999761 = 749821) B749821
theorem B311635 : Blo 307833 311635 := bstep (se 1 (by rfl) ⟨233726, by rfl⟩ : syracuseStep 311635 = 467453) B467453
theorem B311651 : Blo 307833 311651 := bstep (se 1 (by rfl) ⟨233738, by rfl⟩ : syracuseStep 311651 = 467477) B467477
theorem B311667 : Blo 307833 311667 := bstep (se 1 (by rfl) ⟨233750, by rfl⟩ : syracuseStep 311667 = 467501) B467501
theorem B311683 : Blo 307833 311683 := bstep (se 1 (by rfl) ⟨233762, by rfl⟩ : syracuseStep 311683 = 467525) B467525
theorem B311699 : Blo 307833 311699 := bstep (se 1 (by rfl) ⟨233774, by rfl⟩ : syracuseStep 311699 = 467549) B467549
theorem B311715 : Blo 307833 311715 := bstep (se 1 (by rfl) ⟨233786, by rfl⟩ : syracuseStep 311715 = 467573) B467573
theorem B311731 : Blo 307833 311731 := bstep (se 1 (by rfl) ⟨233798, by rfl⟩ : syracuseStep 311731 = 467597) B467597
theorem B311747 : Blo 307833 311747 := bstep (se 1 (by rfl) ⟨233810, by rfl⟩ : syracuseStep 311747 = 467621) B467621
theorem B836045 : Blo 307833 836045 := bstep (se 3 (by rfl) ⟨156758, by rfl⟩ : syracuseStep 836045 = 313517) B313517
theorem B311763 : Blo 307833 311763 := bstep (se 1 (by rfl) ⟨233822, by rfl⟩ : syracuseStep 311763 = 467645) B467645
theorem B311779 : Blo 307833 311779 := bstep (se 1 (by rfl) ⟨233834, by rfl⟩ : syracuseStep 311779 = 467669) B467669
theorem B311795 : Blo 307833 311795 := bstep (se 1 (by rfl) ⟨233846, by rfl⟩ : syracuseStep 311795 = 467693) B467693
theorem B311811 : Blo 307833 311811 := bstep (se 1 (by rfl) ⟨233858, by rfl⟩ : syracuseStep 311811 = 467717) B467717
theorem B311827 : Blo 307833 311827 := bstep (se 1 (by rfl) ⟨233870, by rfl⟩ : syracuseStep 311827 = 467741) B467741
theorem B442913 : Blo 307833 442913 := bstep (se 2 (by rfl) ⟨166092, by rfl⟩ : syracuseStep 442913 = 332185) B332185
theorem B1327715 : Blo 307833 1327715 := bstep (se 1 (by rfl) ⟨995786, by rfl⟩ : syracuseStep 1327715 = 1991573) B1991573
theorem B1688197 : Blo 307833 1688197 := bstep (se 4 (by rfl) ⟨158268, by rfl⟩ : syracuseStep 1688197 = 316537) B316537
theorem B443027 : Blo 307833 443027 := bstep (se 1 (by rfl) ⟨332270, by rfl⟩ : syracuseStep 443027 = 664541) B664541
theorem B443107 : Blo 307833 443107 := bstep (se 1 (by rfl) ⟨332330, by rfl⟩ : syracuseStep 443107 = 664661) B664661
theorem B836369 : Blo 307833 836369 := bstep (se 2 (by rfl) ⟨313638, by rfl⟩ : syracuseStep 836369 = 627277) B627277
theorem B1983473 : Blo 307833 1983473 := bstep (se 2 (by rfl) ⟨743802, by rfl⟩ : syracuseStep 1983473 = 1487605) B1487605
theorem B1328177 : Blo 307833 1328177 := bstep (se 2 (by rfl) ⟨498066, by rfl⟩ : syracuseStep 1328177 = 996133) B996133
theorem B443665 : Blo 307833 443665 := bstep (se 2 (by rfl) ⟨166374, by rfl⟩ : syracuseStep 443665 = 332749) B332749
theorem B607651 : Blo 307833 607651 := bstep (se 1 (by rfl) ⟨455738, by rfl⟩ : syracuseStep 607651 = 911477) B911477
theorem B1492451 : Blo 307833 1492451 := bstep (se 1 (by rfl) ⟨1119338, by rfl⟩ : syracuseStep 1492451 = 2238677) B2238677
theorem B706051 : Blo 307833 706051 := bstep (se 1 (by rfl) ⟨529538, by rfl⟩ : syracuseStep 706051 = 1059077) B1059077
theorem B1754885 : Blo 307833 1754885 := bstep (se 4 (by rfl) ⟨164520, by rfl⟩ : syracuseStep 1754885 = 329041) B329041
theorem B1755341 : Blo 307833 1755341 := bstep (se 3 (by rfl) ⟨329126, by rfl⟩ : syracuseStep 1755341 = 658253) B658253
theorem B346387 : Blo 307833 346387 := bstep (se 1 (by rfl) ⟨259790, by rfl⟩ : syracuseStep 346387 = 519581) B519581
theorem B1558925 : Blo 307833 1558925 := bstep (se 3 (by rfl) ⟨292298, by rfl⟩ : syracuseStep 1558925 = 584597) B584597
theorem B346531 : Blo 307833 346531 := bstep (se 1 (by rfl) ⟨259898, by rfl⟩ : syracuseStep 346531 = 519797) B519797
theorem B346675 : Blo 307833 346675 := bstep (se 1 (by rfl) ⟨260006, by rfl⟩ : syracuseStep 346675 = 520013) B520013
theorem B1493603 : Blo 307833 1493603 := bstep (se 1 (by rfl) ⟨1120202, by rfl⟩ : syracuseStep 1493603 = 2240405) B2240405
theorem B346819 : Blo 307833 346819 := bstep (se 1 (by rfl) ⟨260114, by rfl⟩ : syracuseStep 346819 = 520229) B520229
theorem B1002257 : Blo 307833 1002257 := bstep (se 2 (by rfl) ⟨375846, by rfl⟩ : syracuseStep 1002257 = 751693) B751693
theorem B346963 : Blo 307833 346963 := bstep (se 1 (by rfl) ⟨260222, by rfl⟩ : syracuseStep 346963 = 520445) B520445
theorem B904081 : Blo 307833 904081 := bstep (se 2 (by rfl) ⟨339030, by rfl⟩ : syracuseStep 904081 = 678061) B678061
theorem B347107 : Blo 307833 347107 := bstep (se 1 (by rfl) ⟨260330, by rfl⟩ : syracuseStep 347107 = 520661) B520661
theorem B347251 : Blo 307833 347251 := bstep (se 1 (by rfl) ⟨260438, by rfl⟩ : syracuseStep 347251 = 520877) B520877
theorem B740497 : Blo 307833 740497 := bstep (se 2 (by rfl) ⟨277686, by rfl⟩ : syracuseStep 740497 = 555373) B555373
theorem B314611 : Blo 307833 314611 := bstep (se 1 (by rfl) ⟨235958, by rfl⟩ : syracuseStep 314611 = 471917) B471917
theorem B347395 : Blo 307833 347395 := bstep (se 1 (by rfl) ⟨260546, by rfl⟩ : syracuseStep 347395 = 521093) B521093
theorem B1494371 : Blo 307833 1494371 := bstep (se 1 (by rfl) ⟨1120778, by rfl⟩ : syracuseStep 1494371 = 2241557) B2241557
theorem B5000561 : Blo 307833 5000561 := bstep (se 2 (by rfl) ⟨1875210, by rfl⟩ : syracuseStep 5000561 = 3750421) B3750421
theorem B1985933 : Blo 307833 1985933 := bstep (se 3 (by rfl) ⟨372362, by rfl⟩ : syracuseStep 1985933 = 744725) B744725
theorem B347539 : Blo 307833 347539 := bstep (se 1 (by rfl) ⟨260654, by rfl⟩ : syracuseStep 347539 = 521309) B521309
theorem B2641349 : Blo 307833 2641349 := bstep (se 4 (by rfl) ⟨247626, by rfl⟩ : syracuseStep 2641349 = 495253) B495253
theorem B1887715 : Blo 307833 1887715 := bstep (se 1 (by rfl) ⟨1415786, by rfl⟩ : syracuseStep 1887715 = 2831573) B2831573
theorem B347683 : Blo 307833 347683 := bstep (se 1 (by rfl) ⟨260762, by rfl⟩ : syracuseStep 347683 = 521525) B521525
theorem B347827 : Blo 307833 347827 := bstep (se 1 (by rfl) ⟨260870, by rfl⟩ : syracuseStep 347827 = 521741) B521741
theorem B347971 : Blo 307833 347971 := bstep (se 1 (by rfl) ⟨260978, by rfl⟩ : syracuseStep 347971 = 521957) B521957
theorem B2346893 : Blo 307833 2346893 := bstep (se 3 (by rfl) ⟨440042, by rfl⟩ : syracuseStep 2346893 = 880085) B880085
theorem B348115 : Blo 307833 348115 := bstep (se 1 (by rfl) ⟨261086, by rfl⟩ : syracuseStep 348115 = 522173) B522173
theorem B348259 : Blo 307833 348259 := bstep (se 1 (by rfl) ⟨261194, by rfl⟩ : syracuseStep 348259 = 522389) B522389
theorem B1069283 : Blo 307833 1069283 := bstep (se 1 (by rfl) ⟨801962, by rfl⟩ : syracuseStep 1069283 = 1603925) B1603925
theorem B348403 : Blo 307833 348403 := bstep (se 1 (by rfl) ⟨261302, by rfl⟩ : syracuseStep 348403 = 522605) B522605
theorem B1888589 : Blo 307833 1888589 := bstep (se 3 (by rfl) ⟨354110, by rfl⟩ : syracuseStep 1888589 = 708221) B708221
theorem B348547 : Blo 307833 348547 := bstep (se 1 (by rfl) ⟨261410, by rfl⟩ : syracuseStep 348547 = 522821) B522821
theorem B348691 : Blo 307833 348691 := bstep (se 1 (by rfl) ⟨261518, by rfl⟩ : syracuseStep 348691 = 523037) B523037
theorem B1331747 : Blo 307833 1331747 := bstep (se 1 (by rfl) ⟨998810, by rfl⟩ : syracuseStep 1331747 = 1997621) B1997621
theorem B1495601 : Blo 307833 1495601 := bstep (se 2 (by rfl) ⟨560850, by rfl⟩ : syracuseStep 1495601 = 1121701) B1121701
theorem B348835 : Blo 307833 348835 := bstep (se 1 (by rfl) ⟨261626, by rfl⟩ : syracuseStep 348835 = 523253) B523253
theorem B348979 : Blo 307833 348979 := bstep (se 1 (by rfl) ⟨261734, by rfl⟩ : syracuseStep 348979 = 523469) B523469
theorem B349123 : Blo 307833 349123 := bstep (se 1 (by rfl) ⟨261842, by rfl⟩ : syracuseStep 349123 = 523685) B523685
theorem B1758257 : Blo 307833 1758257 := bstep (se 2 (by rfl) ⟨659346, by rfl⟩ : syracuseStep 1758257 = 1318693) B1318693
theorem B1496141 : Blo 307833 1496141 := bstep (se 3 (by rfl) ⟨280526, by rfl⟩ : syracuseStep 1496141 = 561053) B561053
theorem B349267 : Blo 307833 349267 := bstep (se 1 (by rfl) ⟨261950, by rfl⟩ : syracuseStep 349267 = 523901) B523901
theorem B939235 : Blo 307833 939235 := bstep (se 1 (by rfl) ⟨704426, by rfl⟩ : syracuseStep 939235 = 1408853) B1408853
theorem B349411 : Blo 307833 349411 := bstep (se 1 (by rfl) ⟨262058, by rfl⟩ : syracuseStep 349411 = 524117) B524117
theorem B4216049 : Blo 307833 4216049 := bstep (se 2 (by rfl) ⟨1581018, by rfl⟩ : syracuseStep 4216049 = 3162037) B3162037
theorem B1561841 : Blo 307833 1561841 := bstep (se 2 (by rfl) ⟨585690, by rfl⟩ : syracuseStep 1561841 = 1171381) B1171381
theorem B349555 : Blo 307833 349555 := bstep (se 1 (by rfl) ⟨262166, by rfl⟩ : syracuseStep 349555 = 524333) B524333
theorem B349699 : Blo 307833 349699 := bstep (se 1 (by rfl) ⟨262274, by rfl⟩ : syracuseStep 349699 = 524549) B524549
theorem B1988165 : Blo 307833 1988165 := bstep (se 4 (by rfl) ⟨186390, by rfl⟩ : syracuseStep 1988165 = 372781) B372781
theorem B349843 : Blo 307833 349843 := bstep (se 1 (by rfl) ⟨262382, by rfl⟩ : syracuseStep 349843 = 524765) B524765
theorem B1890053 : Blo 307833 1890053 := bstep (se 4 (by rfl) ⟨177192, by rfl⟩ : syracuseStep 1890053 = 354385) B354385
theorem B349987 : Blo 307833 349987 := bstep (se 1 (by rfl) ⟨262490, by rfl⟩ : syracuseStep 349987 = 524981) B524981
theorem B350131 : Blo 307833 350131 := bstep (se 1 (by rfl) ⟨262598, by rfl⟩ : syracuseStep 350131 = 525197) B525197
theorem B841699 : Blo 307833 841699 := bstep (se 1 (by rfl) ⟨631274, by rfl⟩ : syracuseStep 841699 = 1262549) B1262549
theorem B350275 : Blo 307833 350275 := bstep (se 1 (by rfl) ⟨262706, by rfl⟩ : syracuseStep 350275 = 525413) B525413
theorem B841873 : Blo 307833 841873 := bstep (se 2 (by rfl) ⟨315702, by rfl⟩ : syracuseStep 841873 = 631405) B631405
theorem B350419 : Blo 307833 350419 := bstep (se 1 (by rfl) ⟨262814, by rfl⟩ : syracuseStep 350419 = 525629) B525629
theorem B1267939 : Blo 307833 1267939 := bstep (se 1 (by rfl) ⟨950954, by rfl⟩ : syracuseStep 1267939 = 1901909) B1901909
theorem B1169741 : Blo 307833 1169741 := bstep (se 3 (by rfl) ⟨219326, by rfl⟩ : syracuseStep 1169741 = 438653) B438653
theorem B350563 : Blo 307833 350563 := bstep (se 1 (by rfl) ⟨262922, by rfl⟩ : syracuseStep 350563 = 525845) B525845
theorem B1759715 : Blo 307833 1759715 := bstep (se 1 (by rfl) ⟨1319786, by rfl⟩ : syracuseStep 1759715 = 2639573) B2639573
theorem B350707 : Blo 307833 350707 := bstep (se 1 (by rfl) ⟨263030, by rfl⟩ : syracuseStep 350707 = 526061) B526061
theorem B1563299 : Blo 307833 1563299 := bstep (se 1 (by rfl) ⟨1172474, by rfl⟩ : syracuseStep 1563299 = 2344949) B2344949
theorem B2349809 : Blo 307833 2349809 := bstep (se 2 (by rfl) ⟨881178, by rfl⟩ : syracuseStep 2349809 = 1762357) B1762357
theorem B1039121 : Blo 307833 1039121 := bstep (se 2 (by rfl) ⟨389670, by rfl⟩ : syracuseStep 1039121 = 779341) B779341
theorem B416611 : Blo 307833 416611 := bstep (se 1 (by rfl) ⟨312458, by rfl⟩ : syracuseStep 416611 = 624917) B624917
theorem B18963341 : Blo 307833 18963341 := bstep (se 3 (by rfl) ⟨3555626, by rfl⟩ : syracuseStep 18963341 = 7111253) B7111253
theorem B1498061 : Blo 307833 1498061 := bstep (se 3 (by rfl) ⟨280886, by rfl⟩ : syracuseStep 1498061 = 561773) B561773
theorem B744515 : Blo 307833 744515 := bstep (se 1 (by rfl) ⟨558386, by rfl⟩ : syracuseStep 744515 = 1116773) B1116773
theorem B1039661 : Blo 307833 1039661 := bstep (se 3 (by rfl) ⟨194936, by rfl⟩ : syracuseStep 1039661 = 389873) B389873
theorem B1039715 : Blo 307833 1039715 := bstep (se 1 (by rfl) ⟨779786, by rfl⟩ : syracuseStep 1039715 = 1559573) B1559573
theorem B1564109 : Blo 307833 1564109 := bstep (se 3 (by rfl) ⟨293270, by rfl⟩ : syracuseStep 1564109 = 586541) B586541
theorem B1760717 : Blo 307833 1760717 := bstep (se 3 (by rfl) ⟨330134, by rfl⟩ : syracuseStep 1760717 = 660269) B660269
theorem B1039985 : Blo 307833 1039985 := bstep (se 2 (by rfl) ⟨389994, by rfl⟩ : syracuseStep 1039985 = 779989) B779989
theorem B909041 : Blo 307833 909041 := bstep (se 2 (by rfl) ⟨340890, by rfl⟩ : syracuseStep 909041 = 681781) B681781
theorem B450355 : Blo 307833 450355 := bstep (se 1 (by rfl) ⟨337766, by rfl⟩ : syracuseStep 450355 = 675533) B675533
theorem B3170245 : Blo 307833 3170245 := bstep (se 4 (by rfl) ⟨297210, by rfl⟩ : syracuseStep 3170245 = 594421) B594421
theorem B745571 : Blo 307833 745571 := bstep (se 1 (by rfl) ⟨559178, by rfl⟩ : syracuseStep 745571 = 1118357) B1118357
theorem B1040525 : Blo 307833 1040525 := bstep (se 3 (by rfl) ⟨195098, by rfl⟩ : syracuseStep 1040525 = 390197) B390197
theorem B745649 : Blo 307833 745649 := bstep (se 2 (by rfl) ⟨279618, by rfl⟩ : syracuseStep 745649 = 559237) B559237
theorem B1040579 : Blo 307833 1040579 := bstep (se 1 (by rfl) ⟨780434, by rfl⟩ : syracuseStep 1040579 = 1560869) B1560869
theorem B942349 : Blo 307833 942349 := bstep (se 3 (by rfl) ⟨176690, by rfl⟩ : syracuseStep 942349 = 353381) B353381
theorem B1171853 : Blo 307833 1171853 := bstep (se 3 (by rfl) ⟨219722, by rfl⟩ : syracuseStep 1171853 = 439445) B439445
theorem B876977 : Blo 307833 876977 := bstep (se 2 (by rfl) ⟨328866, by rfl⟩ : syracuseStep 876977 = 657733) B657733
theorem B1040849 : Blo 307833 1040849 := bstep (se 2 (by rfl) ⟨390318, by rfl⟩ : syracuseStep 1040849 = 780637) B780637
theorem B877169 : Blo 307833 877169 := bstep (se 2 (by rfl) ⟨328938, by rfl⟩ : syracuseStep 877169 = 657877) B657877
theorem B418627 : Blo 307833 418627 := bstep (se 1 (by rfl) ⟨313970, by rfl⟩ : syracuseStep 418627 = 627941) B627941
theorem B746417 : Blo 307833 746417 := bstep (se 2 (by rfl) ⟨279906, by rfl⟩ : syracuseStep 746417 = 559813) B559813
theorem B3335093 : Blo 307833 3335093 := bstep (se 5 (by rfl) ⟨156332, by rfl⟩ : syracuseStep 3335093 = 312665) B312665
theorem B1041389 : Blo 307833 1041389 := bstep (se 3 (by rfl) ⟨195260, by rfl⟩ : syracuseStep 1041389 = 390521) B390521
theorem B1041443 : Blo 307833 1041443 := bstep (se 1 (by rfl) ⟨781082, by rfl⟩ : syracuseStep 1041443 = 1562165) B1562165
theorem B353363 : Blo 307833 353363 := bstep (se 1 (by rfl) ⟨265022, by rfl⟩ : syracuseStep 353363 = 530045) B530045
theorem B1172657 : Blo 307833 1172657 := bstep (se 2 (by rfl) ⟨439746, by rfl⟩ : syracuseStep 1172657 = 879493) B879493
theorem B1041713 : Blo 307833 1041713 := bstep (se 2 (by rfl) ⟨390642, by rfl⟩ : syracuseStep 1041713 = 781285) B781285
theorem B779665 : Blo 307833 779665 := bstep (se 2 (by rfl) ⟨292374, by rfl⟩ : syracuseStep 779665 = 584749) B584749
theorem B878161 : Blo 307833 878161 := bstep (se 2 (by rfl) ⟨329310, by rfl⟩ : syracuseStep 878161 = 658621) B658621
theorem B3991139 : Blo 307833 3991139 := bstep (se 1 (by rfl) ⟨2993354, by rfl⟩ : syracuseStep 3991139 = 5986709) B5986709
theorem B779939 : Blo 307833 779939 := bstep (se 1 (by rfl) ⟨584954, by rfl⟩ : syracuseStep 779939 = 1169909) B1169909
theorem B1042253 : Blo 307833 1042253 := bstep (se 3 (by rfl) ⟨195422, by rfl⟩ : syracuseStep 1042253 = 390845) B390845
theorem B1173325 : Blo 307833 1173325 := bstep (se 3 (by rfl) ⟨219998, by rfl⟩ : syracuseStep 1173325 = 439997) B439997
theorem B419665 : Blo 307833 419665 := bstep (se 2 (by rfl) ⟨157374, by rfl⟩ : syracuseStep 419665 = 314749) B314749
theorem B780131 : Blo 307833 780131 := bstep (se 1 (by rfl) ⟨585098, by rfl⟩ : syracuseStep 780131 = 1170197) B1170197
theorem B878435 : Blo 307833 878435 := bstep (se 1 (by rfl) ⟨658826, by rfl⟩ : syracuseStep 878435 = 1317653) B1317653
theorem B1042307 : Blo 307833 1042307 := bstep (se 1 (by rfl) ⟨781730, by rfl⟩ : syracuseStep 1042307 = 1563461) B1563461
theorem B944003 : Blo 307833 944003 := bstep (se 1 (by rfl) ⟨708002, by rfl⟩ : syracuseStep 944003 = 1416005) B1416005
theorem B845741 : Blo 307833 845741 := bstep (se 3 (by rfl) ⟨158576, by rfl⟩ : syracuseStep 845741 = 317153) B317153
theorem B878627 : Blo 307833 878627 := bstep (se 1 (by rfl) ⟨658970, by rfl⟩ : syracuseStep 878627 = 1317941) B1317941
theorem B1042577 : Blo 307833 1042577 := bstep (se 2 (by rfl) ⟨390966, by rfl⟩ : syracuseStep 1042577 = 781933) B781933
theorem B1567025 : Blo 307833 1567025 := bstep (se 2 (by rfl) ⟨587634, by rfl⟩ : syracuseStep 1567025 = 1175269) B1175269
theorem B1763633 : Blo 307833 1763633 := bstep (se 2 (by rfl) ⟨661362, by rfl⟩ : syracuseStep 1763633 = 1322725) B1322725
theorem B1174115 : Blo 307833 1174115 := bstep (se 1 (by rfl) ⟨880586, by rfl⟩ : syracuseStep 1174115 = 1761173) B1761173
theorem B846445 : Blo 307833 846445 := bstep (se 3 (by rfl) ⟨158708, by rfl⟩ : syracuseStep 846445 = 317417) B317417
theorem B1043117 : Blo 307833 1043117 := bstep (se 3 (by rfl) ⟨195584, by rfl⟩ : syracuseStep 1043117 = 391169) B391169
theorem B1043171 : Blo 307833 1043171 := bstep (se 1 (by rfl) ⟨782378, by rfl⟩ : syracuseStep 1043171 = 1564757) B1564757
theorem B781073 : Blo 307833 781073 := bstep (se 2 (by rfl) ⟨292902, by rfl⟩ : syracuseStep 781073 = 585805) B585805
theorem B781123 : Blo 307833 781123 := bstep (se 1 (by rfl) ⟨585842, by rfl⟩ : syracuseStep 781123 = 1171685) B1171685
theorem B879437 : Blo 307833 879437 := bstep (se 3 (by rfl) ⟨164894, by rfl⟩ : syracuseStep 879437 = 329789) B329789
theorem B781265 : Blo 307833 781265 := bstep (se 2 (by rfl) ⟨292974, by rfl⟩ : syracuseStep 781265 = 585949) B585949
theorem B1043441 : Blo 307833 1043441 := bstep (se 2 (by rfl) ⟨391290, by rfl⟩ : syracuseStep 1043441 = 782581) B782581
theorem B879619 : Blo 307833 879619 := bstep (se 1 (by rfl) ⟨659714, by rfl⟩ : syracuseStep 879619 = 1319429) B1319429
theorem B5270669 : Blo 307833 5270669 := bstep (se 3 (by rfl) ⟨988250, by rfl⟩ : syracuseStep 5270669 = 1976501) B1976501
theorem B1666289 : Blo 307833 1666289 := bstep (se 2 (by rfl) ⟨624858, by rfl⟩ : syracuseStep 1666289 = 1249717) B1249717
theorem B1174769 : Blo 307833 1174769 := bstep (se 2 (by rfl) ⟨440538, by rfl⟩ : syracuseStep 1174769 = 881077) B881077
theorem B584977 : Blo 307833 584977 := bstep (se 2 (by rfl) ⟨219366, by rfl⟩ : syracuseStep 584977 = 438733) B438733
theorem B519473 : Blo 307833 519473 := bstep (se 2 (by rfl) ⟨194802, by rfl⟩ : syracuseStep 519473 = 389605) B389605
theorem B519601 : Blo 307833 519601 := bstep (se 2 (by rfl) ⟨194850, by rfl⟩ : syracuseStep 519601 = 389701) B389701
theorem B585137 : Blo 307833 585137 := bstep (se 2 (by rfl) ⟨219426, by rfl⟩ : syracuseStep 585137 = 438853) B438853
theorem B519635 : Blo 307833 519635 := bstep (se 1 (by rfl) ⟨389726, by rfl⟩ : syracuseStep 519635 = 779453) B779453
theorem B880109 : Blo 307833 880109 := bstep (se 3 (by rfl) ⟨165020, by rfl⟩ : syracuseStep 880109 = 330041) B330041
theorem B1043981 : Blo 307833 1043981 := bstep (se 3 (by rfl) ⟨195746, by rfl⟩ : syracuseStep 1043981 = 391493) B391493
theorem B1044035 : Blo 307833 1044035 := bstep (se 1 (by rfl) ⟨783026, by rfl⟩ : syracuseStep 1044035 = 1566053) B1566053
theorem B519763 : Blo 307833 519763 := bstep (se 1 (by rfl) ⟨389822, by rfl⟩ : syracuseStep 519763 = 779645) B779645
theorem B519905 : Blo 307833 519905 := bstep (se 2 (by rfl) ⟨194964, by rfl⟩ : syracuseStep 519905 = 389929) B389929
theorem B1568483 : Blo 307833 1568483 := bstep (se 1 (by rfl) ⟨1176362, by rfl⟩ : syracuseStep 1568483 = 2352725) B2352725
theorem B1765091 : Blo 307833 1765091 := bstep (se 1 (by rfl) ⟨1323818, by rfl⟩ : syracuseStep 1765091 = 2647637) B2647637
theorem B585539 : Blo 307833 585539 := bstep (se 1 (by rfl) ⟨439154, by rfl⟩ : syracuseStep 585539 = 878309) B878309
theorem B1044305 : Blo 307833 1044305 := bstep (se 2 (by rfl) ⟨391614, by rfl⟩ : syracuseStep 1044305 = 783229) B783229
theorem B520033 : Blo 307833 520033 := bstep (se 2 (by rfl) ⟨195012, by rfl⟩ : syracuseStep 520033 = 390025) B390025
theorem B520067 : Blo 307833 520067 := bstep (se 1 (by rfl) ⟨390050, by rfl⟩ : syracuseStep 520067 = 780101) B780101
theorem B782257 : Blo 307833 782257 := bstep (se 2 (by rfl) ⟨293346, by rfl⟩ : syracuseStep 782257 = 586693) B586693
theorem B2650097 : Blo 307833 2650097 := bstep (se 2 (by rfl) ⟨993786, by rfl⟩ : syracuseStep 2650097 = 1987573) B1987573
theorem B520195 : Blo 307833 520195 := bstep (se 1 (by rfl) ⟨390146, by rfl⟩ : syracuseStep 520195 = 780293) B780293
theorem B520337 : Blo 307833 520337 := bstep (se 2 (by rfl) ⟨195126, by rfl⟩ : syracuseStep 520337 = 390253) B390253
theorem B782531 : Blo 307833 782531 := bstep (se 1 (by rfl) ⟨586898, by rfl⟩ : syracuseStep 782531 = 1173797) B1173797
theorem B520465 : Blo 307833 520465 := bstep (se 2 (by rfl) ⟨195174, by rfl⟩ : syracuseStep 520465 = 390349) B390349
theorem B520499 : Blo 307833 520499 := bstep (se 1 (by rfl) ⟨390374, by rfl⟩ : syracuseStep 520499 = 780749) B780749
theorem B1044845 : Blo 307833 1044845 := bstep (se 3 (by rfl) ⟨195908, by rfl⟩ : syracuseStep 1044845 = 391817) B391817
theorem B782723 : Blo 307833 782723 := bstep (se 1 (by rfl) ⟨587042, by rfl⟩ : syracuseStep 782723 = 1174085) B1174085
theorem B1044899 : Blo 307833 1044899 := bstep (se 1 (by rfl) ⟨783674, by rfl⟩ : syracuseStep 1044899 = 1567349) B1567349
theorem B520627 : Blo 307833 520627 := bstep (se 1 (by rfl) ⟨390470, by rfl⟩ : syracuseStep 520627 = 780941) B780941
theorem B1569293 : Blo 307833 1569293 := bstep (se 3 (by rfl) ⟨294242, by rfl⟩ : syracuseStep 1569293 = 588485) B588485
theorem B520769 : Blo 307833 520769 := bstep (se 2 (by rfl) ⟨195288, by rfl⟩ : syracuseStep 520769 = 390577) B390577
theorem B881293 : Blo 307833 881293 := bstep (se 3 (by rfl) ⟨165242, by rfl⟩ : syracuseStep 881293 = 330485) B330485
theorem B1176227 : Blo 307833 1176227 := bstep (se 1 (by rfl) ⟨882170, by rfl⟩ : syracuseStep 1176227 = 1764341) B1764341
theorem B1045169 : Blo 307833 1045169 := bstep (se 2 (by rfl) ⟨391938, by rfl⟩ : syracuseStep 1045169 = 783877) B783877
theorem B1176241 : Blo 307833 1176241 := bstep (se 2 (by rfl) ⟨441090, by rfl⟩ : syracuseStep 1176241 = 882181) B882181
theorem B520897 : Blo 307833 520897 := bstep (se 2 (by rfl) ⟨195336, by rfl⟩ : syracuseStep 520897 = 390673) B390673
theorem B586435 : Blo 307833 586435 := bstep (se 1 (by rfl) ⟨439826, by rfl⟩ : syracuseStep 586435 = 879653) B879653
theorem B520931 : Blo 307833 520931 := bstep (se 1 (by rfl) ⟨390698, by rfl⟩ : syracuseStep 520931 = 781397) B781397
theorem B5206837 : Blo 307833 5206837 := bstep (se 5 (by rfl) ⟨244070, by rfl⟩ : syracuseStep 5206837 = 488141) B488141
theorem B521059 : Blo 307833 521059 := bstep (se 1 (by rfl) ⟨390794, by rfl⟩ : syracuseStep 521059 = 781589) B781589
theorem B586595 : Blo 307833 586595 := bstep (se 1 (by rfl) ⟨439946, by rfl⟩ : syracuseStep 586595 = 879893) B879893
theorem B390035 : Blo 307833 390035 := bstep (se 1 (by rfl) ⟨292526, by rfl⟩ : syracuseStep 390035 = 585053) B585053
theorem B521201 : Blo 307833 521201 := bstep (se 2 (by rfl) ⟨195450, by rfl⟩ : syracuseStep 521201 = 390901) B390901
theorem B521329 : Blo 307833 521329 := bstep (se 2 (by rfl) ⟨195498, by rfl⟩ : syracuseStep 521329 = 390997) B390997
theorem B1537165 : Blo 307833 1537165 := bstep (se 3 (by rfl) ⟨288218, by rfl⟩ : syracuseStep 1537165 = 576437) B576437
theorem B521363 : Blo 307833 521363 := bstep (se 1 (by rfl) ⟨391022, by rfl⟩ : syracuseStep 521363 = 782045) B782045
theorem B1045709 : Blo 307833 1045709 := bstep (se 3 (by rfl) ⟨196070, by rfl⟩ : syracuseStep 1045709 = 392141) B392141
theorem B1045763 : Blo 307833 1045763 := bstep (se 1 (by rfl) ⟨784322, by rfl⟩ : syracuseStep 1045763 = 1568645) B1568645
theorem B521491 : Blo 307833 521491 := bstep (se 1 (by rfl) ⟨391118, by rfl⟩ : syracuseStep 521491 = 782237) B782237
theorem B783665 : Blo 307833 783665 := bstep (se 2 (by rfl) ⟨293874, by rfl⟩ : syracuseStep 783665 = 587749) B587749
theorem B783715 : Blo 307833 783715 := bstep (se 1 (by rfl) ⟨587786, by rfl⟩ : syracuseStep 783715 = 1175573) B1175573
theorem B521633 : Blo 307833 521633 := bstep (se 2 (by rfl) ⟨195612, by rfl⟩ : syracuseStep 521633 = 391225) B391225
theorem B947629 : Blo 307833 947629 := bstep (se 3 (by rfl) ⟨177680, by rfl⟩ : syracuseStep 947629 = 355361) B355361
theorem B783857 : Blo 307833 783857 := bstep (se 2 (by rfl) ⟨293946, by rfl⟩ : syracuseStep 783857 = 587893) B587893
theorem B1046033 : Blo 307833 1046033 := bstep (se 2 (by rfl) ⟨392262, by rfl⟩ : syracuseStep 1046033 = 784525) B784525
theorem B521761 : Blo 307833 521761 := bstep (se 2 (by rfl) ⟨195660, by rfl⟩ : syracuseStep 521761 = 391321) B391321
theorem B521795 : Blo 307833 521795 := bstep (se 1 (by rfl) ⟨391346, by rfl⟩ : syracuseStep 521795 = 782693) B782693
theorem B390739 : Blo 307833 390739 := bstep (se 1 (by rfl) ⟨293054, by rfl⟩ : syracuseStep 390739 = 586109) B586109
theorem B882353 : Blo 307833 882353 := bstep (se 2 (by rfl) ⟨330882, by rfl⟩ : syracuseStep 882353 = 661765) B661765
theorem B390835 : Blo 307833 390835 := bstep (se 1 (by rfl) ⟨293126, by rfl⟩ : syracuseStep 390835 = 586253) B586253
theorem B521923 : Blo 307833 521923 := bstep (se 1 (by rfl) ⟨391442, by rfl⟩ : syracuseStep 521923 = 782885) B782885
theorem B849709 : Blo 307833 849709 := bstep (se 3 (by rfl) ⟨159320, by rfl⟩ : syracuseStep 849709 = 318641) B318641
theorem B522065 : Blo 307833 522065 := bstep (se 2 (by rfl) ⟨195774, by rfl⟩ : syracuseStep 522065 = 391549) B391549
theorem B849773 : Blo 307833 849773 := bstep (se 3 (by rfl) ⟨159332, by rfl⟩ : syracuseStep 849773 = 318665) B318665
theorem B587665 : Blo 307833 587665 := bstep (se 2 (by rfl) ⟨220374, by rfl⟩ : syracuseStep 587665 = 440749) B440749
theorem B522193 : Blo 307833 522193 := bstep (se 2 (by rfl) ⟨195822, by rfl⟩ : syracuseStep 522193 = 391645) B391645
theorem B522227 : Blo 307833 522227 := bstep (se 1 (by rfl) ⟨391670, by rfl⟩ : syracuseStep 522227 = 783341) B783341
theorem B1046573 : Blo 307833 1046573 := bstep (se 3 (by rfl) ⟨196232, by rfl⟩ : syracuseStep 1046573 = 392465) B392465
theorem B1046627 : Blo 307833 1046627 := bstep (se 1 (by rfl) ⟨784970, by rfl⟩ : syracuseStep 1046627 = 1569941) B1569941
theorem B1177699 : Blo 307833 1177699 := bstep (se 1 (by rfl) ⟨883274, by rfl⟩ : syracuseStep 1177699 = 1766549) B1766549
theorem B522355 : Blo 307833 522355 := bstep (se 1 (by rfl) ⟨391766, by rfl⟩ : syracuseStep 522355 = 783533) B783533
theorem B391331 : Blo 307833 391331 := bstep (se 1 (by rfl) ⟨293498, by rfl⟩ : syracuseStep 391331 = 586997) B586997
theorem B522497 : Blo 307833 522497 := bstep (se 2 (by rfl) ⟨195936, by rfl⟩ : syracuseStep 522497 = 391873) B391873
theorem B883025 : Blo 307833 883025 := bstep (se 2 (by rfl) ⟨331134, by rfl⟩ : syracuseStep 883025 = 662269) B662269
theorem B1046897 : Blo 307833 1046897 := bstep (se 2 (by rfl) ⟨392586, by rfl⟩ : syracuseStep 1046897 = 785173) B785173
theorem B522625 : Blo 307833 522625 := bstep (se 2 (by rfl) ⟨195984, by rfl⟩ : syracuseStep 522625 = 391969) B391969
theorem B522659 : Blo 307833 522659 := bstep (se 1 (by rfl) ⟨391994, by rfl⟩ : syracuseStep 522659 = 783989) B783989
theorem B784849 : Blo 307833 784849 := bstep (se 2 (by rfl) ⟨294318, by rfl⟩ : syracuseStep 784849 = 588637) B588637
theorem B522787 : Blo 307833 522787 := bstep (se 1 (by rfl) ⟨392090, by rfl⟩ : syracuseStep 522787 = 784181) B784181
theorem B522929 : Blo 307833 522929 := bstep (se 2 (by rfl) ⟨196098, by rfl⟩ : syracuseStep 522929 = 392197) B392197
theorem B785123 : Blo 307833 785123 := bstep (se 1 (by rfl) ⟨588842, by rfl⟩ : syracuseStep 785123 = 1177685) B1177685
theorem B523057 : Blo 307833 523057 := bstep (se 2 (by rfl) ⟨196146, by rfl⟩ : syracuseStep 523057 = 392293) B392293
theorem B523091 : Blo 307833 523091 := bstep (se 1 (by rfl) ⟨392318, by rfl⟩ : syracuseStep 523091 = 784637) B784637
theorem B392035 : Blo 307833 392035 := bstep (se 1 (by rfl) ⟨294026, by rfl⟩ : syracuseStep 392035 = 588053) B588053
theorem B2227085 : Blo 307833 2227085 := bstep (se 3 (by rfl) ⟨417578, by rfl⟩ : syracuseStep 2227085 = 835157) B835157
theorem B1047437 : Blo 307833 1047437 := bstep (se 3 (by rfl) ⟨196394, by rfl⟩ : syracuseStep 1047437 = 392789) B392789
theorem B785315 : Blo 307833 785315 := bstep (se 1 (by rfl) ⟨588986, by rfl⟩ : syracuseStep 785315 = 1177973) B1177973
theorem B588721 : Blo 307833 588721 := bstep (se 2 (by rfl) ⟨220770, by rfl⟩ : syracuseStep 588721 = 441541) B441541
theorem B392131 : Blo 307833 392131 := bstep (se 1 (by rfl) ⟨294098, by rfl⟩ : syracuseStep 392131 = 588197) B588197
theorem B1047491 : Blo 307833 1047491 := bstep (se 1 (by rfl) ⟨785618, by rfl⟩ : syracuseStep 1047491 = 1571237) B1571237
theorem B523219 : Blo 307833 523219 := bstep (se 1 (by rfl) ⟨392414, by rfl⟩ : syracuseStep 523219 = 784829) B784829
theorem B523361 : Blo 307833 523361 := bstep (se 2 (by rfl) ⟨196260, by rfl⟩ : syracuseStep 523361 = 392521) B392521
theorem B883811 : Blo 307833 883811 := bstep (se 1 (by rfl) ⟨662858, by rfl⟩ : syracuseStep 883811 = 1325717) B1325717
theorem B1047761 : Blo 307833 1047761 := bstep (se 2 (by rfl) ⟨392910, by rfl⟩ : syracuseStep 1047761 = 785821) B785821
theorem B523489 : Blo 307833 523489 := bstep (se 2 (by rfl) ⟨196308, by rfl⟩ : syracuseStep 523489 = 392617) B392617
theorem B523523 : Blo 307833 523523 := bstep (se 1 (by rfl) ⟨392642, by rfl⟩ : syracuseStep 523523 = 785285) B785285
theorem B589123 : Blo 307833 589123 := bstep (se 1 (by rfl) ⟨441842, by rfl⟩ : syracuseStep 589123 = 883685) B883685
theorem B589169 : Blo 307833 589169 := bstep (se 2 (by rfl) ⟨220938, by rfl⟩ : syracuseStep 589169 = 441877) B441877
theorem B1572209 : Blo 307833 1572209 := bstep (se 2 (by rfl) ⟨589578, by rfl⟩ : syracuseStep 1572209 = 1179157) B1179157
theorem B523651 : Blo 307833 523651 := bstep (se 1 (by rfl) ⟨392738, by rfl⟩ : syracuseStep 523651 = 785477) B785477
theorem B884141 : Blo 307833 884141 := bstep (se 3 (by rfl) ⟨165776, by rfl⟩ : syracuseStep 884141 = 331553) B331553
theorem B392627 : Blo 307833 392627 := bstep (se 1 (by rfl) ⟨294470, by rfl⟩ : syracuseStep 392627 = 588941) B588941
theorem B884209 : Blo 307833 884209 := bstep (se 2 (by rfl) ⟨331578, by rfl⟩ : syracuseStep 884209 = 663157) B663157
theorem B523793 : Blo 307833 523793 := bstep (se 2 (by rfl) ⟨196422, by rfl⟩ : syracuseStep 523793 = 392845) B392845
theorem B523921 : Blo 307833 523921 := bstep (se 2 (by rfl) ⟨196470, by rfl⟩ : syracuseStep 523921 = 392941) B392941
theorem B589457 : Blo 307833 589457 := bstep (se 2 (by rfl) ⟨221046, by rfl⟩ : syracuseStep 589457 = 442093) B442093
theorem B523955 : Blo 307833 523955 := bstep (se 1 (by rfl) ⟨392966, by rfl⟩ : syracuseStep 523955 = 785933) B785933
theorem B1048301 : Blo 307833 1048301 := bstep (se 3 (by rfl) ⟨196556, by rfl⟩ : syracuseStep 1048301 = 393113) B393113
theorem B884483 : Blo 307833 884483 := bstep (se 1 (by rfl) ⟨663362, by rfl⟩ : syracuseStep 884483 = 1326725) B1326725
theorem B1048355 : Blo 307833 1048355 := bstep (se 1 (by rfl) ⟨786266, by rfl⟩ : syracuseStep 1048355 = 1572533) B1572533
theorem B524083 : Blo 307833 524083 := bstep (se 1 (by rfl) ⟨393062, by rfl⟩ : syracuseStep 524083 = 786125) B786125
theorem B786257 : Blo 307833 786257 := bstep (se 2 (by rfl) ⟨294846, by rfl⟩ : syracuseStep 786257 = 589693) B589693
theorem B3604337 : Blo 307833 3604337 := bstep (se 2 (by rfl) ⟨1351626, by rfl⟩ : syracuseStep 3604337 = 2703253) B2703253
theorem B786307 : Blo 307833 786307 := bstep (se 1 (by rfl) ⟨589730, by rfl⟩ : syracuseStep 786307 = 1179461) B1179461
theorem B1114033 : Blo 307833 1114033 := bstep (se 2 (by rfl) ⟨417762, by rfl⟩ : syracuseStep 1114033 = 835525) B835525
theorem B524225 : Blo 307833 524225 := bstep (se 2 (by rfl) ⟨196584, by rfl⟩ : syracuseStep 524225 = 393169) B393169
theorem B524299 : Blo 307833 524299 := bstep (se 1 (by rfl) ⟨393224, by rfl⟩ : syracuseStep 524299 = 786449) B786449
theorem B589913 : Blo 307833 589913 := bstep (se 2 (by rfl) ⟨221217, by rfl⟩ : syracuseStep 589913 = 442435) B442435
theorem B524441 : Blo 307833 524441 := bstep (se 2 (by rfl) ⟨196665, by rfl⟩ : syracuseStep 524441 = 393331) B393331
theorem B884915 : Blo 307833 884915 := bstep (se 1 (by rfl) ⟨663686, by rfl⟩ : syracuseStep 884915 = 1327373) B1327373
theorem B786611 : Blo 307833 786611 := bstep (se 1 (by rfl) ⟨589958, by rfl⟩ : syracuseStep 786611 = 1179917) B1179917
theorem B524569 : Blo 307833 524569 := bstep (se 2 (by rfl) ⟨196713, by rfl⟩ : syracuseStep 524569 = 393427) B393427
theorem B557363 : Blo 307833 557363 := bstep (se 1 (by rfl) ⟨418022, by rfl⟩ : syracuseStep 557363 = 836045) B836045
theorem B885143 : Blo 307833 885143 := bstep (se 1 (by rfl) ⟨663857, by rfl⟩ : syracuseStep 885143 = 1327715) B1327715
theorem B786905 : Blo 307833 786905 := bstep (se 2 (by rfl) ⟨295089, by rfl⟩ : syracuseStep 786905 = 590179) B590179
theorem B590323 : Blo 307833 590323 := bstep (se 1 (by rfl) ⟨442742, by rfl⟩ : syracuseStep 590323 = 885485) B885485
theorem B557579 : Blo 307833 557579 := bstep (se 1 (by rfl) ⟨418184, by rfl⟩ : syracuseStep 557579 = 836369) B836369
theorem B1049111 : Blo 307833 1049111 := bstep (se 1 (by rfl) ⟨786833, by rfl⟩ : syracuseStep 1049111 = 1573667) B1573667
theorem B393751 : Blo 307833 393751 := bstep (se 1 (by rfl) ⟨295313, by rfl⟩ : syracuseStep 393751 = 590627) B590627
theorem B754265 : Blo 307833 754265 := bstep (se 2 (by rfl) ⟨282849, by rfl⟩ : syracuseStep 754265 = 565699) B565699
theorem B2851421 : Blo 307833 2851421 := bstep (se 3 (by rfl) ⟨534641, by rfl⟩ : syracuseStep 2851421 = 1069283) B1069283
theorem B885451 : Blo 307833 885451 := bstep (se 1 (by rfl) ⟨664088, by rfl⟩ : syracuseStep 885451 = 1328177) B1328177
theorem B1180433 : Blo 307833 1180433 := bstep (se 2 (by rfl) ⟨442662, by rfl⟩ : syracuseStep 1180433 = 885325) B885325
theorem B1672001 : Blo 307833 1672001 := bstep (se 2 (by rfl) ⟨627000, by rfl⟩ : syracuseStep 1672001 = 1254001) B1254001
theorem B1114955 : Blo 307833 1114955 := bstep (se 1 (by rfl) ⟨836216, by rfl⟩ : syracuseStep 1114955 = 1672433) B1672433
theorem B525143 : Blo 307833 525143 := bstep (se 1 (by rfl) ⟨393857, by rfl⟩ : syracuseStep 525143 = 787715) B787715
theorem B525271 : Blo 307833 525271 := bstep (se 1 (by rfl) ⟨393953, by rfl⟩ : syracuseStep 525271 = 787907) B787907
theorem B590809 : Blo 307833 590809 := bstep (se 2 (by rfl) ⟨221553, by rfl⟩ : syracuseStep 590809 = 443107) B443107
theorem B885725 : Blo 307833 885725 := bstep (se 3 (by rfl) ⟨166073, by rfl⟩ : syracuseStep 885725 = 332147) B332147
theorem B1049651 : Blo 307833 1049651 := bstep (se 1 (by rfl) ⟨787238, by rfl⟩ : syracuseStep 1049651 = 1574477) B1574477
theorem B1180889 : Blo 307833 1180889 := bstep (se 2 (by rfl) ⟨442833, by rfl⟩ : syracuseStep 1180889 = 885667) B885667
theorem B1049921 : Blo 307833 1049921 := bstep (se 2 (by rfl) ⟨393720, by rfl⟩ : syracuseStep 1049921 = 787441) B787441
theorem B394571 : Blo 307833 394571 := bstep (se 1 (by rfl) ⟨295928, by rfl⟩ : syracuseStep 394571 = 591857) B591857
theorem B1181101 : Blo 307833 1181101 := bstep (se 3 (by rfl) ⟨221456, by rfl⟩ : syracuseStep 1181101 = 442913) B442913
theorem B329195 : Blo 307833 329195 := bstep (se 1 (by rfl) ⟨246896, by rfl⟩ : syracuseStep 329195 = 493793) B493793
theorem B591371 : Blo 307833 591371 := bstep (se 1 (by rfl) ⟨443528, by rfl⟩ : syracuseStep 591371 = 887057) B887057
theorem B525899 : Blo 307833 525899 := bstep (se 1 (by rfl) ⟨394424, by rfl⟩ : syracuseStep 525899 = 788849) B788849
theorem B591553 : Blo 307833 591553 := bstep (se 2 (by rfl) ⟨221832, by rfl⟩ : syracuseStep 591553 = 443665) B443665
theorem B526027 : Blo 307833 526027 := bstep (se 1 (by rfl) ⟨394520, by rfl⟩ : syracuseStep 526027 = 789041) B789041
theorem B1181405 : Blo 307833 1181405 := bstep (se 3 (by rfl) ⟨221513, by rfl⟩ : syracuseStep 1181405 = 443027) B443027
theorem B526169 : Blo 307833 526169 := bstep (se 2 (by rfl) ⟨197313, by rfl⟩ : syracuseStep 526169 = 394627) B394627
theorem B1050461 : Blo 307833 1050461 := bstep (se 3 (by rfl) ⟨196961, by rfl⟩ : syracuseStep 1050461 = 393923) B393923
theorem B788555 : Blo 307833 788555 := bstep (se 1 (by rfl) ⟨591416, by rfl⟩ : syracuseStep 788555 = 1182833) B1182833
theorem B559553 : Blo 307833 559553 := bstep (se 2 (by rfl) ⟨209832, by rfl⟩ : syracuseStep 559553 = 419665) B419665
theorem B2657069 : Blo 307833 2657069 := bstep (se 3 (by rfl) ⟨498200, by rfl⟩ : syracuseStep 2657069 = 996401) B996401
theorem B1117003 : Blo 307833 1117003 := bstep (se 1 (by rfl) ⟨837752, by rfl⟩ : syracuseStep 1117003 = 1675505) B1675505
theorem B1772381 : Blo 307833 1772381 := bstep (se 3 (by rfl) ⟨332321, by rfl⟩ : syracuseStep 1772381 = 664643) B664643
theorem B1575773 : Blo 307833 1575773 := bstep (se 3 (by rfl) ⟨295457, by rfl⟩ : syracuseStep 1575773 = 590915) B590915
theorem B330647 : Blo 307833 330647 := bstep (se 1 (by rfl) ⟨247985, by rfl⟩ : syracuseStep 330647 = 495971) B495971
theorem B461771 : Blo 307833 461771 := bstep (se 1 (by rfl) ⟨346328, by rfl⟩ : syracuseStep 461771 = 692657) B692657
theorem B1051595 : Blo 307833 1051595 := bstep (se 1 (by rfl) ⟨788696, by rfl⟩ : syracuseStep 1051595 = 1577393) B1577393
theorem B461783 : Blo 307833 461783 := bstep (se 1 (by rfl) ⟨346337, by rfl⟩ : syracuseStep 461783 = 692675) B692675
theorem B887831 : Blo 307833 887831 := bstep (se 1 (by rfl) ⟨665873, by rfl⟩ : syracuseStep 887831 = 1331747) B1331747
theorem B461849 : Blo 307833 461849 := bstep (se 2 (by rfl) ⟨173193, by rfl⟩ : syracuseStep 461849 = 346387) B346387
theorem B461963 : Blo 307833 461963 := bstep (se 1 (by rfl) ⟨346472, by rfl⟩ : syracuseStep 461963 = 692945) B692945
theorem B461975 : Blo 307833 461975 := bstep (se 1 (by rfl) ⟨346481, by rfl⟩ : syracuseStep 461975 = 692963) B692963
theorem B462041 : Blo 307833 462041 := bstep (se 2 (by rfl) ⟨173265, by rfl⟩ : syracuseStep 462041 = 346531) B346531
theorem B1051865 : Blo 307833 1051865 := bstep (se 2 (by rfl) ⟨394449, by rfl⟩ : syracuseStep 1051865 = 788899) B788899
theorem B462155 : Blo 307833 462155 := bstep (se 1 (by rfl) ⟨346616, by rfl⟩ : syracuseStep 462155 = 693233) B693233
theorem B462167 : Blo 307833 462167 := bstep (se 1 (by rfl) ⟨346625, by rfl⟩ : syracuseStep 462167 = 693251) B693251
theorem B462233 : Blo 307833 462233 := bstep (se 2 (by rfl) ⟨173337, by rfl⟩ : syracuseStep 462233 = 346675) B346675
theorem B462347 : Blo 307833 462347 := bstep (se 1 (by rfl) ⟨346760, by rfl⟩ : syracuseStep 462347 = 693521) B693521
theorem B462359 : Blo 307833 462359 := bstep (se 1 (by rfl) ⟨346769, by rfl⟩ : syracuseStep 462359 = 693539) B693539
theorem B462425 : Blo 307833 462425 := bstep (se 2 (by rfl) ⟨173409, by rfl⟩ : syracuseStep 462425 = 346819) B346819
theorem B462539 : Blo 307833 462539 := bstep (se 1 (by rfl) ⟨346904, by rfl⟩ : syracuseStep 462539 = 693809) B693809
theorem B462551 : Blo 307833 462551 := bstep (se 1 (by rfl) ⟨346913, by rfl⟩ : syracuseStep 462551 = 693827) B693827
theorem B462617 : Blo 307833 462617 := bstep (se 2 (by rfl) ⟨173481, by rfl⟩ : syracuseStep 462617 = 346963) B346963
theorem B10030949 : Blo 307833 10030949 := bstep (se 4 (by rfl) ⟨940401, by rfl⟩ : syracuseStep 10030949 = 1880803) B1880803
theorem B462731 : Blo 307833 462731 := bstep (se 1 (by rfl) ⟨347048, by rfl⟩ : syracuseStep 462731 = 694097) B694097
theorem B462743 : Blo 307833 462743 := bstep (se 1 (by rfl) ⟨347057, by rfl⟩ : syracuseStep 462743 = 694115) B694115
theorem B462809 : Blo 307833 462809 := bstep (se 2 (by rfl) ⟨173553, by rfl⟩ : syracuseStep 462809 = 347107) B347107
theorem B1118231 : Blo 307833 1118231 := bstep (se 1 (by rfl) ⟨838673, by rfl⟩ : syracuseStep 1118231 = 1677347) B1677347
theorem B462923 : Blo 307833 462923 := bstep (se 1 (by rfl) ⟨347192, by rfl⟩ : syracuseStep 462923 = 694385) B694385
theorem B462935 : Blo 307833 462935 := bstep (se 1 (by rfl) ⟨347201, by rfl⟩ : syracuseStep 462935 = 694403) B694403
theorem B463001 : Blo 307833 463001 := bstep (se 2 (by rfl) ⟨173625, by rfl⟩ : syracuseStep 463001 = 347251) B347251
theorem B987329 : Blo 307833 987329 := bstep (se 2 (by rfl) ⟨370248, by rfl⟩ : syracuseStep 987329 = 740497) B740497
theorem B463115 : Blo 307833 463115 := bstep (se 1 (by rfl) ⟨347336, by rfl⟩ : syracuseStep 463115 = 694673) B694673
theorem B463127 : Blo 307833 463127 := bstep (se 1 (by rfl) ⟨347345, by rfl⟩ : syracuseStep 463127 = 694691) B694691
theorem B463193 : Blo 307833 463193 := bstep (se 2 (by rfl) ⟨173697, by rfl⟩ : syracuseStep 463193 = 347395) B347395
theorem B2232677 : Blo 307833 2232677 := bstep (se 4 (by rfl) ⟨209313, by rfl⟩ : syracuseStep 2232677 = 418627) B418627
theorem B463307 : Blo 307833 463307 := bstep (se 1 (by rfl) ⟨347480, by rfl⟩ : syracuseStep 463307 = 694961) B694961
theorem B463319 : Blo 307833 463319 := bstep (se 1 (by rfl) ⟨347489, by rfl⟩ : syracuseStep 463319 = 694979) B694979
theorem B692747 : Blo 307833 692747 := bstep (se 1 (by rfl) ⟨519560, by rfl⟩ : syracuseStep 692747 = 1039121) B1039121
theorem B463385 : Blo 307833 463385 := bstep (se 2 (by rfl) ⟨173769, by rfl⟩ : syracuseStep 463385 = 347539) B347539
theorem B1315379 : Blo 307833 1315379 := bstep (se 1 (by rfl) ⟨986534, by rfl⟩ : syracuseStep 1315379 = 1973069) B1973069
theorem B692801 : Blo 307833 692801 := bstep (se 2 (by rfl) ⟨259800, by rfl⟩ : syracuseStep 692801 = 519601) B519601
theorem B332407 : Blo 307833 332407 := bstep (se 1 (by rfl) ⟨249305, by rfl⟩ : syracuseStep 332407 = 498611) B498611
theorem B463499 : Blo 307833 463499 := bstep (se 1 (by rfl) ⟨347624, by rfl⟩ : syracuseStep 463499 = 695249) B695249
theorem B463511 : Blo 307833 463511 := bstep (se 1 (by rfl) ⟨347633, by rfl⟩ : syracuseStep 463511 = 695267) B695267
theorem B496343 : Blo 307833 496343 := bstep (se 1 (by rfl) ⟨372257, by rfl⟩ : syracuseStep 496343 = 744515) B744515
theorem B463577 : Blo 307833 463577 := bstep (se 2 (by rfl) ⟨173841, by rfl⟩ : syracuseStep 463577 = 347683) B347683
theorem B693017 : Blo 307833 693017 := bstep (se 2 (by rfl) ⟨259881, by rfl⟩ : syracuseStep 693017 = 519763) B519763
theorem B1250093 : Blo 307833 1250093 := bstep (se 3 (by rfl) ⟨234392, by rfl⟩ : syracuseStep 1250093 = 468785) B468785
theorem B463691 : Blo 307833 463691 := bstep (se 1 (by rfl) ⟨347768, by rfl⟩ : syracuseStep 463691 = 695537) B695537
theorem B463703 : Blo 307833 463703 := bstep (se 1 (by rfl) ⟨347777, by rfl⟩ : syracuseStep 463703 = 695555) B695555
theorem B693107 : Blo 307833 693107 := bstep (se 1 (by rfl) ⟨519830, by rfl⟩ : syracuseStep 693107 = 1039661) B1039661
theorem B693143 : Blo 307833 693143 := bstep (se 1 (by rfl) ⟨519857, by rfl⟩ : syracuseStep 693143 = 1039715) B1039715
theorem B1577879 : Blo 307833 1577879 := bstep (se 1 (by rfl) ⟨1183409, by rfl⟩ : syracuseStep 1577879 = 2366819) B2366819
theorem B463769 : Blo 307833 463769 := bstep (se 2 (by rfl) ⟨173913, by rfl⟩ : syracuseStep 463769 = 347827) B347827
theorem B2266061 : Blo 307833 2266061 := bstep (se 3 (by rfl) ⟨424886, by rfl⟩ : syracuseStep 2266061 = 849773) B849773
theorem B594931 : Blo 307833 594931 := bstep (se 1 (by rfl) ⟨446198, by rfl⟩ : syracuseStep 594931 = 892397) B892397
theorem B660467 : Blo 307833 660467 := bstep (se 1 (by rfl) ⟨495350, by rfl⟩ : syracuseStep 660467 = 990701) B990701
theorem B463883 : Blo 307833 463883 := bstep (se 1 (by rfl) ⟨347912, by rfl⟩ : syracuseStep 463883 = 695825) B695825
theorem B463895 : Blo 307833 463895 := bstep (se 1 (by rfl) ⟨347921, by rfl⟩ : syracuseStep 463895 = 695843) B695843
theorem B693323 : Blo 307833 693323 := bstep (se 1 (by rfl) ⟨519992, by rfl⟩ : syracuseStep 693323 = 1039985) B1039985
theorem B463961 : Blo 307833 463961 := bstep (se 2 (by rfl) ⟨173985, by rfl⟩ : syracuseStep 463961 = 347971) B347971
theorem B693377 : Blo 307833 693377 := bstep (se 2 (by rfl) ⟨260016, by rfl⟩ : syracuseStep 693377 = 520033) B520033
theorem B464075 : Blo 307833 464075 := bstep (se 1 (by rfl) ⟨348056, by rfl⟩ : syracuseStep 464075 = 696113) B696113
theorem B464087 : Blo 307833 464087 := bstep (se 1 (by rfl) ⟨348065, by rfl⟩ : syracuseStep 464087 = 696131) B696131
theorem B464153 : Blo 307833 464153 := bstep (se 2 (by rfl) ⟨174057, by rfl⟩ : syracuseStep 464153 = 348115) B348115
theorem B1119539 : Blo 307833 1119539 := bstep (se 1 (by rfl) ⟨839654, by rfl⟩ : syracuseStep 1119539 = 1679309) B1679309
theorem B693593 : Blo 307833 693593 := bstep (se 2 (by rfl) ⟨260097, by rfl⟩ : syracuseStep 693593 = 520195) B520195
theorem B1774979 : Blo 307833 1774979 := bstep (se 1 (by rfl) ⟨1331234, by rfl⟩ : syracuseStep 1774979 = 2662469) B2662469
theorem B464267 : Blo 307833 464267 := bstep (se 1 (by rfl) ⟨348200, by rfl⟩ : syracuseStep 464267 = 696401) B696401
theorem B464279 : Blo 307833 464279 := bstep (se 1 (by rfl) ⟨348209, by rfl⟩ : syracuseStep 464279 = 696419) B696419
theorem B693683 : Blo 307833 693683 := bstep (se 1 (by rfl) ⟨520262, by rfl⟩ : syracuseStep 693683 = 1040525) B1040525
theorem B497099 : Blo 307833 497099 := bstep (se 1 (by rfl) ⟨372824, by rfl⟩ : syracuseStep 497099 = 745649) B745649
theorem B693719 : Blo 307833 693719 := bstep (se 1 (by rfl) ⟨520289, by rfl⟩ : syracuseStep 693719 = 1040579) B1040579
theorem B660953 : Blo 307833 660953 := bstep (se 2 (by rfl) ⟨247857, by rfl⟩ : syracuseStep 660953 = 495715) B495715
theorem B464345 : Blo 307833 464345 := bstep (se 2 (by rfl) ⟨174129, by rfl⟩ : syracuseStep 464345 = 348259) B348259
theorem B464459 : Blo 307833 464459 := bstep (se 1 (by rfl) ⟨348344, by rfl⟩ : syracuseStep 464459 = 696689) B696689
theorem B464471 : Blo 307833 464471 := bstep (se 1 (by rfl) ⟨348353, by rfl⟩ : syracuseStep 464471 = 696707) B696707
theorem B693899 : Blo 307833 693899 := bstep (se 1 (by rfl) ⟨520424, by rfl⟩ : syracuseStep 693899 = 1040849) B1040849
theorem B464537 : Blo 307833 464537 := bstep (se 2 (by rfl) ⟨174201, by rfl⟩ : syracuseStep 464537 = 348403) B348403
theorem B693953 : Blo 307833 693953 := bstep (se 2 (by rfl) ⟨260232, by rfl⟩ : syracuseStep 693953 = 520465) B520465
theorem B464651 : Blo 307833 464651 := bstep (se 1 (by rfl) ⟨348488, by rfl⟩ : syracuseStep 464651 = 696977) B696977
theorem B464663 : Blo 307833 464663 := bstep (se 1 (by rfl) ⟨348497, by rfl⟩ : syracuseStep 464663 = 696995) B696995
theorem B464729 : Blo 307833 464729 := bstep (se 2 (by rfl) ⟨174273, by rfl⟩ : syracuseStep 464729 = 348547) B348547
theorem B694169 : Blo 307833 694169 := bstep (se 2 (by rfl) ⟨260313, by rfl⟩ : syracuseStep 694169 = 520627) B520627
theorem B2365361 : Blo 307833 2365361 := bstep (se 2 (by rfl) ⟨887010, by rfl⟩ : syracuseStep 2365361 = 1774021) B1774021
theorem B464843 : Blo 307833 464843 := bstep (se 1 (by rfl) ⟨348632, by rfl⟩ : syracuseStep 464843 = 697265) B697265
theorem B497611 : Blo 307833 497611 := bstep (se 1 (by rfl) ⟨373208, by rfl⟩ : syracuseStep 497611 = 746417) B746417
theorem B464855 : Blo 307833 464855 := bstep (se 1 (by rfl) ⟨348641, by rfl⟩ : syracuseStep 464855 = 697283) B697283
theorem B694259 : Blo 307833 694259 := bstep (se 1 (by rfl) ⟨520694, by rfl⟩ : syracuseStep 694259 = 1041389) B1041389
theorem B694295 : Blo 307833 694295 := bstep (se 1 (by rfl) ⟨520721, by rfl⟩ : syracuseStep 694295 = 1041443) B1041443
theorem B464921 : Blo 307833 464921 := bstep (se 2 (by rfl) ⟨174345, by rfl⟩ : syracuseStep 464921 = 348691) B348691
theorem B8198213 : Blo 307833 8198213 := bstep (se 4 (by rfl) ⟨768582, by rfl⟩ : syracuseStep 8198213 = 1537165) B1537165
theorem B465035 : Blo 307833 465035 := bstep (se 1 (by rfl) ⟨348776, by rfl⟩ : syracuseStep 465035 = 697553) B697553
theorem B465047 : Blo 307833 465047 := bstep (se 1 (by rfl) ⟨348785, by rfl⟩ : syracuseStep 465047 = 697571) B697571
theorem B694475 : Blo 307833 694475 := bstep (se 1 (by rfl) ⟨520856, by rfl⟩ : syracuseStep 694475 = 1041713) B1041713
theorem B465113 : Blo 307833 465113 := bstep (se 2 (by rfl) ⟨174417, by rfl⟩ : syracuseStep 465113 = 348835) B348835
theorem B989405 : Blo 307833 989405 := bstep (se 3 (by rfl) ⟨185513, by rfl⟩ : syracuseStep 989405 = 371027) B371027
theorem B694529 : Blo 307833 694529 := bstep (se 2 (by rfl) ⟨260448, by rfl⟩ : syracuseStep 694529 = 520897) B520897
theorem B465227 : Blo 307833 465227 := bstep (se 1 (by rfl) ⟨348920, by rfl⟩ : syracuseStep 465227 = 697841) B697841
theorem B465239 : Blo 307833 465239 := bstep (se 1 (by rfl) ⟨348929, by rfl⟩ : syracuseStep 465239 = 697859) B697859
theorem B1120663 : Blo 307833 1120663 := bstep (se 1 (by rfl) ⟨840497, by rfl⟩ : syracuseStep 1120663 = 1680995) B1680995
theorem B2660759 : Blo 307833 2660759 := bstep (se 1 (by rfl) ⟨1995569, by rfl⟩ : syracuseStep 2660759 = 3991139) B3991139
theorem B465305 : Blo 307833 465305 := bstep (se 2 (by rfl) ⟨174489, by rfl⟩ : syracuseStep 465305 = 348979) B348979
theorem B2365847 : Blo 307833 2365847 := bstep (se 1 (by rfl) ⟨1774385, by rfl⟩ : syracuseStep 2365847 = 3548771) B3548771
theorem B1317293 : Blo 307833 1317293 := bstep (se 3 (by rfl) ⟨246992, by rfl⟩ : syracuseStep 1317293 = 493985) B493985
theorem B694745 : Blo 307833 694745 := bstep (se 2 (by rfl) ⟨260529, by rfl⟩ : syracuseStep 694745 = 521059) B521059
theorem B465419 : Blo 307833 465419 := bstep (se 1 (by rfl) ⟨349064, by rfl⟩ : syracuseStep 465419 = 698129) B698129
theorem B465431 : Blo 307833 465431 := bstep (se 1 (by rfl) ⟨349073, by rfl⟩ : syracuseStep 465431 = 698147) B698147
theorem B694835 : Blo 307833 694835 := bstep (se 1 (by rfl) ⟨521126, by rfl⟩ : syracuseStep 694835 = 1042253) B1042253
theorem B596531 : Blo 307833 596531 := bstep (se 1 (by rfl) ⟨447398, by rfl⟩ : syracuseStep 596531 = 894797) B894797
theorem B1972811 : Blo 307833 1972811 := bstep (se 1 (by rfl) ⟨1479608, by rfl⟩ : syracuseStep 1972811 = 2959217) B2959217
theorem B629335 : Blo 307833 629335 := bstep (se 1 (by rfl) ⟨472001, by rfl⟩ : syracuseStep 629335 = 944003) B944003
theorem B694871 : Blo 307833 694871 := bstep (se 1 (by rfl) ⟨521153, by rfl⟩ : syracuseStep 694871 = 1042307) B1042307
theorem B465497 : Blo 307833 465497 := bstep (se 2 (by rfl) ⟨174561, by rfl⟩ : syracuseStep 465497 = 349123) B349123
theorem B1677925 : Blo 307833 1677925 := bstep (se 4 (by rfl) ⟨157305, by rfl⟩ : syracuseStep 1677925 = 314611) B314611
theorem B563827 : Blo 307833 563827 := bstep (se 1 (by rfl) ⟨422870, by rfl⟩ : syracuseStep 563827 = 845741) B845741
theorem B498329 : Blo 307833 498329 := bstep (se 2 (by rfl) ⟨186873, by rfl⟩ : syracuseStep 498329 = 373747) B373747
theorem B465611 : Blo 307833 465611 := bstep (se 1 (by rfl) ⟨349208, by rfl⟩ : syracuseStep 465611 = 698417) B698417
theorem B465623 : Blo 307833 465623 := bstep (se 1 (by rfl) ⟨349217, by rfl⟩ : syracuseStep 465623 = 698435) B698435
theorem B695051 : Blo 307833 695051 := bstep (se 1 (by rfl) ⟨521288, by rfl⟩ : syracuseStep 695051 = 1042577) B1042577
theorem B465689 : Blo 307833 465689 := bstep (se 2 (by rfl) ⟨174633, by rfl⟩ : syracuseStep 465689 = 349267) B349267
theorem B695105 : Blo 307833 695105 := bstep (se 2 (by rfl) ⟨260664, by rfl⟩ : syracuseStep 695105 = 521329) B521329
theorem B465803 : Blo 307833 465803 := bstep (se 1 (by rfl) ⟨349352, by rfl⟩ : syracuseStep 465803 = 698705) B698705
theorem B465815 : Blo 307833 465815 := bstep (se 1 (by rfl) ⟨349361, by rfl⟩ : syracuseStep 465815 = 698723) B698723
theorem B1252313 : Blo 307833 1252313 := bstep (se 2 (by rfl) ⟨469617, by rfl⟩ : syracuseStep 1252313 = 939235) B939235
theorem B465881 : Blo 307833 465881 := bstep (se 2 (by rfl) ⟨174705, by rfl⟩ : syracuseStep 465881 = 349411) B349411
theorem B695321 : Blo 307833 695321 := bstep (se 2 (by rfl) ⟨260745, by rfl⟩ : syracuseStep 695321 = 521491) B521491
theorem B662593 : Blo 307833 662593 := bstep (se 2 (by rfl) ⟨248472, by rfl⟩ : syracuseStep 662593 = 496945) B496945
theorem B465995 : Blo 307833 465995 := bstep (se 1 (by rfl) ⟨349496, by rfl⟩ : syracuseStep 465995 = 698993) B698993
theorem B466007 : Blo 307833 466007 := bstep (se 1 (by rfl) ⟨349505, by rfl⟩ : syracuseStep 466007 = 699011) B699011
theorem B1317977 : Blo 307833 1317977 := bstep (se 2 (by rfl) ⟨494241, by rfl⟩ : syracuseStep 1317977 = 988483) B988483
theorem B629849 : Blo 307833 629849 := bstep (se 2 (by rfl) ⟨236193, by rfl⟩ : syracuseStep 629849 = 472387) B472387
theorem B990301 : Blo 307833 990301 := bstep (se 3 (by rfl) ⟨185681, by rfl⟩ : syracuseStep 990301 = 371363) B371363
theorem B695411 : Blo 307833 695411 := bstep (se 1 (by rfl) ⟨521558, by rfl⟩ : syracuseStep 695411 = 1043117) B1043117
theorem B695447 : Blo 307833 695447 := bstep (se 1 (by rfl) ⟨521585, by rfl⟩ : syracuseStep 695447 = 1043171) B1043171
theorem B466073 : Blo 307833 466073 := bstep (se 2 (by rfl) ⟨174777, by rfl⟩ : syracuseStep 466073 = 349555) B349555
theorem B498841 : Blo 307833 498841 := bstep (se 2 (by rfl) ⟨187065, by rfl⟩ : syracuseStep 498841 = 374131) B374131
theorem B466187 : Blo 307833 466187 := bstep (se 1 (by rfl) ⟨349640, by rfl⟩ : syracuseStep 466187 = 699281) B699281
theorem B466199 : Blo 307833 466199 := bstep (se 1 (by rfl) ⟨349649, by rfl⟩ : syracuseStep 466199 = 699299) B699299
theorem B695627 : Blo 307833 695627 := bstep (se 1 (by rfl) ⟨521720, by rfl⟩ : syracuseStep 695627 = 1043441) B1043441
theorem B466265 : Blo 307833 466265 := bstep (se 2 (by rfl) ⟨174849, by rfl⟩ : syracuseStep 466265 = 349699) B349699
theorem B695681 : Blo 307833 695681 := bstep (se 2 (by rfl) ⟨260880, by rfl⟩ : syracuseStep 695681 = 521761) B521761
theorem B3513779 : Blo 307833 3513779 := bstep (se 1 (by rfl) ⟨2635334, by rfl⟩ : syracuseStep 3513779 = 5270669) B5270669
theorem B466379 : Blo 307833 466379 := bstep (se 1 (by rfl) ⟨349784, by rfl⟩ : syracuseStep 466379 = 699569) B699569
theorem B1056203 : Blo 307833 1056203 := bstep (se 1 (by rfl) ⟨792152, by rfl⟩ : syracuseStep 1056203 = 1584305) B1584305
theorem B466391 : Blo 307833 466391 := bstep (se 1 (by rfl) ⟨349793, by rfl⟩ : syracuseStep 466391 = 699587) B699587
theorem B466457 : Blo 307833 466457 := bstep (se 2 (by rfl) ⟨174921, by rfl⟩ : syracuseStep 466457 = 349843) B349843
theorem B5054021 : Blo 307833 5054021 := bstep (se 4 (by rfl) ⟨473814, by rfl⟩ : syracuseStep 5054021 = 947629) B947629
theorem B695897 : Blo 307833 695897 := bstep (se 2 (by rfl) ⟨260961, by rfl⟩ : syracuseStep 695897 = 521923) B521923
theorem B466571 : Blo 307833 466571 := bstep (se 1 (by rfl) ⟨349928, by rfl⟩ : syracuseStep 466571 = 699857) B699857
theorem B466583 : Blo 307833 466583 := bstep (se 1 (by rfl) ⟨349937, by rfl⟩ : syracuseStep 466583 = 699875) B699875
theorem B1777331 : Blo 307833 1777331 := bstep (se 1 (by rfl) ⟨1332998, by rfl⟩ : syracuseStep 1777331 = 2665997) B2665997
theorem B695987 : Blo 307833 695987 := bstep (se 1 (by rfl) ⟨521990, by rfl⟩ : syracuseStep 695987 = 1043981) B1043981
theorem B696023 : Blo 307833 696023 := bstep (se 1 (by rfl) ⟨522017, by rfl⟩ : syracuseStep 696023 = 1044035) B1044035
theorem B466649 : Blo 307833 466649 := bstep (se 2 (by rfl) ⟨174993, by rfl⟩ : syracuseStep 466649 = 349987) B349987
theorem B466763 : Blo 307833 466763 := bstep (se 1 (by rfl) ⟨350072, by rfl⟩ : syracuseStep 466763 = 700145) B700145
theorem B466775 : Blo 307833 466775 := bstep (se 1 (by rfl) ⟨350081, by rfl⟩ : syracuseStep 466775 = 700163) B700163
theorem B696203 : Blo 307833 696203 := bstep (se 1 (by rfl) ⟨522152, by rfl⟩ : syracuseStep 696203 = 1044305) B1044305
theorem B466841 : Blo 307833 466841 := bstep (se 2 (by rfl) ⟨175065, by rfl⟩ : syracuseStep 466841 = 350131) B350131
theorem B696257 : Blo 307833 696257 := bstep (se 2 (by rfl) ⟨261096, by rfl⟩ : syracuseStep 696257 = 522193) B522193
theorem B1122265 : Blo 307833 1122265 := bstep (se 2 (by rfl) ⟨420849, by rfl⟩ : syracuseStep 1122265 = 841699) B841699
theorem B466955 : Blo 307833 466955 := bstep (se 1 (by rfl) ⟨350216, by rfl⟩ : syracuseStep 466955 = 700433) B700433
theorem B466967 : Blo 307833 466967 := bstep (se 1 (by rfl) ⟨350225, by rfl⟩ : syracuseStep 466967 = 700451) B700451
theorem B467033 : Blo 307833 467033 := bstep (se 2 (by rfl) ⟨175137, by rfl⟩ : syracuseStep 467033 = 350275) B350275
theorem B696473 : Blo 307833 696473 := bstep (se 2 (by rfl) ⟨261177, by rfl⟩ : syracuseStep 696473 = 522355) B522355
theorem B1974451 : Blo 307833 1974451 := bstep (se 1 (by rfl) ⟨1480838, by rfl⟩ : syracuseStep 1974451 = 2961677) B2961677
theorem B1122497 : Blo 307833 1122497 := bstep (se 2 (by rfl) ⟨420936, by rfl⟩ : syracuseStep 1122497 = 841873) B841873
theorem B467147 : Blo 307833 467147 := bstep (se 1 (by rfl) ⟨350360, by rfl⟩ : syracuseStep 467147 = 700721) B700721
theorem B467159 : Blo 307833 467159 := bstep (se 1 (by rfl) ⟨350369, by rfl⟩ : syracuseStep 467159 = 700739) B700739
theorem B696563 : Blo 307833 696563 := bstep (se 1 (by rfl) ⟨522422, by rfl⟩ : syracuseStep 696563 = 1044845) B1044845
theorem B696599 : Blo 307833 696599 := bstep (se 1 (by rfl) ⟨522449, by rfl⟩ : syracuseStep 696599 = 1044899) B1044899
theorem B467225 : Blo 307833 467225 := bstep (se 2 (by rfl) ⟨175209, by rfl⟩ : syracuseStep 467225 = 350419) B350419
theorem B467339 : Blo 307833 467339 := bstep (se 1 (by rfl) ⟨350504, by rfl⟩ : syracuseStep 467339 = 701009) B701009
theorem B1057175 : Blo 307833 1057175 := bstep (se 1 (by rfl) ⟨792881, by rfl⟩ : syracuseStep 1057175 = 1585763) B1585763
theorem B467351 : Blo 307833 467351 := bstep (se 1 (by rfl) ⟨350513, by rfl⟩ : syracuseStep 467351 = 701027) B701027
theorem B696779 : Blo 307833 696779 := bstep (se 1 (by rfl) ⟨522584, by rfl⟩ : syracuseStep 696779 = 1045169) B1045169
theorem B467417 : Blo 307833 467417 := bstep (se 2 (by rfl) ⟨175281, by rfl⟩ : syracuseStep 467417 = 350563) B350563
theorem B696833 : Blo 307833 696833 := bstep (se 2 (by rfl) ⟨261312, by rfl⟩ : syracuseStep 696833 = 522625) B522625
theorem B467531 : Blo 307833 467531 := bstep (se 1 (by rfl) ⟨350648, by rfl⟩ : syracuseStep 467531 = 701297) B701297
theorem B467543 : Blo 307833 467543 := bstep (se 1 (by rfl) ⟨350657, by rfl⟩ : syracuseStep 467543 = 701315) B701315
theorem B467609 : Blo 307833 467609 := bstep (se 2 (by rfl) ⟨175353, by rfl⟩ : syracuseStep 467609 = 350707) B350707
theorem B697049 : Blo 307833 697049 := bstep (se 2 (by rfl) ⟨261393, by rfl⟩ : syracuseStep 697049 = 522787) B522787
theorem B467723 : Blo 307833 467723 := bstep (se 1 (by rfl) ⟨350792, by rfl⟩ : syracuseStep 467723 = 701585) B701585
theorem B467735 : Blo 307833 467735 := bstep (se 1 (by rfl) ⟨350801, by rfl⟩ : syracuseStep 467735 = 701603) B701603
theorem B336683 : Blo 307833 336683 := bstep (se 1 (by rfl) ⟨252512, by rfl⟩ : syracuseStep 336683 = 505025) B505025
theorem B697139 : Blo 307833 697139 := bstep (se 1 (by rfl) ⟨522854, by rfl⟩ : syracuseStep 697139 = 1045709) B1045709
theorem B697175 : Blo 307833 697175 := bstep (se 1 (by rfl) ⟨522881, by rfl⟩ : syracuseStep 697175 = 1045763) B1045763
theorem B3515237 : Blo 307833 3515237 := bstep (se 4 (by rfl) ⟨329553, by rfl⟩ : syracuseStep 3515237 = 659107) B659107
theorem B664499 : Blo 307833 664499 := bstep (se 1 (by rfl) ⟨498374, by rfl⟩ : syracuseStep 664499 = 996749) B996749
theorem B697355 : Blo 307833 697355 := bstep (se 1 (by rfl) ⟨523016, by rfl⟩ : syracuseStep 697355 = 1046033) B1046033
theorem B697409 : Blo 307833 697409 := bstep (se 2 (by rfl) ⟨261528, by rfl⟩ : syracuseStep 697409 = 523057) B523057
theorem B697625 : Blo 307833 697625 := bstep (se 2 (by rfl) ⟨261609, by rfl⟩ : syracuseStep 697625 = 523219) B523219
theorem B697715 : Blo 307833 697715 := bstep (se 1 (by rfl) ⟨523286, by rfl⟩ : syracuseStep 697715 = 1046573) B1046573
theorem B697751 : Blo 307833 697751 := bstep (se 1 (by rfl) ⟨523313, by rfl⟩ : syracuseStep 697751 = 1046627) B1046627
theorem B664985 : Blo 307833 664985 := bstep (se 2 (by rfl) ⟨249369, by rfl⟩ : syracuseStep 664985 = 498739) B498739
theorem B1058269 : Blo 307833 1058269 := bstep (se 3 (by rfl) ⟨198425, by rfl⟩ : syracuseStep 1058269 = 396851) B396851
theorem B2827781 : Blo 307833 2827781 := bstep (se 4 (by rfl) ⟨265104, by rfl⟩ : syracuseStep 2827781 = 530209) B530209
theorem B2631203 : Blo 307833 2631203 := bstep (se 1 (by rfl) ⟨1973402, by rfl⟩ : syracuseStep 2631203 = 3946805) B3946805
theorem B4531781 : Blo 307833 4531781 := bstep (se 4 (by rfl) ⟨424854, by rfl⟩ : syracuseStep 4531781 = 849709) B849709
theorem B697931 : Blo 307833 697931 := bstep (se 1 (by rfl) ⟨523448, by rfl⟩ : syracuseStep 697931 = 1046897) B1046897
theorem B697985 : Blo 307833 697985 := bstep (se 2 (by rfl) ⟨261744, by rfl⟩ : syracuseStep 697985 = 523489) B523489
theorem B698201 : Blo 307833 698201 := bstep (se 2 (by rfl) ⟨261825, by rfl⟩ : syracuseStep 698201 = 523651) B523651
theorem B1484723 : Blo 307833 1484723 := bstep (se 1 (by rfl) ⟨1113542, by rfl⟩ : syracuseStep 1484723 = 2227085) B2227085
theorem B698291 : Blo 307833 698291 := bstep (se 1 (by rfl) ⟨523718, by rfl⟩ : syracuseStep 698291 = 1047437) B1047437
theorem B698327 : Blo 307833 698327 := bstep (se 1 (by rfl) ⟨523745, by rfl⟩ : syracuseStep 698327 = 1047491) B1047491
theorem B665729 : Blo 307833 665729 := bstep (se 2 (by rfl) ⟨249648, by rfl⟩ : syracuseStep 665729 = 499297) B499297
theorem B698507 : Blo 307833 698507 := bstep (se 1 (by rfl) ⟨523880, by rfl⟩ : syracuseStep 698507 = 1047761) B1047761
theorem B698561 : Blo 307833 698561 := bstep (se 2 (by rfl) ⟨261960, by rfl⟩ : syracuseStep 698561 = 523921) B523921
theorem B600473 : Blo 307833 600473 := bstep (se 2 (by rfl) ⟨225177, by rfl⟩ : syracuseStep 600473 = 450355) B450355
theorem B698777 : Blo 307833 698777 := bstep (se 2 (by rfl) ⟨262041, by rfl⟩ : syracuseStep 698777 = 524083) B524083
theorem B698867 : Blo 307833 698867 := bstep (se 1 (by rfl) ⟨524150, by rfl⟩ : syracuseStep 698867 = 1048301) B1048301
theorem B698903 : Blo 307833 698903 := bstep (se 1 (by rfl) ⟨524177, by rfl⟩ : syracuseStep 698903 = 1048355) B1048355
theorem B1485377 : Blo 307833 1485377 := bstep (se 2 (by rfl) ⟨557016, by rfl⟩ : syracuseStep 1485377 = 1114033) B1114033
theorem B2402891 : Blo 307833 2402891 := bstep (se 1 (by rfl) ⟨1802168, by rfl⟩ : syracuseStep 2402891 = 3604337) B3604337
theorem B699083 : Blo 307833 699083 := bstep (se 1 (by rfl) ⟨524312, by rfl⟩ : syracuseStep 699083 = 1048625) B1048625
theorem B699137 : Blo 307833 699137 := bstep (se 2 (by rfl) ⟨262176, by rfl⟩ : syracuseStep 699137 = 524353) B524353
theorem B371479 : Blo 307833 371479 := bstep (se 1 (by rfl) ⟨278609, by rfl⟩ : syracuseStep 371479 = 557219) B557219
theorem B699353 : Blo 307833 699353 := bstep (se 2 (by rfl) ⟨262257, by rfl⟩ : syracuseStep 699353 = 524515) B524515
theorem B1256465 : Blo 307833 1256465 := bstep (se 2 (by rfl) ⟨471174, by rfl⟩ : syracuseStep 1256465 = 942349) B942349
theorem B699443 : Blo 307833 699443 := bstep (se 1 (by rfl) ⟨524582, by rfl⟩ : syracuseStep 699443 = 1049165) B1049165
theorem B699479 : Blo 307833 699479 := bstep (se 1 (by rfl) ⟨524609, by rfl⟩ : syracuseStep 699479 = 1049219) B1049219
theorem B4041859 : Blo 307833 4041859 := bstep (se 1 (by rfl) ⟨3031394, by rfl⟩ : syracuseStep 4041859 = 6062789) B6062789
theorem B699659 : Blo 307833 699659 := bstep (se 1 (by rfl) ⟨524744, by rfl⟩ : syracuseStep 699659 = 1049489) B1049489
theorem B699713 : Blo 307833 699713 := bstep (se 2 (by rfl) ⟨262392, by rfl⟩ : syracuseStep 699713 = 524785) B524785
theorem B1322315 : Blo 307833 1322315 := bstep (se 1 (by rfl) ⟨991736, by rfl⟩ : syracuseStep 1322315 = 1983473) B1983473
theorem B699929 : Blo 307833 699929 := bstep (se 2 (by rfl) ⟨262473, by rfl⟩ : syracuseStep 699929 = 524947) B524947
theorem B2666029 : Blo 307833 2666029 := bstep (se 3 (by rfl) ⟨499880, by rfl⟩ : syracuseStep 2666029 = 999761) B999761
theorem B700019 : Blo 307833 700019 := bstep (se 1 (by rfl) ⟨525014, by rfl⟩ : syracuseStep 700019 = 1050029) B1050029
theorem B994967 : Blo 307833 994967 := bstep (se 1 (by rfl) ⟨746225, by rfl⟩ : syracuseStep 994967 = 1492451) B1492451
theorem B700055 : Blo 307833 700055 := bstep (se 1 (by rfl) ⟨525041, by rfl⟩ : syracuseStep 700055 = 1050083) B1050083
theorem B700235 : Blo 307833 700235 := bstep (se 1 (by rfl) ⟨525176, by rfl⟩ : syracuseStep 700235 = 1050353) B1050353
theorem B6762341 : Blo 307833 6762341 := bstep (se 4 (by rfl) ⟨633969, by rfl⟩ : syracuseStep 6762341 = 1267939) B1267939
theorem B700289 : Blo 307833 700289 := bstep (se 2 (by rfl) ⟨262608, by rfl⟩ : syracuseStep 700289 = 525217) B525217
theorem B700505 : Blo 307833 700505 := bstep (se 2 (by rfl) ⟨262689, by rfl⟩ : syracuseStep 700505 = 525379) B525379
theorem B700595 : Blo 307833 700595 := bstep (se 1 (by rfl) ⟨525446, by rfl⟩ : syracuseStep 700595 = 1050893) B1050893
theorem B700631 : Blo 307833 700631 := bstep (se 1 (by rfl) ⟨525473, by rfl⟩ : syracuseStep 700631 = 1050947) B1050947
theorem B438539 : Blo 307833 438539 := bstep (se 1 (by rfl) ⟨328904, by rfl⟩ : syracuseStep 438539 = 657809) B657809
theorem B2339117 : Blo 307833 2339117 := bstep (se 3 (by rfl) ⟨438584, by rfl⟩ : syracuseStep 2339117 = 877169) B877169
theorem B700811 : Blo 307833 700811 := bstep (se 1 (by rfl) ⟨525608, by rfl⟩ : syracuseStep 700811 = 1051217) B1051217
theorem B995735 : Blo 307833 995735 := bstep (se 1 (by rfl) ⟨746801, by rfl⟩ : syracuseStep 995735 = 1493603) B1493603
theorem B700865 : Blo 307833 700865 := bstep (se 2 (by rfl) ⟨262824, by rfl⟩ : syracuseStep 700865 = 525649) B525649
theorem B668171 : Blo 307833 668171 := bstep (se 1 (by rfl) ⟨501128, by rfl⟩ : syracuseStep 668171 = 1002257) B1002257
theorem B1094219 : Blo 307833 1094219 := bstep (se 1 (by rfl) ⟨820664, by rfl⟩ : syracuseStep 1094219 = 1641329) B1641329
theorem B307851 : Blo 307833 307851 := bstep (se 1 (by rfl) ⟨230888, by rfl⟩ : syracuseStep 307851 = 461777) B461777
theorem B307863 : Blo 307833 307863 := bstep (se 1 (by rfl) ⟨230897, by rfl⟩ : syracuseStep 307863 = 461795) B461795
theorem B701081 : Blo 307833 701081 := bstep (se 2 (by rfl) ⟨262905, by rfl⟩ : syracuseStep 701081 = 525811) B525811
theorem B307883 : Blo 307833 307883 := bstep (se 1 (by rfl) ⟨230912, by rfl⟩ : syracuseStep 307883 = 461825) B461825
theorem B307895 : Blo 307833 307895 := bstep (se 1 (by rfl) ⟨230921, by rfl⟩ : syracuseStep 307895 = 461843) B461843
theorem B307915 : Blo 307833 307915 := bstep (se 1 (by rfl) ⟨230936, by rfl⟩ : syracuseStep 307915 = 461873) B461873
theorem B2994893 : Blo 307833 2994893 := bstep (se 3 (by rfl) ⟨561542, by rfl⟩ : syracuseStep 2994893 = 1123085) B1123085
theorem B307927 : Blo 307833 307927 := bstep (se 1 (by rfl) ⟨230945, by rfl⟩ : syracuseStep 307927 = 461891) B461891
theorem B307947 : Blo 307833 307947 := bstep (se 1 (by rfl) ⟨230960, by rfl⟩ : syracuseStep 307947 = 461921) B461921
theorem B701171 : Blo 307833 701171 := bstep (se 1 (by rfl) ⟨525878, by rfl⟩ : syracuseStep 701171 = 1051757) B1051757
theorem B307959 : Blo 307833 307959 := bstep (se 1 (by rfl) ⟨230969, by rfl⟩ : syracuseStep 307959 = 461939) B461939
theorem B307979 : Blo 307833 307979 := bstep (se 1 (by rfl) ⟨230984, by rfl⟩ : syracuseStep 307979 = 461969) B461969
theorem B307991 : Blo 307833 307991 := bstep (se 1 (by rfl) ⟨230993, by rfl⟩ : syracuseStep 307991 = 461987) B461987
theorem B701207 : Blo 307833 701207 := bstep (se 1 (by rfl) ⟨525905, by rfl⟩ : syracuseStep 701207 = 1051811) B1051811
theorem B308011 : Blo 307833 308011 := bstep (se 1 (by rfl) ⟨231008, by rfl⟩ : syracuseStep 308011 = 462017) B462017
theorem B308023 : Blo 307833 308023 := bstep (se 1 (by rfl) ⟨231017, by rfl⟩ : syracuseStep 308023 = 462035) B462035
theorem B308043 : Blo 307833 308043 := bstep (se 1 (by rfl) ⟨231032, by rfl⟩ : syracuseStep 308043 = 462065) B462065
theorem B308055 : Blo 307833 308055 := bstep (se 1 (by rfl) ⟨231041, by rfl⟩ : syracuseStep 308055 = 462083) B462083
theorem B308075 : Blo 307833 308075 := bstep (se 1 (by rfl) ⟨231056, by rfl⟩ : syracuseStep 308075 = 462113) B462113
theorem B308087 : Blo 307833 308087 := bstep (se 1 (by rfl) ⟨231065, by rfl⟩ : syracuseStep 308087 = 462131) B462131
theorem B308107 : Blo 307833 308107 := bstep (se 1 (by rfl) ⟨231080, by rfl⟩ : syracuseStep 308107 = 462161) B462161
theorem B308119 : Blo 307833 308119 := bstep (se 1 (by rfl) ⟨231089, by rfl⟩ : syracuseStep 308119 = 462179) B462179
theorem B996247 : Blo 307833 996247 := bstep (se 1 (by rfl) ⟨747185, by rfl⟩ : syracuseStep 996247 = 1494371) B1494371
theorem B308139 : Blo 307833 308139 := bstep (se 1 (by rfl) ⟨231104, by rfl⟩ : syracuseStep 308139 = 462209) B462209
theorem B4469681 : Blo 307833 4469681 := bstep (se 2 (by rfl) ⟨1676130, by rfl⟩ : syracuseStep 4469681 = 3352261) B3352261
theorem B1323955 : Blo 307833 1323955 := bstep (se 1 (by rfl) ⟨992966, by rfl⟩ : syracuseStep 1323955 = 1985933) B1985933
theorem B308151 : Blo 307833 308151 := bstep (se 1 (by rfl) ⟨231113, by rfl⟩ : syracuseStep 308151 = 462227) B462227
theorem B308171 : Blo 307833 308171 := bstep (se 1 (by rfl) ⟨231128, by rfl⟩ : syracuseStep 308171 = 462257) B462257
theorem B701387 : Blo 307833 701387 := bstep (se 1 (by rfl) ⟨526040, by rfl⟩ : syracuseStep 701387 = 1052081) B1052081
theorem B308183 : Blo 307833 308183 := bstep (se 1 (by rfl) ⟨231137, by rfl⟩ : syracuseStep 308183 = 462275) B462275
theorem B308203 : Blo 307833 308203 := bstep (se 1 (by rfl) ⟨231152, by rfl⟩ : syracuseStep 308203 = 462305) B462305
theorem B308215 : Blo 307833 308215 := bstep (se 1 (by rfl) ⟨231161, by rfl⟩ : syracuseStep 308215 = 462323) B462323
theorem B701441 : Blo 307833 701441 := bstep (se 2 (by rfl) ⟨263040, by rfl⟩ : syracuseStep 701441 = 526081) B526081
theorem B308235 : Blo 307833 308235 := bstep (se 1 (by rfl) ⟨231176, by rfl⟩ : syracuseStep 308235 = 462353) B462353
theorem B308247 : Blo 307833 308247 := bstep (se 1 (by rfl) ⟨231185, by rfl⟩ : syracuseStep 308247 = 462371) B462371
theorem B308267 : Blo 307833 308267 := bstep (se 1 (by rfl) ⟨231200, by rfl⟩ : syracuseStep 308267 = 462401) B462401
theorem B1258541 : Blo 307833 1258541 := bstep (se 3 (by rfl) ⟨235976, by rfl⟩ : syracuseStep 1258541 = 471953) B471953
theorem B308279 : Blo 307833 308279 := bstep (se 1 (by rfl) ⟨231209, by rfl⟩ : syracuseStep 308279 = 462419) B462419
theorem B308299 : Blo 307833 308299 := bstep (se 1 (by rfl) ⟨231224, by rfl⟩ : syracuseStep 308299 = 462449) B462449
theorem B308311 : Blo 307833 308311 := bstep (se 1 (by rfl) ⟨231233, by rfl⟩ : syracuseStep 308311 = 462467) B462467
theorem B308331 : Blo 307833 308331 := bstep (se 1 (by rfl) ⟨231248, by rfl⟩ : syracuseStep 308331 = 462497) B462497
theorem B308343 : Blo 307833 308343 := bstep (se 1 (by rfl) ⟨231257, by rfl⟩ : syracuseStep 308343 = 462515) B462515
theorem B308363 : Blo 307833 308363 := bstep (se 1 (by rfl) ⟨231272, by rfl⟩ : syracuseStep 308363 = 462545) B462545
theorem B308375 : Blo 307833 308375 := bstep (se 1 (by rfl) ⟨231281, by rfl⟩ : syracuseStep 308375 = 462563) B462563
theorem B308395 : Blo 307833 308395 := bstep (se 1 (by rfl) ⟨231296, by rfl⟩ : syracuseStep 308395 = 462593) B462593
theorem B308407 : Blo 307833 308407 := bstep (se 1 (by rfl) ⟨231305, by rfl⟩ : syracuseStep 308407 = 462611) B462611
theorem B308427 : Blo 307833 308427 := bstep (se 1 (by rfl) ⟨231320, by rfl⟩ : syracuseStep 308427 = 462641) B462641
theorem B308439 : Blo 307833 308439 := bstep (se 1 (by rfl) ⟨231329, by rfl⟩ : syracuseStep 308439 = 462659) B462659
theorem B308459 : Blo 307833 308459 := bstep (se 1 (by rfl) ⟨231344, by rfl⟩ : syracuseStep 308459 = 462689) B462689
theorem B308471 : Blo 307833 308471 := bstep (se 1 (by rfl) ⟨231353, by rfl⟩ : syracuseStep 308471 = 462707) B462707
theorem B308491 : Blo 307833 308491 := bstep (se 1 (by rfl) ⟨231368, by rfl⟩ : syracuseStep 308491 = 462737) B462737
theorem B308503 : Blo 307833 308503 := bstep (se 1 (by rfl) ⟨231377, by rfl⟩ : syracuseStep 308503 = 462755) B462755
theorem B308523 : Blo 307833 308523 := bstep (se 1 (by rfl) ⟨231392, by rfl⟩ : syracuseStep 308523 = 462785) B462785
theorem B308535 : Blo 307833 308535 := bstep (se 1 (by rfl) ⟨231401, by rfl⟩ : syracuseStep 308535 = 462803) B462803
theorem B308555 : Blo 307833 308555 := bstep (se 1 (by rfl) ⟨231416, by rfl⟩ : syracuseStep 308555 = 462833) B462833
theorem B308567 : Blo 307833 308567 := bstep (se 1 (by rfl) ⟨231425, by rfl⟩ : syracuseStep 308567 = 462851) B462851
theorem B308587 : Blo 307833 308587 := bstep (se 1 (by rfl) ⟨231440, by rfl⟩ : syracuseStep 308587 = 462881) B462881
theorem B308599 : Blo 307833 308599 := bstep (se 1 (by rfl) ⟨231449, by rfl⟩ : syracuseStep 308599 = 462899) B462899
theorem B308619 : Blo 307833 308619 := bstep (se 1 (by rfl) ⟨231464, by rfl⟩ : syracuseStep 308619 = 462929) B462929
theorem B308631 : Blo 307833 308631 := bstep (se 1 (by rfl) ⟨231473, by rfl⟩ : syracuseStep 308631 = 462947) B462947
theorem B308651 : Blo 307833 308651 := bstep (se 1 (by rfl) ⟨231488, by rfl⟩ : syracuseStep 308651 = 462977) B462977
theorem B308663 : Blo 307833 308663 := bstep (se 1 (by rfl) ⟨231497, by rfl⟩ : syracuseStep 308663 = 462995) B462995
theorem B38352325 : Blo 307833 38352325 := bstep (se 4 (by rfl) ⟨3595530, by rfl⟩ : syracuseStep 38352325 = 7191061) B7191061
theorem B308683 : Blo 307833 308683 := bstep (se 1 (by rfl) ⟨231512, by rfl⟩ : syracuseStep 308683 = 463025) B463025
theorem B308695 : Blo 307833 308695 := bstep (se 1 (by rfl) ⟨231521, by rfl⟩ : syracuseStep 308695 = 463043) B463043
theorem B308715 : Blo 307833 308715 := bstep (se 1 (by rfl) ⟨231536, by rfl⟩ : syracuseStep 308715 = 463073) B463073
theorem B308727 : Blo 307833 308727 := bstep (se 1 (by rfl) ⟨231545, by rfl⟩ : syracuseStep 308727 = 463091) B463091
theorem B308747 : Blo 307833 308747 := bstep (se 1 (by rfl) ⟨231560, by rfl⟩ : syracuseStep 308747 = 463121) B463121
theorem B308759 : Blo 307833 308759 := bstep (se 1 (by rfl) ⟨231569, by rfl⟩ : syracuseStep 308759 = 463139) B463139
theorem B308779 : Blo 307833 308779 := bstep (se 1 (by rfl) ⟨231584, by rfl⟩ : syracuseStep 308779 = 463169) B463169
theorem B1259059 : Blo 307833 1259059 := bstep (se 1 (by rfl) ⟨944294, by rfl⟩ : syracuseStep 1259059 = 1888589) B1888589
theorem B308791 : Blo 307833 308791 := bstep (se 1 (by rfl) ⟨231593, by rfl⟩ : syracuseStep 308791 = 463187) B463187
theorem B308811 : Blo 307833 308811 := bstep (se 1 (by rfl) ⟨231608, by rfl⟩ : syracuseStep 308811 = 463217) B463217
theorem B308823 : Blo 307833 308823 := bstep (se 1 (by rfl) ⟨231617, by rfl⟩ : syracuseStep 308823 = 463235) B463235
theorem B308843 : Blo 307833 308843 := bstep (se 1 (by rfl) ⟨231632, by rfl⟩ : syracuseStep 308843 = 463265) B463265
theorem B308855 : Blo 307833 308855 := bstep (se 1 (by rfl) ⟨231641, by rfl⟩ : syracuseStep 308855 = 463283) B463283
theorem B308875 : Blo 307833 308875 := bstep (se 1 (by rfl) ⟨231656, by rfl⟩ : syracuseStep 308875 = 463313) B463313
theorem B308887 : Blo 307833 308887 := bstep (se 1 (by rfl) ⟨231665, by rfl⟩ : syracuseStep 308887 = 463331) B463331
theorem B308907 : Blo 307833 308907 := bstep (se 1 (by rfl) ⟨231680, by rfl⟩ : syracuseStep 308907 = 463361) B463361
theorem B308919 : Blo 307833 308919 := bstep (se 1 (by rfl) ⟨231689, by rfl⟩ : syracuseStep 308919 = 463379) B463379
theorem B308939 : Blo 307833 308939 := bstep (se 1 (by rfl) ⟨231704, by rfl⟩ : syracuseStep 308939 = 463409) B463409
theorem B997067 : Blo 307833 997067 := bstep (se 1 (by rfl) ⟨747800, by rfl⟩ : syracuseStep 997067 = 1495601) B1495601
theorem B308951 : Blo 307833 308951 := bstep (se 1 (by rfl) ⟨231713, by rfl⟩ : syracuseStep 308951 = 463427) B463427
theorem B308971 : Blo 307833 308971 := bstep (se 1 (by rfl) ⟨231728, by rfl⟩ : syracuseStep 308971 = 463457) B463457
theorem B308983 : Blo 307833 308983 := bstep (se 1 (by rfl) ⟨231737, by rfl⟩ : syracuseStep 308983 = 463475) B463475
theorem B309003 : Blo 307833 309003 := bstep (se 1 (by rfl) ⟨231752, by rfl⟩ : syracuseStep 309003 = 463505) B463505
theorem B309015 : Blo 307833 309015 := bstep (se 1 (by rfl) ⟨231761, by rfl⟩ : syracuseStep 309015 = 463523) B463523
theorem B309035 : Blo 307833 309035 := bstep (se 1 (by rfl) ⟨231776, by rfl⟩ : syracuseStep 309035 = 463553) B463553
theorem B309047 : Blo 307833 309047 := bstep (se 1 (by rfl) ⟨231785, by rfl⟩ : syracuseStep 309047 = 463571) B463571
theorem B309067 : Blo 307833 309067 := bstep (se 1 (by rfl) ⟨231800, by rfl⟩ : syracuseStep 309067 = 463601) B463601
theorem B309079 : Blo 307833 309079 := bstep (se 1 (by rfl) ⟨231809, by rfl⟩ : syracuseStep 309079 = 463619) B463619
theorem B309099 : Blo 307833 309099 := bstep (se 1 (by rfl) ⟨231824, by rfl⟩ : syracuseStep 309099 = 463649) B463649
theorem B309111 : Blo 307833 309111 := bstep (se 1 (by rfl) ⟨231833, by rfl⟩ : syracuseStep 309111 = 463667) B463667
theorem B309131 : Blo 307833 309131 := bstep (se 1 (by rfl) ⟨231848, by rfl⟩ : syracuseStep 309131 = 463697) B463697
theorem B309143 : Blo 307833 309143 := bstep (se 1 (by rfl) ⟨231857, by rfl⟩ : syracuseStep 309143 = 463715) B463715
theorem B309163 : Blo 307833 309163 := bstep (se 1 (by rfl) ⟨231872, by rfl⟩ : syracuseStep 309163 = 463745) B463745
theorem B309175 : Blo 307833 309175 := bstep (se 1 (by rfl) ⟨231881, by rfl⟩ : syracuseStep 309175 = 463763) B463763
theorem B309195 : Blo 307833 309195 := bstep (se 1 (by rfl) ⟨231896, by rfl⟩ : syracuseStep 309195 = 463793) B463793
theorem B309207 : Blo 307833 309207 := bstep (se 1 (by rfl) ⟨231905, by rfl⟩ : syracuseStep 309207 = 463811) B463811
theorem B309227 : Blo 307833 309227 := bstep (se 1 (by rfl) ⟨231920, by rfl⟩ : syracuseStep 309227 = 463841) B463841
theorem B309239 : Blo 307833 309239 := bstep (se 1 (by rfl) ⟨231929, by rfl⟩ : syracuseStep 309239 = 463859) B463859
theorem B309259 : Blo 307833 309259 := bstep (se 1 (by rfl) ⟨231944, by rfl⟩ : syracuseStep 309259 = 463889) B463889
theorem B309271 : Blo 307833 309271 := bstep (se 1 (by rfl) ⟨231953, by rfl⟩ : syracuseStep 309271 = 463907) B463907
theorem B309291 : Blo 307833 309291 := bstep (se 1 (by rfl) ⟨231968, by rfl⟩ : syracuseStep 309291 = 463937) B463937
theorem B997427 : Blo 307833 997427 := bstep (se 1 (by rfl) ⟨748070, by rfl⟩ : syracuseStep 997427 = 1496141) B1496141
theorem B309303 : Blo 307833 309303 := bstep (se 1 (by rfl) ⟨231977, by rfl⟩ : syracuseStep 309303 = 463955) B463955
theorem B309323 : Blo 307833 309323 := bstep (se 1 (by rfl) ⟨231992, by rfl⟩ : syracuseStep 309323 = 463985) B463985
theorem B440407 : Blo 307833 440407 := bstep (se 1 (by rfl) ⟨330305, by rfl⟩ : syracuseStep 440407 = 660611) B660611
theorem B309335 : Blo 307833 309335 := bstep (se 1 (by rfl) ⟨232001, by rfl⟩ : syracuseStep 309335 = 464003) B464003
theorem B309355 : Blo 307833 309355 := bstep (se 1 (by rfl) ⟨232016, by rfl⟩ : syracuseStep 309355 = 464033) B464033
theorem B309367 : Blo 307833 309367 := bstep (se 1 (by rfl) ⟨232025, by rfl⟩ : syracuseStep 309367 = 464051) B464051
theorem B309387 : Blo 307833 309387 := bstep (se 1 (by rfl) ⟨232040, by rfl⟩ : syracuseStep 309387 = 464081) B464081
theorem B1128593 : Blo 307833 1128593 := bstep (se 2 (by rfl) ⟨423222, by rfl⟩ : syracuseStep 1128593 = 846445) B846445
theorem B309399 : Blo 307833 309399 := bstep (se 1 (by rfl) ⟨232049, by rfl⟩ : syracuseStep 309399 = 464099) B464099
theorem B309419 : Blo 307833 309419 := bstep (se 1 (by rfl) ⟨232064, by rfl⟩ : syracuseStep 309419 = 464129) B464129
theorem B309431 : Blo 307833 309431 := bstep (se 1 (by rfl) ⟨232073, by rfl⟩ : syracuseStep 309431 = 464147) B464147
theorem B309451 : Blo 307833 309451 := bstep (se 1 (by rfl) ⟨232088, by rfl⟩ : syracuseStep 309451 = 464177) B464177
theorem B309463 : Blo 307833 309463 := bstep (se 1 (by rfl) ⟨232097, by rfl⟩ : syracuseStep 309463 = 464195) B464195
theorem B833753 : Blo 307833 833753 := bstep (se 2 (by rfl) ⟨312657, by rfl⟩ : syracuseStep 833753 = 625315) B625315
theorem B309483 : Blo 307833 309483 := bstep (se 1 (by rfl) ⟨232112, by rfl⟩ : syracuseStep 309483 = 464225) B464225
theorem B309495 : Blo 307833 309495 := bstep (se 1 (by rfl) ⟨232121, by rfl⟩ : syracuseStep 309495 = 464243) B464243
theorem B309515 : Blo 307833 309515 := bstep (se 1 (by rfl) ⟨232136, by rfl⟩ : syracuseStep 309515 = 464273) B464273
theorem B309527 : Blo 307833 309527 := bstep (se 1 (by rfl) ⟨232145, by rfl⟩ : syracuseStep 309527 = 464291) B464291
theorem B309547 : Blo 307833 309547 := bstep (se 1 (by rfl) ⟨232160, by rfl⟩ : syracuseStep 309547 = 464321) B464321
theorem B309559 : Blo 307833 309559 := bstep (se 1 (by rfl) ⟨232169, by rfl⟩ : syracuseStep 309559 = 464339) B464339
theorem B309579 : Blo 307833 309579 := bstep (se 1 (by rfl) ⟨232184, by rfl⟩ : syracuseStep 309579 = 464369) B464369
theorem B309591 : Blo 307833 309591 := bstep (se 1 (by rfl) ⟨232193, by rfl⟩ : syracuseStep 309591 = 464387) B464387
theorem B309611 : Blo 307833 309611 := bstep (se 1 (by rfl) ⟨232208, by rfl⟩ : syracuseStep 309611 = 464417) B464417
theorem B309623 : Blo 307833 309623 := bstep (se 1 (by rfl) ⟨232217, by rfl⟩ : syracuseStep 309623 = 464435) B464435
theorem B1325443 : Blo 307833 1325443 := bstep (se 1 (by rfl) ⟨994082, by rfl⟩ : syracuseStep 1325443 = 1988165) B1988165
theorem B309643 : Blo 307833 309643 := bstep (se 1 (by rfl) ⟨232232, by rfl⟩ : syracuseStep 309643 = 464465) B464465
theorem B309655 : Blo 307833 309655 := bstep (se 1 (by rfl) ⟨232241, by rfl⟩ : syracuseStep 309655 = 464483) B464483
theorem B309675 : Blo 307833 309675 := bstep (se 1 (by rfl) ⟨232256, by rfl⟩ : syracuseStep 309675 = 464513) B464513
theorem B309687 : Blo 307833 309687 := bstep (se 1 (by rfl) ⟨232265, by rfl⟩ : syracuseStep 309687 = 464531) B464531
theorem B309707 : Blo 307833 309707 := bstep (se 1 (by rfl) ⟨232280, by rfl⟩ : syracuseStep 309707 = 464561) B464561
theorem B309719 : Blo 307833 309719 := bstep (se 1 (by rfl) ⟨232289, by rfl⟩ : syracuseStep 309719 = 464579) B464579
theorem B309739 : Blo 307833 309739 := bstep (se 1 (by rfl) ⟨232304, by rfl⟩ : syracuseStep 309739 = 464609) B464609
theorem B309751 : Blo 307833 309751 := bstep (se 1 (by rfl) ⟨232313, by rfl⟩ : syracuseStep 309751 = 464627) B464627
theorem B1260035 : Blo 307833 1260035 := bstep (se 1 (by rfl) ⟨945026, by rfl⟩ : syracuseStep 1260035 = 1890053) B1890053
theorem B309771 : Blo 307833 309771 := bstep (se 1 (by rfl) ⟨232328, by rfl⟩ : syracuseStep 309771 = 464657) B464657
theorem B309783 : Blo 307833 309783 := bstep (se 1 (by rfl) ⟨232337, by rfl⟩ : syracuseStep 309783 = 464675) B464675
theorem B309803 : Blo 307833 309803 := bstep (se 1 (by rfl) ⟨232352, by rfl⟩ : syracuseStep 309803 = 464705) B464705
theorem B309815 : Blo 307833 309815 := bstep (se 1 (by rfl) ⟨232361, by rfl⟩ : syracuseStep 309815 = 464723) B464723
theorem B309835 : Blo 307833 309835 := bstep (se 1 (by rfl) ⟨232376, by rfl⟩ : syracuseStep 309835 = 464753) B464753
theorem B309847 : Blo 307833 309847 := bstep (se 1 (by rfl) ⟨232385, by rfl⟩ : syracuseStep 309847 = 464771) B464771
theorem B309867 : Blo 307833 309867 := bstep (se 1 (by rfl) ⟨232400, by rfl⟩ : syracuseStep 309867 = 464801) B464801
theorem B309879 : Blo 307833 309879 := bstep (se 1 (by rfl) ⟨232409, by rfl⟩ : syracuseStep 309879 = 464819) B464819
theorem B309899 : Blo 307833 309899 := bstep (se 1 (by rfl) ⟨232424, by rfl⟩ : syracuseStep 309899 = 464849) B464849
theorem B309911 : Blo 307833 309911 := bstep (se 1 (by rfl) ⟨232433, by rfl⟩ : syracuseStep 309911 = 464867) B464867
theorem B309931 : Blo 307833 309931 := bstep (se 1 (by rfl) ⟨232448, by rfl⟩ : syracuseStep 309931 = 464897) B464897
theorem B309943 : Blo 307833 309943 := bstep (se 1 (by rfl) ⟨232457, by rfl⟩ : syracuseStep 309943 = 464915) B464915
theorem B309963 : Blo 307833 309963 := bstep (se 1 (by rfl) ⟨232472, by rfl⟩ : syracuseStep 309963 = 464945) B464945
theorem B309975 : Blo 307833 309975 := bstep (se 1 (by rfl) ⟨232481, by rfl⟩ : syracuseStep 309975 = 464963) B464963
theorem B309995 : Blo 307833 309995 := bstep (se 1 (by rfl) ⟨232496, by rfl⟩ : syracuseStep 309995 = 464993) B464993
theorem B310007 : Blo 307833 310007 := bstep (se 1 (by rfl) ⟨232505, by rfl⟩ : syracuseStep 310007 = 465011) B465011
theorem B310027 : Blo 307833 310027 := bstep (se 1 (by rfl) ⟨232520, by rfl⟩ : syracuseStep 310027 = 465041) B465041
theorem B1489681 : Blo 307833 1489681 := bstep (se 2 (by rfl) ⟨558630, by rfl⟩ : syracuseStep 1489681 = 1117261) B1117261
theorem B310039 : Blo 307833 310039 := bstep (se 1 (by rfl) ⟨232529, by rfl⟩ : syracuseStep 310039 = 465059) B465059
theorem B310059 : Blo 307833 310059 := bstep (se 1 (by rfl) ⟨232544, by rfl⟩ : syracuseStep 310059 = 465089) B465089
theorem B310071 : Blo 307833 310071 := bstep (se 1 (by rfl) ⟨232553, by rfl⟩ : syracuseStep 310071 = 465107) B465107
theorem B310091 : Blo 307833 310091 := bstep (se 1 (by rfl) ⟨232568, by rfl⟩ : syracuseStep 310091 = 465137) B465137
theorem B310103 : Blo 307833 310103 := bstep (se 1 (by rfl) ⟨232577, by rfl⟩ : syracuseStep 310103 = 465155) B465155
theorem B1489757 : Blo 307833 1489757 := bstep (se 3 (by rfl) ⟨279329, by rfl⟩ : syracuseStep 1489757 = 558659) B558659
theorem B310123 : Blo 307833 310123 := bstep (se 1 (by rfl) ⟨232592, by rfl⟩ : syracuseStep 310123 = 465185) B465185
theorem B310135 : Blo 307833 310135 := bstep (se 1 (by rfl) ⟨232601, by rfl⟩ : syracuseStep 310135 = 465203) B465203
theorem B310155 : Blo 307833 310155 := bstep (se 1 (by rfl) ⟨232616, by rfl⟩ : syracuseStep 310155 = 465233) B465233
theorem B310167 : Blo 307833 310167 := bstep (se 1 (by rfl) ⟨232625, by rfl⟩ : syracuseStep 310167 = 465251) B465251
theorem B310187 : Blo 307833 310187 := bstep (se 1 (by rfl) ⟨232640, by rfl⟩ : syracuseStep 310187 = 465281) B465281
theorem B310199 : Blo 307833 310199 := bstep (se 1 (by rfl) ⟨232649, by rfl⟩ : syracuseStep 310199 = 465299) B465299
theorem B310219 : Blo 307833 310219 := bstep (se 1 (by rfl) ⟨232664, by rfl⟩ : syracuseStep 310219 = 465329) B465329
theorem B310231 : Blo 307833 310231 := bstep (se 1 (by rfl) ⟨232673, by rfl⟩ : syracuseStep 310231 = 465347) B465347
theorem B1326041 : Blo 307833 1326041 := bstep (se 2 (by rfl) ⟨497265, by rfl⟩ : syracuseStep 1326041 = 994531) B994531
theorem B310251 : Blo 307833 310251 := bstep (se 1 (by rfl) ⟨232688, by rfl⟩ : syracuseStep 310251 = 465377) B465377
theorem B310263 : Blo 307833 310263 := bstep (se 1 (by rfl) ⟨232697, by rfl⟩ : syracuseStep 310263 = 465395) B465395
theorem B310283 : Blo 307833 310283 := bstep (se 1 (by rfl) ⟨232712, by rfl⟩ : syracuseStep 310283 = 465425) B465425
theorem B310295 : Blo 307833 310295 := bstep (se 1 (by rfl) ⟨232721, by rfl⟩ : syracuseStep 310295 = 465443) B465443
theorem B310315 : Blo 307833 310315 := bstep (se 1 (by rfl) ⟨232736, by rfl⟩ : syracuseStep 310315 = 465473) B465473
theorem B310327 : Blo 307833 310327 := bstep (se 1 (by rfl) ⟨232745, by rfl⟩ : syracuseStep 310327 = 465491) B465491
theorem B310347 : Blo 307833 310347 := bstep (se 1 (by rfl) ⟨232760, by rfl⟩ : syracuseStep 310347 = 465521) B465521
theorem B310359 : Blo 307833 310359 := bstep (se 1 (by rfl) ⟨232769, by rfl⟩ : syracuseStep 310359 = 465539) B465539
theorem B310379 : Blo 307833 310379 := bstep (se 1 (by rfl) ⟨232784, by rfl⟩ : syracuseStep 310379 = 465569) B465569
theorem B310391 : Blo 307833 310391 := bstep (se 1 (by rfl) ⟨232793, by rfl⟩ : syracuseStep 310391 = 465587) B465587
theorem B310411 : Blo 307833 310411 := bstep (se 1 (by rfl) ⟨232808, by rfl⟩ : syracuseStep 310411 = 465617) B465617
theorem B310423 : Blo 307833 310423 := bstep (se 1 (by rfl) ⟨232817, by rfl⟩ : syracuseStep 310423 = 465635) B465635
theorem B310443 : Blo 307833 310443 := bstep (se 1 (by rfl) ⟨232832, by rfl⟩ : syracuseStep 310443 = 465665) B465665
theorem B310455 : Blo 307833 310455 := bstep (se 1 (by rfl) ⟨232841, by rfl⟩ : syracuseStep 310455 = 465683) B465683
theorem B310475 : Blo 307833 310475 := bstep (se 1 (by rfl) ⟨232856, by rfl⟩ : syracuseStep 310475 = 465713) B465713
theorem B310487 : Blo 307833 310487 := bstep (se 1 (by rfl) ⟨232865, by rfl⟩ : syracuseStep 310487 = 465731) B465731
theorem B310507 : Blo 307833 310507 := bstep (se 1 (by rfl) ⟨232880, by rfl⟩ : syracuseStep 310507 = 465761) B465761
theorem B310519 : Blo 307833 310519 := bstep (se 1 (by rfl) ⟨232889, by rfl⟩ : syracuseStep 310519 = 465779) B465779
theorem B310539 : Blo 307833 310539 := bstep (se 1 (by rfl) ⟨232904, by rfl⟩ : syracuseStep 310539 = 465809) B465809
theorem B310551 : Blo 307833 310551 := bstep (se 1 (by rfl) ⟨232913, by rfl⟩ : syracuseStep 310551 = 465827) B465827
theorem B310571 : Blo 307833 310571 := bstep (se 1 (by rfl) ⟨232928, by rfl⟩ : syracuseStep 310571 = 465857) B465857
theorem B310583 : Blo 307833 310583 := bstep (se 1 (by rfl) ⟨232937, by rfl⟩ : syracuseStep 310583 = 465875) B465875
theorem B1326401 : Blo 307833 1326401 := bstep (se 2 (by rfl) ⟨497400, by rfl⟩ : syracuseStep 1326401 = 994801) B994801
theorem B310603 : Blo 307833 310603 := bstep (se 1 (by rfl) ⟨232952, by rfl⟩ : syracuseStep 310603 = 465905) B465905
theorem B310615 : Blo 307833 310615 := bstep (se 1 (by rfl) ⟨232961, by rfl⟩ : syracuseStep 310615 = 465923) B465923
theorem B310635 : Blo 307833 310635 := bstep (se 1 (by rfl) ⟨232976, by rfl⟩ : syracuseStep 310635 = 465953) B465953
theorem B310647 : Blo 307833 310647 := bstep (se 1 (by rfl) ⟨232985, by rfl⟩ : syracuseStep 310647 = 465971) B465971
theorem B310667 : Blo 307833 310667 := bstep (se 1 (by rfl) ⟨233000, by rfl⟩ : syracuseStep 310667 = 466001) B466001
theorem B310679 : Blo 307833 310679 := bstep (se 1 (by rfl) ⟨233009, by rfl⟩ : syracuseStep 310679 = 466019) B466019
theorem B310699 : Blo 307833 310699 := bstep (se 1 (by rfl) ⟨233024, by rfl⟩ : syracuseStep 310699 = 466049) B466049
theorem B310711 : Blo 307833 310711 := bstep (se 1 (by rfl) ⟨233033, by rfl⟩ : syracuseStep 310711 = 466067) B466067
theorem B310731 : Blo 307833 310731 := bstep (se 1 (by rfl) ⟨233048, by rfl⟩ : syracuseStep 310731 = 466097) B466097
theorem B310743 : Blo 307833 310743 := bstep (se 1 (by rfl) ⟨233057, by rfl⟩ : syracuseStep 310743 = 466115) B466115
theorem B310763 : Blo 307833 310763 := bstep (se 1 (by rfl) ⟨233072, by rfl⟩ : syracuseStep 310763 = 466145) B466145
theorem B310775 : Blo 307833 310775 := bstep (se 1 (by rfl) ⟨233081, by rfl⟩ : syracuseStep 310775 = 466163) B466163
theorem B310795 : Blo 307833 310795 := bstep (se 1 (by rfl) ⟨233096, by rfl⟩ : syracuseStep 310795 = 466193) B466193
theorem B310807 : Blo 307833 310807 := bstep (se 1 (by rfl) ⟨233105, by rfl⟩ : syracuseStep 310807 = 466211) B466211
theorem B310827 : Blo 307833 310827 := bstep (se 1 (by rfl) ⟨233120, by rfl⟩ : syracuseStep 310827 = 466241) B466241
theorem B310839 : Blo 307833 310839 := bstep (se 1 (by rfl) ⟨233129, by rfl⟩ : syracuseStep 310839 = 466259) B466259
theorem B310859 : Blo 307833 310859 := bstep (se 1 (by rfl) ⟨233144, by rfl⟩ : syracuseStep 310859 = 466289) B466289
theorem B310871 : Blo 307833 310871 := bstep (se 1 (by rfl) ⟨233153, by rfl⟩ : syracuseStep 310871 = 466307) B466307
theorem B310891 : Blo 307833 310891 := bstep (se 1 (by rfl) ⟨233168, by rfl⟩ : syracuseStep 310891 = 466337) B466337
theorem B310903 : Blo 307833 310903 := bstep (se 1 (by rfl) ⟨233177, by rfl⟩ : syracuseStep 310903 = 466355) B466355
theorem B310923 : Blo 307833 310923 := bstep (se 1 (by rfl) ⟨233192, by rfl⟩ : syracuseStep 310923 = 466385) B466385
theorem B310935 : Blo 307833 310935 := bstep (se 1 (by rfl) ⟨233201, by rfl⟩ : syracuseStep 310935 = 466403) B466403
theorem B310955 : Blo 307833 310955 := bstep (se 1 (by rfl) ⟨233216, by rfl⟩ : syracuseStep 310955 = 466433) B466433
theorem B310967 : Blo 307833 310967 := bstep (se 1 (by rfl) ⟨233225, by rfl⟩ : syracuseStep 310967 = 466451) B466451
theorem B310987 : Blo 307833 310987 := bstep (se 1 (by rfl) ⟨233240, by rfl⟩ : syracuseStep 310987 = 466481) B466481
theorem B310999 : Blo 307833 310999 := bstep (se 1 (by rfl) ⟨233249, by rfl⟩ : syracuseStep 310999 = 466499) B466499
theorem B311019 : Blo 307833 311019 := bstep (se 1 (by rfl) ⟨233264, by rfl⟩ : syracuseStep 311019 = 466529) B466529
theorem B638707 : Blo 307833 638707 := bstep (se 1 (by rfl) ⟨479030, by rfl⟩ : syracuseStep 638707 = 958061) B958061
theorem B311031 : Blo 307833 311031 := bstep (se 1 (by rfl) ⟨233273, by rfl⟩ : syracuseStep 311031 = 466547) B466547
theorem B311051 : Blo 307833 311051 := bstep (se 1 (by rfl) ⟨233288, by rfl⟩ : syracuseStep 311051 = 466577) B466577
theorem B311063 : Blo 307833 311063 := bstep (se 1 (by rfl) ⟨233297, by rfl⟩ : syracuseStep 311063 = 466595) B466595
theorem B311083 : Blo 307833 311083 := bstep (se 1 (by rfl) ⟨233312, by rfl⟩ : syracuseStep 311083 = 466625) B466625
theorem B311095 : Blo 307833 311095 := bstep (se 1 (by rfl) ⟨233321, by rfl⟩ : syracuseStep 311095 = 466643) B466643
theorem B311115 : Blo 307833 311115 := bstep (se 1 (by rfl) ⟨233336, by rfl⟩ : syracuseStep 311115 = 466673) B466673
theorem B311127 : Blo 307833 311127 := bstep (se 1 (by rfl) ⟨233345, by rfl⟩ : syracuseStep 311127 = 466691) B466691
theorem B311147 : Blo 307833 311147 := bstep (se 1 (by rfl) ⟨233360, by rfl⟩ : syracuseStep 311147 = 466721) B466721
theorem B311159 : Blo 307833 311159 := bstep (se 1 (by rfl) ⟨233369, by rfl⟩ : syracuseStep 311159 = 466739) B466739
theorem B311179 : Blo 307833 311179 := bstep (se 1 (by rfl) ⟨233384, by rfl⟩ : syracuseStep 311179 = 466769) B466769
theorem B311191 : Blo 307833 311191 := bstep (se 1 (by rfl) ⟨233393, by rfl⟩ : syracuseStep 311191 = 466787) B466787
theorem B311211 : Blo 307833 311211 := bstep (se 1 (by rfl) ⟨233408, by rfl⟩ : syracuseStep 311211 = 466817) B466817
theorem B311223 : Blo 307833 311223 := bstep (se 1 (by rfl) ⟨233417, by rfl⟩ : syracuseStep 311223 = 466835) B466835
theorem B311243 : Blo 307833 311243 := bstep (se 1 (by rfl) ⟨233432, by rfl⟩ : syracuseStep 311243 = 466865) B466865
theorem B311255 : Blo 307833 311255 := bstep (se 1 (by rfl) ⟨233441, by rfl⟩ : syracuseStep 311255 = 466883) B466883
theorem B311275 : Blo 307833 311275 := bstep (se 1 (by rfl) ⟨233456, by rfl⟩ : syracuseStep 311275 = 466913) B466913
theorem B311287 : Blo 307833 311287 := bstep (se 1 (by rfl) ⟨233465, by rfl⟩ : syracuseStep 311287 = 466931) B466931
theorem B311307 : Blo 307833 311307 := bstep (se 1 (by rfl) ⟨233480, by rfl⟩ : syracuseStep 311307 = 466961) B466961
theorem B311319 : Blo 307833 311319 := bstep (se 1 (by rfl) ⟨233489, by rfl⟩ : syracuseStep 311319 = 466979) B466979
theorem B311339 : Blo 307833 311339 := bstep (se 1 (by rfl) ⟨233504, by rfl⟩ : syracuseStep 311339 = 467009) B467009
theorem B311351 : Blo 307833 311351 := bstep (se 1 (by rfl) ⟨233513, by rfl⟩ : syracuseStep 311351 = 467027) B467027
theorem B311371 : Blo 307833 311371 := bstep (se 1 (by rfl) ⟨233528, by rfl⟩ : syracuseStep 311371 = 467057) B467057
theorem B311383 : Blo 307833 311383 := bstep (se 1 (by rfl) ⟨233537, by rfl⟩ : syracuseStep 311383 = 467075) B467075
theorem B2343005 : Blo 307833 2343005 := bstep (se 3 (by rfl) ⟨439313, by rfl⟩ : syracuseStep 2343005 = 878627) B878627
theorem B311403 : Blo 307833 311403 := bstep (se 1 (by rfl) ⟨233552, by rfl⟩ : syracuseStep 311403 = 467105) B467105
theorem B311415 : Blo 307833 311415 := bstep (se 1 (by rfl) ⟨233561, by rfl⟩ : syracuseStep 311415 = 467123) B467123
theorem B311435 : Blo 307833 311435 := bstep (se 1 (by rfl) ⟨233576, by rfl⟩ : syracuseStep 311435 = 467153) B467153
theorem B311447 : Blo 307833 311447 := bstep (se 1 (by rfl) ⟨233585, by rfl⟩ : syracuseStep 311447 = 467171) B467171
theorem B311467 : Blo 307833 311467 := bstep (se 1 (by rfl) ⟨233600, by rfl⟩ : syracuseStep 311467 = 467201) B467201
theorem B311479 : Blo 307833 311479 := bstep (se 1 (by rfl) ⟨233609, by rfl⟩ : syracuseStep 311479 = 467219) B467219
theorem B311499 : Blo 307833 311499 := bstep (se 1 (by rfl) ⟨233624, by rfl⟩ : syracuseStep 311499 = 467249) B467249
theorem B311511 : Blo 307833 311511 := bstep (se 1 (by rfl) ⟨233633, by rfl⟩ : syracuseStep 311511 = 467267) B467267
theorem B311531 : Blo 307833 311531 := bstep (se 1 (by rfl) ⟨233648, by rfl⟩ : syracuseStep 311531 = 467297) B467297
theorem B311543 : Blo 307833 311543 := bstep (se 1 (by rfl) ⟨233657, by rfl⟩ : syracuseStep 311543 = 467315) B467315
theorem B311563 : Blo 307833 311563 := bstep (se 1 (by rfl) ⟨233672, by rfl⟩ : syracuseStep 311563 = 467345) B467345
theorem B311575 : Blo 307833 311575 := bstep (se 1 (by rfl) ⟨233681, by rfl⟩ : syracuseStep 311575 = 467363) B467363
theorem B311595 : Blo 307833 311595 := bstep (se 1 (by rfl) ⟨233696, by rfl⟩ : syracuseStep 311595 = 467393) B467393
theorem B311607 : Blo 307833 311607 := bstep (se 1 (by rfl) ⟨233705, by rfl⟩ : syracuseStep 311607 = 467411) B467411
theorem B311627 : Blo 307833 311627 := bstep (se 1 (by rfl) ⟨233720, by rfl⟩ : syracuseStep 311627 = 467441) B467441
theorem B311639 : Blo 307833 311639 := bstep (se 1 (by rfl) ⟨233729, by rfl⟩ : syracuseStep 311639 = 467459) B467459
theorem B311659 : Blo 307833 311659 := bstep (se 1 (by rfl) ⟨233744, by rfl⟩ : syracuseStep 311659 = 467489) B467489
theorem B311671 : Blo 307833 311671 := bstep (se 1 (by rfl) ⟨233753, by rfl⟩ : syracuseStep 311671 = 467507) B467507
theorem B311691 : Blo 307833 311691 := bstep (se 1 (by rfl) ⟨233768, by rfl⟩ : syracuseStep 311691 = 467537) B467537
theorem B835991 : Blo 307833 835991 := bstep (se 1 (by rfl) ⟨626993, by rfl⟩ : syracuseStep 835991 = 1253987) B1253987
theorem B311703 : Blo 307833 311703 := bstep (se 1 (by rfl) ⟨233777, by rfl⟩ : syracuseStep 311703 = 467555) B467555
theorem B311723 : Blo 307833 311723 := bstep (se 1 (by rfl) ⟨233792, by rfl⟩ : syracuseStep 311723 = 467585) B467585
theorem B311735 : Blo 307833 311735 := bstep (se 1 (by rfl) ⟨233801, by rfl⟩ : syracuseStep 311735 = 467603) B467603
theorem B311755 : Blo 307833 311755 := bstep (se 1 (by rfl) ⟨233816, by rfl⟩ : syracuseStep 311755 = 467633) B467633
theorem B311767 : Blo 307833 311767 := bstep (se 1 (by rfl) ⟨233825, by rfl⟩ : syracuseStep 311767 = 467651) B467651
theorem B311787 : Blo 307833 311787 := bstep (se 1 (by rfl) ⟨233840, by rfl⟩ : syracuseStep 311787 = 467681) B467681
theorem B311799 : Blo 307833 311799 := bstep (se 1 (by rfl) ⟨233849, by rfl⟩ : syracuseStep 311799 = 467699) B467699
theorem B311819 : Blo 307833 311819 := bstep (se 1 (by rfl) ⟨233864, by rfl⟩ : syracuseStep 311819 = 467729) B467729
theorem B311831 : Blo 307833 311831 := bstep (se 1 (by rfl) ⟨233873, by rfl⟩ : syracuseStep 311831 = 467747) B467747
theorem B1983041 : Blo 307833 1983041 := bstep (se 2 (by rfl) ⟨743640, by rfl⟩ : syracuseStep 1983041 = 1487281) B1487281
theorem B705779 : Blo 307833 705779 := bstep (se 1 (by rfl) ⟨529334, by rfl⟩ : syracuseStep 705779 = 1058669) B1058669
theorem B1885457 : Blo 307833 1885457 := bstep (se 2 (by rfl) ⟨707046, by rfl⟩ : syracuseStep 1885457 = 1414093) B1414093
theorem B836887 : Blo 307833 836887 := bstep (se 1 (by rfl) ⟨627665, by rfl⟩ : syracuseStep 836887 = 1255331) B1255331
theorem B378379 : Blo 307833 378379 := bstep (se 1 (by rfl) ⟨283784, by rfl⟩ : syracuseStep 378379 = 567569) B567569
theorem B443927 : Blo 307833 443927 := bstep (se 1 (by rfl) ⟨332945, by rfl⟩ : syracuseStep 443927 = 665891) B665891
theorem B2148113 : Blo 307833 2148113 := bstep (se 2 (by rfl) ⟨805542, by rfl⟩ : syracuseStep 2148113 = 1611085) B1611085
theorem B4507571 : Blo 307833 4507571 := bstep (se 1 (by rfl) ⟨3380678, by rfl⟩ : syracuseStep 4507571 = 6761357) B6761357
theorem B346315 : Blo 307833 346315 := bstep (se 1 (by rfl) ⟨259736, by rfl⟩ : syracuseStep 346315 = 519473) B519473
theorem B346423 : Blo 307833 346423 := bstep (se 1 (by rfl) ⟨259817, by rfl⟩ : syracuseStep 346423 = 519635) B519635
theorem B346603 : Blo 307833 346603 := bstep (se 1 (by rfl) ⟨259952, by rfl⟩ : syracuseStep 346603 = 519905) B519905
theorem B346711 : Blo 307833 346711 := bstep (se 1 (by rfl) ⟨260033, by rfl⟩ : syracuseStep 346711 = 520067) B520067
theorem B707201 : Blo 307833 707201 := bstep (se 2 (by rfl) ⟨265200, by rfl⟩ : syracuseStep 707201 = 530401) B530401
theorem B346891 : Blo 307833 346891 := bstep (se 1 (by rfl) ⟨260168, by rfl⟩ : syracuseStep 346891 = 520337) B520337
theorem B3164993 : Blo 307833 3164993 := bstep (se 2 (by rfl) ⟨1186872, by rfl⟩ : syracuseStep 3164993 = 2373745) B2373745
theorem B346999 : Blo 307833 346999 := bstep (se 1 (by rfl) ⟨260249, by rfl⟩ : syracuseStep 346999 = 520499) B520499
theorem B1330141 : Blo 307833 1330141 := bstep (se 3 (by rfl) ⟨249401, by rfl⟩ : syracuseStep 1330141 = 498803) B498803
theorem B347179 : Blo 307833 347179 := bstep (se 1 (by rfl) ⟨260384, by rfl⟩ : syracuseStep 347179 = 520769) B520769
theorem B347287 : Blo 307833 347287 := bstep (se 1 (by rfl) ⟨260465, by rfl⟩ : syracuseStep 347287 = 520931) B520931
theorem B445655 : Blo 307833 445655 := bstep (se 1 (by rfl) ⟨334241, by rfl⟩ : syracuseStep 445655 = 668483) B668483
theorem B4443437 : Blo 307833 4443437 := bstep (se 3 (by rfl) ⟨833144, by rfl⟩ : syracuseStep 4443437 = 1666289) B1666289
theorem B347467 : Blo 307833 347467 := bstep (se 1 (by rfl) ⟨260600, by rfl⟩ : syracuseStep 347467 = 521201) B521201
theorem B347575 : Blo 307833 347575 := bstep (se 1 (by rfl) ⟨260681, by rfl⟩ : syracuseStep 347575 = 521363) B521363
theorem B839105 : Blo 307833 839105 := bstep (se 2 (by rfl) ⟨314664, by rfl⟩ : syracuseStep 839105 = 629329) B629329
theorem B347755 : Blo 307833 347755 := bstep (se 1 (by rfl) ⟨260816, by rfl⟩ : syracuseStep 347755 = 521633) B521633
theorem B347863 : Blo 307833 347863 := bstep (se 1 (by rfl) ⟨260897, by rfl⟩ : syracuseStep 347863 = 521795) B521795
theorem B348043 : Blo 307833 348043 := bstep (se 1 (by rfl) ⟨261032, by rfl⟩ : syracuseStep 348043 = 522065) B522065
theorem B348151 : Blo 307833 348151 := bstep (se 1 (by rfl) ⟨261113, by rfl⟩ : syracuseStep 348151 = 522227) B522227
theorem B10047557 : Blo 307833 10047557 := bstep (se 4 (by rfl) ⟨941958, by rfl⟩ : syracuseStep 10047557 = 1883917) B1883917
theorem B1560707 : Blo 307833 1560707 := bstep (se 1 (by rfl) ⟨1170530, by rfl⟩ : syracuseStep 1560707 = 2341061) B2341061
theorem B348331 : Blo 307833 348331 := bstep (se 1 (by rfl) ⟨261248, by rfl⟩ : syracuseStep 348331 = 522497) B522497
theorem B1331473 : Blo 307833 1331473 := bstep (se 2 (by rfl) ⟨499302, by rfl⟩ : syracuseStep 1331473 = 998605) B998605
theorem B348439 : Blo 307833 348439 := bstep (se 1 (by rfl) ⟨261329, by rfl⟩ : syracuseStep 348439 = 522659) B522659
theorem B315787 : Blo 307833 315787 := bstep (se 1 (by rfl) ⟨236840, by rfl⟩ : syracuseStep 315787 = 473681) B473681
theorem B348619 : Blo 307833 348619 := bstep (se 1 (by rfl) ⟨261464, by rfl⟩ : syracuseStep 348619 = 522929) B522929
theorem B1364441 : Blo 307833 1364441 := bstep (se 2 (by rfl) ⟨511665, by rfl⟩ : syracuseStep 1364441 = 1023331) B1023331
theorem B348727 : Blo 307833 348727 := bstep (se 1 (by rfl) ⟨261545, by rfl⟩ : syracuseStep 348727 = 523091) B523091
theorem B348907 : Blo 307833 348907 := bstep (se 1 (by rfl) ⟨261680, by rfl⟩ : syracuseStep 348907 = 523361) B523361
theorem B349015 : Blo 307833 349015 := bstep (se 1 (by rfl) ⟨261761, by rfl⟩ : syracuseStep 349015 = 523523) B523523
theorem B938945 : Blo 307833 938945 := bstep (se 2 (by rfl) ⟨352104, by rfl⟩ : syracuseStep 938945 = 704209) B704209
theorem B349195 : Blo 307833 349195 := bstep (se 1 (by rfl) ⟨261896, by rfl⟩ : syracuseStep 349195 = 523793) B523793
theorem B2642989 : Blo 307833 2642989 := bstep (se 3 (by rfl) ⟨495560, by rfl⟩ : syracuseStep 2642989 = 991121) B991121
theorem B349303 : Blo 307833 349303 := bstep (se 1 (by rfl) ⟨261977, by rfl⟩ : syracuseStep 349303 = 523955) B523955
theorem B349483 : Blo 307833 349483 := bstep (se 1 (by rfl) ⟨262112, by rfl⟩ : syracuseStep 349483 = 524225) B524225
theorem B1758509 : Blo 307833 1758509 := bstep (se 3 (by rfl) ⟨329720, by rfl⟩ : syracuseStep 1758509 = 659441) B659441
theorem B349591 : Blo 307833 349591 := bstep (se 1 (by rfl) ⟨262193, by rfl⟩ : syracuseStep 349591 = 524387) B524387
theorem B710039 : Blo 307833 710039 := bstep (se 1 (by rfl) ⟨532529, by rfl⟩ : syracuseStep 710039 = 1065059) B1065059
theorem B349771 : Blo 307833 349771 := bstep (se 1 (by rfl) ⟨262328, by rfl⟩ : syracuseStep 349771 = 524657) B524657
theorem B1988189 : Blo 307833 1988189 := bstep (se 3 (by rfl) ⟨372785, by rfl⟩ : syracuseStep 1988189 = 745571) B745571
theorem B349879 : Blo 307833 349879 := bstep (se 1 (by rfl) ⟨262409, by rfl⟩ : syracuseStep 349879 = 524819) B524819
theorem B350059 : Blo 307833 350059 := bstep (se 1 (by rfl) ⟨262544, by rfl⟩ : syracuseStep 350059 = 525089) B525089
theorem B350167 : Blo 307833 350167 := bstep (se 1 (by rfl) ⟨262625, by rfl⟩ : syracuseStep 350167 = 525251) B525251
theorem B1595467 : Blo 307833 1595467 := bstep (se 1 (by rfl) ⟨1196600, by rfl⟩ : syracuseStep 1595467 = 2393201) B2393201
theorem B350347 : Blo 307833 350347 := bstep (se 1 (by rfl) ⟨262760, by rfl⟩ : syracuseStep 350347 = 525521) B525521
theorem B2250929 : Blo 307833 2250929 := bstep (se 2 (by rfl) ⟨844098, by rfl⟩ : syracuseStep 2250929 = 1688197) B1688197
theorem B350455 : Blo 307833 350455 := bstep (se 1 (by rfl) ⟨262841, by rfl⟩ : syracuseStep 350455 = 525683) B525683
theorem B2644325 : Blo 307833 2644325 := bstep (se 4 (by rfl) ⟨247905, by rfl⟩ : syracuseStep 2644325 = 495811) B495811
theorem B350635 : Blo 307833 350635 := bstep (se 1 (by rfl) ⟨262976, by rfl⟩ : syracuseStep 350635 = 525953) B525953
theorem B1169923 : Blo 307833 1169923 := bstep (se 1 (by rfl) ⟨877442, by rfl⟩ : syracuseStep 1169923 = 1754885) B1754885
theorem B350743 : Blo 307833 350743 := bstep (se 1 (by rfl) ⟨263057, by rfl⟩ : syracuseStep 350743 = 526115) B526115
theorem B2382371 : Blo 307833 2382371 := bstep (se 1 (by rfl) ⟨1786778, by rfl⟩ : syracuseStep 2382371 = 3573557) B3573557
theorem B744025 : Blo 307833 744025 := bstep (se 2 (by rfl) ⟨279009, by rfl⟩ : syracuseStep 744025 = 558019) B558019
theorem B1170227 : Blo 307833 1170227 := bstep (se 1 (by rfl) ⟨877670, by rfl⟩ : syracuseStep 1170227 = 1755341) B1755341
theorem B1039283 : Blo 307833 1039283 := bstep (se 1 (by rfl) ⟨779462, by rfl⟩ : syracuseStep 1039283 = 1558925) B1558925
theorem B4545629 : Blo 307833 4545629 := bstep (se 3 (by rfl) ⟨852305, by rfl⟩ : syracuseStep 4545629 = 1704611) B1704611
theorem B1039553 : Blo 307833 1039553 := bstep (se 2 (by rfl) ⟨389832, by rfl⟩ : syracuseStep 1039553 = 779665) B779665
theorem B941401 : Blo 307833 941401 := bstep (se 2 (by rfl) ⟨353025, by rfl⟩ : syracuseStep 941401 = 706051) B706051
theorem B1170881 : Blo 307833 1170881 := bstep (se 2 (by rfl) ⟨439080, by rfl⟩ : syracuseStep 1170881 = 878161) B878161
theorem B351703 : Blo 307833 351703 := bstep (se 1 (by rfl) ⟨263777, by rfl⟩ : syracuseStep 351703 = 527555) B527555
theorem B3333707 : Blo 307833 3333707 := bstep (se 1 (by rfl) ⟨2500280, by rfl⟩ : syracuseStep 3333707 = 5000561) B5000561
theorem B1760899 : Blo 307833 1760899 := bstep (se 1 (by rfl) ⟨1320674, by rfl⟩ : syracuseStep 1760899 = 2641349) B2641349
theorem B1040093 : Blo 307833 1040093 := bstep (se 3 (by rfl) ⟨195017, by rfl⟩ : syracuseStep 1040093 = 390035) B390035
theorem B1564433 : Blo 307833 1564433 := bstep (se 2 (by rfl) ⟨586662, by rfl⟩ : syracuseStep 1564433 = 1173325) B1173325
theorem B1564595 : Blo 307833 1564595 := bstep (se 1 (by rfl) ⟨1173446, by rfl⟩ : syracuseStep 1564595 = 2346893) B2346893
theorem B876737 : Blo 307833 876737 := bstep (se 2 (by rfl) ⟨328776, by rfl⟩ : syracuseStep 876737 = 657553) B657553
theorem B942301 : Blo 307833 942301 := bstep (se 3 (by rfl) ⟨176681, by rfl⟩ : syracuseStep 942301 = 353363) B353363
theorem B876851 : Blo 307833 876851 := bstep (se 1 (by rfl) ⟨657638, by rfl⟩ : syracuseStep 876851 = 1315277) B1315277
theorem B1761857 : Blo 307833 1761857 := bstep (se 2 (by rfl) ⟨660696, by rfl⟩ : syracuseStep 1761857 = 1321393) B1321393
theorem B1172141 : Blo 307833 1172141 := bstep (se 3 (by rfl) ⟨219776, by rfl⟩ : syracuseStep 1172141 = 439553) B439553
theorem B746177 : Blo 307833 746177 := bstep (se 2 (by rfl) ⟨279816, by rfl⟩ : syracuseStep 746177 = 559633) B559633
theorem B1172171 : Blo 307833 1172171 := bstep (se 1 (by rfl) ⟨879128, by rfl⟩ : syracuseStep 1172171 = 1758257) B1758257
theorem B746263 : Blo 307833 746263 := bstep (se 1 (by rfl) ⟨559697, by rfl⟩ : syracuseStep 746263 = 1119395) B1119395
theorem B8971073 : Blo 307833 8971073 := bstep (se 2 (by rfl) ⟨3364152, by rfl⟩ : syracuseStep 8971073 = 6728305) B6728305
theorem B2810699 : Blo 307833 2810699 := bstep (se 1 (by rfl) ⟨2108024, by rfl⟩ : syracuseStep 2810699 = 4216049) B4216049
theorem B1041227 : Blo 307833 1041227 := bstep (se 1 (by rfl) ⟨780920, by rfl⟩ : syracuseStep 1041227 = 1561841) B1561841
theorem B1041497 : Blo 307833 1041497 := bstep (se 2 (by rfl) ⟨390561, by rfl⟩ : syracuseStep 1041497 = 781123) B781123
theorem B1205441 : Blo 307833 1205441 := bstep (se 2 (by rfl) ⟨452040, by rfl⟩ : syracuseStep 1205441 = 904081) B904081
theorem B1336621 : Blo 307833 1336621 := bstep (se 3 (by rfl) ⟨250616, by rfl⟩ : syracuseStep 1336621 = 501233) B501233
theorem B1172825 : Blo 307833 1172825 := bstep (se 2 (by rfl) ⟨439809, by rfl⟩ : syracuseStep 1172825 = 879619) B879619
theorem B1598899 : Blo 307833 1598899 := bstep (se 1 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 1598899 = 2398349) B2398349
theorem B779827 : Blo 307833 779827 := bstep (se 1 (by rfl) ⟨584870, by rfl⟩ : syracuseStep 779827 = 1169741) B1169741
theorem B1009217 : Blo 307833 1009217 := bstep (se 2 (by rfl) ⟨378456, by rfl⟩ : syracuseStep 1009217 = 756913) B756913
theorem B2385539 : Blo 307833 2385539 := bstep (se 1 (by rfl) ⟨1789154, by rfl⟩ : syracuseStep 2385539 = 3578309) B3578309
theorem B1173143 : Blo 307833 1173143 := bstep (se 1 (by rfl) ⟨879857, by rfl⟩ : syracuseStep 1173143 = 1759715) B1759715
theorem B779969 : Blo 307833 779969 := bstep (se 2 (by rfl) ⟨292488, by rfl⟩ : syracuseStep 779969 = 584977) B584977
theorem B1042199 : Blo 307833 1042199 := bstep (se 1 (by rfl) ⟨781649, by rfl⟩ : syracuseStep 1042199 = 1563299) B1563299
theorem B1566539 : Blo 307833 1566539 := bstep (se 1 (by rfl) ⟨1174904, by rfl⟩ : syracuseStep 1566539 = 2349809) B2349809
theorem B1992599 : Blo 307833 1992599 := bstep (se 1 (by rfl) ⟨1494449, by rfl⟩ : syracuseStep 1992599 = 2988899) B2988899
theorem B12642227 : Blo 307833 12642227 := bstep (se 1 (by rfl) ⟨9481670, by rfl⟩ : syracuseStep 12642227 = 18963341) B18963341
theorem B2516953 : Blo 307833 2516953 := bstep (se 2 (by rfl) ⟨943857, by rfl⟩ : syracuseStep 2516953 = 1887715) B1887715
theorem B7596101 : Blo 307833 7596101 := bstep (se 4 (by rfl) ⟨712134, by rfl⟩ : syracuseStep 7596101 = 1424269) B1424269
theorem B1042739 : Blo 307833 1042739 := bstep (se 1 (by rfl) ⟨782054, by rfl⟩ : syracuseStep 1042739 = 1564109) B1564109
theorem B1173811 : Blo 307833 1173811 := bstep (se 1 (by rfl) ⟨880358, by rfl⟩ : syracuseStep 1173811 = 1760717) B1760717
theorem B1043009 : Blo 307833 1043009 := bstep (se 2 (by rfl) ⟨391128, by rfl⟩ : syracuseStep 1043009 = 782257) B782257
theorem B2255435 : Blo 307833 2255435 := bstep (se 1 (by rfl) ⟨1691576, by rfl⟩ : syracuseStep 2255435 = 3383153) B3383153
theorem B715481 : Blo 307833 715481 := bstep (se 2 (by rfl) ⟨268305, by rfl⟩ : syracuseStep 715481 = 536611) B536611
theorem B781235 : Blo 307833 781235 := bstep (se 1 (by rfl) ⟨585926, by rfl⟩ : syracuseStep 781235 = 1171853) B1171853
theorem B584651 : Blo 307833 584651 := bstep (se 1 (by rfl) ⟨438488, by rfl⟩ : syracuseStep 584651 = 876977) B876977
theorem B420823 : Blo 307833 420823 := bstep (se 1 (by rfl) ⟨315617, by rfl⟩ : syracuseStep 420823 = 631235) B631235
theorem B1043549 : Blo 307833 1043549 := bstep (se 3 (by rfl) ⟨195665, by rfl⟩ : syracuseStep 1043549 = 391331) B391331
theorem B584833 : Blo 307833 584833 := bstep (se 2 (by rfl) ⟨219312, by rfl⟩ : syracuseStep 584833 = 438625) B438625
theorem B879767 : Blo 307833 879767 := bstep (se 1 (by rfl) ⟨659825, by rfl⟩ : syracuseStep 879767 = 1319651) B1319651
theorem B2223395 : Blo 307833 2223395 := bstep (se 1 (by rfl) ⟨1667546, by rfl⟩ : syracuseStep 2223395 = 3335093) B3335093
theorem B781771 : Blo 307833 781771 := bstep (se 1 (by rfl) ⟨586328, by rfl⟩ : syracuseStep 781771 = 1172657) B1172657
theorem B1175057 : Blo 307833 1175057 := bstep (se 2 (by rfl) ⟨440646, by rfl⟩ : syracuseStep 1175057 = 881293) B881293
theorem B585281 : Blo 307833 585281 := bstep (se 2 (by rfl) ⟨219480, by rfl⟩ : syracuseStep 585281 = 438961) B438961
theorem B1568321 : Blo 307833 1568321 := bstep (se 2 (by rfl) ⟨588120, by rfl⟩ : syracuseStep 1568321 = 1176241) B1176241
theorem B781913 : Blo 307833 781913 := bstep (se 2 (by rfl) ⟨293217, by rfl⟩ : syracuseStep 781913 = 586435) B586435
theorem B6942449 : Blo 307833 6942449 := bstep (se 2 (by rfl) ⟨2603418, by rfl⟩ : syracuseStep 6942449 = 5206837) B5206837
theorem B519959 : Blo 307833 519959 := bstep (se 1 (by rfl) ⟨389969, by rfl⟩ : syracuseStep 519959 = 779939) B779939
theorem B520087 : Blo 307833 520087 := bstep (se 1 (by rfl) ⟨390065, by rfl⟩ : syracuseStep 520087 = 780131) B780131
theorem B585623 : Blo 307833 585623 := bstep (se 1 (by rfl) ⟨439217, by rfl⟩ : syracuseStep 585623 = 878435) B878435
theorem B3371159 : Blo 307833 3371159 := bstep (se 1 (by rfl) ⟨2528369, by rfl⟩ : syracuseStep 3371159 = 5056739) B5056739
theorem B1044683 : Blo 307833 1044683 := bstep (se 1 (by rfl) ⟨783512, by rfl⟩ : syracuseStep 1044683 = 1567025) B1567025
theorem B1175755 : Blo 307833 1175755 := bstep (se 1 (by rfl) ⟨881816, by rfl⟩ : syracuseStep 1175755 = 1763633) B1763633
theorem B3371329 : Blo 307833 3371329 := bstep (se 2 (by rfl) ⟨1264248, by rfl⟩ : syracuseStep 3371329 = 2528497) B2528497
theorem B782743 : Blo 307833 782743 := bstep (se 1 (by rfl) ⟨587057, by rfl⟩ : syracuseStep 782743 = 1174115) B1174115
theorem B1044953 : Blo 307833 1044953 := bstep (se 2 (by rfl) ⟨391857, by rfl⟩ : syracuseStep 1044953 = 783715) B783715
theorem B1176029 : Blo 307833 1176029 := bstep (se 3 (by rfl) ⟨220505, by rfl⟩ : syracuseStep 1176029 = 441011) B441011
theorem B422411 : Blo 307833 422411 := bstep (se 1 (by rfl) ⟨316808, by rfl⟩ : syracuseStep 422411 = 633617) B633617
theorem B520715 : Blo 307833 520715 := bstep (se 1 (by rfl) ⟨390536, by rfl⟩ : syracuseStep 520715 = 781073) B781073
theorem B586291 : Blo 307833 586291 := bstep (se 1 (by rfl) ⟨439718, by rfl⟩ : syracuseStep 586291 = 879437) B879437
theorem B520843 : Blo 307833 520843 := bstep (se 1 (by rfl) ⟨390632, by rfl⟩ : syracuseStep 520843 = 781265) B781265
theorem B520985 : Blo 307833 520985 := bstep (se 2 (by rfl) ⟨195369, by rfl⟩ : syracuseStep 520985 = 390739) B390739
theorem B783179 : Blo 307833 783179 := bstep (se 1 (by rfl) ⟨587384, by rfl⟩ : syracuseStep 783179 = 1174769) B1174769
theorem B3240805 : Blo 307833 3240805 := bstep (se 4 (by rfl) ⟨303825, by rfl⟩ : syracuseStep 3240805 = 607651) B607651
theorem B521113 : Blo 307833 521113 := bstep (se 2 (by rfl) ⟨195417, by rfl⟩ : syracuseStep 521113 = 390835) B390835
theorem B4027315 : Blo 307833 4027315 := bstep (se 1 (by rfl) ⟨3020486, by rfl⟩ : syracuseStep 4027315 = 6040973) B6040973
theorem B390091 : Blo 307833 390091 := bstep (se 1 (by rfl) ⟨292568, by rfl⟩ : syracuseStep 390091 = 585137) B585137
theorem B586739 : Blo 307833 586739 := bstep (se 1 (by rfl) ⟨440054, by rfl⟩ : syracuseStep 586739 = 880109) B880109
theorem B586777 : Blo 307833 586777 := bstep (se 2 (by rfl) ⟨220041, by rfl⟩ : syracuseStep 586777 = 440083) B440083
theorem B3175499 : Blo 307833 3175499 := bstep (se 1 (by rfl) ⟨2381624, by rfl⟩ : syracuseStep 3175499 = 4763249) B4763249
theorem B1045655 : Blo 307833 1045655 := bstep (se 1 (by rfl) ⟨784241, by rfl⟩ : syracuseStep 1045655 = 1568483) B1568483
theorem B1176727 : Blo 307833 1176727 := bstep (se 1 (by rfl) ⟨882545, by rfl⟩ : syracuseStep 1176727 = 1765091) B1765091
theorem B783553 : Blo 307833 783553 := bstep (se 2 (by rfl) ⟨293832, by rfl⟩ : syracuseStep 783553 = 587665) B587665
theorem B3994829 : Blo 307833 3994829 := bstep (se 3 (by rfl) ⟨749030, by rfl⟩ : syracuseStep 3994829 = 1498061) B1498061
theorem B390359 : Blo 307833 390359 := bstep (se 1 (by rfl) ⟨292769, by rfl⟩ : syracuseStep 390359 = 585539) B585539
theorem B1766731 : Blo 307833 1766731 := bstep (se 1 (by rfl) ⟨1325048, by rfl⟩ : syracuseStep 1766731 = 2650097) B2650097
theorem B1996163 : Blo 307833 1996163 := bstep (se 1 (by rfl) ⟨1497122, by rfl⟩ : syracuseStep 1996163 = 2994245) B2994245
theorem B521687 : Blo 307833 521687 := bstep (se 1 (by rfl) ⟨391265, by rfl⟩ : syracuseStep 521687 = 782531) B782531
theorem B587225 : Blo 307833 587225 := bstep (se 2 (by rfl) ⟨220209, by rfl⟩ : syracuseStep 587225 = 440419) B440419
theorem B1570265 : Blo 307833 1570265 := bstep (se 2 (by rfl) ⟨588849, by rfl⟩ : syracuseStep 1570265 = 1177699) B1177699
theorem B2160145 : Blo 307833 2160145 := bstep (se 2 (by rfl) ⟨810054, by rfl⟩ : syracuseStep 2160145 = 1620109) B1620109
theorem B882227 : Blo 307833 882227 := bstep (se 1 (by rfl) ⟨661670, by rfl⟩ : syracuseStep 882227 = 1323341) B1323341
theorem B521815 : Blo 307833 521815 := bstep (se 1 (by rfl) ⟨391361, by rfl⟩ : syracuseStep 521815 = 782723) B782723
theorem B1767005 : Blo 307833 1767005 := bstep (se 3 (by rfl) ⟨331313, by rfl⟩ : syracuseStep 1767005 = 662627) B662627
theorem B1046195 : Blo 307833 1046195 := bstep (se 1 (by rfl) ⟨784646, by rfl⟩ : syracuseStep 1046195 = 1569293) B1569293
theorem B784151 : Blo 307833 784151 := bstep (se 1 (by rfl) ⟨588113, by rfl⟩ : syracuseStep 784151 = 1176227) B1176227
theorem B391063 : Blo 307833 391063 := bstep (se 1 (by rfl) ⟨293297, by rfl⟩ : syracuseStep 391063 = 586595) B586595
theorem B1177517 : Blo 307833 1177517 := bstep (se 3 (by rfl) ⟨220784, by rfl⟩ : syracuseStep 1177517 = 441569) B441569
theorem B1046465 : Blo 307833 1046465 := bstep (se 2 (by rfl) ⟨392424, by rfl⟩ : syracuseStep 1046465 = 784849) B784849
theorem B2586775 : Blo 307833 2586775 := bstep (se 1 (by rfl) ⟨1940081, by rfl⟩ : syracuseStep 2586775 = 3880163) B3880163
theorem B587969 : Blo 307833 587969 := bstep (se 2 (by rfl) ⟨220488, by rfl⟩ : syracuseStep 587969 = 440977) B440977
theorem B522443 : Blo 307833 522443 := bstep (se 1 (by rfl) ⟨391832, by rfl⟩ : syracuseStep 522443 = 783665) B783665
theorem B522571 : Blo 307833 522571 := bstep (se 1 (by rfl) ⟨391928, by rfl⟩ : syracuseStep 522571 = 783857) B783857
theorem B588235 : Blo 307833 588235 := bstep (se 1 (by rfl) ⟨441176, by rfl⟩ : syracuseStep 588235 = 882353) B882353
theorem B555481 : Blo 307833 555481 := bstep (se 2 (by rfl) ⟨208305, by rfl⟩ : syracuseStep 555481 = 416611) B416611
theorem B522713 : Blo 307833 522713 := bstep (se 2 (by rfl) ⟨196017, by rfl⟩ : syracuseStep 522713 = 392035) B392035
theorem B1047005 : Blo 307833 1047005 := bstep (se 3 (by rfl) ⟨196313, by rfl⟩ : syracuseStep 1047005 = 392627) B392627
theorem B784961 : Blo 307833 784961 := bstep (se 2 (by rfl) ⟨294360, by rfl⟩ : syracuseStep 784961 = 588721) B588721
theorem B1407577 : Blo 307833 1407577 := bstep (se 2 (by rfl) ⟨527841, by rfl⟩ : syracuseStep 1407577 = 1055683) B1055683
theorem B522841 : Blo 307833 522841 := bstep (se 2 (by rfl) ⟨196065, by rfl⟩ : syracuseStep 522841 = 392131) B392131
theorem B588683 : Blo 307833 588683 := bstep (se 1 (by rfl) ⟨441512, by rfl⟩ : syracuseStep 588683 = 883025) B883025
theorem B555979 : Blo 307833 555979 := bstep (se 1 (by rfl) ⟨416984, by rfl⟩ : syracuseStep 555979 = 833969) B833969
theorem B1571885 : Blo 307833 1571885 := bstep (se 3 (by rfl) ⟨294728, by rfl⟩ : syracuseStep 1571885 = 589457) B589457
theorem B588865 : Blo 307833 588865 := bstep (se 2 (by rfl) ⟨220824, by rfl⟩ : syracuseStep 588865 = 441649) B441649
theorem B785497 : Blo 307833 785497 := bstep (se 2 (by rfl) ⟨294561, by rfl⟩ : syracuseStep 785497 = 589123) B589123
theorem B523415 : Blo 307833 523415 := bstep (se 1 (by rfl) ⟨392561, by rfl⟩ : syracuseStep 523415 = 785123) B785123
theorem B523543 : Blo 307833 523543 := bstep (se 1 (by rfl) ⟨392657, by rfl⟩ : syracuseStep 523543 = 785315) B785315
theorem B2424109 : Blo 307833 2424109 := bstep (se 3 (by rfl) ⟨454520, by rfl⟩ : syracuseStep 2424109 = 909041) B909041
theorem B1178945 : Blo 307833 1178945 := bstep (se 2 (by rfl) ⟨442104, by rfl⟩ : syracuseStep 1178945 = 884209) B884209
theorem B589207 : Blo 307833 589207 := bstep (se 1 (by rfl) ⟨441905, by rfl⟩ : syracuseStep 589207 = 883811) B883811
theorem B392779 : Blo 307833 392779 := bstep (se 1 (by rfl) ⟨294584, by rfl⟩ : syracuseStep 392779 = 589169) B589169
theorem B1048139 : Blo 307833 1048139 := bstep (se 1 (by rfl) ⟨786104, by rfl⟩ : syracuseStep 1048139 = 1572209) B1572209
theorem B589427 : Blo 307833 589427 := bstep (se 1 (by rfl) ⟨442070, by rfl⟩ : syracuseStep 589427 = 884141) B884141
theorem B589655 : Blo 307833 589655 := bstep (se 1 (by rfl) ⟨442241, by rfl⟩ : syracuseStep 589655 = 884483) B884483
theorem B1048409 : Blo 307833 1048409 := bstep (se 2 (by rfl) ⟨393153, by rfl⟩ : syracuseStep 1048409 = 786307) B786307
theorem B1671005 : Blo 307833 1671005 := bstep (se 3 (by rfl) ⟨313313, by rfl⟩ : syracuseStep 1671005 = 626627) B626627
theorem B524171 : Blo 307833 524171 := bstep (se 1 (by rfl) ⟨393128, by rfl⟩ : syracuseStep 524171 = 786257) B786257
theorem B1343405 : Blo 307833 1343405 := bstep (se 3 (by rfl) ⟨251888, by rfl⟩ : syracuseStep 1343405 = 503777) B503777
theorem B4226993 : Blo 307833 4226993 := bstep (se 2 (by rfl) ⟨1585122, by rfl⟩ : syracuseStep 4226993 = 3170245) B3170245
theorem B393275 : Blo 307833 393275 := bstep (se 1 (by rfl) ⟨294956, by rfl⟩ : syracuseStep 393275 = 589913) B589913
theorem B589943 : Blo 307833 589943 := bstep (se 1 (by rfl) ⟨442457, by rfl⟩ : syracuseStep 589943 = 884915) B884915
theorem B524407 : Blo 307833 524407 := bstep (se 1 (by rfl) ⟨393305, by rfl⟩ : syracuseStep 524407 = 786611) B786611
theorem B557327 : Blo 307833 557327 := bstep (se 1 (by rfl) ⟨417995, by rfl⟩ : syracuseStep 557327 = 835991) B835991
theorem B590095 : Blo 307833 590095 := bstep (se 1 (by rfl) ⟨442571, by rfl⟩ : syracuseStep 590095 = 885143) B885143
theorem B524603 : Blo 307833 524603 := bstep (se 1 (by rfl) ⟨393452, by rfl⟩ : syracuseStep 524603 = 786905) B786905
theorem B786955 : Blo 307833 786955 := bstep (se 1 (by rfl) ⟨590216, by rfl⟩ : syracuseStep 786955 = 1180433) B1180433
theorem B1114667 : Blo 307833 1114667 := bstep (se 1 (by rfl) ⟨836000, by rfl⟩ : syracuseStep 1114667 = 1672001) B1672001
theorem B590483 : Blo 307833 590483 := bstep (se 1 (by rfl) ⟨442862, by rfl⟩ : syracuseStep 590483 = 885725) B885725
theorem B787097 : Blo 307833 787097 := bstep (se 2 (by rfl) ⟨295161, by rfl⟩ : syracuseStep 787097 = 590323) B590323
theorem B525001 : Blo 307833 525001 := bstep (se 2 (by rfl) ⟨196875, by rfl⟩ : syracuseStep 525001 = 393751) B393751
theorem B787259 : Blo 307833 787259 := bstep (se 1 (by rfl) ⟨590444, by rfl⟩ : syracuseStep 787259 = 1180889) B1180889
theorem B1180601 : Blo 307833 1180601 := bstep (se 2 (by rfl) ⟨442725, by rfl⟩ : syracuseStep 1180601 = 885451) B885451
theorem B394247 : Blo 307833 394247 := bstep (se 1 (by rfl) ⟨295685, by rfl⟩ : syracuseStep 394247 = 591371) B591371
theorem B787603 : Blo 307833 787603 := bstep (se 1 (by rfl) ⟨590702, by rfl⟩ : syracuseStep 787603 = 1181405) B1181405
theorem B787745 : Blo 307833 787745 := bstep (se 2 (by rfl) ⟨295404, by rfl⟩ : syracuseStep 787745 = 590809) B590809
theorem B525703 : Blo 307833 525703 := bstep (se 1 (by rfl) ⟨394277, by rfl⟩ : syracuseStep 525703 = 788555) B788555
theorem B7603789 : Blo 307833 7603789 := bstep (se 3 (by rfl) ⟨1425710, by rfl⟩ : syracuseStep 7603789 = 2851421) B2851421
theorem B1115849 : Blo 307833 1115849 := bstep (se 2 (by rfl) ⟨418443, by rfl⟩ : syracuseStep 1115849 = 836887) B836887
theorem B1771379 : Blo 307833 1771379 := bstep (se 1 (by rfl) ⟨1328534, by rfl⟩ : syracuseStep 1771379 = 2657069) B2657069
theorem B1574801 : Blo 307833 1574801 := bstep (se 2 (by rfl) ⟨590550, by rfl⟩ : syracuseStep 1574801 = 1181101) B1181101
theorem B1181587 : Blo 307833 1181587 := bstep (se 1 (by rfl) ⟨886190, by rfl⟩ : syracuseStep 1181587 = 1772381) B1772381
theorem B1050515 : Blo 307833 1050515 := bstep (se 1 (by rfl) ⟨787886, by rfl⟩ : syracuseStep 1050515 = 1575773) B1575773
theorem B2131865 : Blo 307833 2131865 := bstep (se 2 (by rfl) ⟨799449, by rfl⟩ : syracuseStep 2131865 = 1598899) B1598899
theorem B1411025 : Blo 307833 1411025 := bstep (se 2 (by rfl) ⟨529134, by rfl⟩ : syracuseStep 1411025 = 1058269) B1058269
theorem B591887 : Blo 307833 591887 := bstep (se 1 (by rfl) ⟨443915, by rfl⟩ : syracuseStep 591887 = 887831) B887831
theorem B788737 : Blo 307833 788737 := bstep (se 2 (by rfl) ⟨295776, by rfl⟩ : syracuseStep 788737 = 591553) B591553
theorem B559403 : Blo 307833 559403 := bstep (se 1 (by rfl) ⟨419552, by rfl⟩ : syracuseStep 559403 = 839105) B839105
theorem B6687299 : Blo 307833 6687299 := bstep (se 1 (by rfl) ⟨5015474, by rfl⟩ : syracuseStep 6687299 = 10030949) B10030949
theorem B658219 : Blo 307833 658219 := bstep (se 1 (by rfl) ⟨493664, by rfl⟩ : syracuseStep 658219 = 987329) B987329
theorem B461753 : Blo 307833 461753 := bstep (se 2 (by rfl) ⟨173157, by rfl⟩ : syracuseStep 461753 = 346315) B346315
theorem B461831 : Blo 307833 461831 := bstep (se 1 (by rfl) ⟨346373, by rfl⟩ : syracuseStep 461831 = 692747) B692747
theorem B461867 : Blo 307833 461867 := bstep (se 1 (by rfl) ⟨346400, by rfl⟩ : syracuseStep 461867 = 692801) B692801
theorem B461897 : Blo 307833 461897 := bstep (se 2 (by rfl) ⟨173211, by rfl⟩ : syracuseStep 461897 = 346423) B346423
theorem B330895 : Blo 307833 330895 := bstep (se 1 (by rfl) ⟨248171, by rfl⟩ : syracuseStep 330895 = 496343) B496343
theorem B462011 : Blo 307833 462011 := bstep (se 1 (by rfl) ⟨346508, by rfl⟩ : syracuseStep 462011 = 693017) B693017
theorem B462071 : Blo 307833 462071 := bstep (se 1 (by rfl) ⟨346553, by rfl⟩ : syracuseStep 462071 = 693107) B693107
theorem B462095 : Blo 307833 462095 := bstep (se 1 (by rfl) ⟨346571, by rfl⟩ : syracuseStep 462095 = 693143) B693143
theorem B1051919 : Blo 307833 1051919 := bstep (se 1 (by rfl) ⟨788939, by rfl⟩ : syracuseStep 1051919 = 1577879) B1577879
theorem B1772837 : Blo 307833 1772837 := bstep (se 4 (by rfl) ⟨166203, by rfl⟩ : syracuseStep 1772837 = 332407) B332407
theorem B625963 : Blo 307833 625963 := bstep (se 1 (by rfl) ⟨469472, by rfl⟩ : syracuseStep 625963 = 938945) B938945
theorem B462137 : Blo 307833 462137 := bstep (se 2 (by rfl) ⟨173301, by rfl⟩ : syracuseStep 462137 = 346603) B346603
theorem B462215 : Blo 307833 462215 := bstep (se 1 (by rfl) ⟨346661, by rfl⟩ : syracuseStep 462215 = 693323) B693323
theorem B462251 : Blo 307833 462251 := bstep (se 1 (by rfl) ⟨346688, by rfl⟩ : syracuseStep 462251 = 693377) B693377
theorem B462281 : Blo 307833 462281 := bstep (se 2 (by rfl) ⟨173355, by rfl⟩ : syracuseStep 462281 = 346711) B346711
theorem B2985437 : Blo 307833 2985437 := bstep (se 3 (by rfl) ⟨559769, by rfl⟩ : syracuseStep 2985437 = 1119539) B1119539
theorem B1052189 : Blo 307833 1052189 := bstep (se 3 (by rfl) ⟨197285, by rfl⟩ : syracuseStep 1052189 = 394571) B394571
theorem B462395 : Blo 307833 462395 := bstep (se 1 (by rfl) ⟨346796, by rfl⟩ : syracuseStep 462395 = 693593) B693593
theorem B1183319 : Blo 307833 1183319 := bstep (se 1 (by rfl) ⟨887489, by rfl⟩ : syracuseStep 1183319 = 1774979) B1774979
theorem B462455 : Blo 307833 462455 := bstep (se 1 (by rfl) ⟨346841, by rfl⟩ : syracuseStep 462455 = 693683) B693683
theorem B331399 : Blo 307833 331399 := bstep (se 1 (by rfl) ⟨248549, by rfl⟩ : syracuseStep 331399 = 497099) B497099
theorem B462479 : Blo 307833 462479 := bstep (se 1 (by rfl) ⟨346859, by rfl⟩ : syracuseStep 462479 = 693719) B693719
theorem B462521 : Blo 307833 462521 := bstep (se 2 (by rfl) ⟨173445, by rfl⟩ : syracuseStep 462521 = 346891) B346891
theorem B495305 : Blo 307833 495305 := bstep (se 2 (by rfl) ⟨185739, by rfl⟩ : syracuseStep 495305 = 371479) B371479
theorem B462599 : Blo 307833 462599 := bstep (se 1 (by rfl) ⟨346949, by rfl⟩ : syracuseStep 462599 = 693899) B693899
theorem B462635 : Blo 307833 462635 := bstep (se 1 (by rfl) ⟨346976, by rfl⟩ : syracuseStep 462635 = 693953) B693953
theorem B462665 : Blo 307833 462665 := bstep (se 2 (by rfl) ⟨173499, by rfl⟩ : syracuseStep 462665 = 346999) B346999
theorem B462779 : Blo 307833 462779 := bstep (se 1 (by rfl) ⟨347084, by rfl⟩ : syracuseStep 462779 = 694169) B694169
theorem B561097 : Blo 307833 561097 := bstep (se 2 (by rfl) ⟨210411, by rfl⟩ : syracuseStep 561097 = 420823) B420823
theorem B1576907 : Blo 307833 1576907 := bstep (se 1 (by rfl) ⟨1182680, by rfl⟩ : syracuseStep 1576907 = 2365361) B2365361
theorem B1773521 : Blo 307833 1773521 := bstep (se 2 (by rfl) ⟨665070, by rfl⟩ : syracuseStep 1773521 = 1330141) B1330141
theorem B462839 : Blo 307833 462839 := bstep (se 1 (by rfl) ⟨347129, by rfl⟩ : syracuseStep 462839 = 694259) B694259
theorem B462863 : Blo 307833 462863 := bstep (se 1 (by rfl) ⟨347147, by rfl⟩ : syracuseStep 462863 = 694295) B694295
theorem B462905 : Blo 307833 462905 := bstep (se 2 (by rfl) ⟨173589, by rfl⟩ : syracuseStep 462905 = 347179) B347179
theorem B1183805 : Blo 307833 1183805 := bstep (se 3 (by rfl) ⟨221963, by rfl⟩ : syracuseStep 1183805 = 443927) B443927
theorem B462983 : Blo 307833 462983 := bstep (se 1 (by rfl) ⟨347237, by rfl⟩ : syracuseStep 462983 = 694475) B694475
theorem B659603 : Blo 307833 659603 := bstep (se 1 (by rfl) ⟨494702, by rfl⟩ : syracuseStep 659603 = 989405) B989405
theorem B463019 : Blo 307833 463019 := bstep (se 1 (by rfl) ⟨347264, by rfl⟩ : syracuseStep 463019 = 694529) B694529
theorem B2691245 : Blo 307833 2691245 := bstep (se 3 (by rfl) ⟨504608, by rfl⟩ : syracuseStep 2691245 = 1009217) B1009217
theorem B463049 : Blo 307833 463049 := bstep (se 2 (by rfl) ⟨173643, by rfl⟩ : syracuseStep 463049 = 347287) B347287
theorem B1773839 : Blo 307833 1773839 := bstep (se 1 (by rfl) ⟨1330379, by rfl⟩ : syracuseStep 1773839 = 2660759) B2660759
theorem B1577231 : Blo 307833 1577231 := bstep (se 1 (by rfl) ⟨1182923, by rfl⟩ : syracuseStep 1577231 = 2365847) B2365847
theorem B463163 : Blo 307833 463163 := bstep (se 1 (by rfl) ⟨347372, by rfl⟩ : syracuseStep 463163 = 694745) B694745
theorem B463223 : Blo 307833 463223 := bstep (se 1 (by rfl) ⟨347417, by rfl⟩ : syracuseStep 463223 = 694835) B694835
theorem B1315207 : Blo 307833 1315207 := bstep (se 1 (by rfl) ⟨986405, by rfl⟩ : syracuseStep 1315207 = 1972811) B1972811
theorem B463247 : Blo 307833 463247 := bstep (se 1 (by rfl) ⟨347435, by rfl⟩ : syracuseStep 463247 = 694871) B694871
theorem B463289 : Blo 307833 463289 := bstep (se 2 (by rfl) ⟨173733, by rfl⟩ : syracuseStep 463289 = 347467) B347467
theorem B332219 : Blo 307833 332219 := bstep (se 1 (by rfl) ⟨249164, by rfl⟩ : syracuseStep 332219 = 498329) B498329
theorem B463367 : Blo 307833 463367 := bstep (se 1 (by rfl) ⟨347525, by rfl⟩ : syracuseStep 463367 = 695051) B695051
theorem B2658845 : Blo 307833 2658845 := bstep (se 3 (by rfl) ⟨498533, by rfl⟩ : syracuseStep 2658845 = 997067) B997067
theorem B463403 : Blo 307833 463403 := bstep (se 1 (by rfl) ⟨347552, by rfl⟩ : syracuseStep 463403 = 695105) B695105
theorem B463433 : Blo 307833 463433 := bstep (se 2 (by rfl) ⟨173787, by rfl⟩ : syracuseStep 463433 = 347575) B347575
theorem B692855 : Blo 307833 692855 := bstep (se 1 (by rfl) ⟨519641, by rfl⟩ : syracuseStep 692855 = 1039283) B1039283
theorem B5968565 : Blo 307833 5968565 := bstep (se 5 (by rfl) ⟨279776, by rfl⟩ : syracuseStep 5968565 = 559553) B559553
theorem B463547 : Blo 307833 463547 := bstep (se 1 (by rfl) ⟨347660, by rfl⟩ : syracuseStep 463547 = 695321) B695321
theorem B463607 : Blo 307833 463607 := bstep (se 1 (by rfl) ⟨347705, by rfl⟩ : syracuseStep 463607 = 695411) B695411
theorem B463631 : Blo 307833 463631 := bstep (se 1 (by rfl) ⟨347723, by rfl⟩ : syracuseStep 463631 = 695447) B695447
theorem B693035 : Blo 307833 693035 := bstep (se 1 (by rfl) ⟨519776, by rfl⟩ : syracuseStep 693035 = 1039553) B1039553
theorem B463673 : Blo 307833 463673 := bstep (se 2 (by rfl) ⟨173877, by rfl⟩ : syracuseStep 463673 = 347755) B347755
theorem B463751 : Blo 307833 463751 := bstep (se 1 (by rfl) ⟨347813, by rfl⟩ : syracuseStep 463751 = 695627) B695627
theorem B463787 : Blo 307833 463787 := bstep (se 1 (by rfl) ⟨347840, by rfl⟩ : syracuseStep 463787 = 695681) B695681
theorem B14554037 : Blo 307833 14554037 := bstep (se 5 (by rfl) ⟨682220, by rfl⟩ : syracuseStep 14554037 = 1364441) B1364441
theorem B463817 : Blo 307833 463817 := bstep (se 2 (by rfl) ⟨173931, by rfl⟩ : syracuseStep 463817 = 347863) B347863
theorem B463931 : Blo 307833 463931 := bstep (se 1 (by rfl) ⟨347948, by rfl⟩ : syracuseStep 463931 = 695897) B695897
theorem B1184887 : Blo 307833 1184887 := bstep (se 1 (by rfl) ⟨888665, by rfl⟩ : syracuseStep 1184887 = 1777331) B1777331
theorem B463991 : Blo 307833 463991 := bstep (se 1 (by rfl) ⟨347993, by rfl⟩ : syracuseStep 463991 = 695987) B695987
theorem B464015 : Blo 307833 464015 := bstep (se 1 (by rfl) ⟨348011, by rfl⟩ : syracuseStep 464015 = 696023) B696023
theorem B693395 : Blo 307833 693395 := bstep (se 1 (by rfl) ⟨520046, by rfl⟩ : syracuseStep 693395 = 1040093) B1040093
theorem B464057 : Blo 307833 464057 := bstep (se 2 (by rfl) ⟨174021, by rfl⟩ : syracuseStep 464057 = 348043) B348043
theorem B693449 : Blo 307833 693449 := bstep (se 2 (by rfl) ⟨260043, by rfl⟩ : syracuseStep 693449 = 520087) B520087
theorem B464135 : Blo 307833 464135 := bstep (se 1 (by rfl) ⟨348101, by rfl⟩ : syracuseStep 464135 = 696203) B696203
theorem B464171 : Blo 307833 464171 := bstep (se 1 (by rfl) ⟨348128, by rfl⟩ : syracuseStep 464171 = 696257) B696257
theorem B464201 : Blo 307833 464201 := bstep (se 2 (by rfl) ⟨174075, by rfl⟩ : syracuseStep 464201 = 348151) B348151
theorem B464315 : Blo 307833 464315 := bstep (se 1 (by rfl) ⟨348236, by rfl⟩ : syracuseStep 464315 = 696473) B696473
theorem B464375 : Blo 307833 464375 := bstep (se 1 (by rfl) ⟨348281, by rfl⟩ : syracuseStep 464375 = 696563) B696563
theorem B464399 : Blo 307833 464399 := bstep (se 1 (by rfl) ⟨348299, by rfl⟩ : syracuseStep 464399 = 696599) B696599
theorem B464441 : Blo 307833 464441 := bstep (se 2 (by rfl) ⟨174165, by rfl⟩ : syracuseStep 464441 = 348331) B348331
theorem B464519 : Blo 307833 464519 := bstep (se 1 (by rfl) ⟨348389, by rfl⟩ : syracuseStep 464519 = 696779) B696779
theorem B464555 : Blo 307833 464555 := bstep (se 1 (by rfl) ⟨348416, by rfl⟩ : syracuseStep 464555 = 696833) B696833
theorem B1775297 : Blo 307833 1775297 := bstep (se 2 (by rfl) ⟨665736, by rfl⟩ : syracuseStep 1775297 = 1331473) B1331473
theorem B464585 : Blo 307833 464585 := bstep (se 2 (by rfl) ⟨174219, by rfl⟩ : syracuseStep 464585 = 348439) B348439
theorem B4495105 : Blo 307833 4495105 := bstep (se 2 (by rfl) ⟨1685664, by rfl⟩ : syracuseStep 4495105 = 3371329) B3371329
theorem B464699 : Blo 307833 464699 := bstep (se 1 (by rfl) ⟨348524, by rfl⟩ : syracuseStep 464699 = 697049) B697049
theorem B464759 : Blo 307833 464759 := bstep (se 1 (by rfl) ⟨348569, by rfl⟩ : syracuseStep 464759 = 697139) B697139
theorem B1873799 : Blo 307833 1873799 := bstep (se 1 (by rfl) ⟨1405349, by rfl⟩ : syracuseStep 1873799 = 2810699) B2810699
theorem B694151 : Blo 307833 694151 := bstep (se 1 (by rfl) ⟨520613, by rfl⟩ : syracuseStep 694151 = 1041227) B1041227
theorem B464783 : Blo 307833 464783 := bstep (se 1 (by rfl) ⟨348587, by rfl⟩ : syracuseStep 464783 = 697175) B697175
theorem B464825 : Blo 307833 464825 := bstep (se 2 (by rfl) ⟨174309, by rfl⟩ : syracuseStep 464825 = 348619) B348619
theorem B464903 : Blo 307833 464903 := bstep (se 1 (by rfl) ⟨348677, by rfl⟩ : syracuseStep 464903 = 697355) B697355
theorem B464939 : Blo 307833 464939 := bstep (se 1 (by rfl) ⟨348704, by rfl⟩ : syracuseStep 464939 = 697409) B697409
theorem B694331 : Blo 307833 694331 := bstep (se 1 (by rfl) ⟨520748, by rfl⟩ : syracuseStep 694331 = 1041497) B1041497
theorem B464969 : Blo 307833 464969 := bstep (se 2 (by rfl) ⟨174363, by rfl⟩ : syracuseStep 464969 = 348727) B348727
theorem B2660485 : Blo 307833 2660485 := bstep (se 4 (by rfl) ⟨249420, by rfl⟩ : syracuseStep 2660485 = 498841) B498841
theorem B694457 : Blo 307833 694457 := bstep (se 2 (by rfl) ⟨260421, by rfl⟩ : syracuseStep 694457 = 520843) B520843
theorem B465083 : Blo 307833 465083 := bstep (se 1 (by rfl) ⟨348812, by rfl⟩ : syracuseStep 465083 = 697625) B697625
theorem B465143 : Blo 307833 465143 := bstep (se 1 (by rfl) ⟨348857, by rfl⟩ : syracuseStep 465143 = 697715) B697715
theorem B465167 : Blo 307833 465167 := bstep (se 1 (by rfl) ⟨348875, by rfl⟩ : syracuseStep 465167 = 697751) B697751
theorem B465209 : Blo 307833 465209 := bstep (se 2 (by rfl) ⟨174453, by rfl⟩ : syracuseStep 465209 = 348907) B348907
theorem B3021187 : Blo 307833 3021187 := bstep (se 1 (by rfl) ⟨2265890, by rfl⟩ : syracuseStep 3021187 = 4531781) B4531781
theorem B465287 : Blo 307833 465287 := bstep (se 1 (by rfl) ⟨348965, by rfl⟩ : syracuseStep 465287 = 697931) B697931
theorem B465323 : Blo 307833 465323 := bstep (se 1 (by rfl) ⟨348992, by rfl⟩ : syracuseStep 465323 = 697985) B697985
theorem B465353 : Blo 307833 465353 := bstep (se 2 (by rfl) ⟨174507, by rfl⟩ : syracuseStep 465353 = 349015) B349015
theorem B694799 : Blo 307833 694799 := bstep (se 1 (by rfl) ⟨521099, by rfl⟩ : syracuseStep 694799 = 1042199) B1042199
theorem B694817 : Blo 307833 694817 := bstep (se 2 (by rfl) ⟨260556, by rfl⟩ : syracuseStep 694817 = 521113) B521113
theorem B465467 : Blo 307833 465467 := bstep (se 1 (by rfl) ⟨349100, by rfl⟩ : syracuseStep 465467 = 698201) B698201
theorem B8428151 : Blo 307833 8428151 := bstep (se 1 (by rfl) ⟨6321113, by rfl⟩ : syracuseStep 8428151 = 12642227) B12642227
theorem B989815 : Blo 307833 989815 := bstep (se 1 (by rfl) ⟨742361, by rfl⟩ : syracuseStep 989815 = 1484723) B1484723
theorem B465527 : Blo 307833 465527 := bstep (se 1 (by rfl) ⟨349145, by rfl⟩ : syracuseStep 465527 = 698291) B698291
theorem B465551 : Blo 307833 465551 := bstep (se 1 (by rfl) ⟨349163, by rfl⟩ : syracuseStep 465551 = 698327) B698327
theorem B793241 : Blo 307833 793241 := bstep (se 2 (by rfl) ⟨297465, by rfl⟩ : syracuseStep 793241 = 594931) B594931
theorem B465593 : Blo 307833 465593 := bstep (se 2 (by rfl) ⟨174597, by rfl⟩ : syracuseStep 465593 = 349195) B349195
theorem B465671 : Blo 307833 465671 := bstep (se 1 (by rfl) ⟨349253, by rfl⟩ : syracuseStep 465671 = 698507) B698507
theorem B465707 : Blo 307833 465707 := bstep (se 1 (by rfl) ⟨349280, by rfl⟩ : syracuseStep 465707 = 698561) B698561
theorem B465737 : Blo 307833 465737 := bstep (se 2 (by rfl) ⟨174651, by rfl⟩ : syracuseStep 465737 = 349303) B349303
theorem B695159 : Blo 307833 695159 := bstep (se 1 (by rfl) ⟨521369, by rfl⟩ : syracuseStep 695159 = 1042739) B1042739
theorem B400315 : Blo 307833 400315 := bstep (se 1 (by rfl) ⟨300236, by rfl⟩ : syracuseStep 400315 = 600473) B600473
theorem B465851 : Blo 307833 465851 := bstep (se 1 (by rfl) ⟨349388, by rfl⟩ : syracuseStep 465851 = 698777) B698777
theorem B465911 : Blo 307833 465911 := bstep (se 1 (by rfl) ⟨349433, by rfl⟩ : syracuseStep 465911 = 698867) B698867
theorem B465935 : Blo 307833 465935 := bstep (se 1 (by rfl) ⟨349451, by rfl⟩ : syracuseStep 465935 = 698903) B698903
theorem B695339 : Blo 307833 695339 := bstep (se 1 (by rfl) ⟨521504, by rfl⟩ : syracuseStep 695339 = 1043009) B1043009
theorem B990251 : Blo 307833 990251 := bstep (se 1 (by rfl) ⟨742688, by rfl⟩ : syracuseStep 990251 = 1485377) B1485377
theorem B465977 : Blo 307833 465977 := bstep (se 2 (by rfl) ⟨174741, by rfl⟩ : syracuseStep 465977 = 349483) B349483
theorem B5020805 : Blo 307833 5020805 := bstep (se 4 (by rfl) ⟨470700, by rfl⟩ : syracuseStep 5020805 = 941401) B941401
theorem B466055 : Blo 307833 466055 := bstep (se 1 (by rfl) ⟨349541, by rfl⟩ : syracuseStep 466055 = 699083) B699083
theorem B466091 : Blo 307833 466091 := bstep (se 1 (by rfl) ⟨349568, by rfl⟩ : syracuseStep 466091 = 699137) B699137
theorem B466121 : Blo 307833 466121 := bstep (se 2 (by rfl) ⟨174795, by rfl⟩ : syracuseStep 466121 = 349591) B349591
theorem B466235 : Blo 307833 466235 := bstep (se 1 (by rfl) ⟨349676, by rfl⟩ : syracuseStep 466235 = 699353) B699353
theorem B466295 : Blo 307833 466295 := bstep (se 1 (by rfl) ⟨349721, by rfl⟩ : syracuseStep 466295 = 699443) B699443
theorem B466319 : Blo 307833 466319 := bstep (se 1 (by rfl) ⟨349739, by rfl⟩ : syracuseStep 466319 = 699479) B699479
theorem B695699 : Blo 307833 695699 := bstep (se 1 (by rfl) ⟨521774, by rfl⟩ : syracuseStep 695699 = 1043549) B1043549
theorem B1678745 : Blo 307833 1678745 := bstep (se 2 (by rfl) ⟨629529, by rfl⟩ : syracuseStep 1678745 = 1259059) B1259059
theorem B466361 : Blo 307833 466361 := bstep (se 2 (by rfl) ⟨174885, by rfl⟩ : syracuseStep 466361 = 349771) B349771
theorem B695753 : Blo 307833 695753 := bstep (se 2 (by rfl) ⟨260907, by rfl⟩ : syracuseStep 695753 = 521815) B521815
theorem B466439 : Blo 307833 466439 := bstep (se 1 (by rfl) ⟨349829, by rfl⟩ : syracuseStep 466439 = 699659) B699659
theorem B1482263 : Blo 307833 1482263 := bstep (se 1 (by rfl) ⟨1111697, by rfl⟩ : syracuseStep 1482263 = 2223395) B2223395
theorem B466475 : Blo 307833 466475 := bstep (se 1 (by rfl) ⟨349856, by rfl⟩ : syracuseStep 466475 = 699713) B699713
theorem B466505 : Blo 307833 466505 := bstep (se 2 (by rfl) ⟨174939, by rfl⟩ : syracuseStep 466505 = 349879) B349879
theorem B3972685 : Blo 307833 3972685 := bstep (se 3 (by rfl) ⟨744878, by rfl⟩ : syracuseStep 3972685 = 1489757) B1489757
theorem B466619 : Blo 307833 466619 := bstep (se 1 (by rfl) ⟨349964, by rfl⟩ : syracuseStep 466619 = 699929) B699929
theorem B466679 : Blo 307833 466679 := bstep (se 1 (by rfl) ⟨350009, by rfl⟩ : syracuseStep 466679 = 700019) B700019
theorem B663311 : Blo 307833 663311 := bstep (se 1 (by rfl) ⟨497483, by rfl⟩ : syracuseStep 663311 = 994967) B994967
theorem B466703 : Blo 307833 466703 := bstep (se 1 (by rfl) ⟨350027, by rfl⟩ : syracuseStep 466703 = 700055) B700055
theorem B466745 : Blo 307833 466745 := bstep (se 2 (by rfl) ⟨175029, by rfl⟩ : syracuseStep 466745 = 350059) B350059
theorem B466823 : Blo 307833 466823 := bstep (se 1 (by rfl) ⟨350117, by rfl⟩ : syracuseStep 466823 = 700235) B700235
theorem B466859 : Blo 307833 466859 := bstep (se 1 (by rfl) ⟨350144, by rfl⟩ : syracuseStep 466859 = 700289) B700289
theorem B663481 : Blo 307833 663481 := bstep (se 2 (by rfl) ⟨248805, by rfl⟩ : syracuseStep 663481 = 497611) B497611
theorem B466889 : Blo 307833 466889 := bstep (se 2 (by rfl) ⟨175083, by rfl⟩ : syracuseStep 466889 = 350167) B350167
theorem B467003 : Blo 307833 467003 := bstep (se 1 (by rfl) ⟨350252, by rfl⟩ : syracuseStep 467003 = 700505) B700505
theorem B467063 : Blo 307833 467063 := bstep (se 1 (by rfl) ⟨350297, by rfl⟩ : syracuseStep 467063 = 700595) B700595
theorem B696455 : Blo 307833 696455 := bstep (se 1 (by rfl) ⟨522341, by rfl⟩ : syracuseStep 696455 = 1044683) B1044683
theorem B467087 : Blo 307833 467087 := bstep (se 1 (by rfl) ⟨350315, by rfl⟩ : syracuseStep 467087 = 700631) B700631
theorem B467129 : Blo 307833 467129 := bstep (se 2 (by rfl) ⟨175173, by rfl⟩ : syracuseStep 467129 = 350347) B350347
theorem B3449033 : Blo 307833 3449033 := bstep (se 2 (by rfl) ⟨1293387, by rfl⟩ : syracuseStep 3449033 = 2586775) B2586775
theorem B467207 : Blo 307833 467207 := bstep (se 1 (by rfl) ⟨350405, by rfl⟩ : syracuseStep 467207 = 700811) B700811
theorem B663823 : Blo 307833 663823 := bstep (se 1 (by rfl) ⟨497867, by rfl⟩ : syracuseStep 663823 = 995735) B995735
theorem B467243 : Blo 307833 467243 := bstep (se 1 (by rfl) ⟨350432, by rfl⟩ : syracuseStep 467243 = 700865) B700865
theorem B696635 : Blo 307833 696635 := bstep (se 1 (by rfl) ⟨522476, by rfl⟩ : syracuseStep 696635 = 1044953) B1044953
theorem B467273 : Blo 307833 467273 := bstep (se 2 (by rfl) ⟨175227, by rfl⟩ : syracuseStep 467273 = 350455) B350455
theorem B729479 : Blo 307833 729479 := bstep (se 1 (by rfl) ⟨547109, by rfl⟩ : syracuseStep 729479 = 1094219) B1094219
theorem B696761 : Blo 307833 696761 := bstep (se 2 (by rfl) ⟨261285, by rfl⟩ : syracuseStep 696761 = 522571) B522571
theorem B467387 : Blo 307833 467387 := bstep (se 1 (by rfl) ⟨350540, by rfl⟩ : syracuseStep 467387 = 701081) B701081
theorem B467447 : Blo 307833 467447 := bstep (se 1 (by rfl) ⟨350585, by rfl⟩ : syracuseStep 467447 = 701171) B701171
theorem B467471 : Blo 307833 467471 := bstep (se 1 (by rfl) ⟨350603, by rfl⟩ : syracuseStep 467471 = 701207) B701207
theorem B467513 : Blo 307833 467513 := bstep (se 2 (by rfl) ⟨175317, by rfl⟩ : syracuseStep 467513 = 350635) B350635
theorem B1188413 : Blo 307833 1188413 := bstep (se 3 (by rfl) ⟨222827, by rfl⟩ : syracuseStep 1188413 = 445655) B445655
theorem B467591 : Blo 307833 467591 := bstep (se 1 (by rfl) ⟨350693, by rfl⟩ : syracuseStep 467591 = 701387) B701387
theorem B467627 : Blo 307833 467627 := bstep (se 1 (by rfl) ⟨350720, by rfl⟩ : syracuseStep 467627 = 701441) B701441
theorem B467657 : Blo 307833 467657 := bstep (se 2 (by rfl) ⟨175371, by rfl⟩ : syracuseStep 467657 = 350743) B350743
theorem B697103 : Blo 307833 697103 := bstep (se 1 (by rfl) ⟨522827, by rfl⟩ : syracuseStep 697103 = 1045655) B1045655
theorem B1876769 : Blo 307833 1876769 := bstep (se 2 (by rfl) ⟨703788, by rfl⟩ : syracuseStep 1876769 = 1407577) B1407577
theorem B992033 : Blo 307833 992033 := bstep (se 2 (by rfl) ⟨372012, by rfl⟩ : syracuseStep 992033 = 744025) B744025
theorem B697121 : Blo 307833 697121 := bstep (se 2 (by rfl) ⟨261420, by rfl⟩ : syracuseStep 697121 = 522841) B522841
theorem B2237233 : Blo 307833 2237233 := bstep (se 2 (by rfl) ⟨838962, by rfl⟩ : syracuseStep 2237233 = 1677925) B1677925
theorem B2663219 : Blo 307833 2663219 := bstep (se 1 (by rfl) ⟨1997414, by rfl⟩ : syracuseStep 2663219 = 3994829) B3994829
theorem B697463 : Blo 307833 697463 := bstep (se 1 (by rfl) ⟨523097, by rfl⟩ : syracuseStep 697463 = 1046195) B1046195
theorem B697643 : Blo 307833 697643 := bstep (se 1 (by rfl) ⟨523232, by rfl⟩ : syracuseStep 697643 = 1046465) B1046465
theorem B664951 : Blo 307833 664951 := bstep (se 1 (by rfl) ⟨498713, by rfl⟩ : syracuseStep 664951 = 997427) B997427
theorem B1320401 : Blo 307833 1320401 := bstep (se 2 (by rfl) ⟨495150, by rfl⟩ : syracuseStep 1320401 = 990301) B990301
theorem B698003 : Blo 307833 698003 := bstep (se 1 (by rfl) ⟨523502, by rfl⟩ : syracuseStep 698003 = 1047005) B1047005
theorem B698057 : Blo 307833 698057 := bstep (se 2 (by rfl) ⟨261771, by rfl⟩ : syracuseStep 698057 = 523543) B523543
theorem B468937 : Blo 307833 468937 := bstep (se 2 (by rfl) ⟨175851, by rfl⟩ : syracuseStep 468937 = 351703) B351703
theorem B698759 : Blo 307833 698759 := bstep (se 1 (by rfl) ⟨524069, by rfl⟩ : syracuseStep 698759 = 1048139) B1048139
theorem B3582413 : Blo 307833 3582413 := bstep (se 3 (by rfl) ⟨671702, by rfl⟩ : syracuseStep 3582413 = 1343405) B1343405
theorem B698939 : Blo 307833 698939 := bstep (se 1 (by rfl) ⟨524204, by rfl⟩ : syracuseStep 698939 = 1048409) B1048409
theorem B699065 : Blo 307833 699065 := bstep (se 2 (by rfl) ⟨262149, by rfl⟩ : syracuseStep 699065 = 524299) B524299
theorem B371575 : Blo 307833 371575 := bstep (se 1 (by rfl) ⟨278681, by rfl⟩ : syracuseStep 371575 = 557363) B557363
theorem B2632601 : Blo 307833 2632601 := bstep (se 2 (by rfl) ⟨987225, by rfl⟩ : syracuseStep 2632601 = 1974451) B1974451
theorem B1256401 : Blo 307833 1256401 := bstep (se 2 (by rfl) ⟨471150, by rfl⟩ : syracuseStep 1256401 = 942301) B942301
theorem B371719 : Blo 307833 371719 := bstep (se 1 (by rfl) ⟨278789, by rfl⟩ : syracuseStep 371719 = 557579) B557579
theorem B699407 : Blo 307833 699407 := bstep (se 1 (by rfl) ⟨524555, by rfl⟩ : syracuseStep 699407 = 1049111) B1049111
theorem B699425 : Blo 307833 699425 := bstep (se 2 (by rfl) ⟨262284, by rfl⟩ : syracuseStep 699425 = 524569) B524569
theorem B1322027 : Blo 307833 1322027 := bstep (se 1 (by rfl) ⟨991520, by rfl⟩ : syracuseStep 1322027 = 1983041) B1983041
theorem B502843 : Blo 307833 502843 := bstep (se 1 (by rfl) ⟨377132, by rfl⟩ : syracuseStep 502843 = 754265) B754265
theorem B699767 : Blo 307833 699767 := bstep (se 1 (by rfl) ⟨524825, by rfl⟩ : syracuseStep 699767 = 1049651) B1049651
theorem B470519 : Blo 307833 470519 := bstep (se 1 (by rfl) ⟨352889, by rfl⟩ : syracuseStep 470519 = 705779) B705779
theorem B1256971 : Blo 307833 1256971 := bstep (se 1 (by rfl) ⟨942728, by rfl⟩ : syracuseStep 1256971 = 1885457) B1885457
theorem B699947 : Blo 307833 699947 := bstep (se 1 (by rfl) ⟨524960, by rfl⟩ : syracuseStep 699947 = 1049921) B1049921
theorem B995017 : Blo 307833 995017 := bstep (se 2 (by rfl) ⟨373131, by rfl⟩ : syracuseStep 995017 = 746263) B746263
theorem B700307 : Blo 307833 700307 := bstep (se 1 (by rfl) ⟨525230, by rfl⟩ : syracuseStep 700307 = 1050461) B1050461
theorem B700361 : Blo 307833 700361 := bstep (se 2 (by rfl) ⟨262635, by rfl⟩ : syracuseStep 700361 = 525271) B525271
theorem B1126429 : Blo 307833 1126429 := bstep (se 3 (by rfl) ⟨211205, by rfl⟩ : syracuseStep 1126429 = 422411) B422411
theorem B1782161 : Blo 307833 1782161 := bstep (se 2 (by rfl) ⟨668310, by rfl⟩ : syracuseStep 1782161 = 1336621) B1336621
theorem B471467 : Blo 307833 471467 := bstep (se 1 (by rfl) ⟨353600, by rfl⟩ : syracuseStep 471467 = 707201) B707201
theorem B2109995 : Blo 307833 2109995 := bstep (se 1 (by rfl) ⟨1582496, by rfl⟩ : syracuseStep 2109995 = 3164993) B3164993
theorem B307847 : Blo 307833 307847 := bstep (se 1 (by rfl) ⟨230885, by rfl⟩ : syracuseStep 307847 = 461771) B461771
theorem B701063 : Blo 307833 701063 := bstep (se 1 (by rfl) ⟨525797, by rfl⟩ : syracuseStep 701063 = 1051595) B1051595
theorem B307855 : Blo 307833 307855 := bstep (se 1 (by rfl) ⟨230891, by rfl⟩ : syracuseStep 307855 = 461783) B461783
theorem B504505 : Blo 307833 504505 := bstep (se 2 (by rfl) ⟨189189, by rfl⟩ : syracuseStep 504505 = 378379) B378379
theorem B307899 : Blo 307833 307899 := bstep (se 1 (by rfl) ⟨230924, by rfl⟩ : syracuseStep 307899 = 461849) B461849
theorem B307975 : Blo 307833 307975 := bstep (se 1 (by rfl) ⟨230981, by rfl⟩ : syracuseStep 307975 = 461963) B461963
theorem B307983 : Blo 307833 307983 := bstep (se 1 (by rfl) ⟨230987, by rfl⟩ : syracuseStep 307983 = 461975) B461975
theorem B897821 : Blo 307833 897821 := bstep (se 3 (by rfl) ⟨168341, by rfl⟩ : syracuseStep 897821 = 336683) B336683
theorem B308027 : Blo 307833 308027 := bstep (se 1 (by rfl) ⟨231020, by rfl⟩ : syracuseStep 308027 = 462041) B462041
theorem B701243 : Blo 307833 701243 := bstep (se 1 (by rfl) ⟨525932, by rfl⟩ : syracuseStep 701243 = 1051865) B1051865
theorem B308103 : Blo 307833 308103 := bstep (se 1 (by rfl) ⟨231077, by rfl⟩ : syracuseStep 308103 = 462155) B462155
theorem B308111 : Blo 307833 308111 := bstep (se 1 (by rfl) ⟨231083, by rfl⟩ : syracuseStep 308111 = 462167) B462167
theorem B701369 : Blo 307833 701369 := bstep (se 2 (by rfl) ⟨263013, by rfl⟩ : syracuseStep 701369 = 526027) B526027
theorem B308155 : Blo 307833 308155 := bstep (se 1 (by rfl) ⟨231116, by rfl⟩ : syracuseStep 308155 = 462233) B462233
theorem B308231 : Blo 307833 308231 := bstep (se 1 (by rfl) ⟨231173, by rfl⟩ : syracuseStep 308231 = 462347) B462347
theorem B308239 : Blo 307833 308239 := bstep (se 1 (by rfl) ⟨231179, by rfl⟩ : syracuseStep 308239 = 462359) B462359
theorem B308283 : Blo 307833 308283 := bstep (se 1 (by rfl) ⟨231212, by rfl⟩ : syracuseStep 308283 = 462425) B462425
theorem B2962565 : Blo 307833 2962565 := bstep (se 4 (by rfl) ⟨277740, by rfl⟩ : syracuseStep 2962565 = 555481) B555481
theorem B308359 : Blo 307833 308359 := bstep (se 1 (by rfl) ⟨231269, by rfl⟩ : syracuseStep 308359 = 462539) B462539
theorem B308367 : Blo 307833 308367 := bstep (se 1 (by rfl) ⟨231275, by rfl⟩ : syracuseStep 308367 = 462551) B462551
theorem B308411 : Blo 307833 308411 := bstep (se 1 (by rfl) ⟨231308, by rfl⟩ : syracuseStep 308411 = 462617) B462617
theorem B308487 : Blo 307833 308487 := bstep (se 1 (by rfl) ⟨231365, by rfl⟩ : syracuseStep 308487 = 462731) B462731
theorem B308495 : Blo 307833 308495 := bstep (se 1 (by rfl) ⟨231371, by rfl⟩ : syracuseStep 308495 = 462743) B462743
theorem B3355937 : Blo 307833 3355937 := bstep (se 2 (by rfl) ⟨1258476, by rfl⟩ : syracuseStep 3355937 = 2516953) B2516953
theorem B308539 : Blo 307833 308539 := bstep (se 1 (by rfl) ⟨231404, by rfl⟩ : syracuseStep 308539 = 462809) B462809
theorem B6698371 : Blo 307833 6698371 := bstep (se 1 (by rfl) ⟨5023778, by rfl⟩ : syracuseStep 6698371 = 10047557) B10047557
theorem B308615 : Blo 307833 308615 := bstep (se 1 (by rfl) ⟨231461, by rfl⟩ : syracuseStep 308615 = 462923) B462923
theorem B308623 : Blo 307833 308623 := bstep (se 1 (by rfl) ⟨231467, by rfl⟩ : syracuseStep 308623 = 462935) B462935
theorem B308667 : Blo 307833 308667 := bstep (se 1 (by rfl) ⟨231500, by rfl⟩ : syracuseStep 308667 = 463001) B463001
theorem B308743 : Blo 307833 308743 := bstep (se 1 (by rfl) ⟨231557, by rfl⟩ : syracuseStep 308743 = 463115) B463115
theorem B308751 : Blo 307833 308751 := bstep (se 1 (by rfl) ⟨231563, by rfl⟩ : syracuseStep 308751 = 463127) B463127
theorem B308795 : Blo 307833 308795 := bstep (se 1 (by rfl) ⟨231596, by rfl⟩ : syracuseStep 308795 = 463193) B463193
theorem B1488451 : Blo 307833 1488451 := bstep (se 1 (by rfl) ⟨1116338, by rfl⟩ : syracuseStep 1488451 = 2232677) B2232677
theorem B308871 : Blo 307833 308871 := bstep (se 1 (by rfl) ⟨231653, by rfl⟩ : syracuseStep 308871 = 463307) B463307
theorem B308879 : Blo 307833 308879 := bstep (se 1 (by rfl) ⟨231659, by rfl⟩ : syracuseStep 308879 = 463319) B463319
theorem B308923 : Blo 307833 308923 := bstep (se 1 (by rfl) ⟨231692, by rfl⟩ : syracuseStep 308923 = 463385) B463385
theorem B308999 : Blo 307833 308999 := bstep (se 1 (by rfl) ⟨231749, by rfl⟩ : syracuseStep 308999 = 463499) B463499
theorem B309007 : Blo 307833 309007 := bstep (se 1 (by rfl) ⟨231755, by rfl⟩ : syracuseStep 309007 = 463511) B463511
theorem B3356453 : Blo 307833 3356453 := bstep (se 4 (by rfl) ⟨314667, by rfl⟩ : syracuseStep 3356453 = 629335) B629335
theorem B309051 : Blo 307833 309051 := bstep (se 1 (by rfl) ⟨231788, by rfl⟩ : syracuseStep 309051 = 463577) B463577
theorem B309127 : Blo 307833 309127 := bstep (se 1 (by rfl) ⟨231845, by rfl⟩ : syracuseStep 309127 = 463691) B463691
theorem B309135 : Blo 307833 309135 := bstep (se 1 (by rfl) ⟨231851, by rfl⟩ : syracuseStep 309135 = 463703) B463703
theorem B309179 : Blo 307833 309179 := bstep (se 1 (by rfl) ⟨231884, by rfl⟩ : syracuseStep 309179 = 463769) B463769
theorem B440311 : Blo 307833 440311 := bstep (se 1 (by rfl) ⟨330233, by rfl⟩ : syracuseStep 440311 = 660467) B660467
theorem B309255 : Blo 307833 309255 := bstep (se 1 (by rfl) ⟨231941, by rfl⟩ : syracuseStep 309255 = 463883) B463883
theorem B309263 : Blo 307833 309263 := bstep (se 1 (by rfl) ⟨231947, by rfl⟩ : syracuseStep 309263 = 463895) B463895
theorem B309307 : Blo 307833 309307 := bstep (se 1 (by rfl) ⟨231980, by rfl⟩ : syracuseStep 309307 = 463961) B463961
theorem B309383 : Blo 307833 309383 := bstep (se 1 (by rfl) ⟨232037, by rfl⟩ : syracuseStep 309383 = 464075) B464075
theorem B309391 : Blo 307833 309391 := bstep (se 1 (by rfl) ⟨232043, by rfl⟩ : syracuseStep 309391 = 464087) B464087
theorem B309435 : Blo 307833 309435 := bstep (se 1 (by rfl) ⟨232076, by rfl⟩ : syracuseStep 309435 = 464153) B464153
theorem B309511 : Blo 307833 309511 := bstep (se 1 (by rfl) ⟨232133, by rfl⟩ : syracuseStep 309511 = 464267) B464267
theorem B309519 : Blo 307833 309519 := bstep (se 1 (by rfl) ⟨232139, by rfl⟩ : syracuseStep 309519 = 464279) B464279
theorem B473359 : Blo 307833 473359 := bstep (se 1 (by rfl) ⟨355019, by rfl⟩ : syracuseStep 473359 = 710039) B710039
theorem B440635 : Blo 307833 440635 := bstep (se 1 (by rfl) ⟨330476, by rfl⟩ : syracuseStep 440635 = 660953) B660953
theorem B309563 : Blo 307833 309563 := bstep (se 1 (by rfl) ⟨232172, by rfl⟩ : syracuseStep 309563 = 464345) B464345
theorem B309639 : Blo 307833 309639 := bstep (se 1 (by rfl) ⟨232229, by rfl⟩ : syracuseStep 309639 = 464459) B464459
theorem B309647 : Blo 307833 309647 := bstep (se 1 (by rfl) ⟨232235, by rfl⟩ : syracuseStep 309647 = 464471) B464471
theorem B1325459 : Blo 307833 1325459 := bstep (se 1 (by rfl) ⟨994094, by rfl⟩ : syracuseStep 1325459 = 1988189) B1988189
theorem B1489337 : Blo 307833 1489337 := bstep (se 2 (by rfl) ⟨558501, by rfl⟩ : syracuseStep 1489337 = 1117003) B1117003
theorem B309691 : Blo 307833 309691 := bstep (se 1 (by rfl) ⟨232268, by rfl⟩ : syracuseStep 309691 = 464537) B464537
theorem B309767 : Blo 307833 309767 := bstep (se 1 (by rfl) ⟨232325, by rfl⟩ : syracuseStep 309767 = 464651) B464651
theorem B309775 : Blo 307833 309775 := bstep (se 1 (by rfl) ⟨232331, by rfl⟩ : syracuseStep 309775 = 464663) B464663
theorem B309819 : Blo 307833 309819 := bstep (se 1 (by rfl) ⟨232364, by rfl⟩ : syracuseStep 309819 = 464729) B464729
theorem B309895 : Blo 307833 309895 := bstep (se 1 (by rfl) ⟨232421, by rfl⟩ : syracuseStep 309895 = 464843) B464843
theorem B309903 : Blo 307833 309903 := bstep (se 1 (by rfl) ⟨232427, by rfl⟩ : syracuseStep 309903 = 464855) B464855
theorem B309947 : Blo 307833 309947 := bstep (se 1 (by rfl) ⟨232460, by rfl⟩ : syracuseStep 309947 = 464921) B464921
theorem B310023 : Blo 307833 310023 := bstep (se 1 (by rfl) ⟨232517, by rfl⟩ : syracuseStep 310023 = 465035) B465035
theorem B310031 : Blo 307833 310031 := bstep (se 1 (by rfl) ⟨232523, by rfl⟩ : syracuseStep 310031 = 465047) B465047
theorem B310075 : Blo 307833 310075 := bstep (se 1 (by rfl) ⟨232556, by rfl⟩ : syracuseStep 310075 = 465113) B465113
theorem B5389145 : Blo 307833 5389145 := bstep (se 2 (by rfl) ⟨2020929, by rfl⟩ : syracuseStep 5389145 = 4041859) B4041859
theorem B310151 : Blo 307833 310151 := bstep (se 1 (by rfl) ⟨232613, by rfl⟩ : syracuseStep 310151 = 465227) B465227
theorem B310159 : Blo 307833 310159 := bstep (se 1 (by rfl) ⟨232619, by rfl⟩ : syracuseStep 310159 = 465239) B465239
theorem B310203 : Blo 307833 310203 := bstep (se 1 (by rfl) ⟨232652, by rfl⟩ : syracuseStep 310203 = 465305) B465305
theorem B310279 : Blo 307833 310279 := bstep (se 1 (by rfl) ⟨232709, by rfl⟩ : syracuseStep 310279 = 465419) B465419
theorem B310287 : Blo 307833 310287 := bstep (se 1 (by rfl) ⟨232715, by rfl⟩ : syracuseStep 310287 = 465431) B465431
theorem B1588247 : Blo 307833 1588247 := bstep (se 1 (by rfl) ⟨1191185, by rfl⟩ : syracuseStep 1588247 = 2382371) B2382371
theorem B310331 : Blo 307833 310331 := bstep (se 1 (by rfl) ⟨232748, by rfl⟩ : syracuseStep 310331 = 465497) B465497
theorem B310407 : Blo 307833 310407 := bstep (se 1 (by rfl) ⟨232805, by rfl⟩ : syracuseStep 310407 = 465611) B465611
theorem B310415 : Blo 307833 310415 := bstep (se 1 (by rfl) ⟨232811, by rfl⟩ : syracuseStep 310415 = 465623) B465623
theorem B310459 : Blo 307833 310459 := bstep (se 1 (by rfl) ⟨232844, by rfl⟩ : syracuseStep 310459 = 465689) B465689
theorem B310535 : Blo 307833 310535 := bstep (se 1 (by rfl) ⟨232901, by rfl⟩ : syracuseStep 310535 = 465803) B465803
theorem B310543 : Blo 307833 310543 := bstep (se 1 (by rfl) ⟨232907, by rfl⟩ : syracuseStep 310543 = 465815) B465815
theorem B834875 : Blo 307833 834875 := bstep (se 1 (by rfl) ⟨626156, by rfl⟩ : syracuseStep 834875 = 1252313) B1252313
theorem B310587 : Blo 307833 310587 := bstep (se 1 (by rfl) ⟨232940, by rfl⟩ : syracuseStep 310587 = 465881) B465881
theorem B310663 : Blo 307833 310663 := bstep (se 1 (by rfl) ⟨232997, by rfl⟩ : syracuseStep 310663 = 465995) B465995
theorem B310671 : Blo 307833 310671 := bstep (se 1 (by rfl) ⟨233003, by rfl⟩ : syracuseStep 310671 = 466007) B466007
theorem B3554705 : Blo 307833 3554705 := bstep (se 2 (by rfl) ⟨1333014, by rfl⟩ : syracuseStep 3554705 = 2666029) B2666029
theorem B3030419 : Blo 307833 3030419 := bstep (se 1 (by rfl) ⟨2272814, by rfl⟩ : syracuseStep 3030419 = 4545629) B4545629
theorem B310715 : Blo 307833 310715 := bstep (se 1 (by rfl) ⟨233036, by rfl⟩ : syracuseStep 310715 = 466073) B466073
theorem B310791 : Blo 307833 310791 := bstep (se 1 (by rfl) ⟨233093, by rfl⟩ : syracuseStep 310791 = 466187) B466187
theorem B310799 : Blo 307833 310799 := bstep (se 1 (by rfl) ⟨233099, by rfl⟩ : syracuseStep 310799 = 466199) B466199
theorem B310843 : Blo 307833 310843 := bstep (se 1 (by rfl) ⟨233132, by rfl⟩ : syracuseStep 310843 = 466265) B466265
theorem B2342519 : Blo 307833 2342519 := bstep (se 1 (by rfl) ⟨1756889, by rfl⟩ : syracuseStep 2342519 = 3513779) B3513779
theorem B704135 : Blo 307833 704135 := bstep (se 1 (by rfl) ⟨528101, by rfl⟩ : syracuseStep 704135 = 1056203) B1056203
theorem B310919 : Blo 307833 310919 := bstep (se 1 (by rfl) ⟨233189, by rfl⟩ : syracuseStep 310919 = 466379) B466379
theorem B310927 : Blo 307833 310927 := bstep (se 1 (by rfl) ⟨233195, by rfl⟩ : syracuseStep 310927 = 466391) B466391
theorem B310971 : Blo 307833 310971 := bstep (se 1 (by rfl) ⟨233228, by rfl⟩ : syracuseStep 310971 = 466457) B466457
theorem B311047 : Blo 307833 311047 := bstep (se 1 (by rfl) ⟨233285, by rfl⟩ : syracuseStep 311047 = 466571) B466571
theorem B311055 : Blo 307833 311055 := bstep (se 1 (by rfl) ⟨233291, by rfl⟩ : syracuseStep 311055 = 466583) B466583
theorem B311099 : Blo 307833 311099 := bstep (se 1 (by rfl) ⟨233324, by rfl⟩ : syracuseStep 311099 = 466649) B466649
theorem B311175 : Blo 307833 311175 := bstep (se 1 (by rfl) ⟨233381, by rfl⟩ : syracuseStep 311175 = 466763) B466763
theorem B311183 : Blo 307833 311183 := bstep (se 1 (by rfl) ⟨233387, by rfl⟩ : syracuseStep 311183 = 466775) B466775
theorem B311227 : Blo 307833 311227 := bstep (se 1 (by rfl) ⟨233420, by rfl⟩ : syracuseStep 311227 = 466841) B466841
theorem B311303 : Blo 307833 311303 := bstep (se 1 (by rfl) ⟨233477, by rfl⟩ : syracuseStep 311303 = 466955) B466955
theorem B311311 : Blo 307833 311311 := bstep (se 1 (by rfl) ⟨233483, by rfl⟩ : syracuseStep 311311 = 466967) B466967
theorem B311355 : Blo 307833 311355 := bstep (se 1 (by rfl) ⟨233516, by rfl⟩ : syracuseStep 311355 = 467033) B467033
theorem B311431 : Blo 307833 311431 := bstep (se 1 (by rfl) ⟨233573, by rfl⟩ : syracuseStep 311431 = 467147) B467147
theorem B311439 : Blo 307833 311439 := bstep (se 1 (by rfl) ⟨233579, by rfl⟩ : syracuseStep 311439 = 467159) B467159
theorem B311483 : Blo 307833 311483 := bstep (se 1 (by rfl) ⟨233612, by rfl⟩ : syracuseStep 311483 = 467225) B467225
theorem B311559 : Blo 307833 311559 := bstep (se 1 (by rfl) ⟨233669, by rfl⟩ : syracuseStep 311559 = 467339) B467339
theorem B704783 : Blo 307833 704783 := bstep (se 1 (by rfl) ⟨528587, by rfl⟩ : syracuseStep 704783 = 1057175) B1057175
theorem B311567 : Blo 307833 311567 := bstep (se 1 (by rfl) ⟨233675, by rfl⟩ : syracuseStep 311567 = 467351) B467351
theorem B311611 : Blo 307833 311611 := bstep (se 1 (by rfl) ⟨233708, by rfl⟩ : syracuseStep 311611 = 467417) B467417
theorem B311687 : Blo 307833 311687 := bstep (se 1 (by rfl) ⟨233765, by rfl⟩ : syracuseStep 311687 = 467531) B467531
theorem B311695 : Blo 307833 311695 := bstep (se 1 (by rfl) ⟨233771, by rfl⟩ : syracuseStep 311695 = 467543) B467543
theorem B311739 : Blo 307833 311739 := bstep (se 1 (by rfl) ⟨233804, by rfl⟩ : syracuseStep 311739 = 467609) B467609
theorem B311815 : Blo 307833 311815 := bstep (se 1 (by rfl) ⟨233861, by rfl⟩ : syracuseStep 311815 = 467723) B467723
theorem B311823 : Blo 307833 311823 := bstep (se 1 (by rfl) ⟨233867, by rfl⟩ : syracuseStep 311823 = 467735) B467735
theorem B5980715 : Blo 307833 5980715 := bstep (se 1 (by rfl) ⟨4485536, by rfl⟩ : syracuseStep 5980715 = 8971073) B8971073
theorem B2343491 : Blo 307833 2343491 := bstep (se 1 (by rfl) ⟨1757618, by rfl⟩ : syracuseStep 2343491 = 3515237) B3515237
theorem B442999 : Blo 307833 442999 := bstep (se 1 (by rfl) ⟨332249, by rfl⟩ : syracuseStep 442999 = 664499) B664499
theorem B803627 : Blo 307833 803627 := bstep (se 1 (by rfl) ⟨602720, by rfl⟩ : syracuseStep 803627 = 1205441) B1205441
theorem B443323 : Blo 307833 443323 := bstep (se 1 (by rfl) ⟨332492, by rfl⟩ : syracuseStep 443323 = 664985) B664985
theorem B1885187 : Blo 307833 1885187 := bstep (se 1 (by rfl) ⟨1413890, by rfl⟩ : syracuseStep 1885187 = 2827781) B2827781
theorem B1754135 : Blo 307833 1754135 := bstep (se 1 (by rfl) ⟨1315601, by rfl⟩ : syracuseStep 1754135 = 2631203) B2631203
theorem B1590359 : Blo 307833 1590359 := bstep (se 1 (by rfl) ⟨1192769, by rfl⟩ : syracuseStep 1590359 = 2385539) B2385539
theorem B1328329 : Blo 307833 1328329 := bstep (se 2 (by rfl) ⟨498123, by rfl⟩ : syracuseStep 1328329 = 996247) B996247
theorem B1328399 : Blo 307833 1328399 := bstep (se 1 (by rfl) ⟨996299, by rfl⟩ : syracuseStep 1328399 = 1992599) B1992599
theorem B5064067 : Blo 307833 5064067 := bstep (se 1 (by rfl) ⟨3798050, by rfl⟩ : syracuseStep 5064067 = 7596101) B7596101
theorem B3523985 : Blo 307833 3523985 := bstep (se 2 (by rfl) ⟨1321494, by rfl⟩ : syracuseStep 3523985 = 2642989) B2642989
theorem B443819 : Blo 307833 443819 := bstep (se 1 (by rfl) ⟨332864, by rfl⟩ : syracuseStep 443819 = 665729) B665729
theorem B1590749 : Blo 307833 1590749 := bstep (se 3 (by rfl) ⟨298265, by rfl⟩ : syracuseStep 1590749 = 596531) B596531
theorem B476987 : Blo 307833 476987 := bstep (se 1 (by rfl) ⟨357740, by rfl⟩ : syracuseStep 476987 = 715481) B715481
theorem B51136433 : Blo 307833 51136433 := bstep (se 2 (by rfl) ⟨19176162, by rfl⟩ : syracuseStep 51136433 = 38352325) B38352325
theorem B837643 : Blo 307833 837643 := bstep (se 1 (by rfl) ⟨628232, by rfl⟩ : syracuseStep 837643 = 1256465) B1256465
theorem B346639 : Blo 307833 346639 := bstep (se 1 (by rfl) ⟨259979, by rfl⟩ : syracuseStep 346639 = 519959) B519959
theorem B4508227 : Blo 307833 4508227 := bstep (se 1 (by rfl) ⟨3381170, by rfl⟩ : syracuseStep 4508227 = 6762341) B6762341
theorem B2247439 : Blo 307833 2247439 := bstep (se 1 (by rfl) ⟨1685579, by rfl⟩ : syracuseStep 2247439 = 3371159) B3371159
theorem B1559411 : Blo 307833 1559411 := bstep (se 1 (by rfl) ⟨1169558, by rfl⟩ : syracuseStep 1559411 = 2339117) B2339117
theorem B347143 : Blo 307833 347143 := bstep (se 1 (by rfl) ⟨260357, by rfl⟩ : syracuseStep 347143 = 520715) B520715
theorem B445447 : Blo 307833 445447 := bstep (se 1 (by rfl) ⟨334085, by rfl⟩ : syracuseStep 445447 = 668171) B668171
theorem B347323 : Blo 307833 347323 := bstep (se 1 (by rfl) ⟨260492, by rfl⟩ : syracuseStep 347323 = 520985) B520985
theorem B1494217 : Blo 307833 1494217 := bstep (se 2 (by rfl) ⟨560331, by rfl⟩ : syracuseStep 1494217 = 1120663) B1120663
theorem B1559897 : Blo 307833 1559897 := bstep (se 2 (by rfl) ⟨584961, by rfl⟩ : syracuseStep 1559897 = 1169923) B1169923
theorem B839027 : Blo 307833 839027 := bstep (se 1 (by rfl) ⟨629270, by rfl⟩ : syracuseStep 839027 = 1258541) B1258541
theorem B2116999 : Blo 307833 2116999 := bstep (se 1 (by rfl) ⟨1587749, by rfl⟩ : syracuseStep 2116999 = 3175499) B3175499
theorem B11849165 : Blo 307833 11849165 := bstep (se 3 (by rfl) ⟨2221718, by rfl⟩ : syracuseStep 11849165 = 4443437) B4443437
theorem B1330775 : Blo 307833 1330775 := bstep (se 1 (by rfl) ⟨998081, by rfl⟩ : syracuseStep 1330775 = 1996163) B1996163
theorem B347791 : Blo 307833 347791 := bstep (se 1 (by rfl) ⟨260843, by rfl⟩ : syracuseStep 347791 = 521687) B521687
theorem B1986241 : Blo 307833 1986241 := bstep (se 2 (by rfl) ⟨744840, by rfl⟩ : syracuseStep 1986241 = 1489681) B1489681
theorem B741305 : Blo 307833 741305 := bstep (se 2 (by rfl) ⟨277989, by rfl⟩ : syracuseStep 741305 = 555979) B555979
theorem B348295 : Blo 307833 348295 := bstep (se 1 (by rfl) ⟨261221, by rfl⟩ : syracuseStep 348295 = 522443) B522443
theorem B3526901 : Blo 307833 3526901 := bstep (se 5 (by rfl) ⟨165323, by rfl⟩ : syracuseStep 3526901 = 330647) B330647
theorem B348475 : Blo 307833 348475 := bstep (se 1 (by rfl) ⟨261356, by rfl⟩ : syracuseStep 348475 = 522713) B522713
theorem B840023 : Blo 307833 840023 := bstep (se 1 (by rfl) ⟨630017, by rfl⟩ : syracuseStep 840023 = 1260035) B1260035
theorem B3232145 : Blo 307833 3232145 := bstep (se 2 (by rfl) ⟨1212054, by rfl⟩ : syracuseStep 3232145 = 2424109) B2424109
theorem B348943 : Blo 307833 348943 := bstep (se 1 (by rfl) ⟨261707, by rfl⟩ : syracuseStep 348943 = 523415) B523415
theorem B24171317 : Blo 307833 24171317 := bstep (se 5 (by rfl) ⟨1133030, by rfl⟩ : syracuseStep 24171317 = 2266061) B2266061
theorem B2347865 : Blo 307833 2347865 := bstep (se 2 (by rfl) ⟨880449, by rfl⟩ : syracuseStep 2347865 = 1760899) B1760899
theorem B349447 : Blo 307833 349447 := bstep (se 1 (by rfl) ⟨262085, by rfl⟩ : syracuseStep 349447 = 524171) B524171
theorem B1496353 : Blo 307833 1496353 := bstep (se 2 (by rfl) ⟨561132, by rfl⟩ : syracuseStep 1496353 = 1122265) B1122265
theorem B1562003 : Blo 307833 1562003 := bstep (se 1 (by rfl) ⟨1171502, by rfl⟩ : syracuseStep 1562003 = 2343005) B2343005
theorem B349627 : Blo 307833 349627 := bstep (se 1 (by rfl) ⟨262220, by rfl⟩ : syracuseStep 349627 = 524441) B524441
theorem B8509157 : Blo 307833 8509157 := bstep (se 4 (by rfl) ⟨797733, by rfl⟩ : syracuseStep 8509157 = 1595467) B1595467
theorem B2348837 : Blo 307833 2348837 := bstep (se 4 (by rfl) ⟨220203, by rfl⟩ : syracuseStep 2348837 = 440407) B440407
theorem B743303 : Blo 307833 743303 := bstep (se 1 (by rfl) ⟨557477, by rfl⟩ : syracuseStep 743303 = 1114955) B1114955
theorem B350095 : Blo 307833 350095 := bstep (se 1 (by rfl) ⟨262571, by rfl⟩ : syracuseStep 350095 = 525143) B525143
theorem B1169437 : Blo 307833 1169437 := bstep (se 3 (by rfl) ⟨219269, by rfl⟩ : syracuseStep 1169437 = 438539) B438539
theorem B87447605 : Blo 307833 87447605 := bstep (se 5 (by rfl) ⟨4099106, by rfl⟩ : syracuseStep 87447605 = 8198213) B8198213
theorem B350599 : Blo 307833 350599 := bstep (se 1 (by rfl) ⟨262949, by rfl⟩ : syracuseStep 350599 = 525899) B525899
theorem B1432075 : Blo 307833 1432075 := bstep (se 1 (by rfl) ⟨1074056, by rfl⟩ : syracuseStep 1432075 = 2148113) B2148113
theorem B350779 : Blo 307833 350779 := bstep (se 1 (by rfl) ⟨263084, by rfl⟩ : syracuseStep 350779 = 526169) B526169
theorem B3005047 : Blo 307833 3005047 := bstep (se 1 (by rfl) ⟨2253785, by rfl⟩ : syracuseStep 3005047 = 4507571) B4507571
theorem B1989805 : Blo 307833 1989805 := bstep (se 3 (by rfl) ⟨373088, by rfl⟩ : syracuseStep 1989805 = 746177) B746177
theorem B1039769 : Blo 307833 1039769 := bstep (se 2 (by rfl) ⟨389913, by rfl⟩ : syracuseStep 1039769 = 779827) B779827
theorem B3333581 : Blo 307833 3333581 := bstep (se 3 (by rfl) ⟨625046, by rfl⟩ : syracuseStep 3333581 = 1250093) B1250093
theorem B745487 : Blo 307833 745487 := bstep (se 1 (by rfl) ⟨559115, by rfl⟩ : syracuseStep 745487 = 1118231) B1118231
theorem B1040471 : Blo 307833 1040471 := bstep (se 1 (by rfl) ⟨780353, by rfl⟩ : syracuseStep 1040471 = 1560707) B1560707
theorem B876919 : Blo 307833 876919 := bstep (se 1 (by rfl) ⟨657689, by rfl⟩ : syracuseStep 876919 = 1315379) B1315379
theorem B1565081 : Blo 307833 1565081 := bstep (se 2 (by rfl) ⟨586905, by rfl⟩ : syracuseStep 1565081 = 1173811) B1173811
theorem B1040957 : Blo 307833 1040957 := bstep (se 3 (by rfl) ⟨195179, by rfl⟩ : syracuseStep 1040957 = 390359) B390359
theorem B1172339 : Blo 307833 1172339 := bstep (se 1 (by rfl) ⟨879254, by rfl⟩ : syracuseStep 1172339 = 1758509) B1758509
theorem B877853 : Blo 307833 877853 := bstep (se 3 (by rfl) ⟨164597, by rfl⟩ : syracuseStep 877853 = 329195) B329195
theorem B1500619 : Blo 307833 1500619 := bstep (se 1 (by rfl) ⟨1125464, by rfl⟩ : syracuseStep 1500619 = 2250929) B2250929
theorem B779777 : Blo 307833 779777 := bstep (se 2 (by rfl) ⟨292416, by rfl⟩ : syracuseStep 779777 = 584833) B584833
theorem B1762883 : Blo 307833 1762883 := bstep (se 1 (by rfl) ⟨1322162, by rfl⟩ : syracuseStep 1762883 = 2644325) B2644325
theorem B878195 : Blo 307833 878195 := bstep (se 1 (by rfl) ⟨658646, by rfl⟩ : syracuseStep 878195 = 1317293) B1317293
theorem B780151 : Blo 307833 780151 := bstep (se 1 (by rfl) ⟨585113, by rfl⟩ : syracuseStep 780151 = 1170227) B1170227
theorem B1042361 : Blo 307833 1042361 := bstep (se 2 (by rfl) ⟨390885, by rfl⟩ : syracuseStep 1042361 = 781771) B781771
theorem B878651 : Blo 307833 878651 := bstep (se 1 (by rfl) ⟨658988, by rfl⟩ : syracuseStep 878651 = 1317977) B1317977
theorem B419899 : Blo 307833 419899 := bstep (se 1 (by rfl) ⟨314924, by rfl⟩ : syracuseStep 419899 = 629849) B629849
theorem B780587 : Blo 307833 780587 := bstep (se 1 (by rfl) ⟨585440, by rfl⟩ : syracuseStep 780587 = 1170881) B1170881
theorem B3369347 : Blo 307833 3369347 := bstep (se 1 (by rfl) ⟨2527010, by rfl⟩ : syracuseStep 3369347 = 5054021) B5054021
theorem B2222471 : Blo 307833 2222471 := bstep (se 1 (by rfl) ⟨1666853, by rfl⟩ : syracuseStep 2222471 = 3333707) B3333707
theorem B1042955 : Blo 307833 1042955 := bstep (se 1 (by rfl) ⟨782216, by rfl⟩ : syracuseStep 1042955 = 1564433) B1564433
theorem B1043063 : Blo 307833 1043063 := bstep (se 1 (by rfl) ⟨782297, by rfl⟩ : syracuseStep 1043063 = 1564595) B1564595
theorem B584491 : Blo 307833 584491 := bstep (se 1 (by rfl) ⟨438368, by rfl⟩ : syracuseStep 584491 = 876737) B876737
theorem B748331 : Blo 307833 748331 := bstep (se 1 (by rfl) ⟨561248, by rfl⟩ : syracuseStep 748331 = 1122497) B1122497
theorem B584567 : Blo 307833 584567 := bstep (se 1 (by rfl) ⟨438425, by rfl⟩ : syracuseStep 584567 = 876851) B876851
theorem B1567673 : Blo 307833 1567673 := bstep (se 2 (by rfl) ⟨587877, by rfl⟩ : syracuseStep 1567673 = 1175755) B1175755
theorem B1174571 : Blo 307833 1174571 := bstep (se 1 (by rfl) ⟨880928, by rfl⟩ : syracuseStep 1174571 = 1761857) B1761857
theorem B781427 : Blo 307833 781427 := bstep (se 1 (by rfl) ⟨586070, by rfl⟩ : syracuseStep 781427 = 1172141) B1172141
theorem B781447 : Blo 307833 781447 := bstep (se 1 (by rfl) ⟨586085, by rfl⟩ : syracuseStep 781447 = 1172171) B1172171
theorem B421049 : Blo 307833 421049 := bstep (se 2 (by rfl) ⟨157893, by rfl⟩ : syracuseStep 421049 = 315787) B315787
theorem B1043657 : Blo 307833 1043657 := bstep (se 2 (by rfl) ⟨391371, by rfl⟩ : syracuseStep 1043657 = 782743) B782743
theorem B781721 : Blo 307833 781721 := bstep (se 2 (by rfl) ⟨293145, by rfl⟩ : syracuseStep 781721 = 586291) B586291
theorem B781883 : Blo 307833 781883 := bstep (se 1 (by rfl) ⟨586412, by rfl⟩ : syracuseStep 781883 = 1172825) B1172825
theorem B782095 : Blo 307833 782095 := bstep (se 1 (by rfl) ⟨586571, by rfl⟩ : syracuseStep 782095 = 1173143) B1173143
theorem B519979 : Blo 307833 519979 := bstep (se 1 (by rfl) ⟨389984, by rfl⟩ : syracuseStep 519979 = 779969) B779969
theorem B4321073 : Blo 307833 4321073 := bstep (se 2 (by rfl) ⟨1620402, by rfl⟩ : syracuseStep 4321073 = 3240805) B3240805
theorem B1044359 : Blo 307833 1044359 := bstep (se 1 (by rfl) ⟨783269, by rfl⟩ : syracuseStep 1044359 = 1566539) B1566539
theorem B1765273 : Blo 307833 1765273 := bstep (se 2 (by rfl) ⟨661977, by rfl⟩ : syracuseStep 1765273 = 1323955) B1323955
theorem B5369753 : Blo 307833 5369753 := bstep (se 2 (by rfl) ⟨2013657, by rfl⟩ : syracuseStep 5369753 = 4027315) B4027315
theorem B520121 : Blo 307833 520121 := bstep (se 2 (by rfl) ⟨195045, by rfl⟩ : syracuseStep 520121 = 390091) B390091
theorem B782369 : Blo 307833 782369 := bstep (se 2 (by rfl) ⟨293388, by rfl⟩ : syracuseStep 782369 = 586777) B586777
theorem B1568969 : Blo 307833 1568969 := bstep (se 2 (by rfl) ⟨588363, by rfl⟩ : syracuseStep 1568969 = 1176727) B1176727
theorem B1044737 : Blo 307833 1044737 := bstep (se 2 (by rfl) ⟨391776, by rfl⟩ : syracuseStep 1044737 = 783553) B783553
theorem B1601927 : Blo 307833 1601927 := bstep (se 1 (by rfl) ⟨1201445, by rfl⟩ : syracuseStep 1601927 = 2402891) B2402891
theorem B1503623 : Blo 307833 1503623 := bstep (se 1 (by rfl) ⟨1127717, by rfl⟩ : syracuseStep 1503623 = 2255435) B2255435
theorem B2355641 : Blo 307833 2355641 := bstep (se 2 (by rfl) ⟨883365, by rfl⟩ : syracuseStep 2355641 = 1766731) B1766731
theorem B520823 : Blo 307833 520823 := bstep (se 1 (by rfl) ⟨390617, by rfl⟩ : syracuseStep 520823 = 781235) B781235
theorem B389767 : Blo 307833 389767 := bstep (se 1 (by rfl) ⟨292325, by rfl⟩ : syracuseStep 389767 = 584651) B584651
theorem B2880193 : Blo 307833 2880193 := bstep (se 2 (by rfl) ⟨1080072, by rfl⟩ : syracuseStep 2880193 = 2160145) B2160145
theorem B586511 : Blo 307833 586511 := bstep (se 1 (by rfl) ⟨439883, by rfl⟩ : syracuseStep 586511 = 879767) B879767
theorem B881543 : Blo 307833 881543 := bstep (se 1 (by rfl) ⟨661157, by rfl⟩ : syracuseStep 881543 = 1322315) B1322315
theorem B783371 : Blo 307833 783371 := bstep (se 1 (by rfl) ⟨587528, by rfl⟩ : syracuseStep 783371 = 1175057) B1175057
theorem B390187 : Blo 307833 390187 := bstep (se 1 (by rfl) ⟨292640, by rfl⟩ : syracuseStep 390187 = 585281) B585281
theorem B1045547 : Blo 307833 1045547 := bstep (se 1 (by rfl) ⟨784160, by rfl⟩ : syracuseStep 1045547 = 1568321) B1568321
theorem B521275 : Blo 307833 521275 := bstep (se 1 (by rfl) ⟨390956, by rfl⟩ : syracuseStep 521275 = 781913) B781913
theorem B521417 : Blo 307833 521417 := bstep (se 2 (by rfl) ⟨195531, by rfl⟩ : syracuseStep 521417 = 391063) B391063
theorem B390415 : Blo 307833 390415 := bstep (se 1 (by rfl) ⟨292811, by rfl⟩ : syracuseStep 390415 = 585623) B585623
theorem B784019 : Blo 307833 784019 := bstep (se 1 (by rfl) ⟨588014, by rfl⟩ : syracuseStep 784019 = 1176029) B1176029
theorem B1996595 : Blo 307833 1996595 := bstep (se 1 (by rfl) ⟨1497446, by rfl⟩ : syracuseStep 1996595 = 2994893) B2994893
theorem B1767257 : Blo 307833 1767257 := bstep (se 2 (by rfl) ⟨662721, by rfl⟩ : syracuseStep 1767257 = 1325443) B1325443
theorem B522119 : Blo 307833 522119 := bstep (se 1 (by rfl) ⟨391589, by rfl⟩ : syracuseStep 522119 = 783179) B783179
theorem B784313 : Blo 307833 784313 := bstep (se 2 (by rfl) ⟨294117, by rfl⟩ : syracuseStep 784313 = 588235) B588235
theorem B2979787 : Blo 307833 2979787 := bstep (se 1 (by rfl) ⟨2234840, by rfl⟩ : syracuseStep 2979787 = 4469681) B4469681
theorem B391159 : Blo 307833 391159 := bstep (se 1 (by rfl) ⟨293369, by rfl⟩ : syracuseStep 391159 = 586739) B586739
theorem B751769 : Blo 307833 751769 := bstep (se 2 (by rfl) ⟨281913, by rfl⟩ : syracuseStep 751769 = 563827) B563827
theorem B391483 : Blo 307833 391483 := bstep (se 1 (by rfl) ⟨293612, by rfl⟩ : syracuseStep 391483 = 587225) B587225
theorem B1046843 : Blo 307833 1046843 := bstep (se 1 (by rfl) ⟨785132, by rfl⟩ : syracuseStep 1046843 = 1570265) B1570265
theorem B588151 : Blo 307833 588151 := bstep (se 1 (by rfl) ⟨441113, by rfl⟩ : syracuseStep 588151 = 882227) B882227
theorem B1178003 : Blo 307833 1178003 := bstep (se 1 (by rfl) ⟨883502, by rfl⟩ : syracuseStep 1178003 = 1767005) B1767005
theorem B522767 : Blo 307833 522767 := bstep (se 1 (by rfl) ⟨392075, by rfl⟩ : syracuseStep 522767 = 784151) B784151
theorem B785011 : Blo 307833 785011 := bstep (se 1 (by rfl) ⟨588758, by rfl⟩ : syracuseStep 785011 = 1177517) B1177517
theorem B785153 : Blo 307833 785153 := bstep (se 2 (by rfl) ⟨294432, by rfl⟩ : syracuseStep 785153 = 588865) B588865
theorem B883457 : Blo 307833 883457 := bstep (se 2 (by rfl) ⟨331296, by rfl⟩ : syracuseStep 883457 = 662593) B662593
theorem B752395 : Blo 307833 752395 := bstep (se 1 (by rfl) ⟨564296, by rfl⟩ : syracuseStep 752395 = 1128593) B1128593
theorem B1047329 : Blo 307833 1047329 := bstep (se 2 (by rfl) ⟨392748, by rfl⟩ : syracuseStep 1047329 = 785497) B785497
theorem B391979 : Blo 307833 391979 := bstep (se 1 (by rfl) ⟨293984, by rfl⟩ : syracuseStep 391979 = 587969) B587969
theorem B555835 : Blo 307833 555835 := bstep (se 1 (by rfl) ⟨416876, by rfl⟩ : syracuseStep 555835 = 833753) B833753
theorem B523307 : Blo 307833 523307 := bstep (se 1 (by rfl) ⟨392480, by rfl⟩ : syracuseStep 523307 = 784961) B784961
theorem B785609 : Blo 307833 785609 := bstep (se 2 (by rfl) ⟨294603, by rfl⟩ : syracuseStep 785609 = 589207) B589207
theorem B392455 : Blo 307833 392455 := bstep (se 1 (by rfl) ⟨294341, by rfl⟩ : syracuseStep 392455 = 588683) B588683
theorem B18513197 : Blo 307833 18513197 := bstep (se 3 (by rfl) ⟨3471224, by rfl⟩ : syracuseStep 18513197 = 6942449) B6942449
theorem B884027 : Blo 307833 884027 := bstep (se 1 (by rfl) ⟨663020, by rfl⟩ : syracuseStep 884027 = 1326041) B1326041
theorem B1047923 : Blo 307833 1047923 := bstep (se 1 (by rfl) ⟨785942, by rfl⟩ : syracuseStep 1047923 = 1571885) B1571885
theorem B523705 : Blo 307833 523705 := bstep (se 2 (by rfl) ⟨196389, by rfl⟩ : syracuseStep 523705 = 392779) B392779
theorem B785963 : Blo 307833 785963 := bstep (se 1 (by rfl) ⟨589472, by rfl⟩ : syracuseStep 785963 = 1178945) B1178945
theorem B884267 : Blo 307833 884267 := bstep (se 1 (by rfl) ⟨663200, by rfl⟩ : syracuseStep 884267 = 1326401) B1326401
theorem B851609 : Blo 307833 851609 := bstep (se 2 (by rfl) ⟨319353, by rfl⟩ : syracuseStep 851609 = 638707) B638707
theorem B392951 : Blo 307833 392951 := bstep (se 1 (by rfl) ⟨294713, by rfl⟩ : syracuseStep 392951 = 589427) B589427
theorem B393103 : Blo 307833 393103 := bstep (se 1 (by rfl) ⟨294827, by rfl⟩ : syracuseStep 393103 = 589655) B589655
theorem B1114003 : Blo 307833 1114003 := bstep (se 1 (by rfl) ⟨835502, by rfl⟩ : syracuseStep 1114003 = 1671005) B1671005
theorem B2817995 : Blo 307833 2817995 := bstep (se 1 (by rfl) ⟨2113496, by rfl⟩ : syracuseStep 2817995 = 4226993) B4226993
theorem B1048733 : Blo 307833 1048733 := bstep (se 3 (by rfl) ⟨196637, by rfl⟩ : syracuseStep 1048733 = 393275) B393275
theorem B1573181 : Blo 307833 1573181 := bstep (se 3 (by rfl) ⟨294971, by rfl⟩ : syracuseStep 1573181 = 589943) B589943
theorem B885097 : Blo 307833 885097 := bstep (se 2 (by rfl) ⟨331911, by rfl⟩ : syracuseStep 885097 = 663823) B663823
theorem B786793 : Blo 307833 786793 := bstep (se 2 (by rfl) ⟨295047, by rfl⟩ : syracuseStep 786793 = 590095) B590095
theorem B393655 : Blo 307833 393655 := bstep (se 1 (by rfl) ⟨295241, by rfl⟩ : syracuseStep 393655 = 590483) B590483
theorem B524731 : Blo 307833 524731 := bstep (se 1 (by rfl) ⟨393548, by rfl⟩ : syracuseStep 524731 = 787097) B787097
theorem B524839 : Blo 307833 524839 := bstep (se 1 (by rfl) ⟨393629, by rfl⟩ : syracuseStep 524839 = 787259) B787259
theorem B932774453 : Blo 307833 932774453 := bstep (se 5 (by rfl) ⟨43723802, by rfl⟩ : syracuseStep 932774453 = 87447605) B87447605
theorem B787067 : Blo 307833 787067 := bstep (se 1 (by rfl) ⟨590300, by rfl⟩ : syracuseStep 787067 = 1180601) B1180601
theorem B1049273 : Blo 307833 1049273 := bstep (se 2 (by rfl) ⟨393477, by rfl⟩ : syracuseStep 1049273 = 786955) B786955
theorem B590665 : Blo 307833 590665 := bstep (se 2 (by rfl) ⟨221499, by rfl⟩ : syracuseStep 590665 = 442999) B442999
theorem B885599 : Blo 307833 885599 := bstep (se 1 (by rfl) ⟨664199, by rfl⟩ : syracuseStep 885599 = 1328399) B1328399
theorem B525163 : Blo 307833 525163 := bstep (se 1 (by rfl) ⟨393872, by rfl⟩ : syracuseStep 525163 = 787745) B787745
theorem B2982977 : Blo 307833 2982977 := bstep (se 2 (by rfl) ⟨1118616, by rfl⟩ : syracuseStep 2982977 = 2237233) B2237233
theorem B885917 : Blo 307833 885917 := bstep (se 3 (by rfl) ⟨166109, by rfl⟩ : syracuseStep 885917 = 332219) B332219
theorem B1180919 : Blo 307833 1180919 := bstep (se 1 (by rfl) ⟨885689, by rfl⟩ : syracuseStep 1180919 = 1771379) B1771379
theorem B1049867 : Blo 307833 1049867 := bstep (se 1 (by rfl) ⟨787400, by rfl⟩ : syracuseStep 1049867 = 1574801) B1574801
theorem B1050137 : Blo 307833 1050137 := bstep (se 2 (by rfl) ⟨393801, by rfl⟩ : syracuseStep 1050137 = 787603) B787603
theorem B1771105 : Blo 307833 1771105 := bstep (se 2 (by rfl) ⟨664164, by rfl⟩ : syracuseStep 1771105 = 1328329) B1328329
theorem B886601 : Blo 307833 886601 := bstep (se 2 (by rfl) ⟨332475, by rfl⟩ : syracuseStep 886601 = 664951) B664951
theorem B6752089 : Blo 307833 6752089 := bstep (se 2 (by rfl) ⟨2532033, by rfl⟩ : syracuseStep 6752089 = 5064067) B5064067
theorem B2000825 : Blo 307833 2000825 := bstep (se 2 (by rfl) ⟨750309, by rfl⟩ : syracuseStep 2000825 = 1500619) B1500619
theorem B1181891 : Blo 307833 1181891 := bstep (se 1 (by rfl) ⟨886418, by rfl⟩ : syracuseStep 1181891 = 1772837) B1772837
theorem B559351 : Blo 307833 559351 := bstep (se 1 (by rfl) ⟨419513, by rfl⟩ : syracuseStep 559351 = 839027) B839027
theorem B7899443 : Blo 307833 7899443 := bstep (se 1 (by rfl) ⟨5924582, by rfl⟩ : syracuseStep 7899443 = 11849165) B11849165
theorem B887183 : Blo 307833 887183 := bstep (se 1 (by rfl) ⟨665387, by rfl⟩ : syracuseStep 887183 = 1330775) B1330775
theorem B788879 : Blo 307833 788879 := bstep (se 1 (by rfl) ⟨591659, by rfl⟩ : syracuseStep 788879 = 1183319) B1183319
theorem B330203 : Blo 307833 330203 := bstep (se 1 (by rfl) ⟨247652, by rfl⟩ : syracuseStep 330203 = 495305) B495305
theorem B1575449 : Blo 307833 1575449 := bstep (se 2 (by rfl) ⟨590793, by rfl⟩ : syracuseStep 1575449 = 1181587) B1181587
theorem B625249 : Blo 307833 625249 := bstep (se 2 (by rfl) ⟨234468, by rfl⟩ : syracuseStep 625249 = 468937) B468937
theorem B494203 : Blo 307833 494203 := bstep (se 1 (by rfl) ⟨370652, by rfl⟩ : syracuseStep 494203 = 741305) B741305
theorem B1051271 : Blo 307833 1051271 := bstep (se 1 (by rfl) ⟨788453, by rfl⟩ : syracuseStep 1051271 = 1576907) B1576907
theorem B1182347 : Blo 307833 1182347 := bstep (se 1 (by rfl) ⟨886760, by rfl⟩ : syracuseStep 1182347 = 1773521) B1773521
theorem B1116857 : Blo 307833 1116857 := bstep (se 2 (by rfl) ⟨418821, by rfl⟩ : syracuseStep 1116857 = 837643) B837643
theorem B1051325 : Blo 307833 1051325 := bstep (se 3 (by rfl) ⟨197123, by rfl⟩ : syracuseStep 1051325 = 394247) B394247
theorem B789203 : Blo 307833 789203 := bstep (se 1 (by rfl) ⟨591902, by rfl⟩ : syracuseStep 789203 = 1183805) B1183805
theorem B559865 : Blo 307833 559865 := bstep (se 2 (by rfl) ⟨209949, by rfl⟩ : syracuseStep 559865 = 419899) B419899
theorem B1182559 : Blo 307833 1182559 := bstep (se 1 (by rfl) ⟨886919, by rfl⟩ : syracuseStep 1182559 = 1773839) B1773839
theorem B1051487 : Blo 307833 1051487 := bstep (se 1 (by rfl) ⟨788615, by rfl⟩ : syracuseStep 1051487 = 1577231) B1577231
theorem B560015 : Blo 307833 560015 := bstep (se 1 (by rfl) ⟨420011, by rfl⟩ : syracuseStep 560015 = 840023) B840023
theorem B1051649 : Blo 307833 1051649 := bstep (se 2 (by rfl) ⟨394368, by rfl⟩ : syracuseStep 1051649 = 788737) B788737
theorem B1772563 : Blo 307833 1772563 := bstep (se 1 (by rfl) ⟨1329422, by rfl⟩ : syracuseStep 1772563 = 2658845) B2658845
theorem B461903 : Blo 307833 461903 := bstep (se 1 (by rfl) ⟨346427, by rfl⟩ : syracuseStep 461903 = 692855) B692855
theorem B462023 : Blo 307833 462023 := bstep (se 1 (by rfl) ⟨346517, by rfl⟩ : syracuseStep 462023 = 693035) B693035
theorem B16026917 : Blo 307833 16026917 := bstep (se 4 (by rfl) ⟨1502523, by rfl⟩ : syracuseStep 16026917 = 3005047) B3005047
theorem B462185 : Blo 307833 462185 := bstep (se 2 (by rfl) ⟨173319, by rfl⟩ : syracuseStep 462185 = 346639) B346639
theorem B462263 : Blo 307833 462263 := bstep (se 1 (by rfl) ⟨346697, by rfl⟩ : syracuseStep 462263 = 693395) B693395
theorem B462299 : Blo 307833 462299 := bstep (se 1 (by rfl) ⟨346724, by rfl⟩ : syracuseStep 462299 = 693449) B693449
theorem B1183517 : Blo 307833 1183517 := bstep (se 3 (by rfl) ⟨221909, by rfl⟩ : syracuseStep 1183517 = 443819) B443819
theorem B1183531 : Blo 307833 1183531 := bstep (se 1 (by rfl) ⟨887648, by rfl⟩ : syracuseStep 1183531 = 1775297) B1775297
theorem B5672771 : Blo 307833 5672771 := bstep (se 1 (by rfl) ⟨4254578, by rfl⟩ : syracuseStep 5672771 = 8509157) B8509157
theorem B495433 : Blo 307833 495433 := bstep (se 2 (by rfl) ⟨185787, by rfl⟩ : syracuseStep 495433 = 371575) B371575
theorem B1249199 : Blo 307833 1249199 := bstep (se 1 (by rfl) ⟨936899, by rfl⟩ : syracuseStep 1249199 = 1873799) B1873799
theorem B462767 : Blo 307833 462767 := bstep (se 1 (by rfl) ⟨347075, by rfl⟩ : syracuseStep 462767 = 694151) B694151
theorem B1675201 : Blo 307833 1675201 := bstep (se 2 (by rfl) ⟨628200, by rfl⟩ : syracuseStep 1675201 = 1256401) B1256401
theorem B462857 : Blo 307833 462857 := bstep (se 2 (by rfl) ⟨173571, by rfl⟩ : syracuseStep 462857 = 347143) B347143
theorem B593929 : Blo 307833 593929 := bstep (se 2 (by rfl) ⟨222723, by rfl⟩ : syracuseStep 593929 = 445447) B445447
theorem B462887 : Blo 307833 462887 := bstep (se 1 (by rfl) ⟨347165, by rfl⟩ : syracuseStep 462887 = 694331) B694331
theorem B462971 : Blo 307833 462971 := bstep (se 1 (by rfl) ⟨347228, by rfl⟩ : syracuseStep 462971 = 694457) B694457
theorem B463097 : Blo 307833 463097 := bstep (se 2 (by rfl) ⟨173661, by rfl⟩ : syracuseStep 463097 = 347323) B347323
theorem B463199 : Blo 307833 463199 := bstep (se 1 (by rfl) ⟨347399, by rfl⟩ : syracuseStep 463199 = 694799) B694799
theorem B463211 : Blo 307833 463211 := bstep (se 1 (by rfl) ⟨347408, by rfl⟩ : syracuseStep 463211 = 694817) B694817
theorem B528827 : Blo 307833 528827 := bstep (se 1 (by rfl) ⟨396620, by rfl⟩ : syracuseStep 528827 = 793241) B793241
theorem B463439 : Blo 307833 463439 := bstep (se 1 (by rfl) ⟨347579, by rfl⟩ : syracuseStep 463439 = 695159) B695159
theorem B1675961 : Blo 307833 1675961 := bstep (se 2 (by rfl) ⟨628485, by rfl⟩ : syracuseStep 1675961 = 1256971) B1256971
theorem B463559 : Blo 307833 463559 := bstep (se 1 (by rfl) ⟨347669, by rfl⟩ : syracuseStep 463559 = 695339) B695339
theorem B660167 : Blo 307833 660167 := bstep (se 1 (by rfl) ⟨495125, by rfl⟩ : syracuseStep 660167 = 990251) B990251
theorem B3347203 : Blo 307833 3347203 := bstep (se 1 (by rfl) ⟨2510402, by rfl⟩ : syracuseStep 3347203 = 5020805) B5020805
theorem B463721 : Blo 307833 463721 := bstep (se 2 (by rfl) ⟨173895, by rfl⟩ : syracuseStep 463721 = 347791) B347791
theorem B463799 : Blo 307833 463799 := bstep (se 1 (by rfl) ⟨347849, by rfl⟩ : syracuseStep 463799 = 695699) B695699
theorem B693179 : Blo 307833 693179 := bstep (se 1 (by rfl) ⟨519884, by rfl⟩ : syracuseStep 693179 = 1039769) B1039769
theorem B463835 : Blo 307833 463835 := bstep (se 1 (by rfl) ⟨347876, by rfl⟩ : syracuseStep 463835 = 695753) B695753
theorem B2364389 : Blo 307833 2364389 := bstep (se 4 (by rfl) ⟨221661, by rfl⟩ : syracuseStep 2364389 = 443323) B443323
theorem B988175 : Blo 307833 988175 := bstep (se 1 (by rfl) ⟨741131, by rfl⟩ : syracuseStep 988175 = 1482263) B1482263
theorem B693305 : Blo 307833 693305 := bstep (se 2 (by rfl) ⟨259989, by rfl⟩ : syracuseStep 693305 = 519979) B519979
theorem B496991 : Blo 307833 496991 := bstep (se 1 (by rfl) ⟨372743, by rfl⟩ : syracuseStep 496991 = 745487) B745487
theorem B1578365 : Blo 307833 1578365 := bstep (se 3 (by rfl) ⟨295943, by rfl⟩ : syracuseStep 1578365 = 591887) B591887
theorem B693647 : Blo 307833 693647 := bstep (se 1 (by rfl) ⟨520235, by rfl⟩ : syracuseStep 693647 = 1040471) B1040471
theorem B464303 : Blo 307833 464303 := bstep (se 1 (by rfl) ⟨348227, by rfl⟩ : syracuseStep 464303 = 696455) B696455
theorem B2299355 : Blo 307833 2299355 := bstep (se 1 (by rfl) ⟨1724516, by rfl⟩ : syracuseStep 2299355 = 3449033) B3449033
theorem B464393 : Blo 307833 464393 := bstep (se 2 (by rfl) ⟨174147, by rfl⟩ : syracuseStep 464393 = 348295) B348295
theorem B464423 : Blo 307833 464423 := bstep (se 1 (by rfl) ⟨348317, by rfl⟩ : syracuseStep 464423 = 696635) B696635
theorem B464507 : Blo 307833 464507 := bstep (se 1 (by rfl) ⟨348380, by rfl⟩ : syracuseStep 464507 = 696761) B696761
theorem B693971 : Blo 307833 693971 := bstep (se 1 (by rfl) ⟨520478, by rfl⟩ : syracuseStep 693971 = 1040957) B1040957
theorem B792275 : Blo 307833 792275 := bstep (se 1 (by rfl) ⟨594206, by rfl⟩ : syracuseStep 792275 = 1188413) B1188413
theorem B464633 : Blo 307833 464633 := bstep (se 2 (by rfl) ⟨174237, by rfl⟩ : syracuseStep 464633 = 348475) B348475
theorem B464735 : Blo 307833 464735 := bstep (se 1 (by rfl) ⟨348551, by rfl⟩ : syracuseStep 464735 = 697103) B697103
theorem B1251179 : Blo 307833 1251179 := bstep (se 1 (by rfl) ⟨938384, by rfl⟩ : syracuseStep 1251179 = 1876769) B1876769
theorem B661355 : Blo 307833 661355 := bstep (se 1 (by rfl) ⟨496016, by rfl⟩ : syracuseStep 661355 = 992033) B992033
theorem B464747 : Blo 307833 464747 := bstep (se 1 (by rfl) ⟨348560, by rfl⟩ : syracuseStep 464747 = 697121) B697121
theorem B1775479 : Blo 307833 1775479 := bstep (se 1 (by rfl) ⟨1331609, by rfl⟩ : syracuseStep 1775479 = 2663219) B2663219
theorem B464975 : Blo 307833 464975 := bstep (se 1 (by rfl) ⟨348731, by rfl⟩ : syracuseStep 464975 = 697463) B697463
theorem B465095 : Blo 307833 465095 := bstep (se 1 (by rfl) ⟨348821, by rfl⟩ : syracuseStep 465095 = 697643) B697643
theorem B3840257 : Blo 307833 3840257 := bstep (se 2 (by rfl) ⟨1440096, by rfl⟩ : syracuseStep 3840257 = 2880193) B2880193
theorem B465257 : Blo 307833 465257 := bstep (se 2 (by rfl) ⟨174471, by rfl⟩ : syracuseStep 465257 = 348943) B348943
theorem B465335 : Blo 307833 465335 := bstep (se 1 (by rfl) ⟨349001, by rfl⟩ : syracuseStep 465335 = 698003) B698003
theorem B465371 : Blo 307833 465371 := bstep (se 1 (by rfl) ⟨349028, by rfl⟩ : syracuseStep 465371 = 698057) B698057
theorem B694907 : Blo 307833 694907 := bstep (se 1 (by rfl) ⟨521180, by rfl⟩ : syracuseStep 694907 = 1042361) B1042361
theorem B695033 : Blo 307833 695033 := bstep (se 2 (by rfl) ⟨260637, by rfl⟩ : syracuseStep 695033 = 521275) B521275
theorem B17832797 : Blo 307833 17832797 := bstep (se 3 (by rfl) ⟨3343649, by rfl⟩ : syracuseStep 17832797 = 6687299) B6687299
theorem B1481647 : Blo 307833 1481647 := bstep (se 1 (by rfl) ⟨1111235, by rfl⟩ : syracuseStep 1481647 = 2222471) B2222471
theorem B465839 : Blo 307833 465839 := bstep (se 1 (by rfl) ⟨349379, by rfl⟩ : syracuseStep 465839 = 698759) B698759
theorem B695303 : Blo 307833 695303 := bstep (se 1 (by rfl) ⟨521477, by rfl⟩ : syracuseStep 695303 = 1042955) B1042955
theorem B465929 : Blo 307833 465929 := bstep (se 2 (by rfl) ⟨174723, by rfl⟩ : syracuseStep 465929 = 349447) B349447
theorem B465959 : Blo 307833 465959 := bstep (se 1 (by rfl) ⟨349469, by rfl⟩ : syracuseStep 465959 = 698939) B698939
theorem B695375 : Blo 307833 695375 := bstep (se 1 (by rfl) ⟨521531, by rfl⟩ : syracuseStep 695375 = 1043063) B1043063
theorem B466043 : Blo 307833 466043 := bstep (se 1 (by rfl) ⟨349532, by rfl⟩ : syracuseStep 466043 = 699065) B699065
theorem B498887 : Blo 307833 498887 := bstep (se 1 (by rfl) ⟨374165, by rfl⟩ : syracuseStep 498887 = 748331) B748331
theorem B466169 : Blo 307833 466169 := bstep (se 2 (by rfl) ⟨174813, by rfl⟩ : syracuseStep 466169 = 349627) B349627
theorem B466271 : Blo 307833 466271 := bstep (se 1 (by rfl) ⟨349703, by rfl⟩ : syracuseStep 466271 = 699407) B699407
theorem B466283 : Blo 307833 466283 := bstep (se 1 (by rfl) ⟨349712, by rfl⟩ : syracuseStep 466283 = 699425) B699425
theorem B695771 : Blo 307833 695771 := bstep (se 1 (by rfl) ⟨521828, by rfl⟩ : syracuseStep 695771 = 1043657) B1043657
theorem B466511 : Blo 307833 466511 := bstep (se 1 (by rfl) ⟨349883, by rfl⟩ : syracuseStep 466511 = 699767) B699767
theorem B466631 : Blo 307833 466631 := bstep (se 1 (by rfl) ⟨349973, by rfl⟩ : syracuseStep 466631 = 699947) B699947
theorem B466793 : Blo 307833 466793 := bstep (se 2 (by rfl) ⟨175047, by rfl⟩ : syracuseStep 466793 = 350095) B350095
theorem B696239 : Blo 307833 696239 := bstep (se 1 (by rfl) ⟨522179, by rfl⟩ : syracuseStep 696239 = 1044359) B1044359
theorem B466871 : Blo 307833 466871 := bstep (se 1 (by rfl) ⟨350153, by rfl⟩ : syracuseStep 466871 = 700307) B700307
theorem B3973049 : Blo 307833 3973049 := bstep (se 2 (by rfl) ⟨1489893, by rfl⟩ : syracuseStep 3973049 = 2979787) B2979787
theorem B3579835 : Blo 307833 3579835 := bstep (se 1 (by rfl) ⟨2684876, by rfl⟩ : syracuseStep 3579835 = 5369753) B5369753
theorem B466907 : Blo 307833 466907 := bstep (se 1 (by rfl) ⟨350180, by rfl⟩ : syracuseStep 466907 = 700361) B700361
theorem B696491 : Blo 307833 696491 := bstep (se 1 (by rfl) ⟨522368, by rfl⟩ : syracuseStep 696491 = 1044737) B1044737
theorem B3547313 : Blo 307833 3547313 := bstep (se 2 (by rfl) ⟨1330242, by rfl⟩ : syracuseStep 3547313 = 2660485) B2660485
theorem B1188107 : Blo 307833 1188107 := bstep (se 1 (by rfl) ⟨891080, by rfl⟩ : syracuseStep 1188107 = 1782161) B1782161
theorem B631145 : Blo 307833 631145 := bstep (se 2 (by rfl) ⟨236679, by rfl⟩ : syracuseStep 631145 = 473359) B473359
theorem B467375 : Blo 307833 467375 := bstep (se 1 (by rfl) ⟨350531, by rfl⟩ : syracuseStep 467375 = 701063) B701063
theorem B1122797 : Blo 307833 1122797 := bstep (se 3 (by rfl) ⟨210524, by rfl⟩ : syracuseStep 1122797 = 421049) B421049
theorem B467465 : Blo 307833 467465 := bstep (se 2 (by rfl) ⟨175299, by rfl⟩ : syracuseStep 467465 = 350599) B350599
theorem B598547 : Blo 307833 598547 := bstep (se 1 (by rfl) ⟨448910, by rfl⟩ : syracuseStep 598547 = 897821) B897821
theorem B467495 : Blo 307833 467495 := bstep (se 1 (by rfl) ⟨350621, by rfl⟩ : syracuseStep 467495 = 701243) B701243
theorem B467579 : Blo 307833 467579 := bstep (se 1 (by rfl) ⟨350684, by rfl⟩ : syracuseStep 467579 = 701369) B701369
theorem B1909433 : Blo 307833 1909433 := bstep (se 2 (by rfl) ⟨716037, by rfl⟩ : syracuseStep 1909433 = 1432075) B1432075
theorem B697031 : Blo 307833 697031 := bstep (se 1 (by rfl) ⟨522773, by rfl⟩ : syracuseStep 697031 = 1045547) B1045547
theorem B467705 : Blo 307833 467705 := bstep (se 2 (by rfl) ⟨175389, by rfl⟩ : syracuseStep 467705 = 350779) B350779
theorem B1975043 : Blo 307833 1975043 := bstep (se 1 (by rfl) ⟨1481282, by rfl⟩ : syracuseStep 1975043 = 2962565) B2962565
theorem B1319753 : Blo 307833 1319753 := bstep (se 2 (by rfl) ⟨494907, by rfl⟩ : syracuseStep 1319753 = 989815) B989815
theorem B2237291 : Blo 307833 2237291 := bstep (se 1 (by rfl) ⟨1677968, by rfl⟩ : syracuseStep 2237291 = 3355937) B3355937
theorem B2237635 : Blo 307833 2237635 := bstep (se 1 (by rfl) ⟨1678226, by rfl⟩ : syracuseStep 2237635 = 3356453) B3356453
theorem B533753 : Blo 307833 533753 := bstep (se 2 (by rfl) ⟨200157, by rfl⟩ : syracuseStep 533753 = 400315) B400315
theorem B501179 : Blo 307833 501179 := bstep (se 1 (by rfl) ⟨375884, by rfl⟩ : syracuseStep 501179 = 751769) B751769
theorem B697895 : Blo 307833 697895 := bstep (se 1 (by rfl) ⟨523421, by rfl⟩ : syracuseStep 697895 = 1046843) B1046843
theorem B992891 : Blo 307833 992891 := bstep (se 1 (by rfl) ⟨744668, by rfl⟩ : syracuseStep 992891 = 1489337) B1489337
theorem B698219 : Blo 307833 698219 := bstep (se 1 (by rfl) ⟨523664, by rfl⟩ : syracuseStep 698219 = 1047329) B1047329
theorem B698273 : Blo 307833 698273 := bstep (se 2 (by rfl) ⟨261852, by rfl⟩ : syracuseStep 698273 = 523705) B523705
theorem B1058831 : Blo 307833 1058831 := bstep (se 1 (by rfl) ⟨794123, by rfl⟩ : syracuseStep 1058831 = 1588247) B1588247
theorem B5941349 : Blo 307833 5941349 := bstep (se 4 (by rfl) ⟨557001, by rfl⟩ : syracuseStep 5941349 = 1114003) B1114003
theorem B15050933 : Blo 307833 15050933 := bstep (se 5 (by rfl) ⟨705512, by rfl⟩ : syracuseStep 15050933 = 1411025) B1411025
theorem B698615 : Blo 307833 698615 := bstep (se 1 (by rfl) ⟨523961, by rfl⟩ : syracuseStep 698615 = 1047923) B1047923
theorem B2369803 : Blo 307833 2369803 := bstep (se 1 (by rfl) ⟨1777352, by rfl⟩ : syracuseStep 2369803 = 3554705) B3554705
theorem B469423 : Blo 307833 469423 := bstep (se 1 (by rfl) ⟨352067, by rfl⟩ : syracuseStep 469423 = 704135) B704135
theorem B567739 : Blo 307833 567739 := bstep (se 1 (by rfl) ⟨425804, by rfl⟩ : syracuseStep 567739 = 851609) B851609
theorem B7514653 : Blo 307833 7514653 := bstep (se 3 (by rfl) ⟨1408997, by rfl⟩ : syracuseStep 7514653 = 2817995) B2817995
theorem B6007621 : Blo 307833 6007621 := bstep (se 4 (by rfl) ⟨563214, by rfl⟩ : syracuseStep 6007621 = 1126429) B1126429
theorem B699209 : Blo 307833 699209 := bstep (se 2 (by rfl) ⟨262203, by rfl⟩ : syracuseStep 699209 = 524407) B524407
theorem B469855 : Blo 307833 469855 := bstep (se 1 (by rfl) ⟨352391, by rfl⟩ : syracuseStep 469855 = 704783) B704783
theorem B371551 : Blo 307833 371551 := bstep (se 1 (by rfl) ⟨278663, by rfl⟩ : syracuseStep 371551 = 557327) B557327
theorem B535751 : Blo 307833 535751 := bstep (se 1 (by rfl) ⟨401813, by rfl⟩ : syracuseStep 535751 = 803627) B803627
theorem B1256791 : Blo 307833 1256791 := bstep (se 1 (by rfl) ⟨942593, by rfl⟩ : syracuseStep 1256791 = 1885187) B1885187
theorem B700001 : Blo 307833 700001 := bstep (se 2 (by rfl) ⟨262500, by rfl⟩ : syracuseStep 700001 = 525001) B525001
theorem B1060499 : Blo 307833 1060499 := bstep (se 1 (by rfl) ⟨795374, by rfl⟩ : syracuseStep 1060499 = 1590749) B1590749
theorem B4009661 : Blo 307833 4009661 := bstep (se 3 (by rfl) ⟨751811, by rfl⟩ : syracuseStep 4009661 = 1503623) B1503623
theorem B1257245 : Blo 307833 1257245 := bstep (se 3 (by rfl) ⟨235733, by rfl⟩ : syracuseStep 1257245 = 471467) B471467
theorem B700343 : Blo 307833 700343 := bstep (se 1 (by rfl) ⟨525257, by rfl⟩ : syracuseStep 700343 = 1050515) B1050515
theorem B1421243 : Blo 307833 1421243 := bstep (se 1 (by rfl) ⟨1065932, by rfl⟩ : syracuseStep 1421243 = 2131865) B2131865
theorem B34090955 : Blo 307833 34090955 := bstep (se 1 (by rfl) ⟨25568216, by rfl⟩ : syracuseStep 34090955 = 51136433) B51136433
theorem B372935 : Blo 307833 372935 := bstep (se 1 (by rfl) ⟨279701, by rfl⟩ : syracuseStep 372935 = 559403) B559403
theorem B700937 : Blo 307833 700937 := bstep (se 2 (by rfl) ⟨262851, by rfl⟩ : syracuseStep 700937 = 525703) B525703
theorem B307835 : Blo 307833 307835 := bstep (se 1 (by rfl) ⟨230876, by rfl⟩ : syracuseStep 307835 = 461753) B461753
theorem B307887 : Blo 307833 307887 := bstep (se 1 (by rfl) ⟨230915, by rfl⟩ : syracuseStep 307887 = 461831) B461831
theorem B307911 : Blo 307833 307911 := bstep (se 1 (by rfl) ⟨230933, by rfl⟩ : syracuseStep 307911 = 461867) B461867
theorem B307931 : Blo 307833 307931 := bstep (se 1 (by rfl) ⟨230948, by rfl⟩ : syracuseStep 307931 = 461897) B461897
theorem B10138385 : Blo 307833 10138385 := bstep (se 2 (by rfl) ⟨3801894, by rfl⟩ : syracuseStep 10138385 = 7603789) B7603789
theorem B308007 : Blo 307833 308007 := bstep (se 1 (by rfl) ⟨231005, by rfl⟩ : syracuseStep 308007 = 462011) B462011
theorem B308047 : Blo 307833 308047 := bstep (se 1 (by rfl) ⟨231035, by rfl⟩ : syracuseStep 308047 = 462071) B462071
theorem B308063 : Blo 307833 308063 := bstep (se 1 (by rfl) ⟨231047, by rfl⟩ : syracuseStep 308063 = 462095) B462095
theorem B701279 : Blo 307833 701279 := bstep (se 1 (by rfl) ⟨525959, by rfl⟩ : syracuseStep 701279 = 1051919) B1051919
theorem B308091 : Blo 307833 308091 := bstep (se 1 (by rfl) ⟨231068, by rfl⟩ : syracuseStep 308091 = 462137) B462137
theorem B308143 : Blo 307833 308143 := bstep (se 1 (by rfl) ⟨231107, by rfl⟩ : syracuseStep 308143 = 462215) B462215
theorem B308167 : Blo 307833 308167 := bstep (se 1 (by rfl) ⟨231125, by rfl⟩ : syracuseStep 308167 = 462251) B462251
theorem B308187 : Blo 307833 308187 := bstep (se 1 (by rfl) ⟨231140, by rfl⟩ : syracuseStep 308187 = 462281) B462281
theorem B701459 : Blo 307833 701459 := bstep (se 1 (by rfl) ⟨526094, by rfl⟩ : syracuseStep 701459 = 1052189) B1052189
theorem B308263 : Blo 307833 308263 := bstep (se 1 (by rfl) ⟨231197, by rfl⟩ : syracuseStep 308263 = 462395) B462395
theorem B308303 : Blo 307833 308303 := bstep (se 1 (by rfl) ⟨231227, by rfl⟩ : syracuseStep 308303 = 462455) B462455
theorem B308319 : Blo 307833 308319 := bstep (se 1 (by rfl) ⟨231239, by rfl⟩ : syracuseStep 308319 = 462479) B462479
theorem B308347 : Blo 307833 308347 := bstep (se 1 (by rfl) ⟨231260, by rfl⟩ : syracuseStep 308347 = 462521) B462521
theorem B38810765 : Blo 307833 38810765 := bstep (se 3 (by rfl) ⟨7277018, by rfl⟩ : syracuseStep 38810765 = 14554037) B14554037
theorem B308399 : Blo 307833 308399 := bstep (se 1 (by rfl) ⟨231299, by rfl⟩ : syracuseStep 308399 = 462599) B462599
theorem B308423 : Blo 307833 308423 := bstep (se 1 (by rfl) ⟨231317, by rfl⟩ : syracuseStep 308423 = 462635) B462635
theorem B308443 : Blo 307833 308443 := bstep (se 1 (by rfl) ⟨231332, by rfl⟩ : syracuseStep 308443 = 462665) B462665
theorem B308519 : Blo 307833 308519 := bstep (se 1 (by rfl) ⟨231389, by rfl⟩ : syracuseStep 308519 = 462779) B462779
theorem B308559 : Blo 307833 308559 := bstep (se 1 (by rfl) ⟨231419, by rfl⟩ : syracuseStep 308559 = 462839) B462839
theorem B308575 : Blo 307833 308575 := bstep (se 1 (by rfl) ⟨231431, by rfl⟩ : syracuseStep 308575 = 462863) B462863
theorem B308603 : Blo 307833 308603 := bstep (se 1 (by rfl) ⟨231452, by rfl⟩ : syracuseStep 308603 = 462905) B462905
theorem B308655 : Blo 307833 308655 := bstep (se 1 (by rfl) ⟨231491, by rfl⟩ : syracuseStep 308655 = 462983) B462983
theorem B308679 : Blo 307833 308679 := bstep (se 1 (by rfl) ⟨231509, by rfl⟩ : syracuseStep 308679 = 463019) B463019
theorem B308699 : Blo 307833 308699 := bstep (se 1 (by rfl) ⟨231524, by rfl⟩ : syracuseStep 308699 = 463049) B463049
theorem B308775 : Blo 307833 308775 := bstep (se 1 (by rfl) ⟨231581, by rfl⟩ : syracuseStep 308775 = 463163) B463163
theorem B308815 : Blo 307833 308815 := bstep (se 1 (by rfl) ⟨231611, by rfl⟩ : syracuseStep 308815 = 463223) B463223
theorem B308831 : Blo 307833 308831 := bstep (se 1 (by rfl) ⟨231623, by rfl⟩ : syracuseStep 308831 = 463247) B463247
theorem B308859 : Blo 307833 308859 := bstep (se 1 (by rfl) ⟨231644, by rfl⟩ : syracuseStep 308859 = 463289) B463289
theorem B308911 : Blo 307833 308911 := bstep (se 1 (by rfl) ⟨231683, by rfl⟩ : syracuseStep 308911 = 463367) B463367
theorem B308935 : Blo 307833 308935 := bstep (se 1 (by rfl) ⟨231701, by rfl⟩ : syracuseStep 308935 = 463403) B463403
theorem B308955 : Blo 307833 308955 := bstep (se 1 (by rfl) ⟨231716, by rfl⟩ : syracuseStep 308955 = 463433) B463433
theorem B3979043 : Blo 307833 3979043 := bstep (se 1 (by rfl) ⟨2984282, by rfl⟩ : syracuseStep 3979043 = 5968565) B5968565
theorem B309031 : Blo 307833 309031 := bstep (se 1 (by rfl) ⟨231773, by rfl⟩ : syracuseStep 309031 = 463547) B463547
theorem B309071 : Blo 307833 309071 := bstep (se 1 (by rfl) ⟨231803, by rfl⟩ : syracuseStep 309071 = 463607) B463607
theorem B309087 : Blo 307833 309087 := bstep (se 1 (by rfl) ⟨231815, by rfl⟩ : syracuseStep 309087 = 463631) B463631
theorem B309115 : Blo 307833 309115 := bstep (se 1 (by rfl) ⟨231836, by rfl⟩ : syracuseStep 309115 = 463673) B463673
theorem B309167 : Blo 307833 309167 := bstep (se 1 (by rfl) ⟨231875, by rfl⟩ : syracuseStep 309167 = 463751) B463751
theorem B309191 : Blo 307833 309191 := bstep (se 1 (by rfl) ⟨231893, by rfl⟩ : syracuseStep 309191 = 463787) B463787
theorem B309211 : Blo 307833 309211 := bstep (se 1 (by rfl) ⟨231908, by rfl⟩ : syracuseStep 309211 = 463817) B463817
theorem B309287 : Blo 307833 309287 := bstep (se 1 (by rfl) ⟨231965, by rfl⟩ : syracuseStep 309287 = 463931) B463931
theorem B309327 : Blo 307833 309327 := bstep (se 1 (by rfl) ⟨231995, by rfl⟩ : syracuseStep 309327 = 463991) B463991
theorem B6010969 : Blo 307833 6010969 := bstep (se 2 (by rfl) ⟨2254113, by rfl⟩ : syracuseStep 6010969 = 4508227) B4508227
theorem B309343 : Blo 307833 309343 := bstep (se 1 (by rfl) ⟨232007, by rfl⟩ : syracuseStep 309343 = 464015) B464015
theorem B309371 : Blo 307833 309371 := bstep (se 1 (by rfl) ⟨232028, by rfl⟩ : syracuseStep 309371 = 464057) B464057
theorem B309423 : Blo 307833 309423 := bstep (se 1 (by rfl) ⟨232067, by rfl⟩ : syracuseStep 309423 = 464135) B464135
theorem B309447 : Blo 307833 309447 := bstep (se 1 (by rfl) ⟨232085, by rfl⟩ : syracuseStep 309447 = 464171) B464171
theorem B309467 : Blo 307833 309467 := bstep (se 1 (by rfl) ⟨232100, by rfl⟩ : syracuseStep 309467 = 464201) B464201
theorem B309543 : Blo 307833 309543 := bstep (se 1 (by rfl) ⟨232157, by rfl⟩ : syracuseStep 309543 = 464315) B464315
theorem B309583 : Blo 307833 309583 := bstep (se 1 (by rfl) ⟨232187, by rfl⟩ : syracuseStep 309583 = 464375) B464375
theorem B309599 : Blo 307833 309599 := bstep (se 1 (by rfl) ⟨232199, by rfl⟩ : syracuseStep 309599 = 464399) B464399
theorem B2996585 : Blo 307833 2996585 := bstep (se 2 (by rfl) ⟨1123719, by rfl⟩ : syracuseStep 2996585 = 2247439) B2247439
theorem B309627 : Blo 307833 309627 := bstep (se 1 (by rfl) ⟨232220, by rfl⟩ : syracuseStep 309627 = 464441) B464441
theorem B309679 : Blo 307833 309679 := bstep (se 1 (by rfl) ⟨232259, by rfl⟩ : syracuseStep 309679 = 464519) B464519
theorem B309703 : Blo 307833 309703 := bstep (se 1 (by rfl) ⟨232277, by rfl⟩ : syracuseStep 309703 = 464555) B464555
theorem B309723 : Blo 307833 309723 := bstep (se 1 (by rfl) ⟨232292, by rfl⟩ : syracuseStep 309723 = 464585) B464585
theorem B309799 : Blo 307833 309799 := bstep (se 1 (by rfl) ⟨232349, by rfl⟩ : syracuseStep 309799 = 464699) B464699
theorem B3521069 : Blo 307833 3521069 := bstep (se 3 (by rfl) ⟨660200, by rfl⟩ : syracuseStep 3521069 = 1320401) B1320401
theorem B309839 : Blo 307833 309839 := bstep (se 1 (by rfl) ⟨232379, by rfl⟩ : syracuseStep 309839 = 464759) B464759
theorem B309855 : Blo 307833 309855 := bstep (se 1 (by rfl) ⟨232391, by rfl⟩ : syracuseStep 309855 = 464783) B464783
theorem B309883 : Blo 307833 309883 := bstep (se 1 (by rfl) ⟨232412, by rfl⟩ : syracuseStep 309883 = 464825) B464825
theorem B309935 : Blo 307833 309935 := bstep (se 1 (by rfl) ⟨232451, by rfl⟩ : syracuseStep 309935 = 464903) B464903
theorem B309959 : Blo 307833 309959 := bstep (se 1 (by rfl) ⟨232469, by rfl⟩ : syracuseStep 309959 = 464939) B464939
theorem B309979 : Blo 307833 309979 := bstep (se 1 (by rfl) ⟨232484, by rfl⟩ : syracuseStep 309979 = 464969) B464969
theorem B670457 : Blo 307833 670457 := bstep (se 2 (by rfl) ⟨251421, by rfl⟩ : syracuseStep 670457 = 502843) B502843
theorem B310055 : Blo 307833 310055 := bstep (se 1 (by rfl) ⟨232541, by rfl⟩ : syracuseStep 310055 = 465083) B465083
theorem B310095 : Blo 307833 310095 := bstep (se 1 (by rfl) ⟨232571, by rfl⟩ : syracuseStep 310095 = 465143) B465143
theorem B310111 : Blo 307833 310111 := bstep (se 1 (by rfl) ⟨232583, by rfl⟩ : syracuseStep 310111 = 465167) B465167
theorem B310139 : Blo 307833 310139 := bstep (se 1 (by rfl) ⟨232604, by rfl⟩ : syracuseStep 310139 = 465209) B465209
theorem B310191 : Blo 307833 310191 := bstep (se 1 (by rfl) ⟨232643, by rfl⟩ : syracuseStep 310191 = 465287) B465287
theorem B310215 : Blo 307833 310215 := bstep (se 1 (by rfl) ⟨232661, by rfl⟩ : syracuseStep 310215 = 465323) B465323
theorem B310235 : Blo 307833 310235 := bstep (se 1 (by rfl) ⟨232676, by rfl⟩ : syracuseStep 310235 = 465353) B465353
theorem B310311 : Blo 307833 310311 := bstep (se 1 (by rfl) ⟨232733, by rfl⟩ : syracuseStep 310311 = 465467) B465467
theorem B834617 : Blo 307833 834617 := bstep (se 2 (by rfl) ⟨312981, by rfl⟩ : syracuseStep 834617 = 625963) B625963
theorem B310351 : Blo 307833 310351 := bstep (se 1 (by rfl) ⟨232763, by rfl⟩ : syracuseStep 310351 = 465527) B465527
theorem B310367 : Blo 307833 310367 := bstep (se 1 (by rfl) ⟨232775, by rfl⟩ : syracuseStep 310367 = 465551) B465551
theorem B310395 : Blo 307833 310395 := bstep (se 1 (by rfl) ⟨232796, by rfl⟩ : syracuseStep 310395 = 465593) B465593
theorem B310447 : Blo 307833 310447 := bstep (se 1 (by rfl) ⟨232835, by rfl⟩ : syracuseStep 310447 = 465671) B465671
theorem B310471 : Blo 307833 310471 := bstep (se 1 (by rfl) ⟨232853, by rfl⟩ : syracuseStep 310471 = 465707) B465707
theorem B310491 : Blo 307833 310491 := bstep (se 1 (by rfl) ⟨232868, by rfl⟩ : syracuseStep 310491 = 465737) B465737
theorem B310567 : Blo 307833 310567 := bstep (se 1 (by rfl) ⟨232925, by rfl⟩ : syracuseStep 310567 = 465851) B465851
theorem B310607 : Blo 307833 310607 := bstep (se 1 (by rfl) ⟨232955, by rfl⟩ : syracuseStep 310607 = 465911) B465911
theorem B310623 : Blo 307833 310623 := bstep (se 1 (by rfl) ⟨232967, by rfl⟩ : syracuseStep 310623 = 465935) B465935
theorem B310651 : Blo 307833 310651 := bstep (se 1 (by rfl) ⟨232988, by rfl⟩ : syracuseStep 310651 = 465977) B465977
theorem B310703 : Blo 307833 310703 := bstep (se 1 (by rfl) ⟨233027, by rfl⟩ : syracuseStep 310703 = 466055) B466055
theorem B310727 : Blo 307833 310727 := bstep (se 1 (by rfl) ⟨233045, by rfl⟩ : syracuseStep 310727 = 466091) B466091
theorem B310747 : Blo 307833 310747 := bstep (se 1 (by rfl) ⟨233060, by rfl⟩ : syracuseStep 310747 = 466121) B466121
theorem B441865 : Blo 307833 441865 := bstep (se 2 (by rfl) ⟨165699, by rfl⟩ : syracuseStep 441865 = 331399) B331399
theorem B310823 : Blo 307833 310823 := bstep (se 1 (by rfl) ⟨233117, by rfl⟩ : syracuseStep 310823 = 466235) B466235
theorem B310863 : Blo 307833 310863 := bstep (se 1 (by rfl) ⟨233147, by rfl⟩ : syracuseStep 310863 = 466295) B466295
theorem B310879 : Blo 307833 310879 := bstep (se 1 (by rfl) ⟨233159, by rfl⟩ : syracuseStep 310879 = 466319) B466319
theorem B1326689 : Blo 307833 1326689 := bstep (se 2 (by rfl) ⟨497508, by rfl⟩ : syracuseStep 1326689 = 995017) B995017
theorem B310907 : Blo 307833 310907 := bstep (se 1 (by rfl) ⟨233180, by rfl⟩ : syracuseStep 310907 = 466361) B466361
theorem B310959 : Blo 307833 310959 := bstep (se 1 (by rfl) ⟨233219, by rfl⟩ : syracuseStep 310959 = 466439) B466439
theorem B1982141 : Blo 307833 1982141 := bstep (se 3 (by rfl) ⟨371651, by rfl⟩ : syracuseStep 1982141 = 743303) B743303
theorem B310983 : Blo 307833 310983 := bstep (se 1 (by rfl) ⟨233237, by rfl⟩ : syracuseStep 310983 = 466475) B466475
theorem B311003 : Blo 307833 311003 := bstep (se 1 (by rfl) ⟨233252, by rfl⟩ : syracuseStep 311003 = 466505) B466505
theorem B311079 : Blo 307833 311079 := bstep (se 1 (by rfl) ⟨233309, by rfl⟩ : syracuseStep 311079 = 466619) B466619
theorem B311119 : Blo 307833 311119 := bstep (se 1 (by rfl) ⟨233339, by rfl⟩ : syracuseStep 311119 = 466679) B466679
theorem B442207 : Blo 307833 442207 := bstep (se 1 (by rfl) ⟨331655, by rfl⟩ : syracuseStep 442207 = 663311) B663311
theorem B311135 : Blo 307833 311135 := bstep (se 1 (by rfl) ⟨233351, by rfl⟩ : syracuseStep 311135 = 466703) B466703
theorem B311163 : Blo 307833 311163 := bstep (se 1 (by rfl) ⟨233372, by rfl⟩ : syracuseStep 311163 = 466745) B466745
theorem B311215 : Blo 307833 311215 := bstep (se 1 (by rfl) ⟨233411, by rfl⟩ : syracuseStep 311215 = 466823) B466823
theorem B311239 : Blo 307833 311239 := bstep (se 1 (by rfl) ⟨233429, by rfl⟩ : syracuseStep 311239 = 466859) B466859
theorem B311259 : Blo 307833 311259 := bstep (se 1 (by rfl) ⟨233444, by rfl⟩ : syracuseStep 311259 = 466889) B466889
theorem B1982501 : Blo 307833 1982501 := bstep (se 4 (by rfl) ⟨185859, by rfl⟩ : syracuseStep 1982501 = 371719) B371719
theorem B311335 : Blo 307833 311335 := bstep (se 1 (by rfl) ⟨233501, by rfl⟩ : syracuseStep 311335 = 467003) B467003
theorem B311375 : Blo 307833 311375 := bstep (se 1 (by rfl) ⟨233531, by rfl⟩ : syracuseStep 311375 = 467063) B467063
theorem B311391 : Blo 307833 311391 := bstep (se 1 (by rfl) ⟨233543, by rfl⟩ : syracuseStep 311391 = 467087) B467087
theorem B311419 : Blo 307833 311419 := bstep (se 1 (by rfl) ⟨233564, by rfl⟩ : syracuseStep 311419 = 467129) B467129
theorem B311471 : Blo 307833 311471 := bstep (se 1 (by rfl) ⟨233603, by rfl⟩ : syracuseStep 311471 = 467207) B467207
theorem B311495 : Blo 307833 311495 := bstep (se 1 (by rfl) ⟨233621, by rfl⟩ : syracuseStep 311495 = 467243) B467243
theorem B311515 : Blo 307833 311515 := bstep (se 1 (by rfl) ⟨233636, by rfl⟩ : syracuseStep 311515 = 467273) B467273
theorem B311591 : Blo 307833 311591 := bstep (se 1 (by rfl) ⟨233693, by rfl⟩ : syracuseStep 311591 = 467387) B467387
theorem B311631 : Blo 307833 311631 := bstep (se 1 (by rfl) ⟨233723, by rfl⟩ : syracuseStep 311631 = 467447) B467447
theorem B311647 : Blo 307833 311647 := bstep (se 1 (by rfl) ⟨233735, by rfl⟩ : syracuseStep 311647 = 467471) B467471
theorem B311675 : Blo 307833 311675 := bstep (se 1 (by rfl) ⟨233756, by rfl⟩ : syracuseStep 311675 = 467513) B467513
theorem B311727 : Blo 307833 311727 := bstep (se 1 (by rfl) ⟨233795, by rfl⟩ : syracuseStep 311727 = 467591) B467591
theorem B311751 : Blo 307833 311751 := bstep (se 1 (by rfl) ⟨233813, by rfl⟩ : syracuseStep 311751 = 467627) B467627
theorem B311771 : Blo 307833 311771 := bstep (se 1 (by rfl) ⟨233828, by rfl⟩ : syracuseStep 311771 = 467657) B467657
theorem B1753609 : Blo 307833 1753609 := bstep (se 2 (by rfl) ⟨657603, by rfl⟩ : syracuseStep 1753609 = 1315207) B1315207
theorem B672673 : Blo 307833 672673 := bstep (se 2 (by rfl) ⟨252252, by rfl⟩ : syracuseStep 672673 = 504505) B504505
theorem B2246231 : Blo 307833 2246231 := bstep (se 1 (by rfl) ⟨1684673, by rfl⟩ : syracuseStep 2246231 = 3369347) B3369347
theorem B8931161 : Blo 307833 8931161 := bstep (se 2 (by rfl) ⟨3349185, by rfl⟩ : syracuseStep 8931161 = 6698371) B6698371
theorem B1755067 : Blo 307833 1755067 := bstep (se 1 (by rfl) ⟨1316300, by rfl⟩ : syracuseStep 1755067 = 2632601) B2632601
theorem B11290661 : Blo 307833 11290661 := bstep (se 4 (by rfl) ⟨1058499, by rfl⟩ : syracuseStep 11290661 = 2116999) B2116999
theorem B1984601 : Blo 307833 1984601 := bstep (se 2 (by rfl) ⟨744225, by rfl⟩ : syracuseStep 1984601 = 1488451) B1488451
theorem B313679 : Blo 307833 313679 := bstep (se 1 (by rfl) ⟨235259, by rfl⟩ : syracuseStep 313679 = 470519) B470519
theorem B346747 : Blo 307833 346747 := bstep (se 1 (by rfl) ⟨260060, by rfl⟩ : syracuseStep 346747 = 520121) B520121
theorem B1559249 : Blo 307833 1559249 := bstep (se 2 (by rfl) ⟨584718, by rfl⟩ : syracuseStep 1559249 = 1169437) B1169437
theorem B1067951 : Blo 307833 1067951 := bstep (se 1 (by rfl) ⟨800963, by rfl⟩ : syracuseStep 1067951 = 1601927) B1601927
theorem B347215 : Blo 307833 347215 := bstep (se 1 (by rfl) ⟨260411, by rfl⟩ : syracuseStep 347215 = 520823) B520823
theorem B347611 : Blo 307833 347611 := bstep (se 1 (by rfl) ⟨260708, by rfl⟩ : syracuseStep 347611 = 521417) B521417
theorem B1003193 : Blo 307833 1003193 := bstep (se 2 (by rfl) ⟨376197, by rfl⟩ : syracuseStep 1003193 = 752395) B752395
theorem B8081117 : Blo 307833 8081117 := bstep (se 3 (by rfl) ⟨1515209, by rfl⟩ : syracuseStep 8081117 = 3030419) B3030419
theorem B4476653 : Blo 307833 4476653 := bstep (se 3 (by rfl) ⟨839372, by rfl⟩ : syracuseStep 4476653 = 1678745) B1678745
theorem B741113 : Blo 307833 741113 := bstep (se 2 (by rfl) ⟨277917, by rfl⟩ : syracuseStep 741113 = 555835) B555835
theorem B1331063 : Blo 307833 1331063 := bstep (se 1 (by rfl) ⟨998297, by rfl⟩ : syracuseStep 1331063 = 1996595) B1996595
theorem B348079 : Blo 307833 348079 := bstep (se 1 (by rfl) ⟨261059, by rfl⟩ : syracuseStep 348079 = 522119) B522119
theorem B348511 : Blo 307833 348511 := bstep (se 1 (by rfl) ⟨261383, by rfl⟩ : syracuseStep 348511 = 522767) B522767
theorem B3592763 : Blo 307833 3592763 := bstep (se 1 (by rfl) ⟨2694572, by rfl⟩ : syracuseStep 3592763 = 5389145) B5389145
theorem B348871 : Blo 307833 348871 := bstep (se 1 (by rfl) ⟨261653, by rfl⟩ : syracuseStep 348871 = 523307) B523307
theorem B5296913 : Blo 307833 5296913 := bstep (se 2 (by rfl) ⟨1986342, by rfl⟩ : syracuseStep 5296913 = 3972685) B3972685
theorem B12342131 : Blo 307833 12342131 := bstep (se 1 (by rfl) ⟨9256598, by rfl⟩ : syracuseStep 12342131 = 18513197) B18513197
theorem B1561679 : Blo 307833 1561679 := bstep (se 1 (by rfl) ⟨1171259, by rfl⟩ : syracuseStep 1561679 = 2342519) B2342519
theorem B349735 : Blo 307833 349735 := bstep (se 1 (by rfl) ⟨262301, by rfl⟩ : syracuseStep 349735 = 524603) B524603
theorem B743111 : Blo 307833 743111 := bstep (se 1 (by rfl) ⟨557333, by rfl⟩ : syracuseStep 743111 = 1114667) B1114667
theorem B3987143 : Blo 307833 3987143 := bstep (se 1 (by rfl) ⟨2990357, by rfl⟩ : syracuseStep 3987143 = 5980715) B5980715
theorem B1562327 : Blo 307833 1562327 := bstep (se 1 (by rfl) ⟨1171745, by rfl⟩ : syracuseStep 1562327 = 2343491) B2343491
theorem B1758941 : Blo 307833 1758941 := bstep (se 3 (by rfl) ⟨329801, by rfl⟩ : syracuseStep 1758941 = 659603) B659603
theorem B1169225 : Blo 307833 1169225 := bstep (se 2 (by rfl) ⟨438459, by rfl⟩ : syracuseStep 1169225 = 876919) B876919
theorem B1169423 : Blo 307833 1169423 := bstep (se 1 (by rfl) ⟨877067, by rfl⟩ : syracuseStep 1169423 = 1754135) B1754135
theorem B16963829 : Blo 307833 16963829 := bstep (se 5 (by rfl) ⟨795179, by rfl⟩ : syracuseStep 16963829 = 1590359) B1590359
theorem B2349323 : Blo 307833 2349323 := bstep (se 1 (by rfl) ⟨1761992, by rfl⟩ : syracuseStep 2349323 = 3523985) B3523985
theorem B743899 : Blo 307833 743899 := bstep (se 1 (by rfl) ⟨557924, by rfl⟩ : syracuseStep 743899 = 1115849) B1115849
theorem B1039607 : Blo 307833 1039607 := bstep (se 1 (by rfl) ⟨779705, by rfl⟩ : syracuseStep 1039607 = 1559411) B1559411
theorem B1039931 : Blo 307833 1039931 := bstep (se 1 (by rfl) ⟨779948, by rfl⟩ : syracuseStep 1039931 = 1559897) B1559897
theorem B1990291 : Blo 307833 1990291 := bstep (se 1 (by rfl) ⟨1492718, by rfl⟩ : syracuseStep 1990291 = 2985437) B2985437
theorem B2350781 : Blo 307833 2350781 := bstep (se 3 (by rfl) ⟨440771, by rfl⟩ : syracuseStep 2350781 = 881543) B881543
theorem B1040201 : Blo 307833 1040201 := bstep (se 2 (by rfl) ⟨390075, by rfl⟩ : syracuseStep 1040201 = 780151) B780151
theorem B1794163 : Blo 307833 1794163 := bstep (se 1 (by rfl) ⟨1345622, by rfl⟩ : syracuseStep 1794163 = 2691245) B2691245
theorem B2351267 : Blo 307833 2351267 := bstep (se 1 (by rfl) ⟨1763450, by rfl⟩ : syracuseStep 2351267 = 3526901) B3526901
theorem B2154763 : Blo 307833 2154763 := bstep (se 1 (by rfl) ⟨1616072, by rfl⟩ : syracuseStep 2154763 = 3232145) B3232145
theorem B16114211 : Blo 307833 16114211 := bstep (se 1 (by rfl) ⟨12085658, by rfl⟩ : syracuseStep 16114211 = 24171317) B24171317
theorem B1565243 : Blo 307833 1565243 := bstep (se 1 (by rfl) ⟨1173932, by rfl⟩ : syracuseStep 1565243 = 2347865) B2347865
theorem B1041335 : Blo 307833 1041335 := bstep (se 1 (by rfl) ⟨781001, by rfl⟩ : syracuseStep 1041335 = 1562003) B1562003
theorem B779321 : Blo 307833 779321 := bstep (se 2 (by rfl) ⟨292245, by rfl⟩ : syracuseStep 779321 = 584491) B584491
theorem B877625 : Blo 307833 877625 := bstep (se 2 (by rfl) ⟨329109, by rfl⟩ : syracuseStep 877625 = 658219) B658219
theorem B1565891 : Blo 307833 1565891 := bstep (se 1 (by rfl) ⟨1174418, by rfl⟩ : syracuseStep 1565891 = 2348837) B2348837
theorem B1041929 : Blo 307833 1041929 := bstep (se 2 (by rfl) ⟨390723, by rfl⟩ : syracuseStep 1041929 = 781447) B781447
theorem B1992289 : Blo 307833 1992289 := bstep (se 2 (by rfl) ⟨747108, by rfl⟩ : syracuseStep 1992289 = 1494217) B1494217
theorem B1271965 : Blo 307833 1271965 := bstep (se 3 (by rfl) ⟨238493, by rfl⟩ : syracuseStep 1271965 = 476987) B476987
theorem B2648321 : Blo 307833 2648321 := bstep (se 2 (by rfl) ⟨993120, by rfl⟩ : syracuseStep 2648321 = 1986241) B1986241
theorem B2222387 : Blo 307833 2222387 := bstep (se 1 (by rfl) ⟨1666790, by rfl⟩ : syracuseStep 2222387 = 3333581) B3333581
theorem B1042793 : Blo 307833 1042793 := bstep (se 2 (by rfl) ⟨391047, by rfl⟩ : syracuseStep 1042793 = 782095) B782095
theorem B2353697 : Blo 307833 2353697 := bstep (se 2 (by rfl) ⟨882636, by rfl⟩ : syracuseStep 2353697 = 1765273) B1765273
theorem B748129 : Blo 307833 748129 := bstep (se 2 (by rfl) ⟨280548, by rfl⟩ : syracuseStep 748129 = 561097) B561097
theorem B486319 : Blo 307833 486319 := bstep (se 1 (by rfl) ⟨364739, by rfl⟩ : syracuseStep 486319 = 729479) B729479
theorem B1043387 : Blo 307833 1043387 := bstep (se 1 (by rfl) ⟨782540, by rfl⟩ : syracuseStep 1043387 = 1565081) B1565081
theorem B781559 : Blo 307833 781559 := bstep (se 1 (by rfl) ⟨586169, by rfl⟩ : syracuseStep 781559 = 1172339) B1172339
theorem B6319397 : Blo 307833 6319397 := bstep (se 4 (by rfl) ⟨592443, by rfl⟩ : syracuseStep 6319397 = 1184887) B1184887
theorem B1764773 : Blo 307833 1764773 := bstep (se 4 (by rfl) ⟨165447, by rfl⟩ : syracuseStep 1764773 = 330895) B330895
theorem B519689 : Blo 307833 519689 := bstep (se 2 (by rfl) ⟨194883, by rfl⟩ : syracuseStep 519689 = 389767) B389767
theorem B585235 : Blo 307833 585235 := bstep (se 1 (by rfl) ⟨438926, by rfl⟩ : syracuseStep 585235 = 877853) B877853
theorem B519851 : Blo 307833 519851 := bstep (se 1 (by rfl) ⟨389888, by rfl⟩ : syracuseStep 519851 = 779777) B779777
theorem B1175255 : Blo 307833 1175255 := bstep (se 1 (by rfl) ⟨881441, by rfl⟩ : syracuseStep 1175255 = 1762883) B1762883
theorem B585463 : Blo 307833 585463 := bstep (se 1 (by rfl) ⟨439097, by rfl⟩ : syracuseStep 585463 = 878195) B878195
theorem B585767 : Blo 307833 585767 := bstep (se 1 (by rfl) ⟨439325, by rfl⟩ : syracuseStep 585767 = 878651) B878651
theorem B520249 : Blo 307833 520249 := bstep (se 2 (by rfl) ⟨195093, by rfl⟩ : syracuseStep 520249 = 390187) B390187
theorem B520391 : Blo 307833 520391 := bstep (se 1 (by rfl) ⟨390293, by rfl⟩ : syracuseStep 520391 = 780587) B780587
theorem B2388275 : Blo 307833 2388275 := bstep (se 1 (by rfl) ⟨1791206, by rfl⟩ : syracuseStep 2388275 = 3582413) B3582413
theorem B22475069 : Blo 307833 22475069 := bstep (se 3 (by rfl) ⟨4214075, by rfl⟩ : syracuseStep 22475069 = 8428151) B8428151
theorem B520553 : Blo 307833 520553 := bstep (se 2 (by rfl) ⟨195207, by rfl⟩ : syracuseStep 520553 = 390415) B390415
theorem B1995137 : Blo 307833 1995137 := bstep (se 2 (by rfl) ⟨748176, by rfl⟩ : syracuseStep 1995137 = 1496353) B1496353
theorem B389711 : Blo 307833 389711 := bstep (se 1 (by rfl) ⟨292283, by rfl⟩ : syracuseStep 389711 = 584567) B584567
theorem B1045115 : Blo 307833 1045115 := bstep (se 1 (by rfl) ⟨783836, by rfl⟩ : syracuseStep 1045115 = 1567673) B1567673
theorem B783047 : Blo 307833 783047 := bstep (se 1 (by rfl) ⟨587285, by rfl⟩ : syracuseStep 783047 = 1174571) B1174571
theorem B881351 : Blo 307833 881351 := bstep (se 1 (by rfl) ⟨661013, by rfl⟩ : syracuseStep 881351 = 1322027) B1322027
theorem B520951 : Blo 307833 520951 := bstep (se 1 (by rfl) ⟨390713, by rfl⟩ : syracuseStep 520951 = 781427) B781427
theorem B1045277 : Blo 307833 1045277 := bstep (se 3 (by rfl) ⟨195989, by rfl⟩ : syracuseStep 1045277 = 391979) B391979
theorem B521147 : Blo 307833 521147 := bstep (se 1 (by rfl) ⟨390860, by rfl⟩ : syracuseStep 521147 = 781721) B781721
theorem B5993473 : Blo 307833 5993473 := bstep (se 2 (by rfl) ⟨2247552, by rfl⟩ : syracuseStep 5993473 = 4495105) B4495105
theorem B521255 : Blo 307833 521255 := bstep (se 1 (by rfl) ⟨390941, by rfl⟩ : syracuseStep 521255 = 781883) B781883
theorem B2880715 : Blo 307833 2880715 := bstep (se 1 (by rfl) ⟨2160536, by rfl⟩ : syracuseStep 2880715 = 4321073) B4321073
theorem B521545 : Blo 307833 521545 := bstep (se 2 (by rfl) ⟨195579, by rfl⟩ : syracuseStep 521545 = 391159) B391159
theorem B587081 : Blo 307833 587081 := bstep (se 2 (by rfl) ⟨220155, by rfl⟩ : syracuseStep 587081 = 440311) B440311
theorem B521579 : Blo 307833 521579 := bstep (se 1 (by rfl) ⟨391184, by rfl⟩ : syracuseStep 521579 = 782369) B782369
theorem B1045979 : Blo 307833 1045979 := bstep (se 1 (by rfl) ⟨784484, by rfl⟩ : syracuseStep 1045979 = 1568969) B1568969
theorem B1570427 : Blo 307833 1570427 := bstep (se 1 (by rfl) ⟨1177820, by rfl⟩ : syracuseStep 1570427 = 2355641) B2355641
theorem B1406663 : Blo 307833 1406663 := bstep (se 1 (by rfl) ⟨1054997, by rfl⟩ : syracuseStep 1406663 = 2109995) B2109995
theorem B521977 : Blo 307833 521977 := bstep (se 2 (by rfl) ⟨195741, by rfl⟩ : syracuseStep 521977 = 391483) B391483
theorem B587513 : Blo 307833 587513 := bstep (se 2 (by rfl) ⟨220317, by rfl⟩ : syracuseStep 587513 = 440635) B440635
theorem B784201 : Blo 307833 784201 := bstep (se 2 (by rfl) ⟨294075, by rfl⟩ : syracuseStep 784201 = 588151) B588151
theorem B4028249 : Blo 307833 4028249 := bstep (se 2 (by rfl) ⟨1510593, by rfl⟩ : syracuseStep 4028249 = 3021187) B3021187
theorem B391007 : Blo 307833 391007 := bstep (se 1 (by rfl) ⟨293255, by rfl⟩ : syracuseStep 391007 = 586511) B586511
theorem B522247 : Blo 307833 522247 := bstep (se 1 (by rfl) ⟨391685, by rfl⟩ : syracuseStep 522247 = 783371) B783371
theorem B1046681 : Blo 307833 1046681 := bstep (se 2 (by rfl) ⟨392505, by rfl⟩ : syracuseStep 1046681 = 785011) B785011
theorem B522679 : Blo 307833 522679 := bstep (se 1 (by rfl) ⟨392009, by rfl⟩ : syracuseStep 522679 = 784019) B784019
theorem B1178171 : Blo 307833 1178171 := bstep (se 1 (by rfl) ⟨883628, by rfl⟩ : syracuseStep 1178171 = 1767257) B1767257
theorem B522875 : Blo 307833 522875 := bstep (se 1 (by rfl) ⟨392156, by rfl⟩ : syracuseStep 522875 = 784313) B784313
theorem B2653073 : Blo 307833 2653073 := bstep (se 2 (by rfl) ⟨994902, by rfl⟩ : syracuseStep 2653073 = 1989805) B1989805
theorem B785335 : Blo 307833 785335 := bstep (se 1 (by rfl) ⟨589001, by rfl⟩ : syracuseStep 785335 = 1178003) B1178003
theorem B883639 : Blo 307833 883639 := bstep (se 1 (by rfl) ⟨662729, by rfl⟩ : syracuseStep 883639 = 1325459) B1325459
theorem B523273 : Blo 307833 523273 := bstep (se 2 (by rfl) ⟨196227, by rfl⟩ : syracuseStep 523273 = 392455) B392455
theorem B523435 : Blo 307833 523435 := bstep (se 1 (by rfl) ⟨392576, by rfl⟩ : syracuseStep 523435 = 785153) B785153
theorem B588971 : Blo 307833 588971 := bstep (se 1 (by rfl) ⟨441728, by rfl⟩ : syracuseStep 588971 = 883457) B883457
theorem B1047869 : Blo 307833 1047869 := bstep (se 3 (by rfl) ⟨196475, by rfl⟩ : syracuseStep 1047869 = 392951) B392951
theorem B523739 : Blo 307833 523739 := bstep (se 1 (by rfl) ⟨392804, by rfl⟩ : syracuseStep 523739 = 785609) B785609
theorem B556583 : Blo 307833 556583 := bstep (se 1 (by rfl) ⟨417437, by rfl⟩ : syracuseStep 556583 = 834875) B834875
theorem B589351 : Blo 307833 589351 := bstep (se 1 (by rfl) ⟨442013, by rfl⟩ : syracuseStep 589351 = 884027) B884027
theorem B3538565 : Blo 307833 3538565 := bstep (se 4 (by rfl) ⟨331740, by rfl⟩ : syracuseStep 3538565 = 663481) B663481
theorem B523975 : Blo 307833 523975 := bstep (se 1 (by rfl) ⟨392981, by rfl⟩ : syracuseStep 523975 = 785963) B785963
theorem B589511 : Blo 307833 589511 := bstep (se 1 (by rfl) ⟨442133, by rfl⟩ : syracuseStep 589511 = 884267) B884267
theorem B524137 : Blo 307833 524137 := bstep (se 2 (by rfl) ⟨196551, by rfl⟩ : syracuseStep 524137 = 393103) B393103
theorem B2392217 : Blo 307833 2392217 := bstep (se 2 (by rfl) ⟨897081, by rfl⟩ : syracuseStep 2392217 = 1794163) B1794163
theorem B1048787 : Blo 307833 1048787 := bstep (se 1 (by rfl) ⟨786590, by rfl⟩ : syracuseStep 1048787 = 1573181) B1573181
theorem B524711 : Blo 307833 524711 := bstep (se 1 (by rfl) ⟨393533, by rfl⟩ : syracuseStep 524711 = 787067) B787067
theorem B1180129 : Blo 307833 1180129 := bstep (se 2 (by rfl) ⟨442548, by rfl⟩ : syracuseStep 1180129 = 885097) B885097
theorem B1049057 : Blo 307833 1049057 := bstep (se 2 (by rfl) ⟨393396, by rfl⟩ : syracuseStep 1049057 = 786793) B786793
theorem B590399 : Blo 307833 590399 := bstep (se 1 (by rfl) ⟨442799, by rfl⟩ : syracuseStep 590399 = 885599) B885599
theorem B524873 : Blo 307833 524873 := bstep (se 2 (by rfl) ⟨196827, by rfl⟩ : syracuseStep 524873 = 393655) B393655
theorem B787279 : Blo 307833 787279 := bstep (se 1 (by rfl) ⟨590459, by rfl⟩ : syracuseStep 787279 = 1180919) B1180919
theorem B787553 : Blo 307833 787553 := bstep (se 2 (by rfl) ⟨295332, by rfl⟩ : syracuseStep 787553 = 590665) B590665
theorem B1410205 : Blo 307833 1410205 := bstep (se 3 (by rfl) ⟨264413, by rfl⟩ : syracuseStep 1410205 = 528827) B528827
theorem B591067 : Blo 307833 591067 := bstep (se 1 (by rfl) ⟨443300, by rfl⟩ : syracuseStep 591067 = 886601) B886601
theorem B2983205 : Blo 307833 2983205 := bstep (se 4 (by rfl) ⟨279675, by rfl⟩ : syracuseStep 2983205 = 559351) B559351
theorem B787927 : Blo 307833 787927 := bstep (se 1 (by rfl) ⟨590945, by rfl⟩ : syracuseStep 787927 = 1181891) B1181891
theorem B2983513 : Blo 307833 2983513 := bstep (se 2 (by rfl) ⟨1118817, by rfl⟩ : syracuseStep 2983513 = 2237635) B2237635
theorem B591455 : Blo 307833 591455 := bstep (se 1 (by rfl) ⟨443591, by rfl⟩ : syracuseStep 591455 = 887183) B887183
theorem B525919 : Blo 307833 525919 := bstep (se 1 (by rfl) ⟨394439, by rfl⟩ : syracuseStep 525919 = 788879) B788879
theorem B1050299 : Blo 307833 1050299 := bstep (se 1 (by rfl) ⟨787724, by rfl⟩ : syracuseStep 1050299 = 1575449) B1575449
theorem B788231 : Blo 307833 788231 := bstep (se 1 (by rfl) ⟨591173, by rfl⟩ : syracuseStep 788231 = 1182347) B1182347
theorem B526135 : Blo 307833 526135 := bstep (se 1 (by rfl) ⟨394601, by rfl⟩ : syracuseStep 526135 = 789203) B789203
theorem B2656385 : Blo 307833 2656385 := bstep (se 2 (by rfl) ⟨996144, by rfl⟩ : syracuseStep 2656385 = 1992289) B1992289
theorem B2361473 : Blo 307833 2361473 := bstep (se 2 (by rfl) ⟨885552, by rfl⟩ : syracuseStep 2361473 = 1771105) B1771105
theorem B2984435 : Blo 307833 2984435 := bstep (se 1 (by rfl) ⟨2238326, by rfl⟩ : syracuseStep 2984435 = 4476653) B4476653
theorem B494075 : Blo 307833 494075 := bstep (se 1 (by rfl) ⟨370556, by rfl⟩ : syracuseStep 494075 = 741113) B741113
theorem B789011 : Blo 307833 789011 := bstep (se 1 (by rfl) ⟨591758, by rfl⟩ : syracuseStep 789011 = 1183517) B1183517
theorem B887375 : Blo 307833 887375 := bstep (se 1 (by rfl) ⟨665531, by rfl⟩ : syracuseStep 887375 = 1331063) B1331063
theorem B2395175 : Blo 307833 2395175 := bstep (se 1 (by rfl) ⟨1796381, by rfl⟩ : syracuseStep 2395175 = 3592763) B3592763
theorem B2362445 : Blo 307833 2362445 := bstep (se 3 (by rfl) ⟨442958, by rfl⟩ : syracuseStep 2362445 = 885917) B885917
theorem B1117307 : Blo 307833 1117307 := bstep (se 1 (by rfl) ⟨837980, by rfl⟩ : syracuseStep 1117307 = 1675961) B1675961
theorem B625897 : Blo 307833 625897 := bstep (se 2 (by rfl) ⟨234711, by rfl⟩ : syracuseStep 625897 = 469423) B469423
theorem B8228087 : Blo 307833 8228087 := bstep (se 1 (by rfl) ⟨6171065, by rfl⟩ : syracuseStep 8228087 = 12342131) B12342131
theorem B756985 : Blo 307833 756985 := bstep (se 2 (by rfl) ⟨283869, by rfl⟩ : syracuseStep 756985 = 567739) B567739
theorem B462119 : Blo 307833 462119 := bstep (se 1 (by rfl) ⟨346589, by rfl⟩ : syracuseStep 462119 = 693179) B693179
theorem B1576259 : Blo 307833 1576259 := bstep (se 1 (by rfl) ⟨1182194, by rfl⟩ : syracuseStep 1576259 = 2364389) B2364389
theorem B658783 : Blo 307833 658783 := bstep (se 1 (by rfl) ⟨494087, by rfl⟩ : syracuseStep 658783 = 988175) B988175
theorem B462203 : Blo 307833 462203 := bstep (se 1 (by rfl) ⟨346652, by rfl⟩ : syracuseStep 462203 = 693305) B693305
theorem B462329 : Blo 307833 462329 := bstep (se 2 (by rfl) ⟨173373, by rfl⟩ : syracuseStep 462329 = 346747) B346747
theorem B658937 : Blo 307833 658937 := bstep (se 2 (by rfl) ⟨247101, by rfl⟩ : syracuseStep 658937 = 494203) B494203
theorem B331327 : Blo 307833 331327 := bstep (se 1 (by rfl) ⟨248495, by rfl⟩ : syracuseStep 331327 = 496991) B496991
theorem B1052243 : Blo 307833 1052243 := bstep (se 1 (by rfl) ⟨789182, by rfl⟩ : syracuseStep 1052243 = 1578365) B1578365
theorem B462431 : Blo 307833 462431 := bstep (se 1 (by rfl) ⟨346823, by rfl⟩ : syracuseStep 462431 = 693647) B693647
theorem B626473 : Blo 307833 626473 := bstep (se 2 (by rfl) ⟨234927, by rfl⟩ : syracuseStep 626473 = 469855) B469855
theorem B495401 : Blo 307833 495401 := bstep (se 2 (by rfl) ⟨185775, by rfl⟩ : syracuseStep 495401 = 371551) B371551
theorem B1576745 : Blo 307833 1576745 := bstep (se 2 (by rfl) ⟨591279, by rfl⟩ : syracuseStep 1576745 = 1182559) B1182559
theorem B495407 : Blo 307833 495407 := bstep (se 1 (by rfl) ⟨371555, by rfl⟩ : syracuseStep 495407 = 743111) B743111
theorem B2658095 : Blo 307833 2658095 := bstep (se 1 (by rfl) ⟨1993571, by rfl⟩ : syracuseStep 2658095 = 3987143) B3987143
theorem B462647 : Blo 307833 462647 := bstep (se 1 (by rfl) ⟨346985, by rfl⟩ : syracuseStep 462647 = 693971) B693971
theorem B2363417 : Blo 307833 2363417 := bstep (se 2 (by rfl) ⟨886281, by rfl⟩ : syracuseStep 2363417 = 1772563) B1772563
theorem B462953 : Blo 307833 462953 := bstep (se 2 (by rfl) ⟨173607, by rfl⟩ : syracuseStep 462953 = 347215) B347215
theorem B11309219 : Blo 307833 11309219 := bstep (se 1 (by rfl) ⟨8481914, by rfl⟩ : syracuseStep 11309219 = 16963829) B16963829
theorem B463271 : Blo 307833 463271 := bstep (se 1 (by rfl) ⟨347453, by rfl⟩ : syracuseStep 463271 = 694907) B694907
theorem B1675721 : Blo 307833 1675721 := bstep (se 2 (by rfl) ⟨628395, by rfl⟩ : syracuseStep 1675721 = 1256791) B1256791
theorem B463355 : Blo 307833 463355 := bstep (se 1 (by rfl) ⟨347516, by rfl⟩ : syracuseStep 463355 = 695033) B695033
theorem B5345909 : Blo 307833 5345909 := bstep (se 5 (by rfl) ⟨250589, by rfl⟩ : syracuseStep 5345909 = 501179) B501179
theorem B463481 : Blo 307833 463481 := bstep (se 2 (by rfl) ⟨173805, by rfl⟩ : syracuseStep 463481 = 347611) B347611
theorem B463535 : Blo 307833 463535 := bstep (se 1 (by rfl) ⟨347651, by rfl⟩ : syracuseStep 463535 = 695303) B695303
theorem B463583 : Blo 307833 463583 := bstep (se 1 (by rfl) ⟨347687, by rfl⟩ : syracuseStep 463583 = 695375) B695375
theorem B332591 : Blo 307833 332591 := bstep (se 1 (by rfl) ⟨249443, by rfl⟩ : syracuseStep 332591 = 498887) B498887
theorem B693071 : Blo 307833 693071 := bstep (se 1 (by rfl) ⟨519803, by rfl⟩ : syracuseStep 693071 = 1039607) B1039607
theorem B463847 : Blo 307833 463847 := bstep (se 1 (by rfl) ⟨347885, by rfl⟩ : syracuseStep 463847 = 695771) B695771
theorem B693287 : Blo 307833 693287 := bstep (se 1 (by rfl) ⟨519965, by rfl⟩ : syracuseStep 693287 = 1039931) B1039931
theorem B1578041 : Blo 307833 1578041 := bstep (se 2 (by rfl) ⟨591765, by rfl⟩ : syracuseStep 1578041 = 1183531) B1183531
theorem B660577 : Blo 307833 660577 := bstep (se 2 (by rfl) ⟨247716, by rfl⟩ : syracuseStep 660577 = 495433) B495433
theorem B693467 : Blo 307833 693467 := bstep (se 1 (by rfl) ⟨520100, by rfl⟩ : syracuseStep 693467 = 1040201) B1040201
theorem B464105 : Blo 307833 464105 := bstep (se 2 (by rfl) ⟨174039, by rfl⟩ : syracuseStep 464105 = 348079) B348079
theorem B2233601 : Blo 307833 2233601 := bstep (se 2 (by rfl) ⟨837600, by rfl⟩ : syracuseStep 2233601 = 1675201) B1675201
theorem B464159 : Blo 307833 464159 := bstep (se 1 (by rfl) ⟨348119, by rfl⟩ : syracuseStep 464159 = 696239) B696239
theorem B791905 : Blo 307833 791905 := bstep (se 2 (by rfl) ⟨296964, by rfl⟩ : syracuseStep 791905 = 593929) B593929
theorem B693665 : Blo 307833 693665 := bstep (se 2 (by rfl) ⟨260124, by rfl⟩ : syracuseStep 693665 = 520249) B520249
theorem B464327 : Blo 307833 464327 := bstep (se 1 (by rfl) ⟨348245, by rfl⟩ : syracuseStep 464327 = 696491) B696491
theorem B2364875 : Blo 307833 2364875 := bstep (se 1 (by rfl) ⟨1773656, by rfl⟩ : syracuseStep 2364875 = 3547313) B3547313
theorem B792071 : Blo 307833 792071 := bstep (se 1 (by rfl) ⟨594053, by rfl⟩ : syracuseStep 792071 = 1188107) B1188107
theorem B5936885 : Blo 307833 5936885 := bstep (se 5 (by rfl) ⟨278291, by rfl⟩ : syracuseStep 5936885 = 556583) B556583
theorem B464681 : Blo 307833 464681 := bstep (se 2 (by rfl) ⟨174255, by rfl⟩ : syracuseStep 464681 = 348511) B348511
theorem B464687 : Blo 307833 464687 := bstep (se 1 (by rfl) ⟨348515, by rfl⟩ : syracuseStep 464687 = 697031) B697031
theorem B1316695 : Blo 307833 1316695 := bstep (se 1 (by rfl) ⟨987521, by rfl⟩ : syracuseStep 1316695 = 1975043) B1975043
theorem B694223 : Blo 307833 694223 := bstep (se 1 (by rfl) ⟨520667, by rfl⟩ : syracuseStep 694223 = 1041335) B1041335
theorem B465161 : Blo 307833 465161 := bstep (se 2 (by rfl) ⟨174435, by rfl⟩ : syracuseStep 465161 = 348871) B348871
theorem B694601 : Blo 307833 694601 := bstep (se 2 (by rfl) ⟨260475, by rfl⟩ : syracuseStep 694601 = 520951) B520951
theorem B4462937 : Blo 307833 4462937 := bstep (se 2 (by rfl) ⟨1673601, by rfl⟩ : syracuseStep 4462937 = 3347203) B3347203
theorem B694619 : Blo 307833 694619 := bstep (se 1 (by rfl) ⟨520964, by rfl⟩ : syracuseStep 694619 = 1041929) B1041929
theorem B465263 : Blo 307833 465263 := bstep (se 1 (by rfl) ⟨348947, by rfl⟩ : syracuseStep 465263 = 697895) B697895
theorem B661927 : Blo 307833 661927 := bstep (se 1 (by rfl) ⟨496445, by rfl⟩ : syracuseStep 661927 = 992891) B992891
theorem B465479 : Blo 307833 465479 := bstep (se 1 (by rfl) ⟨349109, by rfl⟩ : syracuseStep 465479 = 698219) B698219
theorem B465515 : Blo 307833 465515 := bstep (se 1 (by rfl) ⟨349136, by rfl⟩ : syracuseStep 465515 = 698273) B698273
theorem B10033955 : Blo 307833 10033955 := bstep (se 1 (by rfl) ⟨7525466, by rfl⟩ : syracuseStep 10033955 = 15050933) B15050933
theorem B465743 : Blo 307833 465743 := bstep (se 1 (by rfl) ⟨349307, by rfl⟩ : syracuseStep 465743 = 698615) B698615
theorem B1481591 : Blo 307833 1481591 := bstep (se 1 (by rfl) ⟨1111193, by rfl⟩ : syracuseStep 1481591 = 2222387) B2222387
theorem B695195 : Blo 307833 695195 := bstep (se 1 (by rfl) ⟨521396, by rfl⟩ : syracuseStep 695195 = 1042793) B1042793
theorem B3840953 : Blo 307833 3840953 := bstep (se 2 (by rfl) ⟨1440357, by rfl⟩ : syracuseStep 3840953 = 2880715) B2880715
theorem B695393 : Blo 307833 695393 := bstep (se 2 (by rfl) ⟨260772, by rfl⟩ : syracuseStep 695393 = 521545) B521545
theorem B466139 : Blo 307833 466139 := bstep (se 1 (by rfl) ⟨349604, by rfl⟩ : syracuseStep 466139 = 699209) B699209
theorem B695591 : Blo 307833 695591 := bstep (se 1 (by rfl) ⟨521693, by rfl⟩ : syracuseStep 695591 = 1043387) B1043387
theorem B466313 : Blo 307833 466313 := bstep (se 2 (by rfl) ⟨174867, by rfl⟩ : syracuseStep 466313 = 349735) B349735
theorem B695969 : Blo 307833 695969 := bstep (se 2 (by rfl) ⟨260988, by rfl⟩ : syracuseStep 695969 = 521977) B521977
theorem B466667 : Blo 307833 466667 := bstep (se 1 (by rfl) ⟨350000, by rfl⟩ : syracuseStep 466667 = 700001) B700001
theorem B2367305 : Blo 307833 2367305 := bstep (se 2 (by rfl) ⟨887739, by rfl⟩ : syracuseStep 2367305 = 1775479) B1775479
theorem B466895 : Blo 307833 466895 := bstep (se 1 (by rfl) ⟨350171, by rfl⟩ : syracuseStep 466895 = 700343) B700343
theorem B696329 : Blo 307833 696329 := bstep (se 2 (by rfl) ⟨261123, by rfl⟩ : syracuseStep 696329 = 522247) B522247
theorem B14983379 : Blo 307833 14983379 := bstep (se 1 (by rfl) ⟨11237534, by rfl⟩ : syracuseStep 14983379 = 22475069) B22475069
theorem B467291 : Blo 307833 467291 := bstep (se 1 (by rfl) ⟨350468, by rfl⟩ : syracuseStep 467291 = 700937) B700937
theorem B696743 : Blo 307833 696743 := bstep (se 1 (by rfl) ⟨522557, by rfl⟩ : syracuseStep 696743 = 1045115) B1045115
theorem B6758923 : Blo 307833 6758923 := bstep (se 1 (by rfl) ⟨5069192, by rfl⟩ : syracuseStep 6758923 = 10138385) B10138385
theorem B696851 : Blo 307833 696851 := bstep (se 1 (by rfl) ⟨522638, by rfl⟩ : syracuseStep 696851 = 1045277) B1045277
theorem B467519 : Blo 307833 467519 := bstep (se 1 (by rfl) ⟨350639, by rfl⟩ : syracuseStep 467519 = 701279) B701279
theorem B696905 : Blo 307833 696905 := bstep (se 2 (by rfl) ⟨261339, by rfl⟩ : syracuseStep 696905 = 522679) B522679
theorem B991865 : Blo 307833 991865 := bstep (se 2 (by rfl) ⟨371949, by rfl⟩ : syracuseStep 991865 = 743899) B743899
theorem B467639 : Blo 307833 467639 := bstep (se 1 (by rfl) ⟨350729, by rfl⟩ : syracuseStep 467639 = 701459) B701459
theorem B16851725 : Blo 307833 16851725 := bstep (se 3 (by rfl) ⟨3159698, by rfl⟩ : syracuseStep 16851725 = 6319397) B6319397
theorem B42738445 : Blo 307833 42738445 := bstep (se 3 (by rfl) ⟨8013458, by rfl⟩ : syracuseStep 42738445 = 16026917) B16026917
theorem B697319 : Blo 307833 697319 := bstep (se 1 (by rfl) ⟨522989, by rfl⟩ : syracuseStep 697319 = 1045979) B1045979
theorem B1975529 : Blo 307833 1975529 := bstep (se 2 (by rfl) ⟨740823, by rfl⟩ : syracuseStep 1975529 = 1481647) B1481647
theorem B697697 : Blo 307833 697697 := bstep (se 2 (by rfl) ⟨261636, by rfl⟩ : syracuseStep 697697 = 523273) B523273
theorem B697787 : Blo 307833 697787 := bstep (se 1 (by rfl) ⟨523340, by rfl⟩ : syracuseStep 697787 = 1046681) B1046681
theorem B697913 : Blo 307833 697913 := bstep (se 2 (by rfl) ⟨261717, by rfl⟩ : syracuseStep 697913 = 523435) B523435
theorem B2827997 : Blo 307833 2827997 := bstep (se 3 (by rfl) ⟨530249, by rfl⟩ : syracuseStep 2827997 = 1060499) B1060499
theorem B698579 : Blo 307833 698579 := bstep (se 1 (by rfl) ⟨523934, by rfl⟩ : syracuseStep 698579 = 1047869) B1047869
theorem B698633 : Blo 307833 698633 := bstep (se 2 (by rfl) ⟨261987, by rfl⟩ : syracuseStep 698633 = 523975) B523975
theorem B1321427 : Blo 307833 1321427 := bstep (se 1 (by rfl) ⟨991070, by rfl⟩ : syracuseStep 1321427 = 1982141) B1982141
theorem B698849 : Blo 307833 698849 := bstep (se 2 (by rfl) ⟨262068, by rfl⟩ : syracuseStep 698849 = 524137) B524137
theorem B1321667 : Blo 307833 1321667 := bstep (se 1 (by rfl) ⟨991250, by rfl⟩ : syracuseStep 1321667 = 1982501) B1982501
theorem B699155 : Blo 307833 699155 := bstep (se 1 (by rfl) ⟨524366, by rfl⟩ : syracuseStep 699155 = 1048733) B1048733
theorem B621849635 : Blo 307833 621849635 := bstep (se 1 (by rfl) ⟨466387226, by rfl⟩ : syracuseStep 621849635 = 932774453) B932774453
theorem B699515 : Blo 307833 699515 := bstep (se 1 (by rfl) ⟨524636, by rfl⟩ : syracuseStep 699515 = 1049273) B1049273
theorem B994493 : Blo 307833 994493 := bstep (se 3 (by rfl) ⟨186467, by rfl⟩ : syracuseStep 994493 = 372935) B372935
theorem B699641 : Blo 307833 699641 := bstep (se 2 (by rfl) ⟨262365, by rfl⟩ : syracuseStep 699641 = 524731) B524731
theorem B2338145 : Blo 307833 2338145 := bstep (se 2 (by rfl) ⟨876804, by rfl⟩ : syracuseStep 2338145 = 1753609) B1753609
theorem B699785 : Blo 307833 699785 := bstep (se 2 (by rfl) ⟨262419, by rfl⟩ : syracuseStep 699785 = 524839) B524839
theorem B699911 : Blo 307833 699911 := bstep (se 1 (by rfl) ⟨524933, by rfl⟩ : syracuseStep 699911 = 1049867) B1049867
theorem B700091 : Blo 307833 700091 := bstep (se 1 (by rfl) ⟨525068, by rfl⟩ : syracuseStep 700091 = 1050137) B1050137
theorem B700217 : Blo 307833 700217 := bstep (se 2 (by rfl) ⟨262581, by rfl⟩ : syracuseStep 700217 = 525163) B525163
theorem B896897 : Blo 307833 896897 := bstep (se 2 (by rfl) ⟨336336, by rfl⟩ : syracuseStep 896897 = 672673) B672673
theorem B1323067 : Blo 307833 1323067 := bstep (se 1 (by rfl) ⟨992300, by rfl⟩ : syracuseStep 1323067 = 1984601) B1984601
theorem B700847 : Blo 307833 700847 := bstep (se 1 (by rfl) ⟨525635, by rfl⟩ : syracuseStep 700847 = 1051271) B1051271
theorem B700883 : Blo 307833 700883 := bstep (se 1 (by rfl) ⟨525662, by rfl⟩ : syracuseStep 700883 = 1051325) B1051325
theorem B373243 : Blo 307833 373243 := bstep (se 1 (by rfl) ⟨279932, by rfl⟩ : syracuseStep 373243 = 559865) B559865
theorem B700991 : Blo 307833 700991 := bstep (se 1 (by rfl) ⟨525743, by rfl⟩ : syracuseStep 700991 = 1051487) B1051487
theorem B373343 : Blo 307833 373343 := bstep (se 1 (by rfl) ⟨280007, by rfl⟩ : syracuseStep 373343 = 560015) B560015
theorem B701099 : Blo 307833 701099 := bstep (se 1 (by rfl) ⟨525824, by rfl⟩ : syracuseStep 701099 = 1051649) B1051649
theorem B307935 : Blo 307833 307935 := bstep (se 1 (by rfl) ⟨230951, by rfl⟩ : syracuseStep 307935 = 461903) B461903
theorem B308015 : Blo 307833 308015 := bstep (se 1 (by rfl) ⟨231011, by rfl⟩ : syracuseStep 308015 = 462023) B462023
theorem B308123 : Blo 307833 308123 := bstep (se 1 (by rfl) ⟨231092, by rfl⟩ : syracuseStep 308123 = 462185) B462185
theorem B308175 : Blo 307833 308175 := bstep (se 1 (by rfl) ⟨231131, by rfl⟩ : syracuseStep 308175 = 462263) B462263
theorem B308199 : Blo 307833 308199 := bstep (se 1 (by rfl) ⟨231149, by rfl⟩ : syracuseStep 308199 = 462299) B462299
theorem B668795 : Blo 307833 668795 := bstep (se 1 (by rfl) ⟨501596, by rfl⟩ : syracuseStep 668795 = 1003193) B1003193
theorem B5387411 : Blo 307833 5387411 := bstep (se 1 (by rfl) ⟨4040558, by rfl⟩ : syracuseStep 5387411 = 8081117) B8081117
theorem B3781847 : Blo 307833 3781847 := bstep (se 1 (by rfl) ⟨2836385, by rfl⟩ : syracuseStep 3781847 = 5672771) B5672771
theorem B2340089 : Blo 307833 2340089 := bstep (se 2 (by rfl) ⟨877533, by rfl⟩ : syracuseStep 2340089 = 1755067) B1755067
theorem B832799 : Blo 307833 832799 := bstep (se 1 (by rfl) ⟨624599, by rfl⟩ : syracuseStep 832799 = 1249199) B1249199
theorem B308511 : Blo 307833 308511 := bstep (se 1 (by rfl) ⟨231383, by rfl⟩ : syracuseStep 308511 = 462767) B462767
theorem B308571 : Blo 307833 308571 := bstep (se 1 (by rfl) ⟨231428, by rfl⟩ : syracuseStep 308571 = 462857) B462857
theorem B308591 : Blo 307833 308591 := bstep (se 1 (by rfl) ⟨231443, by rfl⟩ : syracuseStep 308591 = 462887) B462887
theorem B308647 : Blo 307833 308647 := bstep (se 1 (by rfl) ⟨231485, by rfl⟩ : syracuseStep 308647 = 462971) B462971
theorem B308731 : Blo 307833 308731 := bstep (se 1 (by rfl) ⟨231548, by rfl⟩ : syracuseStep 308731 = 463097) B463097
theorem B308799 : Blo 307833 308799 := bstep (se 1 (by rfl) ⟨231599, by rfl⟩ : syracuseStep 308799 = 463199) B463199
theorem B308807 : Blo 307833 308807 := bstep (se 1 (by rfl) ⟨231605, by rfl⟩ : syracuseStep 308807 = 463211) B463211
theorem B3159737 : Blo 307833 3159737 := bstep (se 2 (by rfl) ⟨1184901, by rfl⟩ : syracuseStep 3159737 = 2369803) B2369803
theorem B308959 : Blo 307833 308959 := bstep (se 1 (by rfl) ⟨231719, by rfl⟩ : syracuseStep 308959 = 463439) B463439
theorem B309039 : Blo 307833 309039 := bstep (se 1 (by rfl) ⟨231779, by rfl⟩ : syracuseStep 309039 = 463559) B463559
theorem B440111 : Blo 307833 440111 := bstep (se 1 (by rfl) ⟨330083, by rfl⟩ : syracuseStep 440111 = 660167) B660167
theorem B309147 : Blo 307833 309147 := bstep (se 1 (by rfl) ⟨231860, by rfl⟩ : syracuseStep 309147 = 463721) B463721
theorem B309199 : Blo 307833 309199 := bstep (se 1 (by rfl) ⟨231899, by rfl⟩ : syracuseStep 309199 = 463799) B463799
theorem B309223 : Blo 307833 309223 := bstep (se 1 (by rfl) ⟨231917, by rfl⟩ : syracuseStep 309223 = 463835) B463835
theorem B833665 : Blo 307833 833665 := bstep (se 2 (by rfl) ⟨312624, by rfl⟩ : syracuseStep 833665 = 625249) B625249
theorem B997505 : Blo 307833 997505 := bstep (se 2 (by rfl) ⟨374064, by rfl⟩ : syracuseStep 997505 = 748129) B748129
theorem B309535 : Blo 307833 309535 := bstep (se 1 (by rfl) ⟨232151, by rfl⟩ : syracuseStep 309535 = 464303) B464303
theorem B309595 : Blo 307833 309595 := bstep (se 1 (by rfl) ⟨232196, by rfl⟩ : syracuseStep 309595 = 464393) B464393
theorem B309615 : Blo 307833 309615 := bstep (se 1 (by rfl) ⟨232211, by rfl⟩ : syracuseStep 309615 = 464423) B464423
theorem B309671 : Blo 307833 309671 := bstep (se 1 (by rfl) ⟨232253, by rfl⟩ : syracuseStep 309671 = 464507) B464507
theorem B8010161 : Blo 307833 8010161 := bstep (se 2 (by rfl) ⟨3003810, by rfl⟩ : syracuseStep 8010161 = 6007621) B6007621
theorem B309755 : Blo 307833 309755 := bstep (se 1 (by rfl) ⟨232316, by rfl⟩ : syracuseStep 309755 = 464633) B464633
theorem B309823 : Blo 307833 309823 := bstep (se 1 (by rfl) ⟨232367, by rfl⟩ : syracuseStep 309823 = 464735) B464735
theorem B834119 : Blo 307833 834119 := bstep (se 1 (by rfl) ⟨625589, by rfl⟩ : syracuseStep 834119 = 1251179) B1251179
theorem B440903 : Blo 307833 440903 := bstep (se 1 (by rfl) ⟨330677, by rfl⟩ : syracuseStep 440903 = 661355) B661355
theorem B309831 : Blo 307833 309831 := bstep (se 1 (by rfl) ⟨232373, by rfl⟩ : syracuseStep 309831 = 464747) B464747
theorem B309983 : Blo 307833 309983 := bstep (se 1 (by rfl) ⟨232487, by rfl⟩ : syracuseStep 309983 = 464975) B464975
theorem B310063 : Blo 307833 310063 := bstep (se 1 (by rfl) ⟨232547, by rfl⟩ : syracuseStep 310063 = 465095) B465095
theorem B310171 : Blo 307833 310171 := bstep (se 1 (by rfl) ⟨232628, by rfl⟩ : syracuseStep 310171 = 465257) B465257
theorem B310223 : Blo 307833 310223 := bstep (se 1 (by rfl) ⟨232667, by rfl⟩ : syracuseStep 310223 = 465335) B465335
theorem B310247 : Blo 307833 310247 := bstep (se 1 (by rfl) ⟨232685, by rfl⟩ : syracuseStep 310247 = 465371) B465371
theorem B2112733 : Blo 307833 2112733 := bstep (se 3 (by rfl) ⟨396137, by rfl⟩ : syracuseStep 2112733 = 792275) B792275
theorem B310559 : Blo 307833 310559 := bstep (se 1 (by rfl) ⟨232919, by rfl⟩ : syracuseStep 310559 = 465839) B465839
theorem B310619 : Blo 307833 310619 := bstep (se 1 (by rfl) ⟨232964, by rfl⟩ : syracuseStep 310619 = 465929) B465929
theorem B310639 : Blo 307833 310639 := bstep (se 1 (by rfl) ⟨232979, by rfl⟩ : syracuseStep 310639 = 465959) B465959
theorem B310695 : Blo 307833 310695 := bstep (se 1 (by rfl) ⟨233021, by rfl⟩ : syracuseStep 310695 = 466043) B466043
theorem B310779 : Blo 307833 310779 := bstep (se 1 (by rfl) ⟨233084, by rfl⟩ : syracuseStep 310779 = 466169) B466169
theorem B310847 : Blo 307833 310847 := bstep (se 1 (by rfl) ⟨233135, by rfl⟩ : syracuseStep 310847 = 466271) B466271
theorem B310855 : Blo 307833 310855 := bstep (se 1 (by rfl) ⟨233141, by rfl⟩ : syracuseStep 310855 = 466283) B466283
theorem B311007 : Blo 307833 311007 := bstep (se 1 (by rfl) ⟨233255, by rfl⟩ : syracuseStep 311007 = 466511) B466511
theorem B311087 : Blo 307833 311087 := bstep (se 1 (by rfl) ⟨233315, by rfl⟩ : syracuseStep 311087 = 466631) B466631
theorem B311195 : Blo 307833 311195 := bstep (se 1 (by rfl) ⟨233396, by rfl⟩ : syracuseStep 311195 = 466793) B466793
theorem B311247 : Blo 307833 311247 := bstep (se 1 (by rfl) ⟨233435, by rfl⟩ : syracuseStep 311247 = 466871) B466871
theorem B311271 : Blo 307833 311271 := bstep (se 1 (by rfl) ⟨233453, by rfl⟩ : syracuseStep 311271 = 466907) B466907
theorem B311583 : Blo 307833 311583 := bstep (se 1 (by rfl) ⟨233687, by rfl⟩ : syracuseStep 311583 = 467375) B467375
theorem B311643 : Blo 307833 311643 := bstep (se 1 (by rfl) ⟨233732, by rfl⟩ : syracuseStep 311643 = 467465) B467465
theorem B311663 : Blo 307833 311663 := bstep (se 1 (by rfl) ⟨233747, by rfl⟩ : syracuseStep 311663 = 467495) B467495
theorem B311719 : Blo 307833 311719 := bstep (se 1 (by rfl) ⟨233789, by rfl⟩ : syracuseStep 311719 = 467579) B467579
theorem B311803 : Blo 307833 311803 := bstep (se 1 (by rfl) ⟨233852, by rfl⟩ : syracuseStep 311803 = 467705) B467705
theorem B1491527 : Blo 307833 1491527 := bstep (se 1 (by rfl) ⟨1118645, by rfl⟩ : syracuseStep 1491527 = 2237291) B2237291
theorem B10240685 : Blo 307833 10240685 := bstep (se 3 (by rfl) ⟨1920128, by rfl⟩ : syracuseStep 10240685 = 3840257) B3840257
theorem B836477 : Blo 307833 836477 := bstep (se 3 (by rfl) ⟨156839, by rfl⟩ : syracuseStep 836477 = 313679) B313679
theorem B705887 : Blo 307833 705887 := bstep (se 1 (by rfl) ⟨529415, by rfl⟩ : syracuseStep 705887 = 1058831) B1058831
theorem B346459 : Blo 307833 346459 := bstep (se 1 (by rfl) ⟨259844, by rfl⟩ : syracuseStep 346459 = 519689) B519689
theorem B346567 : Blo 307833 346567 := bstep (se 1 (by rfl) ⟨259925, by rfl⟩ : syracuseStep 346567 = 519851) B519851
theorem B2673107 : Blo 307833 2673107 := bstep (se 1 (by rfl) ⟨2004830, by rfl⟩ : syracuseStep 2673107 = 4009661) B4009661
theorem B838163 : Blo 307833 838163 := bstep (se 1 (by rfl) ⟨628622, by rfl⟩ : syracuseStep 838163 = 1257245) B1257245
theorem B22727303 : Blo 307833 22727303 := bstep (se 1 (by rfl) ⟨17045477, by rfl⟩ : syracuseStep 22727303 = 34090955) B34090955
theorem B8014625 : Blo 307833 8014625 := bstep (se 2 (by rfl) ⟨3005484, by rfl⟩ : syracuseStep 8014625 = 6010969) B6010969
theorem B346927 : Blo 307833 346927 := bstep (se 1 (by rfl) ⟨260195, by rfl⟩ : syracuseStep 346927 = 520391) B520391
theorem B1592183 : Blo 307833 1592183 := bstep (se 1 (by rfl) ⟨1194137, by rfl⟩ : syracuseStep 1592183 = 2388275) B2388275
theorem B347035 : Blo 307833 347035 := bstep (se 1 (by rfl) ⟨260276, by rfl⟩ : syracuseStep 347035 = 520553) B520553
theorem B1330091 : Blo 307833 1330091 := bstep (se 1 (by rfl) ⟨997568, by rfl⟩ : syracuseStep 1330091 = 1995137) B1995137
theorem B347431 : Blo 307833 347431 := bstep (se 1 (by rfl) ⟨260573, by rfl⟩ : syracuseStep 347431 = 521147) B521147
theorem B347503 : Blo 307833 347503 := bstep (se 1 (by rfl) ⟨260627, by rfl⟩ : syracuseStep 347503 = 521255) B521255
theorem B25873843 : Blo 307833 25873843 := bstep (se 1 (by rfl) ⟨19405382, by rfl⟩ : syracuseStep 25873843 = 38810765) B38810765
theorem B347719 : Blo 307833 347719 := bstep (se 1 (by rfl) ⟨260789, by rfl⟩ : syracuseStep 347719 = 521579) B521579
theorem B937775 : Blo 307833 937775 := bstep (se 1 (by rfl) ⟨703331, by rfl⟩ : syracuseStep 937775 = 1406663) B1406663
theorem B2347379 : Blo 307833 2347379 := bstep (se 1 (by rfl) ⟨1760534, by rfl⟩ : syracuseStep 2347379 = 3521069) B3521069
theorem B348583 : Blo 307833 348583 := bstep (se 1 (by rfl) ⟨261437, by rfl⟩ : syracuseStep 348583 = 522875) B522875
theorem B446971 : Blo 307833 446971 := bstep (se 1 (by rfl) ⟨335228, by rfl⟩ : syracuseStep 446971 = 670457) B670457
theorem B349159 : Blo 307833 349159 := bstep (se 1 (by rfl) ⟨261869, by rfl⟩ : syracuseStep 349159 = 523739) B523739
theorem B4773113 : Blo 307833 4773113 := bstep (se 2 (by rfl) ⟨1789917, by rfl⟩ : syracuseStep 4773113 = 3579835) B3579835
theorem B2873017 : Blo 307833 2873017 := bstep (se 2 (by rfl) ⟨1077381, by rfl⟩ : syracuseStep 2873017 = 2154763) B2154763
theorem B1988651 : Blo 307833 1988651 := bstep (se 1 (by rfl) ⟨1491488, by rfl⟩ : syracuseStep 1988651 = 2982977) B2982977
theorem B1497487 : Blo 307833 1497487 := bstep (se 1 (by rfl) ⟨1123115, by rfl⟩ : syracuseStep 1497487 = 2246231) B2246231
theorem B5954107 : Blo 307833 5954107 := bstep (se 1 (by rfl) ⟨4465580, by rfl⟩ : syracuseStep 5954107 = 8931161) B8931161
theorem B1333883 : Blo 307833 1333883 := bstep (se 1 (by rfl) ⟨1000412, by rfl⟩ : syracuseStep 1333883 = 2000825) B2000825
theorem B7527107 : Blo 307833 7527107 := bstep (se 1 (by rfl) ⟨5645330, by rfl⟩ : syracuseStep 7527107 = 11290661) B11290661
theorem B1596125 : Blo 307833 1596125 := bstep (se 3 (by rfl) ⟨299273, by rfl⟩ : syracuseStep 1596125 = 598547) B598547
theorem B5266295 : Blo 307833 5266295 := bstep (se 1 (by rfl) ⟨3949721, by rfl⟩ : syracuseStep 5266295 = 7899443) B7899443
theorem B1039229 : Blo 307833 1039229 := bstep (se 3 (by rfl) ⟨194855, by rfl⟩ : syracuseStep 1039229 = 389711) B389711
theorem B744571 : Blo 307833 744571 := bstep (se 1 (by rfl) ⟨558428, by rfl⟩ : syracuseStep 744571 = 1116857) B1116857
theorem B1039499 : Blo 307833 1039499 := bstep (se 1 (by rfl) ⟨779624, by rfl⟩ : syracuseStep 1039499 = 1559249) B1559249
theorem B9002785 : Blo 307833 9002785 := bstep (se 2 (by rfl) ⟨3376044, by rfl⟩ : syracuseStep 9002785 = 6752089) B6752089
theorem B1695953 : Blo 307833 1695953 := bstep (se 2 (by rfl) ⟨635982, by rfl⟩ : syracuseStep 1695953 = 1271965) B1271965
theorem B3531275 : Blo 307833 3531275 := bstep (se 1 (by rfl) ⟨2648456, by rfl⟩ : syracuseStep 3531275 = 5296913) B5296913
theorem B10019537 : Blo 307833 10019537 := bstep (se 2 (by rfl) ⟨3757326, by rfl⟩ : syracuseStep 10019537 = 7514653) B7514653
theorem B1041119 : Blo 307833 1041119 := bstep (se 1 (by rfl) ⟨780839, by rfl⟩ : syracuseStep 1041119 = 1561679) B1561679
theorem B1532903 : Blo 307833 1532903 := bstep (se 1 (by rfl) ⟨1149677, by rfl⟩ : syracuseStep 1532903 = 2299355) B2299355
theorem B1041551 : Blo 307833 1041551 := bstep (se 1 (by rfl) ⟨781163, by rfl⟩ : syracuseStep 1041551 = 1562327) B1562327
theorem B1172627 : Blo 307833 1172627 := bstep (se 1 (by rfl) ⟨879470, by rfl⟩ : syracuseStep 1172627 = 1758941) B1758941
theorem B779483 : Blo 307833 779483 := bstep (se 1 (by rfl) ⟨584612, by rfl⟩ : syracuseStep 779483 = 1169225) B1169225
theorem B648425 : Blo 307833 648425 := bstep (se 2 (by rfl) ⟨243159, by rfl⟩ : syracuseStep 648425 = 486319) B486319
theorem B779615 : Blo 307833 779615 := bstep (se 1 (by rfl) ⟨584711, by rfl⟩ : syracuseStep 779615 = 1169423) B1169423
theorem B1566215 : Blo 307833 1566215 := bstep (se 1 (by rfl) ⟨1174661, by rfl⟩ : syracuseStep 1566215 = 2349323) B2349323
theorem B11888531 : Blo 307833 11888531 := bstep (se 1 (by rfl) ⟨8916398, by rfl⟩ : syracuseStep 11888531 = 17832797) B17832797
theorem B1566701 : Blo 307833 1566701 := bstep (se 3 (by rfl) ⟨293756, by rfl⟩ : syracuseStep 1566701 = 587513) B587513
theorem B780313 : Blo 307833 780313 := bstep (se 2 (by rfl) ⟨292617, by rfl⟩ : syracuseStep 780313 = 585235) B585235
theorem B10741997 : Blo 307833 10741997 := bstep (se 3 (by rfl) ⟨2014124, by rfl⟩ : syracuseStep 10741997 = 4028249) B4028249
theorem B1042685 : Blo 307833 1042685 := bstep (se 3 (by rfl) ⟨195503, by rfl⟩ : syracuseStep 1042685 = 391007) B391007
theorem B780617 : Blo 307833 780617 := bstep (se 2 (by rfl) ⟨292731, by rfl⟩ : syracuseStep 780617 = 585463) B585463
theorem B1567187 : Blo 307833 1567187 := bstep (se 1 (by rfl) ⟨1175390, by rfl⟩ : syracuseStep 1567187 = 2350781) B2350781
theorem B2648699 : Blo 307833 2648699 := bstep (se 1 (by rfl) ⟨1986524, by rfl⟩ : syracuseStep 2648699 = 3973049) B3973049
theorem B1567511 : Blo 307833 1567511 := bstep (se 1 (by rfl) ⟨1175633, by rfl⟩ : syracuseStep 1567511 = 2351267) B2351267
theorem B420763 : Blo 307833 420763 := bstep (se 1 (by rfl) ⟨315572, by rfl⟩ : syracuseStep 420763 = 631145) B631145
theorem B748531 : Blo 307833 748531 := bstep (se 1 (by rfl) ⟨561398, by rfl⟩ : syracuseStep 748531 = 1122797) B1122797
theorem B10742807 : Blo 307833 10742807 := bstep (se 1 (by rfl) ⟨8057105, by rfl⟩ : syracuseStep 10742807 = 16114211) B16114211
theorem B1043495 : Blo 307833 1043495 := bstep (se 1 (by rfl) ⟨782621, by rfl⟩ : syracuseStep 1043495 = 1565243) B1565243
theorem B1272955 : Blo 307833 1272955 := bstep (se 1 (by rfl) ⟨954716, by rfl⟩ : syracuseStep 1272955 = 1909433) B1909433
theorem B879835 : Blo 307833 879835 := bstep (se 1 (by rfl) ⟨659876, by rfl⟩ : syracuseStep 879835 = 1319753) B1319753
theorem B519547 : Blo 307833 519547 := bstep (se 1 (by rfl) ⟨389660, by rfl⟩ : syracuseStep 519547 = 779321) B779321
theorem B585083 : Blo 307833 585083 := bstep (se 1 (by rfl) ⟨438812, by rfl⟩ : syracuseStep 585083 = 877625) B877625
theorem B1043927 : Blo 307833 1043927 := bstep (se 1 (by rfl) ⟨782945, by rfl⟩ : syracuseStep 1043927 = 1565891) B1565891
theorem B355835 : Blo 307833 355835 := bstep (se 1 (by rfl) ⟨266876, by rfl⟩ : syracuseStep 355835 = 533753) B533753
theorem B880541 : Blo 307833 880541 := bstep (se 3 (by rfl) ⟨165101, by rfl⟩ : syracuseStep 880541 = 330203) B330203
theorem B7991297 : Blo 307833 7991297 := bstep (se 2 (by rfl) ⟨2996736, by rfl⟩ : syracuseStep 7991297 = 5993473) B5993473
theorem B3960899 : Blo 307833 3960899 := bstep (se 1 (by rfl) ⟨2970674, by rfl⟩ : syracuseStep 3960899 = 5941349) B5941349
theorem B1765547 : Blo 307833 1765547 := bstep (se 1 (by rfl) ⟨1324160, by rfl⟩ : syracuseStep 1765547 = 2648321) B2648321
theorem B1569131 : Blo 307833 1569131 := bstep (se 1 (by rfl) ⟨1176848, by rfl⟩ : syracuseStep 1569131 = 2353697) B2353697
theorem B357167 : Blo 307833 357167 := bstep (se 1 (by rfl) ⟨267875, by rfl⟩ : syracuseStep 357167 = 535751) B535751
theorem B521039 : Blo 307833 521039 := bstep (se 1 (by rfl) ⟨390779, by rfl⟩ : syracuseStep 521039 = 781559) B781559
theorem B1176515 : Blo 307833 1176515 := bstep (se 1 (by rfl) ⟨882386, by rfl⟩ : syracuseStep 1176515 = 1764773) B1764773
theorem B1045601 : Blo 307833 1045601 := bstep (se 2 (by rfl) ⟨392100, by rfl⟩ : syracuseStep 1045601 = 784201) B784201
theorem B2847869 : Blo 307833 2847869 := bstep (se 3 (by rfl) ⟨533975, by rfl⟩ : syracuseStep 2847869 = 1067951) B1067951
theorem B783503 : Blo 307833 783503 := bstep (se 1 (by rfl) ⟨587627, by rfl⟩ : syracuseStep 783503 = 1175255) B1175255
theorem B947495 : Blo 307833 947495 := bstep (se 1 (by rfl) ⟨710621, by rfl⟩ : syracuseStep 947495 = 1421243) B1421243
theorem B390511 : Blo 307833 390511 := bstep (se 1 (by rfl) ⟨292883, by rfl⟩ : syracuseStep 390511 = 585767) B585767
theorem B2356613 : Blo 307833 2356613 := bstep (se 4 (by rfl) ⟨220932, by rfl⟩ : syracuseStep 2356613 = 441865) B441865
theorem B1570589 : Blo 307833 1570589 := bstep (se 3 (by rfl) ⟨294485, by rfl⟩ : syracuseStep 1570589 = 588971) B588971
theorem B522031 : Blo 307833 522031 := bstep (se 1 (by rfl) ⟨391523, by rfl⟩ : syracuseStep 522031 = 783047) B783047
theorem B587567 : Blo 307833 587567 := bstep (se 1 (by rfl) ⟨440675, by rfl⟩ : syracuseStep 587567 = 881351) B881351
theorem B391387 : Blo 307833 391387 := bstep (se 1 (by rfl) ⟨293540, by rfl⟩ : syracuseStep 391387 = 587081) B587081
theorem B1046951 : Blo 307833 1046951 := bstep (se 1 (by rfl) ⟨785213, by rfl⟩ : syracuseStep 1046951 = 1570427) B1570427
theorem B2652695 : Blo 307833 2652695 := bstep (se 1 (by rfl) ⟨1989521, by rfl⟩ : syracuseStep 2652695 = 3979043) B3979043
theorem B1047113 : Blo 307833 1047113 := bstep (se 2 (by rfl) ⟨392667, by rfl⟩ : syracuseStep 1047113 = 785335) B785335
theorem B1178185 : Blo 307833 1178185 := bstep (se 2 (by rfl) ⟨441819, by rfl⟩ : syracuseStep 1178185 = 883639) B883639
theorem B1997723 : Blo 307833 1997723 := bstep (se 1 (by rfl) ⟨1498292, by rfl⟩ : syracuseStep 1997723 = 2996585) B2996585
theorem B785447 : Blo 307833 785447 := bstep (se 1 (by rfl) ⟨589085, by rfl⟩ : syracuseStep 785447 = 1178171) B1178171
theorem B1768715 : Blo 307833 1768715 := bstep (se 1 (by rfl) ⟨1326536, by rfl⟩ : syracuseStep 1768715 = 2653073) B2653073
theorem B556411 : Blo 307833 556411 := bstep (se 1 (by rfl) ⟨417308, by rfl⟩ : syracuseStep 556411 = 834617) B834617
theorem B785801 : Blo 307833 785801 := bstep (se 2 (by rfl) ⟨294675, by rfl⟩ : syracuseStep 785801 = 589351) B589351
theorem B2653721 : Blo 307833 2653721 := bstep (se 2 (by rfl) ⟨995145, by rfl⟩ : syracuseStep 2653721 = 1990291) B1990291
theorem B884459 : Blo 307833 884459 := bstep (se 1 (by rfl) ⟨663344, by rfl⟩ : syracuseStep 884459 = 1326689) B1326689
theorem B2359043 : Blo 307833 2359043 := bstep (se 1 (by rfl) ⟨1769282, by rfl⟩ : syracuseStep 2359043 = 3538565) B3538565
theorem B589609 : Blo 307833 589609 := bstep (se 2 (by rfl) ⟨221103, by rfl⟩ : syracuseStep 589609 = 442207) B442207
theorem B393007 : Blo 307833 393007 := bstep (se 1 (by rfl) ⟨294755, by rfl⟩ : syracuseStep 393007 = 589511) B589511
theorem B393599 : Blo 307833 393599 := bstep (se 1 (by rfl) ⟨295199, by rfl⟩ : syracuseStep 393599 = 590399) B590399
theorem B557651 : Blo 307833 557651 := bstep (se 1 (by rfl) ⟨418238, by rfl⟩ : syracuseStep 557651 = 836477) B836477
theorem B1573505 : Blo 307833 1573505 := bstep (se 2 (by rfl) ⟨590064, by rfl⟩ : syracuseStep 1573505 = 1180129) B1180129
theorem B9011897 : Blo 307833 9011897 := bstep (se 2 (by rfl) ⟨3379461, by rfl⟩ : syracuseStep 9011897 = 6758923) B6758923
theorem B525035 : Blo 307833 525035 := bstep (se 1 (by rfl) ⟨393776, by rfl⟩ : syracuseStep 525035 = 787553) B787553
theorem B56984593 : Blo 307833 56984593 := bstep (se 2 (by rfl) ⟨21369222, by rfl⟩ : syracuseStep 56984593 = 42738445) B42738445
theorem B394303 : Blo 307833 394303 := bstep (se 1 (by rfl) ⟨295727, by rfl⟩ : syracuseStep 394303 = 591455) B591455
theorem B1049705 : Blo 307833 1049705 := bstep (se 2 (by rfl) ⟨393639, by rfl⟩ : syracuseStep 1049705 = 787279) B787279
theorem B525487 : Blo 307833 525487 := bstep (se 1 (by rfl) ⟨394115, by rfl⟩ : syracuseStep 525487 = 788231) B788231
theorem B1770923 : Blo 307833 1770923 := bstep (se 1 (by rfl) ⟨1328192, by rfl⟩ : syracuseStep 1770923 = 2656385) B2656385
theorem B1574315 : Blo 307833 1574315 := bstep (se 1 (by rfl) ⟨1180736, by rfl⟩ : syracuseStep 1574315 = 2361473) B2361473
theorem B788089 : Blo 307833 788089 := bstep (se 2 (by rfl) ⟨295533, by rfl⟩ : syracuseStep 788089 = 591067) B591067
theorem B329383 : Blo 307833 329383 := bstep (se 1 (by rfl) ⟨247037, by rfl⟩ : syracuseStep 329383 = 494075) B494075
theorem B558775 : Blo 307833 558775 := bstep (se 1 (by rfl) ⟨419081, by rfl⟩ : syracuseStep 558775 = 838163) B838163
theorem B526007 : Blo 307833 526007 := bstep (se 1 (by rfl) ⟨394505, by rfl⟩ : syracuseStep 526007 = 789011) B789011
theorem B5343083 : Blo 307833 5343083 := bstep (se 1 (by rfl) ⟨4007312, by rfl⟩ : syracuseStep 5343083 = 8014625) B8014625
theorem B886727 : Blo 307833 886727 := bstep (se 1 (by rfl) ⟨665045, by rfl⟩ : syracuseStep 886727 = 1330091) B1330091
theorem B1050569 : Blo 307833 1050569 := bstep (se 2 (by rfl) ⟨393963, by rfl⟩ : syracuseStep 1050569 = 787927) B787927
theorem B1574963 : Blo 307833 1574963 := bstep (se 1 (by rfl) ⟨1181222, by rfl⟩ : syracuseStep 1574963 = 2362445) B2362445
theorem B952445 : Blo 307833 952445 := bstep (se 3 (by rfl) ⟨178583, by rfl⟩ : syracuseStep 952445 = 357167) B357167
theorem B886909 : Blo 307833 886909 := bstep (se 3 (by rfl) ⟨166295, by rfl⟩ : syracuseStep 886909 = 332591) B332591
theorem B1050839 : Blo 307833 1050839 := bstep (se 1 (by rfl) ⟨788129, by rfl⟩ : syracuseStep 1050839 = 1576259) B1576259
theorem B1051163 : Blo 307833 1051163 := bstep (se 1 (by rfl) ⟨788372, by rfl⟩ : syracuseStep 1051163 = 1576745) B1576745
theorem B1772063 : Blo 307833 1772063 := bstep (se 1 (by rfl) ⟨1329047, by rfl⟩ : syracuseStep 1772063 = 2658095) B2658095
theorem B1575611 : Blo 307833 1575611 := bstep (se 1 (by rfl) ⟨1181708, by rfl⟩ : syracuseStep 1575611 = 2363417) B2363417
theorem B7539479 : Blo 307833 7539479 := bstep (se 1 (by rfl) ⟨5654609, by rfl⟩ : syracuseStep 7539479 = 11309219) B11309219
theorem B1117147 : Blo 307833 1117147 := bstep (se 1 (by rfl) ⟨837860, by rfl⟩ : syracuseStep 1117147 = 1675721) B1675721
theorem B461945 : Blo 307833 461945 := bstep (se 2 (by rfl) ⟨173229, by rfl⟩ : syracuseStep 461945 = 346459) B346459
theorem B462047 : Blo 307833 462047 := bstep (se 1 (by rfl) ⟨346535, by rfl⟩ : syracuseStep 462047 = 693071) B693071
theorem B462089 : Blo 307833 462089 := bstep (se 2 (by rfl) ⟨173283, by rfl⟩ : syracuseStep 462089 = 346567) B346567
theorem B462191 : Blo 307833 462191 := bstep (se 1 (by rfl) ⟨346643, by rfl⟩ : syracuseStep 462191 = 693287) B693287
theorem B1052027 : Blo 307833 1052027 := bstep (se 1 (by rfl) ⟨789020, by rfl⟩ : syracuseStep 1052027 = 1578041) B1578041
theorem B2526653 : Blo 307833 2526653 := bstep (se 3 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 2526653 = 947495) B947495
theorem B462311 : Blo 307833 462311 := bstep (se 1 (by rfl) ⟨346733, by rfl⟩ : syracuseStep 462311 = 693467) B693467
theorem B3182075 : Blo 307833 3182075 := bstep (se 1 (by rfl) ⟨2386556, by rfl⟩ : syracuseStep 3182075 = 4773113) B4773113
theorem B462443 : Blo 307833 462443 := bstep (se 1 (by rfl) ⟨346832, by rfl⟩ : syracuseStep 462443 = 693665) B693665
theorem B1576583 : Blo 307833 1576583 := bstep (se 1 (by rfl) ⟨1182437, by rfl⟩ : syracuseStep 1576583 = 2364875) B2364875
theorem B528047 : Blo 307833 528047 := bstep (se 1 (by rfl) ⟨396035, by rfl⟩ : syracuseStep 528047 = 792071) B792071
theorem B462569 : Blo 307833 462569 := bstep (se 2 (by rfl) ⟨173463, by rfl⟩ : syracuseStep 462569 = 346927) B346927
theorem B462713 : Blo 307833 462713 := bstep (se 2 (by rfl) ⟨173517, by rfl⟩ : syracuseStep 462713 = 347035) B347035
theorem B561017 : Blo 307833 561017 := bstep (se 2 (by rfl) ⟨210381, by rfl⟩ : syracuseStep 561017 = 420763) B420763
theorem B462815 : Blo 307833 462815 := bstep (se 1 (by rfl) ⟨347111, by rfl⟩ : syracuseStep 462815 = 694223) B694223
theorem B463067 : Blo 307833 463067 := bstep (se 1 (by rfl) ⟨347300, by rfl⟩ : syracuseStep 463067 = 694601) B694601
theorem B463079 : Blo 307833 463079 := bstep (se 1 (by rfl) ⟨347309, by rfl⟩ : syracuseStep 463079 = 694619) B694619
theorem B463241 : Blo 307833 463241 := bstep (se 2 (by rfl) ⟨173715, by rfl⟩ : syracuseStep 463241 = 347431) B347431
theorem B889255 : Blo 307833 889255 := bstep (se 1 (by rfl) ⟨666941, by rfl⟩ : syracuseStep 889255 = 1333883) B1333883
theorem B463337 : Blo 307833 463337 := bstep (se 2 (by rfl) ⟨173751, by rfl⟩ : syracuseStep 463337 = 347503) B347503
theorem B692729 : Blo 307833 692729 := bstep (se 2 (by rfl) ⟨259773, by rfl⟩ : syracuseStep 692729 = 519547) B519547
theorem B6689303 : Blo 307833 6689303 := bstep (se 1 (by rfl) ⟨5016977, by rfl⟩ : syracuseStep 6689303 = 10033955) B10033955
theorem B3510863 : Blo 307833 3510863 := bstep (se 1 (by rfl) ⟨2633147, by rfl⟩ : syracuseStep 3510863 = 5266295) B5266295
theorem B987727 : Blo 307833 987727 := bstep (se 1 (by rfl) ⟨740795, by rfl⟩ : syracuseStep 987727 = 1481591) B1481591
theorem B692819 : Blo 307833 692819 := bstep (se 1 (by rfl) ⟨519614, by rfl⟩ : syracuseStep 692819 = 1039229) B1039229
theorem B463463 : Blo 307833 463463 := bstep (se 1 (by rfl) ⟨347597, by rfl⟩ : syracuseStep 463463 = 695195) B695195
theorem B463595 : Blo 307833 463595 := bstep (se 1 (by rfl) ⟨347696, by rfl⟩ : syracuseStep 463595 = 695393) B695393
theorem B692999 : Blo 307833 692999 := bstep (se 1 (by rfl) ⟨519749, by rfl⟩ : syracuseStep 692999 = 1039499) B1039499
theorem B463625 : Blo 307833 463625 := bstep (se 2 (by rfl) ⟨173859, by rfl⟩ : syracuseStep 463625 = 347719) B347719
theorem B463727 : Blo 307833 463727 := bstep (se 1 (by rfl) ⟨347795, by rfl⟩ : syracuseStep 463727 = 695591) B695591
theorem B463979 : Blo 307833 463979 := bstep (se 1 (by rfl) ⟨347984, by rfl⟩ : syracuseStep 463979 = 695969) B695969
theorem B1578203 : Blo 307833 1578203 := bstep (se 1 (by rfl) ⟨1183652, by rfl⟩ : syracuseStep 1578203 = 2367305) B2367305
theorem B464219 : Blo 307833 464219 := bstep (se 1 (by rfl) ⟨348164, by rfl⟩ : syracuseStep 464219 = 696329) B696329
theorem B464495 : Blo 307833 464495 := bstep (se 1 (by rfl) ⟨348371, by rfl⟩ : syracuseStep 464495 = 696743) B696743
theorem B464567 : Blo 307833 464567 := bstep (se 1 (by rfl) ⟨348425, by rfl⟩ : syracuseStep 464567 = 696851) B696851
theorem B464603 : Blo 307833 464603 := bstep (se 1 (by rfl) ⟨348452, by rfl⟩ : syracuseStep 464603 = 696905) B696905
theorem B694079 : Blo 307833 694079 := bstep (se 1 (by rfl) ⟨520559, by rfl⟩ : syracuseStep 694079 = 1041119) B1041119
theorem B464777 : Blo 307833 464777 := bstep (se 2 (by rfl) ⟨174291, by rfl⟩ : syracuseStep 464777 = 348583) B348583
theorem B3971045 : Blo 307833 3971045 := bstep (se 4 (by rfl) ⟨372285, by rfl⟩ : syracuseStep 3971045 = 744571) B744571
theorem B464879 : Blo 307833 464879 := bstep (se 1 (by rfl) ⟨348659, by rfl⟩ : syracuseStep 464879 = 697319) B697319
theorem B497657 : Blo 307833 497657 := bstep (se 2 (by rfl) ⟨186621, by rfl⟩ : syracuseStep 497657 = 373243) B373243
theorem B595961 : Blo 307833 595961 := bstep (se 2 (by rfl) ⟨223485, by rfl⟩ : syracuseStep 595961 = 446971) B446971
theorem B694367 : Blo 307833 694367 := bstep (se 1 (by rfl) ⟨520775, by rfl⟩ : syracuseStep 694367 = 1041551) B1041551
theorem B1317019 : Blo 307833 1317019 := bstep (se 1 (by rfl) ⟨987764, by rfl⟩ : syracuseStep 1317019 = 1975529) B1975529
theorem B432283 : Blo 307833 432283 := bstep (se 1 (by rfl) ⟨324212, by rfl⟩ : syracuseStep 432283 = 648425) B648425
theorem B465131 : Blo 307833 465131 := bstep (se 1 (by rfl) ⟨348848, by rfl⟩ : syracuseStep 465131 = 697697) B697697
theorem B465191 : Blo 307833 465191 := bstep (se 1 (by rfl) ⟨348893, by rfl⟩ : syracuseStep 465191 = 697787) B697787
theorem B465275 : Blo 307833 465275 := bstep (se 1 (by rfl) ⟨348956, by rfl⟩ : syracuseStep 465275 = 697913) B697913
theorem B465545 : Blo 307833 465545 := bstep (se 2 (by rfl) ⟨174579, by rfl⟩ : syracuseStep 465545 = 349159) B349159
theorem B465719 : Blo 307833 465719 := bstep (se 1 (by rfl) ⟨349289, by rfl⟩ : syracuseStep 465719 = 698579) B698579
theorem B695123 : Blo 307833 695123 := bstep (se 1 (by rfl) ⟨521342, by rfl⟩ : syracuseStep 695123 = 1042685) B1042685
theorem B465755 : Blo 307833 465755 := bstep (se 1 (by rfl) ⟨349316, by rfl⟩ : syracuseStep 465755 = 698633) B698633
theorem B2366333 : Blo 307833 2366333 := bstep (se 3 (by rfl) ⟨443687, by rfl⟩ : syracuseStep 2366333 = 887375) B887375
theorem B465899 : Blo 307833 465899 := bstep (se 1 (by rfl) ⟨349424, by rfl⟩ : syracuseStep 465899 = 698849) B698849
theorem B1055873 : Blo 307833 1055873 := bstep (se 2 (by rfl) ⟨395952, by rfl⟩ : syracuseStep 1055873 = 791905) B791905
theorem B466103 : Blo 307833 466103 := bstep (se 1 (by rfl) ⟨349577, by rfl⟩ : syracuseStep 466103 = 699155) B699155
theorem B695663 : Blo 307833 695663 := bstep (se 1 (by rfl) ⟨521747, by rfl⟩ : syracuseStep 695663 = 1043495) B1043495
theorem B466343 : Blo 307833 466343 := bstep (se 1 (by rfl) ⟨349757, by rfl⟩ : syracuseStep 466343 = 699515) B699515
theorem B662995 : Blo 307833 662995 := bstep (se 1 (by rfl) ⟨497246, by rfl⟩ : syracuseStep 662995 = 994493) B994493
theorem B466427 : Blo 307833 466427 := bstep (se 1 (by rfl) ⟨349820, by rfl⟩ : syracuseStep 466427 = 699641) B699641
theorem B466523 : Blo 307833 466523 := bstep (se 1 (by rfl) ⟨349892, by rfl⟩ : syracuseStep 466523 = 699785) B699785
theorem B695951 : Blo 307833 695951 := bstep (se 1 (by rfl) ⟨521963, by rfl⟩ : syracuseStep 695951 = 1043927) B1043927
theorem B466607 : Blo 307833 466607 := bstep (se 1 (by rfl) ⟨349955, by rfl⟩ : syracuseStep 466607 = 699911) B699911
theorem B696041 : Blo 307833 696041 := bstep (se 2 (by rfl) ⟨261015, by rfl⟩ : syracuseStep 696041 = 522031) B522031
theorem B466727 : Blo 307833 466727 := bstep (se 1 (by rfl) ⟨350045, by rfl⟩ : syracuseStep 466727 = 700091) B700091
theorem B466811 : Blo 307833 466811 := bstep (se 1 (by rfl) ⟨350108, by rfl⟩ : syracuseStep 466811 = 700217) B700217
theorem B597931 : Blo 307833 597931 := bstep (se 1 (by rfl) ⟨448448, by rfl⟩ : syracuseStep 597931 = 896897) B896897
theorem B467231 : Blo 307833 467231 := bstep (se 1 (by rfl) ⟨350423, by rfl⟩ : syracuseStep 467231 = 700847) B700847
theorem B467255 : Blo 307833 467255 := bstep (se 1 (by rfl) ⟨350441, by rfl⟩ : syracuseStep 467255 = 700883) B700883
theorem B467327 : Blo 307833 467327 := bstep (se 1 (by rfl) ⟨350495, by rfl⟩ : syracuseStep 467327 = 700991) B700991
theorem B467399 : Blo 307833 467399 := bstep (se 1 (by rfl) ⟨350549, by rfl⟩ : syracuseStep 467399 = 701099) B701099
theorem B697067 : Blo 307833 697067 := bstep (se 1 (by rfl) ⟨522800, by rfl⟩ : syracuseStep 697067 = 1045601) B1045601
theorem B7938809 : Blo 307833 7938809 := bstep (se 2 (by rfl) ⟨2977053, by rfl⟩ : syracuseStep 7938809 = 5954107) B5954107
theorem B2106491 : Blo 307833 2106491 := bstep (se 1 (by rfl) ⟨1579868, by rfl⟩ : syracuseStep 2106491 = 3159737) B3159737
theorem B665003 : Blo 307833 665003 := bstep (se 1 (by rfl) ⟨498752, by rfl⟩ : syracuseStep 665003 = 997505) B997505
theorem B697967 : Blo 307833 697967 := bstep (se 1 (by rfl) ⟨523475, by rfl⟩ : syracuseStep 697967 = 1046951) B1046951
theorem B698075 : Blo 307833 698075 := bstep (se 1 (by rfl) ⟨523556, by rfl⟩ : syracuseStep 698075 = 1047113) B1047113
theorem B1321069 : Blo 307833 1321069 := bstep (se 3 (by rfl) ⟨247700, by rfl⟩ : syracuseStep 1321069 = 495401) B495401
theorem B2500733 : Blo 307833 2500733 := bstep (se 3 (by rfl) ⟨468887, by rfl⟩ : syracuseStep 2500733 = 937775) B937775
theorem B1321085 : Blo 307833 1321085 := bstep (se 3 (by rfl) ⟨247703, by rfl⟩ : syracuseStep 1321085 = 495407) B495407
theorem B12003713 : Blo 307833 12003713 := bstep (se 2 (by rfl) ⟨4501392, by rfl⟩ : syracuseStep 12003713 = 9002785) B9002785
theorem B699191 : Blo 307833 699191 := bstep (se 1 (by rfl) ⟨524393, by rfl⟩ : syracuseStep 699191 = 1048787) B1048787
theorem B699371 : Blo 307833 699371 := bstep (se 1 (by rfl) ⟨524528, by rfl⟩ : syracuseStep 699371 = 1049057) B1049057
theorem B994351 : Blo 307833 994351 := bstep (se 1 (by rfl) ⟨745763, by rfl⟩ : syracuseStep 994351 = 1491527) B1491527
theorem B6827123 : Blo 307833 6827123 := bstep (se 1 (by rfl) ⟨5120342, by rfl⟩ : syracuseStep 6827123 = 10240685) B10240685
theorem B470591 : Blo 307833 470591 := bstep (se 1 (by rfl) ⟨352943, by rfl⟩ : syracuseStep 470591 = 705887) B705887
theorem B700199 : Blo 307833 700199 := bstep (se 1 (by rfl) ⟨525149, by rfl⟩ : syracuseStep 700199 = 1050299) B1050299
theorem B1880273 : Blo 307833 1880273 := bstep (se 2 (by rfl) ⟨705102, by rfl⟩ : syracuseStep 1880273 = 1410205) B1410205
theorem B995581 : Blo 307833 995581 := bstep (se 3 (by rfl) ⟨186671, by rfl⟩ : syracuseStep 995581 = 373343) B373343
theorem B1782071 : Blo 307833 1782071 := bstep (se 1 (by rfl) ⟨1336553, by rfl⟩ : syracuseStep 1782071 = 2673107) B2673107
theorem B15151535 : Blo 307833 15151535 := bstep (se 1 (by rfl) ⟨11363651, by rfl⟩ : syracuseStep 15151535 = 22727303) B22727303
theorem B3978017 : Blo 307833 3978017 := bstep (se 2 (by rfl) ⟨1491756, by rfl⟩ : syracuseStep 3978017 = 2983513) B2983513
theorem B701225 : Blo 307833 701225 := bstep (se 2 (by rfl) ⟨262959, by rfl⟩ : syracuseStep 701225 = 525919) B525919
theorem B5485391 : Blo 307833 5485391 := bstep (se 1 (by rfl) ⟨4114043, by rfl⟩ : syracuseStep 5485391 = 8228087) B8228087
theorem B308079 : Blo 307833 308079 := bstep (se 1 (by rfl) ⟨231059, by rfl⟩ : syracuseStep 308079 = 462119) B462119
theorem B308135 : Blo 307833 308135 := bstep (se 1 (by rfl) ⟨231101, by rfl⟩ : syracuseStep 308135 = 462203) B462203
theorem B308219 : Blo 307833 308219 := bstep (se 1 (by rfl) ⟨231164, by rfl⟩ : syracuseStep 308219 = 462329) B462329
theorem B439291 : Blo 307833 439291 := bstep (se 1 (by rfl) ⟨329468, by rfl⟩ : syracuseStep 439291 = 658937) B658937
theorem B701495 : Blo 307833 701495 := bstep (se 1 (by rfl) ⟨526121, by rfl⟩ : syracuseStep 701495 = 1052243) B1052243
theorem B308287 : Blo 307833 308287 := bstep (se 1 (by rfl) ⟨231215, by rfl⟩ : syracuseStep 308287 = 462431) B462431
theorem B701513 : Blo 307833 701513 := bstep (se 2 (by rfl) ⟨263067, by rfl⟩ : syracuseStep 701513 = 526135) B526135
theorem B308431 : Blo 307833 308431 := bstep (se 1 (by rfl) ⟨231323, by rfl⟩ : syracuseStep 308431 = 462647) B462647
theorem B308635 : Blo 307833 308635 := bstep (se 1 (by rfl) ⟨231476, by rfl⟩ : syracuseStep 308635 = 462953) B462953
theorem B308847 : Blo 307833 308847 := bstep (se 1 (by rfl) ⟨231635, by rfl⟩ : syracuseStep 308847 = 463271) B463271
theorem B1783453 : Blo 307833 1783453 := bstep (se 3 (by rfl) ⟨334397, by rfl⟩ : syracuseStep 1783453 = 668795) B668795
theorem B308903 : Blo 307833 308903 := bstep (se 1 (by rfl) ⟨231677, by rfl⟩ : syracuseStep 308903 = 463355) B463355
theorem B308987 : Blo 307833 308987 := bstep (se 1 (by rfl) ⟨231740, by rfl⟩ : syracuseStep 308987 = 463481) B463481
theorem B309023 : Blo 307833 309023 := bstep (se 1 (by rfl) ⟨231767, by rfl⟩ : syracuseStep 309023 = 463535) B463535
theorem B309055 : Blo 307833 309055 := bstep (se 1 (by rfl) ⟨231791, by rfl⟩ : syracuseStep 309055 = 463583) B463583
theorem B309231 : Blo 307833 309231 := bstep (se 1 (by rfl) ⟨231923, by rfl⟩ : syracuseStep 309231 = 463847) B463847
theorem B309403 : Blo 307833 309403 := bstep (se 1 (by rfl) ⟨232052, by rfl⟩ : syracuseStep 309403 = 464105) B464105
theorem B1489067 : Blo 307833 1489067 := bstep (se 1 (by rfl) ⟨1116800, by rfl⟩ : syracuseStep 1489067 = 2233601) B2233601
theorem B309439 : Blo 307833 309439 := bstep (se 1 (by rfl) ⟨232079, by rfl⟩ : syracuseStep 309439 = 464159) B464159
theorem B309551 : Blo 307833 309551 := bstep (se 1 (by rfl) ⟨232163, by rfl⟩ : syracuseStep 309551 = 464327) B464327
theorem B309787 : Blo 307833 309787 := bstep (se 1 (by rfl) ⟨232340, by rfl⟩ : syracuseStep 309787 = 464681) B464681
theorem B309791 : Blo 307833 309791 := bstep (se 1 (by rfl) ⟨232343, by rfl⟩ : syracuseStep 309791 = 464687) B464687
theorem B1325767 : Blo 307833 1325767 := bstep (se 1 (by rfl) ⟨994325, by rfl⟩ : syracuseStep 1325767 = 1988651) B1988651
theorem B310107 : Blo 307833 310107 := bstep (se 1 (by rfl) ⟨232580, by rfl⟩ : syracuseStep 310107 = 465161) B465161
theorem B310175 : Blo 307833 310175 := bstep (se 1 (by rfl) ⟨232631, by rfl⟩ : syracuseStep 310175 = 465263) B465263
theorem B834529 : Blo 307833 834529 := bstep (se 2 (by rfl) ⟨312948, by rfl⟩ : syracuseStep 834529 = 625897) B625897
theorem B310319 : Blo 307833 310319 := bstep (se 1 (by rfl) ⟨232739, by rfl⟩ : syracuseStep 310319 = 465479) B465479
theorem B310343 : Blo 307833 310343 := bstep (se 1 (by rfl) ⟨232757, by rfl⟩ : syracuseStep 310343 = 465515) B465515
theorem B1064083 : Blo 307833 1064083 := bstep (se 1 (by rfl) ⟨798062, by rfl⟩ : syracuseStep 1064083 = 1596125) B1596125
theorem B310495 : Blo 307833 310495 := bstep (se 1 (by rfl) ⟨232871, by rfl⟩ : syracuseStep 310495 = 465743) B465743
theorem B441769 : Blo 307833 441769 := bstep (se 2 (by rfl) ⟨165663, by rfl⟩ : syracuseStep 441769 = 331327) B331327
theorem B310759 : Blo 307833 310759 := bstep (se 1 (by rfl) ⟨233069, by rfl⟩ : syracuseStep 310759 = 466139) B466139
theorem B310875 : Blo 307833 310875 := bstep (se 1 (by rfl) ⟨233156, by rfl⟩ : syracuseStep 310875 = 466313) B466313
theorem B311111 : Blo 307833 311111 := bstep (se 1 (by rfl) ⟨233333, by rfl⟩ : syracuseStep 311111 = 466667) B466667
theorem B311263 : Blo 307833 311263 := bstep (se 1 (by rfl) ⟨233447, by rfl⟩ : syracuseStep 311263 = 466895) B466895
theorem B1130635 : Blo 307833 1130635 := bstep (se 1 (by rfl) ⟨847976, by rfl⟩ : syracuseStep 1130635 = 1695953) B1695953
theorem B311527 : Blo 307833 311527 := bstep (se 1 (by rfl) ⟨233645, by rfl⟩ : syracuseStep 311527 = 467291) B467291
theorem B311679 : Blo 307833 311679 := bstep (se 1 (by rfl) ⟨233759, by rfl⟩ : syracuseStep 311679 = 467519) B467519
theorem B311759 : Blo 307833 311759 := bstep (se 1 (by rfl) ⟨233819, by rfl⟩ : syracuseStep 311759 = 467639) B467639
theorem B1885331 : Blo 307833 1885331 := bstep (se 1 (by rfl) ⟨1413998, by rfl⟩ : syracuseStep 1885331 = 2827997) B2827997
theorem B7161331 : Blo 307833 7161331 := bstep (se 1 (by rfl) ⟨5370998, by rfl⟩ : syracuseStep 7161331 = 10741997) B10741997
theorem B20072285 : Blo 307833 20072285 := bstep (se 3 (by rfl) ⟨3763553, by rfl⟩ : syracuseStep 20072285 = 7527107) B7527107
theorem B7161871 : Blo 307833 7161871 := bstep (se 1 (by rfl) ⟨5371403, by rfl⟩ : syracuseStep 7161871 = 10742807) B10742807
theorem B414566423 : Blo 307833 414566423 := bstep (se 1 (by rfl) ⟨310924817, by rfl⟩ : syracuseStep 414566423 = 621849635) B621849635
theorem B1558763 : Blo 307833 1558763 := bstep (se 1 (by rfl) ⟨1169072, by rfl⟩ : syracuseStep 1558763 = 2338145) B2338145
theorem B4245821 : Blo 307833 4245821 := bstep (se 3 (by rfl) ⟨796091, by rfl⟩ : syracuseStep 4245821 = 1592183) B1592183
theorem B1755593 : Blo 307833 1755593 := bstep (se 2 (by rfl) ⟨658347, by rfl⟩ : syracuseStep 1755593 = 1316695) B1316695
theorem B10242541 : Blo 307833 10242541 := bstep (se 3 (by rfl) ⟨1920476, by rfl⟩ : syracuseStep 10242541 = 3840953) B3840953
theorem B5327531 : Blo 307833 5327531 := bstep (se 1 (by rfl) ⟨3995648, by rfl⟩ : syracuseStep 5327531 = 7991297) B7991297
theorem B2640599 : Blo 307833 2640599 := bstep (se 1 (by rfl) ⟨1980449, by rfl⟩ : syracuseStep 2640599 = 3960899) B3960899
theorem B347359 : Blo 307833 347359 := bstep (se 1 (by rfl) ⟨260519, by rfl⟩ : syracuseStep 347359 = 521039) B521039
theorem B3591607 : Blo 307833 3591607 := bstep (se 1 (by rfl) ⟨2693705, by rfl⟩ : syracuseStep 3591607 = 5387411) B5387411
theorem B1560059 : Blo 307833 1560059 := bstep (se 1 (by rfl) ⟨1170044, by rfl⟩ : syracuseStep 1560059 = 2340089) B2340089
theorem B1560221 : Blo 307833 1560221 := bstep (se 3 (by rfl) ⟨292541, by rfl⟩ : syracuseStep 1560221 = 585083) B585083
theorem B741881 : Blo 307833 741881 := bstep (se 2 (by rfl) ⟨278205, by rfl⟩ : syracuseStep 741881 = 556411) B556411
theorem B1331815 : Blo 307833 1331815 := bstep (se 1 (by rfl) ⟨998861, by rfl⟩ : syracuseStep 1331815 = 1997723) B1997723
theorem B1594811 : Blo 307833 1594811 := bstep (se 1 (by rfl) ⟨1196108, by rfl⟩ : syracuseStep 1594811 = 2392217) B2392217
theorem B349807 : Blo 307833 349807 := bstep (se 1 (by rfl) ⟨262355, by rfl⟩ : syracuseStep 349807 = 524711) B524711
theorem B349915 : Blo 307833 349915 := bstep (se 1 (by rfl) ⟨262436, by rfl⟩ : syracuseStep 349915 = 524873) B524873
theorem B1988803 : Blo 307833 1988803 := bstep (se 1 (by rfl) ⟨1491602, by rfl⟩ : syracuseStep 1988803 = 2983205) B2983205
theorem B2644973 : Blo 307833 2644973 := bstep (se 3 (by rfl) ⟨495932, by rfl⟩ : syracuseStep 2644973 = 991865) B991865
theorem B1989623 : Blo 307833 1989623 := bstep (se 1 (by rfl) ⟨1492217, by rfl⟩ : syracuseStep 1989623 = 2984435) B2984435
theorem B744871 : Blo 307833 744871 := bstep (se 1 (by rfl) ⟨558653, by rfl⟩ : syracuseStep 744871 = 1117307) B1117307
theorem B4087741 : Blo 307833 4087741 := bstep (se 3 (by rfl) ⟨766451, by rfl⟩ : syracuseStep 4087741 = 1532903) B1532903
theorem B1040417 : Blo 307833 1040417 := bstep (se 2 (by rfl) ⟨390156, by rfl⟩ : syracuseStep 1040417 = 780313) B780313
theorem B1564919 : Blo 307833 1564919 := bstep (se 1 (by rfl) ⟨1173689, by rfl⟩ : syracuseStep 1564919 = 2347379) B2347379
theorem B3563939 : Blo 307833 3563939 := bstep (se 1 (by rfl) ⟨2672954, by rfl⟩ : syracuseStep 3563939 = 5345909) B5345909
theorem B10084925 : Blo 307833 10084925 := bstep (se 3 (by rfl) ⟨1890923, by rfl⟩ : syracuseStep 10084925 = 3781847) B3781847
theorem B1729133 : Blo 307833 1729133 := bstep (se 3 (by rfl) ⟨324212, by rfl⟩ : syracuseStep 1729133 = 648425) B648425
theorem B2220797 : Blo 307833 2220797 := bstep (se 3 (by rfl) ⟨416399, by rfl⟩ : syracuseStep 2220797 = 832799) B832799
theorem B3957923 : Blo 307833 3957923 := bstep (se 1 (by rfl) ⟨2968442, by rfl⟩ : syracuseStep 3957923 = 5936885) B5936885
theorem B1697273 : Blo 307833 1697273 := bstep (se 2 (by rfl) ⟨636477, by rfl⟩ : syracuseStep 1697273 = 1272955) B1272955
theorem B2975291 : Blo 307833 2975291 := bstep (se 1 (by rfl) ⟨2231468, by rfl⟩ : syracuseStep 2975291 = 4462937) B4462937
theorem B1173113 : Blo 307833 1173113 := bstep (se 2 (by rfl) ⟨439917, by rfl⟩ : syracuseStep 1173113 = 879835) B879835
theorem B1009313 : Blo 307833 1009313 := bstep (se 2 (by rfl) ⟨378492, by rfl⟩ : syracuseStep 1009313 = 756985) B756985
theorem B878377 : Blo 307833 878377 := bstep (se 2 (by rfl) ⟨329391, by rfl⟩ : syracuseStep 878377 = 658783) B658783
theorem B34498457 : Blo 307833 34498457 := bstep (se 2 (by rfl) ⟨12936921, by rfl⟩ : syracuseStep 34498457 = 25873843) B25873843
theorem B1173629 : Blo 307833 1173629 := bstep (se 3 (by rfl) ⟨220055, by rfl⟩ : syracuseStep 1173629 = 440111) B440111
theorem B3992165 : Blo 307833 3992165 := bstep (se 4 (by rfl) ⟨374265, by rfl⟩ : syracuseStep 3992165 = 748531) B748531
theorem B1764089 : Blo 307833 1764089 := bstep (se 2 (by rfl) ⟨661533, by rfl⟩ : syracuseStep 1764089 = 1323067) B1323067
theorem B9988919 : Blo 307833 9988919 := bstep (se 1 (by rfl) ⟨7491689, by rfl⟩ : syracuseStep 9988919 = 14983379) B14983379
theorem B2354183 : Blo 307833 2354183 := bstep (se 1 (by rfl) ⟨1765637, by rfl⟩ : syracuseStep 2354183 = 3531275) B3531275
theorem B6679691 : Blo 307833 6679691 := bstep (se 1 (by rfl) ⟨5009768, by rfl⟩ : syracuseStep 6679691 = 10019537) B10019537
theorem B11234483 : Blo 307833 11234483 := bstep (se 1 (by rfl) ⟨8425862, by rfl⟩ : syracuseStep 11234483 = 16851725) B16851725
theorem B781751 : Blo 307833 781751 := bstep (se 1 (by rfl) ⟨586313, by rfl⟩ : syracuseStep 781751 = 1172627) B1172627
theorem B519655 : Blo 307833 519655 := bstep (se 1 (by rfl) ⟨389741, by rfl⟩ : syracuseStep 519655 = 779483) B779483
theorem B519743 : Blo 307833 519743 := bstep (se 1 (by rfl) ⟨389807, by rfl⟩ : syracuseStep 519743 = 779615) B779615
theorem B1044143 : Blo 307833 1044143 := bstep (se 1 (by rfl) ⟨783107, by rfl⟩ : syracuseStep 1044143 = 1566215) B1566215
theorem B7925687 : Blo 307833 7925687 := bstep (se 1 (by rfl) ⟨5944265, by rfl⟩ : syracuseStep 7925687 = 11888531) B11888531
theorem B1044467 : Blo 307833 1044467 := bstep (se 1 (by rfl) ⟨783350, by rfl⟩ : syracuseStep 1044467 = 1566701) B1566701
theorem B880769 : Blo 307833 880769 := bstep (se 2 (by rfl) ⟨330288, by rfl⟩ : syracuseStep 880769 = 660577) B660577
theorem B1175741 : Blo 307833 1175741 := bstep (se 3 (by rfl) ⟨220451, by rfl⟩ : syracuseStep 1175741 = 440903) B440903
theorem B520411 : Blo 307833 520411 := bstep (se 1 (by rfl) ⟨390308, by rfl⟩ : syracuseStep 520411 = 780617) B780617
theorem B880951 : Blo 307833 880951 := bstep (se 1 (by rfl) ⟨660713, by rfl⟩ : syracuseStep 880951 = 1321427) B1321427
theorem B1044791 : Blo 307833 1044791 := bstep (se 1 (by rfl) ⟨783593, by rfl⟩ : syracuseStep 1044791 = 1567187) B1567187
theorem B1765799 : Blo 307833 1765799 := bstep (se 1 (by rfl) ⟨1324349, by rfl⟩ : syracuseStep 1765799 = 2648699) B2648699
theorem B881111 : Blo 307833 881111 := bstep (se 1 (by rfl) ⟨660833, by rfl⟩ : syracuseStep 881111 = 1321667) B1321667
theorem B520681 : Blo 307833 520681 := bstep (se 2 (by rfl) ⟨195255, by rfl⟩ : syracuseStep 520681 = 390511) B390511
theorem B1045007 : Blo 307833 1045007 := bstep (se 1 (by rfl) ⟨783755, by rfl⟩ : syracuseStep 1045007 = 1567511) B1567511
theorem B3830689 : Blo 307833 3830689 := bstep (se 2 (by rfl) ⟨1436508, by rfl⟩ : syracuseStep 3830689 = 2873017) B2873017
theorem B587027 : Blo 307833 587027 := bstep (se 1 (by rfl) ⟨440270, by rfl⟩ : syracuseStep 587027 = 880541) B880541
theorem B6387133 : Blo 307833 6387133 := bstep (se 3 (by rfl) ⟨1197587, by rfl⟩ : syracuseStep 6387133 = 2395175) B2395175
theorem B1177031 : Blo 307833 1177031 := bstep (se 1 (by rfl) ⟨882773, by rfl⟩ : syracuseStep 1177031 = 1765547) B1765547
theorem B1111553 : Blo 307833 1111553 := bstep (se 2 (by rfl) ⟨416832, by rfl⟩ : syracuseStep 1111553 = 833665) B833665
theorem B1046087 : Blo 307833 1046087 := bstep (se 1 (by rfl) ⟨784565, by rfl⟩ : syracuseStep 1046087 = 1569131) B1569131
theorem B521849 : Blo 307833 521849 := bstep (se 2 (by rfl) ⟨195693, by rfl⟩ : syracuseStep 521849 = 391387) B391387
theorem B1996649 : Blo 307833 1996649 := bstep (se 2 (by rfl) ⟨748743, by rfl⟩ : syracuseStep 1996649 = 1497487) B1497487
theorem B882569 : Blo 307833 882569 := bstep (se 2 (by rfl) ⟨330963, by rfl⟩ : syracuseStep 882569 = 661927) B661927
theorem B784343 : Blo 307833 784343 := bstep (se 1 (by rfl) ⟨588257, by rfl⟩ : syracuseStep 784343 = 1176515) B1176515
theorem B1898579 : Blo 307833 1898579 := bstep (se 1 (by rfl) ⟨1423934, by rfl⟩ : syracuseStep 1898579 = 2847869) B2847869
theorem B522335 : Blo 307833 522335 := bstep (se 1 (by rfl) ⟨391751, by rfl⟩ : syracuseStep 522335 = 783503) B783503
theorem B1570913 : Blo 307833 1570913 := bstep (se 2 (by rfl) ⟨589092, by rfl⟩ : syracuseStep 1570913 = 1178185) B1178185
theorem B1571075 : Blo 307833 1571075 := bstep (se 1 (by rfl) ⟨1178306, by rfl⟩ : syracuseStep 1571075 = 2356613) B2356613
theorem B1047059 : Blo 307833 1047059 := bstep (se 1 (by rfl) ⟨785294, by rfl⟩ : syracuseStep 1047059 = 1570589) B1570589
theorem B391711 : Blo 307833 391711 := bstep (se 1 (by rfl) ⟨293783, by rfl⟩ : syracuseStep 391711 = 587567) B587567
theorem B948893 : Blo 307833 948893 := bstep (se 3 (by rfl) ⟨177917, by rfl⟩ : syracuseStep 948893 = 355835) B355835
theorem B3341189 : Blo 307833 3341189 := bstep (se 4 (by rfl) ⟨313236, by rfl⟩ : syracuseStep 3341189 = 626473) B626473
theorem B5340107 : Blo 307833 5340107 := bstep (se 1 (by rfl) ⟨4005080, by rfl⟩ : syracuseStep 5340107 = 8010161) B8010161
theorem B2816977 : Blo 307833 2816977 := bstep (se 2 (by rfl) ⟨1056366, by rfl⟩ : syracuseStep 2816977 = 2112733) B2112733
theorem B1768463 : Blo 307833 1768463 := bstep (se 1 (by rfl) ⟨1326347, by rfl⟩ : syracuseStep 1768463 = 2652695) B2652695
theorem B556079 : Blo 307833 556079 := bstep (se 1 (by rfl) ⟨417059, by rfl⟩ : syracuseStep 556079 = 834119) B834119
theorem B2358557 : Blo 307833 2358557 := bstep (se 3 (by rfl) ⟨442229, by rfl⟩ : syracuseStep 2358557 = 884459) B884459
theorem B523631 : Blo 307833 523631 := bstep (se 1 (by rfl) ⟨392723, by rfl⟩ : syracuseStep 523631 = 785447) B785447
theorem B1179143 : Blo 307833 1179143 := bstep (se 1 (by rfl) ⟨884357, by rfl⟩ : syracuseStep 1179143 = 1768715) B1768715
theorem B523867 : Blo 307833 523867 := bstep (se 1 (by rfl) ⟨392900, by rfl⟩ : syracuseStep 523867 = 785801) B785801
theorem B1769147 : Blo 307833 1769147 := bstep (se 1 (by rfl) ⟨1326860, by rfl⟩ : syracuseStep 1769147 = 2653721) B2653721
theorem B786145 : Blo 307833 786145 := bstep (se 2 (by rfl) ⟨294804, by rfl⟩ : syracuseStep 786145 = 589609) B589609
theorem B524009 : Blo 307833 524009 := bstep (se 2 (by rfl) ⟨196503, by rfl⟩ : syracuseStep 524009 = 393007) B393007
theorem B1572695 : Blo 307833 1572695 := bstep (se 1 (by rfl) ⟨1179521, by rfl⟩ : syracuseStep 1572695 = 2359043) B2359043
theorem B1507513 : Blo 307833 1507513 := bstep (se 2 (by rfl) ⟨565317, by rfl⟩ : syracuseStep 1507513 = 1130635) B1130635
theorem B1049003 : Blo 307833 1049003 := bstep (se 1 (by rfl) ⟨786752, by rfl⟩ : syracuseStep 1049003 = 1573505) B1573505
theorem B5014061 : Blo 307833 5014061 := bstep (se 3 (by rfl) ⟨940136, by rfl⟩ : syracuseStep 5014061 = 1880273) B1880273
theorem B1180615 : Blo 307833 1180615 := bstep (se 1 (by rfl) ⟨885461, by rfl⟩ : syracuseStep 1180615 = 1770923) B1770923
theorem B1049543 : Blo 307833 1049543 := bstep (se 1 (by rfl) ⟨787157, by rfl⟩ : syracuseStep 1049543 = 1574315) B1574315
theorem B1049597 : Blo 307833 1049597 := bstep (se 3 (by rfl) ⟨196799, by rfl⟩ : syracuseStep 1049597 = 393599) B393599
theorem B9503837 : Blo 307833 9503837 := bstep (se 3 (by rfl) ⟨1781969, by rfl⟩ : syracuseStep 9503837 = 3563939) B3563939
theorem B591151 : Blo 307833 591151 := bstep (se 1 (by rfl) ⟨443363, by rfl⟩ : syracuseStep 591151 = 886727) B886727
theorem B1049975 : Blo 307833 1049975 := bstep (se 1 (by rfl) ⟨787481, by rfl⟩ : syracuseStep 1049975 = 1574963) B1574963
theorem B525737 : Blo 307833 525737 := bstep (se 2 (by rfl) ⟨197151, by rfl⟩ : syracuseStep 525737 = 394303) B394303
theorem B1181375 : Blo 307833 1181375 := bstep (se 1 (by rfl) ⟨886031, by rfl⟩ : syracuseStep 1181375 = 1772063) B1772063
theorem B1050407 : Blo 307833 1050407 := bstep (se 1 (by rfl) ⟨787805, by rfl⟩ : syracuseStep 1050407 = 1575611) B1575611
theorem B1050785 : Blo 307833 1050785 := bstep (se 2 (by rfl) ⟨394044, by rfl⟩ : syracuseStep 1050785 = 788089) B788089
theorem B1051055 : Blo 307833 1051055 := bstep (se 1 (by rfl) ⟨788291, by rfl⟩ : syracuseStep 1051055 = 1576583) B1576583
theorem B1182545 : Blo 307833 1182545 := bstep (se 2 (by rfl) ⟨443454, by rfl⟩ : syracuseStep 1182545 = 886909) B886909
theorem B461819 : Blo 307833 461819 := bstep (se 1 (by rfl) ⟨346364, by rfl⟩ : syracuseStep 461819 = 692729) B692729
theorem B494587 : Blo 307833 494587 := bstep (se 1 (by rfl) ⟨370940, by rfl⟩ : syracuseStep 494587 = 741881) B741881
theorem B4459535 : Blo 307833 4459535 := bstep (se 1 (by rfl) ⟨3344651, by rfl⟩ : syracuseStep 4459535 = 6689303) B6689303
theorem B461879 : Blo 307833 461879 := bstep (se 1 (by rfl) ⟨346409, by rfl⟩ : syracuseStep 461879 = 692819) B692819
theorem B461999 : Blo 307833 461999 := bstep (se 1 (by rfl) ⟨346499, by rfl⟩ : syracuseStep 461999 = 692999) B692999
theorem B1052135 : Blo 307833 1052135 := bstep (se 1 (by rfl) ⟨789101, by rfl⟩ : syracuseStep 1052135 = 1578203) B1578203
theorem B462719 : Blo 307833 462719 := bstep (se 1 (by rfl) ⟨347039, by rfl⟩ : syracuseStep 462719 = 694079) B694079
theorem B397307 : Blo 307833 397307 := bstep (se 1 (by rfl) ⟨297980, by rfl⟩ : syracuseStep 397307 = 595961) B595961
theorem B331771 : Blo 307833 331771 := bstep (se 1 (by rfl) ⟨248828, by rfl⟩ : syracuseStep 331771 = 497657) B497657
theorem B462911 : Blo 307833 462911 := bstep (se 1 (by rfl) ⟨347183, by rfl⟩ : syracuseStep 462911 = 694367) B694367
theorem B463145 : Blo 307833 463145 := bstep (se 2 (by rfl) ⟨173679, by rfl⟩ : syracuseStep 463145 = 347359) B347359
theorem B463415 : Blo 307833 463415 := bstep (se 1 (by rfl) ⟨347561, by rfl⟩ : syracuseStep 463415 = 695123) B695123
theorem B4788809 : Blo 307833 4788809 := bstep (se 2 (by rfl) ⟨1795803, by rfl⟩ : syracuseStep 4788809 = 3591607) B3591607
theorem B1577555 : Blo 307833 1577555 := bstep (se 1 (by rfl) ⟨1183166, by rfl⟩ : syracuseStep 1577555 = 2366333) B2366333
theorem B692873 : Blo 307833 692873 := bstep (se 2 (by rfl) ⟨259827, by rfl⟩ : syracuseStep 692873 = 519655) B519655
theorem B463775 : Blo 307833 463775 := bstep (se 1 (by rfl) ⟨347831, by rfl⟩ : syracuseStep 463775 = 695663) B695663
theorem B463967 : Blo 307833 463967 := bstep (se 1 (by rfl) ⟨347975, by rfl⟩ : syracuseStep 463967 = 695951) B695951
theorem B464027 : Blo 307833 464027 := bstep (se 1 (by rfl) ⟨348020, by rfl⟩ : syracuseStep 464027 = 696041) B696041
theorem B693611 : Blo 307833 693611 := bstep (se 1 (by rfl) ⟨520208, by rfl⟩ : syracuseStep 693611 = 1040417) B1040417
theorem B693881 : Blo 307833 693881 := bstep (se 2 (by rfl) ⟨260205, by rfl⟩ : syracuseStep 693881 = 520411) B520411
theorem B6723283 : Blo 307833 6723283 := bstep (se 1 (by rfl) ⟨5042462, by rfl⟩ : syracuseStep 6723283 = 10084925) B10084925
theorem B1152755 : Blo 307833 1152755 := bstep (se 1 (by rfl) ⟨864566, by rfl⟩ : syracuseStep 1152755 = 1729133) B1729133
theorem B464711 : Blo 307833 464711 := bstep (se 1 (by rfl) ⟨348533, by rfl⟩ : syracuseStep 464711 = 697067) B697067
theorem B1480531 : Blo 307833 1480531 := bstep (se 1 (by rfl) ⟨1110398, by rfl⟩ : syracuseStep 1480531 = 2220797) B2220797
theorem B1185673 : Blo 307833 1185673 := bstep (se 2 (by rfl) ⟨444627, by rfl⟩ : syracuseStep 1185673 = 889255) B889255
theorem B694241 : Blo 307833 694241 := bstep (se 2 (by rfl) ⟨260340, by rfl⟩ : syracuseStep 694241 = 520681) B520681
theorem B1316969 : Blo 307833 1316969 := bstep (se 2 (by rfl) ⟨493863, by rfl⟩ : syracuseStep 1316969 = 987727) B987727
theorem B1775753 : Blo 307833 1775753 := bstep (se 2 (by rfl) ⟨665907, by rfl⟩ : syracuseStep 1775753 = 1331815) B1331815
theorem B465311 : Blo 307833 465311 := bstep (se 1 (by rfl) ⟨348983, by rfl⟩ : syracuseStep 465311 = 697967) B697967
theorem B465383 : Blo 307833 465383 := bstep (se 1 (by rfl) ⟨349037, by rfl⟩ : syracuseStep 465383 = 698075) B698075
theorem B8002475 : Blo 307833 8002475 := bstep (se 1 (by rfl) ⟨6001856, by rfl⟩ : syracuseStep 8002475 = 12003713) B12003713
theorem B2661443 : Blo 307833 2661443 := bstep (se 1 (by rfl) ⟨1996082, by rfl⟩ : syracuseStep 2661443 = 3992165) B3992165
theorem B2530381 : Blo 307833 2530381 := bstep (se 3 (by rfl) ⟨474446, by rfl⟩ : syracuseStep 2530381 = 948893) B948893
theorem B6659279 : Blo 307833 6659279 := bstep (se 1 (by rfl) ⟨4994459, by rfl⟩ : syracuseStep 6659279 = 9988919) B9988919
theorem B466127 : Blo 307833 466127 := bstep (se 1 (by rfl) ⟨349595, by rfl⟩ : syracuseStep 466127 = 699191) B699191
theorem B466247 : Blo 307833 466247 := bstep (se 1 (by rfl) ⟨349685, by rfl⟩ : syracuseStep 466247 = 699371) B699371
theorem B466409 : Blo 307833 466409 := bstep (se 2 (by rfl) ⟨174903, by rfl⟩ : syracuseStep 466409 = 349807) B349807
theorem B466553 : Blo 307833 466553 := bstep (se 2 (by rfl) ⟨174957, by rfl⟩ : syracuseStep 466553 = 349915) B349915
theorem B696095 : Blo 307833 696095 := bstep (se 1 (by rfl) ⟨522071, by rfl⟩ : syracuseStep 696095 = 1044143) B1044143
theorem B466799 : Blo 307833 466799 := bstep (se 1 (by rfl) ⟨350099, by rfl⟩ : syracuseStep 466799 = 700199) B700199
theorem B5283791 : Blo 307833 5283791 := bstep (se 1 (by rfl) ⟨3962843, by rfl⟩ : syracuseStep 5283791 = 7925687) B7925687
theorem B696311 : Blo 307833 696311 := bstep (se 1 (by rfl) ⟨522233, by rfl⟩ : syracuseStep 696311 = 1044467) B1044467
theorem B1482877 : Blo 307833 1482877 := bstep (se 3 (by rfl) ⟨278039, by rfl⟩ : syracuseStep 1482877 = 556079) B556079
theorem B1188047 : Blo 307833 1188047 := bstep (se 1 (by rfl) ⟨891035, by rfl⟩ : syracuseStep 1188047 = 1782071) B1782071
theorem B696527 : Blo 307833 696527 := bstep (se 1 (by rfl) ⟨522395, by rfl⟩ : syracuseStep 696527 = 1044791) B1044791
theorem B10101023 : Blo 307833 10101023 := bstep (se 1 (by rfl) ⟨7575767, by rfl⟩ : syracuseStep 10101023 = 15151535) B15151535
theorem B696671 : Blo 307833 696671 := bstep (se 1 (by rfl) ⟨522503, by rfl⟩ : syracuseStep 696671 = 1045007) B1045007
theorem B467483 : Blo 307833 467483 := bstep (se 1 (by rfl) ⟨350612, by rfl⟩ : syracuseStep 467483 = 701225) B701225
theorem B467663 : Blo 307833 467663 := bstep (se 1 (by rfl) ⟨350747, by rfl⟩ : syracuseStep 467663 = 701495) B701495
theorem B467675 : Blo 307833 467675 := bstep (se 1 (by rfl) ⟨350756, by rfl⟩ : syracuseStep 467675 = 701513) B701513
theorem B697391 : Blo 307833 697391 := bstep (se 1 (by rfl) ⟨523043, by rfl⟩ : syracuseStep 697391 = 1046087) B1046087
theorem B992711 : Blo 307833 992711 := bstep (se 1 (by rfl) ⟨744533, by rfl⟩ : syracuseStep 992711 = 1489067) B1489067
theorem B1418777 : Blo 307833 1418777 := bstep (se 2 (by rfl) ⟨532041, by rfl⟩ : syracuseStep 1418777 = 1064083) B1064083
theorem B698039 : Blo 307833 698039 := bstep (se 1 (by rfl) ⟨523529, by rfl⟩ : syracuseStep 698039 = 1047059) B1047059
theorem B993161 : Blo 307833 993161 := bstep (se 2 (by rfl) ⟨372435, by rfl⟩ : syracuseStep 993161 = 744871) B744871
theorem B698489 : Blo 307833 698489 := bstep (se 2 (by rfl) ⟨261933, by rfl⟩ : syracuseStep 698489 = 523867) B523867
theorem B3188965 : Blo 307833 3188965 := bstep (se 4 (by rfl) ⟨298965, by rfl⟩ : syracuseStep 3188965 = 597931) B597931
theorem B5450321 : Blo 307833 5450321 := bstep (se 2 (by rfl) ⟨2043870, by rfl⟩ : syracuseStep 5450321 = 4087741) B4087741
theorem B6007931 : Blo 307833 6007931 := bstep (se 1 (by rfl) ⟨4505948, by rfl⟩ : syracuseStep 6007931 = 9011897) B9011897
theorem B699803 : Blo 307833 699803 := bstep (se 1 (by rfl) ⟨524852, by rfl⟩ : syracuseStep 699803 = 1049705) B1049705
theorem B1256887 : Blo 307833 1256887 := bstep (se 1 (by rfl) ⟨942665, by rfl⟩ : syracuseStep 1256887 = 1885331) B1885331
theorem B13381523 : Blo 307833 13381523 := bstep (se 1 (by rfl) ⟨10036142, by rfl⟩ : syracuseStep 13381523 = 20072285) B20072285
theorem B700379 : Blo 307833 700379 := bstep (se 1 (by rfl) ⟨525284, by rfl⟩ : syracuseStep 700379 = 1050569) B1050569
theorem B276377615 : Blo 307833 276377615 := bstep (se 1 (by rfl) ⟨207283211, by rfl⟩ : syracuseStep 276377615 = 414566423) B414566423
theorem B634963 : Blo 307833 634963 := bstep (se 1 (by rfl) ⟨476222, by rfl⟩ : syracuseStep 634963 = 952445) B952445
theorem B700559 : Blo 307833 700559 := bstep (se 1 (by rfl) ⟨525419, by rfl⟩ : syracuseStep 700559 = 1050839) B1050839
theorem B2830547 : Blo 307833 2830547 := bstep (se 1 (by rfl) ⟨2122910, by rfl⟩ : syracuseStep 2830547 = 4245821) B4245821
theorem B1487069 : Blo 307833 1487069 := bstep (se 3 (by rfl) ⟨278825, by rfl⟩ : syracuseStep 1487069 = 557651) B557651
theorem B700649 : Blo 307833 700649 := bstep (se 2 (by rfl) ⟨262743, by rfl⟩ : syracuseStep 700649 = 525487) B525487
theorem B700775 : Blo 307833 700775 := bstep (se 1 (by rfl) ⟨525581, by rfl⟩ : syracuseStep 700775 = 1051163) B1051163
theorem B3551687 : Blo 307833 3551687 := bstep (se 1 (by rfl) ⟨2663765, by rfl⟩ : syracuseStep 3551687 = 5327531) B5327531
theorem B5026319 : Blo 307833 5026319 := bstep (se 1 (by rfl) ⟨3769739, by rfl⟩ : syracuseStep 5026319 = 7539479) B7539479
theorem B9548441 : Blo 307833 9548441 := bstep (se 2 (by rfl) ⟨3580665, by rfl⟩ : syracuseStep 9548441 = 7161331) B7161331
theorem B307963 : Blo 307833 307963 := bstep (se 1 (by rfl) ⟨230972, by rfl⟩ : syracuseStep 307963 = 461945) B461945
theorem B308031 : Blo 307833 308031 := bstep (se 1 (by rfl) ⟨231023, by rfl⟩ : syracuseStep 308031 = 462047) B462047
theorem B308059 : Blo 307833 308059 := bstep (se 1 (by rfl) ⟨231044, by rfl⟩ : syracuseStep 308059 = 462089) B462089
theorem B439177 : Blo 307833 439177 := bstep (se 2 (by rfl) ⟨164691, by rfl⟩ : syracuseStep 439177 = 329383) B329383
theorem B308127 : Blo 307833 308127 := bstep (se 1 (by rfl) ⟨231095, by rfl⟩ : syracuseStep 308127 = 462191) B462191
theorem B701351 : Blo 307833 701351 := bstep (se 1 (by rfl) ⟨526013, by rfl⟩ : syracuseStep 701351 = 1052027) B1052027
theorem B1684435 : Blo 307833 1684435 := bstep (se 1 (by rfl) ⟨1263326, by rfl⟩ : syracuseStep 1684435 = 2526653) B2526653
theorem B308207 : Blo 307833 308207 := bstep (se 1 (by rfl) ⟨231155, by rfl⟩ : syracuseStep 308207 = 462311) B462311
theorem B308295 : Blo 307833 308295 := bstep (se 1 (by rfl) ⟨231221, by rfl⟩ : syracuseStep 308295 = 462443) B462443
theorem B308379 : Blo 307833 308379 := bstep (se 1 (by rfl) ⟨231284, by rfl⟩ : syracuseStep 308379 = 462569) B462569
theorem B308475 : Blo 307833 308475 := bstep (se 1 (by rfl) ⟨231356, by rfl⟩ : syracuseStep 308475 = 462713) B462713
theorem B308543 : Blo 307833 308543 := bstep (se 1 (by rfl) ⟨231407, by rfl⟩ : syracuseStep 308543 = 462815) B462815
theorem B9549161 : Blo 307833 9549161 := bstep (se 2 (by rfl) ⟨3580935, by rfl⟩ : syracuseStep 9549161 = 7161871) B7161871
theorem B308711 : Blo 307833 308711 := bstep (se 1 (by rfl) ⟨231533, by rfl⟩ : syracuseStep 308711 = 463067) B463067
theorem B308719 : Blo 307833 308719 := bstep (se 1 (by rfl) ⟨231539, by rfl⟩ : syracuseStep 308719 = 463079) B463079
theorem B308827 : Blo 307833 308827 := bstep (se 1 (by rfl) ⟨231620, by rfl⟩ : syracuseStep 308827 = 463241) B463241
theorem B308891 : Blo 307833 308891 := bstep (se 1 (by rfl) ⟨231668, by rfl⟩ : syracuseStep 308891 = 463337) B463337
theorem B5617309 : Blo 307833 5617309 := bstep (se 3 (by rfl) ⟨1053245, by rfl⟩ : syracuseStep 5617309 = 2106491) B2106491
theorem B2340575 : Blo 307833 2340575 := bstep (se 1 (by rfl) ⟨1755431, by rfl⟩ : syracuseStep 2340575 = 3510863) B3510863
theorem B308975 : Blo 307833 308975 := bstep (se 1 (by rfl) ⟨231731, by rfl⟩ : syracuseStep 308975 = 463463) B463463
theorem B309063 : Blo 307833 309063 := bstep (se 1 (by rfl) ⟨231797, by rfl⟩ : syracuseStep 309063 = 463595) B463595
theorem B309083 : Blo 307833 309083 := bstep (se 1 (by rfl) ⟨231812, by rfl⟩ : syracuseStep 309083 = 463625) B463625
theorem B309151 : Blo 307833 309151 := bstep (se 1 (by rfl) ⟨231863, by rfl⟩ : syracuseStep 309151 = 463727) B463727
theorem B309319 : Blo 307833 309319 := bstep (se 1 (by rfl) ⟨231989, by rfl⟩ : syracuseStep 309319 = 463979) B463979
theorem B309479 : Blo 307833 309479 := bstep (se 1 (by rfl) ⟨232109, by rfl⟩ : syracuseStep 309479 = 464219) B464219
theorem B1063207 : Blo 307833 1063207 := bstep (se 1 (by rfl) ⟨797405, by rfl⟩ : syracuseStep 1063207 = 1594811) B1594811
theorem B309663 : Blo 307833 309663 := bstep (se 1 (by rfl) ⟨232247, by rfl⟩ : syracuseStep 309663 = 464495) B464495
theorem B309711 : Blo 307833 309711 := bstep (se 1 (by rfl) ⟨232283, by rfl⟩ : syracuseStep 309711 = 464567) B464567
theorem B309735 : Blo 307833 309735 := bstep (se 1 (by rfl) ⟨232301, by rfl⟩ : syracuseStep 309735 = 464603) B464603
theorem B309851 : Blo 307833 309851 := bstep (se 1 (by rfl) ⟨232388, by rfl⟩ : syracuseStep 309851 = 464777) B464777
theorem B1489529 : Blo 307833 1489529 := bstep (se 2 (by rfl) ⟨558573, by rfl⟩ : syracuseStep 1489529 = 1117147) B1117147
theorem B309919 : Blo 307833 309919 := bstep (se 1 (by rfl) ⟨232439, by rfl⟩ : syracuseStep 309919 = 464879) B464879
theorem B1325801 : Blo 307833 1325801 := bstep (se 2 (by rfl) ⟨497175, by rfl⟩ : syracuseStep 1325801 = 994351) B994351
theorem B310087 : Blo 307833 310087 := bstep (se 1 (by rfl) ⟨232565, by rfl⟩ : syracuseStep 310087 = 465131) B465131
theorem B310127 : Blo 307833 310127 := bstep (se 1 (by rfl) ⟨232595, by rfl⟩ : syracuseStep 310127 = 465191) B465191
theorem B310183 : Blo 307833 310183 := bstep (se 1 (by rfl) ⟨232637, by rfl⟩ : syracuseStep 310183 = 465275) B465275
theorem B310363 : Blo 307833 310363 := bstep (se 1 (by rfl) ⟨232772, by rfl⟩ : syracuseStep 310363 = 465545) B465545
theorem B310479 : Blo 307833 310479 := bstep (se 1 (by rfl) ⟨232859, by rfl⟩ : syracuseStep 310479 = 465719) B465719
theorem B310503 : Blo 307833 310503 := bstep (se 1 (by rfl) ⟨232877, by rfl⟩ : syracuseStep 310503 = 465755) B465755
theorem B310599 : Blo 307833 310599 := bstep (se 1 (by rfl) ⟨232949, by rfl⟩ : syracuseStep 310599 = 465899) B465899
theorem B310735 : Blo 307833 310735 := bstep (se 1 (by rfl) ⟨233051, by rfl⟩ : syracuseStep 310735 = 466103) B466103
theorem B310895 : Blo 307833 310895 := bstep (se 1 (by rfl) ⟨233171, by rfl⟩ : syracuseStep 310895 = 466343) B466343
theorem B310951 : Blo 307833 310951 := bstep (se 1 (by rfl) ⟨233213, by rfl⟩ : syracuseStep 310951 = 466427) B466427
theorem B311015 : Blo 307833 311015 := bstep (se 1 (by rfl) ⟨233261, by rfl⟩ : syracuseStep 311015 = 466523) B466523
theorem B311071 : Blo 307833 311071 := bstep (se 1 (by rfl) ⟨233303, by rfl⟩ : syracuseStep 311071 = 466607) B466607
theorem B311151 : Blo 307833 311151 := bstep (se 1 (by rfl) ⟨233363, by rfl⟩ : syracuseStep 311151 = 466727) B466727
theorem B311207 : Blo 307833 311207 := bstep (se 1 (by rfl) ⟨233405, by rfl⟩ : syracuseStep 311207 = 466811) B466811
theorem B311487 : Blo 307833 311487 := bstep (se 1 (by rfl) ⟨233615, by rfl⟩ : syracuseStep 311487 = 467231) B467231
theorem B311503 : Blo 307833 311503 := bstep (se 1 (by rfl) ⟨233627, by rfl⟩ : syracuseStep 311503 = 467255) B467255
theorem B311551 : Blo 307833 311551 := bstep (se 1 (by rfl) ⟨233663, by rfl⟩ : syracuseStep 311551 = 467327) B467327
theorem B311599 : Blo 307833 311599 := bstep (se 1 (by rfl) ⟨233699, by rfl⟩ : syracuseStep 311599 = 467399) B467399
theorem B1327441 : Blo 307833 1327441 := bstep (se 2 (by rfl) ⟨497790, by rfl⟩ : syracuseStep 1327441 = 995581) B995581
theorem B5292539 : Blo 307833 5292539 := bstep (se 1 (by rfl) ⟨3969404, by rfl⟩ : syracuseStep 5292539 = 7938809) B7938809
theorem B2638615 : Blo 307833 2638615 := bstep (se 1 (by rfl) ⟨1978961, by rfl⟩ : syracuseStep 2638615 = 3957923) B3957923
theorem B443335 : Blo 307833 443335 := bstep (se 1 (by rfl) ⟨332501, by rfl⟩ : syracuseStep 443335 = 665003) B665003
theorem B1131515 : Blo 307833 1131515 := bstep (se 1 (by rfl) ⟨848636, by rfl⟩ : syracuseStep 1131515 = 1697273) B1697273
theorem B1983527 : Blo 307833 1983527 := bstep (se 1 (by rfl) ⟨1487645, by rfl⟩ : syracuseStep 1983527 = 2975291) B2975291
theorem B672875 : Blo 307833 672875 := bstep (se 1 (by rfl) ⟨504656, by rfl⟩ : syracuseStep 672875 = 1009313) B1009313
theorem B7489655 : Blo 307833 7489655 := bstep (se 1 (by rfl) ⟨5617241, by rfl⟩ : syracuseStep 7489655 = 11234483) B11234483
theorem B2377937 : Blo 307833 2377937 := bstep (se 2 (by rfl) ⟨891726, by rfl⟩ : syracuseStep 2377937 = 1783453) B1783453
theorem B346495 : Blo 307833 346495 := bstep (se 1 (by rfl) ⟨259871, by rfl⟩ : syracuseStep 346495 = 519743) B519743
theorem B313727 : Blo 307833 313727 := bstep (se 1 (by rfl) ⟨235295, by rfl⟩ : syracuseStep 313727 = 470591) B470591
theorem B1756025 : Blo 307833 1756025 := bstep (se 2 (by rfl) ⟨658509, by rfl⟩ : syracuseStep 1756025 = 1317019) B1317019
theorem B576377 : Blo 307833 576377 := bstep (se 2 (by rfl) ⟨216141, by rfl⟩ : syracuseStep 576377 = 432283) B432283
theorem B18205661 : Blo 307833 18205661 := bstep (se 3 (by rfl) ⟨3413561, by rfl⟩ : syracuseStep 18205661 = 6827123) B6827123
theorem B3656927 : Blo 307833 3656927 := bstep (se 1 (by rfl) ⟨2742695, by rfl⟩ : syracuseStep 3656927 = 5485391) B5485391
theorem B741035 : Blo 307833 741035 := bstep (se 1 (by rfl) ⟨555776, by rfl⟩ : syracuseStep 741035 = 1111553) B1111553
theorem B347899 : Blo 307833 347899 := bstep (se 1 (by rfl) ⟨260924, by rfl⟩ : syracuseStep 347899 = 521849) B521849
theorem B1331099 : Blo 307833 1331099 := bstep (se 1 (by rfl) ⟨998324, by rfl⟩ : syracuseStep 1331099 = 1996649) B1996649
theorem B3755969 : Blo 307833 3755969 := bstep (se 2 (by rfl) ⟨1408488, by rfl⟩ : syracuseStep 3755969 = 2816977) B2816977
theorem B1265719 : Blo 307833 1265719 := bstep (se 1 (by rfl) ⟨949289, by rfl⟩ : syracuseStep 1265719 = 1898579) B1898579
theorem B348223 : Blo 307833 348223 := bstep (se 1 (by rfl) ⟨261167, by rfl⟩ : syracuseStep 348223 = 522335) B522335
theorem B3560071 : Blo 307833 3560071 := bstep (se 1 (by rfl) ⟨2670053, by rfl⟩ : syracuseStep 3560071 = 5340107) B5340107
theorem B349087 : Blo 307833 349087 := bstep (se 1 (by rfl) ⟨261815, by rfl⟩ : syracuseStep 349087 = 523631) B523631
theorem B1496045 : Blo 307833 1496045 := bstep (se 3 (by rfl) ⟨280508, by rfl⟩ : syracuseStep 1496045 = 561017) B561017
theorem B349339 : Blo 307833 349339 := bstep (se 1 (by rfl) ⟨262004, by rfl⟩ : syracuseStep 349339 = 524009) B524009
theorem B350023 : Blo 307833 350023 := bstep (se 1 (by rfl) ⟨262517, by rfl⟩ : syracuseStep 350023 = 525035) B525035
theorem B350671 : Blo 307833 350671 := bstep (se 1 (by rfl) ⟨263003, by rfl⟩ : syracuseStep 350671 = 526007) B526007
theorem B3562055 : Blo 307833 3562055 := bstep (se 1 (by rfl) ⟨2671541, by rfl⟩ : syracuseStep 3562055 = 5343083) B5343083
theorem B75979457 : Blo 307833 75979457 := bstep (se 2 (by rfl) ⟨28492296, by rfl⟩ : syracuseStep 75979457 = 56984593) B56984593
theorem B1039175 : Blo 307833 1039175 := bstep (se 1 (by rfl) ⟨779381, by rfl⟩ : syracuseStep 1039175 = 1558763) B1558763
theorem B1170395 : Blo 307833 1170395 := bstep (se 1 (by rfl) ⟨877796, by rfl⟩ : syracuseStep 1170395 = 1755593) B1755593
theorem B1760399 : Blo 307833 1760399 := bstep (se 1 (by rfl) ⟨1320299, by rfl⟩ : syracuseStep 1760399 = 2640599) B2640599
theorem B745033 : Blo 307833 745033 := bstep (se 2 (by rfl) ⟨279387, by rfl⟩ : syracuseStep 745033 = 558775) B558775
theorem B1040039 : Blo 307833 1040039 := bstep (se 1 (by rfl) ⟨780029, by rfl⟩ : syracuseStep 1040039 = 1560059) B1560059
theorem B2121383 : Blo 307833 2121383 := bstep (se 1 (by rfl) ⟨1591037, by rfl⟩ : syracuseStep 2121383 = 3182075) B3182075
theorem B1171169 : Blo 307833 1171169 := bstep (se 2 (by rfl) ⟨439188, by rfl⟩ : syracuseStep 1171169 = 878377) B878377
theorem B1040147 : Blo 307833 1040147 := bstep (se 1 (by rfl) ⟨780110, by rfl⟩ : syracuseStep 1040147 = 1560221) B1560221
theorem B352031 : Blo 307833 352031 := bstep (se 1 (by rfl) ⟨264023, by rfl⟩ : syracuseStep 352031 = 528047) B528047
theorem B1761425 : Blo 307833 1761425 := bstep (se 2 (by rfl) ⟨660534, by rfl⟩ : syracuseStep 1761425 = 1321069) B1321069
theorem B13656721 : Blo 307833 13656721 := bstep (se 2 (by rfl) ⟨5121270, by rfl⟩ : syracuseStep 13656721 = 10242541) B10242541
theorem B1565405 : Blo 307833 1565405 := bstep (se 3 (by rfl) ⟨293513, by rfl⟩ : syracuseStep 1565405 = 587027) B587027
theorem B2647363 : Blo 307833 2647363 := bstep (se 1 (by rfl) ⟨1985522, by rfl⟩ : syracuseStep 2647363 = 3971045) B3971045
theorem B1763315 : Blo 307833 1763315 := bstep (se 1 (by rfl) ⟨1322486, by rfl⟩ : syracuseStep 1763315 = 2644973) B2644973
theorem B1043279 : Blo 307833 1043279 := bstep (se 1 (by rfl) ⟨782459, by rfl⟩ : syracuseStep 1043279 = 1564919) B1564919
theorem B1174601 : Blo 307833 1174601 := bstep (se 2 (by rfl) ⟨440475, by rfl⟩ : syracuseStep 1174601 = 880951) B880951
theorem B782075 : Blo 307833 782075 := bstep (se 1 (by rfl) ⟨586556, by rfl⟩ : syracuseStep 782075 = 1173113) B1173113
theorem B5107585 : Blo 307833 5107585 := bstep (se 2 (by rfl) ⟨1915344, by rfl⟩ : syracuseStep 5107585 = 3830689) B3830689
theorem B22998971 : Blo 307833 22998971 := bstep (se 1 (by rfl) ⟨17249228, by rfl⟩ : syracuseStep 22998971 = 34498457) B34498457
theorem B585721 : Blo 307833 585721 := bstep (se 2 (by rfl) ⟨219645, by rfl⟩ : syracuseStep 585721 = 439291) B439291
theorem B1667155 : Blo 307833 1667155 := bstep (se 1 (by rfl) ⟨1250366, by rfl⟩ : syracuseStep 1667155 = 2500733) B2500733
theorem B782419 : Blo 307833 782419 := bstep (se 1 (by rfl) ⟨586814, by rfl⟩ : syracuseStep 782419 = 1173629) B1173629
theorem B880723 : Blo 307833 880723 := bstep (se 1 (by rfl) ⟨660542, by rfl⟩ : syracuseStep 880723 = 1321085) B1321085
theorem B1176059 : Blo 307833 1176059 := bstep (se 1 (by rfl) ⟨882044, by rfl⟩ : syracuseStep 1176059 = 1764089) B1764089
theorem B8516177 : Blo 307833 8516177 := bstep (se 2 (by rfl) ⟨3193566, by rfl⟩ : syracuseStep 8516177 = 6387133) B6387133
theorem B1569455 : Blo 307833 1569455 := bstep (se 1 (by rfl) ⟨1177091, by rfl⟩ : syracuseStep 1569455 = 2354183) B2354183
theorem B4453127 : Blo 307833 4453127 := bstep (se 1 (by rfl) ⟨3339845, by rfl⟩ : syracuseStep 4453127 = 6679691) B6679691
theorem B521167 : Blo 307833 521167 := bstep (se 1 (by rfl) ⟨390875, by rfl⟩ : syracuseStep 521167 = 781751) B781751
theorem B8909837 : Blo 307833 8909837 := bstep (se 3 (by rfl) ⟨1670594, by rfl⟩ : syracuseStep 8909837 = 3341189) B3341189
theorem B5305661 : Blo 307833 5305661 := bstep (se 3 (by rfl) ⟨994811, by rfl⟩ : syracuseStep 5305661 = 1989623) B1989623
theorem B587179 : Blo 307833 587179 := bstep (se 1 (by rfl) ⟨440384, by rfl⟩ : syracuseStep 587179 = 880769) B880769
theorem B783827 : Blo 307833 783827 := bstep (se 1 (by rfl) ⟨587870, by rfl⟩ : syracuseStep 783827 = 1175741) B1175741
theorem B2651737 : Blo 307833 2651737 := bstep (se 2 (by rfl) ⟨994401, by rfl⟩ : syracuseStep 2651737 = 1988803) B1988803
theorem B1177199 : Blo 307833 1177199 := bstep (se 1 (by rfl) ⟨882899, by rfl⟩ : syracuseStep 1177199 = 1765799) B1765799
theorem B587407 : Blo 307833 587407 := bstep (se 1 (by rfl) ⟨440555, by rfl⟩ : syracuseStep 587407 = 881111) B881111
theorem B2815661 : Blo 307833 2815661 := bstep (se 3 (by rfl) ⟨527936, by rfl⟩ : syracuseStep 2815661 = 1055873) B1055873
theorem B2652011 : Blo 307833 2652011 := bstep (se 1 (by rfl) ⟨1989008, by rfl⟩ : syracuseStep 2652011 = 3978017) B3978017
theorem B522281 : Blo 307833 522281 := bstep (se 2 (by rfl) ⟨195855, by rfl⟩ : syracuseStep 522281 = 391711) B391711
theorem B1767689 : Blo 307833 1767689 := bstep (se 2 (by rfl) ⟨662883, by rfl⟩ : syracuseStep 1767689 = 1325767) B1325767
theorem B784687 : Blo 307833 784687 := bstep (se 1 (by rfl) ⟨588515, by rfl⟩ : syracuseStep 784687 = 1177031) B1177031
theorem B588379 : Blo 307833 588379 := bstep (se 1 (by rfl) ⟨441284, by rfl⟩ : syracuseStep 588379 = 882569) B882569
theorem B1112705 : Blo 307833 1112705 := bstep (se 2 (by rfl) ⟨417264, by rfl⟩ : syracuseStep 1112705 = 834529) B834529
theorem B522895 : Blo 307833 522895 := bstep (se 1 (by rfl) ⟨392171, by rfl⟩ : syracuseStep 522895 = 784343) B784343
theorem B1047275 : Blo 307833 1047275 := bstep (se 1 (by rfl) ⟨785456, by rfl⟩ : syracuseStep 1047275 = 1570913) B1570913
theorem B1047383 : Blo 307833 1047383 := bstep (se 1 (by rfl) ⟨785537, by rfl⟩ : syracuseStep 1047383 = 1571075) B1571075
theorem B589025 : Blo 307833 589025 := bstep (se 2 (by rfl) ⟨220884, by rfl⟩ : syracuseStep 589025 = 441769) B441769
theorem B883993 : Blo 307833 883993 := bstep (se 2 (by rfl) ⟨331497, by rfl⟩ : syracuseStep 883993 = 662995) B662995
theorem B1178975 : Blo 307833 1178975 := bstep (se 1 (by rfl) ⟨884231, by rfl⟩ : syracuseStep 1178975 = 1768463) B1768463
theorem B1572371 : Blo 307833 1572371 := bstep (se 1 (by rfl) ⟨1179278, by rfl⟩ : syracuseStep 1572371 = 2358557) B2358557
theorem B1048193 : Blo 307833 1048193 := bstep (se 2 (by rfl) ⟨393072, by rfl⟩ : syracuseStep 1048193 = 786145) B786145
theorem B786095 : Blo 307833 786095 := bstep (se 1 (by rfl) ⟨589571, by rfl⟩ : syracuseStep 786095 = 1179143) B1179143
theorem B1179431 : Blo 307833 1179431 := bstep (se 1 (by rfl) ⟨884573, by rfl⟩ : syracuseStep 1179431 = 1769147) B1769147
theorem B1048463 : Blo 307833 1048463 := bstep (se 1 (by rfl) ⟨786347, by rfl⟩ : syracuseStep 1048463 = 1572695) B1572695
theorem B3342707 : Blo 307833 3342707 := bstep (se 1 (by rfl) ⟨2507030, by rfl⟩ : syracuseStep 3342707 = 5014061) B5014061
theorem B1769921 : Blo 307833 1769921 := bstep (se 2 (by rfl) ⟨663720, by rfl⟩ : syracuseStep 1769921 = 1327441) B1327441
theorem B754343 : Blo 307833 754343 := bstep (se 1 (by rfl) ⟨565757, by rfl⟩ : syracuseStep 754343 = 1131515) B1131515
theorem B787583 : Blo 307833 787583 := bstep (se 1 (by rfl) ⟨590687, by rfl⟩ : syracuseStep 787583 = 1181375) B1181375
theorem B1574153 : Blo 307833 1574153 := bstep (se 2 (by rfl) ⟨590307, by rfl⟩ : syracuseStep 1574153 = 1180615) B1180615
theorem B591113 : Blo 307833 591113 := bstep (se 2 (by rfl) ⟨221667, by rfl⟩ : syracuseStep 591113 = 443335) B443335
theorem B788201 : Blo 307833 788201 := bstep (se 2 (by rfl) ⟨295575, by rfl⟩ : syracuseStep 788201 = 591151) B591151
theorem B788363 : Blo 307833 788363 := bstep (se 1 (by rfl) ⟨591272, by rfl⟩ : syracuseStep 788363 = 1182545) B1182545
theorem B494023 : Blo 307833 494023 := bstep (se 1 (by rfl) ⟨370517, by rfl⟩ : syracuseStep 494023 = 741035) B741035
theorem B887399 : Blo 307833 887399 := bstep (se 1 (by rfl) ⟨665549, by rfl⟩ : syracuseStep 887399 = 1331099) B1331099
theorem B1051703 : Blo 307833 1051703 := bstep (se 1 (by rfl) ⟨788777, by rfl⟩ : syracuseStep 1051703 = 1577555) B1577555
theorem B461915 : Blo 307833 461915 := bstep (se 1 (by rfl) ⟨346436, by rfl⟩ : syracuseStep 461915 = 692873) B692873
theorem B461993 : Blo 307833 461993 := bstep (se 2 (by rfl) ⟨173247, by rfl⟩ : syracuseStep 461993 = 346495) B346495
theorem B462407 : Blo 307833 462407 := bstep (se 1 (by rfl) ⟨346805, by rfl⟩ : syracuseStep 462407 = 693611) B693611
theorem B462587 : Blo 307833 462587 := bstep (se 1 (by rfl) ⟨346940, by rfl⟩ : syracuseStep 462587 = 693881) B693881
theorem B462827 : Blo 307833 462827 := bstep (se 1 (by rfl) ⟨347120, by rfl⟩ : syracuseStep 462827 = 694241) B694241
theorem B659449 : Blo 307833 659449 := bstep (se 2 (by rfl) ⟨247293, by rfl⟩ : syracuseStep 659449 = 494587) B494587
theorem B1183835 : Blo 307833 1183835 := bstep (se 1 (by rfl) ⟨887876, by rfl⟩ : syracuseStep 1183835 = 1775753) B1775753
theorem B692783 : Blo 307833 692783 := bstep (se 1 (by rfl) ⟨519587, by rfl⟩ : syracuseStep 692783 = 1039175) B1039175
theorem B1774295 : Blo 307833 1774295 := bstep (se 1 (by rfl) ⟨1330721, by rfl⟩ : syracuseStep 1774295 = 2661443) B2661443
theorem B463865 : Blo 307833 463865 := bstep (se 2 (by rfl) ⟨173949, by rfl⟩ : syracuseStep 463865 = 347899) B347899
theorem B693359 : Blo 307833 693359 := bstep (se 1 (by rfl) ⟨520019, by rfl⟩ : syracuseStep 693359 = 1040039) B1040039
theorem B1414255 : Blo 307833 1414255 := bstep (se 1 (by rfl) ⟨1060691, by rfl⟩ : syracuseStep 1414255 = 2121383) B2121383
theorem B693431 : Blo 307833 693431 := bstep (se 1 (by rfl) ⟨520073, by rfl⟩ : syracuseStep 693431 = 1040147) B1040147
theorem B464063 : Blo 307833 464063 := bstep (se 1 (by rfl) ⟨348047, by rfl⟩ : syracuseStep 464063 = 696095) B696095
theorem B464207 : Blo 307833 464207 := bstep (se 1 (by rfl) ⟨348155, by rfl⟩ : syracuseStep 464207 = 696311) B696311
theorem B464297 : Blo 307833 464297 := bstep (se 2 (by rfl) ⟨174111, by rfl⟩ : syracuseStep 464297 = 348223) B348223
theorem B792031 : Blo 307833 792031 := bstep (se 1 (by rfl) ⟨594023, by rfl⟩ : syracuseStep 792031 = 1188047) B1188047
theorem B464351 : Blo 307833 464351 := bstep (se 1 (by rfl) ⟨348263, by rfl⟩ : syracuseStep 464351 = 696527) B696527
theorem B464447 : Blo 307833 464447 := bstep (se 1 (by rfl) ⟨348335, by rfl⟩ : syracuseStep 464447 = 696671) B696671
theorem B464927 : Blo 307833 464927 := bstep (se 1 (by rfl) ⟨348695, by rfl⟩ : syracuseStep 464927 = 697391) B697391
theorem B661807 : Blo 307833 661807 := bstep (se 1 (by rfl) ⟨496355, by rfl⟩ : syracuseStep 661807 = 992711) B992711
theorem B465359 : Blo 307833 465359 := bstep (se 1 (by rfl) ⟨349019, by rfl⟩ : syracuseStep 465359 = 698039) B698039
theorem B465449 : Blo 307833 465449 := bstep (se 2 (by rfl) ⟨174543, by rfl⟩ : syracuseStep 465449 = 349087) B349087
theorem B662107 : Blo 307833 662107 := bstep (se 1 (by rfl) ⟨496580, by rfl⟩ : syracuseStep 662107 = 993161) B993161
theorem B694889 : Blo 307833 694889 := bstep (se 2 (by rfl) ⟨260583, by rfl⟩ : syracuseStep 694889 = 521167) B521167
theorem B465659 : Blo 307833 465659 := bstep (se 1 (by rfl) ⟨349244, by rfl⟩ : syracuseStep 465659 = 698489) B698489
theorem B465785 : Blo 307833 465785 := bstep (se 2 (by rfl) ⟨174669, by rfl⟩ : syracuseStep 465785 = 349339) B349339
theorem B695519 : Blo 307833 695519 := bstep (se 1 (by rfl) ⟨521639, by rfl⟩ : syracuseStep 695519 = 1043279) B1043279
theorem B4005287 : Blo 307833 4005287 := bstep (se 1 (by rfl) ⟨3003965, by rfl⟩ : syracuseStep 4005287 = 6007931) B6007931
theorem B466535 : Blo 307833 466535 := bstep (se 1 (by rfl) ⟨349901, by rfl⟩ : syracuseStep 466535 = 699803) B699803
theorem B466697 : Blo 307833 466697 := bstep (se 2 (by rfl) ⟨175011, by rfl⟩ : syracuseStep 466697 = 350023) B350023
theorem B1974041 : Blo 307833 1974041 := bstep (se 2 (by rfl) ⟨740265, by rfl⟩ : syracuseStep 1974041 = 1480531) B1480531
theorem B1580897 : Blo 307833 1580897 := bstep (se 2 (by rfl) ⟨592836, by rfl⟩ : syracuseStep 1580897 = 1185673) B1185673
theorem B8921015 : Blo 307833 8921015 := bstep (se 1 (by rfl) ⟨6690761, by rfl⟩ : syracuseStep 8921015 = 13381523) B13381523
theorem B466919 : Blo 307833 466919 := bstep (se 1 (by rfl) ⟨350189, by rfl⟩ : syracuseStep 466919 = 700379) B700379
theorem B467039 : Blo 307833 467039 := bstep (se 1 (by rfl) ⟨350279, by rfl⟩ : syracuseStep 467039 = 700559) B700559
theorem B991379 : Blo 307833 991379 := bstep (se 1 (by rfl) ⟨743534, by rfl⟩ : syracuseStep 991379 = 1487069) B1487069
theorem B467099 : Blo 307833 467099 := bstep (se 1 (by rfl) ⟨350324, by rfl⟩ : syracuseStep 467099 = 700649) B700649
theorem B467183 : Blo 307833 467183 := bstep (se 1 (by rfl) ⟨350387, by rfl⟩ : syracuseStep 467183 = 700775) B700775
theorem B2367791 : Blo 307833 2367791 := bstep (se 1 (by rfl) ⟨1775843, by rfl⟩ : syracuseStep 2367791 = 3551687) B3551687
theorem B3350879 : Blo 307833 3350879 := bstep (se 1 (by rfl) ⟨2513159, by rfl⟩ : syracuseStep 3350879 = 5026319) B5026319
theorem B1417609 : Blo 307833 1417609 := bstep (se 2 (by rfl) ⟨531603, by rfl⟩ : syracuseStep 1417609 = 1063207) B1063207
theorem B5677451 : Blo 307833 5677451 := bstep (se 1 (by rfl) ⟨4258088, by rfl⟩ : syracuseStep 5677451 = 8516177) B8516177
theorem B6365627 : Blo 307833 6365627 := bstep (se 1 (by rfl) ⟨4774220, by rfl⟩ : syracuseStep 6365627 = 9548441) B9548441
theorem B467561 : Blo 307833 467561 := bstep (se 2 (by rfl) ⟨175335, by rfl⟩ : syracuseStep 467561 = 350671) B350671
theorem B467567 : Blo 307833 467567 := bstep (se 1 (by rfl) ⟨350675, by rfl⟩ : syracuseStep 467567 = 701351) B701351
theorem B5939891 : Blo 307833 5939891 := bstep (se 1 (by rfl) ⟨4454918, by rfl⟩ : syracuseStep 5939891 = 8909837) B8909837
theorem B697193 : Blo 307833 697193 := bstep (se 2 (by rfl) ⟨261447, by rfl⟩ : syracuseStep 697193 = 522895) B522895
theorem B6366107 : Blo 307833 6366107 := bstep (se 1 (by rfl) ⟨4774580, by rfl⟩ : syracuseStep 6366107 = 9549161) B9549161
theorem B1877107 : Blo 307833 1877107 := bstep (se 1 (by rfl) ⟨1407830, by rfl⟩ : syracuseStep 1877107 = 2815661) B2815661
theorem B993019 : Blo 307833 993019 := bstep (se 1 (by rfl) ⟨744764, by rfl⟩ : syracuseStep 993019 = 1489529) B1489529
theorem B698183 : Blo 307833 698183 := bstep (se 1 (by rfl) ⟨523637, by rfl⟩ : syracuseStep 698183 = 1047275) B1047275
theorem B698255 : Blo 307833 698255 := bstep (se 1 (by rfl) ⟨523691, by rfl⟩ : syracuseStep 698255 = 1047383) B1047383
theorem B993377 : Blo 307833 993377 := bstep (se 2 (by rfl) ⟨372516, by rfl⟩ : syracuseStep 993377 = 745033) B745033
theorem B698795 : Blo 307833 698795 := bstep (se 1 (by rfl) ⟨524096, by rfl⟩ : syracuseStep 698795 = 1048193) B1048193
theorem B698975 : Blo 307833 698975 := bstep (se 1 (by rfl) ⟨524231, by rfl⟩ : syracuseStep 698975 = 1048463) B1048463
theorem B1059485 : Blo 307833 1059485 := bstep (se 3 (by rfl) ⟨198653, by rfl⟩ : syracuseStep 1059485 = 397307) B397307
theorem B1977169 : Blo 307833 1977169 := bstep (se 2 (by rfl) ⟨741438, by rfl⟩ : syracuseStep 1977169 = 1482877) B1482877
theorem B2010017 : Blo 307833 2010017 := bstep (se 2 (by rfl) ⟨753756, by rfl⟩ : syracuseStep 2010017 = 1507513) B1507513
theorem B699335 : Blo 307833 699335 := bstep (se 1 (by rfl) ⟨524501, by rfl⟩ : syracuseStep 699335 = 1049003) B1049003
theorem B699695 : Blo 307833 699695 := bstep (se 1 (by rfl) ⟨524771, by rfl⟩ : syracuseStep 699695 = 1049543) B1049543
theorem B699731 : Blo 307833 699731 := bstep (se 1 (by rfl) ⟨524798, by rfl⟩ : syracuseStep 699731 = 1049597) B1049597
theorem B1322351 : Blo 307833 1322351 := bstep (se 1 (by rfl) ⟨991763, by rfl⟩ : syracuseStep 1322351 = 1983527) B1983527
theorem B6335891 : Blo 307833 6335891 := bstep (se 1 (by rfl) ⟨4751918, by rfl⟩ : syracuseStep 6335891 = 9503837) B9503837
theorem B699983 : Blo 307833 699983 := bstep (se 1 (by rfl) ⟨524987, by rfl⟩ : syracuseStep 699983 = 1049975) B1049975
theorem B3518153 : Blo 307833 3518153 := bstep (se 2 (by rfl) ⟨1319307, by rfl⟩ : syracuseStep 3518153 = 2638615) B2638615
theorem B700271 : Blo 307833 700271 := bstep (se 1 (by rfl) ⟨525203, by rfl⟩ : syracuseStep 700271 = 1050407) B1050407
theorem B4993103 : Blo 307833 4993103 := bstep (se 1 (by rfl) ⟨3744827, by rfl⟩ : syracuseStep 4993103 = 7489655) B7489655
theorem B700523 : Blo 307833 700523 := bstep (se 1 (by rfl) ⟨525392, by rfl⟩ : syracuseStep 700523 = 1050785) B1050785
theorem B1585291 : Blo 307833 1585291 := bstep (se 1 (by rfl) ⟨1188968, by rfl⟩ : syracuseStep 1585291 = 2377937) B2377937
theorem B700703 : Blo 307833 700703 := bstep (se 1 (by rfl) ⟨525527, by rfl⟩ : syracuseStep 700703 = 1051055) B1051055
theorem B307879 : Blo 307833 307879 := bstep (se 1 (by rfl) ⟨230909, by rfl⟩ : syracuseStep 307879 = 461819) B461819
theorem B307919 : Blo 307833 307919 := bstep (se 1 (by rfl) ⟨230939, by rfl⟩ : syracuseStep 307919 = 461879) B461879
theorem B307999 : Blo 307833 307999 := bstep (se 1 (by rfl) ⟨230999, by rfl⟩ : syracuseStep 307999 = 461999) B461999
theorem B2437951 : Blo 307833 2437951 := bstep (se 1 (by rfl) ⟨1828463, by rfl⟩ : syracuseStep 2437951 = 3656927) B3656927
theorem B701423 : Blo 307833 701423 := bstep (se 1 (by rfl) ⟨526067, by rfl⟩ : syracuseStep 701423 = 1052135) B1052135
theorem B308479 : Blo 307833 308479 := bstep (se 1 (by rfl) ⟨231359, by rfl⟩ : syracuseStep 308479 = 462719) B462719
theorem B2503979 : Blo 307833 2503979 := bstep (se 1 (by rfl) ⟨1877984, by rfl⟩ : syracuseStep 2503979 = 3755969) B3755969
theorem B308607 : Blo 307833 308607 := bstep (se 1 (by rfl) ⟨231455, by rfl⟩ : syracuseStep 308607 = 462911) B462911
theorem B308763 : Blo 307833 308763 := bstep (se 1 (by rfl) ⟨231572, by rfl⟩ : syracuseStep 308763 = 463145) B463145
theorem B308943 : Blo 307833 308943 := bstep (se 1 (by rfl) ⟨231707, by rfl⟩ : syracuseStep 308943 = 463415) B463415
theorem B3192539 : Blo 307833 3192539 := bstep (se 1 (by rfl) ⟨2394404, by rfl⟩ : syracuseStep 3192539 = 4788809) B4788809
theorem B309183 : Blo 307833 309183 := bstep (se 1 (by rfl) ⟨231887, by rfl⟩ : syracuseStep 309183 = 463775) B463775
theorem B997363 : Blo 307833 997363 := bstep (se 1 (by rfl) ⟨748022, by rfl⟩ : syracuseStep 997363 = 1496045) B1496045
theorem B309311 : Blo 307833 309311 := bstep (se 1 (by rfl) ⟨231983, by rfl⟩ : syracuseStep 309311 = 463967) B463967
theorem B309351 : Blo 307833 309351 := bstep (se 1 (by rfl) ⟨232013, by rfl⟩ : syracuseStep 309351 = 464027) B464027
theorem B768503 : Blo 307833 768503 := bstep (se 1 (by rfl) ⟨576377, by rfl⟩ : syracuseStep 768503 = 1152755) B1152755
theorem B309807 : Blo 307833 309807 := bstep (se 1 (by rfl) ⟨232355, by rfl⟩ : syracuseStep 309807 = 464711) B464711
theorem B310207 : Blo 307833 310207 := bstep (se 1 (by rfl) ⟨232655, by rfl⟩ : syracuseStep 310207 = 465311) B465311
theorem B310255 : Blo 307833 310255 := bstep (se 1 (by rfl) ⟨232691, by rfl⟩ : syracuseStep 310255 = 465383) B465383
theorem B2374703 : Blo 307833 2374703 := bstep (se 1 (by rfl) ⟨1781027, by rfl⟩ : syracuseStep 2374703 = 3562055) B3562055
theorem B4439519 : Blo 307833 4439519 := bstep (se 1 (by rfl) ⟨3329639, by rfl⟩ : syracuseStep 4439519 = 6659279) B6659279
theorem B310751 : Blo 307833 310751 := bstep (se 1 (by rfl) ⟨233063, by rfl⟩ : syracuseStep 310751 = 466127) B466127
theorem B310831 : Blo 307833 310831 := bstep (se 1 (by rfl) ⟨233123, by rfl⟩ : syracuseStep 310831 = 466247) B466247
theorem B310939 : Blo 307833 310939 := bstep (se 1 (by rfl) ⟨233204, by rfl⟩ : syracuseStep 310939 = 466409) B466409
theorem B24592085 : Blo 307833 24592085 := bstep (se 7 (by rfl) ⟨288188, by rfl⟩ : syracuseStep 24592085 = 576377) B576377
theorem B311035 : Blo 307833 311035 := bstep (se 1 (by rfl) ⟨233276, by rfl⟩ : syracuseStep 311035 = 466553) B466553
theorem B311199 : Blo 307833 311199 := bstep (se 1 (by rfl) ⟨233399, by rfl⟩ : syracuseStep 311199 = 466799) B466799
theorem B3522527 : Blo 307833 3522527 := bstep (se 1 (by rfl) ⟨2641895, by rfl⟩ : syracuseStep 3522527 = 5283791) B5283791
theorem B442361 : Blo 307833 442361 := bstep (se 2 (by rfl) ⟨165885, by rfl⟩ : syracuseStep 442361 = 331771) B331771
theorem B1687625 : Blo 307833 1687625 := bstep (se 2 (by rfl) ⟨632859, by rfl⟩ : syracuseStep 1687625 = 1265719) B1265719
theorem B6734015 : Blo 307833 6734015 := bstep (se 1 (by rfl) ⟨5050511, by rfl⟩ : syracuseStep 6734015 = 10101023) B10101023
theorem B311655 : Blo 307833 311655 := bstep (se 1 (by rfl) ⟨233741, by rfl⟩ : syracuseStep 311655 = 467483) B467483
theorem B311775 : Blo 307833 311775 := bstep (se 1 (by rfl) ⟨233831, by rfl⟩ : syracuseStep 311775 = 467663) B467663
theorem B311783 : Blo 307833 311783 := bstep (se 1 (by rfl) ⟨233837, by rfl⟩ : syracuseStep 311783 = 467675) B467675
theorem B836605 : Blo 307833 836605 := bstep (se 3 (by rfl) ⟨156863, by rfl⟩ : syracuseStep 836605 = 313727) B313727
theorem B2245913 : Blo 307833 2245913 := bstep (se 2 (by rfl) ⟨842217, by rfl⟩ : syracuseStep 2245913 = 1684435) B1684435
theorem B7489745 : Blo 307833 7489745 := bstep (se 2 (by rfl) ⟨2808654, by rfl⟩ : syracuseStep 7489745 = 5617309) B5617309
theorem B8964377 : Blo 307833 8964377 := bstep (se 2 (by rfl) ⟨3361641, by rfl⟩ : syracuseStep 8964377 = 6723283) B6723283
theorem B6703397 : Blo 307833 6703397 := bstep (se 4 (by rfl) ⟨628443, by rfl⟩ : syracuseStep 6703397 = 1256887) B1256887
theorem B48548429 : Blo 307833 48548429 := bstep (se 3 (by rfl) ⟨9102830, by rfl⟩ : syracuseStep 48548429 = 18205661) B18205661
theorem B1887031 : Blo 307833 1887031 := bstep (se 1 (by rfl) ⟨1415273, by rfl⟩ : syracuseStep 1887031 = 2830547) B2830547
theorem B3754997 : Blo 307833 3754997 := bstep (se 5 (by rfl) ⟨176015, by rfl⟩ : syracuseStep 3754997 = 352031) B352031
theorem B2968751 : Blo 307833 2968751 := bstep (se 1 (by rfl) ⟨2226563, by rfl⟩ : syracuseStep 2968751 = 4453127) B4453127
theorem B1560383 : Blo 307833 1560383 := bstep (se 1 (by rfl) ⟨1170287, by rfl⟩ : syracuseStep 1560383 = 2340575) B2340575
theorem B348187 : Blo 307833 348187 := bstep (se 1 (by rfl) ⟨261140, by rfl⟩ : syracuseStep 348187 = 522281) B522281
theorem B741803 : Blo 307833 741803 := bstep (se 1 (by rfl) ⟨556352, by rfl⟩ : syracuseStep 741803 = 1112705) B1112705
theorem B3528359 : Blo 307833 3528359 := bstep (se 1 (by rfl) ⟨2646269, by rfl⟩ : syracuseStep 3528359 = 5292539) B5292539
theorem B448583 : Blo 307833 448583 := bstep (se 1 (by rfl) ⟨336437, by rfl⟩ : syracuseStep 448583 = 672875) B672875
theorem B18208961 : Blo 307833 18208961 := bstep (se 2 (by rfl) ⟨6828360, by rfl⟩ : syracuseStep 18208961 = 13656721) B13656721
theorem B350491 : Blo 307833 350491 := bstep (se 1 (by rfl) ⟨262868, by rfl⟩ : syracuseStep 350491 = 525737) B525737
theorem B3529817 : Blo 307833 3529817 := bstep (se 2 (by rfl) ⟨1323681, by rfl⟩ : syracuseStep 3529817 = 2647363) B2647363
theorem B1170683 : Blo 307833 1170683 := bstep (se 1 (by rfl) ⟨878012, by rfl⟩ : syracuseStep 1170683 = 1756025) B1756025
theorem B2973023 : Blo 307833 2973023 := bstep (se 1 (by rfl) ⟨2229767, by rfl⟩ : syracuseStep 2973023 = 4459535) B4459535
theorem B4251953 : Blo 307833 4251953 := bstep (se 2 (by rfl) ⟨1594482, by rfl⟩ : syracuseStep 4251953 = 3188965) B3188965
theorem B877979 : Blo 307833 877979 := bstep (se 1 (by rfl) ⟨658484, by rfl⟩ : syracuseStep 877979 = 1316969) B1316969
theorem B50652971 : Blo 307833 50652971 := bstep (se 1 (by rfl) ⟨37989728, by rfl⟩ : syracuseStep 50652971 = 75979457) B75979457
theorem B5334983 : Blo 307833 5334983 := bstep (se 1 (by rfl) ⟨4001237, by rfl⟩ : syracuseStep 5334983 = 8002475) B8002475
theorem B780263 : Blo 307833 780263 := bstep (se 1 (by rfl) ⟨585197, by rfl⟩ : syracuseStep 780263 = 1170395) B1170395
theorem B1173599 : Blo 307833 1173599 := bstep (se 1 (by rfl) ⟨880199, by rfl⟩ : syracuseStep 1173599 = 1760399) B1760399
theorem B780779 : Blo 307833 780779 := bstep (se 1 (by rfl) ⟨585584, by rfl⟩ : syracuseStep 780779 = 1171169) B1171169
theorem B6810113 : Blo 307833 6810113 := bstep (se 2 (by rfl) ⟨2553792, by rfl⟩ : syracuseStep 6810113 = 5107585) B5107585
theorem B780961 : Blo 307833 780961 := bstep (se 2 (by rfl) ⟨292860, by rfl⟩ : syracuseStep 780961 = 585721) B585721
theorem B1174283 : Blo 307833 1174283 := bstep (se 1 (by rfl) ⟨880712, by rfl⟩ : syracuseStep 1174283 = 1761425) B1761425
theorem B2222873 : Blo 307833 2222873 := bstep (se 2 (by rfl) ⟨833577, by rfl⟩ : syracuseStep 2222873 = 1667155) B1667155
theorem B846617 : Blo 307833 846617 := bstep (se 2 (by rfl) ⟨317481, by rfl⟩ : syracuseStep 846617 = 634963) B634963
theorem B1043225 : Blo 307833 1043225 := bstep (se 2 (by rfl) ⟨391209, by rfl⟩ : syracuseStep 1043225 = 782419) B782419
theorem B1174297 : Blo 307833 1174297 := bstep (se 2 (by rfl) ⟨440361, by rfl⟩ : syracuseStep 1174297 = 880723) B880723
theorem B1043603 : Blo 307833 1043603 := bstep (se 1 (by rfl) ⟨782702, by rfl⟩ : syracuseStep 1043603 = 1565405) B1565405
theorem B4746761 : Blo 307833 4746761 := bstep (se 2 (by rfl) ⟨1780035, by rfl⟩ : syracuseStep 4746761 = 3560071) B3560071
theorem B945851 : Blo 307833 945851 := bstep (se 1 (by rfl) ⟨709388, by rfl⟩ : syracuseStep 945851 = 1418777) B1418777
theorem B585569 : Blo 307833 585569 := bstep (se 2 (by rfl) ⟨219588, by rfl⟩ : syracuseStep 585569 = 439177) B439177
theorem B1175543 : Blo 307833 1175543 := bstep (se 1 (by rfl) ⟨881657, by rfl⟩ : syracuseStep 1175543 = 1763315) B1763315
theorem B3633547 : Blo 307833 3633547 := bstep (se 1 (by rfl) ⟨2725160, by rfl⟩ : syracuseStep 3633547 = 5450321) B5450321
theorem B782905 : Blo 307833 782905 := bstep (se 2 (by rfl) ⟨293589, by rfl⟩ : syracuseStep 782905 = 587179) B587179
theorem B783067 : Blo 307833 783067 := bstep (se 1 (by rfl) ⟨587300, by rfl⟩ : syracuseStep 783067 = 1174601) B1174601
theorem B3535649 : Blo 307833 3535649 := bstep (se 2 (by rfl) ⟨1325868, by rfl⟩ : syracuseStep 3535649 = 2651737) B2651737
theorem B783209 : Blo 307833 783209 := bstep (se 2 (by rfl) ⟨293703, by rfl⟩ : syracuseStep 783209 = 587407) B587407
theorem B521383 : Blo 307833 521383 := bstep (se 1 (by rfl) ⟨391037, by rfl⟩ : syracuseStep 521383 = 782075) B782075
theorem B15332647 : Blo 307833 15332647 := bstep (se 1 (by rfl) ⟨11499485, by rfl⟩ : syracuseStep 15332647 = 22998971) B22998971
theorem B184251743 : Blo 307833 184251743 := bstep (se 1 (by rfl) ⟨138188807, by rfl⟩ : syracuseStep 184251743 = 276377615) B276377615
theorem B784039 : Blo 307833 784039 := bstep (se 1 (by rfl) ⟨588029, by rfl⟩ : syracuseStep 784039 = 1176059) B1176059
theorem B1046249 : Blo 307833 1046249 := bstep (se 2 (by rfl) ⟨392343, by rfl⟩ : syracuseStep 1046249 = 784687) B784687
theorem B1046303 : Blo 307833 1046303 := bstep (se 1 (by rfl) ⟨784727, by rfl⟩ : syracuseStep 1046303 = 1569455) B1569455
theorem B784505 : Blo 307833 784505 := bstep (se 2 (by rfl) ⟨294189, by rfl⟩ : syracuseStep 784505 = 588379) B588379
theorem B3537107 : Blo 307833 3537107 := bstep (se 1 (by rfl) ⟨2652830, by rfl⟩ : syracuseStep 3537107 = 5305661) B5305661
theorem B522551 : Blo 307833 522551 := bstep (se 1 (by rfl) ⟨391913, by rfl⟩ : syracuseStep 522551 = 783827) B783827
theorem B784799 : Blo 307833 784799 := bstep (se 1 (by rfl) ⟨588599, by rfl⟩ : syracuseStep 784799 = 1177199) B1177199
theorem B1768007 : Blo 307833 1768007 := bstep (se 1 (by rfl) ⟨1326005, by rfl⟩ : syracuseStep 1768007 = 2652011) B2652011
theorem B3373841 : Blo 307833 3373841 := bstep (se 2 (by rfl) ⟨1265190, by rfl⟩ : syracuseStep 3373841 = 2530381) B2530381
theorem B1178459 : Blo 307833 1178459 := bstep (se 1 (by rfl) ⟨883844, by rfl⟩ : syracuseStep 1178459 = 1767689) B1767689
theorem B1178657 : Blo 307833 1178657 := bstep (se 2 (by rfl) ⟨441996, by rfl⟩ : syracuseStep 1178657 = 883993) B883993
theorem B883867 : Blo 307833 883867 := bstep (se 1 (by rfl) ⟨662900, by rfl⟩ : syracuseStep 883867 = 1325801) B1325801
theorem B392683 : Blo 307833 392683 := bstep (se 1 (by rfl) ⟨294512, by rfl⟩ : syracuseStep 392683 = 589025) B589025
theorem B785983 : Blo 307833 785983 := bstep (se 1 (by rfl) ⟨589487, by rfl⟩ : syracuseStep 785983 = 1178975) B1178975
theorem B1048247 : Blo 307833 1048247 := bstep (se 1 (by rfl) ⟨786185, by rfl⟩ : syracuseStep 1048247 = 1572371) B1572371
theorem B524063 : Blo 307833 524063 := bstep (se 1 (by rfl) ⟨393047, by rfl⟩ : syracuseStep 524063 = 786095) B786095
theorem B786287 : Blo 307833 786287 := bstep (se 1 (by rfl) ⟨589715, by rfl⟩ : syracuseStep 786287 = 1179431) B1179431
theorem B4489343 : Blo 307833 4489343 := bstep (se 1 (by rfl) ⟨3367007, by rfl⟩ : syracuseStep 4489343 = 6734015) B6734015
theorem B2228471 : Blo 307833 2228471 := bstep (se 1 (by rfl) ⟨1671353, by rfl⟩ : syracuseStep 2228471 = 3342707) B3342707
theorem B1179947 : Blo 307833 1179947 := bstep (se 1 (by rfl) ⟨884960, by rfl⟩ : syracuseStep 1179947 = 1769921) B1769921
theorem B525055 : Blo 307833 525055 := bstep (se 1 (by rfl) ⟨393791, by rfl⟩ : syracuseStep 525055 = 787583) B787583
theorem B1049435 : Blo 307833 1049435 := bstep (se 1 (by rfl) ⟨787076, by rfl⟩ : syracuseStep 1049435 = 1574153) B1574153
theorem B394075 : Blo 307833 394075 := bstep (se 1 (by rfl) ⟨295556, by rfl⟩ : syracuseStep 394075 = 591113) B591113
theorem B525467 : Blo 307833 525467 := bstep (se 1 (by rfl) ⟨394100, by rfl⟩ : syracuseStep 525467 = 788201) B788201
theorem B525575 : Blo 307833 525575 := bstep (se 1 (by rfl) ⟨394181, by rfl⟩ : syracuseStep 525575 = 788363) B788363
theorem B1115473 : Blo 307833 1115473 := bstep (se 2 (by rfl) ⟨418302, by rfl⟩ : syracuseStep 1115473 = 836605) B836605
theorem B591599 : Blo 307833 591599 := bstep (se 1 (by rfl) ⟨443699, by rfl⟩ : syracuseStep 591599 = 887399) B887399
theorem B789223 : Blo 307833 789223 := bstep (se 1 (by rfl) ⟨591917, by rfl⟩ : syracuseStep 789223 = 1183835) B1183835
theorem B461855 : Blo 307833 461855 := bstep (se 1 (by rfl) ⟨346391, by rfl⟩ : syracuseStep 461855 = 692783) B692783
theorem B1182863 : Blo 307833 1182863 := bstep (se 1 (by rfl) ⟨887147, by rfl⟩ : syracuseStep 1182863 = 1774295) B1774295
theorem B658697 : Blo 307833 658697 := bstep (se 2 (by rfl) ⟨247011, by rfl⟩ : syracuseStep 658697 = 494023) B494023
theorem B462239 : Blo 307833 462239 := bstep (se 1 (by rfl) ⟨346679, by rfl⟩ : syracuseStep 462239 = 693359) B693359
theorem B462287 : Blo 307833 462287 := bstep (se 1 (by rfl) ⟨346715, by rfl⟩ : syracuseStep 462287 = 693431) B693431
theorem B463259 : Blo 307833 463259 := bstep (se 1 (by rfl) ⟨347444, by rfl⟩ : syracuseStep 463259 = 694889) B694889
theorem B463679 : Blo 307833 463679 := bstep (se 1 (by rfl) ⟨347759, by rfl⟩ : syracuseStep 463679 = 695519) B695519
theorem B1316027 : Blo 307833 1316027 := bstep (se 1 (by rfl) ⟨987020, by rfl⟩ : syracuseStep 1316027 = 1974041) B1974041
theorem B1053931 : Blo 307833 1053931 := bstep (se 1 (by rfl) ⟨790448, by rfl⟩ : syracuseStep 1053931 = 1580897) B1580897
theorem B464249 : Blo 307833 464249 := bstep (se 2 (by rfl) ⟨174093, by rfl⟩ : syracuseStep 464249 = 348187) B348187
theorem B660919 : Blo 307833 660919 := bstep (se 1 (by rfl) ⟨495689, by rfl⟩ : syracuseStep 660919 = 991379) B991379
theorem B1578527 : Blo 307833 1578527 := bstep (se 1 (by rfl) ⟨1183895, by rfl⟩ : syracuseStep 1578527 = 2367791) B2367791
theorem B2233919 : Blo 307833 2233919 := bstep (se 1 (by rfl) ⟨1675439, by rfl⟩ : syracuseStep 2233919 = 3350879) B3350879
theorem B464795 : Blo 307833 464795 := bstep (se 1 (by rfl) ⟨348596, by rfl⟩ : syracuseStep 464795 = 697193) B697193
theorem B3250601 : Blo 307833 3250601 := bstep (se 2 (by rfl) ⟨1218975, by rfl⟩ : syracuseStep 3250601 = 2437951) B2437951
theorem B465455 : Blo 307833 465455 := bstep (se 1 (by rfl) ⟨349091, by rfl⟩ : syracuseStep 465455 = 698183) B698183
theorem B465503 : Blo 307833 465503 := bstep (se 1 (by rfl) ⟨349127, by rfl⟩ : syracuseStep 465503 = 698255) B698255
theorem B18160301 : Blo 307833 18160301 := bstep (se 3 (by rfl) ⟨3405056, by rfl⟩ : syracuseStep 18160301 = 6810113) B6810113
theorem B662251 : Blo 307833 662251 := bstep (se 1 (by rfl) ⟨496688, by rfl⟩ : syracuseStep 662251 = 993377) B993377
theorem B695177 : Blo 307833 695177 := bstep (se 2 (by rfl) ⟨260691, by rfl⟩ : syracuseStep 695177 = 521383) B521383
theorem B465863 : Blo 307833 465863 := bstep (se 1 (by rfl) ⟨349397, by rfl⟩ : syracuseStep 465863 = 698795) B698795
theorem B465983 : Blo 307833 465983 := bstep (se 1 (by rfl) ⟨349487, by rfl⟩ : syracuseStep 465983 = 698975) B698975
theorem B2825293 : Blo 307833 2825293 := bstep (se 3 (by rfl) ⟨529742, by rfl⟩ : syracuseStep 2825293 = 1059485) B1059485
theorem B1481915 : Blo 307833 1481915 := bstep (se 1 (by rfl) ⟨1111436, by rfl⟩ : syracuseStep 1481915 = 2222873) B2222873
theorem B695483 : Blo 307833 695483 := bstep (se 1 (by rfl) ⟨521612, by rfl⟩ : syracuseStep 695483 = 1043225) B1043225
theorem B1056041 : Blo 307833 1056041 := bstep (se 2 (by rfl) ⟨396015, by rfl⟩ : syracuseStep 1056041 = 792031) B792031
theorem B466223 : Blo 307833 466223 := bstep (se 1 (by rfl) ⟨349667, by rfl⟩ : syracuseStep 466223 = 699335) B699335
theorem B695735 : Blo 307833 695735 := bstep (se 1 (by rfl) ⟨521801, by rfl⟩ : syracuseStep 695735 = 1043603) B1043603
theorem B466463 : Blo 307833 466463 := bstep (se 1 (by rfl) ⟨349847, by rfl⟩ : syracuseStep 466463 = 699695) B699695
theorem B466487 : Blo 307833 466487 := bstep (se 1 (by rfl) ⟨349865, by rfl⟩ : syracuseStep 466487 = 699731) B699731
theorem B466655 : Blo 307833 466655 := bstep (se 1 (by rfl) ⟨349991, by rfl⟩ : syracuseStep 466655 = 699983) B699983
theorem B466847 : Blo 307833 466847 := bstep (se 1 (by rfl) ⟨350135, by rfl⟩ : syracuseStep 466847 = 700271) B700271
theorem B467015 : Blo 307833 467015 := bstep (se 1 (by rfl) ⟨350261, by rfl⟩ : syracuseStep 467015 = 700523) B700523
theorem B467135 : Blo 307833 467135 := bstep (se 1 (by rfl) ⟨350351, by rfl⟩ : syracuseStep 467135 = 700703) B700703
theorem B467321 : Blo 307833 467321 := bstep (se 2 (by rfl) ⟨175245, by rfl⟩ : syracuseStep 467321 = 350491) B350491
theorem B467615 : Blo 307833 467615 := bstep (se 1 (by rfl) ⟨350711, by rfl⟩ : syracuseStep 467615 = 701423) B701423
theorem B697499 : Blo 307833 697499 := bstep (se 1 (by rfl) ⟨523124, by rfl⟩ : syracuseStep 697499 = 1046249) B1046249
theorem B697535 : Blo 307833 697535 := bstep (se 1 (by rfl) ⟨523151, by rfl⟩ : syracuseStep 697535 = 1046303) B1046303
theorem B1583135 : Blo 307833 1583135 := bstep (se 1 (by rfl) ⟨1187351, by rfl⟩ : syracuseStep 1583135 = 2374703) B2374703
theorem B2959679 : Blo 307833 2959679 := bstep (se 1 (by rfl) ⟨2219759, by rfl⟩ : syracuseStep 2959679 = 4439519) B4439519
theorem B698831 : Blo 307833 698831 := bstep (se 1 (by rfl) ⟨524123, by rfl⟩ : syracuseStep 698831 = 1048247) B1048247
theorem B16394723 : Blo 307833 16394723 := bstep (se 1 (by rfl) ⟨12296042, by rfl⟩ : syracuseStep 16394723 = 24592085) B24592085
theorem B1125083 : Blo 307833 1125083 := bstep (se 1 (by rfl) ⟨843812, by rfl⟩ : syracuseStep 1125083 = 1687625) B1687625
theorem B502895 : Blo 307833 502895 := bstep (se 1 (by rfl) ⟨377171, by rfl⟩ : syracuseStep 502895 = 754343) B754343
theorem B4993163 : Blo 307833 4993163 := bstep (se 1 (by rfl) ⟨3744872, by rfl⟩ : syracuseStep 4993163 = 7489745) B7489745
theorem B2502809 : Blo 307833 2502809 := bstep (se 2 (by rfl) ⟨938553, by rfl⟩ : syracuseStep 2502809 = 1877107) B1877107
theorem B5976251 : Blo 307833 5976251 := bstep (se 1 (by rfl) ⟨4482188, by rfl⟩ : syracuseStep 5976251 = 8964377) B8964377
theorem B4468931 : Blo 307833 4468931 := bstep (se 1 (by rfl) ⟨3351698, by rfl⟩ : syracuseStep 4468931 = 6703397) B6703397
theorem B2503331 : Blo 307833 2503331 := bstep (se 1 (by rfl) ⟨1877498, by rfl⟩ : syracuseStep 2503331 = 3754997) B3754997
theorem B701135 : Blo 307833 701135 := bstep (se 1 (by rfl) ⟨525851, by rfl⟩ : syracuseStep 701135 = 1051703) B1051703
theorem B307943 : Blo 307833 307943 := bstep (se 1 (by rfl) ⟨230957, by rfl⟩ : syracuseStep 307943 = 461915) B461915
theorem B307995 : Blo 307833 307995 := bstep (se 1 (by rfl) ⟨230996, by rfl⟩ : syracuseStep 307995 = 461993) B461993
theorem B1979167 : Blo 307833 1979167 := bstep (se 1 (by rfl) ⟨1484375, by rfl⟩ : syracuseStep 1979167 = 2968751) B2968751
theorem B1324025 : Blo 307833 1324025 := bstep (se 2 (by rfl) ⟨496509, by rfl⟩ : syracuseStep 1324025 = 993019) B993019
theorem B308271 : Blo 307833 308271 := bstep (se 1 (by rfl) ⟨231203, by rfl⟩ : syracuseStep 308271 = 462407) B462407
theorem B308391 : Blo 307833 308391 := bstep (se 1 (by rfl) ⟨231293, by rfl⟩ : syracuseStep 308391 = 462587) B462587
theorem B308551 : Blo 307833 308551 := bstep (se 1 (by rfl) ⟨231413, by rfl⟩ : syracuseStep 308551 = 462827) B462827
theorem B309243 : Blo 307833 309243 := bstep (se 1 (by rfl) ⟨231932, by rfl⟩ : syracuseStep 309243 = 463865) B463865
theorem B309375 : Blo 307833 309375 := bstep (se 1 (by rfl) ⟨232031, by rfl⟩ : syracuseStep 309375 = 464063) B464063
theorem B309471 : Blo 307833 309471 := bstep (se 1 (by rfl) ⟨232103, by rfl⟩ : syracuseStep 309471 = 464207) B464207
theorem B309531 : Blo 307833 309531 := bstep (se 1 (by rfl) ⟨232148, by rfl⟩ : syracuseStep 309531 = 464297) B464297
theorem B309567 : Blo 307833 309567 := bstep (se 1 (by rfl) ⟨232175, by rfl⟩ : syracuseStep 309567 = 464351) B464351
theorem B309631 : Blo 307833 309631 := bstep (se 1 (by rfl) ⟨232223, by rfl⟩ : syracuseStep 309631 = 464447) B464447
theorem B2636225 : Blo 307833 2636225 := bstep (se 2 (by rfl) ⟨988584, by rfl⟩ : syracuseStep 2636225 = 1977169) B1977169
theorem B309951 : Blo 307833 309951 := bstep (se 1 (by rfl) ⟨232463, by rfl⟩ : syracuseStep 309951 = 464927) B464927
theorem B12139307 : Blo 307833 12139307 := bstep (se 1 (by rfl) ⟨9104480, by rfl⟩ : syracuseStep 12139307 = 18208961) B18208961
theorem B310239 : Blo 307833 310239 := bstep (se 1 (by rfl) ⟨232679, by rfl⟩ : syracuseStep 310239 = 465359) B465359
theorem B310299 : Blo 307833 310299 := bstep (se 1 (by rfl) ⟨232724, by rfl⟩ : syracuseStep 310299 = 465449) B465449
theorem B7912565 : Blo 307833 7912565 := bstep (se 5 (by rfl) ⟨370901, by rfl⟩ : syracuseStep 7912565 = 741803) B741803
theorem B310439 : Blo 307833 310439 := bstep (se 1 (by rfl) ⟨232829, by rfl⟩ : syracuseStep 310439 = 465659) B465659
theorem B310523 : Blo 307833 310523 := bstep (se 1 (by rfl) ⟨232892, by rfl⟩ : syracuseStep 310523 = 465785) B465785
theorem B1982015 : Blo 307833 1982015 := bstep (se 1 (by rfl) ⟨1486511, by rfl⟩ : syracuseStep 1982015 = 2973023) B2973023
theorem B2670191 : Blo 307833 2670191 := bstep (se 1 (by rfl) ⟨2002643, by rfl⟩ : syracuseStep 2670191 = 4005287) B4005287
theorem B311023 : Blo 307833 311023 := bstep (se 1 (by rfl) ⟨233267, by rfl⟩ : syracuseStep 311023 = 466535) B466535
theorem B311131 : Blo 307833 311131 := bstep (se 1 (by rfl) ⟨233348, by rfl⟩ : syracuseStep 311131 = 466697) B466697
theorem B5947343 : Blo 307833 5947343 := bstep (se 1 (by rfl) ⟨4460507, by rfl⟩ : syracuseStep 5947343 = 8921015) B8921015
theorem B311279 : Blo 307833 311279 := bstep (se 1 (by rfl) ⟨233459, by rfl⟩ : syracuseStep 311279 = 466919) B466919
theorem B311359 : Blo 307833 311359 := bstep (se 1 (by rfl) ⟨233519, by rfl⟩ : syracuseStep 311359 = 467039) B467039
theorem B311399 : Blo 307833 311399 := bstep (se 1 (by rfl) ⟨233549, by rfl⟩ : syracuseStep 311399 = 467099) B467099
theorem B311455 : Blo 307833 311455 := bstep (se 1 (by rfl) ⟨233591, by rfl⟩ : syracuseStep 311455 = 467183) B467183
theorem B2113721 : Blo 307833 2113721 := bstep (se 2 (by rfl) ⟨792645, by rfl⟩ : syracuseStep 2113721 = 1585291) B1585291
theorem B1196221 : Blo 307833 1196221 := bstep (se 3 (by rfl) ⟨224291, by rfl⟩ : syracuseStep 1196221 = 448583) B448583
theorem B2834635 : Blo 307833 2834635 := bstep (se 1 (by rfl) ⟨2125976, by rfl⟩ : syracuseStep 2834635 = 4251953) B4251953
theorem B3784967 : Blo 307833 3784967 := bstep (se 1 (by rfl) ⟨2838725, by rfl⟩ : syracuseStep 3784967 = 5677451) B5677451
theorem B4243751 : Blo 307833 4243751 := bstep (se 1 (by rfl) ⟨3182813, by rfl⟩ : syracuseStep 4243751 = 6365627) B6365627
theorem B311707 : Blo 307833 311707 := bstep (se 1 (by rfl) ⟨233780, by rfl⟩ : syracuseStep 311707 = 467561) B467561
theorem B311711 : Blo 307833 311711 := bstep (se 1 (by rfl) ⟨233783, by rfl⟩ : syracuseStep 311711 = 467567) B467567
theorem B4244071 : Blo 307833 4244071 := bstep (se 1 (by rfl) ⟨3183053, by rfl⟩ : syracuseStep 4244071 = 6366107) B6366107
theorem B33768647 : Blo 307833 33768647 := bstep (se 1 (by rfl) ⟨25326485, by rfl⟩ : syracuseStep 33768647 = 50652971) B50652971
theorem B3556655 : Blo 307833 3556655 := bstep (se 1 (by rfl) ⟨2667491, by rfl⟩ : syracuseStep 3556655 = 5334983) B5334983
theorem B1885673 : Blo 307833 1885673 := bstep (se 2 (by rfl) ⟨707127, by rfl⟩ : syracuseStep 1885673 = 1414255) B1414255
theorem B3164507 : Blo 307833 3164507 := bstep (se 1 (by rfl) ⟨2373380, by rfl⟩ : syracuseStep 3164507 = 4746761) B4746761
theorem B2345435 : Blo 307833 2345435 := bstep (se 1 (by rfl) ⟨1759076, by rfl⟩ : syracuseStep 2345435 = 3518153) B3518153
theorem B1329817 : Blo 307833 1329817 := bstep (se 2 (by rfl) ⟨498681, by rfl⟩ : syracuseStep 1329817 = 997363) B997363
theorem B3328735 : Blo 307833 3328735 := bstep (se 1 (by rfl) ⟨2496551, by rfl⟩ : syracuseStep 3328735 = 4993103) B4993103
theorem B122834495 : Blo 307833 122834495 := bstep (se 1 (by rfl) ⟨92125871, by rfl⟩ : syracuseStep 122834495 = 184251743) B184251743
theorem B348367 : Blo 307833 348367 := bstep (se 1 (by rfl) ⟨261275, by rfl⟩ : syracuseStep 348367 = 522551) B522551
theorem B512335 : Blo 307833 512335 := bstep (se 1 (by rfl) ⟨384251, by rfl⟩ : syracuseStep 512335 = 768503) B768503
theorem B2249227 : Blo 307833 2249227 := bstep (se 1 (by rfl) ⟨1686920, by rfl⟩ : syracuseStep 2249227 = 3373841) B3373841
theorem B1561517 : Blo 307833 1561517 := bstep (se 3 (by rfl) ⟨292784, by rfl⟩ : syracuseStep 1561517 = 585569) B585569
theorem B349375 : Blo 307833 349375 := bstep (se 1 (by rfl) ⟨262031, by rfl⟩ : syracuseStep 349375 = 524063) B524063
theorem B2348351 : Blo 307833 2348351 := bstep (se 1 (by rfl) ⟨1761263, by rfl⟩ : syracuseStep 2348351 = 3522527) B3522527
theorem B1890145 : Blo 307833 1890145 := bstep (se 2 (by rfl) ⟨708804, by rfl⟩ : syracuseStep 1890145 = 1417609) B1417609
theorem B1497275 : Blo 307833 1497275 := bstep (se 1 (by rfl) ⟨1122956, by rfl⟩ : syracuseStep 1497275 = 2245913) B2245913
theorem B32365619 : Blo 307833 32365619 := bstep (se 1 (by rfl) ⟨24274214, by rfl⟩ : syracuseStep 32365619 = 48548429) B48548429
theorem B1040255 : Blo 307833 1040255 := bstep (se 1 (by rfl) ⟨780191, by rfl⟩ : syracuseStep 1040255 = 1560383) B1560383
theorem B1041281 : Blo 307833 1041281 := bstep (se 2 (by rfl) ⟨390480, by rfl⟩ : syracuseStep 1041281 = 780961) B780961
theorem B1565729 : Blo 307833 1565729 := bstep (se 2 (by rfl) ⟨587148, by rfl⟩ : syracuseStep 1565729 = 1174297) B1174297
theorem B2516041 : Blo 307833 2516041 := bstep (se 2 (by rfl) ⟨943515, by rfl⟩ : syracuseStep 2516041 = 1887031) B1887031
theorem B2352239 : Blo 307833 2352239 := bstep (se 1 (by rfl) ⟨1764179, by rfl⟩ : syracuseStep 2352239 = 3528359) B3528359
theorem B8513437 : Blo 307833 8513437 := bstep (se 3 (by rfl) ⟨1596269, by rfl⟩ : syracuseStep 8513437 = 3192539) B3192539
theorem B2353211 : Blo 307833 2353211 := bstep (se 1 (by rfl) ⟨1764908, by rfl⟩ : syracuseStep 2353211 = 3529817) B3529817
theorem B780455 : Blo 307833 780455 := bstep (se 1 (by rfl) ⟨585341, by rfl⟩ : syracuseStep 780455 = 1170683) B1170683
theorem B879265 : Blo 307833 879265 := bstep (se 2 (by rfl) ⟨329724, by rfl⟩ : syracuseStep 879265 = 659449) B659449
theorem B3959927 : Blo 307833 3959927 := bstep (se 1 (by rfl) ⟨2969945, by rfl⟩ : syracuseStep 3959927 = 5939891) B5939891
theorem B4844729 : Blo 307833 4844729 := bstep (se 2 (by rfl) ⟨1816773, by rfl⟩ : syracuseStep 4844729 = 3633547) B3633547
theorem B1043873 : Blo 307833 1043873 := bstep (se 2 (by rfl) ⟨391452, by rfl⟩ : syracuseStep 1043873 = 782905) B782905
theorem B585319 : Blo 307833 585319 := bstep (se 1 (by rfl) ⟨438989, by rfl⟩ : syracuseStep 585319 = 877979) B877979
theorem B1044089 : Blo 307833 1044089 := bstep (se 2 (by rfl) ⟨391533, by rfl⟩ : syracuseStep 1044089 = 783067) B783067
theorem B520175 : Blo 307833 520175 := bstep (se 1 (by rfl) ⟨390131, by rfl⟩ : syracuseStep 520175 = 780263) B780263
theorem B782399 : Blo 307833 782399 := bstep (se 1 (by rfl) ⟨586799, by rfl⟩ : syracuseStep 782399 = 1173599) B1173599
theorem B520519 : Blo 307833 520519 := bstep (se 1 (by rfl) ⟨390389, by rfl⟩ : syracuseStep 520519 = 780779) B780779
theorem B20443529 : Blo 307833 20443529 := bstep (se 2 (by rfl) ⟨7666323, by rfl⟩ : syracuseStep 20443529 = 15332647) B15332647
theorem B782855 : Blo 307833 782855 := bstep (se 1 (by rfl) ⟨587141, by rfl⟩ : syracuseStep 782855 = 1174283) B1174283
theorem B1340011 : Blo 307833 1340011 := bstep (se 1 (by rfl) ⟨1005008, by rfl⟩ : syracuseStep 1340011 = 2010017) B2010017
theorem B2257645 : Blo 307833 2257645 := bstep (se 3 (by rfl) ⟨423308, by rfl⟩ : syracuseStep 2257645 = 846617) B846617
theorem B1045385 : Blo 307833 1045385 := bstep (se 2 (by rfl) ⟨392019, by rfl⟩ : syracuseStep 1045385 = 784039) B784039
theorem B881567 : Blo 307833 881567 := bstep (se 1 (by rfl) ⟨661175, by rfl⟩ : syracuseStep 881567 = 1322351) B1322351
theorem B4223927 : Blo 307833 4223927 := bstep (se 1 (by rfl) ⟨3167945, by rfl⟩ : syracuseStep 4223927 = 6335891) B6335891
theorem B783695 : Blo 307833 783695 := bstep (se 1 (by rfl) ⟨587771, by rfl⟩ : syracuseStep 783695 = 1175543) B1175543
theorem B882409 : Blo 307833 882409 := bstep (se 2 (by rfl) ⟨330903, by rfl⟩ : syracuseStep 882409 = 661807) B661807
theorem B2357099 : Blo 307833 2357099 := bstep (se 1 (by rfl) ⟨1767824, by rfl⟩ : syracuseStep 2357099 = 3535649) B3535649
theorem B522139 : Blo 307833 522139 := bstep (se 1 (by rfl) ⟨391604, by rfl⟩ : syracuseStep 522139 = 783209) B783209
theorem B882809 : Blo 307833 882809 := bstep (se 2 (by rfl) ⟨331053, by rfl⟩ : syracuseStep 882809 = 662107) B662107
theorem B1669319 : Blo 307833 1669319 := bstep (se 1 (by rfl) ⟨1251989, by rfl⟩ : syracuseStep 1669319 = 2503979) B2503979
theorem B523003 : Blo 307833 523003 := bstep (se 1 (by rfl) ⟨392252, by rfl⟩ : syracuseStep 523003 = 784505) B784505
theorem B2358071 : Blo 307833 2358071 := bstep (se 1 (by rfl) ⟨1768553, by rfl⟩ : syracuseStep 2358071 = 3537107) B3537107
theorem B1178489 : Blo 307833 1178489 := bstep (se 2 (by rfl) ⟨441933, by rfl⟩ : syracuseStep 1178489 = 883867) B883867
theorem B523199 : Blo 307833 523199 := bstep (se 1 (by rfl) ⟨392399, by rfl⟩ : syracuseStep 523199 = 784799) B784799
theorem B1178671 : Blo 307833 1178671 := bstep (se 1 (by rfl) ⟨884003, by rfl⟩ : syracuseStep 1178671 = 1768007) B1768007
theorem B2522269 : Blo 307833 2522269 := bstep (se 3 (by rfl) ⟨472925, by rfl⟩ : syracuseStep 2522269 = 945851) B945851
theorem B785639 : Blo 307833 785639 := bstep (se 1 (by rfl) ⟨589229, by rfl⟩ : syracuseStep 785639 = 1178459) B1178459
theorem B523577 : Blo 307833 523577 := bstep (se 2 (by rfl) ⟨196341, by rfl⟩ : syracuseStep 523577 = 392683) B392683
theorem B785771 : Blo 307833 785771 := bstep (se 1 (by rfl) ⟨589328, by rfl⟩ : syracuseStep 785771 = 1178657) B1178657
theorem B1047977 : Blo 307833 1047977 := bstep (se 2 (by rfl) ⟨392991, by rfl⟩ : syracuseStep 1047977 = 785983) B785983
theorem B524191 : Blo 307833 524191 := bstep (se 1 (by rfl) ⟨393143, by rfl⟩ : syracuseStep 524191 = 786287) B786287
theorem B1179629 : Blo 307833 1179629 := bstep (se 3 (by rfl) ⟨221180, by rfl⟩ : syracuseStep 1179629 = 442361) B442361
theorem B1409147 : Blo 307833 1409147 := bstep (se 1 (by rfl) ⟨1056860, by rfl⟩ : syracuseStep 1409147 = 2113721) B2113721
theorem B2523311 : Blo 307833 2523311 := bstep (se 1 (by rfl) ⟨1892483, by rfl⟩ : syracuseStep 2523311 = 3784967) B3784967
theorem B786631 : Blo 307833 786631 := bstep (se 1 (by rfl) ⟨589973, by rfl⟩ : syracuseStep 786631 = 1179947) B1179947
theorem B22512431 : Blo 307833 22512431 := bstep (se 1 (by rfl) ⟨16884323, by rfl⟩ : syracuseStep 22512431 = 33768647) B33768647
theorem B525433 : Blo 307833 525433 := bstep (se 2 (by rfl) ⟨197037, by rfl⟩ : syracuseStep 525433 = 394075) B394075
theorem B394399 : Blo 307833 394399 := bstep (se 1 (by rfl) ⟨295799, by rfl⟩ : syracuseStep 394399 = 591599) B591599
theorem B788575 : Blo 307833 788575 := bstep (se 1 (by rfl) ⟨591431, by rfl⟩ : syracuseStep 788575 = 1182863) B1182863
theorem B81889663 : Blo 307833 81889663 := bstep (se 1 (by rfl) ⟨61417247, by rfl⟩ : syracuseStep 81889663 = 122834495) B122834495
theorem B11995877 : Blo 307833 11995877 := bstep (se 4 (by rfl) ⟨1124613, by rfl⟩ : syracuseStep 11995877 = 2249227) B2249227
theorem B3509405 : Blo 307833 3509405 := bstep (se 3 (by rfl) ⟨658013, by rfl⟩ : syracuseStep 3509405 = 1316027) B1316027
theorem B1773089 : Blo 307833 1773089 := bstep (se 2 (by rfl) ⟨664908, by rfl⟩ : syracuseStep 1773089 = 1329817) B1329817
theorem B1052297 : Blo 307833 1052297 := bstep (se 2 (by rfl) ⟨394611, by rfl⟩ : syracuseStep 1052297 = 789223) B789223
theorem B1052351 : Blo 307833 1052351 := bstep (se 1 (by rfl) ⟨789263, by rfl⟩ : syracuseStep 1052351 = 1578527) B1578527
theorem B2167067 : Blo 307833 2167067 := bstep (se 1 (by rfl) ⟨1625300, by rfl⟩ : syracuseStep 2167067 = 3250601) B3250601
theorem B463451 : Blo 307833 463451 := bstep (se 1 (by rfl) ⟨347588, by rfl⟩ : syracuseStep 463451 = 695177) B695177
theorem B463655 : Blo 307833 463655 := bstep (se 1 (by rfl) ⟨347741, by rfl⟩ : syracuseStep 463655 = 695483) B695483
theorem B463823 : Blo 307833 463823 := bstep (se 1 (by rfl) ⟨347867, by rfl⟩ : syracuseStep 463823 = 695735) B695735
theorem B693503 : Blo 307833 693503 := bstep (se 1 (by rfl) ⟨520127, by rfl⟩ : syracuseStep 693503 = 1040255) B1040255
theorem B464489 : Blo 307833 464489 := bstep (se 2 (by rfl) ⟨174183, by rfl⟩ : syracuseStep 464489 = 348367) B348367
theorem B694025 : Blo 307833 694025 := bstep (se 2 (by rfl) ⟨260259, by rfl⟩ : syracuseStep 694025 = 520519) B520519
theorem B694187 : Blo 307833 694187 := bstep (se 1 (by rfl) ⟨520640, by rfl⟩ : syracuseStep 694187 = 1041281) B1041281
theorem B464999 : Blo 307833 464999 := bstep (se 1 (by rfl) ⟨348749, by rfl⟩ : syracuseStep 464999 = 697499) B697499
theorem B465023 : Blo 307833 465023 := bstep (se 1 (by rfl) ⟨348767, by rfl⟩ : syracuseStep 465023 = 697535) B697535
theorem B1055423 : Blo 307833 1055423 := bstep (se 1 (by rfl) ⟨791567, by rfl⟩ : syracuseStep 1055423 = 1583135) B1583135
theorem B1973119 : Blo 307833 1973119 := bstep (se 1 (by rfl) ⟨1479839, by rfl⟩ : syracuseStep 1973119 = 2959679) B2959679
theorem B465833 : Blo 307833 465833 := bstep (se 2 (by rfl) ⟨174687, by rfl⟩ : syracuseStep 465833 = 349375) B349375
theorem B465887 : Blo 307833 465887 := bstep (se 1 (by rfl) ⟨349415, by rfl⟩ : syracuseStep 465887 = 698831) B698831
theorem B695915 : Blo 307833 695915 := bstep (se 1 (by rfl) ⟨521936, by rfl⟩ : syracuseStep 695915 = 1043873) B1043873
theorem B696059 : Blo 307833 696059 := bstep (se 1 (by rfl) ⟨522044, by rfl⟩ : syracuseStep 696059 = 1044089) B1044089
theorem B696185 : Blo 307833 696185 := bstep (se 2 (by rfl) ⟨261069, by rfl⟩ : syracuseStep 696185 = 522139) B522139
theorem B467423 : Blo 307833 467423 := bstep (se 1 (by rfl) ⟨350567, by rfl⟩ : syracuseStep 467423 = 701135) B701135
theorem B12919277 : Blo 307833 12919277 := bstep (se 3 (by rfl) ⟨2422364, by rfl⟩ : syracuseStep 12919277 = 4844729) B4844729
theorem B696923 : Blo 307833 696923 := bstep (se 1 (by rfl) ⟨522692, by rfl⟩ : syracuseStep 696923 = 1045385) B1045385
theorem B697337 : Blo 307833 697337 := bstep (se 2 (by rfl) ⟨261501, by rfl⟩ : syracuseStep 697337 = 523003) B523003
theorem B698651 : Blo 307833 698651 := bstep (se 1 (by rfl) ⟨523988, by rfl⟩ : syracuseStep 698651 = 1047977) B1047977
theorem B1321343 : Blo 307833 1321343 := bstep (se 1 (by rfl) ⟨991007, by rfl⟩ : syracuseStep 1321343 = 1982015) B1982015
theorem B1780127 : Blo 307833 1780127 := bstep (se 1 (by rfl) ⟨1335095, by rfl⟩ : syracuseStep 1780127 = 2670191) B2670191
theorem B698921 : Blo 307833 698921 := bstep (se 2 (by rfl) ⟨262095, by rfl⟩ : syracuseStep 698921 = 524191) B524191
theorem B2992895 : Blo 307833 2992895 := bstep (se 1 (by rfl) ⟨2244671, by rfl⟩ : syracuseStep 2992895 = 4489343) B4489343
theorem B1485647 : Blo 307833 1485647 := bstep (se 1 (by rfl) ⟨1114235, by rfl⟩ : syracuseStep 1485647 = 2228471) B2228471
theorem B2829167 : Blo 307833 2829167 := bstep (se 1 (by rfl) ⟨2121875, by rfl⟩ : syracuseStep 2829167 = 4243751) B4243751
theorem B3779513 : Blo 307833 3779513 := bstep (se 2 (by rfl) ⟨1417317, by rfl⟩ : syracuseStep 3779513 = 2834635) B2834635
theorem B699623 : Blo 307833 699623 := bstep (se 1 (by rfl) ⟨524717, by rfl⟩ : syracuseStep 699623 = 1049435) B1049435
theorem B2371103 : Blo 307833 2371103 := bstep (se 1 (by rfl) ⟨1778327, by rfl⟩ : syracuseStep 2371103 = 3556655) B3556655
theorem B1257115 : Blo 307833 1257115 := bstep (se 1 (by rfl) ⟨942836, by rfl⟩ : syracuseStep 1257115 = 1885673) B1885673
theorem B700073 : Blo 307833 700073 := bstep (se 2 (by rfl) ⟨262527, by rfl⟩ : syracuseStep 700073 = 525055) B525055
theorem B2109671 : Blo 307833 2109671 := bstep (se 1 (by rfl) ⟨1582253, by rfl⟩ : syracuseStep 2109671 = 3164507) B3164507
theorem B2732453 : Blo 307833 2732453 := bstep (se 4 (by rfl) ⟨256167, by rfl⟩ : syracuseStep 2732453 = 512335) B512335
theorem B1487297 : Blo 307833 1487297 := bstep (se 2 (by rfl) ⟨557736, by rfl⟩ : syracuseStep 1487297 = 1115473) B1115473
theorem B307903 : Blo 307833 307903 := bstep (se 1 (by rfl) ⟨230927, by rfl⟩ : syracuseStep 307903 = 461855) B461855
theorem B308159 : Blo 307833 308159 := bstep (se 1 (by rfl) ⟨231119, by rfl⟩ : syracuseStep 308159 = 462239) B462239
theorem B308191 : Blo 307833 308191 := bstep (se 1 (by rfl) ⟨231143, by rfl⟩ : syracuseStep 308191 = 462287) B462287
theorem B11351249 : Blo 307833 11351249 := bstep (se 2 (by rfl) ⟨4256718, by rfl⟩ : syracuseStep 11351249 = 8513437) B8513437
theorem B308839 : Blo 307833 308839 := bstep (se 1 (by rfl) ⟨231629, by rfl⟩ : syracuseStep 308839 = 463259) B463259
theorem B309119 : Blo 307833 309119 := bstep (se 1 (by rfl) ⟨231839, by rfl⟩ : syracuseStep 309119 = 463679) B463679
theorem B309499 : Blo 307833 309499 := bstep (se 1 (by rfl) ⟨232124, by rfl⟩ : syracuseStep 309499 = 464249) B464249
theorem B4438313 : Blo 307833 4438313 := bstep (se 2 (by rfl) ⟨1664367, by rfl⟩ : syracuseStep 4438313 = 3328735) B3328735
theorem B1489279 : Blo 307833 1489279 := bstep (se 1 (by rfl) ⟨1116959, by rfl⟩ : syracuseStep 1489279 = 2233919) B2233919
theorem B309863 : Blo 307833 309863 := bstep (se 1 (by rfl) ⟨232397, by rfl⟩ : syracuseStep 309863 = 464795) B464795
theorem B998183 : Blo 307833 998183 := bstep (se 1 (by rfl) ⟨748637, by rfl⟩ : syracuseStep 998183 = 1497275) B1497275
theorem B310303 : Blo 307833 310303 := bstep (se 1 (by rfl) ⟨232727, by rfl⟩ : syracuseStep 310303 = 465455) B465455
theorem B310335 : Blo 307833 310335 := bstep (se 1 (by rfl) ⟨232751, by rfl⟩ : syracuseStep 310335 = 465503) B465503
theorem B12106867 : Blo 307833 12106867 := bstep (se 1 (by rfl) ⟨9080150, by rfl⟩ : syracuseStep 12106867 = 18160301) B18160301
theorem B310575 : Blo 307833 310575 := bstep (se 1 (by rfl) ⟨232931, by rfl⟩ : syracuseStep 310575 = 465863) B465863
theorem B21577079 : Blo 307833 21577079 := bstep (se 1 (by rfl) ⟨16182809, by rfl⟩ : syracuseStep 21577079 = 32365619) B32365619
theorem B310655 : Blo 307833 310655 := bstep (se 1 (by rfl) ⟨232991, by rfl⟩ : syracuseStep 310655 = 465983) B465983
theorem B704027 : Blo 307833 704027 := bstep (se 1 (by rfl) ⟨528020, by rfl⟩ : syracuseStep 704027 = 1056041) B1056041
theorem B310815 : Blo 307833 310815 := bstep (se 1 (by rfl) ⟨233111, by rfl⟩ : syracuseStep 310815 = 466223) B466223
theorem B310975 : Blo 307833 310975 := bstep (se 1 (by rfl) ⟨233231, by rfl⟩ : syracuseStep 310975 = 466463) B466463
theorem B310991 : Blo 307833 310991 := bstep (se 1 (by rfl) ⟨233243, by rfl⟩ : syracuseStep 310991 = 466487) B466487
theorem B311103 : Blo 307833 311103 := bstep (se 1 (by rfl) ⟨233327, by rfl⟩ : syracuseStep 311103 = 466655) B466655
theorem B311231 : Blo 307833 311231 := bstep (se 1 (by rfl) ⟨233423, by rfl⟩ : syracuseStep 311231 = 466847) B466847
theorem B311343 : Blo 307833 311343 := bstep (se 1 (by rfl) ⟨233507, by rfl⟩ : syracuseStep 311343 = 467015) B467015
theorem B311423 : Blo 307833 311423 := bstep (se 1 (by rfl) ⟨233567, by rfl⟩ : syracuseStep 311423 = 467135) B467135
theorem B311547 : Blo 307833 311547 := bstep (se 1 (by rfl) ⟨233660, by rfl⟩ : syracuseStep 311547 = 467321) B467321
theorem B13418885 : Blo 307833 13418885 := bstep (se 4 (by rfl) ⟨1258020, by rfl⟩ : syracuseStep 13418885 = 2516041) B2516041
theorem B311743 : Blo 307833 311743 := bstep (se 1 (by rfl) ⟨233807, by rfl⟩ : syracuseStep 311743 = 467615) B467615
theorem B1786681 : Blo 307833 1786681 := bstep (se 2 (by rfl) ⟨670005, by rfl⟩ : syracuseStep 1786681 = 1340011) B1340011
theorem B13452101 : Blo 307833 13452101 := bstep (se 4 (by rfl) ⟨1261134, by rfl⟩ : syracuseStep 13452101 = 2522269) B2522269
theorem B2638889 : Blo 307833 2638889 := bstep (se 2 (by rfl) ⟨989583, by rfl⟩ : syracuseStep 2638889 = 1979167) B1979167
theorem B10929815 : Blo 307833 10929815 := bstep (se 1 (by rfl) ⟨8197361, by rfl⟩ : syracuseStep 10929815 = 16394723) B16394723
theorem B2639951 : Blo 307833 2639951 := bstep (se 1 (by rfl) ⟨1979963, by rfl⟩ : syracuseStep 2639951 = 3959927) B3959927
theorem B346783 : Blo 307833 346783 := bstep (se 1 (by rfl) ⟨260087, by rfl⟩ : syracuseStep 346783 = 520175) B520175
theorem B3328775 : Blo 307833 3328775 := bstep (se 1 (by rfl) ⟨2496581, by rfl⟩ : syracuseStep 3328775 = 4993163) B4993163
theorem B3984167 : Blo 307833 3984167 := bstep (se 1 (by rfl) ⟨2988125, by rfl⟩ : syracuseStep 3984167 = 5976251) B5976251
theorem B3951773 : Blo 307833 3951773 := bstep (se 3 (by rfl) ⟨740957, by rfl⟩ : syracuseStep 3951773 = 1481915) B1481915
theorem B1756525 : Blo 307833 1756525 := bstep (se 3 (by rfl) ⟨329348, by rfl⟩ : syracuseStep 1756525 = 658697) B658697
theorem B1757483 : Blo 307833 1757483 := bstep (se 1 (by rfl) ⟨1318112, by rfl⟩ : syracuseStep 1757483 = 2636225) B2636225
theorem B10080773 : Blo 307833 10080773 := bstep (se 4 (by rfl) ⟨945072, by rfl⟩ : syracuseStep 10080773 = 1890145) B1890145
theorem B348799 : Blo 307833 348799 := bstep (se 1 (by rfl) ⟨261599, by rfl⟩ : syracuseStep 348799 = 523199) B523199
theorem B349051 : Blo 307833 349051 := bstep (se 1 (by rfl) ⟨261788, by rfl⟩ : syracuseStep 349051 = 523577) B523577
theorem B1594961 : Blo 307833 1594961 := bstep (se 2 (by rfl) ⟨598110, by rfl⟩ : syracuseStep 1594961 = 1196221) B1196221
theorem B350311 : Blo 307833 350311 := bstep (se 1 (by rfl) ⟨262733, by rfl⟩ : syracuseStep 350311 = 525467) B525467
theorem B5658761 : Blo 307833 5658761 := bstep (se 2 (by rfl) ⟨2122035, by rfl⟩ : syracuseStep 5658761 = 4244071) B4244071
theorem B350383 : Blo 307833 350383 := bstep (se 1 (by rfl) ⟨262787, by rfl⟩ : syracuseStep 350383 = 525575) B525575
theorem B1563623 : Blo 307833 1563623 := bstep (se 1 (by rfl) ⟨1172717, by rfl⟩ : syracuseStep 1563623 = 2345435) B2345435
theorem B1041011 : Blo 307833 1041011 := bstep (se 1 (by rfl) ⟨780758, by rfl⟩ : syracuseStep 1041011 = 1561517) B1561517
theorem B1565567 : Blo 307833 1565567 := bstep (se 1 (by rfl) ⟨1174175, by rfl⟩ : syracuseStep 1565567 = 2348351) B2348351
theorem B1172353 : Blo 307833 1172353 := bstep (se 2 (by rfl) ⟨439632, by rfl⟩ : syracuseStep 1172353 = 879265) B879265
theorem B780425 : Blo 307833 780425 := bstep (se 2 (by rfl) ⟨292659, by rfl⟩ : syracuseStep 780425 = 585319) B585319
theorem B1043819 : Blo 307833 1043819 := bstep (se 1 (by rfl) ⟨782864, by rfl⟩ : syracuseStep 1043819 = 1565729) B1565729
theorem B1568159 : Blo 307833 1568159 := bstep (se 1 (by rfl) ⟨1176119, by rfl⟩ : syracuseStep 1568159 = 2352239) B2352239
theorem B3010193 : Blo 307833 3010193 := bstep (se 2 (by rfl) ⟨1128822, by rfl⟩ : syracuseStep 3010193 = 2257645) B2257645
theorem B1568807 : Blo 307833 1568807 := bstep (se 1 (by rfl) ⟨1176605, by rfl⟩ : syracuseStep 1568807 = 2353211) B2353211
theorem B520303 : Blo 307833 520303 := bstep (se 1 (by rfl) ⟨390227, by rfl⟩ : syracuseStep 520303 = 780455) B780455
theorem B1405241 : Blo 307833 1405241 := bstep (se 2 (by rfl) ⟨526965, by rfl⟩ : syracuseStep 1405241 = 1053931) B1053931
theorem B750055 : Blo 307833 750055 := bstep (se 1 (by rfl) ⟨562541, by rfl⟩ : syracuseStep 750055 = 1125083) B1125083
theorem B881225 : Blo 307833 881225 := bstep (se 2 (by rfl) ⟨330459, by rfl⟩ : syracuseStep 881225 = 660919) B660919
theorem B1176545 : Blo 307833 1176545 := bstep (se 2 (by rfl) ⟨441204, by rfl⟩ : syracuseStep 1176545 = 882409) B882409
theorem B521599 : Blo 307833 521599 := bstep (se 1 (by rfl) ⟨391199, by rfl⟩ : syracuseStep 521599 = 782399) B782399
theorem B1668539 : Blo 307833 1668539 := bstep (se 1 (by rfl) ⟨1251404, by rfl⟩ : syracuseStep 1668539 = 2502809) B2502809
theorem B2979287 : Blo 307833 2979287 := bstep (se 1 (by rfl) ⟨2234465, by rfl⟩ : syracuseStep 2979287 = 4468931) B4468931
theorem B13629019 : Blo 307833 13629019 := bstep (se 1 (by rfl) ⟨10221764, by rfl⟩ : syracuseStep 13629019 = 20443529) B20443529
theorem B1341053 : Blo 307833 1341053 := bstep (se 3 (by rfl) ⟨251447, by rfl⟩ : syracuseStep 1341053 = 502895) B502895
theorem B521903 : Blo 307833 521903 := bstep (se 1 (by rfl) ⟨391427, by rfl⟩ : syracuseStep 521903 = 782855) B782855
theorem B1668887 : Blo 307833 1668887 := bstep (se 1 (by rfl) ⟨1251665, by rfl⟩ : syracuseStep 1668887 = 2503331) B2503331
theorem B587711 : Blo 307833 587711 := bstep (se 1 (by rfl) ⟨440783, by rfl⟩ : syracuseStep 587711 = 881567) B881567
theorem B2815951 : Blo 307833 2815951 := bstep (se 1 (by rfl) ⟨2111963, by rfl⟩ : syracuseStep 2815951 = 4223927) B4223927
theorem B882683 : Blo 307833 882683 := bstep (se 1 (by rfl) ⟨662012, by rfl⟩ : syracuseStep 882683 = 1324025) B1324025
theorem B522463 : Blo 307833 522463 := bstep (se 1 (by rfl) ⟨391847, by rfl⟩ : syracuseStep 522463 = 783695) B783695
theorem B883001 : Blo 307833 883001 := bstep (se 2 (by rfl) ⟨331125, by rfl⟩ : syracuseStep 883001 = 662251) B662251
theorem B1571399 : Blo 307833 1571399 := bstep (se 1 (by rfl) ⟨1178549, by rfl⟩ : syracuseStep 1571399 = 2357099) B2357099
theorem B1571561 : Blo 307833 1571561 := bstep (se 2 (by rfl) ⟨589335, by rfl⟩ : syracuseStep 1571561 = 1178671) B1178671
theorem B588539 : Blo 307833 588539 := bstep (se 1 (by rfl) ⟨441404, by rfl⟩ : syracuseStep 588539 = 882809) B882809
theorem B3767057 : Blo 307833 3767057 := bstep (se 2 (by rfl) ⟨1412646, by rfl⟩ : syracuseStep 3767057 = 2825293) B2825293
theorem B1112879 : Blo 307833 1112879 := bstep (se 1 (by rfl) ⟨834659, by rfl⟩ : syracuseStep 1112879 = 1669319) B1669319
theorem B8092871 : Blo 307833 8092871 := bstep (se 1 (by rfl) ⟨6069653, by rfl⟩ : syracuseStep 8092871 = 12139307) B12139307
theorem B1572047 : Blo 307833 1572047 := bstep (se 1 (by rfl) ⟨1179035, by rfl⟩ : syracuseStep 1572047 = 2358071) B2358071
theorem B785659 : Blo 307833 785659 := bstep (se 1 (by rfl) ⟨589244, by rfl⟩ : syracuseStep 785659 = 1178489) B1178489
theorem B5275043 : Blo 307833 5275043 := bstep (se 1 (by rfl) ⟨3956282, by rfl⟩ : syracuseStep 5275043 = 7912565) B7912565
theorem B523759 : Blo 307833 523759 := bstep (se 1 (by rfl) ⟨392819, by rfl⟩ : syracuseStep 523759 = 785639) B785639
theorem B523847 : Blo 307833 523847 := bstep (se 1 (by rfl) ⟨392885, by rfl⟩ : syracuseStep 523847 = 785771) B785771
theorem B3964895 : Blo 307833 3964895 := bstep (se 1 (by rfl) ⟨2973671, by rfl⟩ : syracuseStep 3964895 = 5947343) B5947343
theorem B786419 : Blo 307833 786419 := bstep (se 1 (by rfl) ⟨589814, by rfl⟩ : syracuseStep 786419 = 1179629) B1179629
theorem B8945923 : Blo 307833 8945923 := bstep (se 1 (by rfl) ⟨6709442, by rfl⟩ : syracuseStep 8945923 = 13418885) B13418885
theorem B1048841 : Blo 307833 1048841 := bstep (se 2 (by rfl) ⟨393315, by rfl⟩ : syracuseStep 1048841 = 786631) B786631
theorem B15008287 : Blo 307833 15008287 := bstep (se 1 (by rfl) ⟨11256215, by rfl⟩ : syracuseStep 15008287 = 22512431) B22512431
theorem B525865 : Blo 307833 525865 := bstep (se 2 (by rfl) ⟨197199, by rfl⟩ : syracuseStep 525865 = 394399) B394399
theorem B7997251 : Blo 307833 7997251 := bstep (se 1 (by rfl) ⟨5997938, by rfl⟩ : syracuseStep 7997251 = 11995877) B11995877
theorem B2656111 : Blo 307833 2656111 := bstep (se 1 (by rfl) ⟨1992083, by rfl⟩ : syracuseStep 2656111 = 3984167) B3984167
theorem B1182059 : Blo 307833 1182059 := bstep (se 1 (by rfl) ⟨886544, by rfl⟩ : syracuseStep 1182059 = 1773089) B1773089
theorem B1051433 : Blo 307833 1051433 := bstep (se 2 (by rfl) ⟨394287, by rfl⟩ : syracuseStep 1051433 = 788575) B788575
theorem B1444711 : Blo 307833 1444711 := bstep (se 1 (by rfl) ⟨1083533, by rfl⟩ : syracuseStep 1444711 = 2167067) B2167067
theorem B6720515 : Blo 307833 6720515 := bstep (se 1 (by rfl) ⟨5040386, by rfl⟩ : syracuseStep 6720515 = 10080773) B10080773
theorem B109186217 : Blo 307833 109186217 := bstep (se 2 (by rfl) ⟨40944831, by rfl⟩ : syracuseStep 109186217 = 81889663) B81889663
theorem B462335 : Blo 307833 462335 := bstep (se 1 (by rfl) ⟨346751, by rfl⟩ : syracuseStep 462335 = 693503) B693503
theorem B462377 : Blo 307833 462377 := bstep (se 2 (by rfl) ⟨173391, by rfl⟩ : syracuseStep 462377 = 346783) B346783
theorem B462683 : Blo 307833 462683 := bstep (se 1 (by rfl) ⟨347012, by rfl⟩ : syracuseStep 462683 = 694025) B694025
theorem B462791 : Blo 307833 462791 := bstep (se 1 (by rfl) ⟨347093, by rfl⟩ : syracuseStep 462791 = 694187) B694187
theorem B3772507 : Blo 307833 3772507 := bstep (se 1 (by rfl) ⟨2829380, by rfl⟩ : syracuseStep 3772507 = 5658761) B5658761
theorem B1676153 : Blo 307833 1676153 := bstep (se 2 (by rfl) ⟨628557, by rfl⟩ : syracuseStep 1676153 = 1257115) B1257115
theorem B463943 : Blo 307833 463943 := bstep (se 1 (by rfl) ⟨347957, by rfl⟩ : syracuseStep 463943 = 695915) B695915
theorem B464039 : Blo 307833 464039 := bstep (se 1 (by rfl) ⟨348029, by rfl⟩ : syracuseStep 464039 = 696059) B696059
theorem B464123 : Blo 307833 464123 := bstep (se 1 (by rfl) ⟨348092, by rfl⟩ : syracuseStep 464123 = 696185) B696185
theorem B693737 : Blo 307833 693737 := bstep (se 2 (by rfl) ⟨260151, by rfl⟩ : syracuseStep 693737 = 520303) B520303
theorem B464615 : Blo 307833 464615 := bstep (se 1 (by rfl) ⟨348461, by rfl⟩ : syracuseStep 464615 = 696923) B696923
theorem B694007 : Blo 307833 694007 := bstep (se 1 (by rfl) ⟨520505, by rfl⟩ : syracuseStep 694007 = 1041011) B1041011
theorem B464891 : Blo 307833 464891 := bstep (se 1 (by rfl) ⟨348668, by rfl⟩ : syracuseStep 464891 = 697337) B697337
theorem B465065 : Blo 307833 465065 := bstep (se 2 (by rfl) ⟨174399, by rfl⟩ : syracuseStep 465065 = 348799) B348799
theorem B465401 : Blo 307833 465401 := bstep (se 2 (by rfl) ⟨174525, by rfl⟩ : syracuseStep 465401 = 349051) B349051
theorem B465767 : Blo 307833 465767 := bstep (se 1 (by rfl) ⟨349325, by rfl⟩ : syracuseStep 465767 = 698651) B698651
theorem B1186751 : Blo 307833 1186751 := bstep (se 1 (by rfl) ⟨890063, by rfl⟩ : syracuseStep 1186751 = 1780127) B1780127
theorem B465947 : Blo 307833 465947 := bstep (se 1 (by rfl) ⟨349460, by rfl⟩ : syracuseStep 465947 = 698921) B698921
theorem B695465 : Blo 307833 695465 := bstep (se 2 (by rfl) ⟨260799, by rfl⟩ : syracuseStep 695465 = 521599) B521599
theorem B990431 : Blo 307833 990431 := bstep (se 1 (by rfl) ⟨742823, by rfl⟩ : syracuseStep 990431 = 1485647) B1485647
theorem B2661821 : Blo 307833 2661821 := bstep (se 3 (by rfl) ⟨499091, by rfl⟩ : syracuseStep 2661821 = 998183) B998183
theorem B466415 : Blo 307833 466415 := bstep (se 1 (by rfl) ⟨349811, by rfl⟩ : syracuseStep 466415 = 699623) B699623
theorem B695879 : Blo 307833 695879 := bstep (se 1 (by rfl) ⟨521909, by rfl⟩ : syracuseStep 695879 = 1043819) B1043819
theorem B1580735 : Blo 307833 1580735 := bstep (se 1 (by rfl) ⟨1185551, by rfl⟩ : syracuseStep 1580735 = 2371103) B2371103
theorem B2006795 : Blo 307833 2006795 := bstep (se 1 (by rfl) ⟨1505096, by rfl⟩ : syracuseStep 2006795 = 3010193) B3010193
theorem B466715 : Blo 307833 466715 := bstep (se 1 (by rfl) ⟨350036, by rfl⟩ : syracuseStep 466715 = 700073) B700073
theorem B467081 : Blo 307833 467081 := bstep (se 2 (by rfl) ⟨175155, by rfl⟩ : syracuseStep 467081 = 350311) B350311
theorem B467177 : Blo 307833 467177 := bstep (se 2 (by rfl) ⟨175191, by rfl⟩ : syracuseStep 467177 = 350383) B350383
theorem B696617 : Blo 307833 696617 := bstep (se 2 (by rfl) ⟨261231, by rfl⟩ : syracuseStep 696617 = 522463) B522463
theorem B991531 : Blo 307833 991531 := bstep (se 1 (by rfl) ⟨743648, by rfl⟩ : syracuseStep 991531 = 1487297) B1487297
theorem B894035 : Blo 307833 894035 := bstep (se 1 (by rfl) ⟨670526, by rfl⟩ : syracuseStep 894035 = 1341053) B1341053
theorem B2630825 : Blo 307833 2630825 := bstep (se 2 (by rfl) ⟨986559, by rfl⟩ : syracuseStep 2630825 = 1973119) B1973119
theorem B2958875 : Blo 307833 2958875 := bstep (se 1 (by rfl) ⟨2219156, by rfl⟩ : syracuseStep 2958875 = 4438313) B4438313
theorem B698345 : Blo 307833 698345 := bstep (se 2 (by rfl) ⟨261879, by rfl⟩ : syracuseStep 698345 = 523759) B523759
theorem B3516695 : Blo 307833 3516695 := bstep (se 1 (by rfl) ⟨2637521, by rfl⟩ : syracuseStep 3516695 = 5275043) B5275043
theorem B469351 : Blo 307833 469351 := bstep (se 1 (by rfl) ⟨352013, by rfl⟩ : syracuseStep 469351 = 704027) B704027
theorem B1682207 : Blo 307833 1682207 := bstep (se 1 (by rfl) ⟨1261655, by rfl⟩ : syracuseStep 1682207 = 2523311) B2523311
theorem B7286543 : Blo 307833 7286543 := bstep (se 1 (by rfl) ⟨5464907, by rfl⟩ : syracuseStep 7286543 = 10929815) B10929815
theorem B700577 : Blo 307833 700577 := bstep (se 2 (by rfl) ⟨262716, by rfl⟩ : syracuseStep 700577 = 525433) B525433
theorem B2339603 : Blo 307833 2339603 := bstep (se 1 (by rfl) ⟨1754702, by rfl⟩ : syracuseStep 2339603 = 3509405) B3509405
theorem B2634515 : Blo 307833 2634515 := bstep (se 1 (by rfl) ⟨1975886, by rfl⟩ : syracuseStep 2634515 = 3951773) B3951773
theorem B701531 : Blo 307833 701531 := bstep (se 1 (by rfl) ⟨526148, by rfl⟩ : syracuseStep 701531 = 1052297) B1052297
theorem B701567 : Blo 307833 701567 := bstep (se 1 (by rfl) ⟨526175, by rfl⟩ : syracuseStep 701567 = 1052351) B1052351
theorem B308967 : Blo 307833 308967 := bstep (se 1 (by rfl) ⟨231725, by rfl⟩ : syracuseStep 308967 = 463451) B463451
theorem B309103 : Blo 307833 309103 := bstep (se 1 (by rfl) ⟨231827, by rfl⟩ : syracuseStep 309103 = 463655) B463655
theorem B309215 : Blo 307833 309215 := bstep (se 1 (by rfl) ⟨231911, by rfl⟩ : syracuseStep 309215 = 463823) B463823
theorem B1063307 : Blo 307833 1063307 := bstep (se 1 (by rfl) ⟨797480, by rfl⟩ : syracuseStep 1063307 = 1594961) B1594961
theorem B309659 : Blo 307833 309659 := bstep (se 1 (by rfl) ⟨232244, by rfl⟩ : syracuseStep 309659 = 464489) B464489
theorem B309999 : Blo 307833 309999 := bstep (se 1 (by rfl) ⟨232499, by rfl⟩ : syracuseStep 309999 = 464999) B464999
theorem B310015 : Blo 307833 310015 := bstep (se 1 (by rfl) ⟨232511, by rfl⟩ : syracuseStep 310015 = 465023) B465023
theorem B703615 : Blo 307833 703615 := bstep (se 1 (by rfl) ⟨527711, by rfl⟩ : syracuseStep 703615 = 1055423) B1055423
theorem B2342033 : Blo 307833 2342033 := bstep (se 2 (by rfl) ⟨878262, by rfl⟩ : syracuseStep 2342033 = 1756525) B1756525
theorem B310555 : Blo 307833 310555 := bstep (se 1 (by rfl) ⟨232916, by rfl⟩ : syracuseStep 310555 = 465833) B465833
theorem B310591 : Blo 307833 310591 := bstep (se 1 (by rfl) ⟨232943, by rfl⟩ : syracuseStep 310591 = 465887) B465887
theorem B311615 : Blo 307833 311615 := bstep (se 1 (by rfl) ⟨233711, by rfl⟩ : syracuseStep 311615 = 467423) B467423
theorem B1000073 : Blo 307833 1000073 := bstep (se 2 (by rfl) ⟨375027, by rfl⟩ : syracuseStep 1000073 = 750055) B750055
theorem B1886111 : Blo 307833 1886111 := bstep (se 1 (by rfl) ⟨1414583, by rfl⟩ : syracuseStep 1886111 = 2829167) B2829167
theorem B18172025 : Blo 307833 18172025 := bstep (se 2 (by rfl) ⟨6814509, by rfl⟩ : syracuseStep 18172025 = 13629019) B13629019
theorem B2967677 : Blo 307833 2967677 := bstep (se 3 (by rfl) ⟨556439, by rfl⟩ : syracuseStep 2967677 = 1112879) B1112879
theorem B3754601 : Blo 307833 3754601 := bstep (se 2 (by rfl) ⟨1407975, by rfl⟩ : syracuseStep 3754601 = 2815951) B2815951
theorem B936827 : Blo 307833 936827 := bstep (se 1 (by rfl) ⟨702620, by rfl⟩ : syracuseStep 936827 = 1405241) B1405241
theorem B1821635 : Blo 307833 1821635 := bstep (se 1 (by rfl) ⟨1366226, by rfl⟩ : syracuseStep 1821635 = 2732453) B2732453
theorem B1985705 : Blo 307833 1985705 := bstep (se 2 (by rfl) ⟨744639, by rfl⟩ : syracuseStep 1985705 = 1489279) B1489279
theorem B1986191 : Blo 307833 1986191 := bstep (se 1 (by rfl) ⟨1489643, by rfl⟩ : syracuseStep 1986191 = 2979287) B2979287
theorem B347935 : Blo 307833 347935 := bstep (se 1 (by rfl) ⟨260951, by rfl⟩ : syracuseStep 347935 = 521903) B521903
theorem B16142489 : Blo 307833 16142489 := bstep (se 2 (by rfl) ⟨6053433, by rfl⟩ : syracuseStep 16142489 = 12106867) B12106867
theorem B2511371 : Blo 307833 2511371 := bstep (se 1 (by rfl) ⟨1883528, by rfl⟩ : syracuseStep 2511371 = 3767057) B3767057
theorem B5395247 : Blo 307833 5395247 := bstep (se 1 (by rfl) ⟨4046435, by rfl⟩ : syracuseStep 5395247 = 8092871) B8092871
theorem B349231 : Blo 307833 349231 := bstep (se 1 (by rfl) ⟨261923, by rfl⟩ : syracuseStep 349231 = 523847) B523847
theorem B2643263 : Blo 307833 2643263 := bstep (se 1 (by rfl) ⟨1982447, by rfl⟩ : syracuseStep 2643263 = 3964895) B3964895
theorem B939431 : Blo 307833 939431 := bstep (se 1 (by rfl) ⟨704573, by rfl⟩ : syracuseStep 939431 = 1409147) B1409147
theorem B8968067 : Blo 307833 8968067 := bstep (se 1 (by rfl) ⟨6726050, by rfl⟩ : syracuseStep 8968067 = 13452101) B13452101
theorem B1759259 : Blo 307833 1759259 := bstep (se 1 (by rfl) ⟨1319444, by rfl⟩ : syracuseStep 1759259 = 2638889) B2638889
theorem B1563137 : Blo 307833 1563137 := bstep (se 2 (by rfl) ⟨586176, by rfl⟩ : syracuseStep 1563137 = 1172353) B1172353
theorem B1759967 : Blo 307833 1759967 := bstep (se 1 (by rfl) ⟨1319975, by rfl⟩ : syracuseStep 1759967 = 2639951) B2639951
theorem B2219183 : Blo 307833 2219183 := bstep (se 1 (by rfl) ⟨1664387, by rfl⟩ : syracuseStep 2219183 = 3328775) B3328775
theorem B1171655 : Blo 307833 1171655 := bstep (se 1 (by rfl) ⟨878741, by rfl⟩ : syracuseStep 1171655 = 1757483) B1757483
theorem B4449437 : Blo 307833 4449437 := bstep (se 3 (by rfl) ⟨834269, by rfl⟩ : syracuseStep 4449437 = 1668539) B1668539
theorem B9528965 : Blo 307833 9528965 := bstep (se 4 (by rfl) ⟨893340, by rfl⟩ : syracuseStep 9528965 = 1786681) B1786681
theorem B1042415 : Blo 307833 1042415 := bstep (se 1 (by rfl) ⟨781811, by rfl⟩ : syracuseStep 1042415 = 1563623) B1563623
theorem B8612851 : Blo 307833 8612851 := bstep (se 1 (by rfl) ⟨6459638, by rfl⟩ : syracuseStep 8612851 = 12919277) B12919277
theorem B1043711 : Blo 307833 1043711 := bstep (se 1 (by rfl) ⟨782783, by rfl⟩ : syracuseStep 1043711 = 1565567) B1565567
theorem B2354669 : Blo 307833 2354669 := bstep (se 3 (by rfl) ⟨441500, by rfl⟩ : syracuseStep 2354669 = 883001) B883001
theorem B520283 : Blo 307833 520283 := bstep (se 1 (by rfl) ⟨390212, by rfl⟩ : syracuseStep 520283 = 780425) B780425
theorem B880895 : Blo 307833 880895 := bstep (se 1 (by rfl) ⟨660671, by rfl⟩ : syracuseStep 880895 = 1321343) B1321343
theorem B1995263 : Blo 307833 1995263 := bstep (se 1 (by rfl) ⟨1496447, by rfl⟩ : syracuseStep 1995263 = 2992895) B2992895
theorem B2519675 : Blo 307833 2519675 := bstep (se 1 (by rfl) ⟨1889756, by rfl⟩ : syracuseStep 2519675 = 3779513) B3779513
theorem B1045439 : Blo 307833 1045439 := bstep (se 1 (by rfl) ⟨784079, by rfl⟩ : syracuseStep 1045439 = 1568159) B1568159
theorem B1045871 : Blo 307833 1045871 := bstep (se 1 (by rfl) ⟨784403, by rfl⟩ : syracuseStep 1045871 = 1568807) B1568807
theorem B1406447 : Blo 307833 1406447 := bstep (se 1 (by rfl) ⟨1054835, by rfl⟩ : syracuseStep 1406447 = 2109671) B2109671
theorem B587483 : Blo 307833 587483 := bstep (se 1 (by rfl) ⟨440612, by rfl⟩ : syracuseStep 587483 = 881225) B881225
theorem B784363 : Blo 307833 784363 := bstep (se 1 (by rfl) ⟨588272, by rfl⟩ : syracuseStep 784363 = 1176545) B1176545
theorem B7567499 : Blo 307833 7567499 := bstep (se 1 (by rfl) ⟨5675624, by rfl⟩ : syracuseStep 7567499 = 11351249) B11351249
theorem B1112591 : Blo 307833 1112591 := bstep (se 1 (by rfl) ⟨834443, by rfl⟩ : syracuseStep 1112591 = 1668887) B1668887
theorem B391807 : Blo 307833 391807 := bstep (se 1 (by rfl) ⟨293855, by rfl⟩ : syracuseStep 391807 = 587711) B587711
theorem B588455 : Blo 307833 588455 := bstep (se 1 (by rfl) ⟨441341, by rfl⟩ : syracuseStep 588455 = 882683) B882683
theorem B1047545 : Blo 307833 1047545 := bstep (se 2 (by rfl) ⟨392829, by rfl⟩ : syracuseStep 1047545 = 785659) B785659
theorem B1047599 : Blo 307833 1047599 := bstep (se 1 (by rfl) ⟨785699, by rfl⟩ : syracuseStep 1047599 = 1571399) B1571399
theorem B1047707 : Blo 307833 1047707 := bstep (se 1 (by rfl) ⟨785780, by rfl⟩ : syracuseStep 1047707 = 1571561) B1571561
theorem B392359 : Blo 307833 392359 := bstep (se 1 (by rfl) ⟨294269, by rfl⟩ : syracuseStep 392359 = 588539) B588539
theorem B1048031 : Blo 307833 1048031 := bstep (se 1 (by rfl) ⟨786023, by rfl⟩ : syracuseStep 1048031 = 1572047) B1572047
theorem B14384719 : Blo 307833 14384719 := bstep (se 1 (by rfl) ⟨10788539, by rfl⟩ : syracuseStep 14384719 = 21577079) B21577079
theorem B524279 : Blo 307833 524279 := bstep (se 1 (by rfl) ⟨393209, by rfl⟩ : syracuseStep 524279 = 786419) B786419
theorem B11927897 : Blo 307833 11927897 := bstep (se 2 (by rfl) ⟨4472961, by rfl⟩ : syracuseStep 11927897 = 8945923) B8945923
theorem B788039 : Blo 307833 788039 := bstep (se 1 (by rfl) ⟨591029, by rfl⟩ : syracuseStep 788039 = 1182059) B1182059
theorem B624551 : Blo 307833 624551 := bstep (se 1 (by rfl) ⟨468413, by rfl⟩ : syracuseStep 624551 = 936827) B936827
theorem B1214423 : Blo 307833 1214423 := bstep (se 1 (by rfl) ⟨910817, by rfl⟩ : syracuseStep 1214423 = 1821635) B1821635
theorem B3541481 : Blo 307833 3541481 := bstep (se 2 (by rfl) ⟨1328055, by rfl⟩ : syracuseStep 3541481 = 2656111) B2656111
theorem B625801 : Blo 307833 625801 := bstep (se 2 (by rfl) ⟨234675, by rfl⟩ : syracuseStep 625801 = 469351) B469351
theorem B1117435 : Blo 307833 1117435 := bstep (se 1 (by rfl) ⟨838076, by rfl⟩ : syracuseStep 1117435 = 1676153) B1676153
theorem B626287 : Blo 307833 626287 := bstep (se 1 (by rfl) ⟨469715, by rfl⟩ : syracuseStep 626287 = 939431) B939431
theorem B462491 : Blo 307833 462491 := bstep (se 1 (by rfl) ⟨346868, by rfl⟩ : syracuseStep 462491 = 693737) B693737
theorem B462671 : Blo 307833 462671 := bstep (se 1 (by rfl) ⟨347003, by rfl⟩ : syracuseStep 462671 = 694007) B694007
theorem B791167 : Blo 307833 791167 := bstep (se 1 (by rfl) ⟨593375, by rfl⟩ : syracuseStep 791167 = 1186751) B1186751
theorem B463643 : Blo 307833 463643 := bstep (se 1 (by rfl) ⟨347732, by rfl⟩ : syracuseStep 463643 = 695465) B695465
theorem B1479455 : Blo 307833 1479455 := bstep (se 1 (by rfl) ⟨1109591, by rfl⟩ : syracuseStep 1479455 = 2219183) B2219183
theorem B660287 : Blo 307833 660287 := bstep (se 1 (by rfl) ⟨495215, by rfl⟩ : syracuseStep 660287 = 990431) B990431
theorem B1774547 : Blo 307833 1774547 := bstep (se 1 (by rfl) ⟨1330910, by rfl⟩ : syracuseStep 1774547 = 2661821) B2661821
theorem B463913 : Blo 307833 463913 := bstep (se 2 (by rfl) ⟨173967, by rfl⟩ : syracuseStep 463913 = 347935) B347935
theorem B463919 : Blo 307833 463919 := bstep (se 1 (by rfl) ⟨347939, by rfl⟩ : syracuseStep 463919 = 695879) B695879
theorem B1053823 : Blo 307833 1053823 := bstep (se 1 (by rfl) ⟨790367, by rfl⟩ : syracuseStep 1053823 = 1580735) B1580735
theorem B464411 : Blo 307833 464411 := bstep (se 1 (by rfl) ⟨348308, by rfl⟩ : syracuseStep 464411 = 696617) B696617
theorem B1972583 : Blo 307833 1972583 := bstep (se 1 (by rfl) ⟨1479437, by rfl⟩ : syracuseStep 1972583 = 2958875) B2958875
theorem B465563 : Blo 307833 465563 := bstep (se 1 (by rfl) ⟨349172, by rfl⟩ : syracuseStep 465563 = 698345) B698345
theorem B694943 : Blo 307833 694943 := bstep (se 1 (by rfl) ⟨521207, by rfl⟩ : syracuseStep 694943 = 1042415) B1042415
theorem B465641 : Blo 307833 465641 := bstep (se 2 (by rfl) ⟨174615, by rfl⟩ : syracuseStep 465641 = 349231) B349231
theorem B1121471 : Blo 307833 1121471 := bstep (se 1 (by rfl) ⟨841103, by rfl⟩ : syracuseStep 1121471 = 1682207) B1682207
theorem B695807 : Blo 307833 695807 := bstep (se 1 (by rfl) ⟨521855, by rfl⟩ : syracuseStep 695807 = 1043711) B1043711
theorem B4857695 : Blo 307833 4857695 := bstep (se 1 (by rfl) ⟨3643271, by rfl⟩ : syracuseStep 4857695 = 7286543) B7286543
theorem B467051 : Blo 307833 467051 := bstep (se 1 (by rfl) ⟨350288, by rfl⟩ : syracuseStep 467051 = 700577) B700577
theorem B1679783 : Blo 307833 1679783 := bstep (se 1 (by rfl) ⟨1259837, by rfl⟩ : syracuseStep 1679783 = 2519675) B2519675
theorem B696959 : Blo 307833 696959 := bstep (se 1 (by rfl) ⟨522719, by rfl⟩ : syracuseStep 696959 = 1045439) B1045439
theorem B467687 : Blo 307833 467687 := bstep (se 1 (by rfl) ⟨350765, by rfl⟩ : syracuseStep 467687 = 701531) B701531
theorem B467711 : Blo 307833 467711 := bstep (se 1 (by rfl) ⟨350783, by rfl⟩ : syracuseStep 467711 = 701567) B701567
theorem B697247 : Blo 307833 697247 := bstep (se 1 (by rfl) ⟨522935, by rfl⟩ : syracuseStep 697247 = 1045871) B1045871
theorem B698363 : Blo 307833 698363 := bstep (se 1 (by rfl) ⟨523772, by rfl⟩ : syracuseStep 698363 = 1047545) B1047545
theorem B5351453 : Blo 307833 5351453 := bstep (se 3 (by rfl) ⟨1003397, by rfl⟩ : syracuseStep 5351453 = 2006795) B2006795
theorem B698399 : Blo 307833 698399 := bstep (se 1 (by rfl) ⟨523799, by rfl⟩ : syracuseStep 698399 = 1047599) B1047599
theorem B698471 : Blo 307833 698471 := bstep (se 1 (by rfl) ⟨523853, by rfl⟩ : syracuseStep 698471 = 1047707) B1047707
theorem B19179625 : Blo 307833 19179625 := bstep (se 2 (by rfl) ⟨7192359, by rfl⟩ : syracuseStep 19179625 = 14384719) B14384719
theorem B698687 : Blo 307833 698687 := bstep (se 1 (by rfl) ⟨524015, by rfl⟩ : syracuseStep 698687 = 1048031) B1048031
theorem B699227 : Blo 307833 699227 := bstep (se 1 (by rfl) ⟨524420, by rfl⟩ : syracuseStep 699227 = 1048841) B1048841
theorem B666715 : Blo 307833 666715 := bstep (se 1 (by rfl) ⟨500036, by rfl⟩ : syracuseStep 666715 = 1000073) B1000073
theorem B1257407 : Blo 307833 1257407 := bstep (se 1 (by rfl) ⟨943055, by rfl⟩ : syracuseStep 1257407 = 1886111) B1886111
theorem B6696989 : Blo 307833 6696989 := bstep (se 3 (by rfl) ⟨1255685, by rfl⟩ : syracuseStep 6696989 = 2511371) B2511371
theorem B1978451 : Blo 307833 1978451 := bstep (se 1 (by rfl) ⟨1483838, by rfl⟩ : syracuseStep 1978451 = 2967677) B2967677
theorem B5288165 : Blo 307833 5288165 := bstep (se 4 (by rfl) ⟨495765, by rfl⟩ : syracuseStep 5288165 = 991531) B991531
theorem B2503067 : Blo 307833 2503067 := bstep (se 1 (by rfl) ⟨1877300, by rfl⟩ : syracuseStep 2503067 = 3754601) B3754601
theorem B700955 : Blo 307833 700955 := bstep (se 1 (by rfl) ⟨525716, by rfl⟩ : syracuseStep 700955 = 1051433) B1051433
theorem B701153 : Blo 307833 701153 := bstep (se 2 (by rfl) ⟨262932, by rfl⟩ : syracuseStep 701153 = 525865) B525865
theorem B1323803 : Blo 307833 1323803 := bstep (se 1 (by rfl) ⟨992852, by rfl⟩ : syracuseStep 1323803 = 1985705) B1985705
theorem B72790811 : Blo 307833 72790811 := bstep (se 1 (by rfl) ⟨54593108, by rfl⟩ : syracuseStep 72790811 = 109186217) B109186217
theorem B308223 : Blo 307833 308223 := bstep (se 1 (by rfl) ⟨231167, by rfl⟩ : syracuseStep 308223 = 462335) B462335
theorem B308251 : Blo 307833 308251 := bstep (se 1 (by rfl) ⟨231188, by rfl⟩ : syracuseStep 308251 = 462377) B462377
theorem B10663001 : Blo 307833 10663001 := bstep (se 2 (by rfl) ⟨3998625, by rfl⟩ : syracuseStep 10663001 = 7997251) B7997251
theorem B1324127 : Blo 307833 1324127 := bstep (se 1 (by rfl) ⟨993095, by rfl⟩ : syracuseStep 1324127 = 1986191) B1986191
theorem B308455 : Blo 307833 308455 := bstep (se 1 (by rfl) ⟨231341, by rfl⟩ : syracuseStep 308455 = 462683) B462683
theorem B308527 : Blo 307833 308527 := bstep (se 1 (by rfl) ⟨231395, by rfl⟩ : syracuseStep 308527 = 462791) B462791
theorem B10761659 : Blo 307833 10761659 := bstep (se 1 (by rfl) ⟨8071244, by rfl⟩ : syracuseStep 10761659 = 16142489) B16142489
theorem B309295 : Blo 307833 309295 := bstep (se 1 (by rfl) ⟨231971, by rfl⟩ : syracuseStep 309295 = 463943) B463943
theorem B309359 : Blo 307833 309359 := bstep (se 1 (by rfl) ⟨232019, by rfl⟩ : syracuseStep 309359 = 464039) B464039
theorem B309415 : Blo 307833 309415 := bstep (se 1 (by rfl) ⟨232061, by rfl⟩ : syracuseStep 309415 = 464123) B464123
theorem B309743 : Blo 307833 309743 := bstep (se 1 (by rfl) ⟨232307, by rfl⟩ : syracuseStep 309743 = 464615) B464615
theorem B5978711 : Blo 307833 5978711 := bstep (se 1 (by rfl) ⟨4484033, by rfl⟩ : syracuseStep 5978711 = 8968067) B8968067
theorem B11483801 : Blo 307833 11483801 := bstep (se 2 (by rfl) ⟨4306425, by rfl⟩ : syracuseStep 11483801 = 8612851) B8612851
theorem B309927 : Blo 307833 309927 := bstep (se 1 (by rfl) ⟨232445, by rfl⟩ : syracuseStep 309927 = 464891) B464891
theorem B310043 : Blo 307833 310043 := bstep (se 1 (by rfl) ⟨232532, by rfl⟩ : syracuseStep 310043 = 465065) B465065
theorem B310267 : Blo 307833 310267 := bstep (se 1 (by rfl) ⟨232700, by rfl⟩ : syracuseStep 310267 = 465401) B465401
theorem B310511 : Blo 307833 310511 := bstep (se 1 (by rfl) ⟨232883, by rfl⟩ : syracuseStep 310511 = 465767) B465767
theorem B310631 : Blo 307833 310631 := bstep (se 1 (by rfl) ⟨232973, by rfl⟩ : syracuseStep 310631 = 465947) B465947
theorem B310943 : Blo 307833 310943 := bstep (se 1 (by rfl) ⟨233207, by rfl⟩ : syracuseStep 310943 = 466415) B466415
theorem B311143 : Blo 307833 311143 := bstep (se 1 (by rfl) ⟨233357, by rfl⟩ : syracuseStep 311143 = 466715) B466715
theorem B311387 : Blo 307833 311387 := bstep (se 1 (by rfl) ⟨233540, by rfl⟩ : syracuseStep 311387 = 467081) B467081
theorem B5030009 : Blo 307833 5030009 := bstep (se 2 (by rfl) ⟨1886253, by rfl⟩ : syracuseStep 5030009 = 3772507) B3772507
theorem B311451 : Blo 307833 311451 := bstep (se 1 (by rfl) ⟨233588, by rfl⟩ : syracuseStep 311451 = 467177) B467177
theorem B2966291 : Blo 307833 2966291 := bstep (se 1 (by rfl) ⟨2224718, by rfl⟩ : syracuseStep 2966291 = 4449437) B4449437
theorem B1753883 : Blo 307833 1753883 := bstep (se 1 (by rfl) ⟨1315412, by rfl⟩ : syracuseStep 1753883 = 2630825) B2630825
theorem B2344463 : Blo 307833 2344463 := bstep (se 1 (by rfl) ⟨1758347, by rfl⟩ : syracuseStep 2344463 = 3516695) B3516695
theorem B346855 : Blo 307833 346855 := bstep (se 1 (by rfl) ⟨260141, by rfl⟩ : syracuseStep 346855 = 520283) B520283
theorem B1330175 : Blo 307833 1330175 := bstep (se 1 (by rfl) ⟨997631, by rfl⟩ : syracuseStep 1330175 = 1995263) B1995263
theorem B1559735 : Blo 307833 1559735 := bstep (se 1 (by rfl) ⟨1169801, by rfl⟩ : syracuseStep 1559735 = 2339603) B2339603
theorem B1756343 : Blo 307833 1756343 := bstep (se 1 (by rfl) ⟨1317257, by rfl⟩ : syracuseStep 1756343 = 2634515) B2634515
theorem B937631 : Blo 307833 937631 := bstep (se 1 (by rfl) ⟨703223, by rfl⟩ : syracuseStep 937631 = 1406447) B1406447
theorem B938153 : Blo 307833 938153 := bstep (se 2 (by rfl) ⟨351807, by rfl⟩ : syracuseStep 938153 = 703615) B703615
theorem B708871 : Blo 307833 708871 := bstep (se 1 (by rfl) ⟨531653, by rfl⟩ : syracuseStep 708871 = 1063307) B1063307
theorem B741727 : Blo 307833 741727 := bstep (se 1 (by rfl) ⟨556295, by rfl⟩ : syracuseStep 741727 = 1112591) B1112591
theorem B1561355 : Blo 307833 1561355 := bstep (se 1 (by rfl) ⟨1171016, by rfl⟩ : syracuseStep 1561355 = 2342033) B2342033
theorem B349519 : Blo 307833 349519 := bstep (se 1 (by rfl) ⟨262139, by rfl⟩ : syracuseStep 349519 = 524279) B524279
theorem B20011049 : Blo 307833 20011049 := bstep (se 2 (by rfl) ⟨7504143, by rfl⟩ : syracuseStep 20011049 = 15008287) B15008287
theorem B12114683 : Blo 307833 12114683 := bstep (se 1 (by rfl) ⟨9086012, by rfl⟩ : syracuseStep 12114683 = 18172025) B18172025
theorem B4480343 : Blo 307833 4480343 := bstep (se 1 (by rfl) ⟨3360257, by rfl⟩ : syracuseStep 4480343 = 6720515) B6720515
theorem B2384093 : Blo 307833 2384093 := bstep (se 3 (by rfl) ⟨447017, by rfl⟩ : syracuseStep 2384093 = 894035) B894035
theorem B3596831 : Blo 307833 3596831 := bstep (se 1 (by rfl) ⟨2697623, by rfl⟩ : syracuseStep 3596831 = 5395247) B5395247
theorem B1762175 : Blo 307833 1762175 := bstep (se 1 (by rfl) ⟨1321631, by rfl⟩ : syracuseStep 1762175 = 2643263) B2643263
theorem B1926281 : Blo 307833 1926281 := bstep (se 2 (by rfl) ⟨722355, by rfl⟩ : syracuseStep 1926281 = 1444711) B1444711
theorem B1172839 : Blo 307833 1172839 := bstep (se 1 (by rfl) ⟨879629, by rfl⟩ : syracuseStep 1172839 = 1759259) B1759259
theorem B1042091 : Blo 307833 1042091 := bstep (se 1 (by rfl) ⟨781568, by rfl⟩ : syracuseStep 1042091 = 1563137) B1563137
theorem B1173311 : Blo 307833 1173311 := bstep (se 1 (by rfl) ⟨879983, by rfl⟩ : syracuseStep 1173311 = 1759967) B1759967
theorem B781103 : Blo 307833 781103 := bstep (se 1 (by rfl) ⟨585827, by rfl⟩ : syracuseStep 781103 = 1171655) B1171655
theorem B6352643 : Blo 307833 6352643 := bstep (se 1 (by rfl) ⟨4764482, by rfl⟩ : syracuseStep 6352643 = 9528965) B9528965
theorem B1569779 : Blo 307833 1569779 := bstep (se 1 (by rfl) ⟨1177334, by rfl⟩ : syracuseStep 1569779 = 2354669) B2354669
theorem B1045817 : Blo 307833 1045817 := bstep (se 2 (by rfl) ⟨392181, by rfl⟩ : syracuseStep 1045817 = 784363) B784363
theorem B587263 : Blo 307833 587263 := bstep (se 1 (by rfl) ⟨440447, by rfl⟩ : syracuseStep 587263 = 880895) B880895
theorem B522409 : Blo 307833 522409 := bstep (se 2 (by rfl) ⟨195903, by rfl⟩ : syracuseStep 522409 = 391807) B391807
theorem B391655 : Blo 307833 391655 := bstep (se 1 (by rfl) ⟨293741, by rfl⟩ : syracuseStep 391655 = 587483) B587483
theorem B5044999 : Blo 307833 5044999 := bstep (se 1 (by rfl) ⟨3783749, by rfl⟩ : syracuseStep 5044999 = 7567499) B7567499
theorem B523145 : Blo 307833 523145 := bstep (se 2 (by rfl) ⟨196179, by rfl⟩ : syracuseStep 523145 = 392359) B392359
theorem B392303 : Blo 307833 392303 := bstep (se 1 (by rfl) ⟨294227, by rfl⟩ : syracuseStep 392303 = 588455) B588455
theorem B525359 : Blo 307833 525359 := bstep (se 1 (by rfl) ⟨394019, by rfl⟩ : syracuseStep 525359 = 788039) B788039
theorem B2360987 : Blo 307833 2360987 := bstep (se 1 (by rfl) ⟨1770740, by rfl⟩ : syracuseStep 2360987 = 3541481) B3541481
theorem B886783 : Blo 307833 886783 := bstep (se 1 (by rfl) ⟨665087, by rfl⟩ : syracuseStep 886783 = 1330175) B1330175
theorem B625087 : Blo 307833 625087 := bstep (se 1 (by rfl) ⟨468815, by rfl⟩ : syracuseStep 625087 = 937631) B937631
theorem B986303 : Blo 307833 986303 := bstep (se 1 (by rfl) ⟨739727, by rfl⟩ : syracuseStep 986303 = 1479455) B1479455
theorem B1183031 : Blo 307833 1183031 := bstep (se 1 (by rfl) ⟨887273, by rfl⟩ : syracuseStep 1183031 = 1774547) B1774547
theorem B462473 : Blo 307833 462473 := bstep (se 2 (by rfl) ⟨173427, by rfl⟩ : syracuseStep 462473 = 346855) B346855
theorem B13340699 : Blo 307833 13340699 := bstep (se 1 (by rfl) ⟨10005524, by rfl⟩ : syracuseStep 13340699 = 20011049) B20011049
theorem B888953 : Blo 307833 888953 := bstep (se 2 (by rfl) ⟨333357, by rfl⟩ : syracuseStep 888953 = 666715) B666715
theorem B1315055 : Blo 307833 1315055 := bstep (se 1 (by rfl) ⟨986291, by rfl⟩ : syracuseStep 1315055 = 1972583) B1972583
theorem B463295 : Blo 307833 463295 := bstep (se 1 (by rfl) ⟨347471, by rfl⟩ : syracuseStep 463295 = 694943) B694943
theorem B2986895 : Blo 307833 2986895 := bstep (se 1 (by rfl) ⟨2240171, by rfl⟩ : syracuseStep 2986895 = 4480343) B4480343
theorem B463871 : Blo 307833 463871 := bstep (se 1 (by rfl) ⟨347903, by rfl⟩ : syracuseStep 463871 = 695807) B695807
theorem B2397887 : Blo 307833 2397887 := bstep (se 1 (by rfl) ⟨1798415, by rfl⟩ : syracuseStep 2397887 = 3596831) B3596831
theorem B464639 : Blo 307833 464639 := bstep (se 1 (by rfl) ⟨348479, by rfl⟩ : syracuseStep 464639 = 696959) B696959
theorem B988969 : Blo 307833 988969 := bstep (se 2 (by rfl) ⟨370863, by rfl⟩ : syracuseStep 988969 = 741727) B741727
theorem B464831 : Blo 307833 464831 := bstep (se 1 (by rfl) ⟨348623, by rfl⟩ : syracuseStep 464831 = 697247) B697247
theorem B1284187 : Blo 307833 1284187 := bstep (se 1 (by rfl) ⟨963140, by rfl⟩ : syracuseStep 1284187 = 1926281) B1926281
theorem B1054889 : Blo 307833 1054889 := bstep (se 2 (by rfl) ⟨395583, by rfl⟩ : syracuseStep 1054889 = 791167) B791167
theorem B694727 : Blo 307833 694727 := bstep (se 1 (by rfl) ⟨521045, by rfl⟩ : syracuseStep 694727 = 1042091) B1042091
theorem B465575 : Blo 307833 465575 := bstep (se 1 (by rfl) ⟨349181, by rfl⟩ : syracuseStep 465575 = 698363) B698363
theorem B465599 : Blo 307833 465599 := bstep (se 1 (by rfl) ⟨349199, by rfl⟩ : syracuseStep 465599 = 698399) B698399
theorem B465647 : Blo 307833 465647 := bstep (se 1 (by rfl) ⟨349235, by rfl⟩ : syracuseStep 465647 = 698471) B698471
theorem B465791 : Blo 307833 465791 := bstep (se 1 (by rfl) ⟨349343, by rfl⟩ : syracuseStep 465791 = 698687) B698687
theorem B466025 : Blo 307833 466025 := bstep (se 2 (by rfl) ⟨174759, by rfl⟩ : syracuseStep 466025 = 349519) B349519
theorem B466151 : Blo 307833 466151 := bstep (se 1 (by rfl) ⟨349613, by rfl⟩ : syracuseStep 466151 = 699227) B699227
theorem B4235095 : Blo 307833 4235095 := bstep (se 1 (by rfl) ⟨3176321, by rfl⟩ : syracuseStep 4235095 = 6352643) B6352643
theorem B4464659 : Blo 307833 4464659 := bstep (se 1 (by rfl) ⟨3348494, by rfl⟩ : syracuseStep 4464659 = 6696989) B6696989
theorem B1318967 : Blo 307833 1318967 := bstep (se 1 (by rfl) ⟨989225, by rfl⟩ : syracuseStep 1318967 = 1978451) B1978451
theorem B696545 : Blo 307833 696545 := bstep (se 2 (by rfl) ⟨261204, by rfl⟩ : syracuseStep 696545 = 522409) B522409
theorem B467303 : Blo 307833 467303 := bstep (se 1 (by rfl) ⟨350477, by rfl⟩ : syracuseStep 467303 = 700955) B700955
theorem B467435 : Blo 307833 467435 := bstep (se 1 (by rfl) ⟨350576, by rfl⟩ : syracuseStep 467435 = 701153) B701153
theorem B697211 : Blo 307833 697211 := bstep (se 1 (by rfl) ⟨522908, by rfl⟩ : syracuseStep 697211 = 1045817) B1045817
theorem B6726665 : Blo 307833 6726665 := bstep (se 2 (by rfl) ⟨2522499, by rfl⟩ : syracuseStep 6726665 = 5044999) B5044999
theorem B3353339 : Blo 307833 3353339 := bstep (se 1 (by rfl) ⟨2515004, by rfl⟩ : syracuseStep 3353339 = 5030009) B5030009
theorem B2501741 : Blo 307833 2501741 := bstep (se 3 (by rfl) ⟨469076, by rfl⟩ : syracuseStep 2501741 = 938153) B938153
theorem B1977527 : Blo 307833 1977527 := bstep (se 1 (by rfl) ⟨1483145, by rfl⟩ : syracuseStep 1977527 = 2966291) B2966291
theorem B308327 : Blo 307833 308327 := bstep (se 1 (by rfl) ⟨231245, by rfl⟩ : syracuseStep 308327 = 462491) B462491
theorem B308447 : Blo 307833 308447 := bstep (se 1 (by rfl) ⟨231335, by rfl⟩ : syracuseStep 308447 = 462671) B462671
theorem B25572833 : Blo 307833 25572833 := bstep (se 2 (by rfl) ⟨9589812, by rfl⟩ : syracuseStep 25572833 = 19179625) B19179625
theorem B309095 : Blo 307833 309095 := bstep (se 1 (by rfl) ⟨231821, by rfl⟩ : syracuseStep 309095 = 463643) B463643
theorem B440191 : Blo 307833 440191 := bstep (se 1 (by rfl) ⟨330143, by rfl⟩ : syracuseStep 440191 = 660287) B660287
theorem B309275 : Blo 307833 309275 := bstep (se 1 (by rfl) ⟨231956, by rfl⟩ : syracuseStep 309275 = 463913) B463913
theorem B309279 : Blo 307833 309279 := bstep (se 1 (by rfl) ⟨231959, by rfl⟩ : syracuseStep 309279 = 463919) B463919
theorem B309607 : Blo 307833 309607 := bstep (se 1 (by rfl) ⟨232205, by rfl⟩ : syracuseStep 309607 = 464411) B464411
theorem B834401 : Blo 307833 834401 := bstep (se 2 (by rfl) ⟨312900, by rfl⟩ : syracuseStep 834401 = 625801) B625801
theorem B1489913 : Blo 307833 1489913 := bstep (se 2 (by rfl) ⟨558717, by rfl⟩ : syracuseStep 1489913 = 1117435) B1117435
theorem B310375 : Blo 307833 310375 := bstep (se 1 (by rfl) ⟨232781, by rfl⟩ : syracuseStep 310375 = 465563) B465563
theorem B310427 : Blo 307833 310427 := bstep (se 1 (by rfl) ⟨232820, by rfl⟩ : syracuseStep 310427 = 465641) B465641
theorem B8076455 : Blo 307833 8076455 := bstep (se 1 (by rfl) ⟨6057341, by rfl⟩ : syracuseStep 8076455 = 12114683) B12114683
theorem B835049 : Blo 307833 835049 := bstep (se 2 (by rfl) ⟨313143, by rfl⟩ : syracuseStep 835049 = 626287) B626287
theorem B311367 : Blo 307833 311367 := bstep (se 1 (by rfl) ⟨233525, by rfl⟩ : syracuseStep 311367 = 467051) B467051
theorem B1589395 : Blo 307833 1589395 := bstep (se 1 (by rfl) ⟨1192046, by rfl⟩ : syracuseStep 1589395 = 2384093) B2384093
theorem B311791 : Blo 307833 311791 := bstep (se 1 (by rfl) ⟨233843, by rfl⟩ : syracuseStep 311791 = 467687) B467687
theorem B311807 : Blo 307833 311807 := bstep (se 1 (by rfl) ⟨233855, by rfl⟩ : syracuseStep 311807 = 467711) B467711
theorem B838271 : Blo 307833 838271 := bstep (se 1 (by rfl) ⟨628703, by rfl⟩ : syracuseStep 838271 = 1257407) B1257407
theorem B3525443 : Blo 307833 3525443 := bstep (se 1 (by rfl) ⟨2644082, by rfl⟩ : syracuseStep 3525443 = 5288165) B5288165
theorem B3985807 : Blo 307833 3985807 := bstep (se 1 (by rfl) ⟨2989355, by rfl⟩ : syracuseStep 3985807 = 5978711) B5978711
theorem B7655867 : Blo 307833 7655867 := bstep (se 1 (by rfl) ⟨5741900, by rfl⟩ : syracuseStep 7655867 = 11483801) B11483801
theorem B348763 : Blo 307833 348763 := bstep (se 1 (by rfl) ⟨261572, by rfl⟩ : syracuseStep 348763 = 523145) B523145
theorem B7951931 : Blo 307833 7951931 := bstep (se 1 (by rfl) ⟨5963948, by rfl⟩ : syracuseStep 7951931 = 11927897) B11927897
theorem B1169255 : Blo 307833 1169255 := bstep (se 1 (by rfl) ⟨876941, by rfl⟩ : syracuseStep 1169255 = 1753883) B1753883
theorem B1562975 : Blo 307833 1562975 := bstep (se 1 (by rfl) ⟨1172231, by rfl⟩ : syracuseStep 1562975 = 2344463) B2344463
theorem B6674845 : Blo 307833 6674845 := bstep (se 3 (by rfl) ⟨1251533, by rfl⟩ : syracuseStep 6674845 = 2503067) B2503067
theorem B4479421 : Blo 307833 4479421 := bstep (se 3 (by rfl) ⟨839891, by rfl⟩ : syracuseStep 4479421 = 1679783) B1679783
theorem B809615 : Blo 307833 809615 := bstep (se 1 (by rfl) ⟨607211, by rfl⟩ : syracuseStep 809615 = 1214423) B1214423
theorem B1563785 : Blo 307833 1563785 := bstep (se 2 (by rfl) ⟨586419, by rfl⟩ : syracuseStep 1563785 = 1172839) B1172839
theorem B1039823 : Blo 307833 1039823 := bstep (se 1 (by rfl) ⟨779867, by rfl⟩ : syracuseStep 1039823 = 1559735) B1559735
theorem B1170895 : Blo 307833 1170895 := bstep (se 1 (by rfl) ⟨878171, by rfl⟩ : syracuseStep 1170895 = 1756343) B1756343
theorem B1040903 : Blo 307833 1040903 := bstep (se 1 (by rfl) ⟨780677, by rfl⟩ : syracuseStep 1040903 = 1561355) B1561355
theorem B747647 : Blo 307833 747647 := bstep (se 1 (by rfl) ⟨560735, by rfl⟩ : syracuseStep 747647 = 1121471) B1121471
theorem B1665469 : Blo 307833 1665469 := bstep (se 3 (by rfl) ⟨312275, by rfl⟩ : syracuseStep 1665469 = 624551) B624551
theorem B3238463 : Blo 307833 3238463 := bstep (se 1 (by rfl) ⟨2428847, by rfl⟩ : syracuseStep 3238463 = 4857695) B4857695
theorem B945161 : Blo 307833 945161 := bstep (se 2 (by rfl) ⟨354435, by rfl⟩ : syracuseStep 945161 = 708871) B708871
theorem B1174783 : Blo 307833 1174783 := bstep (se 1 (by rfl) ⟨881087, by rfl⟩ : syracuseStep 1174783 = 1762175) B1762175
theorem B782207 : Blo 307833 782207 := bstep (se 1 (by rfl) ⟨586655, by rfl⟩ : syracuseStep 782207 = 1173311) B1173311
theorem B1044413 : Blo 307833 1044413 := bstep (se 3 (by rfl) ⟨195827, by rfl⟩ : syracuseStep 1044413 = 391655) B391655
theorem B3567635 : Blo 307833 3567635 := bstep (se 1 (by rfl) ⟨2675726, by rfl⟩ : syracuseStep 3567635 = 5351453) B5351453
theorem B1405097 : Blo 307833 1405097 := bstep (se 2 (by rfl) ⟨526911, by rfl⟩ : syracuseStep 1405097 = 1053823) B1053823
theorem B520735 : Blo 307833 520735 := bstep (se 1 (by rfl) ⟨390551, by rfl⟩ : syracuseStep 520735 = 781103) B781103
theorem B783017 : Blo 307833 783017 := bstep (se 2 (by rfl) ⟨293631, by rfl⟩ : syracuseStep 783017 = 587263) B587263
theorem B1046141 : Blo 307833 1046141 := bstep (se 3 (by rfl) ⟨196151, by rfl⟩ : syracuseStep 1046141 = 392303) B392303
theorem B882535 : Blo 307833 882535 := bstep (se 1 (by rfl) ⟨661901, by rfl⟩ : syracuseStep 882535 = 1323803) B1323803
theorem B48527207 : Blo 307833 48527207 := bstep (se 1 (by rfl) ⟨36395405, by rfl⟩ : syracuseStep 48527207 = 72790811) B72790811
theorem B1046519 : Blo 307833 1046519 := bstep (se 1 (by rfl) ⟨784889, by rfl⟩ : syracuseStep 1046519 = 1569779) B1569779
theorem B7108667 : Blo 307833 7108667 := bstep (se 1 (by rfl) ⟨5331500, by rfl⟩ : syracuseStep 7108667 = 10663001) B10663001
theorem B882751 : Blo 307833 882751 := bstep (se 1 (by rfl) ⟨662063, by rfl⟩ : syracuseStep 882751 = 1324127) B1324127
theorem B7174439 : Blo 307833 7174439 := bstep (se 1 (by rfl) ⟨5380829, by rfl⟩ : syracuseStep 7174439 = 10761659) B10761659
theorem B1573991 : Blo 307833 1573991 := bstep (se 1 (by rfl) ⟨1180493, by rfl⟩ : syracuseStep 1573991 = 2360987) B2360987
theorem B558847 : Blo 307833 558847 := bstep (se 1 (by rfl) ⟨419135, by rfl⟩ : syracuseStep 558847 = 838271) B838271
theorem B788687 : Blo 307833 788687 := bstep (se 1 (by rfl) ⟨591515, by rfl⟩ : syracuseStep 788687 = 1183031) B1183031
theorem B7965053 : Blo 307833 7965053 := bstep (se 3 (by rfl) ⟨1493447, by rfl⟩ : syracuseStep 7965053 = 2986895) B2986895
theorem B1182377 : Blo 307833 1182377 := bstep (se 2 (by rfl) ⟨443391, by rfl⟩ : syracuseStep 1182377 = 886783) B886783
theorem B463151 : Blo 307833 463151 := bstep (se 1 (by rfl) ⟨347363, by rfl⟩ : syracuseStep 463151 = 694727) B694727
theorem B693215 : Blo 307833 693215 := bstep (se 1 (by rfl) ⟨519911, by rfl⟩ : syracuseStep 693215 = 1039823) B1039823
theorem B464363 : Blo 307833 464363 := bstep (se 1 (by rfl) ⟨348272, by rfl⟩ : syracuseStep 464363 = 696545) B696545
theorem B693935 : Blo 307833 693935 := bstep (se 1 (by rfl) ⟨520451, by rfl⟩ : syracuseStep 693935 = 1040903) B1040903
theorem B5314409 : Blo 307833 5314409 := bstep (se 2 (by rfl) ⟨1992903, by rfl⟩ : syracuseStep 5314409 = 3985807) B3985807
theorem B464807 : Blo 307833 464807 := bstep (se 1 (by rfl) ⟨348605, by rfl⟩ : syracuseStep 464807 = 697211) B697211
theorem B694313 : Blo 307833 694313 := bstep (se 2 (by rfl) ⟨260367, by rfl⟩ : syracuseStep 694313 = 520735) B520735
theorem B465017 : Blo 307833 465017 := bstep (se 2 (by rfl) ⟨174381, by rfl⟩ : syracuseStep 465017 = 348763) B348763
theorem B498431 : Blo 307833 498431 := bstep (se 1 (by rfl) ⟨373823, by rfl⟩ : syracuseStep 498431 = 747647) B747647
theorem B2235559 : Blo 307833 2235559 := bstep (se 1 (by rfl) ⟨1676669, by rfl⟩ : syracuseStep 2235559 = 3353339) B3353339
theorem B630107 : Blo 307833 630107 := bstep (se 1 (by rfl) ⟨472580, by rfl⟩ : syracuseStep 630107 = 945161) B945161
theorem B1318351 : Blo 307833 1318351 := bstep (se 1 (by rfl) ⟨988763, by rfl⟩ : syracuseStep 1318351 = 1977527) B1977527
theorem B1318625 : Blo 307833 1318625 := bstep (se 2 (by rfl) ⟨494484, by rfl⟩ : syracuseStep 1318625 = 988969) B988969
theorem B696275 : Blo 307833 696275 := bstep (se 1 (by rfl) ⟨522206, by rfl⟩ : syracuseStep 696275 = 1044413) B1044413
theorem B1712249 : Blo 307833 1712249 := bstep (se 2 (by rfl) ⟨642093, by rfl⟩ : syracuseStep 1712249 = 1284187) B1284187
theorem B2630141 : Blo 307833 2630141 := bstep (se 3 (by rfl) ⟨493151, by rfl⟩ : syracuseStep 2630141 = 986303) B986303
theorem B5972561 : Blo 307833 5972561 := bstep (se 2 (by rfl) ⟨2239710, by rfl⟩ : syracuseStep 5972561 = 4479421) B4479421
theorem B17048555 : Blo 307833 17048555 := bstep (se 1 (by rfl) ⟨12786416, by rfl⟩ : syracuseStep 17048555 = 25572833) B25572833
theorem B697427 : Blo 307833 697427 := bstep (se 1 (by rfl) ⟨523070, by rfl⟩ : syracuseStep 697427 = 1046141) B1046141
theorem B32351471 : Blo 307833 32351471 := bstep (se 1 (by rfl) ⟨24263603, by rfl⟩ : syracuseStep 32351471 = 48527207) B48527207
theorem B697679 : Blo 307833 697679 := bstep (se 1 (by rfl) ⟨523259, by rfl⟩ : syracuseStep 697679 = 1046519) B1046519
theorem B993275 : Blo 307833 993275 := bstep (se 1 (by rfl) ⟨744956, by rfl⟩ : syracuseStep 993275 = 1489913) B1489913
theorem B5384303 : Blo 307833 5384303 := bstep (se 1 (by rfl) ⟨4038227, by rfl⟩ : syracuseStep 5384303 = 8076455) B8076455
theorem B5646793 : Blo 307833 5646793 := bstep (se 2 (by rfl) ⟨2117547, by rfl⟩ : syracuseStep 5646793 = 4235095) B4235095
theorem B2370541 : Blo 307833 2370541 := bstep (se 3 (by rfl) ⟨444476, by rfl⟩ : syracuseStep 2370541 = 888953) B888953
theorem B308315 : Blo 307833 308315 := bstep (se 1 (by rfl) ⟨231236, by rfl⟩ : syracuseStep 308315 = 462473) B462473
theorem B8893799 : Blo 307833 8893799 := bstep (se 1 (by rfl) ⟨6670349, by rfl⟩ : syracuseStep 8893799 = 13340699) B13340699
theorem B308863 : Blo 307833 308863 := bstep (se 1 (by rfl) ⟨231647, by rfl⟩ : syracuseStep 308863 = 463295) B463295
theorem B833449 : Blo 307833 833449 := bstep (se 2 (by rfl) ⟨312543, by rfl⟩ : syracuseStep 833449 = 625087) B625087
theorem B309247 : Blo 307833 309247 := bstep (se 1 (by rfl) ⟨231935, by rfl⟩ : syracuseStep 309247 = 463871) B463871
theorem B309759 : Blo 307833 309759 := bstep (se 1 (by rfl) ⟨232319, by rfl⟩ : syracuseStep 309759 = 464639) B464639
theorem B309887 : Blo 307833 309887 := bstep (se 1 (by rfl) ⟨232415, by rfl⟩ : syracuseStep 309887 = 464831) B464831
theorem B703259 : Blo 307833 703259 := bstep (se 1 (by rfl) ⟨527444, by rfl⟩ : syracuseStep 703259 = 1054889) B1054889
theorem B539743 : Blo 307833 539743 := bstep (se 1 (by rfl) ⟨404807, by rfl⟩ : syracuseStep 539743 = 809615) B809615
theorem B310383 : Blo 307833 310383 := bstep (se 1 (by rfl) ⟨232787, by rfl⟩ : syracuseStep 310383 = 465575) B465575
theorem B310399 : Blo 307833 310399 := bstep (se 1 (by rfl) ⟨232799, by rfl⟩ : syracuseStep 310399 = 465599) B465599
theorem B310431 : Blo 307833 310431 := bstep (se 1 (by rfl) ⟨232823, by rfl⟩ : syracuseStep 310431 = 465647) B465647
theorem B310527 : Blo 307833 310527 := bstep (se 1 (by rfl) ⟨232895, by rfl⟩ : syracuseStep 310527 = 465791) B465791
theorem B310683 : Blo 307833 310683 := bstep (se 1 (by rfl) ⟨233012, by rfl⟩ : syracuseStep 310683 = 466025) B466025
theorem B310767 : Blo 307833 310767 := bstep (se 1 (by rfl) ⟨233075, by rfl⟩ : syracuseStep 310767 = 466151) B466151
theorem B311535 : Blo 307833 311535 := bstep (se 1 (by rfl) ⟨233651, by rfl⟩ : syracuseStep 311535 = 467303) B467303
theorem B311623 : Blo 307833 311623 := bstep (se 1 (by rfl) ⟨233717, by rfl⟩ : syracuseStep 311623 = 467435) B467435
theorem B8635901 : Blo 307833 8635901 := bstep (se 3 (by rfl) ⟨1619231, by rfl⟩ : syracuseStep 8635901 = 3238463) B3238463
theorem B2378423 : Blo 307833 2378423 := bstep (se 1 (by rfl) ⟨1783817, by rfl⟩ : syracuseStep 2378423 = 3567635) B3567635
theorem B936731 : Blo 307833 936731 := bstep (se 1 (by rfl) ⟨702548, by rfl⟩ : syracuseStep 936731 = 1405097) B1405097
theorem B8899793 : Blo 307833 8899793 := bstep (se 2 (by rfl) ⟨3337422, by rfl⟩ : syracuseStep 8899793 = 6674845) B6674845
theorem B4739111 : Blo 307833 4739111 := bstep (se 1 (by rfl) ⟨3554333, by rfl⟩ : syracuseStep 4739111 = 7108667) B7108667
theorem B1561193 : Blo 307833 1561193 := bstep (se 2 (by rfl) ⟨585447, by rfl⟩ : syracuseStep 1561193 = 1170895) B1170895
theorem B2119193 : Blo 307833 2119193 := bstep (se 2 (by rfl) ⟨794697, by rfl⟩ : syracuseStep 2119193 = 1589395) B1589395
theorem B350239 : Blo 307833 350239 := bstep (se 1 (by rfl) ⟨262679, by rfl⟩ : syracuseStep 350239 = 525359) B525359
theorem B2350295 : Blo 307833 2350295 := bstep (se 1 (by rfl) ⟨1762721, by rfl⟩ : syracuseStep 2350295 = 3525443) B3525443
theorem B876703 : Blo 307833 876703 := bstep (se 1 (by rfl) ⟨657527, by rfl⟩ : syracuseStep 876703 = 1315055) B1315055
theorem B5103911 : Blo 307833 5103911 := bstep (se 1 (by rfl) ⟨3827933, by rfl⟩ : syracuseStep 5103911 = 7655867) B7655867
theorem B2220625 : Blo 307833 2220625 := bstep (se 2 (by rfl) ⟨832734, by rfl⟩ : syracuseStep 2220625 = 1665469) B1665469
theorem B5301287 : Blo 307833 5301287 := bstep (se 1 (by rfl) ⟨3975965, by rfl⟩ : syracuseStep 5301287 = 7951931) B7951931
theorem B1598591 : Blo 307833 1598591 := bstep (se 1 (by rfl) ⟨1198943, by rfl⟩ : syracuseStep 1598591 = 2397887) B2397887
theorem B779503 : Blo 307833 779503 := bstep (se 1 (by rfl) ⟨584627, by rfl⟩ : syracuseStep 779503 = 1169255) B1169255
theorem B1041983 : Blo 307833 1041983 := bstep (se 1 (by rfl) ⟨781487, by rfl⟩ : syracuseStep 1041983 = 1562975) B1562975
theorem B1566377 : Blo 307833 1566377 := bstep (se 2 (by rfl) ⟨587391, by rfl⟩ : syracuseStep 1566377 = 1174783) B1174783
theorem B1042523 : Blo 307833 1042523 := bstep (se 1 (by rfl) ⟨781892, by rfl⟩ : syracuseStep 1042523 = 1563785) B1563785
theorem B2976439 : Blo 307833 2976439 := bstep (se 1 (by rfl) ⟨2232329, by rfl⟩ : syracuseStep 2976439 = 4464659) B4464659
theorem B879311 : Blo 307833 879311 := bstep (se 1 (by rfl) ⟨659483, by rfl⟩ : syracuseStep 879311 = 1318967) B1318967
theorem B4484443 : Blo 307833 4484443 := bstep (se 1 (by rfl) ⟨3363332, by rfl⟩ : syracuseStep 4484443 = 6726665) B6726665
theorem B1667827 : Blo 307833 1667827 := bstep (se 1 (by rfl) ⟨1250870, by rfl⟩ : syracuseStep 1667827 = 2501741) B2501741
theorem B2225069 : Blo 307833 2225069 := bstep (se 3 (by rfl) ⟨417200, by rfl⟩ : syracuseStep 2225069 = 834401) B834401
theorem B1176713 : Blo 307833 1176713 := bstep (se 2 (by rfl) ⟨441267, by rfl⟩ : syracuseStep 1176713 = 882535) B882535
theorem B586921 : Blo 307833 586921 := bstep (se 2 (by rfl) ⟨220095, by rfl⟩ : syracuseStep 586921 = 440191) B440191
theorem B521471 : Blo 307833 521471 := bstep (se 1 (by rfl) ⟨391103, by rfl⟩ : syracuseStep 521471 = 782207) B782207
theorem B1177001 : Blo 307833 1177001 := bstep (se 2 (by rfl) ⟨441375, by rfl⟩ : syracuseStep 1177001 = 882751) B882751
theorem B522011 : Blo 307833 522011 := bstep (se 1 (by rfl) ⟨391508, by rfl⟩ : syracuseStep 522011 = 783017) B783017
theorem B4782959 : Blo 307833 4782959 := bstep (se 1 (by rfl) ⟨3587219, by rfl⟩ : syracuseStep 4782959 = 7174439) B7174439
theorem B556699 : Blo 307833 556699 := bstep (se 1 (by rfl) ⟨417524, by rfl⟩ : syracuseStep 556699 = 835049) B835049
theorem B1049327 : Blo 307833 1049327 := bstep (se 1 (by rfl) ⟨786995, by rfl⟩ : syracuseStep 1049327 = 1573991) B1573991
theorem B525791 : Blo 307833 525791 := bstep (se 1 (by rfl) ⟨394343, by rfl⟩ : syracuseStep 525791 = 788687) B788687
theorem B5310035 : Blo 307833 5310035 := bstep (se 1 (by rfl) ⟨3982526, by rfl⟩ : syracuseStep 5310035 = 7965053) B7965053
theorem B788251 : Blo 307833 788251 := bstep (se 1 (by rfl) ⟨591188, by rfl⟩ : syracuseStep 788251 = 1182377) B1182377
theorem B5933195 : Blo 307833 5933195 := bstep (se 1 (by rfl) ⟨4449896, by rfl⟩ : syracuseStep 5933195 = 8899793) B8899793
theorem B462143 : Blo 307833 462143 := bstep (se 1 (by rfl) ⟨346607, by rfl⟩ : syracuseStep 462143 = 693215) B693215
theorem B3968585 : Blo 307833 3968585 := bstep (se 2 (by rfl) ⟨1488219, by rfl⟩ : syracuseStep 3968585 = 2976439) B2976439
theorem B1412795 : Blo 307833 1412795 := bstep (se 1 (by rfl) ⟨1059596, by rfl⟩ : syracuseStep 1412795 = 2119193) B2119193
theorem B462623 : Blo 307833 462623 := bstep (se 1 (by rfl) ⟨346967, by rfl⟩ : syracuseStep 462623 = 693935) B693935
theorem B3542939 : Blo 307833 3542939 := bstep (se 1 (by rfl) ⟨2657204, by rfl⟩ : syracuseStep 3542939 = 5314409) B5314409
theorem B462875 : Blo 307833 462875 := bstep (se 1 (by rfl) ⟨347156, by rfl⟩ : syracuseStep 462875 = 694313) B694313
theorem B464183 : Blo 307833 464183 := bstep (se 1 (by rfl) ⟨348137, by rfl⟩ : syracuseStep 464183 = 696275) B696275
theorem B464951 : Blo 307833 464951 := bstep (se 1 (by rfl) ⟨348713, by rfl⟩ : syracuseStep 464951 = 697427) B697427
theorem B21567647 : Blo 307833 21567647 := bstep (se 1 (by rfl) ⟨16175735, by rfl⟩ : syracuseStep 21567647 = 32351471) B32351471
theorem B465119 : Blo 307833 465119 := bstep (se 1 (by rfl) ⟨348839, by rfl⟩ : syracuseStep 465119 = 697679) B697679
theorem B694655 : Blo 307833 694655 := bstep (se 1 (by rfl) ⟨520991, by rfl⟩ : syracuseStep 694655 = 1041983) B1041983
theorem B662183 : Blo 307833 662183 := bstep (se 1 (by rfl) ⟨496637, by rfl⟩ : syracuseStep 662183 = 993275) B993275
theorem B695015 : Blo 307833 695015 := bstep (se 1 (by rfl) ⟨521261, by rfl⟩ : syracuseStep 695015 = 1042523) B1042523
theorem B2497949 : Blo 307833 2497949 := bstep (se 3 (by rfl) ⟨468365, by rfl⟩ : syracuseStep 2497949 = 936731) B936731
theorem B466985 : Blo 307833 466985 := bstep (se 2 (by rfl) ⟨175119, by rfl⟩ : syracuseStep 466985 = 350239) B350239
theorem B1483379 : Blo 307833 1483379 := bstep (se 1 (by rfl) ⟨1112534, by rfl⟩ : syracuseStep 1483379 = 2225069) B2225069
theorem B468839 : Blo 307833 468839 := bstep (se 1 (by rfl) ⟨351629, by rfl⟩ : syracuseStep 468839 = 703259) B703259
theorem B3188639 : Blo 307833 3188639 := bstep (se 1 (by rfl) ⟨2391479, by rfl⟩ : syracuseStep 3188639 = 4782959) B4782959
theorem B2960833 : Blo 307833 2960833 := bstep (se 2 (by rfl) ⟨1110312, by rfl⟩ : syracuseStep 2960833 = 2220625) B2220625
theorem B3159407 : Blo 307833 3159407 := bstep (se 1 (by rfl) ⟨2369555, by rfl⟩ : syracuseStep 3159407 = 4739111) B4739111
theorem B308767 : Blo 307833 308767 := bstep (se 1 (by rfl) ⟨231575, by rfl⟩ : syracuseStep 308767 = 463151) B463151
theorem B309575 : Blo 307833 309575 := bstep (se 1 (by rfl) ⟨232181, by rfl⟩ : syracuseStep 309575 = 464363) B464363
theorem B309871 : Blo 307833 309871 := bstep (se 1 (by rfl) ⟨232403, by rfl⟩ : syracuseStep 309871 = 464807) B464807
theorem B3160721 : Blo 307833 3160721 := bstep (se 2 (by rfl) ⟨1185270, by rfl⟩ : syracuseStep 3160721 = 2370541) B2370541
theorem B310011 : Blo 307833 310011 := bstep (se 1 (by rfl) ⟨232508, by rfl⟩ : syracuseStep 310011 = 465017) B465017
theorem B5979257 : Blo 307833 5979257 := bstep (se 2 (by rfl) ⟨2242221, by rfl⟩ : syracuseStep 5979257 = 4484443) B4484443
theorem B1753427 : Blo 307833 1753427 := bstep (se 1 (by rfl) ⟨1315070, by rfl⟩ : syracuseStep 1753427 = 2630141) B2630141
theorem B3981707 : Blo 307833 3981707 := bstep (se 1 (by rfl) ⟨2986280, by rfl⟩ : syracuseStep 3981707 = 5972561) B5972561
theorem B1065727 : Blo 307833 1065727 := bstep (se 1 (by rfl) ⟨799295, by rfl⟩ : syracuseStep 1065727 = 1598591) B1598591
theorem B3589535 : Blo 307833 3589535 := bstep (se 1 (by rfl) ⟨2692151, by rfl⟩ : syracuseStep 3589535 = 5384303) B5384303
theorem B6342461 : Blo 307833 6342461 := bstep (se 3 (by rfl) ⟨1189211, by rfl⟩ : syracuseStep 6342461 = 2378423) B2378423
theorem B1329149 : Blo 307833 1329149 := bstep (se 3 (by rfl) ⟨249215, by rfl⟩ : syracuseStep 1329149 = 498431) B498431
theorem B347647 : Blo 307833 347647 := bstep (se 1 (by rfl) ⟨260735, by rfl⟩ : syracuseStep 347647 = 521471) B521471
theorem B348007 : Blo 307833 348007 := bstep (se 1 (by rfl) ⟨261005, by rfl⟩ : syracuseStep 348007 = 522011) B522011
theorem B1757801 : Blo 307833 1757801 := bstep (se 2 (by rfl) ⟨659175, by rfl⟩ : syracuseStep 1757801 = 1318351) B1318351
theorem B742265 : Blo 307833 742265 := bstep (se 2 (by rfl) ⟨278349, by rfl⟩ : syracuseStep 742265 = 556699) B556699
theorem B1168937 : Blo 307833 1168937 := bstep (se 2 (by rfl) ⟨438351, by rfl⟩ : syracuseStep 1168937 = 876703) B876703
theorem B1039337 : Blo 307833 1039337 := bstep (se 2 (by rfl) ⟨389751, by rfl⟩ : syracuseStep 1039337 = 779503) B779503
theorem B745129 : Blo 307833 745129 := bstep (se 2 (by rfl) ⟨279423, by rfl⟩ : syracuseStep 745129 = 558847) B558847
theorem B1040795 : Blo 307833 1040795 := bstep (se 1 (by rfl) ⟨780596, by rfl⟩ : syracuseStep 1040795 = 1561193) B1561193
theorem B7529057 : Blo 307833 7529057 := bstep (se 2 (by rfl) ⟨2823396, by rfl⟩ : syracuseStep 7529057 = 5646793) B5646793
theorem B23029069 : Blo 307833 23029069 := bstep (se 3 (by rfl) ⟨4317950, by rfl⟩ : syracuseStep 23029069 = 8635901) B8635901
theorem B1566863 : Blo 307833 1566863 := bstep (se 1 (by rfl) ⟨1175147, by rfl⟩ : syracuseStep 1566863 = 2350295) B2350295
theorem B420071 : Blo 307833 420071 := bstep (se 1 (by rfl) ⟨315053, by rfl⟩ : syracuseStep 420071 = 630107) B630107
theorem B879083 : Blo 307833 879083 := bstep (se 1 (by rfl) ⟨659312, by rfl⟩ : syracuseStep 879083 = 1318625) B1318625
theorem B1141499 : Blo 307833 1141499 := bstep (se 1 (by rfl) ⟨856124, by rfl⟩ : syracuseStep 1141499 = 1712249) B1712249
theorem B3402607 : Blo 307833 3402607 := bstep (se 1 (by rfl) ⟨2551955, by rfl⟩ : syracuseStep 3402607 = 5103911) B5103911
theorem B11365703 : Blo 307833 11365703 := bstep (se 1 (by rfl) ⟨8524277, by rfl⟩ : syracuseStep 11365703 = 17048555) B17048555
theorem B3534191 : Blo 307833 3534191 := bstep (se 1 (by rfl) ⟨2650643, by rfl⟩ : syracuseStep 3534191 = 5301287) B5301287
theorem B2223769 : Blo 307833 2223769 := bstep (se 2 (by rfl) ⟨833913, by rfl⟩ : syracuseStep 2223769 = 1667827) B1667827
theorem B1044251 : Blo 307833 1044251 := bstep (se 1 (by rfl) ⟨783188, by rfl⟩ : syracuseStep 1044251 = 1566377) B1566377
theorem B782561 : Blo 307833 782561 := bstep (se 2 (by rfl) ⟨293460, by rfl⟩ : syracuseStep 782561 = 586921) B586921
theorem B586207 : Blo 307833 586207 := bstep (se 1 (by rfl) ⟨439655, by rfl⟩ : syracuseStep 586207 = 879311) B879311
theorem B1111265 : Blo 307833 1111265 := bstep (se 2 (by rfl) ⟨416724, by rfl⟩ : syracuseStep 1111265 = 833449) B833449
theorem B784475 : Blo 307833 784475 := bstep (se 1 (by rfl) ⟨588356, by rfl⟩ : syracuseStep 784475 = 1176713) B1176713
theorem B5929199 : Blo 307833 5929199 := bstep (se 1 (by rfl) ⟨4446899, by rfl⟩ : syracuseStep 5929199 = 8893799) B8893799
theorem B784667 : Blo 307833 784667 := bstep (se 1 (by rfl) ⟨588500, by rfl⟩ : syracuseStep 784667 = 1177001) B1177001
theorem B719657 : Blo 307833 719657 := bstep (se 2 (by rfl) ⟨269871, by rfl⟩ : syracuseStep 719657 = 539743) B539743
theorem B2980745 : Blo 307833 2980745 := bstep (se 2 (by rfl) ⟨1117779, by rfl⟩ : syracuseStep 2980745 = 2235559) B2235559
theorem B2654471 : Blo 307833 2654471 := bstep (se 1 (by rfl) ⟨1990853, by rfl⟩ : syracuseStep 2654471 = 3981707) B3981707
theorem B2393023 : Blo 307833 2393023 := bstep (se 1 (by rfl) ⟨1794767, by rfl⟩ : syracuseStep 2393023 = 3589535) B3589535
theorem B3540023 : Blo 307833 3540023 := bstep (se 1 (by rfl) ⟨2655017, by rfl⟩ : syracuseStep 3540023 = 5310035) B5310035
theorem B4228307 : Blo 307833 4228307 := bstep (se 1 (by rfl) ⟨3171230, by rfl⟩ : syracuseStep 4228307 = 6342461) B6342461
theorem B30705425 : Blo 307833 30705425 := bstep (se 2 (by rfl) ⟨11514534, by rfl⟩ : syracuseStep 30705425 = 23029069) B23029069
theorem B1051001 : Blo 307833 1051001 := bstep (se 2 (by rfl) ⟨394125, by rfl⟩ : syracuseStep 1051001 = 788251) B788251
theorem B2361959 : Blo 307833 2361959 := bstep (se 1 (by rfl) ⟨1771469, by rfl⟩ : syracuseStep 2361959 = 3542939) B3542939
theorem B494843 : Blo 307833 494843 := bstep (se 1 (by rfl) ⟨371132, by rfl⟩ : syracuseStep 494843 = 742265) B742265
theorem B463103 : Blo 307833 463103 := bstep (se 1 (by rfl) ⟨347327, by rfl⟩ : syracuseStep 463103 = 694655) B694655
theorem B463343 : Blo 307833 463343 := bstep (se 1 (by rfl) ⟨347507, by rfl⟩ : syracuseStep 463343 = 695015) B695015
theorem B692891 : Blo 307833 692891 := bstep (se 1 (by rfl) ⟨519668, by rfl⟩ : syracuseStep 692891 = 1039337) B1039337
theorem B463529 : Blo 307833 463529 := bstep (se 2 (by rfl) ⟨173823, by rfl⟩ : syracuseStep 463529 = 347647) B347647
theorem B1250237 : Blo 307833 1250237 := bstep (se 3 (by rfl) ⟨234419, by rfl⟩ : syracuseStep 1250237 = 468839) B468839
theorem B464009 : Blo 307833 464009 := bstep (se 2 (by rfl) ⟨174003, by rfl⟩ : syracuseStep 464009 = 348007) B348007
theorem B3544397 : Blo 307833 3544397 := bstep (se 3 (by rfl) ⟨664574, by rfl⟩ : syracuseStep 3544397 = 1329149) B1329149
theorem B693863 : Blo 307833 693863 := bstep (se 1 (by rfl) ⟨520397, by rfl⟩ : syracuseStep 693863 = 1040795) B1040795
theorem B5019371 : Blo 307833 5019371 := bstep (se 1 (by rfl) ⟨3764528, by rfl⟩ : syracuseStep 5019371 = 7529057) B7529057
theorem B988919 : Blo 307833 988919 := bstep (se 1 (by rfl) ⟨741689, by rfl⟩ : syracuseStep 988919 = 1483379) B1483379
theorem B57513725 : Blo 307833 57513725 := bstep (se 3 (by rfl) ⟨10783823, by rfl⟩ : syracuseStep 57513725 = 21567647) B21567647
theorem B1120189 : Blo 307833 1120189 := bstep (se 3 (by rfl) ⟨210035, by rfl⟩ : syracuseStep 1120189 = 420071) B420071
theorem B7577135 : Blo 307833 7577135 := bstep (se 1 (by rfl) ⟨5682851, by rfl⟩ : syracuseStep 7577135 = 11365703) B11365703
theorem B696167 : Blo 307833 696167 := bstep (se 1 (by rfl) ⟨522125, by rfl⟩ : syracuseStep 696167 = 1044251) B1044251
theorem B3974021 : Blo 307833 3974021 := bstep (se 4 (by rfl) ⟨372564, by rfl⟩ : syracuseStep 3974021 = 745129) B745129
theorem B2106271 : Blo 307833 2106271 := bstep (se 1 (by rfl) ⟨1579703, by rfl⟩ : syracuseStep 2106271 = 3159407) B3159407
theorem B2107147 : Blo 307833 2107147 := bstep (se 1 (by rfl) ⟨1580360, by rfl⟩ : syracuseStep 2107147 = 3160721) B3160721
theorem B699551 : Blo 307833 699551 := bstep (se 1 (by rfl) ⟨524663, by rfl⟩ : syracuseStep 699551 = 1049327) B1049327
theorem B308095 : Blo 307833 308095 := bstep (se 1 (by rfl) ⟨231071, by rfl⟩ : syracuseStep 308095 = 462143) B462143
theorem B308415 : Blo 307833 308415 := bstep (se 1 (by rfl) ⟨231311, by rfl⟩ : syracuseStep 308415 = 462623) B462623
theorem B308583 : Blo 307833 308583 := bstep (se 1 (by rfl) ⟨231437, by rfl⟩ : syracuseStep 308583 = 462875) B462875
theorem B309455 : Blo 307833 309455 := bstep (se 1 (by rfl) ⟨232091, by rfl⟩ : syracuseStep 309455 = 464183) B464183
theorem B4536809 : Blo 307833 4536809 := bstep (se 2 (by rfl) ⟨1701303, by rfl⟩ : syracuseStep 4536809 = 3402607) B3402607
theorem B5683877 : Blo 307833 5683877 := bstep (se 4 (by rfl) ⟨532863, by rfl⟩ : syracuseStep 5683877 = 1065727) B1065727
theorem B309967 : Blo 307833 309967 := bstep (se 1 (by rfl) ⟨232475, by rfl⟩ : syracuseStep 309967 = 464951) B464951
theorem B310079 : Blo 307833 310079 := bstep (se 1 (by rfl) ⟨232559, by rfl⟩ : syracuseStep 310079 = 465119) B465119
theorem B441455 : Blo 307833 441455 := bstep (se 1 (by rfl) ⟨331091, by rfl⟩ : syracuseStep 441455 = 662183) B662183
theorem B3947777 : Blo 307833 3947777 := bstep (se 2 (by rfl) ⟨1480416, by rfl⟩ : syracuseStep 3947777 = 2960833) B2960833
theorem B2965025 : Blo 307833 2965025 := bstep (se 2 (by rfl) ⟨1111884, by rfl⟩ : syracuseStep 2965025 = 2223769) B2223769
theorem B311323 : Blo 307833 311323 := bstep (se 1 (by rfl) ⟨233492, by rfl⟩ : syracuseStep 311323 = 466985) B466985
theorem B740843 : Blo 307833 740843 := bstep (se 1 (by rfl) ⟨555632, by rfl⟩ : syracuseStep 740843 = 1111265) B1111265
theorem B3952799 : Blo 307833 3952799 := bstep (se 1 (by rfl) ⟨2964599, by rfl⟩ : syracuseStep 3952799 = 5929199) B5929199
theorem B479771 : Blo 307833 479771 := bstep (se 1 (by rfl) ⟨359828, by rfl⟩ : syracuseStep 479771 = 719657) B719657
theorem B1987163 : Blo 307833 1987163 := bstep (se 1 (by rfl) ⟨1490372, by rfl⟩ : syracuseStep 1987163 = 2980745) B2980745
theorem B3986171 : Blo 307833 3986171 := bstep (se 1 (by rfl) ⟨2989628, by rfl⟩ : syracuseStep 3986171 = 5979257) B5979257
theorem B1168951 : Blo 307833 1168951 := bstep (se 1 (by rfl) ⟨876713, by rfl⟩ : syracuseStep 1168951 = 1753427) B1753427
theorem B350527 : Blo 307833 350527 := bstep (se 1 (by rfl) ⟨262895, by rfl⟩ : syracuseStep 350527 = 525791) B525791
theorem B3955463 : Blo 307833 3955463 := bstep (se 1 (by rfl) ⟨2966597, by rfl⟩ : syracuseStep 3955463 = 5933195) B5933195
theorem B2645723 : Blo 307833 2645723 := bstep (se 1 (by rfl) ⟨1984292, by rfl⟩ : syracuseStep 2645723 = 3968585) B3968585
theorem B941863 : Blo 307833 941863 := bstep (se 1 (by rfl) ⟨706397, by rfl⟩ : syracuseStep 941863 = 1412795) B1412795
theorem B1171867 : Blo 307833 1171867 := bstep (se 1 (by rfl) ⟨878900, by rfl⟩ : syracuseStep 1171867 = 1757801) B1757801
theorem B779291 : Blo 307833 779291 := bstep (se 1 (by rfl) ⟨584468, by rfl⟩ : syracuseStep 779291 = 1168937) B1168937
theorem B1665299 : Blo 307833 1665299 := bstep (se 1 (by rfl) ⟨1248974, by rfl⟩ : syracuseStep 1665299 = 2497949) B2497949
theorem B781609 : Blo 307833 781609 := bstep (se 2 (by rfl) ⟨293103, by rfl⟩ : syracuseStep 781609 = 586207) B586207
theorem B2125759 : Blo 307833 2125759 := bstep (se 1 (by rfl) ⟨1594319, by rfl⟩ : syracuseStep 2125759 = 3188639) B3188639
theorem B1044575 : Blo 307833 1044575 := bstep (se 1 (by rfl) ⟨783431, by rfl⟩ : syracuseStep 1044575 = 1566863) B1566863
theorem B586055 : Blo 307833 586055 := bstep (se 1 (by rfl) ⟨439541, by rfl⟩ : syracuseStep 586055 = 879083) B879083
theorem B3043997 : Blo 307833 3043997 := bstep (se 3 (by rfl) ⟨570749, by rfl⟩ : syracuseStep 3043997 = 1141499) B1141499
theorem B2356127 : Blo 307833 2356127 := bstep (se 1 (by rfl) ⟨1767095, by rfl⟩ : syracuseStep 2356127 = 3534191) B3534191
theorem B521707 : Blo 307833 521707 := bstep (se 1 (by rfl) ⟨391280, by rfl⟩ : syracuseStep 521707 = 782561) B782561
theorem B522983 : Blo 307833 522983 := bstep (se 1 (by rfl) ⟨392237, by rfl⟩ : syracuseStep 522983 = 784475) B784475
theorem B523111 : Blo 307833 523111 := bstep (se 1 (by rfl) ⟨392333, by rfl⟩ : syracuseStep 523111 = 784667) B784667
theorem B1769647 : Blo 307833 1769647 := bstep (se 1 (by rfl) ⟨1327235, by rfl⟩ : syracuseStep 1769647 = 2654471) B2654471
theorem B2360015 : Blo 307833 2360015 := bstep (se 1 (by rfl) ⟨1770011, by rfl⟩ : syracuseStep 2360015 = 3540023) B3540023
theorem B2818871 : Blo 307833 2818871 := bstep (se 1 (by rfl) ⟨2114153, by rfl⟩ : syracuseStep 2818871 = 4228307) B4228307
theorem B1574639 : Blo 307833 1574639 := bstep (se 1 (by rfl) ⟨1180979, by rfl⟩ : syracuseStep 1574639 = 2361959) B2361959
theorem B493895 : Blo 307833 493895 := bstep (se 1 (by rfl) ⟨370421, by rfl⟩ : syracuseStep 493895 = 740843) B740843
theorem B461927 : Blo 307833 461927 := bstep (se 1 (by rfl) ⟨346445, by rfl⟩ : syracuseStep 461927 = 692891) B692891
theorem B2657447 : Blo 307833 2657447 := bstep (se 1 (by rfl) ⟨1993085, by rfl⟩ : syracuseStep 2657447 = 3986171) B3986171
theorem B2362931 : Blo 307833 2362931 := bstep (se 1 (by rfl) ⟨1772198, by rfl⟩ : syracuseStep 2362931 = 3544397) B3544397
theorem B462575 : Blo 307833 462575 := bstep (se 1 (by rfl) ⟨346931, by rfl⟩ : syracuseStep 462575 = 693863) B693863
theorem B3346247 : Blo 307833 3346247 := bstep (se 1 (by rfl) ⟨2509685, by rfl⟩ : syracuseStep 3346247 = 5019371) B5019371
theorem B659279 : Blo 307833 659279 := bstep (se 1 (by rfl) ⟨494459, by rfl⟩ : syracuseStep 659279 = 988919) B988919
theorem B38342483 : Blo 307833 38342483 := bstep (se 1 (by rfl) ⟨28756862, by rfl⟩ : syracuseStep 38342483 = 57513725) B57513725
theorem B5051423 : Blo 307833 5051423 := bstep (se 1 (by rfl) ⟨3788567, by rfl⟩ : syracuseStep 5051423 = 7577135) B7577135
theorem B464111 : Blo 307833 464111 := bstep (se 1 (by rfl) ⟨348083, by rfl⟩ : syracuseStep 464111 = 696167) B696167
theorem B695609 : Blo 307833 695609 := bstep (se 2 (by rfl) ⟨260853, by rfl⟩ : syracuseStep 695609 = 521707) B521707
theorem B466367 : Blo 307833 466367 := bstep (se 1 (by rfl) ⟨349775, by rfl⟩ : syracuseStep 466367 = 699551) B699551
theorem B696383 : Blo 307833 696383 := bstep (se 1 (by rfl) ⟨522287, by rfl⟩ : syracuseStep 696383 = 1044575) B1044575
theorem B467369 : Blo 307833 467369 := bstep (se 2 (by rfl) ⟨175263, by rfl⟩ : syracuseStep 467369 = 350527) B350527
theorem B1319581 : Blo 307833 1319581 := bstep (se 3 (by rfl) ⟨247421, by rfl⟩ : syracuseStep 1319581 = 494843) B494843
theorem B697481 : Blo 307833 697481 := bstep (se 2 (by rfl) ⟨261555, by rfl⟩ : syracuseStep 697481 = 523111) B523111
theorem B3024539 : Blo 307833 3024539 := bstep (se 1 (by rfl) ⟨2268404, by rfl⟩ : syracuseStep 3024539 = 4536809) B4536809
theorem B2631851 : Blo 307833 2631851 := bstep (se 1 (by rfl) ⟨1973888, by rfl⟩ : syracuseStep 2631851 = 3947777) B3947777
theorem B1976683 : Blo 307833 1976683 := bstep (se 1 (by rfl) ⟨1482512, by rfl⟩ : syracuseStep 1976683 = 2965025) B2965025
theorem B1255817 : Blo 307833 1255817 := bstep (se 2 (by rfl) ⟨470931, by rfl⟩ : syracuseStep 1255817 = 941863) B941863
theorem B3190697 : Blo 307833 3190697 := bstep (se 2 (by rfl) ⟨1196511, by rfl⟩ : syracuseStep 3190697 = 2393023) B2393023
theorem B700667 : Blo 307833 700667 := bstep (se 1 (by rfl) ⟨525500, by rfl⟩ : syracuseStep 700667 = 1051001) B1051001
theorem B2635199 : Blo 307833 2635199 := bstep (se 1 (by rfl) ⟨1976399, by rfl⟩ : syracuseStep 2635199 = 3952799) B3952799
theorem B308735 : Blo 307833 308735 := bstep (se 1 (by rfl) ⟨231551, by rfl⟩ : syracuseStep 308735 = 463103) B463103
theorem B308895 : Blo 307833 308895 := bstep (se 1 (by rfl) ⟨231671, by rfl⟩ : syracuseStep 308895 = 463343) B463343
theorem B1324775 : Blo 307833 1324775 := bstep (se 1 (by rfl) ⟨993581, by rfl⟩ : syracuseStep 1324775 = 1987163) B1987163
theorem B309019 : Blo 307833 309019 := bstep (se 1 (by rfl) ⟨231764, by rfl⟩ : syracuseStep 309019 = 463529) B463529
theorem B833491 : Blo 307833 833491 := bstep (se 1 (by rfl) ⟨625118, by rfl⟩ : syracuseStep 833491 = 1250237) B1250237
theorem B309339 : Blo 307833 309339 := bstep (se 1 (by rfl) ⟨232004, by rfl⟩ : syracuseStep 309339 = 464009) B464009
theorem B2636975 : Blo 307833 2636975 := bstep (se 1 (by rfl) ⟨1977731, by rfl⟩ : syracuseStep 2636975 = 3955463) B3955463
theorem B2834345 : Blo 307833 2834345 := bstep (se 2 (by rfl) ⟨1062879, by rfl⟩ : syracuseStep 2834345 = 2125759) B2125759
theorem B1558601 : Blo 307833 1558601 := bstep (se 2 (by rfl) ⟨584475, by rfl⟩ : syracuseStep 1558601 = 1168951) B1168951
theorem B1493585 : Blo 307833 1493585 := bstep (se 2 (by rfl) ⟨560094, by rfl⟩ : syracuseStep 1493585 = 1120189) B1120189
theorem B3789251 : Blo 307833 3789251 := bstep (se 1 (by rfl) ⟨2841938, by rfl⟩ : syracuseStep 3789251 = 5683877) B5683877
theorem B348655 : Blo 307833 348655 := bstep (se 1 (by rfl) ⟨261491, by rfl⟩ : syracuseStep 348655 = 522983) B522983
theorem B1562489 : Blo 307833 1562489 := bstep (se 2 (by rfl) ⟨585933, by rfl⟩ : syracuseStep 1562489 = 1171867) B1171867
theorem B1562813 : Blo 307833 1562813 := bstep (se 3 (by rfl) ⟨293027, by rfl⟩ : syracuseStep 1562813 = 586055) B586055
theorem B20470283 : Blo 307833 20470283 := bstep (se 1 (by rfl) ⟨15352712, by rfl⟩ : syracuseStep 20470283 = 30705425) B30705425
theorem B2808361 : Blo 307833 2808361 := bstep (se 2 (by rfl) ⟨1053135, by rfl⟩ : syracuseStep 2808361 = 2106271) B2106271
theorem B2809529 : Blo 307833 2809529 := bstep (se 2 (by rfl) ⟨1053573, by rfl⟩ : syracuseStep 2809529 = 2107147) B2107147
theorem B319847 : Blo 307833 319847 := bstep (se 1 (by rfl) ⟨239885, by rfl⟩ : syracuseStep 319847 = 479771) B479771
theorem B1042145 : Blo 307833 1042145 := bstep (se 2 (by rfl) ⟨390804, by rfl⟩ : syracuseStep 1042145 = 781609) B781609
theorem B1763815 : Blo 307833 1763815 := bstep (se 1 (by rfl) ⟨1322861, by rfl⟩ : syracuseStep 1763815 = 2645723) B2645723
theorem B2649347 : Blo 307833 2649347 := bstep (se 1 (by rfl) ⟨1987010, by rfl⟩ : syracuseStep 2649347 = 3974021) B3974021
theorem B519527 : Blo 307833 519527 := bstep (se 1 (by rfl) ⟨389645, by rfl⟩ : syracuseStep 519527 = 779291) B779291
theorem B1110199 : Blo 307833 1110199 := bstep (se 1 (by rfl) ⟨832649, by rfl⟩ : syracuseStep 1110199 = 1665299) B1665299
theorem B1177213 : Blo 307833 1177213 := bstep (se 3 (by rfl) ⟨220727, by rfl⟩ : syracuseStep 1177213 = 441455) B441455
theorem B2029331 : Blo 307833 2029331 := bstep (se 1 (by rfl) ⟨1521998, by rfl⟩ : syracuseStep 2029331 = 3043997) B3043997
theorem B1570751 : Blo 307833 1570751 := bstep (se 1 (by rfl) ⟨1178063, by rfl⟩ : syracuseStep 1570751 = 2356127) B2356127
theorem B2359529 : Blo 307833 2359529 := bstep (se 2 (by rfl) ⟨884823, by rfl⟩ : syracuseStep 2359529 = 1769647) B1769647
theorem B1573343 : Blo 307833 1573343 := bstep (se 1 (by rfl) ⟨1180007, by rfl⟩ : syracuseStep 1573343 = 2360015) B2360015
theorem B852925 : Blo 307833 852925 := bstep (se 3 (by rfl) ⟨159923, by rfl⟩ : syracuseStep 852925 = 319847) B319847
theorem B1049759 : Blo 307833 1049759 := bstep (se 1 (by rfl) ⟨787319, by rfl⟩ : syracuseStep 1049759 = 1574639) B1574639
theorem B1771631 : Blo 307833 1771631 := bstep (se 1 (by rfl) ⟨1328723, by rfl⟩ : syracuseStep 1771631 = 2657447) B2657447
theorem B1575287 : Blo 307833 1575287 := bstep (se 1 (by rfl) ⟨1181465, by rfl⟩ : syracuseStep 1575287 = 2362931) B2362931
theorem B2230831 : Blo 307833 2230831 := bstep (se 1 (by rfl) ⟨1673123, by rfl⟩ : syracuseStep 2230831 = 3346247) B3346247
theorem B25561655 : Blo 307833 25561655 := bstep (se 1 (by rfl) ⟨19171241, by rfl⟩ : syracuseStep 25561655 = 38342483) B38342483
theorem B2526167 : Blo 307833 2526167 := bstep (se 1 (by rfl) ⟨1894625, by rfl⟩ : syracuseStep 2526167 = 3789251) B3789251
theorem B5411549 : Blo 307833 5411549 := bstep (se 3 (by rfl) ⟨1014665, by rfl⟩ : syracuseStep 5411549 = 2029331) B2029331
theorem B463739 : Blo 307833 463739 := bstep (se 1 (by rfl) ⟨347804, by rfl⟩ : syracuseStep 463739 = 695609) B695609
theorem B1873019 : Blo 307833 1873019 := bstep (se 1 (by rfl) ⟨1404764, by rfl⟩ : syracuseStep 1873019 = 2809529) B2809529
theorem B464255 : Blo 307833 464255 := bstep (se 1 (by rfl) ⟨348191, by rfl⟩ : syracuseStep 464255 = 696383) B696383
theorem B1480265 : Blo 307833 1480265 := bstep (se 2 (by rfl) ⟨555099, by rfl⟩ : syracuseStep 1480265 = 1110199) B1110199
theorem B464873 : Blo 307833 464873 := bstep (se 2 (by rfl) ⟨174327, by rfl⟩ : syracuseStep 464873 = 348655) B348655
theorem B464987 : Blo 307833 464987 := bstep (se 1 (by rfl) ⟨348740, by rfl⟩ : syracuseStep 464987 = 697481) B697481
theorem B1317053 : Blo 307833 1317053 := bstep (se 3 (by rfl) ⟨246947, by rfl⟩ : syracuseStep 1317053 = 493895) B493895
theorem B694763 : Blo 307833 694763 := bstep (se 1 (by rfl) ⟨521072, by rfl⟩ : syracuseStep 694763 = 1042145) B1042145
theorem B467111 : Blo 307833 467111 := bstep (se 1 (by rfl) ⟨350333, by rfl⟩ : syracuseStep 467111 = 700667) B700667
theorem B3744481 : Blo 307833 3744481 := bstep (se 2 (by rfl) ⟨1404180, by rfl⟩ : syracuseStep 3744481 = 2808361) B2808361
theorem B1879247 : Blo 307833 1879247 := bstep (se 1 (by rfl) ⟨1409435, by rfl⟩ : syracuseStep 1879247 = 2818871) B2818871
theorem B995723 : Blo 307833 995723 := bstep (se 1 (by rfl) ⟨746792, by rfl⟩ : syracuseStep 995723 = 1493585) B1493585
theorem B307951 : Blo 307833 307951 := bstep (se 1 (by rfl) ⟨230963, by rfl⟩ : syracuseStep 307951 = 461927) B461927
theorem B308383 : Blo 307833 308383 := bstep (se 1 (by rfl) ⟨231287, by rfl⟩ : syracuseStep 308383 = 462575) B462575
theorem B439519 : Blo 307833 439519 := bstep (se 1 (by rfl) ⟨329639, by rfl⟩ : syracuseStep 439519 = 659279) B659279
theorem B2635577 : Blo 307833 2635577 := bstep (se 2 (by rfl) ⟨988341, by rfl⟩ : syracuseStep 2635577 = 1976683) B1976683
theorem B309407 : Blo 307833 309407 := bstep (se 1 (by rfl) ⟨232055, by rfl⟩ : syracuseStep 309407 = 464111) B464111
theorem B13646855 : Blo 307833 13646855 := bstep (se 1 (by rfl) ⟨10235141, by rfl⟩ : syracuseStep 13646855 = 20470283) B20470283
theorem B310911 : Blo 307833 310911 := bstep (se 1 (by rfl) ⟨233183, by rfl⟩ : syracuseStep 310911 = 466367) B466367
theorem B311579 : Blo 307833 311579 := bstep (se 1 (by rfl) ⟨233684, by rfl⟩ : syracuseStep 311579 = 467369) B467369
theorem B2016359 : Blo 307833 2016359 := bstep (se 1 (by rfl) ⟨1512269, by rfl⟩ : syracuseStep 2016359 = 3024539) B3024539
theorem B1754567 : Blo 307833 1754567 := bstep (se 1 (by rfl) ⟨1315925, by rfl⟩ : syracuseStep 1754567 = 2631851) B2631851
theorem B837211 : Blo 307833 837211 := bstep (se 1 (by rfl) ⟨627908, by rfl⟩ : syracuseStep 837211 = 1255817) B1255817
theorem B346351 : Blo 307833 346351 := bstep (se 1 (by rfl) ⟨259763, by rfl⟩ : syracuseStep 346351 = 519527) B519527
theorem B1756799 : Blo 307833 1756799 := bstep (se 1 (by rfl) ⟨1317599, by rfl⟩ : syracuseStep 1756799 = 2635199) B2635199
theorem B1757983 : Blo 307833 1757983 := bstep (se 1 (by rfl) ⟨1318487, by rfl⟩ : syracuseStep 1757983 = 2636975) B2636975
theorem B1889563 : Blo 307833 1889563 := bstep (se 1 (by rfl) ⟨1417172, by rfl⟩ : syracuseStep 1889563 = 2834345) B2834345
theorem B1759441 : Blo 307833 1759441 := bstep (se 2 (by rfl) ⟨659790, by rfl⟩ : syracuseStep 1759441 = 1319581) B1319581
theorem B1039067 : Blo 307833 1039067 := bstep (se 1 (by rfl) ⟨779300, by rfl⟩ : syracuseStep 1039067 = 1558601) B1558601
theorem B2351753 : Blo 307833 2351753 := bstep (se 2 (by rfl) ⟨881907, by rfl⟩ : syracuseStep 2351753 = 1763815) B1763815
theorem B3367615 : Blo 307833 3367615 := bstep (se 1 (by rfl) ⟨2525711, by rfl⟩ : syracuseStep 3367615 = 5051423) B5051423
theorem B1041659 : Blo 307833 1041659 := bstep (se 1 (by rfl) ⟨781244, by rfl⟩ : syracuseStep 1041659 = 1562489) B1562489
theorem B1041875 : Blo 307833 1041875 := bstep (se 1 (by rfl) ⟨781406, by rfl⟩ : syracuseStep 1041875 = 1562813) B1562813
theorem B3532733 : Blo 307833 3532733 := bstep (se 3 (by rfl) ⟨662387, by rfl⟩ : syracuseStep 3532733 = 1324775) B1324775
theorem B1569617 : Blo 307833 1569617 := bstep (se 2 (by rfl) ⟨588606, by rfl⟩ : syracuseStep 1569617 = 1177213) B1177213
theorem B1766231 : Blo 307833 1766231 := bstep (se 1 (by rfl) ⟨1324673, by rfl⟩ : syracuseStep 1766231 = 2649347) B2649347
theorem B1111321 : Blo 307833 1111321 := bstep (se 2 (by rfl) ⟨416745, by rfl⟩ : syracuseStep 1111321 = 833491) B833491
theorem B2127131 : Blo 307833 2127131 := bstep (se 1 (by rfl) ⟨1595348, by rfl⟩ : syracuseStep 2127131 = 3190697) B3190697
theorem B1047167 : Blo 307833 1047167 := bstep (se 1 (by rfl) ⟨785375, by rfl⟩ : syracuseStep 1047167 = 1570751) B1570751
theorem B1573019 : Blo 307833 1573019 := bstep (se 1 (by rfl) ⟨1179764, by rfl⟩ : syracuseStep 1573019 = 2359529) B2359529
theorem B1048895 : Blo 307833 1048895 := bstep (se 1 (by rfl) ⟨786671, by rfl⟩ : syracuseStep 1048895 = 1573343) B1573343
theorem B1344239 : Blo 307833 1344239 := bstep (se 1 (by rfl) ⟨1008179, by rfl⟩ : syracuseStep 1344239 = 2016359) B2016359
theorem B4490153 : Blo 307833 4490153 := bstep (se 2 (by rfl) ⟨1683807, by rfl⟩ : syracuseStep 4490153 = 3367615) B3367615
theorem B1181087 : Blo 307833 1181087 := bstep (se 1 (by rfl) ⟨885815, by rfl⟩ : syracuseStep 1181087 = 1771631) B1771631
theorem B1050191 : Blo 307833 1050191 := bstep (se 1 (by rfl) ⟨787643, by rfl⟩ : syracuseStep 1050191 = 1575287) B1575287
theorem B17041103 : Blo 307833 17041103 := bstep (se 1 (by rfl) ⟨12780827, by rfl⟩ : syracuseStep 17041103 = 25561655) B25561655
theorem B1116281 : Blo 307833 1116281 := bstep (se 2 (by rfl) ⟨418605, by rfl⟩ : syracuseStep 1116281 = 837211) B837211
theorem B461801 : Blo 307833 461801 := bstep (se 2 (by rfl) ⟨173175, by rfl⟩ : syracuseStep 461801 = 346351) B346351
theorem B1248679 : Blo 307833 1248679 := bstep (se 1 (by rfl) ⟨936509, by rfl⟩ : syracuseStep 1248679 = 1873019) B1873019
theorem B986843 : Blo 307833 986843 := bstep (se 1 (by rfl) ⟨740132, by rfl⟩ : syracuseStep 986843 = 1480265) B1480265
theorem B463175 : Blo 307833 463175 := bstep (se 1 (by rfl) ⟨347381, by rfl⟩ : syracuseStep 463175 = 694763) B694763
theorem B692711 : Blo 307833 692711 := bstep (se 1 (by rfl) ⟨519533, by rfl⟩ : syracuseStep 692711 = 1039067) B1039067
theorem B694439 : Blo 307833 694439 := bstep (se 1 (by rfl) ⟨520829, by rfl⟩ : syracuseStep 694439 = 1041659) B1041659
theorem B694583 : Blo 307833 694583 := bstep (se 1 (by rfl) ⟨520937, by rfl⟩ : syracuseStep 694583 = 1041875) B1041875
theorem B1481761 : Blo 307833 1481761 := bstep (se 2 (by rfl) ⟨555660, by rfl⟩ : syracuseStep 1481761 = 1111321) B1111321
theorem B1252831 : Blo 307833 1252831 := bstep (se 1 (by rfl) ⟨939623, by rfl⟩ : syracuseStep 1252831 = 1879247) B1879247
theorem B663815 : Blo 307833 663815 := bstep (se 1 (by rfl) ⟨497861, by rfl⟩ : syracuseStep 663815 = 995723) B995723
theorem B1418087 : Blo 307833 1418087 := bstep (se 1 (by rfl) ⟨1063565, by rfl⟩ : syracuseStep 1418087 = 2127131) B2127131
theorem B698111 : Blo 307833 698111 := bstep (se 1 (by rfl) ⟨523583, by rfl⟩ : syracuseStep 698111 = 1047167) B1047167
theorem B699839 : Blo 307833 699839 := bstep (se 1 (by rfl) ⟨524879, by rfl⟩ : syracuseStep 699839 = 1049759) B1049759
theorem B4992641 : Blo 307833 4992641 := bstep (se 2 (by rfl) ⟨1872240, by rfl⟩ : syracuseStep 4992641 = 3744481) B3744481
theorem B14430797 : Blo 307833 14430797 := bstep (se 3 (by rfl) ⟨2705774, by rfl⟩ : syracuseStep 14430797 = 5411549) B5411549
theorem B1684111 : Blo 307833 1684111 := bstep (se 1 (by rfl) ⟨1263083, by rfl⟩ : syracuseStep 1684111 = 2526167) B2526167
theorem B309159 : Blo 307833 309159 := bstep (se 1 (by rfl) ⟨231869, by rfl⟩ : syracuseStep 309159 = 463739) B463739
theorem B309503 : Blo 307833 309503 := bstep (se 1 (by rfl) ⟨232127, by rfl⟩ : syracuseStep 309503 = 464255) B464255
theorem B309915 : Blo 307833 309915 := bstep (se 1 (by rfl) ⟨232436, by rfl⟩ : syracuseStep 309915 = 464873) B464873
theorem B309991 : Blo 307833 309991 := bstep (se 1 (by rfl) ⟨232493, by rfl⟩ : syracuseStep 309991 = 464987) B464987
theorem B311407 : Blo 307833 311407 := bstep (se 1 (by rfl) ⟨233555, by rfl⟩ : syracuseStep 311407 = 467111) B467111
theorem B2343977 : Blo 307833 2343977 := bstep (se 2 (by rfl) ⟨878991, by rfl⟩ : syracuseStep 2343977 = 1757983) B1757983
theorem B2345921 : Blo 307833 2345921 := bstep (se 2 (by rfl) ⟨879720, by rfl⟩ : syracuseStep 2345921 = 1759441) B1759441
theorem B1757051 : Blo 307833 1757051 := bstep (se 1 (by rfl) ⟨1317788, by rfl⟩ : syracuseStep 1757051 = 2635577) B2635577
theorem B9097903 : Blo 307833 9097903 := bstep (se 1 (by rfl) ⟨6823427, by rfl⟩ : syracuseStep 9097903 = 13646855) B13646855
theorem B1169711 : Blo 307833 1169711 := bstep (se 1 (by rfl) ⟨877283, by rfl⟩ : syracuseStep 1169711 = 1754567) B1754567
theorem B1137233 : Blo 307833 1137233 := bstep (se 2 (by rfl) ⟨426462, by rfl⟩ : syracuseStep 1137233 = 852925) B852925
theorem B1171199 : Blo 307833 1171199 := bstep (se 1 (by rfl) ⟨878399, by rfl⟩ : syracuseStep 1171199 = 1756799) B1756799
theorem B2974441 : Blo 307833 2974441 := bstep (se 2 (by rfl) ⟨1115415, by rfl⟩ : syracuseStep 2974441 = 2230831) B2230831
theorem B878035 : Blo 307833 878035 := bstep (se 1 (by rfl) ⟨658526, by rfl⟩ : syracuseStep 878035 = 1317053) B1317053
theorem B1567835 : Blo 307833 1567835 := bstep (se 1 (by rfl) ⟨1175876, by rfl⟩ : syracuseStep 1567835 = 2351753) B2351753
theorem B2355155 : Blo 307833 2355155 := bstep (se 1 (by rfl) ⟨1766366, by rfl⟩ : syracuseStep 2355155 = 3532733) B3532733
theorem B586025 : Blo 307833 586025 := bstep (se 2 (by rfl) ⟨219759, by rfl⟩ : syracuseStep 586025 = 439519) B439519
theorem B2519417 : Blo 307833 2519417 := bstep (se 2 (by rfl) ⟨944781, by rfl⟩ : syracuseStep 2519417 = 1889563) B1889563
theorem B1046411 : Blo 307833 1046411 := bstep (se 1 (by rfl) ⟨784808, by rfl⟩ : syracuseStep 1046411 = 1569617) B1569617
theorem B1177487 : Blo 307833 1177487 := bstep (se 1 (by rfl) ⟨883115, by rfl⟩ : syracuseStep 1177487 = 1766231) B1766231
theorem B1048679 : Blo 307833 1048679 := bstep (se 1 (by rfl) ⟨786509, by rfl⟩ : syracuseStep 1048679 = 1573019) B1573019
theorem B1770173 : Blo 307833 1770173 := bstep (se 3 (by rfl) ⟨331907, by rfl⟩ : syracuseStep 1770173 = 663815) B663815
theorem B787391 : Blo 307833 787391 := bstep (se 1 (by rfl) ⟨590543, by rfl⟩ : syracuseStep 787391 = 1181087) B1181087
theorem B3965921 : Blo 307833 3965921 := bstep (se 2 (by rfl) ⟨1487220, by rfl⟩ : syracuseStep 3965921 = 2974441) B2974441
theorem B657895 : Blo 307833 657895 := bstep (se 1 (by rfl) ⟨493421, by rfl⟩ : syracuseStep 657895 = 986843) B986843
theorem B461807 : Blo 307833 461807 := bstep (se 1 (by rfl) ⟨346355, by rfl⟩ : syracuseStep 461807 = 692711) B692711
theorem B462959 : Blo 307833 462959 := bstep (se 1 (by rfl) ⟨347219, by rfl⟩ : syracuseStep 462959 = 694439) B694439
theorem B463055 : Blo 307833 463055 := bstep (se 1 (by rfl) ⟨347291, by rfl⟩ : syracuseStep 463055 = 694583) B694583
theorem B758155 : Blo 307833 758155 := bstep (se 1 (by rfl) ⟨568616, by rfl⟩ : syracuseStep 758155 = 1137233) B1137233
theorem B465407 : Blo 307833 465407 := bstep (se 1 (by rfl) ⟨349055, by rfl⟩ : syracuseStep 465407 = 698111) B698111
theorem B6659621 : Blo 307833 6659621 := bstep (se 4 (by rfl) ⟨624339, by rfl⟩ : syracuseStep 6659621 = 1248679) B1248679
theorem B466559 : Blo 307833 466559 := bstep (se 1 (by rfl) ⟨349919, by rfl⟩ : syracuseStep 466559 = 699839) B699839
theorem B1679611 : Blo 307833 1679611 := bstep (se 1 (by rfl) ⟨1259708, by rfl⟩ : syracuseStep 1679611 = 2519417) B2519417
theorem B697607 : Blo 307833 697607 := bstep (se 1 (by rfl) ⟨523205, by rfl⟩ : syracuseStep 697607 = 1046411) B1046411
theorem B1975681 : Blo 307833 1975681 := bstep (se 2 (by rfl) ⟨740880, by rfl⟩ : syracuseStep 1975681 = 1481761) B1481761
theorem B699263 : Blo 307833 699263 := bstep (se 1 (by rfl) ⟨524447, by rfl⟩ : syracuseStep 699263 = 1048895) B1048895
theorem B896159 : Blo 307833 896159 := bstep (se 1 (by rfl) ⟨672119, by rfl⟩ : syracuseStep 896159 = 1344239) B1344239
theorem B2993435 : Blo 307833 2993435 := bstep (se 1 (by rfl) ⟨2245076, by rfl⟩ : syracuseStep 2993435 = 4490153) B4490153
theorem B700127 : Blo 307833 700127 := bstep (se 1 (by rfl) ⟨525095, by rfl⟩ : syracuseStep 700127 = 1050191) B1050191
theorem B307867 : Blo 307833 307867 := bstep (se 1 (by rfl) ⟨230900, by rfl⟩ : syracuseStep 307867 = 461801) B461801
theorem B3781565 : Blo 307833 3781565 := bstep (se 3 (by rfl) ⟨709043, by rfl⟩ : syracuseStep 3781565 = 1418087) B1418087
theorem B308783 : Blo 307833 308783 := bstep (se 1 (by rfl) ⟨231587, by rfl⟩ : syracuseStep 308783 = 463175) B463175
theorem B2245481 : Blo 307833 2245481 := bstep (se 2 (by rfl) ⟨842055, by rfl⟩ : syracuseStep 2245481 = 1684111) B1684111
theorem B3328427 : Blo 307833 3328427 := bstep (se 1 (by rfl) ⟨2496320, by rfl⟩ : syracuseStep 3328427 = 4992641) B4992641
theorem B9620531 : Blo 307833 9620531 := bstep (se 1 (by rfl) ⟨7215398, by rfl⟩ : syracuseStep 9620531 = 14430797) B14430797
theorem B1562651 : Blo 307833 1562651 := bstep (se 1 (by rfl) ⟨1171988, by rfl⟩ : syracuseStep 1562651 = 2343977) B2343977
theorem B11360735 : Blo 307833 11360735 := bstep (se 1 (by rfl) ⟨8520551, by rfl⟩ : syracuseStep 11360735 = 17041103) B17041103
theorem B1170713 : Blo 307833 1170713 := bstep (se 2 (by rfl) ⟨439017, by rfl⟩ : syracuseStep 1170713 = 878035) B878035
theorem B1563947 : Blo 307833 1563947 := bstep (se 1 (by rfl) ⟨1172960, by rfl⟩ : syracuseStep 1563947 = 2345921) B2345921
theorem B1171367 : Blo 307833 1171367 := bstep (se 1 (by rfl) ⟨878525, by rfl⟩ : syracuseStep 1171367 = 1757051) B1757051
theorem B48522149 : Blo 307833 48522149 := bstep (se 4 (by rfl) ⟨4548951, by rfl⟩ : syracuseStep 48522149 = 9097903) B9097903
theorem B779807 : Blo 307833 779807 := bstep (se 1 (by rfl) ⟨584855, by rfl⟩ : syracuseStep 779807 = 1169711) B1169711
theorem B780799 : Blo 307833 780799 := bstep (se 1 (by rfl) ⟨585599, by rfl⟩ : syracuseStep 780799 = 1171199) B1171199
theorem B2976749 : Blo 307833 2976749 := bstep (se 3 (by rfl) ⟨558140, by rfl⟩ : syracuseStep 2976749 = 1116281) B1116281
theorem B1045223 : Blo 307833 1045223 := bstep (se 1 (by rfl) ⟨783917, by rfl⟩ : syracuseStep 1045223 = 1567835) B1567835
theorem B1570103 : Blo 307833 1570103 := bstep (se 1 (by rfl) ⟨1177577, by rfl⟩ : syracuseStep 1570103 = 2355155) B2355155
theorem B390683 : Blo 307833 390683 := bstep (se 1 (by rfl) ⟨293012, by rfl⟩ : syracuseStep 390683 = 586025) B586025
theorem B784991 : Blo 307833 784991 := bstep (se 1 (by rfl) ⟨588743, by rfl⟩ : syracuseStep 784991 = 1177487) B1177487
theorem B1670441 : Blo 307833 1670441 := bstep (se 2 (by rfl) ⟨626415, by rfl⟩ : syracuseStep 1670441 = 1252831) B1252831
theorem B1180115 : Blo 307833 1180115 := bstep (se 1 (by rfl) ⟨885086, by rfl⟩ : syracuseStep 1180115 = 1770173) B1770173
theorem B524927 : Blo 307833 524927 := bstep (se 1 (by rfl) ⟨393695, by rfl⟩ : syracuseStep 524927 = 787391) B787391
theorem B7573823 : Blo 307833 7573823 := bstep (se 1 (by rfl) ⟨5680367, by rfl⟩ : syracuseStep 7573823 = 11360735) B11360735
theorem B32348099 : Blo 307833 32348099 := bstep (se 1 (by rfl) ⟨24261074, by rfl⟩ : syracuseStep 32348099 = 48522149) B48522149
theorem B465071 : Blo 307833 465071 := bstep (se 1 (by rfl) ⟨348803, by rfl⟩ : syracuseStep 465071 = 697607) B697607
theorem B466175 : Blo 307833 466175 := bstep (se 1 (by rfl) ⟨349631, by rfl⟩ : syracuseStep 466175 = 699263) B699263
theorem B597439 : Blo 307833 597439 := bstep (se 1 (by rfl) ⟨448079, by rfl⟩ : syracuseStep 597439 = 896159) B896159
theorem B466751 : Blo 307833 466751 := bstep (se 1 (by rfl) ⟨350063, by rfl⟩ : syracuseStep 466751 = 700127) B700127
theorem B696815 : Blo 307833 696815 := bstep (se 1 (by rfl) ⟨522611, by rfl⟩ : syracuseStep 696815 = 1045223) B1045223
theorem B699119 : Blo 307833 699119 := bstep (se 1 (by rfl) ⟨524339, by rfl⟩ : syracuseStep 699119 = 1048679) B1048679
theorem B2239481 : Blo 307833 2239481 := bstep (se 2 (by rfl) ⟨839805, by rfl⟩ : syracuseStep 2239481 = 1679611) B1679611
theorem B2634241 : Blo 307833 2634241 := bstep (se 2 (by rfl) ⟨987840, by rfl⟩ : syracuseStep 2634241 = 1975681) B1975681
theorem B307871 : Blo 307833 307871 := bstep (se 1 (by rfl) ⟨230903, by rfl⟩ : syracuseStep 307871 = 461807) B461807
theorem B308639 : Blo 307833 308639 := bstep (se 1 (by rfl) ⟨231479, by rfl⟩ : syracuseStep 308639 = 462959) B462959
theorem B308703 : Blo 307833 308703 := bstep (se 1 (by rfl) ⟨231527, by rfl⟩ : syracuseStep 308703 = 463055) B463055
theorem B310271 : Blo 307833 310271 := bstep (se 1 (by rfl) ⟨232703, by rfl⟩ : syracuseStep 310271 = 465407) B465407
theorem B4439747 : Blo 307833 4439747 := bstep (se 1 (by rfl) ⟨3329810, by rfl⟩ : syracuseStep 4439747 = 6659621) B6659621
theorem B311039 : Blo 307833 311039 := bstep (se 1 (by rfl) ⟨233279, by rfl⟩ : syracuseStep 311039 = 466559) B466559
theorem B1984499 : Blo 307833 1984499 := bstep (se 1 (by rfl) ⟨1488374, by rfl⟩ : syracuseStep 1984499 = 2976749) B2976749
theorem B1496987 : Blo 307833 1496987 := bstep (se 1 (by rfl) ⟨1122740, by rfl⟩ : syracuseStep 1496987 = 2245481) B2245481
theorem B2643947 : Blo 307833 2643947 := bstep (se 1 (by rfl) ⟨1982960, by rfl⟩ : syracuseStep 2643947 = 3965921) B3965921
theorem B2218951 : Blo 307833 2218951 := bstep (se 1 (by rfl) ⟨1664213, by rfl⟩ : syracuseStep 2218951 = 3328427) B3328427
theorem B6413687 : Blo 307833 6413687 := bstep (se 1 (by rfl) ⟨4810265, by rfl⟩ : syracuseStep 6413687 = 9620531) B9620531
theorem B877193 : Blo 307833 877193 := bstep (se 2 (by rfl) ⟨328947, by rfl⟩ : syracuseStep 877193 = 657895) B657895
theorem B1041065 : Blo 307833 1041065 := bstep (se 2 (by rfl) ⟨390399, by rfl⟩ : syracuseStep 1041065 = 780799) B780799
theorem B1041767 : Blo 307833 1041767 := bstep (se 1 (by rfl) ⟨781325, by rfl⟩ : syracuseStep 1041767 = 1562651) B1562651
theorem B1041821 : Blo 307833 1041821 := bstep (se 3 (by rfl) ⟨195341, by rfl⟩ : syracuseStep 1041821 = 390683) B390683
theorem B780475 : Blo 307833 780475 := bstep (se 1 (by rfl) ⟨585356, by rfl⟩ : syracuseStep 780475 = 1170713) B1170713
theorem B1042631 : Blo 307833 1042631 := bstep (se 1 (by rfl) ⟨781973, by rfl⟩ : syracuseStep 1042631 = 1563947) B1563947
theorem B780911 : Blo 307833 780911 := bstep (se 1 (by rfl) ⟨585683, by rfl⟩ : syracuseStep 780911 = 1171367) B1171367
theorem B1010873 : Blo 307833 1010873 := bstep (se 2 (by rfl) ⟨379077, by rfl⟩ : syracuseStep 1010873 = 758155) B758155
theorem B519871 : Blo 307833 519871 := bstep (se 1 (by rfl) ⟨389903, by rfl⟩ : syracuseStep 519871 = 779807) B779807
theorem B1995623 : Blo 307833 1995623 := bstep (se 1 (by rfl) ⟨1496717, by rfl⟩ : syracuseStep 1995623 = 2993435) B2993435
theorem B2521043 : Blo 307833 2521043 := bstep (se 1 (by rfl) ⟨1890782, by rfl⟩ : syracuseStep 2521043 = 3781565) B3781565
theorem B4454509 : Blo 307833 4454509 := bstep (se 3 (by rfl) ⟨835220, by rfl⟩ : syracuseStep 4454509 = 1670441) B1670441
theorem B1046735 : Blo 307833 1046735 := bstep (se 1 (by rfl) ⟨785051, by rfl⟩ : syracuseStep 1046735 = 1570103) B1570103
theorem B523327 : Blo 307833 523327 := bstep (se 1 (by rfl) ⟨392495, by rfl⟩ : syracuseStep 523327 = 784991) B784991
theorem B786743 : Blo 307833 786743 := bstep (se 1 (by rfl) ⟨590057, by rfl⟩ : syracuseStep 786743 = 1180115) B1180115
theorem B5049215 : Blo 307833 5049215 := bstep (se 1 (by rfl) ⟨3786911, by rfl⟩ : syracuseStep 5049215 = 7573823) B7573823
theorem B693161 : Blo 307833 693161 := bstep (se 2 (by rfl) ⟨259935, by rfl⟩ : syracuseStep 693161 = 519871) B519871
theorem B464543 : Blo 307833 464543 := bstep (se 1 (by rfl) ⟨348407, by rfl⟩ : syracuseStep 464543 = 696815) B696815
theorem B694043 : Blo 307833 694043 := bstep (se 1 (by rfl) ⟨520532, by rfl⟩ : syracuseStep 694043 = 1041065) B1041065
theorem B3512321 : Blo 307833 3512321 := bstep (se 2 (by rfl) ⟨1317120, by rfl⟩ : syracuseStep 3512321 = 2634241) B2634241
theorem B694511 : Blo 307833 694511 := bstep (se 1 (by rfl) ⟨520883, by rfl⟩ : syracuseStep 694511 = 1041767) B1041767
theorem B694547 : Blo 307833 694547 := bstep (se 1 (by rfl) ⟨520910, by rfl⟩ : syracuseStep 694547 = 1041821) B1041821
theorem B695087 : Blo 307833 695087 := bstep (se 1 (by rfl) ⟨521315, by rfl⟩ : syracuseStep 695087 = 1042631) B1042631
theorem B466079 : Blo 307833 466079 := bstep (se 1 (by rfl) ⟨349559, by rfl⟩ : syracuseStep 466079 = 699119) B699119
theorem B3186341 : Blo 307833 3186341 := bstep (se 4 (by rfl) ⟨298719, by rfl⟩ : syracuseStep 3186341 = 597439) B597439
theorem B5939345 : Blo 307833 5939345 := bstep (se 2 (by rfl) ⟨2227254, by rfl⟩ : syracuseStep 5939345 = 4454509) B4454509
theorem B2958601 : Blo 307833 2958601 := bstep (se 2 (by rfl) ⟨1109475, by rfl⟩ : syracuseStep 2958601 = 2218951) B2218951
theorem B1680695 : Blo 307833 1680695 := bstep (se 1 (by rfl) ⟨1260521, by rfl⟩ : syracuseStep 1680695 = 2521043) B2521043
theorem B697769 : Blo 307833 697769 := bstep (se 2 (by rfl) ⟨261663, by rfl⟩ : syracuseStep 697769 = 523327) B523327
theorem B697823 : Blo 307833 697823 := bstep (se 1 (by rfl) ⟨523367, by rfl⟩ : syracuseStep 697823 = 1046735) B1046735
theorem B2959831 : Blo 307833 2959831 := bstep (se 1 (by rfl) ⟨2219873, by rfl⟩ : syracuseStep 2959831 = 4439747) B4439747
theorem B1322999 : Blo 307833 1322999 := bstep (se 1 (by rfl) ⟨992249, by rfl⟩ : syracuseStep 1322999 = 1984499) B1984499
theorem B997991 : Blo 307833 997991 := bstep (se 1 (by rfl) ⟨748493, by rfl⟩ : syracuseStep 997991 = 1496987) B1496987
theorem B310047 : Blo 307833 310047 := bstep (se 1 (by rfl) ⟨232535, by rfl⟩ : syracuseStep 310047 = 465071) B465071
theorem B310783 : Blo 307833 310783 := bstep (se 1 (by rfl) ⟨233087, by rfl⟩ : syracuseStep 310783 = 466175) B466175
theorem B4275791 : Blo 307833 4275791 := bstep (se 1 (by rfl) ⟨3206843, by rfl⟩ : syracuseStep 4275791 = 6413687) B6413687
theorem B86261597 : Blo 307833 86261597 := bstep (se 3 (by rfl) ⟨16174049, by rfl⟩ : syracuseStep 86261597 = 32348099) B32348099
theorem B311167 : Blo 307833 311167 := bstep (se 1 (by rfl) ⟨233375, by rfl⟩ : syracuseStep 311167 = 466751) B466751
theorem B1492987 : Blo 307833 1492987 := bstep (se 1 (by rfl) ⟨1119740, by rfl⟩ : syracuseStep 1492987 = 2239481) B2239481
theorem B673915 : Blo 307833 673915 := bstep (se 1 (by rfl) ⟨505436, by rfl⟩ : syracuseStep 673915 = 1010873) B1010873
theorem B1330415 : Blo 307833 1330415 := bstep (se 1 (by rfl) ⟨997811, by rfl⟩ : syracuseStep 1330415 = 1995623) B1995623
theorem B349951 : Blo 307833 349951 := bstep (se 1 (by rfl) ⟨262463, by rfl⟩ : syracuseStep 349951 = 524927) B524927
theorem B1040633 : Blo 307833 1040633 := bstep (se 2 (by rfl) ⟨390237, by rfl⟩ : syracuseStep 1040633 = 780475) B780475
theorem B1762631 : Blo 307833 1762631 := bstep (se 1 (by rfl) ⟨1321973, by rfl⟩ : syracuseStep 1762631 = 2643947) B2643947
theorem B584795 : Blo 307833 584795 := bstep (se 1 (by rfl) ⟨438596, by rfl⟩ : syracuseStep 584795 = 877193) B877193
theorem B520607 : Blo 307833 520607 := bstep (se 1 (by rfl) ⟨390455, by rfl⟩ : syracuseStep 520607 = 780911) B780911
theorem B524495 : Blo 307833 524495 := bstep (se 1 (by rfl) ⟨393371, by rfl⟩ : syracuseStep 524495 = 786743) B786743
theorem B886943 : Blo 307833 886943 := bstep (se 1 (by rfl) ⟨665207, by rfl⟩ : syracuseStep 886943 = 1330415) B1330415
theorem B462107 : Blo 307833 462107 := bstep (se 1 (by rfl) ⟨346580, by rfl⟩ : syracuseStep 462107 = 693161) B693161
theorem B462695 : Blo 307833 462695 := bstep (se 1 (by rfl) ⟨347021, by rfl⟩ : syracuseStep 462695 = 694043) B694043
theorem B463007 : Blo 307833 463007 := bstep (se 1 (by rfl) ⟨347255, by rfl⟩ : syracuseStep 463007 = 694511) B694511
theorem B463031 : Blo 307833 463031 := bstep (se 1 (by rfl) ⟨347273, by rfl⟩ : syracuseStep 463031 = 694547) B694547
theorem B463391 : Blo 307833 463391 := bstep (se 1 (by rfl) ⟨347543, by rfl⟩ : syracuseStep 463391 = 695087) B695087
theorem B693755 : Blo 307833 693755 := bstep (se 1 (by rfl) ⟨520316, by rfl⟩ : syracuseStep 693755 = 1040633) B1040633
theorem B1120463 : Blo 307833 1120463 := bstep (se 1 (by rfl) ⟨840347, by rfl⟩ : syracuseStep 1120463 = 1680695) B1680695
theorem B465179 : Blo 307833 465179 := bstep (se 1 (by rfl) ⟨348884, by rfl⟩ : syracuseStep 465179 = 697769) B697769
theorem B465215 : Blo 307833 465215 := bstep (se 1 (by rfl) ⟨348911, by rfl⟩ : syracuseStep 465215 = 697823) B697823
theorem B466601 : Blo 307833 466601 := bstep (se 2 (by rfl) ⟨174975, by rfl⟩ : syracuseStep 466601 = 349951) B349951
theorem B665327 : Blo 307833 665327 := bstep (se 1 (by rfl) ⟨498995, by rfl⟩ : syracuseStep 665327 = 997991) B997991
theorem B3944801 : Blo 307833 3944801 := bstep (se 2 (by rfl) ⟨1479300, by rfl⟩ : syracuseStep 3944801 = 2958601) B2958601
theorem B898553 : Blo 307833 898553 := bstep (se 2 (by rfl) ⟨336957, by rfl⟩ : syracuseStep 898553 = 673915) B673915
theorem B3946441 : Blo 307833 3946441 := bstep (se 2 (by rfl) ⟨1479915, by rfl⟩ : syracuseStep 3946441 = 2959831) B2959831
theorem B309695 : Blo 307833 309695 := bstep (se 1 (by rfl) ⟨232271, by rfl⟩ : syracuseStep 309695 = 464543) B464543
theorem B2341547 : Blo 307833 2341547 := bstep (se 1 (by rfl) ⟨1756160, by rfl⟩ : syracuseStep 2341547 = 3512321) B3512321
theorem B310719 : Blo 307833 310719 := bstep (se 1 (by rfl) ⟨233039, by rfl⟩ : syracuseStep 310719 = 466079) B466079
theorem B347071 : Blo 307833 347071 := bstep (se 1 (by rfl) ⟨260303, by rfl⟩ : syracuseStep 347071 = 520607) B520607
theorem B3366143 : Blo 307833 3366143 := bstep (se 1 (by rfl) ⟨2524607, by rfl⟩ : syracuseStep 3366143 = 5049215) B5049215
theorem B1990649 : Blo 307833 1990649 := bstep (se 2 (by rfl) ⟨746493, by rfl⟩ : syracuseStep 1990649 = 1492987) B1492987
theorem B2124227 : Blo 307833 2124227 := bstep (se 1 (by rfl) ⟨1593170, by rfl⟩ : syracuseStep 2124227 = 3186341) B3186341
theorem B3959563 : Blo 307833 3959563 := bstep (se 1 (by rfl) ⟨2969672, by rfl⟩ : syracuseStep 3959563 = 5939345) B5939345
theorem B1175087 : Blo 307833 1175087 := bstep (se 1 (by rfl) ⟨881315, by rfl⟩ : syracuseStep 1175087 = 1762631) B1762631
theorem B389863 : Blo 307833 389863 := bstep (se 1 (by rfl) ⟨292397, by rfl⟩ : syracuseStep 389863 = 584795) B584795
theorem B881999 : Blo 307833 881999 := bstep (se 1 (by rfl) ⟨661499, by rfl⟩ : syracuseStep 881999 = 1322999) B1322999
theorem B2850527 : Blo 307833 2850527 := bstep (se 1 (by rfl) ⟨2137895, by rfl⟩ : syracuseStep 2850527 = 4275791) B4275791
theorem B57507731 : Blo 307833 57507731 := bstep (se 1 (by rfl) ⟨43130798, by rfl⟩ : syracuseStep 57507731 = 86261597) B86261597
theorem B591295 : Blo 307833 591295 := bstep (se 1 (by rfl) ⟨443471, by rfl⟩ : syracuseStep 591295 = 886943) B886943
theorem B462503 : Blo 307833 462503 := bstep (se 1 (by rfl) ⟨346877, by rfl⟩ : syracuseStep 462503 = 693755) B693755
theorem B5279417 : Blo 307833 5279417 := bstep (se 2 (by rfl) ⟨1979781, by rfl⟩ : syracuseStep 5279417 = 3959563) B3959563
theorem B462761 : Blo 307833 462761 := bstep (se 2 (by rfl) ⟨173535, by rfl⟩ : syracuseStep 462761 = 347071) B347071
theorem B2396141 : Blo 307833 2396141 := bstep (se 3 (by rfl) ⟨449276, by rfl⟩ : syracuseStep 2396141 = 898553) B898553
theorem B1416151 : Blo 307833 1416151 := bstep (se 1 (by rfl) ⟨1062113, by rfl⟩ : syracuseStep 1416151 = 2124227) B2124227
theorem B2629867 : Blo 307833 2629867 := bstep (se 1 (by rfl) ⟨1972400, by rfl⟩ : syracuseStep 2629867 = 3944801) B3944801
theorem B308071 : Blo 307833 308071 := bstep (se 1 (by rfl) ⟨231053, by rfl⟩ : syracuseStep 308071 = 462107) B462107
theorem B308463 : Blo 307833 308463 := bstep (se 1 (by rfl) ⟨231347, by rfl⟩ : syracuseStep 308463 = 462695) B462695
theorem B308671 : Blo 307833 308671 := bstep (se 1 (by rfl) ⟨231503, by rfl⟩ : syracuseStep 308671 = 463007) B463007
theorem B308687 : Blo 307833 308687 := bstep (se 1 (by rfl) ⟨231515, by rfl⟩ : syracuseStep 308687 = 463031) B463031
theorem B308927 : Blo 307833 308927 := bstep (se 1 (by rfl) ⟨231695, by rfl⟩ : syracuseStep 308927 = 463391) B463391
theorem B310119 : Blo 307833 310119 := bstep (se 1 (by rfl) ⟨232589, by rfl⟩ : syracuseStep 310119 = 465179) B465179
theorem B310143 : Blo 307833 310143 := bstep (se 1 (by rfl) ⟨232607, by rfl⟩ : syracuseStep 310143 = 465215) B465215
theorem B2244095 : Blo 307833 2244095 := bstep (se 1 (by rfl) ⟨1683071, by rfl⟩ : syracuseStep 2244095 = 3366143) B3366143
theorem B311067 : Blo 307833 311067 := bstep (se 1 (by rfl) ⟨233300, by rfl⟩ : syracuseStep 311067 = 466601) B466601
theorem B1327099 : Blo 307833 1327099 := bstep (se 1 (by rfl) ⟨995324, by rfl⟩ : syracuseStep 1327099 = 1990649) B1990649
theorem B443551 : Blo 307833 443551 := bstep (se 1 (by rfl) ⟨332663, by rfl⟩ : syracuseStep 443551 = 665327) B665327
theorem B5261921 : Blo 307833 5261921 := bstep (se 2 (by rfl) ⟨1973220, by rfl⟩ : syracuseStep 5261921 = 3946441) B3946441
theorem B1561031 : Blo 307833 1561031 := bstep (se 1 (by rfl) ⟨1170773, by rfl⟩ : syracuseStep 1561031 = 2341547) B2341547
theorem B349663 : Blo 307833 349663 := bstep (se 1 (by rfl) ⟨262247, by rfl⟩ : syracuseStep 349663 = 524495) B524495
theorem B746975 : Blo 307833 746975 := bstep (se 1 (by rfl) ⟨560231, by rfl⟩ : syracuseStep 746975 = 1120463) B1120463
theorem B519817 : Blo 307833 519817 := bstep (se 2 (by rfl) ⟨194931, by rfl⟩ : syracuseStep 519817 = 389863) B389863
theorem B783391 : Blo 307833 783391 := bstep (se 1 (by rfl) ⟨587543, by rfl⟩ : syracuseStep 783391 = 1175087) B1175087
theorem B587999 : Blo 307833 587999 := bstep (se 1 (by rfl) ⟨440999, by rfl⟩ : syracuseStep 587999 = 881999) B881999
theorem B1900351 : Blo 307833 1900351 := bstep (se 1 (by rfl) ⟨1425263, by rfl⟩ : syracuseStep 1900351 = 2850527) B2850527
theorem B38338487 : Blo 307833 38338487 := bstep (se 1 (by rfl) ⟨28753865, by rfl⟩ : syracuseStep 38338487 = 57507731) B57507731
theorem B3506489 : Blo 307833 3506489 := bstep (se 2 (by rfl) ⟨1314933, by rfl⟩ : syracuseStep 3506489 = 2629867) B2629867
theorem B591401 : Blo 307833 591401 := bstep (se 2 (by rfl) ⟨221775, by rfl⟩ : syracuseStep 591401 = 443551) B443551
theorem B3507947 : Blo 307833 3507947 := bstep (se 1 (by rfl) ⟨2630960, by rfl⟩ : syracuseStep 3507947 = 5261921) B5261921
theorem B788393 : Blo 307833 788393 := bstep (se 2 (by rfl) ⟨295647, by rfl⟩ : syracuseStep 788393 = 591295) B591295
theorem B693089 : Blo 307833 693089 := bstep (se 2 (by rfl) ⟨259908, by rfl⟩ : syracuseStep 693089 = 519817) B519817
theorem B497983 : Blo 307833 497983 := bstep (se 1 (by rfl) ⟨373487, by rfl⟩ : syracuseStep 497983 = 746975) B746975
theorem B466217 : Blo 307833 466217 := bstep (se 2 (by rfl) ⟨174831, by rfl⟩ : syracuseStep 466217 = 349663) B349663
theorem B10135205 : Blo 307833 10135205 := bstep (se 4 (by rfl) ⟨950175, by rfl⟩ : syracuseStep 10135205 = 1900351) B1900351
theorem B308335 : Blo 307833 308335 := bstep (se 1 (by rfl) ⟨231251, by rfl⟩ : syracuseStep 308335 = 462503) B462503
theorem B3519611 : Blo 307833 3519611 := bstep (se 1 (by rfl) ⟨2639708, by rfl⟩ : syracuseStep 3519611 = 5279417) B5279417
theorem B308507 : Blo 307833 308507 := bstep (se 1 (by rfl) ⟨231380, by rfl⟩ : syracuseStep 308507 = 462761) B462761
theorem B1888201 : Blo 307833 1888201 := bstep (se 2 (by rfl) ⟨708075, by rfl⟩ : syracuseStep 1888201 = 1416151) B1416151
theorem B1496063 : Blo 307833 1496063 := bstep (se 1 (by rfl) ⟨1122047, by rfl⟩ : syracuseStep 1496063 = 2244095) B2244095
theorem B1597427 : Blo 307833 1597427 := bstep (se 1 (by rfl) ⟨1198070, by rfl⟩ : syracuseStep 1597427 = 2396141) B2396141
theorem B1040687 : Blo 307833 1040687 := bstep (se 1 (by rfl) ⟨780515, by rfl⟩ : syracuseStep 1040687 = 1561031) B1561031
theorem B1567997 : Blo 307833 1567997 := bstep (se 3 (by rfl) ⟨293999, by rfl⟩ : syracuseStep 1567997 = 587999) B587999
theorem B1044521 : Blo 307833 1044521 := bstep (se 2 (by rfl) ⟨391695, by rfl⟩ : syracuseStep 1044521 = 783391) B783391
theorem B25558991 : Blo 307833 25558991 := bstep (se 1 (by rfl) ⟨19169243, by rfl⟩ : syracuseStep 25558991 = 38338487) B38338487
theorem B1769465 : Blo 307833 1769465 := bstep (se 2 (by rfl) ⟨663549, by rfl⟩ : syracuseStep 1769465 = 1327099) B1327099
theorem B525595 : Blo 307833 525595 := bstep (se 1 (by rfl) ⟨394196, by rfl⟩ : syracuseStep 525595 = 788393) B788393
theorem B462059 : Blo 307833 462059 := bstep (se 1 (by rfl) ⟨346544, by rfl⟩ : syracuseStep 462059 = 693089) B693089
theorem B1577069 : Blo 307833 1577069 := bstep (se 3 (by rfl) ⟨295700, by rfl⟩ : syracuseStep 1577069 = 591401) B591401
theorem B693791 : Blo 307833 693791 := bstep (se 1 (by rfl) ⟨520343, by rfl⟩ : syracuseStep 693791 = 1040687) B1040687
theorem B6756803 : Blo 307833 6756803 := bstep (se 1 (by rfl) ⟨5067602, by rfl⟩ : syracuseStep 6756803 = 10135205) B10135205
theorem B696347 : Blo 307833 696347 := bstep (se 1 (by rfl) ⟨522260, by rfl⟩ : syracuseStep 696347 = 1044521) B1044521
theorem B663977 : Blo 307833 663977 := bstep (se 2 (by rfl) ⟨248991, by rfl⟩ : syracuseStep 663977 = 497983) B497983
theorem B2337659 : Blo 307833 2337659 := bstep (se 1 (by rfl) ⟨1753244, by rfl⟩ : syracuseStep 2337659 = 3506489) B3506489
theorem B2338631 : Blo 307833 2338631 := bstep (se 1 (by rfl) ⟨1753973, by rfl⟩ : syracuseStep 2338631 = 3507947) B3507947
theorem B997375 : Blo 307833 997375 := bstep (se 1 (by rfl) ⟨748031, by rfl⟩ : syracuseStep 997375 = 1496063) B1496063
theorem B310811 : Blo 307833 310811 := bstep (se 1 (by rfl) ⟨233108, by rfl⟩ : syracuseStep 310811 = 466217) B466217
theorem B1064951 : Blo 307833 1064951 := bstep (se 1 (by rfl) ⟨798713, by rfl⟩ : syracuseStep 1064951 = 1597427) B1597427
theorem B2346407 : Blo 307833 2346407 := bstep (se 1 (by rfl) ⟨1759805, by rfl⟩ : syracuseStep 2346407 = 3519611) B3519611
theorem B2517601 : Blo 307833 2517601 := bstep (se 2 (by rfl) ⟨944100, by rfl⟩ : syracuseStep 2517601 = 1888201) B1888201
theorem B1045331 : Blo 307833 1045331 := bstep (se 1 (by rfl) ⟨783998, by rfl⟩ : syracuseStep 1045331 = 1567997) B1567997
theorem B17039327 : Blo 307833 17039327 := bstep (se 1 (by rfl) ⟨12779495, by rfl⟩ : syracuseStep 17039327 = 25558991) B25558991
theorem B1179643 : Blo 307833 1179643 := bstep (se 1 (by rfl) ⟨884732, by rfl⟩ : syracuseStep 1179643 = 1769465) B1769465
theorem B1770605 : Blo 307833 1770605 := bstep (se 3 (by rfl) ⟨331988, by rfl⟩ : syracuseStep 1770605 = 663977) B663977
theorem B1051379 : Blo 307833 1051379 := bstep (se 1 (by rfl) ⟨788534, by rfl⟩ : syracuseStep 1051379 = 1577069) B1577069
theorem B462527 : Blo 307833 462527 := bstep (se 1 (by rfl) ⟨346895, by rfl⟩ : syracuseStep 462527 = 693791) B693791
theorem B464231 : Blo 307833 464231 := bstep (se 1 (by rfl) ⟨348173, by rfl⟩ : syracuseStep 464231 = 696347) B696347
theorem B696887 : Blo 307833 696887 := bstep (se 1 (by rfl) ⟨522665, by rfl⟩ : syracuseStep 696887 = 1045331) B1045331
theorem B700793 : Blo 307833 700793 := bstep (se 2 (by rfl) ⟨262797, by rfl⟩ : syracuseStep 700793 = 525595) B525595
theorem B308039 : Blo 307833 308039 := bstep (se 1 (by rfl) ⟨231029, by rfl⟩ : syracuseStep 308039 = 462059) B462059
theorem B3356801 : Blo 307833 3356801 := bstep (se 2 (by rfl) ⟨1258800, by rfl⟩ : syracuseStep 3356801 = 2517601) B2517601
theorem B4504535 : Blo 307833 4504535 := bstep (se 1 (by rfl) ⟨3378401, by rfl⟩ : syracuseStep 4504535 = 6756803) B6756803
theorem B1572857 : Blo 307833 1572857 := bstep (se 2 (by rfl) ⟨589821, by rfl⟩ : syracuseStep 1572857 = 1179643) B1179643
theorem B1558439 : Blo 307833 1558439 := bstep (se 1 (by rfl) ⟨1168829, by rfl⟩ : syracuseStep 1558439 = 2337659) B2337659
theorem B1559087 : Blo 307833 1559087 := bstep (se 1 (by rfl) ⟨1169315, by rfl⟩ : syracuseStep 1559087 = 2338631) B2338631
theorem B1329833 : Blo 307833 1329833 := bstep (se 2 (by rfl) ⟨498687, by rfl⟩ : syracuseStep 1329833 = 997375) B997375
theorem B45438205 : Blo 307833 45438205 := bstep (se 3 (by rfl) ⟨8519663, by rfl⟩ : syracuseStep 45438205 = 17039327) B17039327
theorem B709967 : Blo 307833 709967 := bstep (se 1 (by rfl) ⟨532475, by rfl⟩ : syracuseStep 709967 = 1064951) B1064951
theorem B1564271 : Blo 307833 1564271 := bstep (se 1 (by rfl) ⟨1173203, by rfl⟩ : syracuseStep 1564271 = 2346407) B2346407
theorem B1180403 : Blo 307833 1180403 := bstep (se 1 (by rfl) ⟨885302, by rfl⟩ : syracuseStep 1180403 = 1770605) B1770605
theorem B886555 : Blo 307833 886555 := bstep (se 1 (by rfl) ⟨664916, by rfl⟩ : syracuseStep 886555 = 1329833) B1329833
theorem B464591 : Blo 307833 464591 := bstep (se 1 (by rfl) ⟨348443, by rfl⟩ : syracuseStep 464591 = 696887) B696887
theorem B467195 : Blo 307833 467195 := bstep (se 1 (by rfl) ⟨350396, by rfl⟩ : syracuseStep 467195 = 700793) B700793
theorem B2237867 : Blo 307833 2237867 := bstep (se 1 (by rfl) ⟨1678400, by rfl⟩ : syracuseStep 2237867 = 3356801) B3356801
theorem B700919 : Blo 307833 700919 := bstep (se 1 (by rfl) ⟨525689, by rfl⟩ : syracuseStep 700919 = 1051379) B1051379
theorem B308351 : Blo 307833 308351 := bstep (se 1 (by rfl) ⟨231263, by rfl⟩ : syracuseStep 308351 = 462527) B462527
theorem B473311 : Blo 307833 473311 := bstep (se 1 (by rfl) ⟨354983, by rfl⟩ : syracuseStep 473311 = 709967) B709967
theorem B309487 : Blo 307833 309487 := bstep (se 1 (by rfl) ⟨232115, by rfl⟩ : syracuseStep 309487 = 464231) B464231
theorem B3003023 : Blo 307833 3003023 := bstep (se 1 (by rfl) ⟨2252267, by rfl⟩ : syracuseStep 3003023 = 4504535) B4504535
theorem B1038959 : Blo 307833 1038959 := bstep (se 1 (by rfl) ⟨779219, by rfl⟩ : syracuseStep 1038959 = 1558439) B1558439
theorem B1039391 : Blo 307833 1039391 := bstep (se 1 (by rfl) ⟨779543, by rfl⟩ : syracuseStep 1039391 = 1559087) B1559087
theorem B1042847 : Blo 307833 1042847 := bstep (se 1 (by rfl) ⟨782135, by rfl⟩ : syracuseStep 1042847 = 1564271) B1564271
theorem B60584273 : Blo 307833 60584273 := bstep (se 2 (by rfl) ⟨22719102, by rfl⟩ : syracuseStep 60584273 = 45438205) B45438205
theorem B1048571 : Blo 307833 1048571 := bstep (se 1 (by rfl) ⟨786428, by rfl⟩ : syracuseStep 1048571 = 1572857) B1572857
theorem B786935 : Blo 307833 786935 := bstep (se 1 (by rfl) ⟨590201, by rfl⟩ : syracuseStep 786935 = 1180403) B1180403
theorem B1182073 : Blo 307833 1182073 := bstep (se 2 (by rfl) ⟨443277, by rfl⟩ : syracuseStep 1182073 = 886555) B886555
theorem B2002015 : Blo 307833 2002015 := bstep (se 1 (by rfl) ⟨1501511, by rfl⟩ : syracuseStep 2002015 = 3003023) B3003023
theorem B692639 : Blo 307833 692639 := bstep (se 1 (by rfl) ⟨519479, by rfl⟩ : syracuseStep 692639 = 1038959) B1038959
theorem B692927 : Blo 307833 692927 := bstep (se 1 (by rfl) ⟨519695, by rfl⟩ : syracuseStep 692927 = 1039391) B1039391
theorem B695231 : Blo 307833 695231 := bstep (se 1 (by rfl) ⟨521423, by rfl⟩ : syracuseStep 695231 = 1042847) B1042847
theorem B631081 : Blo 307833 631081 := bstep (se 2 (by rfl) ⟨236655, by rfl⟩ : syracuseStep 631081 = 473311) B473311
theorem B467279 : Blo 307833 467279 := bstep (se 1 (by rfl) ⟨350459, by rfl⟩ : syracuseStep 467279 = 700919) B700919
theorem B699047 : Blo 307833 699047 := bstep (se 1 (by rfl) ⟨524285, by rfl⟩ : syracuseStep 699047 = 1048571) B1048571
theorem B309727 : Blo 307833 309727 := bstep (se 1 (by rfl) ⟨232295, by rfl⟩ : syracuseStep 309727 = 464591) B464591
theorem B311463 : Blo 307833 311463 := bstep (se 1 (by rfl) ⟨233597, by rfl⟩ : syracuseStep 311463 = 467195) B467195
theorem B1491911 : Blo 307833 1491911 := bstep (se 1 (by rfl) ⟨1118933, by rfl⟩ : syracuseStep 1491911 = 2237867) B2237867
theorem B40389515 : Blo 307833 40389515 := bstep (se 1 (by rfl) ⟨30292136, by rfl⟩ : syracuseStep 40389515 = 60584273) B60584273
theorem B524623 : Blo 307833 524623 := bstep (se 1 (by rfl) ⟨393467, by rfl⟩ : syracuseStep 524623 = 786935) B786935
theorem B461759 : Blo 307833 461759 := bstep (se 1 (by rfl) ⟨346319, by rfl⟩ : syracuseStep 461759 = 692639) B692639
theorem B461951 : Blo 307833 461951 := bstep (se 1 (by rfl) ⟨346463, by rfl⟩ : syracuseStep 461951 = 692927) B692927
theorem B1576097 : Blo 307833 1576097 := bstep (se 2 (by rfl) ⟨591036, by rfl⟩ : syracuseStep 1576097 = 1182073) B1182073
theorem B463487 : Blo 307833 463487 := bstep (se 1 (by rfl) ⟨347615, by rfl⟩ : syracuseStep 463487 = 695231) B695231
theorem B466031 : Blo 307833 466031 := bstep (se 1 (by rfl) ⟨349523, by rfl⟩ : syracuseStep 466031 = 699047) B699047
theorem B994607 : Blo 307833 994607 := bstep (se 1 (by rfl) ⟨745955, by rfl⟩ : syracuseStep 994607 = 1491911) B1491911
theorem B311519 : Blo 307833 311519 := bstep (se 1 (by rfl) ⟨233639, by rfl⟩ : syracuseStep 311519 = 467279) B467279
theorem B841441 : Blo 307833 841441 := bstep (se 2 (by rfl) ⟨315540, by rfl⟩ : syracuseStep 841441 = 631081) B631081
theorem B26926343 : Blo 307833 26926343 := bstep (se 1 (by rfl) ⟨20194757, by rfl⟩ : syracuseStep 26926343 = 40389515) B40389515
theorem B10677413 : Blo 307833 10677413 := bstep (se 4 (by rfl) ⟨1001007, by rfl⟩ : syracuseStep 10677413 = 2002015) B2002015
theorem B1050731 : Blo 307833 1050731 := bstep (se 1 (by rfl) ⟨788048, by rfl⟩ : syracuseStep 1050731 = 1576097) B1576097
theorem B7118275 : Blo 307833 7118275 := bstep (se 1 (by rfl) ⟨5338706, by rfl⟩ : syracuseStep 7118275 = 10677413) B10677413
theorem B663071 : Blo 307833 663071 := bstep (se 1 (by rfl) ⟨497303, by rfl⟩ : syracuseStep 663071 = 994607) B994607
theorem B1121921 : Blo 307833 1121921 := bstep (se 2 (by rfl) ⟨420720, by rfl⟩ : syracuseStep 1121921 = 841441) B841441
theorem B699497 : Blo 307833 699497 := bstep (se 2 (by rfl) ⟨262311, by rfl⟩ : syracuseStep 699497 = 524623) B524623
theorem B307839 : Blo 307833 307839 := bstep (se 1 (by rfl) ⟨230879, by rfl⟩ : syracuseStep 307839 = 461759) B461759
theorem B307967 : Blo 307833 307967 := bstep (se 1 (by rfl) ⟨230975, by rfl⟩ : syracuseStep 307967 = 461951) B461951
theorem B308991 : Blo 307833 308991 := bstep (se 1 (by rfl) ⟨231743, by rfl⟩ : syracuseStep 308991 = 463487) B463487
theorem B310687 : Blo 307833 310687 := bstep (se 1 (by rfl) ⟨233015, by rfl⟩ : syracuseStep 310687 = 466031) B466031
theorem B17950895 : Blo 307833 17950895 := bstep (se 1 (by rfl) ⟨13463171, by rfl⟩ : syracuseStep 17950895 = 26926343) B26926343
theorem B11967263 : Blo 307833 11967263 := bstep (se 1 (by rfl) ⟨8975447, by rfl⟩ : syracuseStep 11967263 = 17950895) B17950895
theorem B466331 : Blo 307833 466331 := bstep (se 1 (by rfl) ⟨349748, by rfl⟩ : syracuseStep 466331 = 699497) B699497
theorem B700487 : Blo 307833 700487 := bstep (se 1 (by rfl) ⟨525365, by rfl⟩ : syracuseStep 700487 = 1050731) B1050731
theorem B9491033 : Blo 307833 9491033 := bstep (se 2 (by rfl) ⟨3559137, by rfl⟩ : syracuseStep 9491033 = 7118275) B7118275
theorem B747947 : Blo 307833 747947 := bstep (se 1 (by rfl) ⟨560960, by rfl⟩ : syracuseStep 747947 = 1121921) B1121921
theorem B1768189 : Blo 307833 1768189 := bstep (se 3 (by rfl) ⟨331535, by rfl⟩ : syracuseStep 1768189 = 663071) B663071
theorem B498631 : Blo 307833 498631 := bstep (se 1 (by rfl) ⟨373973, by rfl⟩ : syracuseStep 498631 = 747947) B747947
theorem B466991 : Blo 307833 466991 := bstep (se 1 (by rfl) ⟨350243, by rfl⟩ : syracuseStep 466991 = 700487) B700487
theorem B25309421 : Blo 307833 25309421 := bstep (se 3 (by rfl) ⟨4745516, by rfl⟩ : syracuseStep 25309421 = 9491033) B9491033
theorem B7978175 : Blo 307833 7978175 := bstep (se 1 (by rfl) ⟨5983631, by rfl⟩ : syracuseStep 7978175 = 11967263) B11967263
theorem B310887 : Blo 307833 310887 := bstep (se 1 (by rfl) ⟨233165, by rfl⟩ : syracuseStep 310887 = 466331) B466331
theorem B2357585 : Blo 307833 2357585 := bstep (se 2 (by rfl) ⟨884094, by rfl⟩ : syracuseStep 2357585 = 1768189) B1768189
theorem B664841 : Blo 307833 664841 := bstep (se 2 (by rfl) ⟨249315, by rfl⟩ : syracuseStep 664841 = 498631) B498631
theorem B5318783 : Blo 307833 5318783 := bstep (se 1 (by rfl) ⟨3989087, by rfl⟩ : syracuseStep 5318783 = 7978175) B7978175
theorem B311327 : Blo 307833 311327 := bstep (se 1 (by rfl) ⟨233495, by rfl⟩ : syracuseStep 311327 = 466991) B466991
theorem B16872947 : Blo 307833 16872947 := bstep (se 1 (by rfl) ⟨12654710, by rfl⟩ : syracuseStep 16872947 = 25309421) B25309421
theorem B1571723 : Blo 307833 1571723 := bstep (se 1 (by rfl) ⟨1178792, by rfl⟩ : syracuseStep 1571723 = 2357585) B2357585
theorem B3545855 : Blo 307833 3545855 := bstep (se 1 (by rfl) ⟨2659391, by rfl⟩ : syracuseStep 3545855 = 5318783) B5318783
theorem B11248631 : Blo 307833 11248631 := bstep (se 1 (by rfl) ⟨8436473, by rfl⟩ : syracuseStep 11248631 = 16872947) B16872947
theorem B443227 : Blo 307833 443227 := bstep (se 1 (by rfl) ⟨332420, by rfl⟩ : syracuseStep 443227 = 664841) B664841
theorem B1047815 : Blo 307833 1047815 := bstep (se 1 (by rfl) ⟨785861, by rfl⟩ : syracuseStep 1047815 = 1571723) B1571723
theorem B590969 : Blo 307833 590969 := bstep (se 2 (by rfl) ⟨221613, by rfl⟩ : syracuseStep 590969 = 443227) B443227
theorem B2363903 : Blo 307833 2363903 := bstep (se 1 (by rfl) ⟨1772927, by rfl⟩ : syracuseStep 2363903 = 3545855) B3545855
theorem B698543 : Blo 307833 698543 := bstep (se 1 (by rfl) ⟨523907, by rfl⟩ : syracuseStep 698543 = 1047815) B1047815
theorem B7499087 : Blo 307833 7499087 := bstep (se 1 (by rfl) ⟨5624315, by rfl⟩ : syracuseStep 7499087 = 11248631) B11248631
theorem B393979 : Blo 307833 393979 := bstep (se 1 (by rfl) ⟨295484, by rfl⟩ : syracuseStep 393979 = 590969) B590969
theorem B1575935 : Blo 307833 1575935 := bstep (se 1 (by rfl) ⟨1181951, by rfl⟩ : syracuseStep 1575935 = 2363903) B2363903
theorem B465695 : Blo 307833 465695 := bstep (se 1 (by rfl) ⟨349271, by rfl⟩ : syracuseStep 465695 = 698543) B698543
theorem B4999391 : Blo 307833 4999391 := bstep (se 1 (by rfl) ⟨3749543, by rfl⟩ : syracuseStep 4999391 = 7499087) B7499087
theorem B525305 : Blo 307833 525305 := bstep (se 2 (by rfl) ⟨196989, by rfl⟩ : syracuseStep 525305 = 393979) B393979
theorem B1050623 : Blo 307833 1050623 := bstep (se 1 (by rfl) ⟨787967, by rfl⟩ : syracuseStep 1050623 = 1575935) B1575935
theorem B310463 : Blo 307833 310463 := bstep (se 1 (by rfl) ⟨232847, by rfl⟩ : syracuseStep 310463 = 465695) B465695
theorem B3332927 : Blo 307833 3332927 := bstep (se 1 (by rfl) ⟨2499695, by rfl⟩ : syracuseStep 3332927 = 4999391) B4999391
theorem B700415 : Blo 307833 700415 := bstep (se 1 (by rfl) ⟨525311, by rfl⟩ : syracuseStep 700415 = 1050623) B1050623
theorem B350203 : Blo 307833 350203 := bstep (se 1 (by rfl) ⟨262652, by rfl⟩ : syracuseStep 350203 = 525305) B525305
theorem B2221951 : Blo 307833 2221951 := bstep (se 1 (by rfl) ⟨1666463, by rfl⟩ : syracuseStep 2221951 = 3332927) B3332927
theorem B466937 : Blo 307833 466937 := bstep (se 2 (by rfl) ⟨175101, by rfl⟩ : syracuseStep 466937 = 350203) B350203
theorem B466943 : Blo 307833 466943 := bstep (se 1 (by rfl) ⟨350207, by rfl⟩ : syracuseStep 466943 = 700415) B700415
theorem B2962601 : Blo 307833 2962601 := bstep (se 2 (by rfl) ⟨1110975, by rfl⟩ : syracuseStep 2962601 = 2221951) B2221951
theorem B1975067 : Blo 307833 1975067 := bstep (se 1 (by rfl) ⟨1481300, by rfl⟩ : syracuseStep 1975067 = 2962601) B2962601
theorem B311291 : Blo 307833 311291 := bstep (se 1 (by rfl) ⟨233468, by rfl⟩ : syracuseStep 311291 = 466937) B466937
theorem B311295 : Blo 307833 311295 := bstep (se 1 (by rfl) ⟨233471, by rfl⟩ : syracuseStep 311295 = 466943) B466943
theorem B1316711 : Blo 307833 1316711 := bstep (se 1 (by rfl) ⟨987533, by rfl⟩ : syracuseStep 1316711 = 1975067) B1975067
theorem B877807 : Blo 307833 877807 := bstep (se 1 (by rfl) ⟨658355, by rfl⟩ : syracuseStep 877807 = 1316711) B1316711
theorem B1170409 : Blo 307833 1170409 := bstep (se 2 (by rfl) ⟨438903, by rfl⟩ : syracuseStep 1170409 = 877807) B877807
theorem B1560545 : Blo 307833 1560545 := bstep (se 2 (by rfl) ⟨585204, by rfl⟩ : syracuseStep 1560545 = 1170409) B1170409
theorem B1040363 : Blo 307833 1040363 := bstep (se 1 (by rfl) ⟨780272, by rfl⟩ : syracuseStep 1040363 = 1560545) B1560545
theorem B693575 : Blo 307833 693575 := bstep (se 1 (by rfl) ⟨520181, by rfl⟩ : syracuseStep 693575 = 1040363) B1040363
theorem B462383 : Blo 307833 462383 := bstep (se 1 (by rfl) ⟨346787, by rfl⟩ : syracuseStep 462383 = 693575) B693575
theorem B308255 : Blo 307833 308255 := bstep (se 1 (by rfl) ⟨231191, by rfl⟩ : syracuseStep 308255 = 462383) B462383

theorem C0 (j : ℕ) (h1 : 76958 ≤ j) (h2 : j ≤ 77657) : Blo 307833 (4 * j + 3) := by
  interval_cases j
  · exact B307835
  · exact B307839
  · exact B307843
  · exact B307847
  · exact B307851
  · exact B307855
  · exact B307859
  · exact B307863
  · exact B307867
  · exact B307871
  · exact B307875
  · exact B307879
  · exact B307883
  · exact B307887
  · exact B307891
  · exact B307895
  · exact B307899
  · exact B307903
  · exact B307907
  · exact B307911
  · exact B307915
  · exact B307919
  · exact B307923
  · exact B307927
  · exact B307931
  · exact B307935
  · exact B307939
  · exact B307943
  · exact B307947
  · exact B307951
  · exact B307955
  · exact B307959
  · exact B307963
  · exact B307967
  · exact B307971
  · exact B307975
  · exact B307979
  · exact B307983
  · exact B307987
  · exact B307991
  · exact B307995
  · exact B307999
  · exact B308003
  · exact B308007
  · exact B308011
  · exact B308015
  · exact B308019
  · exact B308023
  · exact B308027
  · exact B308031
  · exact B308035
  · exact B308039
  · exact B308043
  · exact B308047
  · exact B308051
  · exact B308055
  · exact B308059
  · exact B308063
  · exact B308067
  · exact B308071
  · exact B308075
  · exact B308079
  · exact B308083
  · exact B308087
  · exact B308091
  · exact B308095
  · exact B308099
  · exact B308103
  · exact B308107
  · exact B308111
  · exact B308115
  · exact B308119
  · exact B308123
  · exact B308127
  · exact B308131
  · exact B308135
  · exact B308139
  · exact B308143
  · exact B308147
  · exact B308151
  · exact B308155
  · exact B308159
  · exact B308163
  · exact B308167
  · exact B308171
  · exact B308175
  · exact B308179
  · exact B308183
  · exact B308187
  · exact B308191
  · exact B308195
  · exact B308199
  · exact B308203
  · exact B308207
  · exact B308211
  · exact B308215
  · exact B308219
  · exact B308223
  · exact B308227
  · exact B308231
  · exact B308235
  · exact B308239
  · exact B308243
  · exact B308247
  · exact B308251
  · exact B308255
  · exact B308259
  · exact B308263
  · exact B308267
  · exact B308271
  · exact B308275
  · exact B308279
  · exact B308283
  · exact B308287
  · exact B308291
  · exact B308295
  · exact B308299
  · exact B308303
  · exact B308307
  · exact B308311
  · exact B308315
  · exact B308319
  · exact B308323
  · exact B308327
  · exact B308331
  · exact B308335
  · exact B308339
  · exact B308343
  · exact B308347
  · exact B308351
  · exact B308355
  · exact B308359
  · exact B308363
  · exact B308367
  · exact B308371
  · exact B308375
  · exact B308379
  · exact B308383
  · exact B308387
  · exact B308391
  · exact B308395
  · exact B308399
  · exact B308403
  · exact B308407
  · exact B308411
  · exact B308415
  · exact B308419
  · exact B308423
  · exact B308427
  · exact B308431
  · exact B308435
  · exact B308439
  · exact B308443
  · exact B308447
  · exact B308451
  · exact B308455
  · exact B308459
  · exact B308463
  · exact B308467
  · exact B308471
  · exact B308475
  · exact B308479
  · exact B308483
  · exact B308487
  · exact B308491
  · exact B308495
  · exact B308499
  · exact B308503
  · exact B308507
  · exact B308511
  · exact B308515
  · exact B308519
  · exact B308523
  · exact B308527
  · exact B308531
  · exact B308535
  · exact B308539
  · exact B308543
  · exact B308547
  · exact B308551
  · exact B308555
  · exact B308559
  · exact B308563
  · exact B308567
  · exact B308571
  · exact B308575
  · exact B308579
  · exact B308583
  · exact B308587
  · exact B308591
  · exact B308595
  · exact B308599
  · exact B308603
  · exact B308607
  · exact B308611
  · exact B308615
  · exact B308619
  · exact B308623
  · exact B308627
  · exact B308631
  · exact B308635
  · exact B308639
  · exact B308643
  · exact B308647
  · exact B308651
  · exact B308655
  · exact B308659
  · exact B308663
  · exact B308667
  · exact B308671
  · exact B308675
  · exact B308679
  · exact B308683
  · exact B308687
  · exact B308691
  · exact B308695
  · exact B308699
  · exact B308703
  · exact B308707
  · exact B308711
  · exact B308715
  · exact B308719
  · exact B308723
  · exact B308727
  · exact B308731
  · exact B308735
  · exact B308739
  · exact B308743
  · exact B308747
  · exact B308751
  · exact B308755
  · exact B308759
  · exact B308763
  · exact B308767
  · exact B308771
  · exact B308775
  · exact B308779
  · exact B308783
  · exact B308787
  · exact B308791
  · exact B308795
  · exact B308799
  · exact B308803
  · exact B308807
  · exact B308811
  · exact B308815
  · exact B308819
  · exact B308823
  · exact B308827
  · exact B308831
  · exact B308835
  · exact B308839
  · exact B308843
  · exact B308847
  · exact B308851
  · exact B308855
  · exact B308859
  · exact B308863
  · exact B308867
  · exact B308871
  · exact B308875
  · exact B308879
  · exact B308883
  · exact B308887
  · exact B308891
  · exact B308895
  · exact B308899
  · exact B308903
  · exact B308907
  · exact B308911
  · exact B308915
  · exact B308919
  · exact B308923
  · exact B308927
  · exact B308931
  · exact B308935
  · exact B308939
  · exact B308943
  · exact B308947
  · exact B308951
  · exact B308955
  · exact B308959
  · exact B308963
  · exact B308967
  · exact B308971
  · exact B308975
  · exact B308979
  · exact B308983
  · exact B308987
  · exact B308991
  · exact B308995
  · exact B308999
  · exact B309003
  · exact B309007
  · exact B309011
  · exact B309015
  · exact B309019
  · exact B309023
  · exact B309027
  · exact B309031
  · exact B309035
  · exact B309039
  · exact B309043
  · exact B309047
  · exact B309051
  · exact B309055
  · exact B309059
  · exact B309063
  · exact B309067
  · exact B309071
  · exact B309075
  · exact B309079
  · exact B309083
  · exact B309087
  · exact B309091
  · exact B309095
  · exact B309099
  · exact B309103
  · exact B309107
  · exact B309111
  · exact B309115
  · exact B309119
  · exact B309123
  · exact B309127
  · exact B309131
  · exact B309135
  · exact B309139
  · exact B309143
  · exact B309147
  · exact B309151
  · exact B309155
  · exact B309159
  · exact B309163
  · exact B309167
  · exact B309171
  · exact B309175
  · exact B309179
  · exact B309183
  · exact B309187
  · exact B309191
  · exact B309195
  · exact B309199
  · exact B309203
  · exact B309207
  · exact B309211
  · exact B309215
  · exact B309219
  · exact B309223
  · exact B309227
  · exact B309231
  · exact B309235
  · exact B309239
  · exact B309243
  · exact B309247
  · exact B309251
  · exact B309255
  · exact B309259
  · exact B309263
  · exact B309267
  · exact B309271
  · exact B309275
  · exact B309279
  · exact B309283
  · exact B309287
  · exact B309291
  · exact B309295
  · exact B309299
  · exact B309303
  · exact B309307
  · exact B309311
  · exact B309315
  · exact B309319
  · exact B309323
  · exact B309327
  · exact B309331
  · exact B309335
  · exact B309339
  · exact B309343
  · exact B309347
  · exact B309351
  · exact B309355
  · exact B309359
  · exact B309363
  · exact B309367
  · exact B309371
  · exact B309375
  · exact B309379
  · exact B309383
  · exact B309387
  · exact B309391
  · exact B309395
  · exact B309399
  · exact B309403
  · exact B309407
  · exact B309411
  · exact B309415
  · exact B309419
  · exact B309423
  · exact B309427
  · exact B309431
  · exact B309435
  · exact B309439
  · exact B309443
  · exact B309447
  · exact B309451
  · exact B309455
  · exact B309459
  · exact B309463
  · exact B309467
  · exact B309471
  · exact B309475
  · exact B309479
  · exact B309483
  · exact B309487
  · exact B309491
  · exact B309495
  · exact B309499
  · exact B309503
  · exact B309507
  · exact B309511
  · exact B309515
  · exact B309519
  · exact B309523
  · exact B309527
  · exact B309531
  · exact B309535
  · exact B309539
  · exact B309543
  · exact B309547
  · exact B309551
  · exact B309555
  · exact B309559
  · exact B309563
  · exact B309567
  · exact B309571
  · exact B309575
  · exact B309579
  · exact B309583
  · exact B309587
  · exact B309591
  · exact B309595
  · exact B309599
  · exact B309603
  · exact B309607
  · exact B309611
  · exact B309615
  · exact B309619
  · exact B309623
  · exact B309627
  · exact B309631
  · exact B309635
  · exact B309639
  · exact B309643
  · exact B309647
  · exact B309651
  · exact B309655
  · exact B309659
  · exact B309663
  · exact B309667
  · exact B309671
  · exact B309675
  · exact B309679
  · exact B309683
  · exact B309687
  · exact B309691
  · exact B309695
  · exact B309699
  · exact B309703
  · exact B309707
  · exact B309711
  · exact B309715
  · exact B309719
  · exact B309723
  · exact B309727
  · exact B309731
  · exact B309735
  · exact B309739
  · exact B309743
  · exact B309747
  · exact B309751
  · exact B309755
  · exact B309759
  · exact B309763
  · exact B309767
  · exact B309771
  · exact B309775
  · exact B309779
  · exact B309783
  · exact B309787
  · exact B309791
  · exact B309795
  · exact B309799
  · exact B309803
  · exact B309807
  · exact B309811
  · exact B309815
  · exact B309819
  · exact B309823
  · exact B309827
  · exact B309831
  · exact B309835
  · exact B309839
  · exact B309843
  · exact B309847
  · exact B309851
  · exact B309855
  · exact B309859
  · exact B309863
  · exact B309867
  · exact B309871
  · exact B309875
  · exact B309879
  · exact B309883
  · exact B309887
  · exact B309891
  · exact B309895
  · exact B309899
  · exact B309903
  · exact B309907
  · exact B309911
  · exact B309915
  · exact B309919
  · exact B309923
  · exact B309927
  · exact B309931
  · exact B309935
  · exact B309939
  · exact B309943
  · exact B309947
  · exact B309951
  · exact B309955
  · exact B309959
  · exact B309963
  · exact B309967
  · exact B309971
  · exact B309975
  · exact B309979
  · exact B309983
  · exact B309987
  · exact B309991
  · exact B309995
  · exact B309999
  · exact B310003
  · exact B310007
  · exact B310011
  · exact B310015
  · exact B310019
  · exact B310023
  · exact B310027
  · exact B310031
  · exact B310035
  · exact B310039
  · exact B310043
  · exact B310047
  · exact B310051
  · exact B310055
  · exact B310059
  · exact B310063
  · exact B310067
  · exact B310071
  · exact B310075
  · exact B310079
  · exact B310083
  · exact B310087
  · exact B310091
  · exact B310095
  · exact B310099
  · exact B310103
  · exact B310107
  · exact B310111
  · exact B310115
  · exact B310119
  · exact B310123
  · exact B310127
  · exact B310131
  · exact B310135
  · exact B310139
  · exact B310143
  · exact B310147
  · exact B310151
  · exact B310155
  · exact B310159
  · exact B310163
  · exact B310167
  · exact B310171
  · exact B310175
  · exact B310179
  · exact B310183
  · exact B310187
  · exact B310191
  · exact B310195
  · exact B310199
  · exact B310203
  · exact B310207
  · exact B310211
  · exact B310215
  · exact B310219
  · exact B310223
  · exact B310227
  · exact B310231
  · exact B310235
  · exact B310239
  · exact B310243
  · exact B310247
  · exact B310251
  · exact B310255
  · exact B310259
  · exact B310263
  · exact B310267
  · exact B310271
  · exact B310275
  · exact B310279
  · exact B310283
  · exact B310287
  · exact B310291
  · exact B310295
  · exact B310299
  · exact B310303
  · exact B310307
  · exact B310311
  · exact B310315
  · exact B310319
  · exact B310323
  · exact B310327
  · exact B310331
  · exact B310335
  · exact B310339
  · exact B310343
  · exact B310347
  · exact B310351
  · exact B310355
  · exact B310359
  · exact B310363
  · exact B310367
  · exact B310371
  · exact B310375
  · exact B310379
  · exact B310383
  · exact B310387
  · exact B310391
  · exact B310395
  · exact B310399
  · exact B310403
  · exact B310407
  · exact B310411
  · exact B310415
  · exact B310419
  · exact B310423
  · exact B310427
  · exact B310431
  · exact B310435
  · exact B310439
  · exact B310443
  · exact B310447
  · exact B310451
  · exact B310455
  · exact B310459
  · exact B310463
  · exact B310467
  · exact B310471
  · exact B310475
  · exact B310479
  · exact B310483
  · exact B310487
  · exact B310491
  · exact B310495
  · exact B310499
  · exact B310503
  · exact B310507
  · exact B310511
  · exact B310515
  · exact B310519
  · exact B310523
  · exact B310527
  · exact B310531
  · exact B310535
  · exact B310539
  · exact B310543
  · exact B310547
  · exact B310551
  · exact B310555
  · exact B310559
  · exact B310563
  · exact B310567
  · exact B310571
  · exact B310575
  · exact B310579
  · exact B310583
  · exact B310587
  · exact B310591
  · exact B310595
  · exact B310599
  · exact B310603
  · exact B310607
  · exact B310611
  · exact B310615
  · exact B310619
  · exact B310623
  · exact B310627
  · exact B310631

theorem C1 (j : ℕ) (h1 : 77658 ≤ j) (h2 : j ≤ 77957) : Blo 307833 (4 * j + 3) := by
  interval_cases j
  · exact B310635
  · exact B310639
  · exact B310643
  · exact B310647
  · exact B310651
  · exact B310655
  · exact B310659
  · exact B310663
  · exact B310667
  · exact B310671
  · exact B310675
  · exact B310679
  · exact B310683
  · exact B310687
  · exact B310691
  · exact B310695
  · exact B310699
  · exact B310703
  · exact B310707
  · exact B310711
  · exact B310715
  · exact B310719
  · exact B310723
  · exact B310727
  · exact B310731
  · exact B310735
  · exact B310739
  · exact B310743
  · exact B310747
  · exact B310751
  · exact B310755
  · exact B310759
  · exact B310763
  · exact B310767
  · exact B310771
  · exact B310775
  · exact B310779
  · exact B310783
  · exact B310787
  · exact B310791
  · exact B310795
  · exact B310799
  · exact B310803
  · exact B310807
  · exact B310811
  · exact B310815
  · exact B310819
  · exact B310823
  · exact B310827
  · exact B310831
  · exact B310835
  · exact B310839
  · exact B310843
  · exact B310847
  · exact B310851
  · exact B310855
  · exact B310859
  · exact B310863
  · exact B310867
  · exact B310871
  · exact B310875
  · exact B310879
  · exact B310883
  · exact B310887
  · exact B310891
  · exact B310895
  · exact B310899
  · exact B310903
  · exact B310907
  · exact B310911
  · exact B310915
  · exact B310919
  · exact B310923
  · exact B310927
  · exact B310931
  · exact B310935
  · exact B310939
  · exact B310943
  · exact B310947
  · exact B310951
  · exact B310955
  · exact B310959
  · exact B310963
  · exact B310967
  · exact B310971
  · exact B310975
  · exact B310979
  · exact B310983
  · exact B310987
  · exact B310991
  · exact B310995
  · exact B310999
  · exact B311003
  · exact B311007
  · exact B311011
  · exact B311015
  · exact B311019
  · exact B311023
  · exact B311027
  · exact B311031
  · exact B311035
  · exact B311039
  · exact B311043
  · exact B311047
  · exact B311051
  · exact B311055
  · exact B311059
  · exact B311063
  · exact B311067
  · exact B311071
  · exact B311075
  · exact B311079
  · exact B311083
  · exact B311087
  · exact B311091
  · exact B311095
  · exact B311099
  · exact B311103
  · exact B311107
  · exact B311111
  · exact B311115
  · exact B311119
  · exact B311123
  · exact B311127
  · exact B311131
  · exact B311135
  · exact B311139
  · exact B311143
  · exact B311147
  · exact B311151
  · exact B311155
  · exact B311159
  · exact B311163
  · exact B311167
  · exact B311171
  · exact B311175
  · exact B311179
  · exact B311183
  · exact B311187
  · exact B311191
  · exact B311195
  · exact B311199
  · exact B311203
  · exact B311207
  · exact B311211
  · exact B311215
  · exact B311219
  · exact B311223
  · exact B311227
  · exact B311231
  · exact B311235
  · exact B311239
  · exact B311243
  · exact B311247
  · exact B311251
  · exact B311255
  · exact B311259
  · exact B311263
  · exact B311267
  · exact B311271
  · exact B311275
  · exact B311279
  · exact B311283
  · exact B311287
  · exact B311291
  · exact B311295
  · exact B311299
  · exact B311303
  · exact B311307
  · exact B311311
  · exact B311315
  · exact B311319
  · exact B311323
  · exact B311327
  · exact B311331
  · exact B311335
  · exact B311339
  · exact B311343
  · exact B311347
  · exact B311351
  · exact B311355
  · exact B311359
  · exact B311363
  · exact B311367
  · exact B311371
  · exact B311375
  · exact B311379
  · exact B311383
  · exact B311387
  · exact B311391
  · exact B311395
  · exact B311399
  · exact B311403
  · exact B311407
  · exact B311411
  · exact B311415
  · exact B311419
  · exact B311423
  · exact B311427
  · exact B311431
  · exact B311435
  · exact B311439
  · exact B311443
  · exact B311447
  · exact B311451
  · exact B311455
  · exact B311459
  · exact B311463
  · exact B311467
  · exact B311471
  · exact B311475
  · exact B311479
  · exact B311483
  · exact B311487
  · exact B311491
  · exact B311495
  · exact B311499
  · exact B311503
  · exact B311507
  · exact B311511
  · exact B311515
  · exact B311519
  · exact B311523
  · exact B311527
  · exact B311531
  · exact B311535
  · exact B311539
  · exact B311543
  · exact B311547
  · exact B311551
  · exact B311555
  · exact B311559
  · exact B311563
  · exact B311567
  · exact B311571
  · exact B311575
  · exact B311579
  · exact B311583
  · exact B311587
  · exact B311591
  · exact B311595
  · exact B311599
  · exact B311603
  · exact B311607
  · exact B311611
  · exact B311615
  · exact B311619
  · exact B311623
  · exact B311627
  · exact B311631
  · exact B311635
  · exact B311639
  · exact B311643
  · exact B311647
  · exact B311651
  · exact B311655
  · exact B311659
  · exact B311663
  · exact B311667
  · exact B311671
  · exact B311675
  · exact B311679
  · exact B311683
  · exact B311687
  · exact B311691
  · exact B311695
  · exact B311699
  · exact B311703
  · exact B311707
  · exact B311711
  · exact B311715
  · exact B311719
  · exact B311723
  · exact B311727
  · exact B311731
  · exact B311735
  · exact B311739
  · exact B311743
  · exact B311747
  · exact B311751
  · exact B311755
  · exact B311759
  · exact B311763
  · exact B311767
  · exact B311771
  · exact B311775
  · exact B311779
  · exact B311783
  · exact B311787
  · exact B311791
  · exact B311795
  · exact B311799
  · exact B311803
  · exact B311807
  · exact B311811
  · exact B311815
  · exact B311819
  · exact B311823
  · exact B311827
  · exact B311831

theorem solution (m : ℕ) (hlo : 307833 ≤ m) (hhi : m ≤ 311833) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 76958 ≤ j := by omega
    have hj2 : j ≤ 77957 := by omega
    have hb : Blo 307833 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 77658 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
