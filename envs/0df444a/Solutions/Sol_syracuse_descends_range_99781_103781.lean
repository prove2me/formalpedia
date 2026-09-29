-- Prove2me | solution 1 for syracuse_descends_range_99781_103781
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:24.580892+00:00
-- url     : https://prove2.me/submissions/10867add-2864-4a78-9e32-1013d091b4a1

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


theorem B229421 : Blo 99781 229421 := bbase (se 3 (by rfl) ⟨43016, by rfl⟩ : syracuseStep 229421 = 86033) (by norm_num)
theorem B163885 : Blo 99781 163885 := bbase (se 3 (by rfl) ⟨30728, by rfl⟩ : syracuseStep 163885 = 61457) (by norm_num)
theorem B229445 : Blo 99781 229445 := bbase (se 4 (by rfl) ⟨21510, by rfl⟩ : syracuseStep 229445 = 43021) (by norm_num)
theorem B131149 : Blo 99781 131149 := bbase (se 3 (by rfl) ⟨24590, by rfl⟩ : syracuseStep 131149 = 49181) (by norm_num)
theorem B262237 : Blo 99781 262237 := bbase (se 3 (by rfl) ⟨49169, by rfl⟩ : syracuseStep 262237 = 98339) (by norm_num)
theorem B229517 : Blo 99781 229517 := bbase (se 3 (by rfl) ⟨43034, by rfl⟩ : syracuseStep 229517 = 86069) (by norm_num)
theorem B327845 : Blo 99781 327845 := bbase (se 4 (by rfl) ⟨30735, by rfl⟩ : syracuseStep 327845 = 61471) (by norm_num)
theorem B295109 : Blo 99781 295109 := bbase (se 4 (by rfl) ⟨27666, by rfl⟩ : syracuseStep 295109 = 55333) (by norm_num)
theorem B262349 : Blo 99781 262349 := bbase (se 3 (by rfl) ⟨49190, by rfl⟩ : syracuseStep 262349 = 98381) (by norm_num)
theorem B229589 : Blo 99781 229589 := bbase (se 7 (by rfl) ⟨2690, by rfl⟩ : syracuseStep 229589 = 5381) (by norm_num)
theorem B131321 : Blo 99781 131321 := bbase (se 2 (by rfl) ⟨49245, by rfl⟩ : syracuseStep 131321 = 98491) (by norm_num)
theorem B229661 : Blo 99781 229661 := bbase (se 3 (by rfl) ⟨43061, by rfl⟩ : syracuseStep 229661 = 86123) (by norm_num)
theorem B229733 : Blo 99781 229733 := bbase (se 4 (by rfl) ⟨21537, by rfl⟩ : syracuseStep 229733 = 43075) (by norm_num)
theorem B262541 : Blo 99781 262541 := bbase (se 3 (by rfl) ⟨49226, by rfl⟩ : syracuseStep 262541 = 98453) (by norm_num)
theorem B197005 : Blo 99781 197005 := bbase (se 3 (by rfl) ⟨36938, by rfl⟩ : syracuseStep 197005 = 73877) (by norm_num)
theorem B229805 : Blo 99781 229805 := bbase (se 3 (by rfl) ⟨43088, by rfl⟩ : syracuseStep 229805 = 86177) (by norm_num)
theorem B164333 : Blo 99781 164333 := bbase (se 3 (by rfl) ⟨30812, by rfl⟩ : syracuseStep 164333 = 61625) (by norm_num)
theorem B229877 : Blo 99781 229877 := bbase (se 5 (by rfl) ⟨10775, by rfl⟩ : syracuseStep 229877 = 21551) (by norm_num)
theorem B393781 : Blo 99781 393781 := bbase (se 5 (by rfl) ⟨18458, by rfl⟩ : syracuseStep 393781 = 36917) (by norm_num)
theorem B229949 : Blo 99781 229949 := bbase (se 3 (by rfl) ⟨43115, by rfl⟩ : syracuseStep 229949 = 86231) (by norm_num)
theorem B230021 : Blo 99781 230021 := bbase (se 4 (by rfl) ⟨21564, by rfl⟩ : syracuseStep 230021 = 43129) (by norm_num)
theorem B230093 : Blo 99781 230093 := bbase (se 3 (by rfl) ⟨43142, by rfl⟩ : syracuseStep 230093 = 86285) (by norm_num)
theorem B230165 : Blo 99781 230165 := bbase (se 6 (by rfl) ⟨5394, by rfl⟩ : syracuseStep 230165 = 10789) (by norm_num)
theorem B230237 : Blo 99781 230237 := bbase (se 3 (by rfl) ⟨43169, by rfl⟩ : syracuseStep 230237 = 86339) (by norm_num)
theorem B230309 : Blo 99781 230309 := bbase (se 4 (by rfl) ⟨21591, by rfl⟩ : syracuseStep 230309 = 43183) (by norm_num)
theorem B230381 : Blo 99781 230381 := bbase (se 3 (by rfl) ⟨43196, by rfl⟩ : syracuseStep 230381 = 86393) (by norm_num)
theorem B230453 : Blo 99781 230453 := bbase (se 5 (by rfl) ⟨10802, by rfl⟩ : syracuseStep 230453 = 21605) (by norm_num)
theorem B525365 : Blo 99781 525365 := bbase (se 5 (by rfl) ⟨24626, by rfl⟩ : syracuseStep 525365 = 49253) (by norm_num)
theorem B230525 : Blo 99781 230525 := bbase (se 3 (by rfl) ⟨43223, by rfl⟩ : syracuseStep 230525 = 86447) (by norm_num)
theorem B230597 : Blo 99781 230597 := bbase (se 4 (by rfl) ⟨21618, by rfl⟩ : syracuseStep 230597 = 43237) (by norm_num)
theorem B230669 : Blo 99781 230669 := bbase (se 3 (by rfl) ⟨43250, by rfl⟩ : syracuseStep 230669 = 86501) (by norm_num)
theorem B427285 : Blo 99781 427285 := bbase (se 6 (by rfl) ⟨10014, by rfl⟩ : syracuseStep 427285 = 20029) (by norm_num)
theorem B427301 : Blo 99781 427301 := bbase (se 4 (by rfl) ⟨40059, by rfl⟩ : syracuseStep 427301 = 80119) (by norm_num)
theorem B656693 : Blo 99781 656693 := bbase (se 5 (by rfl) ⟨30782, by rfl⟩ : syracuseStep 656693 = 61565) (by norm_num)
theorem B230741 : Blo 99781 230741 := bbase (se 12 (by rfl) ⟨84, by rfl⟩ : syracuseStep 230741 = 169) (by norm_num)
theorem B296309 : Blo 99781 296309 := bbase (se 5 (by rfl) ⟨13889, by rfl⟩ : syracuseStep 296309 = 27779) (by norm_num)
theorem B230813 : Blo 99781 230813 := bbase (se 3 (by rfl) ⟨43277, by rfl⟩ : syracuseStep 230813 = 86555) (by norm_num)
theorem B230885 : Blo 99781 230885 := bbase (se 4 (by rfl) ⟨21645, by rfl⟩ : syracuseStep 230885 = 43291) (by norm_num)
theorem B230917 : Blo 99781 230917 := bbase (se 4 (by rfl) ⟨21648, by rfl⟩ : syracuseStep 230917 = 43297) (by norm_num)
theorem B230957 : Blo 99781 230957 := bbase (se 3 (by rfl) ⟨43304, by rfl⟩ : syracuseStep 230957 = 86609) (by norm_num)
theorem B231029 : Blo 99781 231029 := bbase (se 5 (by rfl) ⟨10829, by rfl⟩ : syracuseStep 231029 = 21659) (by norm_num)
theorem B231101 : Blo 99781 231101 := bbase (se 3 (by rfl) ⟨43331, by rfl⟩ : syracuseStep 231101 = 86663) (by norm_num)
theorem B231173 : Blo 99781 231173 := bbase (se 4 (by rfl) ⟨21672, by rfl⟩ : syracuseStep 231173 = 43345) (by norm_num)
theorem B231245 : Blo 99781 231245 := bbase (se 3 (by rfl) ⟨43358, by rfl⟩ : syracuseStep 231245 = 86717) (by norm_num)
theorem B132949 : Blo 99781 132949 := bbase (se 9 (by rfl) ⟨389, by rfl⟩ : syracuseStep 132949 = 779) (by norm_num)
theorem B231317 : Blo 99781 231317 := bbase (se 6 (by rfl) ⟨5421, by rfl⟩ : syracuseStep 231317 = 10843) (by norm_num)
theorem B755669 : Blo 99781 755669 := bbase (se 7 (by rfl) ⟨8855, by rfl⟩ : syracuseStep 755669 = 17711) (by norm_num)
theorem B165845 : Blo 99781 165845 := bbase (se 7 (by rfl) ⟨1943, by rfl⟩ : syracuseStep 165845 = 3887) (by norm_num)
theorem B231389 : Blo 99781 231389 := bbase (se 3 (by rfl) ⟨43385, by rfl⟩ : syracuseStep 231389 = 86771) (by norm_num)
theorem B231461 : Blo 99781 231461 := bbase (se 4 (by rfl) ⟨21699, by rfl⟩ : syracuseStep 231461 = 43399) (by norm_num)
theorem B165973 : Blo 99781 165973 := bbase (se 8 (by rfl) ⟨972, by rfl⟩ : syracuseStep 165973 = 1945) (by norm_num)
theorem B231533 : Blo 99781 231533 := bbase (se 3 (by rfl) ⟨43412, by rfl⟩ : syracuseStep 231533 = 86825) (by norm_num)
theorem B329845 : Blo 99781 329845 := bbase (se 5 (by rfl) ⟨15461, by rfl⟩ : syracuseStep 329845 = 30923) (by norm_num)
theorem B231605 : Blo 99781 231605 := bbase (se 5 (by rfl) ⟨10856, by rfl⟩ : syracuseStep 231605 = 21713) (by norm_num)
theorem B592085 : Blo 99781 592085 := bbase (se 7 (by rfl) ⟨6938, by rfl⟩ : syracuseStep 592085 = 13877) (by norm_num)
theorem B231677 : Blo 99781 231677 := bbase (se 3 (by rfl) ⟨43439, by rfl⟩ : syracuseStep 231677 = 86879) (by norm_num)
theorem B264485 : Blo 99781 264485 := bbase (se 4 (by rfl) ⟨24795, by rfl⟩ : syracuseStep 264485 = 49591) (by norm_num)
theorem B231749 : Blo 99781 231749 := bbase (se 4 (by rfl) ⟨21726, by rfl⟩ : syracuseStep 231749 = 43453) (by norm_num)
theorem B3705173 : Blo 99781 3705173 := bbase (se 10 (by rfl) ⟨5427, by rfl⟩ : syracuseStep 3705173 = 10855) (by norm_num)
theorem B231821 : Blo 99781 231821 := bbase (se 3 (by rfl) ⟨43466, by rfl⟩ : syracuseStep 231821 = 86933) (by norm_num)
theorem B231893 : Blo 99781 231893 := bbase (se 7 (by rfl) ⟨2717, by rfl⟩ : syracuseStep 231893 = 5435) (by norm_num)
theorem B231965 : Blo 99781 231965 := bbase (se 3 (by rfl) ⟨43493, by rfl⟩ : syracuseStep 231965 = 86987) (by norm_num)
theorem B232037 : Blo 99781 232037 := bbase (se 4 (by rfl) ⟨21753, by rfl⟩ : syracuseStep 232037 = 43507) (by norm_num)
theorem B232109 : Blo 99781 232109 := bbase (se 3 (by rfl) ⟨43520, by rfl⟩ : syracuseStep 232109 = 87041) (by norm_num)
theorem B199349 : Blo 99781 199349 := bbase (se 5 (by rfl) ⟨9344, by rfl⟩ : syracuseStep 199349 = 18689) (by norm_num)
theorem B428773 : Blo 99781 428773 := bbase (se 4 (by rfl) ⟨40197, by rfl⟩ : syracuseStep 428773 = 80395) (by norm_num)
theorem B428789 : Blo 99781 428789 := bbase (se 5 (by rfl) ⟨20099, by rfl⟩ : syracuseStep 428789 = 40199) (by norm_num)
theorem B232181 : Blo 99781 232181 := bbase (se 5 (by rfl) ⟨10883, by rfl⟩ : syracuseStep 232181 = 21767) (by norm_num)
theorem B232253 : Blo 99781 232253 := bbase (se 3 (by rfl) ⟨43547, by rfl⟩ : syracuseStep 232253 = 87095) (by norm_num)
theorem B265037 : Blo 99781 265037 := bbase (se 3 (by rfl) ⟨49694, by rfl⟩ : syracuseStep 265037 = 99389) (by norm_num)
theorem B232325 : Blo 99781 232325 := bbase (se 4 (by rfl) ⟨21780, by rfl⟩ : syracuseStep 232325 = 43561) (by norm_num)
theorem B101297 : Blo 99781 101297 := bbase (se 2 (by rfl) ⟨37986, by rfl⟩ : syracuseStep 101297 = 75973) (by norm_num)
theorem B232397 : Blo 99781 232397 := bbase (se 3 (by rfl) ⟨43574, by rfl⟩ : syracuseStep 232397 = 87149) (by norm_num)
theorem B232469 : Blo 99781 232469 := bbase (se 6 (by rfl) ⟨5448, by rfl⟩ : syracuseStep 232469 = 10897) (by norm_num)
theorem B232541 : Blo 99781 232541 := bbase (se 3 (by rfl) ⟨43601, by rfl⟩ : syracuseStep 232541 = 87203) (by norm_num)
theorem B494741 : Blo 99781 494741 := bbase (se 6 (by rfl) ⟨11595, by rfl⟩ : syracuseStep 494741 = 23191) (by norm_num)
theorem B232613 : Blo 99781 232613 := bbase (se 4 (by rfl) ⟨21807, by rfl⟩ : syracuseStep 232613 = 43615) (by norm_num)
theorem B232685 : Blo 99781 232685 := bbase (se 3 (by rfl) ⟨43628, by rfl⟩ : syracuseStep 232685 = 87257) (by norm_num)
theorem B101633 : Blo 99781 101633 := bbase (se 2 (by rfl) ⟨38112, by rfl⟩ : syracuseStep 101633 = 76225) (by norm_num)
theorem B593173 : Blo 99781 593173 := bbase (se 6 (by rfl) ⟨13902, by rfl⟩ : syracuseStep 593173 = 27805) (by norm_num)
theorem B232757 : Blo 99781 232757 := bbase (se 5 (by rfl) ⟨10910, by rfl⟩ : syracuseStep 232757 = 21821) (by norm_num)
theorem B232829 : Blo 99781 232829 := bbase (se 3 (by rfl) ⟨43655, by rfl⟩ : syracuseStep 232829 = 87311) (by norm_num)
theorem B494981 : Blo 99781 494981 := bbase (se 4 (by rfl) ⟨46404, by rfl⟩ : syracuseStep 494981 = 92809) (by norm_num)
theorem B232901 : Blo 99781 232901 := bbase (se 4 (by rfl) ⟨21834, by rfl⟩ : syracuseStep 232901 = 43669) (by norm_num)
theorem B232973 : Blo 99781 232973 := bbase (se 3 (by rfl) ⟨43682, by rfl⟩ : syracuseStep 232973 = 87365) (by norm_num)
theorem B364085 : Blo 99781 364085 := bbase (se 5 (by rfl) ⟨17066, by rfl⟩ : syracuseStep 364085 = 34133) (by norm_num)
theorem B724565 : Blo 99781 724565 := bbase (se 8 (by rfl) ⟨4245, by rfl⟩ : syracuseStep 724565 = 8491) (by norm_num)
theorem B233045 : Blo 99781 233045 := bbase (se 8 (by rfl) ⟨1365, by rfl⟩ : syracuseStep 233045 = 2731) (by norm_num)
theorem B233117 : Blo 99781 233117 := bbase (se 3 (by rfl) ⟨43709, by rfl⟩ : syracuseStep 233117 = 87419) (by norm_num)
theorem B364213 : Blo 99781 364213 := bbase (se 5 (by rfl) ⟨17072, by rfl⟩ : syracuseStep 364213 = 34145) (by norm_num)
theorem B233189 : Blo 99781 233189 := bbase (se 4 (by rfl) ⟨21861, by rfl⟩ : syracuseStep 233189 = 43723) (by norm_num)
theorem B233261 : Blo 99781 233261 := bbase (se 3 (by rfl) ⟨43736, by rfl⟩ : syracuseStep 233261 = 87473) (by norm_num)
theorem B102217 : Blo 99781 102217 := bbase (se 2 (by rfl) ⟨38331, by rfl⟩ : syracuseStep 102217 = 76663) (by norm_num)
theorem B560981 : Blo 99781 560981 := bbase (se 9 (by rfl) ⟨1643, by rfl⟩ : syracuseStep 560981 = 3287) (by norm_num)
theorem B233333 : Blo 99781 233333 := bbase (se 5 (by rfl) ⟨10937, by rfl⟩ : syracuseStep 233333 = 21875) (by norm_num)
theorem B233405 : Blo 99781 233405 := bbase (se 3 (by rfl) ⟨43763, by rfl⟩ : syracuseStep 233405 = 87527) (by norm_num)
theorem B233477 : Blo 99781 233477 := bbase (se 4 (by rfl) ⟨21888, by rfl⟩ : syracuseStep 233477 = 43777) (by norm_num)
theorem B102565 : Blo 99781 102565 := bbase (se 4 (by rfl) ⟨9615, by rfl⟩ : syracuseStep 102565 = 19231) (by norm_num)
theorem B1118549 : Blo 99781 1118549 := bbase (se 10 (by rfl) ⟨1638, by rfl⟩ : syracuseStep 1118549 = 3277) (by norm_num)
theorem B168293 : Blo 99781 168293 := bbase (se 4 (by rfl) ⟨15777, by rfl⟩ : syracuseStep 168293 = 31555) (by norm_num)
theorem B102889 : Blo 99781 102889 := bbase (se 2 (by rfl) ⟨38583, by rfl⟩ : syracuseStep 102889 = 77167) (by norm_num)
theorem B168493 : Blo 99781 168493 := bbase (se 3 (by rfl) ⟨31592, by rfl⟩ : syracuseStep 168493 = 63185) (by norm_num)
theorem B168533 : Blo 99781 168533 := bbase (se 8 (by rfl) ⟨987, by rfl⟩ : syracuseStep 168533 = 1975) (by norm_num)
theorem B168581 : Blo 99781 168581 := bbase (se 4 (by rfl) ⟨15804, by rfl⟩ : syracuseStep 168581 = 31609) (by norm_num)
theorem B856757 : Blo 99781 856757 := bbase (se 5 (by rfl) ⟨40160, by rfl⟩ : syracuseStep 856757 = 80321) (by norm_num)
theorem B824021 : Blo 99781 824021 := bbase (se 7 (by rfl) ⟨9656, by rfl⟩ : syracuseStep 824021 = 19313) (by norm_num)
theorem B168709 : Blo 99781 168709 := bbase (se 4 (by rfl) ⟨15816, by rfl⟩ : syracuseStep 168709 = 31633) (by norm_num)
theorem B168797 : Blo 99781 168797 := bbase (se 3 (by rfl) ⟨31649, by rfl⟩ : syracuseStep 168797 = 63299) (by norm_num)
theorem B758645 : Blo 99781 758645 := bbase (se 5 (by rfl) ⟨35561, by rfl⟩ : syracuseStep 758645 = 71123) (by norm_num)
theorem B431045 : Blo 99781 431045 := bbase (se 4 (by rfl) ⟨40410, by rfl⟩ : syracuseStep 431045 = 80821) (by norm_num)
theorem B168925 : Blo 99781 168925 := bbase (se 3 (by rfl) ⟨31673, by rfl⟩ : syracuseStep 168925 = 63347) (by norm_num)
theorem B103393 : Blo 99781 103393 := bbase (se 2 (by rfl) ⟨38772, by rfl⟩ : syracuseStep 103393 = 77545) (by norm_num)
theorem B169013 : Blo 99781 169013 := bbase (se 5 (by rfl) ⟨7922, by rfl⟩ : syracuseStep 169013 = 15845) (by norm_num)
theorem B169141 : Blo 99781 169141 := bbase (se 5 (by rfl) ⟨7928, by rfl⟩ : syracuseStep 169141 = 15857) (by norm_num)
theorem B169229 : Blo 99781 169229 := bbase (se 3 (by rfl) ⟨31730, by rfl⟩ : syracuseStep 169229 = 63461) (by norm_num)
theorem B169357 : Blo 99781 169357 := bbase (se 3 (by rfl) ⟨31754, by rfl⟩ : syracuseStep 169357 = 63509) (by norm_num)
theorem B169445 : Blo 99781 169445 := bbase (se 4 (by rfl) ⟨15885, by rfl⟩ : syracuseStep 169445 = 31771) (by norm_num)
theorem B136765 : Blo 99781 136765 := bbase (se 3 (by rfl) ⟨25643, by rfl⟩ : syracuseStep 136765 = 51287) (by norm_num)
theorem B104009 : Blo 99781 104009 := bbase (se 2 (by rfl) ⟨39003, by rfl⟩ : syracuseStep 104009 = 78007) (by norm_num)
theorem B169573 : Blo 99781 169573 := bbase (se 4 (by rfl) ⟨15897, by rfl⟩ : syracuseStep 169573 = 31795) (by norm_num)
theorem B104041 : Blo 99781 104041 := bbase (se 2 (by rfl) ⟨39015, by rfl⟩ : syracuseStep 104041 = 78031) (by norm_num)
theorem B202405 : Blo 99781 202405 := bbase (se 4 (by rfl) ⟨18975, by rfl⟩ : syracuseStep 202405 = 37951) (by norm_num)
theorem B169661 : Blo 99781 169661 := bbase (se 3 (by rfl) ⟨31811, by rfl⟩ : syracuseStep 169661 = 63623) (by norm_num)
theorem B366277 : Blo 99781 366277 := bbase (se 4 (by rfl) ⟨34338, by rfl⟩ : syracuseStep 366277 = 68677) (by norm_num)
theorem B169789 : Blo 99781 169789 := bbase (se 3 (by rfl) ⟨31835, by rfl⟩ : syracuseStep 169789 = 63671) (by norm_num)
theorem B169877 : Blo 99781 169877 := bbase (se 6 (by rfl) ⟨3981, by rfl⟩ : syracuseStep 169877 = 7963) (by norm_num)
theorem B104425 : Blo 99781 104425 := bbase (se 2 (by rfl) ⟨39159, by rfl⟩ : syracuseStep 104425 = 78319) (by norm_num)
theorem B170005 : Blo 99781 170005 := bbase (se 6 (by rfl) ⟨3984, by rfl⟩ : syracuseStep 170005 = 7969) (by norm_num)
theorem B497765 : Blo 99781 497765 := bbase (se 4 (by rfl) ⟨46665, by rfl⟩ : syracuseStep 497765 = 93331) (by norm_num)
theorem B170093 : Blo 99781 170093 := bbase (se 3 (by rfl) ⟨31892, by rfl⟩ : syracuseStep 170093 = 63785) (by norm_num)
theorem B104609 : Blo 99781 104609 := bbase (se 2 (by rfl) ⟨39228, by rfl⟩ : syracuseStep 104609 = 78457) (by norm_num)
theorem B170221 : Blo 99781 170221 := bbase (se 3 (by rfl) ⟨31916, by rfl⟩ : syracuseStep 170221 = 63833) (by norm_num)
theorem B170309 : Blo 99781 170309 := bbase (se 4 (by rfl) ⟨15966, by rfl⟩ : syracuseStep 170309 = 31933) (by norm_num)
theorem B170437 : Blo 99781 170437 := bbase (se 4 (by rfl) ⟨15978, by rfl⟩ : syracuseStep 170437 = 31957) (by norm_num)
theorem B104941 : Blo 99781 104941 := bbase (se 3 (by rfl) ⟨19676, by rfl⟩ : syracuseStep 104941 = 39353) (by norm_num)
theorem B104965 : Blo 99781 104965 := bbase (se 4 (by rfl) ⟨9840, by rfl⟩ : syracuseStep 104965 = 19681) (by norm_num)
theorem B170525 : Blo 99781 170525 := bbase (se 3 (by rfl) ⟨31973, by rfl⟩ : syracuseStep 170525 = 63947) (by norm_num)
theorem B530981 : Blo 99781 530981 := bbase (se 4 (by rfl) ⟨49779, by rfl⟩ : syracuseStep 530981 = 99559) (by norm_num)
theorem B498325 : Blo 99781 498325 := bbase (se 6 (by rfl) ⟨11679, by rfl⟩ : syracuseStep 498325 = 23359) (by norm_num)
theorem B170653 : Blo 99781 170653 := bbase (se 3 (by rfl) ⟨31997, by rfl⟩ : syracuseStep 170653 = 63995) (by norm_num)
theorem B3185365 : Blo 99781 3185365 := bbase (se 7 (by rfl) ⟨37328, by rfl⟩ : syracuseStep 3185365 = 74657) (by norm_num)
theorem B170741 : Blo 99781 170741 := bbase (se 5 (by rfl) ⟨8003, by rfl⟩ : syracuseStep 170741 = 16007) (by norm_num)
theorem B138029 : Blo 99781 138029 := bbase (se 3 (by rfl) ⟨25880, by rfl⟩ : syracuseStep 138029 = 51761) (by norm_num)
theorem B170869 : Blo 99781 170869 := bbase (se 5 (by rfl) ⟨8009, by rfl⟩ : syracuseStep 170869 = 16019) (by norm_num)
theorem B170957 : Blo 99781 170957 := bbase (se 3 (by rfl) ⟨32054, by rfl⟩ : syracuseStep 170957 = 64109) (by norm_num)
theorem B171085 : Blo 99781 171085 := bbase (se 3 (by rfl) ⟨32078, by rfl⟩ : syracuseStep 171085 = 64157) (by norm_num)
theorem B236629 : Blo 99781 236629 := bbase (se 8 (by rfl) ⟨1386, by rfl⟩ : syracuseStep 236629 = 2773) (by norm_num)
theorem B171173 : Blo 99781 171173 := bbase (se 4 (by rfl) ⟨16047, by rfl⟩ : syracuseStep 171173 = 32095) (by norm_num)
theorem B695573 : Blo 99781 695573 := bbase (se 6 (by rfl) ⟨16302, by rfl⟩ : syracuseStep 695573 = 32605) (by norm_num)
theorem B171301 : Blo 99781 171301 := bbase (se 4 (by rfl) ⟨16059, by rfl⟩ : syracuseStep 171301 = 32119) (by norm_num)
theorem B171389 : Blo 99781 171389 := bbase (se 3 (by rfl) ⟨32135, by rfl⟩ : syracuseStep 171389 = 64271) (by norm_num)
theorem B171517 : Blo 99781 171517 := bbase (se 3 (by rfl) ⟨32159, by rfl⟩ : syracuseStep 171517 = 64319) (by norm_num)
theorem B138781 : Blo 99781 138781 := bbase (se 3 (by rfl) ⟨26021, by rfl⟩ : syracuseStep 138781 = 52043) (by norm_num)
theorem B859733 : Blo 99781 859733 := bbase (se 8 (by rfl) ⟨5037, by rfl⟩ : syracuseStep 859733 = 10075) (by norm_num)
theorem B171605 : Blo 99781 171605 := bbase (se 8 (by rfl) ⟨1005, by rfl⟩ : syracuseStep 171605 = 2011) (by norm_num)
theorem B171733 : Blo 99781 171733 := bbase (se 7 (by rfl) ⟨2012, by rfl⟩ : syracuseStep 171733 = 4025) (by norm_num)
theorem B171821 : Blo 99781 171821 := bbase (se 3 (by rfl) ⟨32216, by rfl⟩ : syracuseStep 171821 = 64433) (by norm_num)
theorem B204709 : Blo 99781 204709 := bbase (se 4 (by rfl) ⟨19191, by rfl⟩ : syracuseStep 204709 = 38383) (by norm_num)
theorem B171949 : Blo 99781 171949 := bbase (se 3 (by rfl) ⟨32240, by rfl⟩ : syracuseStep 171949 = 64481) (by norm_num)
theorem B172037 : Blo 99781 172037 := bbase (se 4 (by rfl) ⟨16128, by rfl⟩ : syracuseStep 172037 = 32257) (by norm_num)
theorem B172165 : Blo 99781 172165 := bbase (se 4 (by rfl) ⟨16140, by rfl⟩ : syracuseStep 172165 = 32281) (by norm_num)
theorem B172253 : Blo 99781 172253 := bbase (se 3 (by rfl) ⟨32297, by rfl⟩ : syracuseStep 172253 = 64595) (by norm_num)
theorem B172381 : Blo 99781 172381 := bbase (se 3 (by rfl) ⟨32321, by rfl⟩ : syracuseStep 172381 = 64643) (by norm_num)
theorem B237917 : Blo 99781 237917 := bbase (se 3 (by rfl) ⟨44609, by rfl⟩ : syracuseStep 237917 = 89219) (by norm_num)
theorem B205229 : Blo 99781 205229 := bbase (se 3 (by rfl) ⟨38480, by rfl⟩ : syracuseStep 205229 = 76961) (by norm_num)
theorem B172469 : Blo 99781 172469 := bbase (se 5 (by rfl) ⟨8084, by rfl⟩ : syracuseStep 172469 = 16169) (by norm_num)
theorem B369173 : Blo 99781 369173 := bbase (se 6 (by rfl) ⟨8652, by rfl⟩ : syracuseStep 369173 = 17305) (by norm_num)
theorem B172597 : Blo 99781 172597 := bbase (se 5 (by rfl) ⟨8090, by rfl⟩ : syracuseStep 172597 = 16181) (by norm_num)
theorem B107129 : Blo 99781 107129 := bbase (se 2 (by rfl) ⟨40173, by rfl⟩ : syracuseStep 107129 = 80347) (by norm_num)
theorem B172685 : Blo 99781 172685 := bbase (se 3 (by rfl) ⟨32378, by rfl⟩ : syracuseStep 172685 = 64757) (by norm_num)
theorem B172813 : Blo 99781 172813 := bbase (se 3 (by rfl) ⟨32402, by rfl⟩ : syracuseStep 172813 = 64805) (by norm_num)
theorem B140077 : Blo 99781 140077 := bbase (se 3 (by rfl) ⟨26264, by rfl⟩ : syracuseStep 140077 = 52529) (by norm_num)
theorem B303925 : Blo 99781 303925 := bbase (se 5 (by rfl) ⟨14246, by rfl⟩ : syracuseStep 303925 = 28493) (by norm_num)
theorem B369461 : Blo 99781 369461 := bbase (se 5 (by rfl) ⟨17318, by rfl⟩ : syracuseStep 369461 = 34637) (by norm_num)
theorem B172901 : Blo 99781 172901 := bbase (se 4 (by rfl) ⟨16209, by rfl⟩ : syracuseStep 172901 = 32419) (by norm_num)
theorem B435077 : Blo 99781 435077 := bbase (se 4 (by rfl) ⟨40788, by rfl⟩ : syracuseStep 435077 = 81577) (by norm_num)
theorem B173029 : Blo 99781 173029 := bbase (se 4 (by rfl) ⟨16221, by rfl⟩ : syracuseStep 173029 = 32443) (by norm_num)
theorem B926741 : Blo 99781 926741 := bbase (se 6 (by rfl) ⟨21720, by rfl⟩ : syracuseStep 926741 = 43441) (by norm_num)
theorem B205861 : Blo 99781 205861 := bbase (se 4 (by rfl) ⟨19299, by rfl⟩ : syracuseStep 205861 = 38599) (by norm_num)
theorem B107573 : Blo 99781 107573 := bbase (se 5 (by rfl) ⟨5042, by rfl⟩ : syracuseStep 107573 = 10085) (by norm_num)
theorem B173117 : Blo 99781 173117 := bbase (se 3 (by rfl) ⟨32459, by rfl⟩ : syracuseStep 173117 = 64919) (by norm_num)
theorem B337013 : Blo 99781 337013 := bbase (se 5 (by rfl) ⟨15797, by rfl⟩ : syracuseStep 337013 = 31595) (by norm_num)
theorem B173245 : Blo 99781 173245 := bbase (se 3 (by rfl) ⟨32483, by rfl⟩ : syracuseStep 173245 = 64967) (by norm_num)
theorem B173333 : Blo 99781 173333 := bbase (se 6 (by rfl) ⟨4062, by rfl⟩ : syracuseStep 173333 = 8125) (by norm_num)
theorem B992533 : Blo 99781 992533 := bbase (se 6 (by rfl) ⟨23262, by rfl⟩ : syracuseStep 992533 = 46525) (by norm_num)
theorem B107821 : Blo 99781 107821 := bbase (se 3 (by rfl) ⟨20216, by rfl⟩ : syracuseStep 107821 = 40433) (by norm_num)
theorem B173461 : Blo 99781 173461 := bbase (se 6 (by rfl) ⟨4065, by rfl⟩ : syracuseStep 173461 = 8131) (by norm_num)
theorem B173549 : Blo 99781 173549 := bbase (se 3 (by rfl) ⟨32540, by rfl⟩ : syracuseStep 173549 = 65081) (by norm_num)
theorem B337445 : Blo 99781 337445 := bbase (se 4 (by rfl) ⟨31635, by rfl⟩ : syracuseStep 337445 = 63271) (by norm_num)
theorem B173677 : Blo 99781 173677 := bbase (se 3 (by rfl) ⟨32564, by rfl⟩ : syracuseStep 173677 = 65129) (by norm_num)
theorem B206525 : Blo 99781 206525 := bbase (se 3 (by rfl) ⟨38723, by rfl⟩ : syracuseStep 206525 = 77447) (by norm_num)
theorem B173765 : Blo 99781 173765 := bbase (se 4 (by rfl) ⟨16290, by rfl⟩ : syracuseStep 173765 = 32581) (by norm_num)
theorem B108253 : Blo 99781 108253 := bbase (se 3 (by rfl) ⟨20297, by rfl⟩ : syracuseStep 108253 = 40595) (by norm_num)
theorem B108325 : Blo 99781 108325 := bbase (se 4 (by rfl) ⟨10155, by rfl⟩ : syracuseStep 108325 = 20311) (by norm_num)
theorem B173893 : Blo 99781 173893 := bbase (se 4 (by rfl) ⟨16302, by rfl⟩ : syracuseStep 173893 = 32605) (by norm_num)
theorem B173981 : Blo 99781 173981 := bbase (se 3 (by rfl) ⟨32621, by rfl⟩ : syracuseStep 173981 = 65243) (by norm_num)
theorem B337877 : Blo 99781 337877 := bbase (se 7 (by rfl) ⟨3959, by rfl⟩ : syracuseStep 337877 = 7919) (by norm_num)
theorem B174109 : Blo 99781 174109 := bbase (se 3 (by rfl) ⟨32645, by rfl⟩ : syracuseStep 174109 = 65291) (by norm_num)
theorem B174197 : Blo 99781 174197 := bbase (se 5 (by rfl) ⟨8165, by rfl⟩ : syracuseStep 174197 = 16331) (by norm_num)
theorem B108697 : Blo 99781 108697 := bbase (se 2 (by rfl) ⟨40761, by rfl⟩ : syracuseStep 108697 = 81523) (by norm_num)
theorem B239773 : Blo 99781 239773 := bbase (se 3 (by rfl) ⟨44957, by rfl⟩ : syracuseStep 239773 = 89915) (by norm_num)
theorem B207029 : Blo 99781 207029 := bbase (se 5 (by rfl) ⟨9704, by rfl⟩ : syracuseStep 207029 = 19409) (by norm_num)
theorem B174325 : Blo 99781 174325 := bbase (se 5 (by rfl) ⟨8171, by rfl⟩ : syracuseStep 174325 = 16343) (by norm_num)
theorem B174413 : Blo 99781 174413 := bbase (se 3 (by rfl) ⟨32702, by rfl⟩ : syracuseStep 174413 = 65405) (by norm_num)
theorem B338309 : Blo 99781 338309 := bbase (se 4 (by rfl) ⟨31716, by rfl⟩ : syracuseStep 338309 = 63433) (by norm_num)
theorem B108973 : Blo 99781 108973 := bbase (se 3 (by rfl) ⟨20432, by rfl⟩ : syracuseStep 108973 = 40865) (by norm_num)
theorem B174541 : Blo 99781 174541 := bbase (se 3 (by rfl) ⟨32726, by rfl⟩ : syracuseStep 174541 = 65453) (by norm_num)
theorem B109073 : Blo 99781 109073 := bbase (se 2 (by rfl) ⟨40902, by rfl⟩ : syracuseStep 109073 = 81805) (by norm_num)
theorem B174629 : Blo 99781 174629 := bbase (se 4 (by rfl) ⟨16371, by rfl⟩ : syracuseStep 174629 = 32743) (by norm_num)
theorem B109145 : Blo 99781 109145 := bbase (se 2 (by rfl) ⟨40929, by rfl⟩ : syracuseStep 109145 = 81859) (by norm_num)
theorem B436853 : Blo 99781 436853 := bbase (se 5 (by rfl) ⟨20477, by rfl⟩ : syracuseStep 436853 = 40955) (by norm_num)
theorem B174757 : Blo 99781 174757 := bbase (se 4 (by rfl) ⟨16383, by rfl⟩ : syracuseStep 174757 = 32767) (by norm_num)
theorem B731861 : Blo 99781 731861 := bbase (se 7 (by rfl) ⟨8576, by rfl⟩ : syracuseStep 731861 = 17153) (by norm_num)
theorem B174845 : Blo 99781 174845 := bbase (se 3 (by rfl) ⟨32783, by rfl⟩ : syracuseStep 174845 = 65567) (by norm_num)
theorem B109333 : Blo 99781 109333 := bbase (se 6 (by rfl) ⟨2562, by rfl⟩ : syracuseStep 109333 = 5125) (by norm_num)
theorem B338741 : Blo 99781 338741 := bbase (se 5 (by rfl) ⟨15878, by rfl⟩ : syracuseStep 338741 = 31757) (by norm_num)
theorem B240445 : Blo 99781 240445 := bbase (se 3 (by rfl) ⟨45083, by rfl⟩ : syracuseStep 240445 = 90167) (by norm_num)
theorem B273269 : Blo 99781 273269 := bbase (se 5 (by rfl) ⟨12809, by rfl⟩ : syracuseStep 273269 = 25619) (by norm_num)
theorem B174973 : Blo 99781 174973 := bbase (se 3 (by rfl) ⟨32807, by rfl⟩ : syracuseStep 174973 = 65615) (by norm_num)
theorem B109517 : Blo 99781 109517 := bbase (se 3 (by rfl) ⟨20534, by rfl⟩ : syracuseStep 109517 = 41069) (by norm_num)
theorem B175061 : Blo 99781 175061 := bbase (se 7 (by rfl) ⟨2051, by rfl⟩ : syracuseStep 175061 = 4103) (by norm_num)
theorem B240677 : Blo 99781 240677 := bbase (se 4 (by rfl) ⟨22563, by rfl⟩ : syracuseStep 240677 = 45127) (by norm_num)
theorem B240725 : Blo 99781 240725 := bbase (se 8 (by rfl) ⟨1410, by rfl⟩ : syracuseStep 240725 = 2821) (by norm_num)
theorem B208013 : Blo 99781 208013 := bbase (se 3 (by rfl) ⟨39002, by rfl⟩ : syracuseStep 208013 = 78005) (by norm_num)
theorem B109717 : Blo 99781 109717 := bbase (se 6 (by rfl) ⟨2571, by rfl⟩ : syracuseStep 109717 = 5143) (by norm_num)
theorem B109765 : Blo 99781 109765 := bbase (se 4 (by rfl) ⟨10290, by rfl⟩ : syracuseStep 109765 = 20581) (by norm_num)
theorem B142565 : Blo 99781 142565 := bbase (se 4 (by rfl) ⟨13365, by rfl⟩ : syracuseStep 142565 = 26731) (by norm_num)
theorem B339173 : Blo 99781 339173 := bbase (se 4 (by rfl) ⟨31797, by rfl⟩ : syracuseStep 339173 = 63595) (by norm_num)
theorem B208261 : Blo 99781 208261 := bbase (se 4 (by rfl) ⟨19524, by rfl⟩ : syracuseStep 208261 = 39049) (by norm_num)
theorem B437845 : Blo 99781 437845 := bbase (se 8 (by rfl) ⟨2565, by rfl⟩ : syracuseStep 437845 = 5131) (by norm_num)
theorem B339605 : Blo 99781 339605 := bbase (se 6 (by rfl) ⟨7959, by rfl⟩ : syracuseStep 339605 = 15919) (by norm_num)
theorem B110269 : Blo 99781 110269 := bbase (se 3 (by rfl) ⟨20675, by rfl⟩ : syracuseStep 110269 = 41351) (by norm_num)
theorem B110341 : Blo 99781 110341 := bbase (se 4 (by rfl) ⟨10344, by rfl⟩ : syracuseStep 110341 = 20689) (by norm_num)
theorem B110521 : Blo 99781 110521 := bbase (se 2 (by rfl) ⟨41445, by rfl⟩ : syracuseStep 110521 = 82891) (by norm_num)
theorem B405445 : Blo 99781 405445 := bbase (se 4 (by rfl) ⟨38010, by rfl⟩ : syracuseStep 405445 = 76021) (by norm_num)
theorem B143317 : Blo 99781 143317 := bbase (se 7 (by rfl) ⟨1679, by rfl⟩ : syracuseStep 143317 = 3359) (by norm_num)
theorem B340037 : Blo 99781 340037 := bbase (se 4 (by rfl) ⟨31878, by rfl⟩ : syracuseStep 340037 = 63757) (by norm_num)
theorem B242117 : Blo 99781 242117 := bbase (se 4 (by rfl) ⟨22698, by rfl⟩ : syracuseStep 242117 = 45397) (by norm_num)
theorem B766421 : Blo 99781 766421 := bbase (se 7 (by rfl) ⟨8981, by rfl⟩ : syracuseStep 766421 = 17963) (by norm_num)
theorem B176597 : Blo 99781 176597 := bbase (se 7 (by rfl) ⟨2069, by rfl⟩ : syracuseStep 176597 = 4139) (by norm_num)
theorem B340469 : Blo 99781 340469 := bbase (se 5 (by rfl) ⟨15959, by rfl⟩ : syracuseStep 340469 = 31919) (by norm_num)
theorem B242309 : Blo 99781 242309 := bbase (se 4 (by rfl) ⟨22716, by rfl⟩ : syracuseStep 242309 = 45433) (by norm_num)
theorem B144109 : Blo 99781 144109 := bbase (se 3 (by rfl) ⟨27020, by rfl⟩ : syracuseStep 144109 = 54041) (by norm_num)
theorem B340901 : Blo 99781 340901 := bbase (se 4 (by rfl) ⟨31959, by rfl⟩ : syracuseStep 340901 = 63919) (by norm_num)
theorem B144445 : Blo 99781 144445 := bbase (se 3 (by rfl) ⟨27083, by rfl⟩ : syracuseStep 144445 = 54167) (by norm_num)
theorem B504917 : Blo 99781 504917 := bbase (se 8 (by rfl) ⟨2958, by rfl⟩ : syracuseStep 504917 = 5917) (by norm_num)
theorem B177349 : Blo 99781 177349 := bbase (se 4 (by rfl) ⟨16626, by rfl⟩ : syracuseStep 177349 = 33253) (by norm_num)
theorem B210157 : Blo 99781 210157 := bbase (se 3 (by rfl) ⟨39404, by rfl⟩ : syracuseStep 210157 = 78809) (by norm_num)
theorem B144661 : Blo 99781 144661 := bbase (se 6 (by rfl) ⟨3390, by rfl⟩ : syracuseStep 144661 = 6781) (by norm_num)
theorem B341333 : Blo 99781 341333 := bbase (se 13 (by rfl) ⟨62, by rfl⟩ : syracuseStep 341333 = 125) (by norm_num)
theorem B996725 : Blo 99781 996725 := bbase (se 5 (by rfl) ⟨46721, by rfl⟩ : syracuseStep 996725 = 93443) (by norm_num)
theorem B112261 : Blo 99781 112261 := bbase (se 4 (by rfl) ⟨10524, by rfl⟩ : syracuseStep 112261 = 21049) (by norm_num)
theorem B145037 : Blo 99781 145037 := bbase (se 3 (by rfl) ⟨27194, by rfl⟩ : syracuseStep 145037 = 54389) (by norm_num)
theorem B112297 : Blo 99781 112297 := bbase (se 2 (by rfl) ⟨42111, by rfl⟩ : syracuseStep 112297 = 84223) (by norm_num)
theorem B112333 : Blo 99781 112333 := bbase (se 3 (by rfl) ⟨21062, by rfl⟩ : syracuseStep 112333 = 42125) (by norm_num)
theorem B112369 : Blo 99781 112369 := bbase (se 2 (by rfl) ⟨42138, by rfl⟩ : syracuseStep 112369 = 84277) (by norm_num)
theorem B341765 : Blo 99781 341765 := bbase (se 4 (by rfl) ⟨32040, by rfl⟩ : syracuseStep 341765 = 64081) (by norm_num)
theorem B112405 : Blo 99781 112405 := bbase (se 6 (by rfl) ⟨2634, by rfl⟩ : syracuseStep 112405 = 5269) (by norm_num)
theorem B112441 : Blo 99781 112441 := bbase (se 2 (by rfl) ⟨42165, by rfl⟩ : syracuseStep 112441 = 84331) (by norm_num)
theorem B112477 : Blo 99781 112477 := bbase (se 3 (by rfl) ⟨21089, by rfl⟩ : syracuseStep 112477 = 42179) (by norm_num)
theorem B112513 : Blo 99781 112513 := bbase (se 2 (by rfl) ⟨42192, by rfl⟩ : syracuseStep 112513 = 84385) (by norm_num)
theorem B145309 : Blo 99781 145309 := bbase (se 3 (by rfl) ⟨27245, by rfl⟩ : syracuseStep 145309 = 54491) (by norm_num)
theorem B112549 : Blo 99781 112549 := bbase (se 4 (by rfl) ⟨10551, by rfl⟩ : syracuseStep 112549 = 21103) (by norm_num)
theorem B112585 : Blo 99781 112585 := bbase (se 2 (by rfl) ⟨42219, by rfl⟩ : syracuseStep 112585 = 84439) (by norm_num)
theorem B112621 : Blo 99781 112621 := bbase (se 3 (by rfl) ⟨21116, by rfl⟩ : syracuseStep 112621 = 42233) (by norm_num)
theorem B112657 : Blo 99781 112657 := bbase (se 2 (by rfl) ⟨42246, by rfl⟩ : syracuseStep 112657 = 84493) (by norm_num)
theorem B112693 : Blo 99781 112693 := bbase (se 5 (by rfl) ⟨5282, by rfl⟩ : syracuseStep 112693 = 10565) (by norm_num)
theorem B571445 : Blo 99781 571445 := bbase (se 5 (by rfl) ⟨26786, by rfl⟩ : syracuseStep 571445 = 53573) (by norm_num)
theorem B505925 : Blo 99781 505925 := bbase (se 4 (by rfl) ⟨47430, by rfl⟩ : syracuseStep 505925 = 94861) (by norm_num)
theorem B112729 : Blo 99781 112729 := bbase (se 2 (by rfl) ⟨42273, by rfl⟩ : syracuseStep 112729 = 84547) (by norm_num)
theorem B112765 : Blo 99781 112765 := bbase (se 3 (by rfl) ⟨21143, by rfl⟩ : syracuseStep 112765 = 42287) (by norm_num)
theorem B112801 : Blo 99781 112801 := bbase (se 2 (by rfl) ⟨42300, by rfl⟩ : syracuseStep 112801 = 84601) (by norm_num)
theorem B342197 : Blo 99781 342197 := bbase (se 5 (by rfl) ⟨16040, by rfl⟩ : syracuseStep 342197 = 32081) (by norm_num)
theorem B112837 : Blo 99781 112837 := bbase (se 4 (by rfl) ⟨10578, by rfl⟩ : syracuseStep 112837 = 21157) (by norm_num)
theorem B112873 : Blo 99781 112873 := bbase (se 2 (by rfl) ⟨42327, by rfl⟩ : syracuseStep 112873 = 84655) (by norm_num)
theorem B669941 : Blo 99781 669941 := bbase (se 5 (by rfl) ⟨31403, by rfl⟩ : syracuseStep 669941 = 62807) (by norm_num)
theorem B112909 : Blo 99781 112909 := bbase (se 3 (by rfl) ⟨21170, by rfl⟩ : syracuseStep 112909 = 42341) (by norm_num)
theorem B112945 : Blo 99781 112945 := bbase (se 2 (by rfl) ⟨42354, by rfl⟩ : syracuseStep 112945 = 84709) (by norm_num)
theorem B112981 : Blo 99781 112981 := bbase (se 10 (by rfl) ⟨165, by rfl⟩ : syracuseStep 112981 = 331) (by norm_num)
theorem B113017 : Blo 99781 113017 := bbase (se 2 (by rfl) ⟨42381, by rfl⟩ : syracuseStep 113017 = 84763) (by norm_num)
theorem B113053 : Blo 99781 113053 := bbase (se 3 (by rfl) ⟨21197, by rfl⟩ : syracuseStep 113053 = 42395) (by norm_num)
theorem B440741 : Blo 99781 440741 := bbase (se 4 (by rfl) ⟨41319, by rfl⟩ : syracuseStep 440741 = 82639) (by norm_num)
theorem B113089 : Blo 99781 113089 := bbase (se 2 (by rfl) ⟨42408, by rfl⟩ : syracuseStep 113089 = 84817) (by norm_num)
theorem B113125 : Blo 99781 113125 := bbase (se 4 (by rfl) ⟨10605, by rfl⟩ : syracuseStep 113125 = 21211) (by norm_num)
theorem B113161 : Blo 99781 113161 := bbase (se 2 (by rfl) ⟨42435, by rfl⟩ : syracuseStep 113161 = 84871) (by norm_num)
theorem B113197 : Blo 99781 113197 := bbase (se 3 (by rfl) ⟨21224, by rfl⟩ : syracuseStep 113197 = 42449) (by norm_num)
theorem B113233 : Blo 99781 113233 := bbase (se 2 (by rfl) ⟨42462, by rfl⟩ : syracuseStep 113233 = 84925) (by norm_num)
theorem B244309 : Blo 99781 244309 := bbase (se 8 (by rfl) ⟨1431, by rfl⟩ : syracuseStep 244309 = 2863) (by norm_num)
theorem B342629 : Blo 99781 342629 := bbase (se 4 (by rfl) ⟨32121, by rfl⟩ : syracuseStep 342629 = 64243) (by norm_num)
theorem B113269 : Blo 99781 113269 := bbase (se 5 (by rfl) ⟨5309, by rfl⟩ : syracuseStep 113269 = 10619) (by norm_num)
theorem B113305 : Blo 99781 113305 := bbase (se 2 (by rfl) ⟨42489, by rfl⟩ : syracuseStep 113305 = 84979) (by norm_num)
theorem B735925 : Blo 99781 735925 := bbase (se 5 (by rfl) ⟨34496, by rfl⟩ : syracuseStep 735925 = 68993) (by norm_num)
theorem B113341 : Blo 99781 113341 := bbase (se 3 (by rfl) ⟨21251, by rfl⟩ : syracuseStep 113341 = 42503) (by norm_num)
theorem B113377 : Blo 99781 113377 := bbase (se 2 (by rfl) ⟨42516, by rfl⟩ : syracuseStep 113377 = 85033) (by norm_num)
theorem B113413 : Blo 99781 113413 := bbase (se 4 (by rfl) ⟨10632, by rfl⟩ : syracuseStep 113413 = 21265) (by norm_num)
theorem B113449 : Blo 99781 113449 := bbase (se 2 (by rfl) ⟨42543, by rfl⟩ : syracuseStep 113449 = 85087) (by norm_num)
theorem B113485 : Blo 99781 113485 := bbase (se 3 (by rfl) ⟨21278, by rfl⟩ : syracuseStep 113485 = 42557) (by norm_num)
theorem B113521 : Blo 99781 113521 := bbase (se 2 (by rfl) ⟨42570, by rfl⟩ : syracuseStep 113521 = 85141) (by norm_num)
theorem B113557 : Blo 99781 113557 := bbase (se 6 (by rfl) ⟨2661, by rfl⟩ : syracuseStep 113557 = 5323) (by norm_num)
theorem B113593 : Blo 99781 113593 := bbase (se 2 (by rfl) ⟨42597, by rfl⟩ : syracuseStep 113593 = 85195) (by norm_num)
theorem B113629 : Blo 99781 113629 := bbase (se 3 (by rfl) ⟨21305, by rfl⟩ : syracuseStep 113629 = 42611) (by norm_num)
theorem B113665 : Blo 99781 113665 := bbase (se 2 (by rfl) ⟨42624, by rfl⟩ : syracuseStep 113665 = 85249) (by norm_num)
theorem B343061 : Blo 99781 343061 := bbase (se 6 (by rfl) ⟨8040, by rfl⟩ : syracuseStep 343061 = 16081) (by norm_num)
theorem B146461 : Blo 99781 146461 := bbase (se 3 (by rfl) ⟨27461, by rfl⟩ : syracuseStep 146461 = 54923) (by norm_num)
theorem B113701 : Blo 99781 113701 := bbase (se 4 (by rfl) ⟨10659, by rfl⟩ : syracuseStep 113701 = 21319) (by norm_num)
theorem B113737 : Blo 99781 113737 := bbase (se 2 (by rfl) ⟨42651, by rfl⟩ : syracuseStep 113737 = 85303) (by norm_num)
theorem B113773 : Blo 99781 113773 := bbase (se 3 (by rfl) ⟨21332, by rfl⟩ : syracuseStep 113773 = 42665) (by norm_num)
theorem B113809 : Blo 99781 113809 := bbase (se 2 (by rfl) ⟨42678, by rfl⟩ : syracuseStep 113809 = 85357) (by norm_num)
theorem B244885 : Blo 99781 244885 := bbase (se 6 (by rfl) ⟨5739, by rfl⟩ : syracuseStep 244885 = 11479) (by norm_num)
theorem B113845 : Blo 99781 113845 := bbase (se 5 (by rfl) ⟨5336, by rfl⟩ : syracuseStep 113845 = 10673) (by norm_num)
theorem B572629 : Blo 99781 572629 := bbase (se 7 (by rfl) ⟨6710, by rfl⟩ : syracuseStep 572629 = 13421) (by norm_num)
theorem B113881 : Blo 99781 113881 := bbase (se 2 (by rfl) ⟨42705, by rfl⟩ : syracuseStep 113881 = 85411) (by norm_num)
theorem B113917 : Blo 99781 113917 := bbase (se 3 (by rfl) ⟨21359, by rfl⟩ : syracuseStep 113917 = 42719) (by norm_num)
theorem B113953 : Blo 99781 113953 := bbase (se 2 (by rfl) ⟨42732, by rfl⟩ : syracuseStep 113953 = 85465) (by norm_num)
theorem B113989 : Blo 99781 113989 := bbase (se 4 (by rfl) ⟨10686, by rfl⟩ : syracuseStep 113989 = 21373) (by norm_num)
theorem B507221 : Blo 99781 507221 := bbase (se 11 (by rfl) ⟨371, by rfl⟩ : syracuseStep 507221 = 743) (by norm_num)
theorem B310613 : Blo 99781 310613 := bbase (se 11 (by rfl) ⟨227, by rfl⟩ : syracuseStep 310613 = 455) (by norm_num)
theorem B114025 : Blo 99781 114025 := bbase (se 2 (by rfl) ⟨42759, by rfl⟩ : syracuseStep 114025 = 85519) (by norm_num)
theorem B114061 : Blo 99781 114061 := bbase (se 3 (by rfl) ⟨21386, by rfl⟩ : syracuseStep 114061 = 42773) (by norm_num)
theorem B114097 : Blo 99781 114097 := bbase (se 2 (by rfl) ⟨42786, by rfl⟩ : syracuseStep 114097 = 85573) (by norm_num)
theorem B343493 : Blo 99781 343493 := bbase (se 4 (by rfl) ⟨32202, by rfl⟩ : syracuseStep 343493 = 64405) (by norm_num)
theorem B114133 : Blo 99781 114133 := bbase (se 7 (by rfl) ⟨1337, by rfl⟩ : syracuseStep 114133 = 2675) (by norm_num)
theorem B245213 : Blo 99781 245213 := bbase (se 3 (by rfl) ⟨45977, by rfl⟩ : syracuseStep 245213 = 91955) (by norm_num)
theorem B114169 : Blo 99781 114169 := bbase (se 2 (by rfl) ⟨42813, by rfl⟩ : syracuseStep 114169 = 85627) (by norm_num)
theorem B245269 : Blo 99781 245269 := bbase (se 6 (by rfl) ⟨5748, by rfl⟩ : syracuseStep 245269 = 11497) (by norm_num)
theorem B114205 : Blo 99781 114205 := bbase (se 3 (by rfl) ⟨21413, by rfl⟩ : syracuseStep 114205 = 42827) (by norm_num)
theorem B114241 : Blo 99781 114241 := bbase (se 2 (by rfl) ⟨42840, by rfl⟩ : syracuseStep 114241 = 85681) (by norm_num)
theorem B114277 : Blo 99781 114277 := bbase (se 4 (by rfl) ⟨10713, by rfl⟩ : syracuseStep 114277 = 21427) (by norm_num)
theorem B147053 : Blo 99781 147053 := bbase (se 3 (by rfl) ⟨27572, by rfl⟩ : syracuseStep 147053 = 55145) (by norm_num)
theorem B114313 : Blo 99781 114313 := bbase (se 2 (by rfl) ⟨42867, by rfl⟩ : syracuseStep 114313 = 85735) (by norm_num)
theorem B245413 : Blo 99781 245413 := bbase (se 4 (by rfl) ⟨23007, by rfl⟩ : syracuseStep 245413 = 46015) (by norm_num)
theorem B114349 : Blo 99781 114349 := bbase (se 3 (by rfl) ⟨21440, by rfl⟩ : syracuseStep 114349 = 42881) (by norm_num)
theorem B147133 : Blo 99781 147133 := bbase (se 3 (by rfl) ⟨27587, by rfl⟩ : syracuseStep 147133 = 55175) (by norm_num)
theorem B114385 : Blo 99781 114385 := bbase (se 2 (by rfl) ⟨42894, by rfl⟩ : syracuseStep 114385 = 85789) (by norm_num)
theorem B114421 : Blo 99781 114421 := bbase (se 5 (by rfl) ⟨5363, by rfl⟩ : syracuseStep 114421 = 10727) (by norm_num)
theorem B245501 : Blo 99781 245501 := bbase (se 3 (by rfl) ⟨46031, by rfl⟩ : syracuseStep 245501 = 92063) (by norm_num)
theorem B540437 : Blo 99781 540437 := bbase (se 6 (by rfl) ⟨12666, by rfl⟩ : syracuseStep 540437 = 25333) (by norm_num)
theorem B114457 : Blo 99781 114457 := bbase (se 2 (by rfl) ⟨42921, by rfl⟩ : syracuseStep 114457 = 85843) (by norm_num)
theorem B147253 : Blo 99781 147253 := bbase (se 5 (by rfl) ⟨6902, by rfl⟩ : syracuseStep 147253 = 13805) (by norm_num)
theorem B114493 : Blo 99781 114493 := bbase (se 3 (by rfl) ⟨21467, by rfl⟩ : syracuseStep 114493 = 42935) (by norm_num)
theorem B114529 : Blo 99781 114529 := bbase (se 2 (by rfl) ⟨42948, by rfl⟩ : syracuseStep 114529 = 85897) (by norm_num)
theorem B343925 : Blo 99781 343925 := bbase (se 5 (by rfl) ⟨16121, by rfl⟩ : syracuseStep 343925 = 32243) (by norm_num)
theorem B114565 : Blo 99781 114565 := bbase (se 4 (by rfl) ⟨10740, by rfl⟩ : syracuseStep 114565 = 21481) (by norm_num)
theorem B147349 : Blo 99781 147349 := bbase (se 6 (by rfl) ⟨3453, by rfl⟩ : syracuseStep 147349 = 6907) (by norm_num)
theorem B114601 : Blo 99781 114601 := bbase (se 2 (by rfl) ⟨42975, by rfl⟩ : syracuseStep 114601 = 85951) (by norm_num)
theorem B245693 : Blo 99781 245693 := bbase (se 3 (by rfl) ⟨46067, by rfl⟩ : syracuseStep 245693 = 92135) (by norm_num)
theorem B114637 : Blo 99781 114637 := bbase (se 3 (by rfl) ⟨21494, by rfl⟩ : syracuseStep 114637 = 42989) (by norm_num)
theorem B114673 : Blo 99781 114673 := bbase (se 2 (by rfl) ⟨43002, by rfl⟩ : syracuseStep 114673 = 86005) (by norm_num)
theorem B114709 : Blo 99781 114709 := bbase (se 6 (by rfl) ⟨2688, by rfl⟩ : syracuseStep 114709 = 5377) (by norm_num)
theorem B114745 : Blo 99781 114745 := bbase (se 2 (by rfl) ⟨43029, by rfl⟩ : syracuseStep 114745 = 86059) (by norm_num)
theorem B114781 : Blo 99781 114781 := bbase (se 3 (by rfl) ⟨21521, by rfl⟩ : syracuseStep 114781 = 43043) (by norm_num)
theorem B114817 : Blo 99781 114817 := bbase (se 2 (by rfl) ⟨43056, by rfl⟩ : syracuseStep 114817 = 86113) (by norm_num)
theorem B114853 : Blo 99781 114853 := bbase (se 4 (by rfl) ⟨10767, by rfl⟩ : syracuseStep 114853 = 21535) (by norm_num)
theorem B114889 : Blo 99781 114889 := bbase (se 2 (by rfl) ⟨43083, by rfl⟩ : syracuseStep 114889 = 86167) (by norm_num)
theorem B278741 : Blo 99781 278741 := bbase (se 7 (by rfl) ⟨3266, by rfl⟩ : syracuseStep 278741 = 6533) (by norm_num)
theorem B114925 : Blo 99781 114925 := bbase (se 3 (by rfl) ⟨21548, by rfl⟩ : syracuseStep 114925 = 43097) (by norm_num)
theorem B835829 : Blo 99781 835829 := bbase (se 5 (by rfl) ⟨39179, by rfl⟩ : syracuseStep 835829 = 78359) (by norm_num)
theorem B114961 : Blo 99781 114961 := bbase (se 2 (by rfl) ⟨43110, by rfl⟩ : syracuseStep 114961 = 86221) (by norm_num)
theorem B344357 : Blo 99781 344357 := bbase (se 4 (by rfl) ⟨32283, by rfl⟩ : syracuseStep 344357 = 64567) (by norm_num)
theorem B213293 : Blo 99781 213293 := bbase (se 3 (by rfl) ⟨39992, by rfl⟩ : syracuseStep 213293 = 79985) (by norm_num)
theorem B213301 : Blo 99781 213301 := bbase (se 5 (by rfl) ⟨9998, by rfl⟩ : syracuseStep 213301 = 19997) (by norm_num)
theorem B114997 : Blo 99781 114997 := bbase (se 5 (by rfl) ⟨5390, by rfl⟩ : syracuseStep 114997 = 10781) (by norm_num)
theorem B115033 : Blo 99781 115033 := bbase (se 2 (by rfl) ⟨43137, by rfl⟩ : syracuseStep 115033 = 86275) (by norm_num)
theorem B115069 : Blo 99781 115069 := bbase (se 3 (by rfl) ⟨21575, by rfl⟩ : syracuseStep 115069 = 43151) (by norm_num)
theorem B115105 : Blo 99781 115105 := bbase (se 2 (by rfl) ⟨43164, by rfl⟩ : syracuseStep 115105 = 86329) (by norm_num)
theorem B115141 : Blo 99781 115141 := bbase (se 4 (by rfl) ⟨10794, by rfl⟩ : syracuseStep 115141 = 21589) (by norm_num)
theorem B442853 : Blo 99781 442853 := bbase (se 4 (by rfl) ⟨41517, by rfl⟩ : syracuseStep 442853 = 83035) (by norm_num)
theorem B115177 : Blo 99781 115177 := bbase (se 2 (by rfl) ⟨43191, by rfl⟩ : syracuseStep 115177 = 86383) (by norm_num)
theorem B115213 : Blo 99781 115213 := bbase (se 3 (by rfl) ⟨21602, by rfl⟩ : syracuseStep 115213 = 43205) (by norm_num)
theorem B115249 : Blo 99781 115249 := bbase (se 2 (by rfl) ⟨43218, by rfl⟩ : syracuseStep 115249 = 86437) (by norm_num)
theorem B115285 : Blo 99781 115285 := bbase (se 8 (by rfl) ⟨675, by rfl⟩ : syracuseStep 115285 = 1351) (by norm_num)
theorem B508517 : Blo 99781 508517 := bbase (se 4 (by rfl) ⟨47673, by rfl⟩ : syracuseStep 508517 = 95347) (by norm_num)
theorem B115321 : Blo 99781 115321 := bbase (se 2 (by rfl) ⟨43245, by rfl⟩ : syracuseStep 115321 = 86491) (by norm_num)
theorem B115345 : Blo 99781 115345 := bbase (se 2 (by rfl) ⟨43254, by rfl⟩ : syracuseStep 115345 = 86509) (by norm_num)
theorem B115357 : Blo 99781 115357 := bbase (se 3 (by rfl) ⟨21629, by rfl⟩ : syracuseStep 115357 = 43259) (by norm_num)
theorem B705205 : Blo 99781 705205 := bbase (se 5 (by rfl) ⟨33056, by rfl⟩ : syracuseStep 705205 = 66113) (by norm_num)
theorem B115393 : Blo 99781 115393 := bbase (se 2 (by rfl) ⟨43272, by rfl⟩ : syracuseStep 115393 = 86545) (by norm_num)
theorem B344789 : Blo 99781 344789 := bbase (se 7 (by rfl) ⟨4040, by rfl⟩ : syracuseStep 344789 = 8081) (by norm_num)
theorem B115429 : Blo 99781 115429 := bbase (se 4 (by rfl) ⟨10821, by rfl⟩ : syracuseStep 115429 = 21643) (by norm_num)
theorem B443141 : Blo 99781 443141 := bbase (se 4 (by rfl) ⟨41544, by rfl⟩ : syracuseStep 443141 = 83089) (by norm_num)
theorem B115465 : Blo 99781 115465 := bbase (se 2 (by rfl) ⟨43299, by rfl⟩ : syracuseStep 115465 = 86599) (by norm_num)
theorem B115501 : Blo 99781 115501 := bbase (se 3 (by rfl) ⟨21656, by rfl⟩ : syracuseStep 115501 = 43313) (by norm_num)
theorem B115537 : Blo 99781 115537 := bbase (se 2 (by rfl) ⟨43326, by rfl⟩ : syracuseStep 115537 = 86653) (by norm_num)
theorem B115573 : Blo 99781 115573 := bbase (se 5 (by rfl) ⟨5417, by rfl⟩ : syracuseStep 115573 = 10835) (by norm_num)
theorem B246653 : Blo 99781 246653 := bbase (se 3 (by rfl) ⟨46247, by rfl⟩ : syracuseStep 246653 = 92495) (by norm_num)
theorem B115609 : Blo 99781 115609 := bbase (se 2 (by rfl) ⟨43353, by rfl⟩ : syracuseStep 115609 = 86707) (by norm_num)
theorem B115645 : Blo 99781 115645 := bbase (se 3 (by rfl) ⟨21683, by rfl⟩ : syracuseStep 115645 = 43367) (by norm_num)
theorem B115681 : Blo 99781 115681 := bbase (se 2 (by rfl) ⟨43380, by rfl⟩ : syracuseStep 115681 = 86761) (by norm_num)
theorem B345061 : Blo 99781 345061 := bbase (se 4 (by rfl) ⟨32349, by rfl⟩ : syracuseStep 345061 = 64699) (by norm_num)
theorem B115717 : Blo 99781 115717 := bbase (se 4 (by rfl) ⟨10848, by rfl⟩ : syracuseStep 115717 = 21697) (by norm_num)
theorem B115753 : Blo 99781 115753 := bbase (se 2 (by rfl) ⟨43407, by rfl⟩ : syracuseStep 115753 = 86815) (by norm_num)
theorem B115789 : Blo 99781 115789 := bbase (se 3 (by rfl) ⟨21710, by rfl⟩ : syracuseStep 115789 = 43421) (by norm_num)
theorem B115825 : Blo 99781 115825 := bbase (se 2 (by rfl) ⟨43434, by rfl⟩ : syracuseStep 115825 = 86869) (by norm_num)
theorem B345221 : Blo 99781 345221 := bbase (se 4 (by rfl) ⟨32364, by rfl⟩ : syracuseStep 345221 = 64729) (by norm_num)
theorem B574613 : Blo 99781 574613 := bbase (se 6 (by rfl) ⟨13467, by rfl⟩ : syracuseStep 574613 = 26935) (by norm_num)
theorem B115861 : Blo 99781 115861 := bbase (se 6 (by rfl) ⟨2715, by rfl⟩ : syracuseStep 115861 = 5431) (by norm_num)
theorem B115897 : Blo 99781 115897 := bbase (se 2 (by rfl) ⟨43461, by rfl⟩ : syracuseStep 115897 = 86923) (by norm_num)
theorem B115933 : Blo 99781 115933 := bbase (se 3 (by rfl) ⟨21737, by rfl⟩ : syracuseStep 115933 = 43475) (by norm_num)
theorem B115969 : Blo 99781 115969 := bbase (se 2 (by rfl) ⟨43488, by rfl⟩ : syracuseStep 115969 = 86977) (by norm_num)
theorem B116005 : Blo 99781 116005 := bbase (se 4 (by rfl) ⟨10875, by rfl⟩ : syracuseStep 116005 = 21751) (by norm_num)
theorem B116041 : Blo 99781 116041 := bbase (se 2 (by rfl) ⟨43515, by rfl⟩ : syracuseStep 116041 = 87031) (by norm_num)
theorem B116077 : Blo 99781 116077 := bbase (se 3 (by rfl) ⟨21764, by rfl⟩ : syracuseStep 116077 = 43529) (by norm_num)
theorem B247157 : Blo 99781 247157 := bbase (se 5 (by rfl) ⟨11585, by rfl⟩ : syracuseStep 247157 = 23171) (by norm_num)
theorem B181645 : Blo 99781 181645 := bbase (se 3 (by rfl) ⟨34058, by rfl⟩ : syracuseStep 181645 = 68117) (by norm_num)
theorem B116113 : Blo 99781 116113 := bbase (se 2 (by rfl) ⟨43542, by rfl⟩ : syracuseStep 116113 = 87085) (by norm_num)
theorem B214429 : Blo 99781 214429 := bbase (se 3 (by rfl) ⟨40205, by rfl⟩ : syracuseStep 214429 = 80411) (by norm_num)
theorem B116149 : Blo 99781 116149 := bbase (se 5 (by rfl) ⟨5444, by rfl⟩ : syracuseStep 116149 = 10889) (by norm_num)
theorem B116185 : Blo 99781 116185 := bbase (se 2 (by rfl) ⟨43569, by rfl⟩ : syracuseStep 116185 = 87139) (by norm_num)
theorem B116221 : Blo 99781 116221 := bbase (se 3 (by rfl) ⟨21791, by rfl⟩ : syracuseStep 116221 = 43583) (by norm_num)
theorem B116257 : Blo 99781 116257 := bbase (se 2 (by rfl) ⟨43596, by rfl⟩ : syracuseStep 116257 = 87193) (by norm_num)
theorem B345653 : Blo 99781 345653 := bbase (se 5 (by rfl) ⟨16202, by rfl⟩ : syracuseStep 345653 = 32405) (by norm_num)
theorem B116293 : Blo 99781 116293 := bbase (se 4 (by rfl) ⟨10902, by rfl⟩ : syracuseStep 116293 = 21805) (by norm_num)
theorem B116329 : Blo 99781 116329 := bbase (se 2 (by rfl) ⟨43623, by rfl⟩ : syracuseStep 116329 = 87247) (by norm_num)
theorem B116365 : Blo 99781 116365 := bbase (se 3 (by rfl) ⟨21818, by rfl⟩ : syracuseStep 116365 = 43637) (by norm_num)
theorem B116401 : Blo 99781 116401 := bbase (se 2 (by rfl) ⟨43650, by rfl⟩ : syracuseStep 116401 = 87301) (by norm_num)
theorem B116437 : Blo 99781 116437 := bbase (se 7 (by rfl) ⟨1364, by rfl⟩ : syracuseStep 116437 = 2729) (by norm_num)
theorem B116473 : Blo 99781 116473 := bbase (se 2 (by rfl) ⟨43677, by rfl⟩ : syracuseStep 116473 = 87355) (by norm_num)
theorem B214805 : Blo 99781 214805 := bbase (se 6 (by rfl) ⟨5034, by rfl⟩ : syracuseStep 214805 = 10069) (by norm_num)
theorem B116509 : Blo 99781 116509 := bbase (se 3 (by rfl) ⟨21845, by rfl⟩ : syracuseStep 116509 = 43691) (by norm_num)
theorem B116545 : Blo 99781 116545 := bbase (se 2 (by rfl) ⟨43704, by rfl⟩ : syracuseStep 116545 = 87409) (by norm_num)
theorem B411493 : Blo 99781 411493 := bbase (se 4 (by rfl) ⟨38577, by rfl⟩ : syracuseStep 411493 = 77155) (by norm_num)
theorem B116581 : Blo 99781 116581 := bbase (se 4 (by rfl) ⟨10929, by rfl⟩ : syracuseStep 116581 = 21859) (by norm_num)
theorem B509813 : Blo 99781 509813 := bbase (se 5 (by rfl) ⟨23897, by rfl⟩ : syracuseStep 509813 = 47795) (by norm_num)
theorem B116617 : Blo 99781 116617 := bbase (se 2 (by rfl) ⟨43731, by rfl⟩ : syracuseStep 116617 = 87463) (by norm_num)
theorem B116653 : Blo 99781 116653 := bbase (se 3 (by rfl) ⟨21872, by rfl⟩ : syracuseStep 116653 = 43745) (by norm_num)
theorem B116689 : Blo 99781 116689 := bbase (se 2 (by rfl) ⟨43758, by rfl⟩ : syracuseStep 116689 = 87517) (by norm_num)
theorem B247781 : Blo 99781 247781 := bbase (se 4 (by rfl) ⟨23229, by rfl⟩ : syracuseStep 247781 = 46459) (by norm_num)
theorem B346085 : Blo 99781 346085 := bbase (se 4 (by rfl) ⟨32445, by rfl⟩ : syracuseStep 346085 = 64891) (by norm_num)
theorem B870389 : Blo 99781 870389 := bbase (se 5 (by rfl) ⟨40799, by rfl⟩ : syracuseStep 870389 = 81599) (by norm_num)
theorem B116725 : Blo 99781 116725 := bbase (se 5 (by rfl) ⟨5471, by rfl⟩ : syracuseStep 116725 = 10943) (by norm_num)
theorem B247901 : Blo 99781 247901 := bbase (se 3 (by rfl) ⟨46481, by rfl⟩ : syracuseStep 247901 = 92963) (by norm_num)
theorem B149693 : Blo 99781 149693 := bbase (se 3 (by rfl) ⟨28067, by rfl⟩ : syracuseStep 149693 = 56135) (by norm_num)
theorem B149717 : Blo 99781 149717 := bbase (se 7 (by rfl) ⟨1754, by rfl⟩ : syracuseStep 149717 = 3509) (by norm_num)
theorem B149741 : Blo 99781 149741 := bbase (se 3 (by rfl) ⟨28076, by rfl⟩ : syracuseStep 149741 = 56153) (by norm_num)
theorem B149765 : Blo 99781 149765 := bbase (se 4 (by rfl) ⟨14040, by rfl⟩ : syracuseStep 149765 = 28081) (by norm_num)
theorem B149789 : Blo 99781 149789 := bbase (se 3 (by rfl) ⟨28085, by rfl⟩ : syracuseStep 149789 = 56171) (by norm_num)
theorem B149813 : Blo 99781 149813 := bbase (se 5 (by rfl) ⟨7022, by rfl⟩ : syracuseStep 149813 = 14045) (by norm_num)
theorem B149837 : Blo 99781 149837 := bbase (se 3 (by rfl) ⟨28094, by rfl⟩ : syracuseStep 149837 = 56189) (by norm_num)
theorem B149861 : Blo 99781 149861 := bbase (se 4 (by rfl) ⟨14049, by rfl⟩ : syracuseStep 149861 = 28099) (by norm_num)
theorem B149885 : Blo 99781 149885 := bbase (se 3 (by rfl) ⟨28103, by rfl⟩ : syracuseStep 149885 = 56207) (by norm_num)
theorem B149909 : Blo 99781 149909 := bbase (se 6 (by rfl) ⟨3513, by rfl⟩ : syracuseStep 149909 = 7027) (by norm_num)
theorem B346517 : Blo 99781 346517 := bbase (se 6 (by rfl) ⟨8121, by rfl⟩ : syracuseStep 346517 = 16243) (by norm_num)
theorem B149933 : Blo 99781 149933 := bbase (se 3 (by rfl) ⟨28112, by rfl⟩ : syracuseStep 149933 = 56225) (by norm_num)
theorem B149957 : Blo 99781 149957 := bbase (se 4 (by rfl) ⟨14058, by rfl⟩ : syracuseStep 149957 = 28117) (by norm_num)
theorem B182741 : Blo 99781 182741 := bbase (se 7 (by rfl) ⟨2141, by rfl⟩ : syracuseStep 182741 = 4283) (by norm_num)
theorem B149981 : Blo 99781 149981 := bbase (se 3 (by rfl) ⟨28121, by rfl⟩ : syracuseStep 149981 = 56243) (by norm_num)
theorem B150005 : Blo 99781 150005 := bbase (se 5 (by rfl) ⟨7031, by rfl⟩ : syracuseStep 150005 = 14063) (by norm_num)
theorem B150029 : Blo 99781 150029 := bbase (se 3 (by rfl) ⟨28130, by rfl⟩ : syracuseStep 150029 = 56261) (by norm_num)
theorem B150053 : Blo 99781 150053 := bbase (se 4 (by rfl) ⟨14067, by rfl⟩ : syracuseStep 150053 = 28135) (by norm_num)
theorem B150077 : Blo 99781 150077 := bbase (se 3 (by rfl) ⟨28139, by rfl⟩ : syracuseStep 150077 = 56279) (by norm_num)
theorem B150101 : Blo 99781 150101 := bbase (se 8 (by rfl) ⟨879, by rfl⟩ : syracuseStep 150101 = 1759) (by norm_num)
theorem B150125 : Blo 99781 150125 := bbase (se 3 (by rfl) ⟨28148, by rfl⟩ : syracuseStep 150125 = 56297) (by norm_num)
theorem B150149 : Blo 99781 150149 := bbase (se 4 (by rfl) ⟨14076, by rfl⟩ : syracuseStep 150149 = 28153) (by norm_num)
theorem B150173 : Blo 99781 150173 := bbase (se 3 (by rfl) ⟨28157, by rfl⟩ : syracuseStep 150173 = 56315) (by norm_num)
theorem B150197 : Blo 99781 150197 := bbase (se 5 (by rfl) ⟨7040, by rfl⟩ : syracuseStep 150197 = 14081) (by norm_num)
theorem B150221 : Blo 99781 150221 := bbase (se 3 (by rfl) ⟨28166, by rfl⟩ : syracuseStep 150221 = 56333) (by norm_num)
theorem B150245 : Blo 99781 150245 := bbase (se 4 (by rfl) ⟨14085, by rfl⟩ : syracuseStep 150245 = 28171) (by norm_num)
theorem B150269 : Blo 99781 150269 := bbase (se 3 (by rfl) ⟨28175, by rfl⟩ : syracuseStep 150269 = 56351) (by norm_num)
theorem B150293 : Blo 99781 150293 := bbase (se 6 (by rfl) ⟨3522, by rfl⟩ : syracuseStep 150293 = 7045) (by norm_num)
theorem B150317 : Blo 99781 150317 := bbase (se 3 (by rfl) ⟨28184, by rfl⟩ : syracuseStep 150317 = 56369) (by norm_num)
theorem B346949 : Blo 99781 346949 := bbase (se 4 (by rfl) ⟨32526, by rfl⟩ : syracuseStep 346949 = 65053) (by norm_num)
theorem B150341 : Blo 99781 150341 := bbase (se 4 (by rfl) ⟨14094, by rfl⟩ : syracuseStep 150341 = 28189) (by norm_num)
theorem B150365 : Blo 99781 150365 := bbase (se 3 (by rfl) ⟨28193, by rfl⟩ : syracuseStep 150365 = 56387) (by norm_num)
theorem B150389 : Blo 99781 150389 := bbase (se 5 (by rfl) ⟨7049, by rfl⟩ : syracuseStep 150389 = 14099) (by norm_num)
theorem B150413 : Blo 99781 150413 := bbase (se 3 (by rfl) ⟨28202, by rfl⟩ : syracuseStep 150413 = 56405) (by norm_num)
theorem B150437 : Blo 99781 150437 := bbase (se 4 (by rfl) ⟨14103, by rfl⟩ : syracuseStep 150437 = 28207) (by norm_num)
theorem B150461 : Blo 99781 150461 := bbase (se 3 (by rfl) ⟨28211, by rfl⟩ : syracuseStep 150461 = 56423) (by norm_num)
theorem B150485 : Blo 99781 150485 := bbase (se 7 (by rfl) ⟨1763, by rfl⟩ : syracuseStep 150485 = 3527) (by norm_num)
theorem B150509 : Blo 99781 150509 := bbase (se 3 (by rfl) ⟨28220, by rfl⟩ : syracuseStep 150509 = 56441) (by norm_num)
theorem B150533 : Blo 99781 150533 := bbase (se 4 (by rfl) ⟨14112, by rfl⟩ : syracuseStep 150533 = 28225) (by norm_num)
theorem B150557 : Blo 99781 150557 := bbase (se 3 (by rfl) ⟨28229, by rfl⟩ : syracuseStep 150557 = 56459) (by norm_num)
theorem B150581 : Blo 99781 150581 := bbase (se 5 (by rfl) ⟨7058, by rfl⟩ : syracuseStep 150581 = 14117) (by norm_num)
theorem B150605 : Blo 99781 150605 := bbase (se 3 (by rfl) ⟨28238, by rfl⟩ : syracuseStep 150605 = 56477) (by norm_num)
theorem B150629 : Blo 99781 150629 := bbase (se 4 (by rfl) ⟨14121, by rfl⟩ : syracuseStep 150629 = 28243) (by norm_num)
theorem B150653 : Blo 99781 150653 := bbase (se 3 (by rfl) ⟨28247, by rfl⟩ : syracuseStep 150653 = 56495) (by norm_num)
theorem B511109 : Blo 99781 511109 := bbase (se 4 (by rfl) ⟨47916, by rfl⟩ : syracuseStep 511109 = 95833) (by norm_num)
theorem B150677 : Blo 99781 150677 := bbase (se 6 (by rfl) ⟨3531, by rfl⟩ : syracuseStep 150677 = 7063) (by norm_num)
theorem B150701 : Blo 99781 150701 := bbase (se 3 (by rfl) ⟨28256, by rfl⟩ : syracuseStep 150701 = 56513) (by norm_num)
theorem B150725 : Blo 99781 150725 := bbase (se 4 (by rfl) ⟨14130, by rfl⟩ : syracuseStep 150725 = 28261) (by norm_num)
theorem B150749 : Blo 99781 150749 := bbase (se 3 (by rfl) ⟨28265, by rfl⟩ : syracuseStep 150749 = 56531) (by norm_num)
theorem B150773 : Blo 99781 150773 := bbase (se 5 (by rfl) ⟨7067, by rfl⟩ : syracuseStep 150773 = 14135) (by norm_num)
theorem B347381 : Blo 99781 347381 := bbase (se 5 (by rfl) ⟨16283, by rfl⟩ : syracuseStep 347381 = 32567) (by norm_num)
theorem B150797 : Blo 99781 150797 := bbase (se 3 (by rfl) ⟨28274, by rfl⟩ : syracuseStep 150797 = 56549) (by norm_num)
theorem B150821 : Blo 99781 150821 := bbase (se 4 (by rfl) ⟨14139, by rfl⟩ : syracuseStep 150821 = 28279) (by norm_num)
theorem B576821 : Blo 99781 576821 := bbase (se 5 (by rfl) ⟨27038, by rfl⟩ : syracuseStep 576821 = 54077) (by norm_num)
theorem B150845 : Blo 99781 150845 := bbase (se 3 (by rfl) ⟨28283, by rfl⟩ : syracuseStep 150845 = 56567) (by norm_num)
theorem B150869 : Blo 99781 150869 := bbase (se 11 (by rfl) ⟨110, by rfl⟩ : syracuseStep 150869 = 221) (by norm_num)
theorem B150893 : Blo 99781 150893 := bbase (se 3 (by rfl) ⟨28292, by rfl⟩ : syracuseStep 150893 = 56585) (by norm_num)
theorem B216445 : Blo 99781 216445 := bbase (se 3 (by rfl) ⟨40583, by rfl⟩ : syracuseStep 216445 = 81167) (by norm_num)
theorem B150917 : Blo 99781 150917 := bbase (se 4 (by rfl) ⟨14148, by rfl⟩ : syracuseStep 150917 = 28297) (by norm_num)
theorem B150941 : Blo 99781 150941 := bbase (se 3 (by rfl) ⟨28301, by rfl⟩ : syracuseStep 150941 = 56603) (by norm_num)
theorem B150965 : Blo 99781 150965 := bbase (se 5 (by rfl) ⟨7076, by rfl⟩ : syracuseStep 150965 = 14153) (by norm_num)
theorem B282053 : Blo 99781 282053 := bbase (se 4 (by rfl) ⟨26442, by rfl⟩ : syracuseStep 282053 = 52885) (by norm_num)
theorem B150989 : Blo 99781 150989 := bbase (se 3 (by rfl) ⟨28310, by rfl⟩ : syracuseStep 150989 = 56621) (by norm_num)
theorem B151013 : Blo 99781 151013 := bbase (se 4 (by rfl) ⟨14157, by rfl⟩ : syracuseStep 151013 = 28315) (by norm_num)
theorem B151037 : Blo 99781 151037 := bbase (se 3 (by rfl) ⟨28319, by rfl⟩ : syracuseStep 151037 = 56639) (by norm_num)
theorem B151061 : Blo 99781 151061 := bbase (se 6 (by rfl) ⟨3540, by rfl⟩ : syracuseStep 151061 = 7081) (by norm_num)
theorem B151085 : Blo 99781 151085 := bbase (se 3 (by rfl) ⟨28328, by rfl⟩ : syracuseStep 151085 = 56657) (by norm_num)
theorem B151109 : Blo 99781 151109 := bbase (se 4 (by rfl) ⟨14166, by rfl⟩ : syracuseStep 151109 = 28333) (by norm_num)
theorem B151133 : Blo 99781 151133 := bbase (se 3 (by rfl) ⟨28337, by rfl⟩ : syracuseStep 151133 = 56675) (by norm_num)
theorem B151157 : Blo 99781 151157 := bbase (se 5 (by rfl) ⟨7085, by rfl⟩ : syracuseStep 151157 = 14171) (by norm_num)
theorem B151181 : Blo 99781 151181 := bbase (se 3 (by rfl) ⟨28346, by rfl⟩ : syracuseStep 151181 = 56693) (by norm_num)
theorem B151205 : Blo 99781 151205 := bbase (se 4 (by rfl) ⟨14175, by rfl⟩ : syracuseStep 151205 = 28351) (by norm_num)
theorem B347813 : Blo 99781 347813 := bbase (se 4 (by rfl) ⟨32607, by rfl⟩ : syracuseStep 347813 = 65215) (by norm_num)
theorem B151229 : Blo 99781 151229 := bbase (se 3 (by rfl) ⟨28355, by rfl⟩ : syracuseStep 151229 = 56711) (by norm_num)
theorem B151253 : Blo 99781 151253 := bbase (se 7 (by rfl) ⟨1772, by rfl⟩ : syracuseStep 151253 = 3545) (by norm_num)
theorem B380645 : Blo 99781 380645 := bbase (se 4 (by rfl) ⟨35685, by rfl⟩ : syracuseStep 380645 = 71371) (by norm_num)
theorem B151277 : Blo 99781 151277 := bbase (se 3 (by rfl) ⟨28364, by rfl⟩ : syracuseStep 151277 = 56729) (by norm_num)
theorem B151301 : Blo 99781 151301 := bbase (se 4 (by rfl) ⟨14184, by rfl⟩ : syracuseStep 151301 = 28369) (by norm_num)
theorem B151325 : Blo 99781 151325 := bbase (se 3 (by rfl) ⟨28373, by rfl⟩ : syracuseStep 151325 = 56747) (by norm_num)
theorem B151349 : Blo 99781 151349 := bbase (se 5 (by rfl) ⟨7094, by rfl⟩ : syracuseStep 151349 = 14189) (by norm_num)
theorem B151373 : Blo 99781 151373 := bbase (se 3 (by rfl) ⟨28382, by rfl⟩ : syracuseStep 151373 = 56765) (by norm_num)
theorem B151397 : Blo 99781 151397 := bbase (se 4 (by rfl) ⟨14193, by rfl⟩ : syracuseStep 151397 = 28387) (by norm_num)
theorem B151421 : Blo 99781 151421 := bbase (se 3 (by rfl) ⟨28391, by rfl⟩ : syracuseStep 151421 = 56783) (by norm_num)
theorem B151445 : Blo 99781 151445 := bbase (se 6 (by rfl) ⟨3549, by rfl⟩ : syracuseStep 151445 = 7099) (by norm_num)
theorem B151469 : Blo 99781 151469 := bbase (se 3 (by rfl) ⟨28400, by rfl⟩ : syracuseStep 151469 = 56801) (by norm_num)
theorem B151493 : Blo 99781 151493 := bbase (se 4 (by rfl) ⟨14202, by rfl⟩ : syracuseStep 151493 = 28405) (by norm_num)
theorem B151517 : Blo 99781 151517 := bbase (se 3 (by rfl) ⟨28409, by rfl⟩ : syracuseStep 151517 = 56819) (by norm_num)
theorem B151541 : Blo 99781 151541 := bbase (se 5 (by rfl) ⟨7103, by rfl⟩ : syracuseStep 151541 = 14207) (by norm_num)
theorem B937973 : Blo 99781 937973 := bbase (se 5 (by rfl) ⟨43967, by rfl⟩ : syracuseStep 937973 = 87935) (by norm_num)
theorem B380933 : Blo 99781 380933 := bbase (se 4 (by rfl) ⟨35712, by rfl⟩ : syracuseStep 380933 = 71425) (by norm_num)
theorem B151565 : Blo 99781 151565 := bbase (se 3 (by rfl) ⟨28418, by rfl⟩ : syracuseStep 151565 = 56837) (by norm_num)
theorem B151589 : Blo 99781 151589 := bbase (se 4 (by rfl) ⟨14211, by rfl⟩ : syracuseStep 151589 = 28423) (by norm_num)
theorem B774197 : Blo 99781 774197 := bbase (se 5 (by rfl) ⟨36290, by rfl⟩ : syracuseStep 774197 = 72581) (by norm_num)
theorem B151613 : Blo 99781 151613 := bbase (se 3 (by rfl) ⟨28427, by rfl⟩ : syracuseStep 151613 = 56855) (by norm_num)
theorem B151637 : Blo 99781 151637 := bbase (se 8 (by rfl) ⟨888, by rfl⟩ : syracuseStep 151637 = 1777) (by norm_num)
theorem B348245 : Blo 99781 348245 := bbase (se 8 (by rfl) ⟨2040, by rfl⟩ : syracuseStep 348245 = 4081) (by norm_num)
theorem B151661 : Blo 99781 151661 := bbase (se 3 (by rfl) ⟨28436, by rfl⟩ : syracuseStep 151661 = 56873) (by norm_num)
theorem B151685 : Blo 99781 151685 := bbase (se 4 (by rfl) ⟨14220, by rfl⟩ : syracuseStep 151685 = 28441) (by norm_num)
theorem B151709 : Blo 99781 151709 := bbase (se 3 (by rfl) ⟨28445, by rfl⟩ : syracuseStep 151709 = 56891) (by norm_num)
theorem B151733 : Blo 99781 151733 := bbase (se 5 (by rfl) ⟨7112, by rfl⟩ : syracuseStep 151733 = 14225) (by norm_num)
theorem B151757 : Blo 99781 151757 := bbase (se 3 (by rfl) ⟨28454, by rfl⟩ : syracuseStep 151757 = 56909) (by norm_num)
theorem B151781 : Blo 99781 151781 := bbase (se 4 (by rfl) ⟨14229, by rfl⟩ : syracuseStep 151781 = 28459) (by norm_num)
theorem B217333 : Blo 99781 217333 := bbase (se 5 (by rfl) ⟨10187, by rfl⟩ : syracuseStep 217333 = 20375) (by norm_num)
theorem B151805 : Blo 99781 151805 := bbase (se 3 (by rfl) ⟨28463, by rfl⟩ : syracuseStep 151805 = 56927) (by norm_num)
theorem B151829 : Blo 99781 151829 := bbase (se 6 (by rfl) ⟨3558, by rfl⟩ : syracuseStep 151829 = 7117) (by norm_num)
theorem B151853 : Blo 99781 151853 := bbase (se 3 (by rfl) ⟨28472, by rfl⟩ : syracuseStep 151853 = 56945) (by norm_num)
theorem B151877 : Blo 99781 151877 := bbase (se 4 (by rfl) ⟨14238, by rfl⟩ : syracuseStep 151877 = 28477) (by norm_num)
theorem B151901 : Blo 99781 151901 := bbase (se 3 (by rfl) ⟨28481, by rfl⟩ : syracuseStep 151901 = 56963) (by norm_num)
theorem B151925 : Blo 99781 151925 := bbase (se 5 (by rfl) ⟨7121, by rfl⟩ : syracuseStep 151925 = 14243) (by norm_num)
theorem B479621 : Blo 99781 479621 := bbase (se 4 (by rfl) ⟨44964, by rfl⟩ : syracuseStep 479621 = 89929) (by norm_num)
theorem B151949 : Blo 99781 151949 := bbase (se 3 (by rfl) ⟨28490, by rfl⟩ : syracuseStep 151949 = 56981) (by norm_num)
theorem B512405 : Blo 99781 512405 := bbase (se 6 (by rfl) ⟨12009, by rfl⟩ : syracuseStep 512405 = 24019) (by norm_num)
theorem B348565 : Blo 99781 348565 := bbase (se 6 (by rfl) ⟨8169, by rfl⟩ : syracuseStep 348565 = 16339) (by norm_num)
theorem B151973 : Blo 99781 151973 := bbase (se 4 (by rfl) ⟨14247, by rfl⟩ : syracuseStep 151973 = 28495) (by norm_num)
theorem B151997 : Blo 99781 151997 := bbase (se 3 (by rfl) ⟨28499, by rfl⟩ : syracuseStep 151997 = 56999) (by norm_num)
theorem B152021 : Blo 99781 152021 := bbase (se 7 (by rfl) ⟨1781, by rfl⟩ : syracuseStep 152021 = 3563) (by norm_num)
theorem B152045 : Blo 99781 152045 := bbase (se 3 (by rfl) ⟨28508, by rfl⟩ : syracuseStep 152045 = 57017) (by norm_num)
theorem B152069 : Blo 99781 152069 := bbase (se 4 (by rfl) ⟨14256, by rfl⟩ : syracuseStep 152069 = 28513) (by norm_num)
theorem B348677 : Blo 99781 348677 := bbase (se 4 (by rfl) ⟨32688, by rfl⟩ : syracuseStep 348677 = 65377) (by norm_num)
theorem B152093 : Blo 99781 152093 := bbase (se 3 (by rfl) ⟨28517, by rfl⟩ : syracuseStep 152093 = 57035) (by norm_num)
theorem B152117 : Blo 99781 152117 := bbase (se 5 (by rfl) ⟨7130, by rfl⟩ : syracuseStep 152117 = 14261) (by norm_num)
theorem B152141 : Blo 99781 152141 := bbase (se 3 (by rfl) ⟨28526, by rfl⟩ : syracuseStep 152141 = 57053) (by norm_num)
theorem B152165 : Blo 99781 152165 := bbase (se 4 (by rfl) ⟨14265, by rfl⟩ : syracuseStep 152165 = 28531) (by norm_num)
theorem B184933 : Blo 99781 184933 := bbase (se 4 (by rfl) ⟨17337, by rfl⟩ : syracuseStep 184933 = 34675) (by norm_num)
theorem B152189 : Blo 99781 152189 := bbase (se 3 (by rfl) ⟨28535, by rfl⟩ : syracuseStep 152189 = 57071) (by norm_num)
theorem B152213 : Blo 99781 152213 := bbase (se 6 (by rfl) ⟨3567, by rfl⟩ : syracuseStep 152213 = 7135) (by norm_num)
theorem B152237 : Blo 99781 152237 := bbase (se 3 (by rfl) ⟨28544, by rfl⟩ : syracuseStep 152237 = 57089) (by norm_num)
theorem B152261 : Blo 99781 152261 := bbase (se 4 (by rfl) ⟨14274, by rfl⟩ : syracuseStep 152261 = 28549) (by norm_num)
theorem B152285 : Blo 99781 152285 := bbase (se 3 (by rfl) ⟨28553, by rfl⟩ : syracuseStep 152285 = 57107) (by norm_num)
theorem B217829 : Blo 99781 217829 := bbase (se 4 (by rfl) ⟨20421, by rfl⟩ : syracuseStep 217829 = 40843) (by norm_num)
theorem B152309 : Blo 99781 152309 := bbase (se 5 (by rfl) ⟨7139, by rfl⟩ : syracuseStep 152309 = 14279) (by norm_num)
theorem B152333 : Blo 99781 152333 := bbase (se 3 (by rfl) ⟨28562, by rfl⟩ : syracuseStep 152333 = 57125) (by norm_num)
theorem B152357 : Blo 99781 152357 := bbase (se 4 (by rfl) ⟨14283, by rfl⟩ : syracuseStep 152357 = 28567) (by norm_num)
theorem B152381 : Blo 99781 152381 := bbase (se 3 (by rfl) ⟨28571, by rfl⟩ : syracuseStep 152381 = 57143) (by norm_num)
theorem B152405 : Blo 99781 152405 := bbase (se 9 (by rfl) ⟨446, by rfl⟩ : syracuseStep 152405 = 893) (by norm_num)
theorem B152429 : Blo 99781 152429 := bbase (se 3 (by rfl) ⟨28580, by rfl⟩ : syracuseStep 152429 = 57161) (by norm_num)
theorem B152437 : Blo 99781 152437 := bbase (se 5 (by rfl) ⟨7145, by rfl⟩ : syracuseStep 152437 = 14291) (by norm_num)
theorem B152453 : Blo 99781 152453 := bbase (se 4 (by rfl) ⟨14292, by rfl⟩ : syracuseStep 152453 = 28585) (by norm_num)
theorem B152477 : Blo 99781 152477 := bbase (se 3 (by rfl) ⟨28589, by rfl⟩ : syracuseStep 152477 = 57179) (by norm_num)
theorem B152501 : Blo 99781 152501 := bbase (se 5 (by rfl) ⟨7148, by rfl⟩ : syracuseStep 152501 = 14297) (by norm_num)
theorem B349109 : Blo 99781 349109 := bbase (se 5 (by rfl) ⟨16364, by rfl⟩ : syracuseStep 349109 = 32729) (by norm_num)
theorem B152525 : Blo 99781 152525 := bbase (se 3 (by rfl) ⟨28598, by rfl⟩ : syracuseStep 152525 = 57197) (by norm_num)
theorem B152549 : Blo 99781 152549 := bbase (se 4 (by rfl) ⟨14301, by rfl⟩ : syracuseStep 152549 = 28603) (by norm_num)
theorem B152573 : Blo 99781 152573 := bbase (se 3 (by rfl) ⟨28607, by rfl⟩ : syracuseStep 152573 = 57215) (by norm_num)
theorem B152597 : Blo 99781 152597 := bbase (se 6 (by rfl) ⟨3576, by rfl⟩ : syracuseStep 152597 = 7153) (by norm_num)
theorem B152621 : Blo 99781 152621 := bbase (se 3 (by rfl) ⟨28616, by rfl⟩ : syracuseStep 152621 = 57233) (by norm_num)
theorem B152645 : Blo 99781 152645 := bbase (se 4 (by rfl) ⟨14310, by rfl⟩ : syracuseStep 152645 = 28621) (by norm_num)
theorem B152669 : Blo 99781 152669 := bbase (se 3 (by rfl) ⟨28625, by rfl⟩ : syracuseStep 152669 = 57251) (by norm_num)
theorem B152693 : Blo 99781 152693 := bbase (se 5 (by rfl) ⟨7157, by rfl⟩ : syracuseStep 152693 = 14315) (by norm_num)
theorem B152717 : Blo 99781 152717 := bbase (se 3 (by rfl) ⟨28634, by rfl⟩ : syracuseStep 152717 = 57269) (by norm_num)
theorem B382117 : Blo 99781 382117 := bbase (se 4 (by rfl) ⟨35823, by rfl⟩ : syracuseStep 382117 = 71647) (by norm_num)
theorem B152741 : Blo 99781 152741 := bbase (se 4 (by rfl) ⟨14319, by rfl⟩ : syracuseStep 152741 = 28639) (by norm_num)
theorem B152765 : Blo 99781 152765 := bbase (se 3 (by rfl) ⟨28643, by rfl⟩ : syracuseStep 152765 = 57287) (by norm_num)
theorem B152789 : Blo 99781 152789 := bbase (se 7 (by rfl) ⟨1790, by rfl⟩ : syracuseStep 152789 = 3581) (by norm_num)
theorem B152813 : Blo 99781 152813 := bbase (se 3 (by rfl) ⟨28652, by rfl⟩ : syracuseStep 152813 = 57305) (by norm_num)
theorem B152837 : Blo 99781 152837 := bbase (se 4 (by rfl) ⟨14328, by rfl⟩ : syracuseStep 152837 = 28657) (by norm_num)
theorem B152861 : Blo 99781 152861 := bbase (se 3 (by rfl) ⟨28661, by rfl⟩ : syracuseStep 152861 = 57323) (by norm_num)
theorem B152885 : Blo 99781 152885 := bbase (se 5 (by rfl) ⟨7166, by rfl⟩ : syracuseStep 152885 = 14333) (by norm_num)
theorem B152909 : Blo 99781 152909 := bbase (se 3 (by rfl) ⟨28670, by rfl⟩ : syracuseStep 152909 = 57341) (by norm_num)
theorem B152933 : Blo 99781 152933 := bbase (se 4 (by rfl) ⟨14337, by rfl⟩ : syracuseStep 152933 = 28675) (by norm_num)
theorem B349541 : Blo 99781 349541 := bbase (se 4 (by rfl) ⟨32769, by rfl⟩ : syracuseStep 349541 = 65539) (by norm_num)
theorem B152957 : Blo 99781 152957 := bbase (se 3 (by rfl) ⟨28679, by rfl⟩ : syracuseStep 152957 = 57359) (by norm_num)
theorem B152981 : Blo 99781 152981 := bbase (se 6 (by rfl) ⟨3585, by rfl⟩ : syracuseStep 152981 = 7171) (by norm_num)
theorem B153005 : Blo 99781 153005 := bbase (se 3 (by rfl) ⟨28688, by rfl⟩ : syracuseStep 153005 = 57377) (by norm_num)
theorem B153029 : Blo 99781 153029 := bbase (se 4 (by rfl) ⟨14346, by rfl⟩ : syracuseStep 153029 = 28693) (by norm_num)
theorem B185797 : Blo 99781 185797 := bbase (se 4 (by rfl) ⟨17418, by rfl⟩ : syracuseStep 185797 = 34837) (by norm_num)
theorem B382421 : Blo 99781 382421 := bbase (se 7 (by rfl) ⟨4481, by rfl⟩ : syracuseStep 382421 = 8963) (by norm_num)
theorem B153053 : Blo 99781 153053 := bbase (se 3 (by rfl) ⟨28697, by rfl⟩ : syracuseStep 153053 = 57395) (by norm_num)
theorem B644597 : Blo 99781 644597 := bbase (se 5 (by rfl) ⟨30215, by rfl⟩ : syracuseStep 644597 = 60431) (by norm_num)
theorem B153077 : Blo 99781 153077 := bbase (se 5 (by rfl) ⟨7175, by rfl⟩ : syracuseStep 153077 = 14351) (by norm_num)
theorem B153101 : Blo 99781 153101 := bbase (se 3 (by rfl) ⟨28706, by rfl⟩ : syracuseStep 153101 = 57413) (by norm_num)
theorem B153125 : Blo 99781 153125 := bbase (se 4 (by rfl) ⟨14355, by rfl⟩ : syracuseStep 153125 = 28711) (by norm_num)
theorem B153149 : Blo 99781 153149 := bbase (se 3 (by rfl) ⟨28715, by rfl⟩ : syracuseStep 153149 = 57431) (by norm_num)
theorem B218693 : Blo 99781 218693 := bbase (se 4 (by rfl) ⟨20502, by rfl⟩ : syracuseStep 218693 = 41005) (by norm_num)
theorem B153173 : Blo 99781 153173 := bbase (se 8 (by rfl) ⟨897, by rfl⟩ : syracuseStep 153173 = 1795) (by norm_num)
theorem B153197 : Blo 99781 153197 := bbase (se 3 (by rfl) ⟨28724, by rfl⟩ : syracuseStep 153197 = 57449) (by norm_num)
theorem B153221 : Blo 99781 153221 := bbase (se 4 (by rfl) ⟨14364, by rfl⟩ : syracuseStep 153221 = 28729) (by norm_num)
theorem B153245 : Blo 99781 153245 := bbase (se 3 (by rfl) ⟨28733, by rfl⟩ : syracuseStep 153245 = 57467) (by norm_num)
theorem B513701 : Blo 99781 513701 := bbase (se 4 (by rfl) ⟨48159, by rfl⟩ : syracuseStep 513701 = 96319) (by norm_num)
theorem B153269 : Blo 99781 153269 := bbase (se 5 (by rfl) ⟨7184, by rfl⟩ : syracuseStep 153269 = 14369) (by norm_num)
theorem B153293 : Blo 99781 153293 := bbase (se 3 (by rfl) ⟨28742, by rfl⟩ : syracuseStep 153293 = 57485) (by norm_num)
theorem B218837 : Blo 99781 218837 := bbase (se 7 (by rfl) ⟨2564, by rfl⟩ : syracuseStep 218837 = 5129) (by norm_num)
theorem B153317 : Blo 99781 153317 := bbase (se 4 (by rfl) ⟨14373, by rfl⟩ : syracuseStep 153317 = 28747) (by norm_num)
theorem B153341 : Blo 99781 153341 := bbase (se 3 (by rfl) ⟨28751, by rfl⟩ : syracuseStep 153341 = 57503) (by norm_num)
theorem B153365 : Blo 99781 153365 := bbase (se 6 (by rfl) ⟨3594, by rfl⟩ : syracuseStep 153365 = 7189) (by norm_num)
theorem B349973 : Blo 99781 349973 := bbase (se 6 (by rfl) ⟨8202, by rfl⟩ : syracuseStep 349973 = 16405) (by norm_num)
theorem B153389 : Blo 99781 153389 := bbase (se 3 (by rfl) ⟨28760, by rfl⟩ : syracuseStep 153389 = 57521) (by norm_num)
theorem B153413 : Blo 99781 153413 := bbase (se 4 (by rfl) ⟨14382, by rfl⟩ : syracuseStep 153413 = 28765) (by norm_num)
theorem B153437 : Blo 99781 153437 := bbase (se 3 (by rfl) ⟨28769, by rfl⟩ : syracuseStep 153437 = 57539) (by norm_num)
theorem B153461 : Blo 99781 153461 := bbase (se 5 (by rfl) ⟨7193, by rfl⟩ : syracuseStep 153461 = 14387) (by norm_num)
theorem B153485 : Blo 99781 153485 := bbase (se 3 (by rfl) ⟨28778, by rfl⟩ : syracuseStep 153485 = 57557) (by norm_num)
theorem B153509 : Blo 99781 153509 := bbase (se 4 (by rfl) ⟨14391, by rfl⟩ : syracuseStep 153509 = 28783) (by norm_num)
theorem B153533 : Blo 99781 153533 := bbase (se 3 (by rfl) ⟨28787, by rfl⟩ : syracuseStep 153533 = 57575) (by norm_num)
theorem B186317 : Blo 99781 186317 := bbase (se 3 (by rfl) ⟨34934, by rfl⟩ : syracuseStep 186317 = 69869) (by norm_num)
theorem B284629 : Blo 99781 284629 := bbase (se 7 (by rfl) ⟨3335, by rfl⟩ : syracuseStep 284629 = 6671) (by norm_num)
theorem B153557 : Blo 99781 153557 := bbase (se 7 (by rfl) ⟨1799, by rfl⟩ : syracuseStep 153557 = 3599) (by norm_num)
theorem B120809 : Blo 99781 120809 := bbase (se 2 (by rfl) ⟨45303, by rfl⟩ : syracuseStep 120809 = 90607) (by norm_num)
theorem B153581 : Blo 99781 153581 := bbase (se 3 (by rfl) ⟨28796, by rfl⟩ : syracuseStep 153581 = 57593) (by norm_num)
theorem B153605 : Blo 99781 153605 := bbase (se 4 (by rfl) ⟨14400, by rfl⟩ : syracuseStep 153605 = 28801) (by norm_num)
theorem B186397 : Blo 99781 186397 := bbase (se 3 (by rfl) ⟨34949, by rfl⟩ : syracuseStep 186397 = 69899) (by norm_num)
theorem B153629 : Blo 99781 153629 := bbase (se 3 (by rfl) ⟨28805, by rfl⟩ : syracuseStep 153629 = 57611) (by norm_num)
theorem B153653 : Blo 99781 153653 := bbase (se 5 (by rfl) ⟨7202, by rfl⟩ : syracuseStep 153653 = 14405) (by norm_num)
theorem B153677 : Blo 99781 153677 := bbase (se 3 (by rfl) ⟨28814, by rfl⟩ : syracuseStep 153677 = 57629) (by norm_num)
theorem B153701 : Blo 99781 153701 := bbase (se 4 (by rfl) ⟨14409, by rfl⟩ : syracuseStep 153701 = 28819) (by norm_num)
theorem B284789 : Blo 99781 284789 := bbase (se 5 (by rfl) ⟨13349, by rfl⟩ : syracuseStep 284789 = 26699) (by norm_num)
theorem B252029 : Blo 99781 252029 := bbase (se 3 (by rfl) ⟨47255, by rfl⟩ : syracuseStep 252029 = 94511) (by norm_num)
theorem B153725 : Blo 99781 153725 := bbase (se 3 (by rfl) ⟨28823, by rfl⟩ : syracuseStep 153725 = 57647) (by norm_num)
theorem B153749 : Blo 99781 153749 := bbase (se 6 (by rfl) ⟨3603, by rfl⟩ : syracuseStep 153749 = 7207) (by norm_num)
theorem B153773 : Blo 99781 153773 := bbase (se 3 (by rfl) ⟨28832, by rfl⟩ : syracuseStep 153773 = 57665) (by norm_num)
theorem B153797 : Blo 99781 153797 := bbase (se 4 (by rfl) ⟨14418, by rfl⟩ : syracuseStep 153797 = 28837) (by norm_num)
theorem B153821 : Blo 99781 153821 := bbase (se 3 (by rfl) ⟨28841, by rfl⟩ : syracuseStep 153821 = 57683) (by norm_num)
theorem B153845 : Blo 99781 153845 := bbase (se 5 (by rfl) ⟨7211, by rfl⟩ : syracuseStep 153845 = 14423) (by norm_num)
theorem B153869 : Blo 99781 153869 := bbase (se 3 (by rfl) ⟨28850, by rfl⟩ : syracuseStep 153869 = 57701) (by norm_num)
theorem B121117 : Blo 99781 121117 := bbase (se 3 (by rfl) ⟨22709, by rfl⟩ : syracuseStep 121117 = 45419) (by norm_num)
theorem B153893 : Blo 99781 153893 := bbase (se 4 (by rfl) ⟨14427, by rfl⟩ : syracuseStep 153893 = 28855) (by norm_num)
theorem B153917 : Blo 99781 153917 := bbase (se 3 (by rfl) ⟨28859, by rfl⟩ : syracuseStep 153917 = 57719) (by norm_num)
theorem B153941 : Blo 99781 153941 := bbase (se 10 (by rfl) ⟨225, by rfl⟩ : syracuseStep 153941 = 451) (by norm_num)
theorem B285029 : Blo 99781 285029 := bbase (se 4 (by rfl) ⟨26721, by rfl⟩ : syracuseStep 285029 = 53443) (by norm_num)
theorem B153965 : Blo 99781 153965 := bbase (se 3 (by rfl) ⟨28868, by rfl⟩ : syracuseStep 153965 = 57737) (by norm_num)
theorem B153989 : Blo 99781 153989 := bbase (se 4 (by rfl) ⟨14436, by rfl⟩ : syracuseStep 153989 = 28873) (by norm_num)
theorem B154013 : Blo 99781 154013 := bbase (se 3 (by rfl) ⟨28877, by rfl⟩ : syracuseStep 154013 = 57755) (by norm_num)
theorem B154037 : Blo 99781 154037 := bbase (se 5 (by rfl) ⟨7220, by rfl⟩ : syracuseStep 154037 = 14441) (by norm_num)
theorem B219581 : Blo 99781 219581 := bbase (se 3 (by rfl) ⟨41171, by rfl⟩ : syracuseStep 219581 = 82343) (by norm_num)
theorem B121285 : Blo 99781 121285 := bbase (se 4 (by rfl) ⟨11370, by rfl⟩ : syracuseStep 121285 = 22741) (by norm_num)
theorem B154061 : Blo 99781 154061 := bbase (se 3 (by rfl) ⟨28886, by rfl⟩ : syracuseStep 154061 = 57773) (by norm_num)
theorem B154085 : Blo 99781 154085 := bbase (se 4 (by rfl) ⟨14445, by rfl⟩ : syracuseStep 154085 = 28891) (by norm_num)
theorem B154109 : Blo 99781 154109 := bbase (se 3 (by rfl) ⟨28895, by rfl⟩ : syracuseStep 154109 = 57791) (by norm_num)
theorem B154133 : Blo 99781 154133 := bbase (se 6 (by rfl) ⟨3612, by rfl⟩ : syracuseStep 154133 = 7225) (by norm_num)
theorem B285221 : Blo 99781 285221 := bbase (se 4 (by rfl) ⟨26739, by rfl⟩ : syracuseStep 285221 = 53479) (by norm_num)
theorem B154157 : Blo 99781 154157 := bbase (se 3 (by rfl) ⟨28904, by rfl⟩ : syracuseStep 154157 = 57809) (by norm_num)
theorem B154181 : Blo 99781 154181 := bbase (se 4 (by rfl) ⟨14454, by rfl⟩ : syracuseStep 154181 = 28909) (by norm_num)
theorem B154205 : Blo 99781 154205 := bbase (se 3 (by rfl) ⟨28913, by rfl⟩ : syracuseStep 154205 = 57827) (by norm_num)
theorem B154229 : Blo 99781 154229 := bbase (se 5 (by rfl) ⟨7229, by rfl⟩ : syracuseStep 154229 = 14459) (by norm_num)
theorem B121481 : Blo 99781 121481 := bbase (se 2 (by rfl) ⟨45555, by rfl⟩ : syracuseStep 121481 = 91111) (by norm_num)
theorem B154253 : Blo 99781 154253 := bbase (se 3 (by rfl) ⟨28922, by rfl⟩ : syracuseStep 154253 = 57845) (by norm_num)
theorem B154277 : Blo 99781 154277 := bbase (se 4 (by rfl) ⟨14463, by rfl⟩ : syracuseStep 154277 = 28927) (by norm_num)
theorem B154301 : Blo 99781 154301 := bbase (se 3 (by rfl) ⟨28931, by rfl⟩ : syracuseStep 154301 = 57863) (by norm_num)
theorem B252629 : Blo 99781 252629 := bbase (se 7 (by rfl) ⟨2960, by rfl⟩ : syracuseStep 252629 = 5921) (by norm_num)
theorem B154325 : Blo 99781 154325 := bbase (se 7 (by rfl) ⟨1808, by rfl⟩ : syracuseStep 154325 = 3617) (by norm_num)
theorem B154349 : Blo 99781 154349 := bbase (se 3 (by rfl) ⟨28940, by rfl⟩ : syracuseStep 154349 = 57881) (by norm_num)
theorem B154373 : Blo 99781 154373 := bbase (se 4 (by rfl) ⟨14472, by rfl⟩ : syracuseStep 154373 = 28945) (by norm_num)
theorem B154397 : Blo 99781 154397 := bbase (se 3 (by rfl) ⟨28949, by rfl⟩ : syracuseStep 154397 = 57899) (by norm_num)
theorem B187181 : Blo 99781 187181 := bbase (se 3 (by rfl) ⟨35096, by rfl⟩ : syracuseStep 187181 = 70193) (by norm_num)
theorem B154421 : Blo 99781 154421 := bbase (se 5 (by rfl) ⟨7238, by rfl⟩ : syracuseStep 154421 = 14477) (by norm_num)
theorem B154445 : Blo 99781 154445 := bbase (se 3 (by rfl) ⟨28958, by rfl⟩ : syracuseStep 154445 = 57917) (by norm_num)
theorem B154469 : Blo 99781 154469 := bbase (se 4 (by rfl) ⟨14481, by rfl⟩ : syracuseStep 154469 = 28963) (by norm_num)
theorem B154493 : Blo 99781 154493 := bbase (se 3 (by rfl) ⟨28967, by rfl⟩ : syracuseStep 154493 = 57935) (by norm_num)
theorem B252821 : Blo 99781 252821 := bbase (se 6 (by rfl) ⟨5925, by rfl⟩ : syracuseStep 252821 = 11851) (by norm_num)
theorem B154517 : Blo 99781 154517 := bbase (se 6 (by rfl) ⟨3621, by rfl⟩ : syracuseStep 154517 = 7243) (by norm_num)
theorem B154541 : Blo 99781 154541 := bbase (se 3 (by rfl) ⟨28976, by rfl⟩ : syracuseStep 154541 = 57953) (by norm_num)
theorem B514997 : Blo 99781 514997 := bbase (se 5 (by rfl) ⟨24140, by rfl⟩ : syracuseStep 514997 = 48281) (by norm_num)
theorem B154565 : Blo 99781 154565 := bbase (se 4 (by rfl) ⟨14490, by rfl⟩ : syracuseStep 154565 = 28981) (by norm_num)
theorem B154589 : Blo 99781 154589 := bbase (se 3 (by rfl) ⟨28985, by rfl⟩ : syracuseStep 154589 = 57971) (by norm_num)
theorem B154613 : Blo 99781 154613 := bbase (se 5 (by rfl) ⟨7247, by rfl⟩ : syracuseStep 154613 = 14495) (by norm_num)
theorem B154637 : Blo 99781 154637 := bbase (se 3 (by rfl) ⟨28994, by rfl⟩ : syracuseStep 154637 = 57989) (by norm_num)
theorem B154661 : Blo 99781 154661 := bbase (se 4 (by rfl) ⟨14499, by rfl⟩ : syracuseStep 154661 = 28999) (by norm_num)
theorem B154685 : Blo 99781 154685 := bbase (se 3 (by rfl) ⟨29003, by rfl⟩ : syracuseStep 154685 = 58007) (by norm_num)
theorem B154709 : Blo 99781 154709 := bbase (se 8 (by rfl) ⟨906, by rfl⟩ : syracuseStep 154709 = 1813) (by norm_num)
theorem B154733 : Blo 99781 154733 := bbase (se 3 (by rfl) ⟨29012, by rfl⟩ : syracuseStep 154733 = 58025) (by norm_num)
theorem B154757 : Blo 99781 154757 := bbase (se 4 (by rfl) ⟨14508, by rfl⟩ : syracuseStep 154757 = 29017) (by norm_num)
theorem B154781 : Blo 99781 154781 := bbase (se 3 (by rfl) ⟨29021, by rfl⟩ : syracuseStep 154781 = 58043) (by norm_num)
theorem B220333 : Blo 99781 220333 := bbase (se 3 (by rfl) ⟨41312, by rfl⟩ : syracuseStep 220333 = 82625) (by norm_num)
theorem B154805 : Blo 99781 154805 := bbase (se 5 (by rfl) ⟨7256, by rfl⟩ : syracuseStep 154805 = 14513) (by norm_num)
theorem B154829 : Blo 99781 154829 := bbase (se 3 (by rfl) ⟨29030, by rfl⟩ : syracuseStep 154829 = 58061) (by norm_num)
theorem B154853 : Blo 99781 154853 := bbase (se 4 (by rfl) ⟨14517, by rfl⟩ : syracuseStep 154853 = 29035) (by norm_num)
theorem B253165 : Blo 99781 253165 := bbase (se 3 (by rfl) ⟨47468, by rfl⟩ : syracuseStep 253165 = 94937) (by norm_num)
theorem B154877 : Blo 99781 154877 := bbase (se 3 (by rfl) ⟨29039, by rfl⟩ : syracuseStep 154877 = 58079) (by norm_num)
theorem B154901 : Blo 99781 154901 := bbase (se 6 (by rfl) ⟨3630, by rfl⟩ : syracuseStep 154901 = 7261) (by norm_num)
theorem B154925 : Blo 99781 154925 := bbase (se 3 (by rfl) ⟨29048, by rfl⟩ : syracuseStep 154925 = 58097) (by norm_num)
theorem B220477 : Blo 99781 220477 := bbase (se 3 (by rfl) ⟨41339, by rfl⟩ : syracuseStep 220477 = 82679) (by norm_num)
theorem B154949 : Blo 99781 154949 := bbase (se 4 (by rfl) ⟨14526, by rfl⟩ : syracuseStep 154949 = 29053) (by norm_num)
theorem B1170773 : Blo 99781 1170773 := bbase (se 11 (by rfl) ⟨857, by rfl⟩ : syracuseStep 1170773 = 1715) (by norm_num)
theorem B253277 : Blo 99781 253277 := bbase (se 3 (by rfl) ⟨47489, by rfl⟩ : syracuseStep 253277 = 94979) (by norm_num)
theorem B154973 : Blo 99781 154973 := bbase (se 3 (by rfl) ⟨29057, by rfl⟩ : syracuseStep 154973 = 58115) (by norm_num)
theorem B875893 : Blo 99781 875893 := bbase (se 5 (by rfl) ⟨41057, by rfl⟩ : syracuseStep 875893 = 82115) (by norm_num)
theorem B154997 : Blo 99781 154997 := bbase (se 5 (by rfl) ⟨7265, by rfl⟩ : syracuseStep 154997 = 14531) (by norm_num)
theorem B155021 : Blo 99781 155021 := bbase (se 3 (by rfl) ⟨29066, by rfl⟩ : syracuseStep 155021 = 58133) (by norm_num)
theorem B155045 : Blo 99781 155045 := bbase (se 4 (by rfl) ⟨14535, by rfl⟩ : syracuseStep 155045 = 29071) (by norm_num)
theorem B155069 : Blo 99781 155069 := bbase (se 3 (by rfl) ⟨29075, by rfl⟩ : syracuseStep 155069 = 58151) (by norm_num)
theorem B482773 : Blo 99781 482773 := bbase (se 7 (by rfl) ⟨5657, by rfl⟩ : syracuseStep 482773 = 11315) (by norm_num)
theorem B155093 : Blo 99781 155093 := bbase (se 7 (by rfl) ⟨1817, by rfl⟩ : syracuseStep 155093 = 3635) (by norm_num)
theorem B155117 : Blo 99781 155117 := bbase (se 3 (by rfl) ⟨29084, by rfl⟩ : syracuseStep 155117 = 58169) (by norm_num)
theorem B286213 : Blo 99781 286213 := bbase (se 4 (by rfl) ⟨26832, by rfl⟩ : syracuseStep 286213 = 53665) (by norm_num)
theorem B155141 : Blo 99781 155141 := bbase (se 4 (by rfl) ⟨14544, by rfl⟩ : syracuseStep 155141 = 29089) (by norm_num)
theorem B384533 : Blo 99781 384533 := bbase (se 6 (by rfl) ⟨9012, by rfl⟩ : syracuseStep 384533 = 18025) (by norm_num)
theorem B253469 : Blo 99781 253469 := bbase (se 3 (by rfl) ⟨47525, by rfl⟩ : syracuseStep 253469 = 95051) (by norm_num)
theorem B155165 : Blo 99781 155165 := bbase (se 3 (by rfl) ⟨29093, by rfl⟩ : syracuseStep 155165 = 58187) (by norm_num)
theorem B155189 : Blo 99781 155189 := bbase (se 5 (by rfl) ⟨7274, by rfl⟩ : syracuseStep 155189 = 14549) (by norm_num)
theorem B155213 : Blo 99781 155213 := bbase (se 3 (by rfl) ⟨29102, by rfl⟩ : syracuseStep 155213 = 58205) (by norm_num)
theorem B155237 : Blo 99781 155237 := bbase (se 4 (by rfl) ⟨14553, by rfl⟩ : syracuseStep 155237 = 29107) (by norm_num)
theorem B155261 : Blo 99781 155261 := bbase (se 3 (by rfl) ⟨29111, by rfl⟩ : syracuseStep 155261 = 58223) (by norm_num)
theorem B155285 : Blo 99781 155285 := bbase (se 6 (by rfl) ⟨3639, by rfl⟩ : syracuseStep 155285 = 7279) (by norm_num)
theorem B155309 : Blo 99781 155309 := bbase (se 3 (by rfl) ⟨29120, by rfl⟩ : syracuseStep 155309 = 58241) (by norm_num)
theorem B220853 : Blo 99781 220853 := bbase (se 5 (by rfl) ⟨10352, by rfl⟩ : syracuseStep 220853 = 20705) (by norm_num)
theorem B155333 : Blo 99781 155333 := bbase (se 4 (by rfl) ⟨14562, by rfl⟩ : syracuseStep 155333 = 29125) (by norm_num)
theorem B155357 : Blo 99781 155357 := bbase (se 3 (by rfl) ⟨29129, by rfl⟩ : syracuseStep 155357 = 58259) (by norm_num)
theorem B351989 : Blo 99781 351989 := bbase (se 5 (by rfl) ⟨16499, by rfl⟩ : syracuseStep 351989 = 32999) (by norm_num)
theorem B155381 : Blo 99781 155381 := bbase (se 5 (by rfl) ⟨7283, by rfl⟩ : syracuseStep 155381 = 14567) (by norm_num)
theorem B155405 : Blo 99781 155405 := bbase (se 3 (by rfl) ⟨29138, by rfl⟩ : syracuseStep 155405 = 58277) (by norm_num)
theorem B155429 : Blo 99781 155429 := bbase (se 4 (by rfl) ⟨14571, by rfl⟩ : syracuseStep 155429 = 29143) (by norm_num)
theorem B384821 : Blo 99781 384821 := bbase (se 5 (by rfl) ⟨18038, by rfl⟩ : syracuseStep 384821 = 36077) (by norm_num)
theorem B155453 : Blo 99781 155453 := bbase (se 3 (by rfl) ⟨29147, by rfl⟩ : syracuseStep 155453 = 58295) (by norm_num)
theorem B155477 : Blo 99781 155477 := bbase (se 9 (by rfl) ⟨455, by rfl⟩ : syracuseStep 155477 = 911) (by norm_num)
theorem B155501 : Blo 99781 155501 := bbase (se 3 (by rfl) ⟨29156, by rfl⟩ : syracuseStep 155501 = 58313) (by norm_num)
theorem B253813 : Blo 99781 253813 := bbase (se 5 (by rfl) ⟨11897, by rfl⟩ : syracuseStep 253813 = 23795) (by norm_num)
theorem B155525 : Blo 99781 155525 := bbase (se 4 (by rfl) ⟨14580, by rfl⟩ : syracuseStep 155525 = 29161) (by norm_num)
theorem B155549 : Blo 99781 155549 := bbase (se 3 (by rfl) ⟨29165, by rfl⟩ : syracuseStep 155549 = 58331) (by norm_num)
theorem B155573 : Blo 99781 155573 := bbase (se 5 (by rfl) ⟨7292, by rfl⟩ : syracuseStep 155573 = 14585) (by norm_num)
theorem B155597 : Blo 99781 155597 := bbase (se 3 (by rfl) ⟨29174, by rfl⟩ : syracuseStep 155597 = 58349) (by norm_num)
theorem B253925 : Blo 99781 253925 := bbase (se 4 (by rfl) ⟨23805, by rfl⟩ : syracuseStep 253925 = 47611) (by norm_num)
theorem B155621 : Blo 99781 155621 := bbase (se 4 (by rfl) ⟨14589, by rfl⟩ : syracuseStep 155621 = 29179) (by norm_num)
theorem B155645 : Blo 99781 155645 := bbase (se 3 (by rfl) ⟨29183, by rfl⟩ : syracuseStep 155645 = 58367) (by norm_num)
theorem B155669 : Blo 99781 155669 := bbase (se 6 (by rfl) ⟨3648, by rfl⟩ : syracuseStep 155669 = 7297) (by norm_num)
theorem B221221 : Blo 99781 221221 := bbase (se 4 (by rfl) ⟨20739, by rfl⟩ : syracuseStep 221221 = 41479) (by norm_num)
theorem B254117 : Blo 99781 254117 := bbase (se 4 (by rfl) ⟨23823, by rfl⟩ : syracuseStep 254117 = 47647) (by norm_num)
theorem B123053 : Blo 99781 123053 := bbase (se 3 (by rfl) ⟨23072, by rfl⟩ : syracuseStep 123053 = 46145) (by norm_num)
theorem B516293 : Blo 99781 516293 := bbase (se 4 (by rfl) ⟨48402, by rfl⟩ : syracuseStep 516293 = 96805) (by norm_num)
theorem B123077 : Blo 99781 123077 := bbase (se 4 (by rfl) ⟨11538, by rfl⟩ : syracuseStep 123077 = 23077) (by norm_num)
theorem B123373 : Blo 99781 123373 := bbase (se 3 (by rfl) ⟨23132, by rfl⟩ : syracuseStep 123373 = 46265) (by norm_num)
theorem B123385 : Blo 99781 123385 := bbase (se 2 (by rfl) ⟨46269, by rfl⟩ : syracuseStep 123385 = 92539) (by norm_num)
theorem B254461 : Blo 99781 254461 := bbase (se 3 (by rfl) ⟨47711, by rfl⟩ : syracuseStep 254461 = 95423) (by norm_num)
theorem B287317 : Blo 99781 287317 := bbase (se 8 (by rfl) ⟨1683, by rfl⟩ : syracuseStep 287317 = 3367) (by norm_num)
theorem B254573 : Blo 99781 254573 := bbase (se 3 (by rfl) ⟨47732, by rfl⟩ : syracuseStep 254573 = 95465) (by norm_num)
theorem B647797 : Blo 99781 647797 := bbase (se 5 (by rfl) ⟨30365, by rfl⟩ : syracuseStep 647797 = 60731) (by norm_num)
theorem B123557 : Blo 99781 123557 := bbase (se 4 (by rfl) ⟨11583, by rfl⟩ : syracuseStep 123557 = 23167) (by norm_num)
theorem B123673 : Blo 99781 123673 := bbase (se 2 (by rfl) ⟨46377, by rfl⟩ : syracuseStep 123673 = 92755) (by norm_num)
theorem B254765 : Blo 99781 254765 := bbase (se 3 (by rfl) ⟨47768, by rfl⟩ : syracuseStep 254765 = 95537) (by norm_num)
theorem B123769 : Blo 99781 123769 := bbase (se 2 (by rfl) ⟨46413, by rfl⟩ : syracuseStep 123769 = 92827) (by norm_num)
theorem B386005 : Blo 99781 386005 := bbase (se 7 (by rfl) ⟨4523, by rfl⟩ : syracuseStep 386005 = 9047) (by norm_num)
theorem B123913 : Blo 99781 123913 := bbase (se 2 (by rfl) ⟨46467, by rfl⟩ : syracuseStep 123913 = 92935) (by norm_num)
theorem B2057237 : Blo 99781 2057237 := bbase (se 6 (by rfl) ⟨48216, by rfl⟩ : syracuseStep 2057237 = 96433) (by norm_num)
theorem B189533 : Blo 99781 189533 := bbase (se 3 (by rfl) ⟨35537, by rfl⟩ : syracuseStep 189533 = 71075) (by norm_num)
theorem B123997 : Blo 99781 123997 := bbase (se 3 (by rfl) ⟨23249, by rfl⟩ : syracuseStep 123997 = 46499) (by norm_num)
theorem B255109 : Blo 99781 255109 := bbase (se 4 (by rfl) ⟨23916, by rfl⟩ : syracuseStep 255109 = 47833) (by norm_num)
theorem B189677 : Blo 99781 189677 := bbase (se 3 (by rfl) ⟨35564, by rfl⟩ : syracuseStep 189677 = 71129) (by norm_num)
theorem B255221 : Blo 99781 255221 := bbase (se 5 (by rfl) ⟨11963, by rfl⟩ : syracuseStep 255221 = 23927) (by norm_num)
theorem B386309 : Blo 99781 386309 := bbase (se 4 (by rfl) ⟨36216, by rfl⟩ : syracuseStep 386309 = 72433) (by norm_num)
theorem B517429 : Blo 99781 517429 := bbase (se 5 (by rfl) ⟨24254, by rfl⟩ : syracuseStep 517429 = 48509) (by norm_num)
theorem B877877 : Blo 99781 877877 := bbase (se 5 (by rfl) ⟨41150, by rfl⟩ : syracuseStep 877877 = 82301) (by norm_num)
theorem B255413 : Blo 99781 255413 := bbase (se 5 (by rfl) ⟨11972, by rfl⟩ : syracuseStep 255413 = 23945) (by norm_num)
theorem B517589 : Blo 99781 517589 := bbase (se 7 (by rfl) ⟨6065, by rfl⟩ : syracuseStep 517589 = 12131) (by norm_num)
theorem B976373 : Blo 99781 976373 := bbase (se 5 (by rfl) ⟨45767, by rfl⟩ : syracuseStep 976373 = 91535) (by norm_num)
theorem B321029 : Blo 99781 321029 := bbase (se 4 (by rfl) ⟨30096, by rfl⟩ : syracuseStep 321029 = 60193) (by norm_num)
theorem B222725 : Blo 99781 222725 := bbase (se 4 (by rfl) ⟨20880, by rfl⟩ : syracuseStep 222725 = 41761) (by norm_num)
theorem B189965 : Blo 99781 189965 := bbase (se 3 (by rfl) ⟨35618, by rfl⟩ : syracuseStep 189965 = 71237) (by norm_num)
theorem B157229 : Blo 99781 157229 := bbase (se 3 (by rfl) ⟨29480, by rfl⟩ : syracuseStep 157229 = 58961) (by norm_num)
theorem B190117 : Blo 99781 190117 := bbase (se 4 (by rfl) ⟨17823, by rfl⟩ : syracuseStep 190117 = 35647) (by norm_num)
theorem B255757 : Blo 99781 255757 := bbase (se 3 (by rfl) ⟨47954, by rfl⟩ : syracuseStep 255757 = 95909) (by norm_num)
theorem B255869 : Blo 99781 255869 := bbase (se 3 (by rfl) ⟨47975, by rfl⟩ : syracuseStep 255869 = 95951) (by norm_num)
theorem B419717 : Blo 99781 419717 := bbase (se 4 (by rfl) ⟨39348, by rfl⟩ : syracuseStep 419717 = 78697) (by norm_num)
theorem B190421 : Blo 99781 190421 := bbase (se 7 (by rfl) ⟨2231, by rfl⟩ : syracuseStep 190421 = 4463) (by norm_num)
theorem B157717 : Blo 99781 157717 := bbase (se 6 (by rfl) ⟨3696, by rfl⟩ : syracuseStep 157717 = 7393) (by norm_num)
theorem B288821 : Blo 99781 288821 := bbase (se 5 (by rfl) ⟨13538, by rfl⟩ : syracuseStep 288821 = 27077) (by norm_num)
theorem B256061 : Blo 99781 256061 := bbase (se 3 (by rfl) ⟨48011, by rfl⟩ : syracuseStep 256061 = 96023) (by norm_num)
theorem B256405 : Blo 99781 256405 := bbase (se 6 (by rfl) ⟨6009, by rfl⟩ : syracuseStep 256405 = 12019) (by norm_num)
theorem B256517 : Blo 99781 256517 := bbase (se 4 (by rfl) ⟨24048, by rfl⟩ : syracuseStep 256517 = 48097) (by norm_num)
theorem B485909 : Blo 99781 485909 := bbase (se 6 (by rfl) ⟨11388, by rfl⟩ : syracuseStep 485909 = 22777) (by norm_num)
theorem B125633 : Blo 99781 125633 := bbase (se 2 (by rfl) ⟨47112, by rfl⟩ : syracuseStep 125633 = 94225) (by norm_num)
theorem B191173 : Blo 99781 191173 := bbase (se 4 (by rfl) ⟨17922, by rfl⟩ : syracuseStep 191173 = 35845) (by norm_num)
theorem B256709 : Blo 99781 256709 := bbase (se 4 (by rfl) ⟨24066, by rfl⟩ : syracuseStep 256709 = 48133) (by norm_num)
theorem B518885 : Blo 99781 518885 := bbase (se 4 (by rfl) ⟨48645, by rfl⟩ : syracuseStep 518885 = 97291) (by norm_num)
theorem B125669 : Blo 99781 125669 := bbase (se 4 (by rfl) ⟨11781, by rfl⟩ : syracuseStep 125669 = 23563) (by norm_num)
theorem B322309 : Blo 99781 322309 := bbase (se 4 (by rfl) ⟨30216, by rfl⟩ : syracuseStep 322309 = 60433) (by norm_num)
theorem B191317 : Blo 99781 191317 := bbase (se 9 (by rfl) ⟨560, by rfl⟩ : syracuseStep 191317 = 1121) (by norm_num)
theorem B191477 : Blo 99781 191477 := bbase (se 5 (by rfl) ⟨8975, by rfl⟩ : syracuseStep 191477 = 17951) (by norm_num)
theorem B257053 : Blo 99781 257053 := bbase (se 3 (by rfl) ⟨48197, by rfl⟩ : syracuseStep 257053 = 96395) (by norm_num)
theorem B191621 : Blo 99781 191621 := bbase (se 4 (by rfl) ⟨17964, by rfl⟩ : syracuseStep 191621 = 35929) (by norm_num)
theorem B257165 : Blo 99781 257165 := bbase (se 3 (by rfl) ⟨48218, by rfl⟩ : syracuseStep 257165 = 96437) (by norm_num)
theorem B224549 : Blo 99781 224549 := bbase (se 4 (by rfl) ⟨21051, by rfl⟩ : syracuseStep 224549 = 42103) (by norm_num)
theorem B388421 : Blo 99781 388421 := bbase (se 4 (by rfl) ⟨36414, by rfl⟩ : syracuseStep 388421 = 72829) (by norm_num)
theorem B257357 : Blo 99781 257357 := bbase (se 3 (by rfl) ⟨48254, by rfl⟩ : syracuseStep 257357 = 96509) (by norm_num)
theorem B126289 : Blo 99781 126289 := bbase (se 2 (by rfl) ⟨47358, by rfl⟩ : syracuseStep 126289 = 94717) (by norm_num)
theorem B224621 : Blo 99781 224621 := bbase (se 3 (by rfl) ⟨42116, by rfl⟩ : syracuseStep 224621 = 84233) (by norm_num)
theorem B191909 : Blo 99781 191909 := bbase (se 4 (by rfl) ⟨17991, by rfl⟩ : syracuseStep 191909 = 35983) (by norm_num)
theorem B224693 : Blo 99781 224693 := bbase (se 5 (by rfl) ⟨10532, by rfl⟩ : syracuseStep 224693 = 21065) (by norm_num)
theorem B126461 : Blo 99781 126461 := bbase (se 3 (by rfl) ⟨23711, by rfl⟩ : syracuseStep 126461 = 47423) (by norm_num)
theorem B224765 : Blo 99781 224765 := bbase (se 3 (by rfl) ⟨42143, by rfl⟩ : syracuseStep 224765 = 84287) (by norm_num)
theorem B126517 : Blo 99781 126517 := bbase (se 5 (by rfl) ⟨5930, by rfl⟩ : syracuseStep 126517 = 11861) (by norm_num)
theorem B192061 : Blo 99781 192061 := bbase (se 3 (by rfl) ⟨36011, by rfl⟩ : syracuseStep 192061 = 72023) (by norm_num)
theorem B224837 : Blo 99781 224837 := bbase (se 4 (by rfl) ⟨21078, by rfl⟩ : syracuseStep 224837 = 42157) (by norm_num)
theorem B159301 : Blo 99781 159301 := bbase (se 4 (by rfl) ⟨14934, by rfl⟩ : syracuseStep 159301 = 29869) (by norm_num)
theorem B290405 : Blo 99781 290405 := bbase (se 4 (by rfl) ⟨27225, by rfl⟩ : syracuseStep 290405 = 54451) (by norm_num)
theorem B388709 : Blo 99781 388709 := bbase (se 4 (by rfl) ⟨36441, by rfl⟩ : syracuseStep 388709 = 72883) (by norm_num)
theorem B224909 : Blo 99781 224909 := bbase (se 3 (by rfl) ⟨42170, by rfl⟩ : syracuseStep 224909 = 84341) (by norm_num)
theorem B126613 : Blo 99781 126613 := bbase (se 6 (by rfl) ⟨2967, by rfl⟩ : syracuseStep 126613 = 5935) (by norm_num)
theorem B781973 : Blo 99781 781973 := bbase (se 6 (by rfl) ⟨18327, by rfl⟩ : syracuseStep 781973 = 36655) (by norm_num)
theorem B257701 : Blo 99781 257701 := bbase (se 4 (by rfl) ⟨24159, by rfl⟩ : syracuseStep 257701 = 48319) (by norm_num)
theorem B224981 : Blo 99781 224981 := bbase (se 7 (by rfl) ⟨2636, by rfl⟩ : syracuseStep 224981 = 5273) (by norm_num)
theorem B257813 : Blo 99781 257813 := bbase (se 6 (by rfl) ⟨6042, by rfl⟩ : syracuseStep 257813 = 12085) (by norm_num)
theorem B225053 : Blo 99781 225053 := bbase (se 3 (by rfl) ⟨42197, by rfl⟩ : syracuseStep 225053 = 84395) (by norm_num)
theorem B126785 : Blo 99781 126785 := bbase (se 2 (by rfl) ⟨47544, by rfl⟩ : syracuseStep 126785 = 95089) (by norm_num)
theorem B225125 : Blo 99781 225125 := bbase (se 4 (by rfl) ⟨21105, by rfl⟩ : syracuseStep 225125 = 42211) (by norm_num)
theorem B192365 : Blo 99781 192365 := bbase (se 3 (by rfl) ⟨36068, by rfl⟩ : syracuseStep 192365 = 72137) (by norm_num)
theorem B126841 : Blo 99781 126841 := bbase (se 2 (by rfl) ⟨47565, by rfl⟩ : syracuseStep 126841 = 95131) (by norm_num)
theorem B225197 : Blo 99781 225197 := bbase (se 3 (by rfl) ⟨42224, by rfl⟩ : syracuseStep 225197 = 84449) (by norm_num)
theorem B258005 : Blo 99781 258005 := bbase (se 7 (by rfl) ⟨3023, by rfl⟩ : syracuseStep 258005 = 6047) (by norm_num)
theorem B126937 : Blo 99781 126937 := bbase (se 2 (by rfl) ⟨47601, by rfl⟩ : syracuseStep 126937 = 95203) (by norm_num)
theorem B225269 : Blo 99781 225269 := bbase (se 5 (by rfl) ⟨10559, by rfl⟩ : syracuseStep 225269 = 21119) (by norm_num)
theorem B520181 : Blo 99781 520181 := bbase (se 5 (by rfl) ⟨24383, by rfl⟩ : syracuseStep 520181 = 48767) (by norm_num)
theorem B127013 : Blo 99781 127013 := bbase (se 4 (by rfl) ⟨11907, by rfl⟩ : syracuseStep 127013 = 23815) (by norm_num)
theorem B225341 : Blo 99781 225341 := bbase (se 3 (by rfl) ⟨42251, by rfl⟩ : syracuseStep 225341 = 84503) (by norm_num)
theorem B323669 : Blo 99781 323669 := bbase (se 8 (by rfl) ⟨1896, by rfl⟩ : syracuseStep 323669 = 3793) (by norm_num)
theorem B225413 : Blo 99781 225413 := bbase (se 4 (by rfl) ⟨21132, by rfl⟩ : syracuseStep 225413 = 42265) (by norm_num)
theorem B127109 : Blo 99781 127109 := bbase (se 4 (by rfl) ⟨11916, by rfl⟩ : syracuseStep 127109 = 23833) (by norm_num)
theorem B127165 : Blo 99781 127165 := bbase (se 3 (by rfl) ⟨23843, by rfl⟩ : syracuseStep 127165 = 47687) (by norm_num)
theorem B225485 : Blo 99781 225485 := bbase (se 3 (by rfl) ⟨42278, by rfl⟩ : syracuseStep 225485 = 84557) (by norm_num)
theorem B323797 : Blo 99781 323797 := bbase (se 7 (by rfl) ⟨3794, by rfl⟩ : syracuseStep 323797 = 7589) (by norm_num)
theorem B291077 : Blo 99781 291077 := bbase (se 4 (by rfl) ⟨27288, by rfl⟩ : syracuseStep 291077 = 54577) (by norm_num)
theorem B225557 : Blo 99781 225557 := bbase (se 6 (by rfl) ⟨5286, by rfl⟩ : syracuseStep 225557 = 10573) (by norm_num)
theorem B127261 : Blo 99781 127261 := bbase (se 3 (by rfl) ⟨23861, by rfl⟩ : syracuseStep 127261 = 47723) (by norm_num)
theorem B258349 : Blo 99781 258349 := bbase (se 3 (by rfl) ⟨48440, by rfl⟩ : syracuseStep 258349 = 96881) (by norm_num)
theorem B225629 : Blo 99781 225629 := bbase (se 3 (by rfl) ⟨42305, by rfl⟩ : syracuseStep 225629 = 84611) (by norm_num)
theorem B258461 : Blo 99781 258461 := bbase (se 3 (by rfl) ⟨48461, by rfl⟩ : syracuseStep 258461 = 96923) (by norm_num)
theorem B225701 : Blo 99781 225701 := bbase (se 4 (by rfl) ⟨21159, by rfl⟩ : syracuseStep 225701 = 42319) (by norm_num)
theorem B127433 : Blo 99781 127433 := bbase (se 2 (by rfl) ⟨47787, by rfl⟩ : syracuseStep 127433 = 95575) (by norm_num)
theorem B324053 : Blo 99781 324053 := bbase (se 7 (by rfl) ⟨3797, by rfl⟩ : syracuseStep 324053 = 7595) (by norm_num)
theorem B225773 : Blo 99781 225773 := bbase (se 3 (by rfl) ⟨42332, by rfl⟩ : syracuseStep 225773 = 84665) (by norm_num)
theorem B127489 : Blo 99781 127489 := bbase (se 2 (by rfl) ⟨47808, by rfl⟩ : syracuseStep 127489 = 95617) (by norm_num)
theorem B160309 : Blo 99781 160309 := bbase (se 5 (by rfl) ⟨7514, by rfl⟩ : syracuseStep 160309 = 15029) (by norm_num)
theorem B225845 : Blo 99781 225845 := bbase (se 5 (by rfl) ⟨10586, by rfl⟩ : syracuseStep 225845 = 21173) (by norm_num)
theorem B193117 : Blo 99781 193117 := bbase (se 3 (by rfl) ⟨36209, by rfl⟩ : syracuseStep 193117 = 72419) (by norm_num)
theorem B258653 : Blo 99781 258653 := bbase (se 3 (by rfl) ⟨48497, by rfl⟩ : syracuseStep 258653 = 96995) (by norm_num)
theorem B127585 : Blo 99781 127585 := bbase (se 2 (by rfl) ⟨47844, by rfl⟩ : syracuseStep 127585 = 95689) (by norm_num)
theorem B225917 : Blo 99781 225917 := bbase (se 3 (by rfl) ⟨42359, by rfl⟩ : syracuseStep 225917 = 84719) (by norm_num)
theorem B291509 : Blo 99781 291509 := bbase (se 5 (by rfl) ⟨13664, by rfl⟩ : syracuseStep 291509 = 27329) (by norm_num)
theorem B225989 : Blo 99781 225989 := bbase (se 4 (by rfl) ⟨21186, by rfl⟩ : syracuseStep 225989 = 42373) (by norm_num)
theorem B193261 : Blo 99781 193261 := bbase (se 3 (by rfl) ⟨36236, by rfl⟩ : syracuseStep 193261 = 72473) (by norm_num)
theorem B389893 : Blo 99781 389893 := bbase (se 4 (by rfl) ⟨36552, by rfl⟩ : syracuseStep 389893 = 73105) (by norm_num)
theorem B226061 : Blo 99781 226061 := bbase (se 3 (by rfl) ⟨42386, by rfl⟩ : syracuseStep 226061 = 84773) (by norm_num)
theorem B127757 : Blo 99781 127757 := bbase (se 3 (by rfl) ⟨23954, by rfl⟩ : syracuseStep 127757 = 47909) (by norm_num)
theorem B127813 : Blo 99781 127813 := bbase (se 4 (by rfl) ⟨11982, by rfl⟩ : syracuseStep 127813 = 23965) (by norm_num)
theorem B226133 : Blo 99781 226133 := bbase (se 9 (by rfl) ⟨662, by rfl⟩ : syracuseStep 226133 = 1325) (by norm_num)
theorem B193421 : Blo 99781 193421 := bbase (se 3 (by rfl) ⟨36266, by rfl⟩ : syracuseStep 193421 = 72533) (by norm_num)
theorem B226205 : Blo 99781 226205 := bbase (se 3 (by rfl) ⟨42413, by rfl⟩ : syracuseStep 226205 = 84827) (by norm_num)
theorem B127909 : Blo 99781 127909 := bbase (se 4 (by rfl) ⟨11991, by rfl⟩ : syracuseStep 127909 = 23983) (by norm_num)
theorem B258997 : Blo 99781 258997 := bbase (se 5 (by rfl) ⟨12140, by rfl⟩ : syracuseStep 258997 = 24281) (by norm_num)
theorem B586709 : Blo 99781 586709 := bbase (se 7 (by rfl) ⟨6875, by rfl⟩ : syracuseStep 586709 = 13751) (by norm_num)
theorem B226277 : Blo 99781 226277 := bbase (se 4 (by rfl) ⟨21213, by rfl⟩ : syracuseStep 226277 = 42427) (by norm_num)
theorem B193565 : Blo 99781 193565 := bbase (se 3 (by rfl) ⟨36293, by rfl⟩ : syracuseStep 193565 = 72587) (by norm_num)
theorem B259109 : Blo 99781 259109 := bbase (se 4 (by rfl) ⟨24291, by rfl⟩ : syracuseStep 259109 = 48583) (by norm_num)
theorem B226349 : Blo 99781 226349 := bbase (se 3 (by rfl) ⟨42440, by rfl⟩ : syracuseStep 226349 = 84881) (by norm_num)
theorem B390197 : Blo 99781 390197 := bbase (se 5 (by rfl) ⟨18290, by rfl⟩ : syracuseStep 390197 = 36581) (by norm_num)
theorem B128065 : Blo 99781 128065 := bbase (se 2 (by rfl) ⟨48024, by rfl⟩ : syracuseStep 128065 = 96049) (by norm_num)
theorem B128081 : Blo 99781 128081 := bbase (se 2 (by rfl) ⟨48030, by rfl⟩ : syracuseStep 128081 = 96061) (by norm_num)
theorem B160861 : Blo 99781 160861 := bbase (se 3 (by rfl) ⟨30161, by rfl⟩ : syracuseStep 160861 = 60323) (by norm_num)
theorem B226421 : Blo 99781 226421 := bbase (se 5 (by rfl) ⟨10613, by rfl⟩ : syracuseStep 226421 = 21227) (by norm_num)
theorem B128137 : Blo 99781 128137 := bbase (se 2 (by rfl) ⟨48051, by rfl⟩ : syracuseStep 128137 = 96103) (by norm_num)
theorem B226493 : Blo 99781 226493 := bbase (se 3 (by rfl) ⟨42467, by rfl⟩ : syracuseStep 226493 = 84935) (by norm_num)
theorem B259301 : Blo 99781 259301 := bbase (se 4 (by rfl) ⟨24309, by rfl⟩ : syracuseStep 259301 = 48619) (by norm_num)
theorem B128233 : Blo 99781 128233 := bbase (se 2 (by rfl) ⟨48087, by rfl⟩ : syracuseStep 128233 = 96175) (by norm_num)
theorem B488693 : Blo 99781 488693 := bbase (se 5 (by rfl) ⟨22907, by rfl⟩ : syracuseStep 488693 = 45815) (by norm_num)
theorem B226565 : Blo 99781 226565 := bbase (se 4 (by rfl) ⟨21240, by rfl⟩ : syracuseStep 226565 = 42481) (by norm_num)
theorem B521477 : Blo 99781 521477 := bbase (se 4 (by rfl) ⟨48888, by rfl⟩ : syracuseStep 521477 = 97777) (by norm_num)
theorem B193853 : Blo 99781 193853 := bbase (se 3 (by rfl) ⟨36347, by rfl⟩ : syracuseStep 193853 = 72695) (by norm_num)
theorem B226637 : Blo 99781 226637 := bbase (se 3 (by rfl) ⟨42494, by rfl⟩ : syracuseStep 226637 = 84989) (by norm_num)
theorem B161117 : Blo 99781 161117 := bbase (se 3 (by rfl) ⟨30209, by rfl⟩ : syracuseStep 161117 = 60419) (by norm_num)
theorem B226709 : Blo 99781 226709 := bbase (se 6 (by rfl) ⟨5313, by rfl⟩ : syracuseStep 226709 = 10627) (by norm_num)
theorem B128405 : Blo 99781 128405 := bbase (se 6 (by rfl) ⟨3009, by rfl⟩ : syracuseStep 128405 = 6019) (by norm_num)
theorem B128413 : Blo 99781 128413 := bbase (se 3 (by rfl) ⟨24077, by rfl⟩ : syracuseStep 128413 = 48155) (by norm_num)
theorem B292261 : Blo 99781 292261 := bbase (se 4 (by rfl) ⟨27399, by rfl⟩ : syracuseStep 292261 = 54799) (by norm_num)
theorem B128461 : Blo 99781 128461 := bbase (se 3 (by rfl) ⟨24086, by rfl⟩ : syracuseStep 128461 = 48173) (by norm_num)
theorem B194005 : Blo 99781 194005 := bbase (se 7 (by rfl) ⟨2273, by rfl⟩ : syracuseStep 194005 = 4547) (by norm_num)
theorem B226781 : Blo 99781 226781 := bbase (se 3 (by rfl) ⟨42521, by rfl⟩ : syracuseStep 226781 = 85043) (by norm_num)
theorem B226853 : Blo 99781 226853 := bbase (se 4 (by rfl) ⟨21267, by rfl⟩ : syracuseStep 226853 = 42535) (by norm_num)
theorem B128557 : Blo 99781 128557 := bbase (se 3 (by rfl) ⟨24104, by rfl⟩ : syracuseStep 128557 = 48209) (by norm_num)
theorem B259645 : Blo 99781 259645 := bbase (se 3 (by rfl) ⟨48683, by rfl⟩ : syracuseStep 259645 = 97367) (by norm_num)
theorem B226925 : Blo 99781 226925 := bbase (se 3 (by rfl) ⟨42548, by rfl⟩ : syracuseStep 226925 = 85097) (by norm_num)
theorem B259757 : Blo 99781 259757 := bbase (se 3 (by rfl) ⟨48704, by rfl⟩ : syracuseStep 259757 = 97409) (by norm_num)
theorem B226997 : Blo 99781 226997 := bbase (se 5 (by rfl) ⟨10640, by rfl⟩ : syracuseStep 226997 = 21281) (by norm_num)
theorem B521909 : Blo 99781 521909 := bbase (se 5 (by rfl) ⟨24464, by rfl⟩ : syracuseStep 521909 = 48929) (by norm_num)
theorem B128729 : Blo 99781 128729 := bbase (se 2 (by rfl) ⟨48273, by rfl⟩ : syracuseStep 128729 = 96547) (by norm_num)
theorem B128741 : Blo 99781 128741 := bbase (se 4 (by rfl) ⟨12069, by rfl⟩ : syracuseStep 128741 = 24139) (by norm_num)
theorem B227069 : Blo 99781 227069 := bbase (se 3 (by rfl) ⟨42575, by rfl⟩ : syracuseStep 227069 = 85151) (by norm_num)
theorem B194309 : Blo 99781 194309 := bbase (se 4 (by rfl) ⟨18216, by rfl⟩ : syracuseStep 194309 = 36433) (by norm_num)
theorem B128785 : Blo 99781 128785 := bbase (se 2 (by rfl) ⟨48294, by rfl⟩ : syracuseStep 128785 = 96589) (by norm_num)
theorem B227141 : Blo 99781 227141 := bbase (se 4 (by rfl) ⟨21294, by rfl⟩ : syracuseStep 227141 = 42589) (by norm_num)
theorem B259949 : Blo 99781 259949 := bbase (se 3 (by rfl) ⟨48740, by rfl⟩ : syracuseStep 259949 = 97481) (by norm_num)
theorem B128881 : Blo 99781 128881 := bbase (se 2 (by rfl) ⟨48330, by rfl⟩ : syracuseStep 128881 = 96661) (by norm_num)
theorem B227213 : Blo 99781 227213 := bbase (se 3 (by rfl) ⟨42602, by rfl⟩ : syracuseStep 227213 = 85205) (by norm_num)
theorem B1963925 : Blo 99781 1963925 := bbase (se 6 (by rfl) ⟨46029, by rfl⟩ : syracuseStep 1963925 = 92059) (by norm_num)
theorem B227285 : Blo 99781 227285 := bbase (se 7 (by rfl) ⟨2663, by rfl⟩ : syracuseStep 227285 = 5327) (by norm_num)
theorem B161821 : Blo 99781 161821 := bbase (se 3 (by rfl) ⟨30341, by rfl⟩ : syracuseStep 161821 = 60683) (by norm_num)
theorem B227357 : Blo 99781 227357 := bbase (se 3 (by rfl) ⟨42629, by rfl⟩ : syracuseStep 227357 = 85259) (by norm_num)
theorem B129053 : Blo 99781 129053 := bbase (se 3 (by rfl) ⟨24197, by rfl⟩ : syracuseStep 129053 = 48395) (by norm_num)
theorem B129109 : Blo 99781 129109 := bbase (se 8 (by rfl) ⟨756, by rfl⟩ : syracuseStep 129109 = 1513) (by norm_num)
theorem B227429 : Blo 99781 227429 := bbase (se 4 (by rfl) ⟨21321, by rfl⟩ : syracuseStep 227429 = 42643) (by norm_num)
theorem B227501 : Blo 99781 227501 := bbase (se 3 (by rfl) ⟨42656, by rfl⟩ : syracuseStep 227501 = 85313) (by norm_num)
theorem B129205 : Blo 99781 129205 := bbase (se 5 (by rfl) ⟨6056, by rfl⟩ : syracuseStep 129205 = 12113) (by norm_num)
theorem B260293 : Blo 99781 260293 := bbase (se 4 (by rfl) ⟨24402, by rfl⟩ : syracuseStep 260293 = 48805) (by norm_num)
theorem B227573 : Blo 99781 227573 := bbase (se 5 (by rfl) ⟨10667, by rfl⟩ : syracuseStep 227573 = 21335) (by norm_num)
theorem B260405 : Blo 99781 260405 := bbase (se 5 (by rfl) ⟨12206, by rfl⟩ : syracuseStep 260405 = 24413) (by norm_num)
theorem B227645 : Blo 99781 227645 := bbase (se 3 (by rfl) ⟨42683, by rfl⟩ : syracuseStep 227645 = 85367) (by norm_num)
theorem B129377 : Blo 99781 129377 := bbase (se 2 (by rfl) ⟨48516, by rfl⟩ : syracuseStep 129377 = 97033) (by norm_num)
theorem B227717 : Blo 99781 227717 := bbase (se 4 (by rfl) ⟨21348, by rfl⟩ : syracuseStep 227717 = 42697) (by norm_num)
theorem B129433 : Blo 99781 129433 := bbase (se 2 (by rfl) ⟨48537, by rfl⟩ : syracuseStep 129433 = 97075) (by norm_num)
theorem B162245 : Blo 99781 162245 := bbase (se 4 (by rfl) ⟨15210, by rfl⟩ : syracuseStep 162245 = 30421) (by norm_num)
theorem B227789 : Blo 99781 227789 := bbase (se 3 (by rfl) ⟨42710, by rfl⟩ : syracuseStep 227789 = 85421) (by norm_num)
theorem B195061 : Blo 99781 195061 := bbase (se 5 (by rfl) ⟨9143, by rfl⟩ : syracuseStep 195061 = 18287) (by norm_num)
theorem B260597 : Blo 99781 260597 := bbase (se 5 (by rfl) ⟨12215, by rfl⟩ : syracuseStep 260597 = 24431) (by norm_num)
theorem B129529 : Blo 99781 129529 := bbase (se 2 (by rfl) ⟨48573, by rfl⟩ : syracuseStep 129529 = 97147) (by norm_num)
theorem B227861 : Blo 99781 227861 := bbase (se 6 (by rfl) ⟨5340, by rfl⟩ : syracuseStep 227861 = 10681) (by norm_num)
theorem B653845 : Blo 99781 653845 := bbase (se 6 (by rfl) ⟨15324, by rfl⟩ : syracuseStep 653845 = 30649) (by norm_num)
theorem B522773 : Blo 99781 522773 := bbase (se 6 (by rfl) ⟨12252, by rfl⟩ : syracuseStep 522773 = 24505) (by norm_num)
theorem B227933 : Blo 99781 227933 := bbase (se 3 (by rfl) ⟨42737, by rfl⟩ : syracuseStep 227933 = 85475) (by norm_num)
theorem B195205 : Blo 99781 195205 := bbase (se 4 (by rfl) ⟨18300, by rfl⟩ : syracuseStep 195205 = 36601) (by norm_num)
theorem B228005 : Blo 99781 228005 := bbase (se 4 (by rfl) ⟨21375, by rfl⟩ : syracuseStep 228005 = 42751) (by norm_num)
theorem B129701 : Blo 99781 129701 := bbase (se 4 (by rfl) ⟨12159, by rfl⟩ : syracuseStep 129701 = 24319) (by norm_num)
theorem B129757 : Blo 99781 129757 := bbase (se 3 (by rfl) ⟨24329, by rfl⟩ : syracuseStep 129757 = 48659) (by norm_num)
theorem B162533 : Blo 99781 162533 := bbase (se 4 (by rfl) ⟨15237, by rfl⟩ : syracuseStep 162533 = 30475) (by norm_num)
theorem B228077 : Blo 99781 228077 := bbase (se 3 (by rfl) ⟨42764, by rfl⟩ : syracuseStep 228077 = 85529) (by norm_num)
theorem B195365 : Blo 99781 195365 := bbase (se 4 (by rfl) ⟨18315, by rfl⟩ : syracuseStep 195365 = 36631) (by norm_num)
theorem B228149 : Blo 99781 228149 := bbase (se 5 (by rfl) ⟨10694, by rfl⟩ : syracuseStep 228149 = 21389) (by norm_num)
theorem B129853 : Blo 99781 129853 := bbase (se 3 (by rfl) ⟨24347, by rfl⟩ : syracuseStep 129853 = 48695) (by norm_num)
theorem B260941 : Blo 99781 260941 := bbase (se 3 (by rfl) ⟨48926, by rfl⟩ : syracuseStep 260941 = 97853) (by norm_num)
theorem B228181 : Blo 99781 228181 := bbase (se 9 (by rfl) ⟨668, by rfl⟩ : syracuseStep 228181 = 1337) (by norm_num)
theorem B326501 : Blo 99781 326501 := bbase (se 4 (by rfl) ⟨30609, by rfl⟩ : syracuseStep 326501 = 61219) (by norm_num)
theorem B228221 : Blo 99781 228221 := bbase (se 3 (by rfl) ⟨42791, by rfl⟩ : syracuseStep 228221 = 85583) (by norm_num)
theorem B195509 : Blo 99781 195509 := bbase (se 5 (by rfl) ⟨9164, by rfl⟩ : syracuseStep 195509 = 18329) (by norm_num)
theorem B261053 : Blo 99781 261053 := bbase (se 3 (by rfl) ⟨48947, by rfl⟩ : syracuseStep 261053 = 97895) (by norm_num)
theorem B228293 : Blo 99781 228293 := bbase (se 4 (by rfl) ⟨21402, by rfl⟩ : syracuseStep 228293 = 42805) (by norm_num)
theorem B162757 : Blo 99781 162757 := bbase (se 4 (by rfl) ⟨15258, by rfl⟩ : syracuseStep 162757 = 30517) (by norm_num)
theorem B130025 : Blo 99781 130025 := bbase (se 2 (by rfl) ⟨48759, by rfl⟩ : syracuseStep 130025 = 97519) (by norm_num)
theorem B457733 : Blo 99781 457733 := bbase (se 4 (by rfl) ⟨42912, by rfl⟩ : syracuseStep 457733 = 85825) (by norm_num)
theorem B228365 : Blo 99781 228365 := bbase (se 3 (by rfl) ⟨42818, by rfl⟩ : syracuseStep 228365 = 85637) (by norm_num)
theorem B130081 : Blo 99781 130081 := bbase (se 2 (by rfl) ⟨48780, by rfl⟩ : syracuseStep 130081 = 97561) (by norm_num)
theorem B228437 : Blo 99781 228437 := bbase (se 8 (by rfl) ⟨1338, by rfl⟩ : syracuseStep 228437 = 2677) (by norm_num)
theorem B392309 : Blo 99781 392309 := bbase (se 5 (by rfl) ⟨18389, by rfl⟩ : syracuseStep 392309 = 36779) (by norm_num)
theorem B261245 : Blo 99781 261245 := bbase (se 3 (by rfl) ⟨48983, by rfl⟩ : syracuseStep 261245 = 97967) (by norm_num)
theorem B130177 : Blo 99781 130177 := bbase (se 2 (by rfl) ⟨48816, by rfl⟩ : syracuseStep 130177 = 97633) (by norm_num)
theorem B228509 : Blo 99781 228509 := bbase (se 3 (by rfl) ⟨42845, by rfl⟩ : syracuseStep 228509 = 85691) (by norm_num)
theorem B195797 : Blo 99781 195797 := bbase (se 7 (by rfl) ⟨2294, by rfl⟩ : syracuseStep 195797 = 4589) (by norm_num)
theorem B228581 : Blo 99781 228581 := bbase (se 4 (by rfl) ⟨21429, by rfl⟩ : syracuseStep 228581 = 42859) (by norm_num)
theorem B163109 : Blo 99781 163109 := bbase (se 4 (by rfl) ⟨15291, by rfl⟩ : syracuseStep 163109 = 30583) (by norm_num)
theorem B228653 : Blo 99781 228653 := bbase (se 3 (by rfl) ⟨42872, by rfl⟩ : syracuseStep 228653 = 85745) (by norm_num)
theorem B130349 : Blo 99781 130349 := bbase (se 3 (by rfl) ⟨24440, by rfl⟩ : syracuseStep 130349 = 48881) (by norm_num)
theorem B130405 : Blo 99781 130405 := bbase (se 4 (by rfl) ⟨12225, by rfl⟩ : syracuseStep 130405 = 24451) (by norm_num)
theorem B195949 : Blo 99781 195949 := bbase (se 3 (by rfl) ⟨36740, by rfl⟩ : syracuseStep 195949 = 73481) (by norm_num)
theorem B228725 : Blo 99781 228725 := bbase (se 5 (by rfl) ⟨10721, by rfl⟩ : syracuseStep 228725 = 21443) (by norm_num)
theorem B392597 : Blo 99781 392597 := bbase (se 6 (by rfl) ⟨9201, by rfl⟩ : syracuseStep 392597 = 18403) (by norm_num)
theorem B228797 : Blo 99781 228797 := bbase (se 3 (by rfl) ⟨42899, by rfl⟩ : syracuseStep 228797 = 85799) (by norm_num)
theorem B130501 : Blo 99781 130501 := bbase (se 4 (by rfl) ⟨12234, by rfl⟩ : syracuseStep 130501 = 24469) (by norm_num)
theorem B261589 : Blo 99781 261589 := bbase (se 7 (by rfl) ⟨3065, by rfl⟩ : syracuseStep 261589 = 6131) (by norm_num)
theorem B228869 : Blo 99781 228869 := bbase (se 4 (by rfl) ⟨21456, by rfl⟩ : syracuseStep 228869 = 42913) (by norm_num)
theorem B261701 : Blo 99781 261701 := bbase (se 4 (by rfl) ⟨24534, by rfl⟩ : syracuseStep 261701 = 49069) (by norm_num)
theorem B228941 : Blo 99781 228941 := bbase (se 3 (by rfl) ⟨42926, by rfl⟩ : syracuseStep 228941 = 85853) (by norm_num)
theorem B130673 : Blo 99781 130673 := bbase (se 2 (by rfl) ⟨49002, by rfl⟩ : syracuseStep 130673 = 98005) (by norm_num)
theorem B229013 : Blo 99781 229013 := bbase (se 6 (by rfl) ⟨5367, by rfl⟩ : syracuseStep 229013 = 10735) (by norm_num)
theorem B196253 : Blo 99781 196253 := bbase (se 3 (by rfl) ⟨36797, by rfl⟩ : syracuseStep 196253 = 73595) (by norm_num)
theorem B130729 : Blo 99781 130729 := bbase (se 2 (by rfl) ⟨49023, by rfl⟩ : syracuseStep 130729 = 98047) (by norm_num)
theorem B229085 : Blo 99781 229085 := bbase (se 3 (by rfl) ⟨42953, by rfl⟩ : syracuseStep 229085 = 85907) (by norm_num)
theorem B261893 : Blo 99781 261893 := bbase (se 4 (by rfl) ⟨24552, by rfl⟩ : syracuseStep 261893 = 49105) (by norm_num)
theorem B130825 : Blo 99781 130825 := bbase (se 2 (by rfl) ⟨49059, by rfl⟩ : syracuseStep 130825 = 98119) (by norm_num)
theorem B229157 : Blo 99781 229157 := bbase (se 4 (by rfl) ⟨21483, by rfl⟩ : syracuseStep 229157 = 42967) (by norm_num)
theorem B524069 : Blo 99781 524069 := bbase (se 4 (by rfl) ⟨49131, by rfl⟩ : syracuseStep 524069 = 98263) (by norm_num)
theorem B1408853 : Blo 99781 1408853 := bbase (se 9 (by rfl) ⟨4127, by rfl⟩ : syracuseStep 1408853 = 8255) (by norm_num)
theorem B229229 : Blo 99781 229229 := bbase (se 3 (by rfl) ⟨42980, by rfl⟩ : syracuseStep 229229 = 85961) (by norm_num)
theorem B229301 : Blo 99781 229301 := bbase (se 5 (by rfl) ⟨10748, by rfl⟩ : syracuseStep 229301 = 21497) (by norm_num)
theorem B130997 : Blo 99781 130997 := bbase (se 5 (by rfl) ⟨6140, by rfl⟩ : syracuseStep 130997 = 12281) (by norm_num)
theorem B131053 : Blo 99781 131053 := bbase (se 3 (by rfl) ⟨24572, by rfl⟩ : syracuseStep 131053 = 49145) (by norm_num)
theorem B557045 : Blo 99781 557045 := bbase (se 5 (by rfl) ⟨26111, by rfl⟩ : syracuseStep 557045 = 52223) (by norm_num)
theorem B229373 : Blo 99781 229373 := bbase (se 3 (by rfl) ⟨43007, by rfl⟩ : syracuseStep 229373 = 86015) (by norm_num)
theorem B294961 : Blo 99781 294961 := bstep (se 2 (by rfl) ⟨110610, by rfl⟩ : syracuseStep 294961 = 221221) B221221
theorem B196739 : Blo 99781 196739 := bstep (se 1 (by rfl) ⟨147554, by rfl⟩ : syracuseStep 196739 = 295109) B295109
theorem B557219 : Blo 99781 557219 := bstep (se 1 (by rfl) ⟨417914, by rfl⟩ : syracuseStep 557219 = 835829) B835829
theorem B229553 : Blo 99781 229553 := bstep (se 2 (by rfl) ⟨86082, by rfl⟩ : syracuseStep 229553 = 172165) B172165
theorem B229571 : Blo 99781 229571 := bstep (se 1 (by rfl) ⟨172178, by rfl⟩ : syracuseStep 229571 = 344357) B344357
theorem B295235 : Blo 99781 295235 := bstep (se 1 (by rfl) ⟨221426, by rfl⟩ : syracuseStep 295235 = 442853) B442853
theorem B328141 : Blo 99781 328141 := bstep (se 3 (by rfl) ⟨61526, by rfl⟩ : syracuseStep 328141 = 123053) B123053
theorem B229841 : Blo 99781 229841 := bstep (se 2 (by rfl) ⟨86190, by rfl⟩ : syracuseStep 229841 = 172381) B172381
theorem B229859 : Blo 99781 229859 := bstep (se 1 (by rfl) ⟨172394, by rfl⟩ : syracuseStep 229859 = 344789) B344789
theorem B295427 : Blo 99781 295427 := bstep (se 1 (by rfl) ⟨221570, by rfl⟩ : syracuseStep 295427 = 443141) B443141
theorem B328205 : Blo 99781 328205 := bstep (se 3 (by rfl) ⟨61538, by rfl⟩ : syracuseStep 328205 = 123077) B123077
theorem B262673 : Blo 99781 262673 := bstep (se 2 (by rfl) ⟨98502, by rfl⟩ : syracuseStep 262673 = 197005) B197005
theorem B1147445 : Blo 99781 1147445 := bstep (se 5 (by rfl) ⟨53786, by rfl⟩ : syracuseStep 1147445 = 107573) B107573
theorem B164435 : Blo 99781 164435 := bstep (se 1 (by rfl) ⟨123326, by rfl⟩ : syracuseStep 164435 = 246653) B246653
theorem B164497 : Blo 99781 164497 := bstep (se 2 (by rfl) ⟨61686, by rfl⟩ : syracuseStep 164497 = 123373) B123373
theorem B164513 : Blo 99781 164513 := bstep (se 2 (by rfl) ⟨61692, by rfl⟩ : syracuseStep 164513 = 123385) B123385
theorem B230129 : Blo 99781 230129 := bstep (se 2 (by rfl) ⟨86298, by rfl⟩ : syracuseStep 230129 = 172597) B172597
theorem B525041 : Blo 99781 525041 := bstep (se 2 (by rfl) ⟨196890, by rfl⟩ : syracuseStep 525041 = 393781) B393781
theorem B230147 : Blo 99781 230147 := bstep (se 1 (by rfl) ⟨172610, by rfl⟩ : syracuseStep 230147 = 345221) B345221
theorem B164771 : Blo 99781 164771 := bstep (se 1 (by rfl) ⟨123578, by rfl⟩ : syracuseStep 164771 = 247157) B247157
theorem B230417 : Blo 99781 230417 := bstep (se 2 (by rfl) ⟨86406, by rfl⟩ : syracuseStep 230417 = 172813) B172813
theorem B164897 : Blo 99781 164897 := bstep (se 2 (by rfl) ⟨61836, by rfl⟩ : syracuseStep 164897 = 123673) B123673
theorem B230435 : Blo 99781 230435 := bstep (se 1 (by rfl) ⟨172826, by rfl⟩ : syracuseStep 230435 = 345653) B345653
theorem B165025 : Blo 99781 165025 := bstep (se 2 (by rfl) ⟨61884, by rfl⟩ : syracuseStep 165025 = 123769) B123769
theorem B460081 : Blo 99781 460081 := bstep (se 2 (by rfl) ⟨172530, by rfl⟩ : syracuseStep 460081 = 345061) B345061
theorem B230705 : Blo 99781 230705 := bstep (se 2 (by rfl) ⟨86514, by rfl⟩ : syracuseStep 230705 = 173029) B173029
theorem B165187 : Blo 99781 165187 := bstep (se 1 (by rfl) ⟨123890, by rfl⟩ : syracuseStep 165187 = 247781) B247781
theorem B230723 : Blo 99781 230723 := bstep (se 1 (by rfl) ⟨173042, by rfl⟩ : syracuseStep 230723 = 346085) B346085
theorem B165329 : Blo 99781 165329 := bstep (se 2 (by rfl) ⟨61998, by rfl⟩ : syracuseStep 165329 = 123997) B123997
theorem B99795 : Blo 99781 99795 := bstep (se 1 (by rfl) ⟨74846, by rfl⟩ : syracuseStep 99795 = 149693) B149693
theorem B99811 : Blo 99781 99811 := bstep (se 1 (by rfl) ⟨74858, by rfl⟩ : syracuseStep 99811 = 149717) B149717
theorem B394723 : Blo 99781 394723 := bstep (se 1 (by rfl) ⟨296042, by rfl⟩ : syracuseStep 394723 = 592085) B592085
theorem B99827 : Blo 99781 99827 := bstep (se 1 (by rfl) ⟨74870, by rfl⟩ : syracuseStep 99827 = 149741) B149741
theorem B99843 : Blo 99781 99843 := bstep (se 1 (by rfl) ⟨74882, by rfl⟩ : syracuseStep 99843 = 149765) B149765
theorem B99859 : Blo 99781 99859 := bstep (se 1 (by rfl) ⟨74894, by rfl⟩ : syracuseStep 99859 = 149789) B149789
theorem B99875 : Blo 99781 99875 := bstep (se 1 (by rfl) ⟨74906, by rfl⟩ : syracuseStep 99875 = 149813) B149813
theorem B99891 : Blo 99781 99891 := bstep (se 1 (by rfl) ⟨74918, by rfl⟩ : syracuseStep 99891 = 149837) B149837
theorem B99907 : Blo 99781 99907 := bstep (se 1 (by rfl) ⟨74930, by rfl⟩ : syracuseStep 99907 = 149861) B149861
theorem B230993 : Blo 99781 230993 := bstep (se 2 (by rfl) ⟨86622, by rfl⟩ : syracuseStep 230993 = 173245) B173245
theorem B99923 : Blo 99781 99923 := bstep (se 1 (by rfl) ⟨74942, by rfl⟩ : syracuseStep 99923 = 149885) B149885
theorem B99939 : Blo 99781 99939 := bstep (se 1 (by rfl) ⟨74954, by rfl⟩ : syracuseStep 99939 = 149909) B149909
theorem B231011 : Blo 99781 231011 := bstep (se 1 (by rfl) ⟨173258, by rfl⟩ : syracuseStep 231011 = 346517) B346517
theorem B99955 : Blo 99781 99955 := bstep (se 1 (by rfl) ⟨74966, by rfl⟩ : syracuseStep 99955 = 149933) B149933
theorem B99971 : Blo 99781 99971 := bstep (se 1 (by rfl) ⟨74978, by rfl⟩ : syracuseStep 99971 = 149957) B149957
theorem B99987 : Blo 99781 99987 := bstep (se 1 (by rfl) ⟨74990, by rfl⟩ : syracuseStep 99987 = 149981) B149981
theorem B100003 : Blo 99781 100003 := bstep (se 1 (by rfl) ⟨75002, by rfl⟩ : syracuseStep 100003 = 150005) B150005
theorem B100019 : Blo 99781 100019 := bstep (se 1 (by rfl) ⟨75014, by rfl⟩ : syracuseStep 100019 = 150029) B150029
theorem B100035 : Blo 99781 100035 := bstep (se 1 (by rfl) ⟨75026, by rfl⟩ : syracuseStep 100035 = 150053) B150053
theorem B100051 : Blo 99781 100051 := bstep (se 1 (by rfl) ⟨75038, by rfl⟩ : syracuseStep 100051 = 150077) B150077
theorem B100067 : Blo 99781 100067 := bstep (se 1 (by rfl) ⟨75050, by rfl⟩ : syracuseStep 100067 = 150101) B150101
theorem B689905 : Blo 99781 689905 := bstep (se 2 (by rfl) ⟨258714, by rfl⟩ : syracuseStep 689905 = 517429) B517429
theorem B100083 : Blo 99781 100083 := bstep (se 1 (by rfl) ⟨75062, by rfl⟩ : syracuseStep 100083 = 150125) B150125
theorem B100099 : Blo 99781 100099 := bstep (se 1 (by rfl) ⟨75074, by rfl⟩ : syracuseStep 100099 = 150149) B150149
theorem B100115 : Blo 99781 100115 := bstep (se 1 (by rfl) ⟨75086, by rfl⟩ : syracuseStep 100115 = 150173) B150173
theorem B100131 : Blo 99781 100131 := bstep (se 1 (by rfl) ⟨75098, by rfl⟩ : syracuseStep 100131 = 150197) B150197
theorem B132899 : Blo 99781 132899 := bstep (se 1 (by rfl) ⟨99674, by rfl⟩ : syracuseStep 132899 = 199349) B199349
theorem B100147 : Blo 99781 100147 := bstep (se 1 (by rfl) ⟨75110, by rfl⟩ : syracuseStep 100147 = 150221) B150221
theorem B100163 : Blo 99781 100163 := bstep (se 1 (by rfl) ⟨75122, by rfl⟩ : syracuseStep 100163 = 150245) B150245
theorem B100179 : Blo 99781 100179 := bstep (se 1 (by rfl) ⟨75134, by rfl⟩ : syracuseStep 100179 = 150269) B150269
theorem B100195 : Blo 99781 100195 := bstep (se 1 (by rfl) ⟨75146, by rfl⟩ : syracuseStep 100195 = 150293) B150293
theorem B231281 : Blo 99781 231281 := bstep (se 2 (by rfl) ⟨86730, by rfl⟩ : syracuseStep 231281 = 173461) B173461
theorem B100211 : Blo 99781 100211 := bstep (se 1 (by rfl) ⟨75158, by rfl⟩ : syracuseStep 100211 = 150317) B150317
theorem B100227 : Blo 99781 100227 := bstep (se 1 (by rfl) ⟨75170, by rfl⟩ : syracuseStep 100227 = 150341) B150341
theorem B231299 : Blo 99781 231299 := bstep (se 1 (by rfl) ⟨173474, by rfl⟩ : syracuseStep 231299 = 346949) B346949
theorem B100243 : Blo 99781 100243 := bstep (se 1 (by rfl) ⟨75182, by rfl⟩ : syracuseStep 100243 = 150365) B150365
theorem B100259 : Blo 99781 100259 := bstep (se 1 (by rfl) ⟨75194, by rfl⟩ : syracuseStep 100259 = 150389) B150389
theorem B100275 : Blo 99781 100275 := bstep (se 1 (by rfl) ⟨75206, by rfl⟩ : syracuseStep 100275 = 150413) B150413
theorem B100291 : Blo 99781 100291 := bstep (se 1 (by rfl) ⟨75218, by rfl⟩ : syracuseStep 100291 = 150437) B150437
theorem B100307 : Blo 99781 100307 := bstep (se 1 (by rfl) ⟨75230, by rfl⟩ : syracuseStep 100307 = 150461) B150461
theorem B100323 : Blo 99781 100323 := bstep (se 1 (by rfl) ⟨75242, by rfl⟩ : syracuseStep 100323 = 150485) B150485
theorem B100339 : Blo 99781 100339 := bstep (se 1 (by rfl) ⟨75254, by rfl⟩ : syracuseStep 100339 = 150509) B150509
theorem B100355 : Blo 99781 100355 := bstep (se 1 (by rfl) ⟨75266, by rfl⟩ : syracuseStep 100355 = 150533) B150533
theorem B100371 : Blo 99781 100371 := bstep (se 1 (by rfl) ⟨75278, by rfl⟩ : syracuseStep 100371 = 150557) B150557
theorem B100387 : Blo 99781 100387 := bstep (se 1 (by rfl) ⟨75290, by rfl⟩ : syracuseStep 100387 = 150581) B150581
theorem B100403 : Blo 99781 100403 := bstep (se 1 (by rfl) ⟨75302, by rfl⟩ : syracuseStep 100403 = 150605) B150605
theorem B100419 : Blo 99781 100419 := bstep (se 1 (by rfl) ⟨75314, by rfl⟩ : syracuseStep 100419 = 150629) B150629
theorem B100435 : Blo 99781 100435 := bstep (se 1 (by rfl) ⟨75326, by rfl⟩ : syracuseStep 100435 = 150653) B150653
theorem B329827 : Blo 99781 329827 := bstep (se 1 (by rfl) ⟨247370, by rfl⟩ : syracuseStep 329827 = 494741) B494741
theorem B100451 : Blo 99781 100451 := bstep (se 1 (by rfl) ⟨75338, by rfl⟩ : syracuseStep 100451 = 150677) B150677
theorem B100467 : Blo 99781 100467 := bstep (se 1 (by rfl) ⟨75350, by rfl⟩ : syracuseStep 100467 = 150701) B150701
theorem B100483 : Blo 99781 100483 := bstep (se 1 (by rfl) ⟨75362, by rfl⟩ : syracuseStep 100483 = 150725) B150725
theorem B985229 : Blo 99781 985229 := bstep (se 3 (by rfl) ⟨184730, by rfl⟩ : syracuseStep 985229 = 369461) B369461
theorem B231569 : Blo 99781 231569 := bstep (se 2 (by rfl) ⟨86838, by rfl⟩ : syracuseStep 231569 = 173677) B173677
theorem B100499 : Blo 99781 100499 := bstep (se 1 (by rfl) ⟨75374, by rfl⟩ : syracuseStep 100499 = 150749) B150749
theorem B100515 : Blo 99781 100515 := bstep (se 1 (by rfl) ⟨75386, by rfl⟩ : syracuseStep 100515 = 150773) B150773
theorem B231587 : Blo 99781 231587 := bstep (se 1 (by rfl) ⟨173690, by rfl⟩ : syracuseStep 231587 = 347381) B347381
theorem B100531 : Blo 99781 100531 := bstep (se 1 (by rfl) ⟨75398, by rfl⟩ : syracuseStep 100531 = 150797) B150797
theorem B100547 : Blo 99781 100547 := bstep (se 1 (by rfl) ⟨75410, by rfl⟩ : syracuseStep 100547 = 150821) B150821
theorem B100563 : Blo 99781 100563 := bstep (se 1 (by rfl) ⟨75422, by rfl⟩ : syracuseStep 100563 = 150845) B150845
theorem B100579 : Blo 99781 100579 := bstep (se 1 (by rfl) ⟨75434, by rfl⟩ : syracuseStep 100579 = 150869) B150869
theorem B100595 : Blo 99781 100595 := bstep (se 1 (by rfl) ⟨75446, by rfl⟩ : syracuseStep 100595 = 150893) B150893
theorem B100611 : Blo 99781 100611 := bstep (se 1 (by rfl) ⟨75458, by rfl⟩ : syracuseStep 100611 = 150917) B150917
theorem B329987 : Blo 99781 329987 := bstep (se 1 (by rfl) ⟨247490, by rfl⟩ : syracuseStep 329987 = 494981) B494981
theorem B100627 : Blo 99781 100627 := bstep (se 1 (by rfl) ⟨75470, by rfl⟩ : syracuseStep 100627 = 150941) B150941
theorem B100643 : Blo 99781 100643 := bstep (se 1 (by rfl) ⟨75482, by rfl⟩ : syracuseStep 100643 = 150965) B150965
theorem B100659 : Blo 99781 100659 := bstep (se 1 (by rfl) ⟨75494, by rfl⟩ : syracuseStep 100659 = 150989) B150989
theorem B100675 : Blo 99781 100675 := bstep (se 1 (by rfl) ⟨75506, by rfl⟩ : syracuseStep 100675 = 151013) B151013
theorem B100691 : Blo 99781 100691 := bstep (se 1 (by rfl) ⟨75518, by rfl⟩ : syracuseStep 100691 = 151037) B151037
theorem B100707 : Blo 99781 100707 := bstep (se 1 (by rfl) ⟨75530, by rfl⟩ : syracuseStep 100707 = 151061) B151061
theorem B100723 : Blo 99781 100723 := bstep (se 1 (by rfl) ⟨75542, by rfl⟩ : syracuseStep 100723 = 151085) B151085
theorem B100739 : Blo 99781 100739 := bstep (se 1 (by rfl) ⟨75554, by rfl⟩ : syracuseStep 100739 = 151109) B151109
theorem B100755 : Blo 99781 100755 := bstep (se 1 (by rfl) ⟨75566, by rfl⟩ : syracuseStep 100755 = 151133) B151133
theorem B100771 : Blo 99781 100771 := bstep (se 1 (by rfl) ⟨75578, by rfl⟩ : syracuseStep 100771 = 151157) B151157
theorem B231857 : Blo 99781 231857 := bstep (se 2 (by rfl) ⟨86946, by rfl⟩ : syracuseStep 231857 = 173893) B173893
theorem B100787 : Blo 99781 100787 := bstep (se 1 (by rfl) ⟨75590, by rfl⟩ : syracuseStep 100787 = 151181) B151181
theorem B100803 : Blo 99781 100803 := bstep (se 1 (by rfl) ⟨75602, by rfl⟩ : syracuseStep 100803 = 151205) B151205
theorem B231875 : Blo 99781 231875 := bstep (se 1 (by rfl) ⟨173906, by rfl⟩ : syracuseStep 231875 = 347813) B347813
theorem B100819 : Blo 99781 100819 := bstep (se 1 (by rfl) ⟨75614, by rfl⟩ : syracuseStep 100819 = 151229) B151229
theorem B100835 : Blo 99781 100835 := bstep (se 1 (by rfl) ⟨75626, by rfl⟩ : syracuseStep 100835 = 151253) B151253
theorem B100851 : Blo 99781 100851 := bstep (se 1 (by rfl) ⟨75638, by rfl⟩ : syracuseStep 100851 = 151277) B151277
theorem B100867 : Blo 99781 100867 := bstep (se 1 (by rfl) ⟨75650, by rfl⟩ : syracuseStep 100867 = 151301) B151301
theorem B100883 : Blo 99781 100883 := bstep (se 1 (by rfl) ⟨75662, by rfl⟩ : syracuseStep 100883 = 151325) B151325
theorem B100899 : Blo 99781 100899 := bstep (se 1 (by rfl) ⟨75674, by rfl⟩ : syracuseStep 100899 = 151349) B151349
theorem B100915 : Blo 99781 100915 := bstep (se 1 (by rfl) ⟨75686, by rfl⟩ : syracuseStep 100915 = 151373) B151373
theorem B100931 : Blo 99781 100931 := bstep (se 1 (by rfl) ⟨75698, by rfl⟩ : syracuseStep 100931 = 151397) B151397
theorem B559685 : Blo 99781 559685 := bstep (se 4 (by rfl) ⟨52470, by rfl⟩ : syracuseStep 559685 = 104941) B104941
theorem B100947 : Blo 99781 100947 := bstep (se 1 (by rfl) ⟨75710, by rfl⟩ : syracuseStep 100947 = 151421) B151421
theorem B100963 : Blo 99781 100963 := bstep (se 1 (by rfl) ⟨75722, by rfl⟩ : syracuseStep 100963 = 151445) B151445
theorem B100979 : Blo 99781 100979 := bstep (se 1 (by rfl) ⟨75734, by rfl⟩ : syracuseStep 100979 = 151469) B151469
theorem B100995 : Blo 99781 100995 := bstep (se 1 (by rfl) ⟨75746, by rfl⟩ : syracuseStep 100995 = 151493) B151493
theorem B101011 : Blo 99781 101011 := bstep (se 1 (by rfl) ⟨75758, by rfl⟩ : syracuseStep 101011 = 151517) B151517
theorem B101027 : Blo 99781 101027 := bstep (se 1 (by rfl) ⟨75770, by rfl⟩ : syracuseStep 101027 = 151541) B151541
theorem B625315 : Blo 99781 625315 := bstep (se 1 (by rfl) ⟨468986, by rfl⟩ : syracuseStep 625315 = 937973) B937973
theorem B101043 : Blo 99781 101043 := bstep (se 1 (by rfl) ⟨75782, by rfl⟩ : syracuseStep 101043 = 151565) B151565
theorem B101059 : Blo 99781 101059 := bstep (se 1 (by rfl) ⟨75794, by rfl⟩ : syracuseStep 101059 = 151589) B151589
theorem B559813 : Blo 99781 559813 := bstep (se 4 (by rfl) ⟨52482, by rfl⟩ : syracuseStep 559813 = 104965) B104965
theorem B232145 : Blo 99781 232145 := bstep (se 2 (by rfl) ⟨87054, by rfl⟩ : syracuseStep 232145 = 174109) B174109
theorem B101075 : Blo 99781 101075 := bstep (se 1 (by rfl) ⟨75806, by rfl⟩ : syracuseStep 101075 = 151613) B151613
theorem B101091 : Blo 99781 101091 := bstep (se 1 (by rfl) ⟨75818, by rfl⟩ : syracuseStep 101091 = 151637) B151637
theorem B232163 : Blo 99781 232163 := bstep (se 1 (by rfl) ⟨174122, by rfl⟩ : syracuseStep 232163 = 348245) B348245
theorem B101107 : Blo 99781 101107 := bstep (se 1 (by rfl) ⟨75830, by rfl⟩ : syracuseStep 101107 = 151661) B151661
theorem B101123 : Blo 99781 101123 := bstep (se 1 (by rfl) ⟨75842, by rfl⟩ : syracuseStep 101123 = 151685) B151685
theorem B101139 : Blo 99781 101139 := bstep (se 1 (by rfl) ⟨75854, by rfl⟩ : syracuseStep 101139 = 151709) B151709
theorem B101155 : Blo 99781 101155 := bstep (se 1 (by rfl) ⟨75866, by rfl⟩ : syracuseStep 101155 = 151733) B151733
theorem B101171 : Blo 99781 101171 := bstep (se 1 (by rfl) ⟨75878, by rfl⟩ : syracuseStep 101171 = 151757) B151757
theorem B101187 : Blo 99781 101187 := bstep (se 1 (by rfl) ⟨75890, by rfl⟩ : syracuseStep 101187 = 151781) B151781
theorem B101203 : Blo 99781 101203 := bstep (se 1 (by rfl) ⟨75902, by rfl⟩ : syracuseStep 101203 = 151805) B151805
theorem B101219 : Blo 99781 101219 := bstep (se 1 (by rfl) ⟨75914, by rfl⟩ : syracuseStep 101219 = 151829) B151829
theorem B101235 : Blo 99781 101235 := bstep (se 1 (by rfl) ⟨75926, by rfl⟩ : syracuseStep 101235 = 151853) B151853
theorem B101251 : Blo 99781 101251 := bstep (se 1 (by rfl) ⟨75938, by rfl⟩ : syracuseStep 101251 = 151877) B151877
theorem B101267 : Blo 99781 101267 := bstep (se 1 (by rfl) ⟨75950, by rfl⟩ : syracuseStep 101267 = 151901) B151901
theorem B101283 : Blo 99781 101283 := bstep (se 1 (by rfl) ⟨75962, by rfl⟩ : syracuseStep 101283 = 151925) B151925
theorem B101299 : Blo 99781 101299 := bstep (se 1 (by rfl) ⟨75974, by rfl⟩ : syracuseStep 101299 = 151949) B151949
theorem B101315 : Blo 99781 101315 := bstep (se 1 (by rfl) ⟨75986, by rfl⟩ : syracuseStep 101315 = 151973) B151973
theorem B854981 : Blo 99781 854981 := bstep (se 4 (by rfl) ⟨80154, by rfl⟩ : syracuseStep 854981 = 160309) B160309
theorem B101331 : Blo 99781 101331 := bstep (se 1 (by rfl) ⟨75998, by rfl⟩ : syracuseStep 101331 = 151997) B151997
theorem B101347 : Blo 99781 101347 := bstep (se 1 (by rfl) ⟨76010, by rfl⟩ : syracuseStep 101347 = 152021) B152021
theorem B232433 : Blo 99781 232433 := bstep (se 2 (by rfl) ⟨87162, by rfl⟩ : syracuseStep 232433 = 174325) B174325
theorem B101363 : Blo 99781 101363 := bstep (se 1 (by rfl) ⟨76022, by rfl⟩ : syracuseStep 101363 = 152045) B152045
theorem B101379 : Blo 99781 101379 := bstep (se 1 (by rfl) ⟨76034, by rfl⟩ : syracuseStep 101379 = 152069) B152069
theorem B232451 : Blo 99781 232451 := bstep (se 1 (by rfl) ⟨174338, by rfl⟩ : syracuseStep 232451 = 348677) B348677
theorem B101395 : Blo 99781 101395 := bstep (se 1 (by rfl) ⟨76046, by rfl⟩ : syracuseStep 101395 = 152093) B152093
theorem B101411 : Blo 99781 101411 := bstep (se 1 (by rfl) ⟨76058, by rfl⟩ : syracuseStep 101411 = 152117) B152117
theorem B101427 : Blo 99781 101427 := bstep (se 1 (by rfl) ⟨76070, by rfl⟩ : syracuseStep 101427 = 152141) B152141
theorem B101443 : Blo 99781 101443 := bstep (se 1 (by rfl) ⟨76082, by rfl⟩ : syracuseStep 101443 = 152165) B152165
theorem B101459 : Blo 99781 101459 := bstep (se 1 (by rfl) ⟨76094, by rfl⟩ : syracuseStep 101459 = 152189) B152189
theorem B101475 : Blo 99781 101475 := bstep (se 1 (by rfl) ⟨76106, by rfl⟩ : syracuseStep 101475 = 152213) B152213
theorem B101491 : Blo 99781 101491 := bstep (se 1 (by rfl) ⟨76118, by rfl⟩ : syracuseStep 101491 = 152237) B152237
theorem B101507 : Blo 99781 101507 := bstep (se 1 (by rfl) ⟨76130, by rfl⟩ : syracuseStep 101507 = 152261) B152261
theorem B101523 : Blo 99781 101523 := bstep (se 1 (by rfl) ⟨76142, by rfl⟩ : syracuseStep 101523 = 152285) B152285
theorem B101539 : Blo 99781 101539 := bstep (se 1 (by rfl) ⟨76154, by rfl⟩ : syracuseStep 101539 = 152309) B152309
theorem B101555 : Blo 99781 101555 := bstep (se 1 (by rfl) ⟨76166, by rfl⟩ : syracuseStep 101555 = 152333) B152333
theorem B101571 : Blo 99781 101571 := bstep (se 1 (by rfl) ⟨76178, by rfl⟩ : syracuseStep 101571 = 152357) B152357
theorem B101587 : Blo 99781 101587 := bstep (se 1 (by rfl) ⟨76190, by rfl⟩ : syracuseStep 101587 = 152381) B152381
theorem B101603 : Blo 99781 101603 := bstep (se 1 (by rfl) ⟨76202, by rfl⟩ : syracuseStep 101603 = 152405) B152405
theorem B101619 : Blo 99781 101619 := bstep (se 1 (by rfl) ⟨76214, by rfl⟩ : syracuseStep 101619 = 152429) B152429
theorem B101635 : Blo 99781 101635 := bstep (se 1 (by rfl) ⟨76226, by rfl⟩ : syracuseStep 101635 = 152453) B152453
theorem B232721 : Blo 99781 232721 := bstep (se 2 (by rfl) ⟨87270, by rfl⟩ : syracuseStep 232721 = 174541) B174541
theorem B101651 : Blo 99781 101651 := bstep (se 1 (by rfl) ⟨76238, by rfl⟩ : syracuseStep 101651 = 152477) B152477
theorem B101667 : Blo 99781 101667 := bstep (se 1 (by rfl) ⟨76250, by rfl⟩ : syracuseStep 101667 = 152501) B152501
theorem B232739 : Blo 99781 232739 := bstep (se 1 (by rfl) ⟨174554, by rfl⟩ : syracuseStep 232739 = 349109) B349109
theorem B101683 : Blo 99781 101683 := bstep (se 1 (by rfl) ⟨76262, by rfl⟩ : syracuseStep 101683 = 152525) B152525
theorem B101699 : Blo 99781 101699 := bstep (se 1 (by rfl) ⟨76274, by rfl⟩ : syracuseStep 101699 = 152549) B152549
theorem B101715 : Blo 99781 101715 := bstep (se 1 (by rfl) ⟨76286, by rfl⟩ : syracuseStep 101715 = 152573) B152573
theorem B101731 : Blo 99781 101731 := bstep (se 1 (by rfl) ⟨76298, by rfl⟩ : syracuseStep 101731 = 152597) B152597
theorem B101747 : Blo 99781 101747 := bstep (se 1 (by rfl) ⟨76310, by rfl⟩ : syracuseStep 101747 = 152621) B152621
theorem B101763 : Blo 99781 101763 := bstep (se 1 (by rfl) ⟨76322, by rfl⟩ : syracuseStep 101763 = 152645) B152645
theorem B101779 : Blo 99781 101779 := bstep (se 1 (by rfl) ⟨76334, by rfl⟩ : syracuseStep 101779 = 152669) B152669
theorem B101795 : Blo 99781 101795 := bstep (se 1 (by rfl) ⟨76346, by rfl⟩ : syracuseStep 101795 = 152693) B152693
theorem B101811 : Blo 99781 101811 := bstep (se 1 (by rfl) ⟨76358, by rfl⟩ : syracuseStep 101811 = 152717) B152717
theorem B101827 : Blo 99781 101827 := bstep (se 1 (by rfl) ⟨76370, by rfl⟩ : syracuseStep 101827 = 152741) B152741
theorem B101843 : Blo 99781 101843 := bstep (se 1 (by rfl) ⟨76382, by rfl⟩ : syracuseStep 101843 = 152765) B152765
theorem B101859 : Blo 99781 101859 := bstep (se 1 (by rfl) ⟨76394, by rfl⟩ : syracuseStep 101859 = 152789) B152789
theorem B101875 : Blo 99781 101875 := bstep (se 1 (by rfl) ⟨76406, by rfl⟩ : syracuseStep 101875 = 152813) B152813
theorem B101891 : Blo 99781 101891 := bstep (se 1 (by rfl) ⟨76418, by rfl⟩ : syracuseStep 101891 = 152837) B152837
theorem B101907 : Blo 99781 101907 := bstep (se 1 (by rfl) ⟨76430, by rfl⟩ : syracuseStep 101907 = 152861) B152861
theorem B101923 : Blo 99781 101923 := bstep (se 1 (by rfl) ⟨76442, by rfl⟩ : syracuseStep 101923 = 152885) B152885
theorem B233009 : Blo 99781 233009 := bstep (se 2 (by rfl) ⟨87378, by rfl⟩ : syracuseStep 233009 = 174757) B174757
theorem B101939 : Blo 99781 101939 := bstep (se 1 (by rfl) ⟨76454, by rfl⟩ : syracuseStep 101939 = 152909) B152909
theorem B101955 : Blo 99781 101955 := bstep (se 1 (by rfl) ⟨76466, by rfl⟩ : syracuseStep 101955 = 152933) B152933
theorem B233027 : Blo 99781 233027 := bstep (se 1 (by rfl) ⟨174770, by rfl⟩ : syracuseStep 233027 = 349541) B349541
theorem B101971 : Blo 99781 101971 := bstep (se 1 (by rfl) ⟨76478, by rfl⟩ : syracuseStep 101971 = 152957) B152957
theorem B101987 : Blo 99781 101987 := bstep (se 1 (by rfl) ⟨76490, by rfl⟩ : syracuseStep 101987 = 152981) B152981
theorem B102003 : Blo 99781 102003 := bstep (se 1 (by rfl) ⟨76502, by rfl⟩ : syracuseStep 102003 = 153005) B153005
theorem B102019 : Blo 99781 102019 := bstep (se 1 (by rfl) ⟨76514, by rfl⟩ : syracuseStep 102019 = 153029) B153029
theorem B790157 : Blo 99781 790157 := bstep (se 3 (by rfl) ⟨148154, by rfl⟩ : syracuseStep 790157 = 296309) B296309
theorem B102035 : Blo 99781 102035 := bstep (se 1 (by rfl) ⟨76526, by rfl⟩ : syracuseStep 102035 = 153053) B153053
theorem B429731 : Blo 99781 429731 := bstep (se 1 (by rfl) ⟨322298, by rfl⟩ : syracuseStep 429731 = 644597) B644597
theorem B102051 : Blo 99781 102051 := bstep (se 1 (by rfl) ⟨76538, by rfl⟩ : syracuseStep 102051 = 153077) B153077
theorem B102067 : Blo 99781 102067 := bstep (se 1 (by rfl) ⟨76550, by rfl⟩ : syracuseStep 102067 = 153101) B153101
theorem B102083 : Blo 99781 102083 := bstep (se 1 (by rfl) ⟨76562, by rfl⟩ : syracuseStep 102083 = 153125) B153125
theorem B102099 : Blo 99781 102099 := bstep (se 1 (by rfl) ⟨76574, by rfl⟩ : syracuseStep 102099 = 153149) B153149
theorem B102115 : Blo 99781 102115 := bstep (se 1 (by rfl) ⟨76586, by rfl⟩ : syracuseStep 102115 = 153173) B153173
theorem B102131 : Blo 99781 102131 := bstep (se 1 (by rfl) ⟨76598, by rfl⟩ : syracuseStep 102131 = 153197) B153197
theorem B102147 : Blo 99781 102147 := bstep (se 1 (by rfl) ⟨76610, by rfl⟩ : syracuseStep 102147 = 153221) B153221
theorem B102163 : Blo 99781 102163 := bstep (se 1 (by rfl) ⟨76622, by rfl⟩ : syracuseStep 102163 = 153245) B153245
theorem B102179 : Blo 99781 102179 := bstep (se 1 (by rfl) ⟨76634, by rfl⟩ : syracuseStep 102179 = 153269) B153269
theorem B102195 : Blo 99781 102195 := bstep (se 1 (by rfl) ⟨76646, by rfl⟩ : syracuseStep 102195 = 153293) B153293
theorem B102211 : Blo 99781 102211 := bstep (se 1 (by rfl) ⟨76658, by rfl⟩ : syracuseStep 102211 = 153317) B153317
theorem B233297 : Blo 99781 233297 := bstep (se 2 (by rfl) ⟨87486, by rfl⟩ : syracuseStep 233297 = 174973) B174973
theorem B102227 : Blo 99781 102227 := bstep (se 1 (by rfl) ⟨76670, by rfl⟩ : syracuseStep 102227 = 153341) B153341
theorem B102243 : Blo 99781 102243 := bstep (se 1 (by rfl) ⟨76682, by rfl⟩ : syracuseStep 102243 = 153365) B153365
theorem B233315 : Blo 99781 233315 := bstep (se 1 (by rfl) ⟨174986, by rfl⟩ : syracuseStep 233315 = 349973) B349973
theorem B102259 : Blo 99781 102259 := bstep (se 1 (by rfl) ⟨76694, by rfl⟩ : syracuseStep 102259 = 153389) B153389
theorem B102275 : Blo 99781 102275 := bstep (se 1 (by rfl) ⟨76706, by rfl⟩ : syracuseStep 102275 = 153413) B153413
theorem B102291 : Blo 99781 102291 := bstep (se 1 (by rfl) ⟨76718, by rfl⟩ : syracuseStep 102291 = 153437) B153437
theorem B102307 : Blo 99781 102307 := bstep (se 1 (by rfl) ⟨76730, by rfl⟩ : syracuseStep 102307 = 153461) B153461
theorem B102323 : Blo 99781 102323 := bstep (se 1 (by rfl) ⟨76742, by rfl⟩ : syracuseStep 102323 = 153485) B153485
theorem B102339 : Blo 99781 102339 := bstep (se 1 (by rfl) ⟨76754, by rfl⟩ : syracuseStep 102339 = 153509) B153509
theorem B102355 : Blo 99781 102355 := bstep (se 1 (by rfl) ⟨76766, by rfl⟩ : syracuseStep 102355 = 153533) B153533
theorem B102371 : Blo 99781 102371 := bstep (se 1 (by rfl) ⟨76778, by rfl⟩ : syracuseStep 102371 = 153557) B153557
theorem B102387 : Blo 99781 102387 := bstep (se 1 (by rfl) ⟨76790, by rfl⟩ : syracuseStep 102387 = 153581) B153581
theorem B102403 : Blo 99781 102403 := bstep (se 1 (by rfl) ⟨76802, by rfl⟩ : syracuseStep 102403 = 153605) B153605
theorem B102419 : Blo 99781 102419 := bstep (se 1 (by rfl) ⟨76814, by rfl⟩ : syracuseStep 102419 = 153629) B153629
theorem B102435 : Blo 99781 102435 := bstep (se 1 (by rfl) ⟨76826, by rfl⟩ : syracuseStep 102435 = 153653) B153653
theorem B102451 : Blo 99781 102451 := bstep (se 1 (by rfl) ⟨76838, by rfl⟩ : syracuseStep 102451 = 153677) B153677
theorem B102467 : Blo 99781 102467 := bstep (se 1 (by rfl) ⟨76850, by rfl⟩ : syracuseStep 102467 = 153701) B153701
theorem B102483 : Blo 99781 102483 := bstep (se 1 (by rfl) ⟨76862, by rfl⟩ : syracuseStep 102483 = 153725) B153725
theorem B102499 : Blo 99781 102499 := bstep (se 1 (by rfl) ⟨76874, by rfl⟩ : syracuseStep 102499 = 153749) B153749
theorem B102515 : Blo 99781 102515 := bstep (se 1 (by rfl) ⟨76886, by rfl⟩ : syracuseStep 102515 = 153773) B153773
theorem B102531 : Blo 99781 102531 := bstep (se 1 (by rfl) ⟨76898, by rfl⟩ : syracuseStep 102531 = 153797) B153797
theorem B102547 : Blo 99781 102547 := bstep (se 1 (by rfl) ⟨76910, by rfl⟩ : syracuseStep 102547 = 153821) B153821
theorem B102563 : Blo 99781 102563 := bstep (se 1 (by rfl) ⟨76922, by rfl⟩ : syracuseStep 102563 = 153845) B153845
theorem B102579 : Blo 99781 102579 := bstep (se 1 (by rfl) ⟨76934, by rfl⟩ : syracuseStep 102579 = 153869) B153869
theorem B102595 : Blo 99781 102595 := bstep (se 1 (by rfl) ⟨76946, by rfl⟩ : syracuseStep 102595 = 153893) B153893
theorem B102611 : Blo 99781 102611 := bstep (se 1 (by rfl) ⟨76958, by rfl⟩ : syracuseStep 102611 = 153917) B153917
theorem B102627 : Blo 99781 102627 := bstep (se 1 (by rfl) ⟨76970, by rfl⟩ : syracuseStep 102627 = 153941) B153941
theorem B102643 : Blo 99781 102643 := bstep (se 1 (by rfl) ⟨76982, by rfl⟩ : syracuseStep 102643 = 153965) B153965
theorem B102659 : Blo 99781 102659 := bstep (se 1 (by rfl) ⟨76994, by rfl⟩ : syracuseStep 102659 = 153989) B153989
theorem B102675 : Blo 99781 102675 := bstep (se 1 (by rfl) ⟨77006, by rfl⟩ : syracuseStep 102675 = 154013) B154013
theorem B102691 : Blo 99781 102691 := bstep (se 1 (by rfl) ⟨77018, by rfl⟩ : syracuseStep 102691 = 154037) B154037
theorem B102707 : Blo 99781 102707 := bstep (se 1 (by rfl) ⟨77030, by rfl⟩ : syracuseStep 102707 = 154061) B154061
theorem B102723 : Blo 99781 102723 := bstep (se 1 (by rfl) ⟨77042, by rfl⟩ : syracuseStep 102723 = 154085) B154085
theorem B102739 : Blo 99781 102739 := bstep (se 1 (by rfl) ⟨77054, by rfl⟩ : syracuseStep 102739 = 154109) B154109
theorem B102755 : Blo 99781 102755 := bstep (se 1 (by rfl) ⟨77066, by rfl⟩ : syracuseStep 102755 = 154133) B154133
theorem B790897 : Blo 99781 790897 := bstep (se 2 (by rfl) ⟨296586, by rfl⟩ : syracuseStep 790897 = 593173) B593173
theorem B102771 : Blo 99781 102771 := bstep (se 1 (by rfl) ⟨77078, by rfl⟩ : syracuseStep 102771 = 154157) B154157
theorem B102787 : Blo 99781 102787 := bstep (se 1 (by rfl) ⟨77090, by rfl⟩ : syracuseStep 102787 = 154181) B154181
theorem B102803 : Blo 99781 102803 := bstep (se 1 (by rfl) ⟨77102, by rfl⟩ : syracuseStep 102803 = 154205) B154205
theorem B102819 : Blo 99781 102819 := bstep (se 1 (by rfl) ⟨77114, by rfl⟩ : syracuseStep 102819 = 154229) B154229
theorem B102835 : Blo 99781 102835 := bstep (se 1 (by rfl) ⟨77126, by rfl⟩ : syracuseStep 102835 = 154253) B154253
theorem B168385 : Blo 99781 168385 := bstep (se 2 (by rfl) ⟨63144, by rfl⟩ : syracuseStep 168385 = 126289) B126289
theorem B102851 : Blo 99781 102851 := bstep (se 1 (by rfl) ⟨77138, by rfl⟩ : syracuseStep 102851 = 154277) B154277
theorem B102867 : Blo 99781 102867 := bstep (se 1 (by rfl) ⟨77150, by rfl⟩ : syracuseStep 102867 = 154301) B154301
theorem B168419 : Blo 99781 168419 := bstep (se 1 (by rfl) ⟨126314, by rfl⟩ : syracuseStep 168419 = 252629) B252629
theorem B102883 : Blo 99781 102883 := bstep (se 1 (by rfl) ⟨77162, by rfl⟩ : syracuseStep 102883 = 154325) B154325
theorem B102899 : Blo 99781 102899 := bstep (se 1 (by rfl) ⟨77174, by rfl⟩ : syracuseStep 102899 = 154349) B154349
theorem B102915 : Blo 99781 102915 := bstep (se 1 (by rfl) ⟨77186, by rfl⟩ : syracuseStep 102915 = 154373) B154373
theorem B102931 : Blo 99781 102931 := bstep (se 1 (by rfl) ⟨77198, by rfl⟩ : syracuseStep 102931 = 154397) B154397
theorem B102947 : Blo 99781 102947 := bstep (se 1 (by rfl) ⟨77210, by rfl⟩ : syracuseStep 102947 = 154421) B154421
theorem B102963 : Blo 99781 102963 := bstep (se 1 (by rfl) ⟨77222, by rfl⟩ : syracuseStep 102963 = 154445) B154445
theorem B102979 : Blo 99781 102979 := bstep (se 1 (by rfl) ⟨77234, by rfl⟩ : syracuseStep 102979 = 154469) B154469
theorem B102995 : Blo 99781 102995 := bstep (se 1 (by rfl) ⟨77246, by rfl⟩ : syracuseStep 102995 = 154493) B154493
theorem B103011 : Blo 99781 103011 := bstep (se 1 (by rfl) ⟨77258, by rfl⟩ : syracuseStep 103011 = 154517) B154517
theorem B168547 : Blo 99781 168547 := bstep (se 1 (by rfl) ⟨126410, by rfl⟩ : syracuseStep 168547 = 252821) B252821
theorem B103027 : Blo 99781 103027 := bstep (se 1 (by rfl) ⟨77270, by rfl⟩ : syracuseStep 103027 = 154541) B154541
theorem B103043 : Blo 99781 103043 := bstep (se 1 (by rfl) ⟨77282, by rfl⟩ : syracuseStep 103043 = 154565) B154565
theorem B103059 : Blo 99781 103059 := bstep (se 1 (by rfl) ⟨77294, by rfl⟩ : syracuseStep 103059 = 154589) B154589
theorem B103075 : Blo 99781 103075 := bstep (se 1 (by rfl) ⟨77306, by rfl⟩ : syracuseStep 103075 = 154613) B154613
theorem B103091 : Blo 99781 103091 := bstep (se 1 (by rfl) ⟨77318, by rfl⟩ : syracuseStep 103091 = 154637) B154637
theorem B103107 : Blo 99781 103107 := bstep (se 1 (by rfl) ⟨77330, by rfl⟩ : syracuseStep 103107 = 154661) B154661
theorem B103123 : Blo 99781 103123 := bstep (se 1 (by rfl) ⟨77342, by rfl⟩ : syracuseStep 103123 = 154685) B154685
theorem B103139 : Blo 99781 103139 := bstep (se 1 (by rfl) ⟨77354, by rfl⟩ : syracuseStep 103139 = 154709) B154709
theorem B168689 : Blo 99781 168689 := bstep (se 2 (by rfl) ⟨63258, by rfl⟩ : syracuseStep 168689 = 126517) B126517
theorem B103155 : Blo 99781 103155 := bstep (se 1 (by rfl) ⟨77366, by rfl⟩ : syracuseStep 103155 = 154733) B154733
theorem B103171 : Blo 99781 103171 := bstep (se 1 (by rfl) ⟨77378, by rfl⟩ : syracuseStep 103171 = 154757) B154757
theorem B103187 : Blo 99781 103187 := bstep (se 1 (by rfl) ⟨77390, by rfl⟩ : syracuseStep 103187 = 154781) B154781
theorem B103203 : Blo 99781 103203 := bstep (se 1 (by rfl) ⟨77402, by rfl⟩ : syracuseStep 103203 = 154805) B154805
theorem B103219 : Blo 99781 103219 := bstep (se 1 (by rfl) ⟨77414, by rfl⟩ : syracuseStep 103219 = 154829) B154829
theorem B103235 : Blo 99781 103235 := bstep (se 1 (by rfl) ⟨77426, by rfl⟩ : syracuseStep 103235 = 154853) B154853
theorem B103251 : Blo 99781 103251 := bstep (se 1 (by rfl) ⟨77438, by rfl⟩ : syracuseStep 103251 = 154877) B154877
theorem B463715 : Blo 99781 463715 := bstep (se 1 (by rfl) ⟨347786, by rfl⟩ : syracuseStep 463715 = 695573) B695573
theorem B103267 : Blo 99781 103267 := bstep (se 1 (by rfl) ⟨77450, by rfl⟩ : syracuseStep 103267 = 154901) B154901
theorem B168817 : Blo 99781 168817 := bstep (se 2 (by rfl) ⟨63306, by rfl⟩ : syracuseStep 168817 = 126613) B126613
theorem B103283 : Blo 99781 103283 := bstep (se 1 (by rfl) ⟨77462, by rfl⟩ : syracuseStep 103283 = 154925) B154925
theorem B103299 : Blo 99781 103299 := bstep (se 1 (by rfl) ⟨77474, by rfl⟩ : syracuseStep 103299 = 154949) B154949
theorem B168851 : Blo 99781 168851 := bstep (se 1 (by rfl) ⟨126638, by rfl⟩ : syracuseStep 168851 = 253277) B253277
theorem B103315 : Blo 99781 103315 := bstep (se 1 (by rfl) ⟨77486, by rfl⟩ : syracuseStep 103315 = 154973) B154973
theorem B103331 : Blo 99781 103331 := bstep (se 1 (by rfl) ⟨77498, by rfl⟩ : syracuseStep 103331 = 154997) B154997
theorem B103347 : Blo 99781 103347 := bstep (se 1 (by rfl) ⟨77510, by rfl⟩ : syracuseStep 103347 = 155021) B155021
theorem B103363 : Blo 99781 103363 := bstep (se 1 (by rfl) ⟨77522, by rfl⟩ : syracuseStep 103363 = 155045) B155045
theorem B103379 : Blo 99781 103379 := bstep (se 1 (by rfl) ⟨77534, by rfl⟩ : syracuseStep 103379 = 155069) B155069
theorem B103395 : Blo 99781 103395 := bstep (se 1 (by rfl) ⟨77546, by rfl⟩ : syracuseStep 103395 = 155093) B155093
theorem B103411 : Blo 99781 103411 := bstep (se 1 (by rfl) ⟨77558, by rfl⟩ : syracuseStep 103411 = 155117) B155117
theorem B103427 : Blo 99781 103427 := bstep (se 1 (by rfl) ⟨77570, by rfl⟩ : syracuseStep 103427 = 155141) B155141
theorem B168979 : Blo 99781 168979 := bstep (se 1 (by rfl) ⟨126734, by rfl⟩ : syracuseStep 168979 = 253469) B253469
theorem B103443 : Blo 99781 103443 := bstep (se 1 (by rfl) ⟨77582, by rfl⟩ : syracuseStep 103443 = 155165) B155165
theorem B103459 : Blo 99781 103459 := bstep (se 1 (by rfl) ⟨77594, by rfl⟩ : syracuseStep 103459 = 155189) B155189
theorem B103475 : Blo 99781 103475 := bstep (se 1 (by rfl) ⟨77606, by rfl⟩ : syracuseStep 103475 = 155213) B155213
theorem B103491 : Blo 99781 103491 := bstep (se 1 (by rfl) ⟨77618, by rfl⟩ : syracuseStep 103491 = 155237) B155237
theorem B103507 : Blo 99781 103507 := bstep (se 1 (by rfl) ⟨77630, by rfl⟩ : syracuseStep 103507 = 155261) B155261
theorem B136289 : Blo 99781 136289 := bstep (se 2 (by rfl) ⟨51108, by rfl⟩ : syracuseStep 136289 = 102217) B102217
theorem B103523 : Blo 99781 103523 := bstep (se 1 (by rfl) ⟨77642, by rfl⟩ : syracuseStep 103523 = 155285) B155285
theorem B103539 : Blo 99781 103539 := bstep (se 1 (by rfl) ⟨77654, by rfl⟩ : syracuseStep 103539 = 155309) B155309
theorem B103555 : Blo 99781 103555 := bstep (se 1 (by rfl) ⟨77666, by rfl⟩ : syracuseStep 103555 = 155333) B155333
theorem B103571 : Blo 99781 103571 := bstep (se 1 (by rfl) ⟨77678, by rfl⟩ : syracuseStep 103571 = 155357) B155357
theorem B169121 : Blo 99781 169121 := bstep (se 2 (by rfl) ⟨63420, by rfl⟩ : syracuseStep 169121 = 126841) B126841
theorem B234659 : Blo 99781 234659 := bstep (se 1 (by rfl) ⟨175994, by rfl⟩ : syracuseStep 234659 = 351989) B351989
theorem B103587 : Blo 99781 103587 := bstep (se 1 (by rfl) ⟨77690, by rfl⟩ : syracuseStep 103587 = 155381) B155381
theorem B103603 : Blo 99781 103603 := bstep (se 1 (by rfl) ⟨77702, by rfl⟩ : syracuseStep 103603 = 155405) B155405
theorem B103619 : Blo 99781 103619 := bstep (se 1 (by rfl) ⟨77714, by rfl⟩ : syracuseStep 103619 = 155429) B155429
theorem B103635 : Blo 99781 103635 := bstep (se 1 (by rfl) ⟨77726, by rfl⟩ : syracuseStep 103635 = 155453) B155453
theorem B103651 : Blo 99781 103651 := bstep (se 1 (by rfl) ⟨77738, by rfl⟩ : syracuseStep 103651 = 155477) B155477
theorem B103667 : Blo 99781 103667 := bstep (se 1 (by rfl) ⟨77750, by rfl⟩ : syracuseStep 103667 = 155501) B155501
theorem B103683 : Blo 99781 103683 := bstep (se 1 (by rfl) ⟨77762, by rfl⟩ : syracuseStep 103683 = 155525) B155525
theorem B103699 : Blo 99781 103699 := bstep (se 1 (by rfl) ⟨77774, by rfl⟩ : syracuseStep 103699 = 155549) B155549
theorem B169249 : Blo 99781 169249 := bstep (se 2 (by rfl) ⟨63468, by rfl⟩ : syracuseStep 169249 = 126937) B126937
theorem B103715 : Blo 99781 103715 := bstep (se 1 (by rfl) ⟨77786, by rfl⟩ : syracuseStep 103715 = 155573) B155573
theorem B103731 : Blo 99781 103731 := bstep (se 1 (by rfl) ⟨77798, by rfl⟩ : syracuseStep 103731 = 155597) B155597
theorem B169283 : Blo 99781 169283 := bstep (se 1 (by rfl) ⟨126962, by rfl⟩ : syracuseStep 169283 = 253925) B253925
theorem B103747 : Blo 99781 103747 := bstep (se 1 (by rfl) ⟨77810, by rfl⟩ : syracuseStep 103747 = 155621) B155621
theorem B103763 : Blo 99781 103763 := bstep (se 1 (by rfl) ⟨77822, by rfl⟩ : syracuseStep 103763 = 155645) B155645
theorem B103779 : Blo 99781 103779 := bstep (se 1 (by rfl) ⟨77834, by rfl⟩ : syracuseStep 103779 = 155669) B155669
theorem B660869 : Blo 99781 660869 := bstep (se 4 (by rfl) ⟨61956, by rfl⟩ : syracuseStep 660869 = 123913) B123913
theorem B169411 : Blo 99781 169411 := bstep (se 1 (by rfl) ⟨127058, by rfl⟩ : syracuseStep 169411 = 254117) B254117
theorem B661069 : Blo 99781 661069 := bstep (se 3 (by rfl) ⟨123950, by rfl⟩ : syracuseStep 661069 = 247901) B247901
theorem B169553 : Blo 99781 169553 := bstep (se 2 (by rfl) ⟨63582, by rfl⟩ : syracuseStep 169553 = 127165) B127165
theorem B431729 : Blo 99781 431729 := bstep (se 2 (by rfl) ⟨161898, by rfl⟩ : syracuseStep 431729 = 323797) B323797
theorem B136819 : Blo 99781 136819 := bstep (se 1 (by rfl) ⟨102614, by rfl⟩ : syracuseStep 136819 = 205229) B205229
theorem B169681 : Blo 99781 169681 := bstep (se 2 (by rfl) ⟨63630, by rfl⟩ : syracuseStep 169681 = 127261) B127261
theorem B169715 : Blo 99781 169715 := bstep (se 1 (by rfl) ⟨127286, by rfl⟩ : syracuseStep 169715 = 254573) B254573
theorem B464753 : Blo 99781 464753 := bstep (se 2 (by rfl) ⟨174282, by rfl⟩ : syracuseStep 464753 = 348565) B348565
theorem B169843 : Blo 99781 169843 := bstep (se 1 (by rfl) ⟨127382, by rfl⟩ : syracuseStep 169843 = 254765) B254765
theorem B169985 : Blo 99781 169985 := bstep (se 2 (by rfl) ⟨63744, by rfl⟩ : syracuseStep 169985 = 127489) B127489
theorem B170113 : Blo 99781 170113 := bstep (se 2 (by rfl) ⟨63792, by rfl⟩ : syracuseStep 170113 = 127585) B127585
theorem B170147 : Blo 99781 170147 := bstep (se 1 (by rfl) ⟨127610, by rfl⟩ : syracuseStep 170147 = 255221) B255221
theorem B170275 : Blo 99781 170275 := bstep (se 1 (by rfl) ⟨127706, by rfl⟩ : syracuseStep 170275 = 255413) B255413
theorem B104819 : Blo 99781 104819 := bstep (se 1 (by rfl) ⟨78614, by rfl⟩ : syracuseStep 104819 = 157229) B157229
theorem B170417 : Blo 99781 170417 := bstep (se 2 (by rfl) ⟨63906, by rfl⟩ : syracuseStep 170417 = 127813) B127813
theorem B137683 : Blo 99781 137683 := bstep (se 1 (by rfl) ⟨103262, by rfl⟩ : syracuseStep 137683 = 206525) B206525
theorem B203249 : Blo 99781 203249 := bstep (se 2 (by rfl) ⟨76218, by rfl⟩ : syracuseStep 203249 = 152437) B152437
theorem B170545 : Blo 99781 170545 := bstep (se 2 (by rfl) ⟨63954, by rfl⟩ : syracuseStep 170545 = 127909) B127909
theorem B170579 : Blo 99781 170579 := bstep (se 1 (by rfl) ⟨127934, by rfl⟩ : syracuseStep 170579 = 255869) B255869
theorem B137857 : Blo 99781 137857 := bstep (se 2 (by rfl) ⟨51696, by rfl⟩ : syracuseStep 137857 = 103393) B103393
theorem B170707 : Blo 99781 170707 := bstep (se 1 (by rfl) ⟨128030, by rfl⟩ : syracuseStep 170707 = 256061) B256061
theorem B170753 : Blo 99781 170753 := bstep (se 2 (by rfl) ⟨64032, by rfl⟩ : syracuseStep 170753 = 128065) B128065
theorem B760589 : Blo 99781 760589 := bstep (se 3 (by rfl) ⟨142610, by rfl⟩ : syracuseStep 760589 = 285221) B285221
theorem B138019 : Blo 99781 138019 := bstep (se 1 (by rfl) ⟨103514, by rfl⟩ : syracuseStep 138019 = 207029) B207029
theorem B170849 : Blo 99781 170849 := bstep (se 2 (by rfl) ⟨64068, by rfl⟩ : syracuseStep 170849 = 128137) B128137
theorem B236465 : Blo 99781 236465 := bstep (se 2 (by rfl) ⟨88674, by rfl⟩ : syracuseStep 236465 = 177349) B177349
theorem B170977 : Blo 99781 170977 := bstep (se 2 (by rfl) ⟨64116, by rfl⟩ : syracuseStep 170977 = 128233) B128233
theorem B171011 : Blo 99781 171011 := bstep (se 1 (by rfl) ⟨128258, by rfl⟩ : syracuseStep 171011 = 256517) B256517
theorem B1317941 : Blo 99781 1317941 := bstep (se 5 (by rfl) ⟨61778, by rfl⟩ : syracuseStep 1317941 = 123557) B123557
theorem B171139 : Blo 99781 171139 := bstep (se 1 (by rfl) ⟨128354, by rfl⟩ : syracuseStep 171139 = 256709) B256709
theorem B335021 : Blo 99781 335021 := bstep (se 3 (by rfl) ⟨62816, by rfl⟩ : syracuseStep 335021 = 125633) B125633
theorem B171217 : Blo 99781 171217 := bstep (se 2 (by rfl) ⟨64206, by rfl⟩ : syracuseStep 171217 = 128413) B128413
theorem B433421 : Blo 99781 433421 := bstep (se 3 (by rfl) ⟨81266, by rfl⟩ : syracuseStep 433421 = 162533) B162533
theorem B335117 : Blo 99781 335117 := bstep (se 3 (by rfl) ⟨62834, by rfl⟩ : syracuseStep 335117 = 125669) B125669
theorem B171281 : Blo 99781 171281 := bstep (se 2 (by rfl) ⟨64230, by rfl⟩ : syracuseStep 171281 = 128461) B128461
theorem B171409 : Blo 99781 171409 := bstep (se 2 (by rfl) ⟨64278, by rfl⟩ : syracuseStep 171409 = 128557) B128557
theorem B171443 : Blo 99781 171443 := bstep (se 1 (by rfl) ⟨128582, by rfl⟩ : syracuseStep 171443 = 257165) B257165
theorem B368077 : Blo 99781 368077 := bstep (se 3 (by rfl) ⟨69014, by rfl⟩ : syracuseStep 368077 = 138029) B138029
theorem B138721 : Blo 99781 138721 := bstep (se 2 (by rfl) ⟨52020, by rfl⟩ : syracuseStep 138721 = 104041) B104041
theorem B269873 : Blo 99781 269873 := bstep (se 2 (by rfl) ⟨101202, by rfl⟩ : syracuseStep 269873 = 202405) B202405
theorem B171571 : Blo 99781 171571 := bstep (se 1 (by rfl) ⟨128678, by rfl⟩ : syracuseStep 171571 = 257357) B257357
theorem B171713 : Blo 99781 171713 := bstep (se 2 (by rfl) ⟨64392, by rfl⟩ : syracuseStep 171713 = 128785) B128785
theorem B990917 : Blo 99781 990917 := bstep (se 4 (by rfl) ⟨92898, by rfl⟩ : syracuseStep 990917 = 185797) B185797
theorem B270125 : Blo 99781 270125 := bstep (se 3 (by rfl) ⟨50648, by rfl⟩ : syracuseStep 270125 = 101297) B101297
theorem B171841 : Blo 99781 171841 := bstep (se 2 (by rfl) ⟨64440, by rfl⟩ : syracuseStep 171841 = 128881) B128881
theorem B171875 : Blo 99781 171875 := bstep (se 1 (by rfl) ⟨128906, by rfl⟩ : syracuseStep 171875 = 257813) B257813
theorem B172003 : Blo 99781 172003 := bstep (se 1 (by rfl) ⟨129002, by rfl⟩ : syracuseStep 172003 = 258005) B258005
theorem B172145 : Blo 99781 172145 := bstep (se 2 (by rfl) ⟨64554, by rfl⟩ : syracuseStep 172145 = 129109) B129109
theorem B172273 : Blo 99781 172273 := bstep (se 2 (by rfl) ⟨64602, by rfl⟩ : syracuseStep 172273 = 129205) B129205
theorem B172307 : Blo 99781 172307 := bstep (se 1 (by rfl) ⟨129230, by rfl⟩ : syracuseStep 172307 = 258461) B258461
theorem B172435 : Blo 99781 172435 := bstep (se 1 (by rfl) ⟨129326, by rfl⟩ : syracuseStep 172435 = 258653) B258653
theorem B172577 : Blo 99781 172577 := bstep (se 2 (by rfl) ⟨64716, by rfl⟩ : syracuseStep 172577 = 129433) B129433
theorem B172705 : Blo 99781 172705 := bstep (se 2 (by rfl) ⟨64764, by rfl⟩ : syracuseStep 172705 = 129529) B129529
theorem B271021 : Blo 99781 271021 := bstep (se 3 (by rfl) ⟨50816, by rfl⟩ : syracuseStep 271021 = 101633) B101633
theorem B172739 : Blo 99781 172739 := bstep (se 1 (by rfl) ⟨129554, by rfl⟩ : syracuseStep 172739 = 259109) B259109
theorem B336611 : Blo 99781 336611 := bstep (se 1 (by rfl) ⟨252458, by rfl⟩ : syracuseStep 336611 = 504917) B504917
theorem B172867 : Blo 99781 172867 := bstep (se 1 (by rfl) ⟨129650, by rfl⟩ : syracuseStep 172867 = 259301) B259301
theorem B664433 : Blo 99781 664433 := bstep (se 2 (by rfl) ⟨249162, by rfl⟩ : syracuseStep 664433 = 498325) B498325
theorem B828301 : Blo 99781 828301 := bstep (se 3 (by rfl) ⟨155306, by rfl⟩ : syracuseStep 828301 = 310613) B310613
theorem B107411 : Blo 99781 107411 := bstep (se 1 (by rfl) ⟨80558, by rfl⟩ : syracuseStep 107411 = 161117) B161117
theorem B664483 : Blo 99781 664483 := bstep (se 1 (by rfl) ⟨498362, by rfl⟩ : syracuseStep 664483 = 996725) B996725
theorem B173009 : Blo 99781 173009 := bstep (se 2 (by rfl) ⟨64878, by rfl⟩ : syracuseStep 173009 = 129757) B129757
theorem B173137 : Blo 99781 173137 := bstep (se 2 (by rfl) ⟨64926, by rfl⟩ : syracuseStep 173137 = 129853) B129853
theorem B304241 : Blo 99781 304241 := bstep (se 2 (by rfl) ⟨114090, by rfl⟩ : syracuseStep 304241 = 228181) B228181
theorem B173171 : Blo 99781 173171 := bstep (se 1 (by rfl) ⟨129878, by rfl⟩ : syracuseStep 173171 = 259757) B259757
theorem B173299 : Blo 99781 173299 := bstep (se 1 (by rfl) ⟨129974, by rfl⟩ : syracuseStep 173299 = 259949) B259949
theorem B337229 : Blo 99781 337229 := bstep (se 3 (by rfl) ⟨63230, by rfl⟩ : syracuseStep 337229 = 126461) B126461
theorem B173441 : Blo 99781 173441 := bstep (se 2 (by rfl) ⟨65040, by rfl⟩ : syracuseStep 173441 = 130081) B130081
theorem B337283 : Blo 99781 337283 := bstep (se 1 (by rfl) ⟨252962, by rfl⟩ : syracuseStep 337283 = 505925) B505925
theorem B173569 : Blo 99781 173569 := bstep (se 2 (by rfl) ⟨65088, by rfl⟩ : syracuseStep 173569 = 130177) B130177
theorem B173603 : Blo 99781 173603 := bstep (se 1 (by rfl) ⟨130202, by rfl⟩ : syracuseStep 173603 = 260405) B260405
theorem B763505 : Blo 99781 763505 := bstep (se 2 (by rfl) ⟨286314, by rfl⟩ : syracuseStep 763505 = 572629) B572629
theorem B108163 : Blo 99781 108163 := bstep (se 1 (by rfl) ⟨81122, by rfl⟩ : syracuseStep 108163 = 162245) B162245
theorem B337553 : Blo 99781 337553 := bstep (se 2 (by rfl) ⟨126582, by rfl⟩ : syracuseStep 337553 = 253165) B253165
theorem B173731 : Blo 99781 173731 := bstep (se 1 (by rfl) ⟨130298, by rfl⟩ : syracuseStep 173731 = 260597) B260597
theorem B173873 : Blo 99781 173873 := bstep (se 2 (by rfl) ⟨65202, by rfl⟩ : syracuseStep 173873 = 130405) B130405
theorem B174001 : Blo 99781 174001 := bstep (se 2 (by rfl) ⟨65250, by rfl⟩ : syracuseStep 174001 = 130501) B130501
theorem B174035 : Blo 99781 174035 := bstep (se 1 (by rfl) ⟨130526, by rfl⟩ : syracuseStep 174035 = 261053) B261053
theorem B305155 : Blo 99781 305155 := bstep (se 1 (by rfl) ⟨228866, by rfl⟩ : syracuseStep 305155 = 457733) B457733
theorem B174163 : Blo 99781 174163 := bstep (se 1 (by rfl) ⟨130622, by rfl⟩ : syracuseStep 174163 = 261245) B261245
theorem B338093 : Blo 99781 338093 := bstep (se 3 (by rfl) ⟨63392, by rfl⟩ : syracuseStep 338093 = 126785) B126785
theorem B108739 : Blo 99781 108739 := bstep (se 1 (by rfl) ⟨81554, by rfl⟩ : syracuseStep 108739 = 163109) B163109
theorem B174305 : Blo 99781 174305 := bstep (se 2 (by rfl) ⟨65364, by rfl⟩ : syracuseStep 174305 = 130729) B130729
theorem B338147 : Blo 99781 338147 := bstep (se 1 (by rfl) ⟨253610, by rfl⟩ : syracuseStep 338147 = 507221) B507221
theorem B174433 : Blo 99781 174433 := bstep (se 2 (by rfl) ⟨65412, by rfl⟩ : syracuseStep 174433 = 130825) B130825
theorem B174467 : Blo 99781 174467 := bstep (se 1 (by rfl) ⟨130850, by rfl⟩ : syracuseStep 174467 = 261701) B261701
theorem B338417 : Blo 99781 338417 := bstep (se 2 (by rfl) ⟨126906, by rfl⟩ : syracuseStep 338417 = 253813) B253813
theorem B174595 : Blo 99781 174595 := bstep (se 1 (by rfl) ⟨130946, by rfl⟩ : syracuseStep 174595 = 261893) B261893
theorem B272945 : Blo 99781 272945 := bstep (se 2 (by rfl) ⟨102354, by rfl⟩ : syracuseStep 272945 = 204709) B204709
theorem B174737 : Blo 99781 174737 := bstep (se 2 (by rfl) ⟨65526, by rfl⟩ : syracuseStep 174737 = 131053) B131053
theorem B371363 : Blo 99781 371363 := bstep (se 1 (by rfl) ⟨278522, by rfl⟩ : syracuseStep 371363 = 557045) B557045
theorem B338701 : Blo 99781 338701 := bstep (se 3 (by rfl) ⟨63506, by rfl⟩ : syracuseStep 338701 = 127013) B127013
theorem B174865 : Blo 99781 174865 := bstep (se 2 (by rfl) ⟨65574, by rfl⟩ : syracuseStep 174865 = 131149) B131149
theorem B174899 : Blo 99781 174899 := bstep (se 1 (by rfl) ⟨131174, by rfl⟩ : syracuseStep 174899 = 262349) B262349
theorem B863045 : Blo 99781 863045 := bstep (se 4 (by rfl) ⟨80910, by rfl⟩ : syracuseStep 863045 = 161821) B161821
theorem B994117 : Blo 99781 994117 := bstep (se 4 (by rfl) ⟨93198, by rfl⟩ : syracuseStep 994117 = 186397) B186397
theorem B175027 : Blo 99781 175027 := bstep (se 1 (by rfl) ⟨131270, by rfl⟩ : syracuseStep 175027 = 262541) B262541
theorem B109555 : Blo 99781 109555 := bstep (se 1 (by rfl) ⟨82166, by rfl⟩ : syracuseStep 109555 = 164333) B164333
theorem B338957 : Blo 99781 338957 := bstep (se 3 (by rfl) ⟨63554, by rfl⟩ : syracuseStep 338957 = 127109) B127109
theorem B339011 : Blo 99781 339011 := bstep (se 1 (by rfl) ⟨254258, by rfl⟩ : syracuseStep 339011 = 508517) B508517
theorem B339281 : Blo 99781 339281 := bstep (se 2 (by rfl) ⟨127230, by rfl⟩ : syracuseStep 339281 = 254461) B254461
theorem B568781 : Blo 99781 568781 := bstep (se 3 (by rfl) ⟨106646, by rfl⟩ : syracuseStep 568781 = 213293) B213293
theorem B863729 : Blo 99781 863729 := bstep (se 2 (by rfl) ⟨323898, by rfl⟩ : syracuseStep 863729 = 647797) B647797
theorem B405005 : Blo 99781 405005 := bstep (se 3 (by rfl) ⟨75938, by rfl⟩ : syracuseStep 405005 = 151877) B151877
theorem B437795 : Blo 99781 437795 := bstep (se 1 (by rfl) ⟨328346, by rfl⟩ : syracuseStep 437795 = 656693) B656693
theorem B405233 : Blo 99781 405233 := bstep (se 2 (by rfl) ⟨151962, by rfl⟩ : syracuseStep 405233 = 303925) B303925
theorem B143203 : Blo 99781 143203 := bstep (se 1 (by rfl) ⟨107402, by rfl⟩ : syracuseStep 143203 = 214805) B214805
theorem B339821 : Blo 99781 339821 := bstep (se 3 (by rfl) ⟨63716, by rfl⟩ : syracuseStep 339821 = 127433) B127433
theorem B339875 : Blo 99781 339875 := bstep (se 1 (by rfl) ⟨254906, by rfl⟩ : syracuseStep 339875 = 509813) B509813
theorem B1159109 : Blo 99781 1159109 := bstep (se 4 (by rfl) ⟨108666, by rfl⟩ : syracuseStep 1159109 = 217333) B217333
theorem B274481 : Blo 99781 274481 := bstep (se 2 (by rfl) ⟨102930, by rfl⟩ : syracuseStep 274481 = 205861) B205861
theorem B340145 : Blo 99781 340145 := bstep (se 2 (by rfl) ⟨127554, by rfl⟩ : syracuseStep 340145 = 255109) B255109
theorem B2470115 : Blo 99781 2470115 := bstep (se 1 (by rfl) ⟨1852586, by rfl⟩ : syracuseStep 2470115 = 3705173) B3705173
theorem B569713 : Blo 99781 569713 := bstep (se 2 (by rfl) ⟨213642, by rfl⟩ : syracuseStep 569713 = 427285) B427285
theorem B1323377 : Blo 99781 1323377 := bstep (se 2 (by rfl) ⟨496266, by rfl⟩ : syracuseStep 1323377 = 992533) B992533
theorem B307889 : Blo 99781 307889 := bstep (se 2 (by rfl) ⟨115458, by rfl⟩ : syracuseStep 307889 = 230917) B230917
theorem B340685 : Blo 99781 340685 := bstep (se 3 (by rfl) ⟨63878, by rfl⟩ : syracuseStep 340685 = 127757) B127757
theorem B340739 : Blo 99781 340739 := bstep (se 1 (by rfl) ⟨255554, by rfl⟩ : syracuseStep 340739 = 511109) B511109
theorem B144337 : Blo 99781 144337 := bstep (se 2 (by rfl) ⟨54126, by rfl⟩ : syracuseStep 144337 = 108253) B108253
theorem B341009 : Blo 99781 341009 := bstep (se 2 (by rfl) ⟨127878, by rfl⟩ : syracuseStep 341009 = 255757) B255757
theorem B242723 : Blo 99781 242723 := bstep (se 1 (by rfl) ⟨182042, by rfl⟩ : syracuseStep 242723 = 364085) B364085
theorem B144433 : Blo 99781 144433 := bstep (se 2 (by rfl) ⟨54162, by rfl⟩ : syracuseStep 144433 = 108325) B108325
theorem B177265 : Blo 99781 177265 := bstep (se 2 (by rfl) ⟨66474, by rfl⟩ : syracuseStep 177265 = 132949) B132949
theorem B373987 : Blo 99781 373987 := bstep (se 1 (by rfl) ⟨280490, by rfl⟩ : syracuseStep 373987 = 560981) B560981
theorem B210289 : Blo 99781 210289 := bstep (se 2 (by rfl) ⟨78858, by rfl⟩ : syracuseStep 210289 = 157717) B157717
theorem B439793 : Blo 99781 439793 := bstep (se 2 (by rfl) ⟨164922, by rfl⟩ : syracuseStep 439793 = 329845) B329845
theorem B144929 : Blo 99781 144929 := bstep (se 2 (by rfl) ⟨54348, by rfl⟩ : syracuseStep 144929 = 108697) B108697
theorem B341549 : Blo 99781 341549 := bstep (se 3 (by rfl) ⟨64040, by rfl⟩ : syracuseStep 341549 = 128081) B128081
theorem B112195 : Blo 99781 112195 := bstep (se 1 (by rfl) ⟨84146, by rfl⟩ : syracuseStep 112195 = 168293) B168293
theorem B341603 : Blo 99781 341603 := bstep (se 1 (by rfl) ⟨256202, by rfl⟩ : syracuseStep 341603 = 512405) B512405
theorem B112355 : Blo 99781 112355 := bstep (se 1 (by rfl) ⟨84266, by rfl⟩ : syracuseStep 112355 = 168533) B168533
theorem B112387 : Blo 99781 112387 := bstep (se 1 (by rfl) ⟨84290, by rfl⟩ : syracuseStep 112387 = 168581) B168581
theorem B571171 : Blo 99781 571171 := bstep (se 1 (by rfl) ⟨428378, by rfl⟩ : syracuseStep 571171 = 856757) B856757
theorem B341873 : Blo 99781 341873 := bstep (se 2 (by rfl) ⟨128202, by rfl⟩ : syracuseStep 341873 = 256405) B256405
theorem B145297 : Blo 99781 145297 := bstep (se 2 (by rfl) ⟨54486, by rfl⟩ : syracuseStep 145297 = 108973) B108973
theorem B112531 : Blo 99781 112531 := bstep (se 1 (by rfl) ⟨84398, by rfl⟩ : syracuseStep 112531 = 168797) B168797
theorem B505763 : Blo 99781 505763 := bstep (se 1 (by rfl) ⟨379322, by rfl⟩ : syracuseStep 505763 = 758645) B758645
theorem B112675 : Blo 99781 112675 := bstep (se 1 (by rfl) ⟨84506, by rfl⟩ : syracuseStep 112675 = 169013) B169013
theorem B112819 : Blo 99781 112819 := bstep (se 1 (by rfl) ⟨84614, by rfl⟩ : syracuseStep 112819 = 169229) B169229
theorem B571697 : Blo 99781 571697 := bstep (se 2 (by rfl) ⟨214386, by rfl⟩ : syracuseStep 571697 = 428773) B428773
theorem B112963 : Blo 99781 112963 := bstep (se 1 (by rfl) ⟨84722, by rfl⟩ : syracuseStep 112963 = 169445) B169445
theorem B145795 : Blo 99781 145795 := bstep (se 1 (by rfl) ⟨109346, by rfl⟩ : syracuseStep 145795 = 218693) B218693
theorem B342413 : Blo 99781 342413 := bstep (se 3 (by rfl) ⟨64202, by rfl⟩ : syracuseStep 342413 = 128405) B128405
theorem B342467 : Blo 99781 342467 := bstep (se 1 (by rfl) ⟨256850, by rfl⟩ : syracuseStep 342467 = 513701) B513701
theorem B113107 : Blo 99781 113107 := bstep (se 1 (by rfl) ⟨84830, by rfl⟩ : syracuseStep 113107 = 169661) B169661
theorem B145891 : Blo 99781 145891 := bstep (se 1 (by rfl) ⟨109418, by rfl⟩ : syracuseStep 145891 = 218837) B218837
theorem B113251 : Blo 99781 113251 := bstep (se 1 (by rfl) ⟨84938, by rfl⟩ : syracuseStep 113251 = 169877) B169877
theorem B1718981 : Blo 99781 1718981 := bstep (se 4 (by rfl) ⟨161154, by rfl⟩ : syracuseStep 1718981 = 322309) B322309
theorem B506573 : Blo 99781 506573 := bstep (se 3 (by rfl) ⟨94982, by rfl⟩ : syracuseStep 506573 = 189965) B189965
theorem B342737 : Blo 99781 342737 := bstep (se 2 (by rfl) ⟨128526, by rfl⟩ : syracuseStep 342737 = 257053) B257053
theorem B113395 : Blo 99781 113395 := bstep (se 1 (by rfl) ⟨85046, by rfl⟩ : syracuseStep 113395 = 170093) B170093
theorem B277357 : Blo 99781 277357 := bstep (se 3 (by rfl) ⟨52004, by rfl⟩ : syracuseStep 277357 = 104009) B104009
theorem B113539 : Blo 99781 113539 := bstep (se 1 (by rfl) ⟨85154, by rfl⟩ : syracuseStep 113539 = 170309) B170309
theorem B146387 : Blo 99781 146387 := bstep (se 1 (by rfl) ⟨109790, by rfl⟩ : syracuseStep 146387 = 219581) B219581
theorem B113683 : Blo 99781 113683 := bstep (se 1 (by rfl) ⟨85262, by rfl⟩ : syracuseStep 113683 = 170525) B170525
theorem B113827 : Blo 99781 113827 := bstep (se 1 (by rfl) ⟨85370, by rfl⟩ : syracuseStep 113827 = 170741) B170741
theorem B277681 : Blo 99781 277681 := bstep (se 2 (by rfl) ⟨104130, by rfl⟩ : syracuseStep 277681 = 208261) B208261
theorem B343277 : Blo 99781 343277 := bstep (se 3 (by rfl) ⟨64364, by rfl⟩ : syracuseStep 343277 = 128729) B128729
theorem B343331 : Blo 99781 343331 := bstep (se 1 (by rfl) ⟨257498, by rfl⟩ : syracuseStep 343331 = 514997) B514997
theorem B113971 : Blo 99781 113971 := bstep (se 1 (by rfl) ⟨85478, by rfl⟩ : syracuseStep 113971 = 170957) B170957
theorem B212401 : Blo 99781 212401 := bstep (se 2 (by rfl) ⟨79650, by rfl⟩ : syracuseStep 212401 = 159301) B159301
theorem B114115 : Blo 99781 114115 := bstep (se 1 (by rfl) ⟨85586, by rfl⟩ : syracuseStep 114115 = 171173) B171173
theorem B343601 : Blo 99781 343601 := bstep (se 2 (by rfl) ⟨128850, by rfl⟩ : syracuseStep 343601 = 257701) B257701
theorem B147025 : Blo 99781 147025 := bstep (se 2 (by rfl) ⟨55134, by rfl⟩ : syracuseStep 147025 = 110269) B110269
theorem B114259 : Blo 99781 114259 := bstep (se 1 (by rfl) ⟨85694, by rfl⟩ : syracuseStep 114259 = 171389) B171389
theorem B573155 : Blo 99781 573155 := bstep (se 1 (by rfl) ⟨429866, by rfl⟩ : syracuseStep 573155 = 859733) B859733
theorem B114403 : Blo 99781 114403 := bstep (se 1 (by rfl) ⟨85802, by rfl⟩ : syracuseStep 114403 = 171605) B171605
theorem B114547 : Blo 99781 114547 := bstep (se 1 (by rfl) ⟨85910, by rfl⟩ : syracuseStep 114547 = 171821) B171821
theorem B2015117 : Blo 99781 2015117 := bstep (se 3 (by rfl) ⟨377834, by rfl⟩ : syracuseStep 2015117 = 755669) B755669
theorem B442253 : Blo 99781 442253 := bstep (se 3 (by rfl) ⟨82922, by rfl⟩ : syracuseStep 442253 = 165845) B165845
theorem B147361 : Blo 99781 147361 := bstep (se 2 (by rfl) ⟨55260, by rfl⟩ : syracuseStep 147361 = 110521) B110521
theorem B540593 : Blo 99781 540593 := bstep (se 2 (by rfl) ⟨202722, by rfl⟩ : syracuseStep 540593 = 405445) B405445
theorem B114691 : Blo 99781 114691 := bstep (se 1 (by rfl) ⟨86018, by rfl⟩ : syracuseStep 114691 = 172037) B172037
theorem B344141 : Blo 99781 344141 := bstep (se 3 (by rfl) ⟨64526, by rfl⟩ : syracuseStep 344141 = 129053) B129053
theorem B344195 : Blo 99781 344195 := bstep (se 1 (by rfl) ⟨258146, by rfl⟩ : syracuseStep 344195 = 516293) B516293
theorem B114835 : Blo 99781 114835 := bstep (se 1 (by rfl) ⟨86126, by rfl⟩ : syracuseStep 114835 = 172253) B172253
theorem B1327373 : Blo 99781 1327373 := bstep (se 3 (by rfl) ⟨248882, by rfl⟩ : syracuseStep 1327373 = 497765) B497765
theorem B114979 : Blo 99781 114979 := bstep (se 1 (by rfl) ⟨86234, by rfl⟩ : syracuseStep 114979 = 172469) B172469
theorem B672077 : Blo 99781 672077 := bstep (se 3 (by rfl) ⟨126014, by rfl⟩ : syracuseStep 672077 = 252029) B252029
theorem B246115 : Blo 99781 246115 := bstep (se 1 (by rfl) ⟨184586, by rfl⟩ : syracuseStep 246115 = 369173) B369173
theorem B344465 : Blo 99781 344465 := bstep (se 2 (by rfl) ⟨129174, by rfl⟩ : syracuseStep 344465 = 258349) B258349
theorem B278957 : Blo 99781 278957 := bstep (se 3 (by rfl) ⟨52304, by rfl⟩ : syracuseStep 278957 = 104609) B104609
theorem B115123 : Blo 99781 115123 := bstep (se 1 (by rfl) ⟨86342, by rfl⟩ : syracuseStep 115123 = 172685) B172685
theorem B115267 : Blo 99781 115267 := bstep (se 1 (by rfl) ⟨86450, by rfl⟩ : syracuseStep 115267 = 172901) B172901
theorem B115411 : Blo 99781 115411 := bstep (se 1 (by rfl) ⟨86558, by rfl⟩ : syracuseStep 115411 = 173117) B173117
theorem B705293 : Blo 99781 705293 := bstep (se 3 (by rfl) ⟨132242, by rfl⟩ : syracuseStep 705293 = 264485) B264485
theorem B246577 : Blo 99781 246577 := bstep (se 2 (by rfl) ⟨92466, by rfl⟩ : syracuseStep 246577 = 184933) B184933
theorem B115555 : Blo 99781 115555 := bstep (se 1 (by rfl) ⟨86666, by rfl⟩ : syracuseStep 115555 = 173333) B173333
theorem B345005 : Blo 99781 345005 := bstep (se 3 (by rfl) ⟨64688, by rfl⟩ : syracuseStep 345005 = 129377) B129377
theorem B345059 : Blo 99781 345059 := bstep (se 1 (by rfl) ⟨258794, by rfl⟩ : syracuseStep 345059 = 517589) B517589
theorem B115699 : Blo 99781 115699 := bstep (se 1 (by rfl) ⟨86774, by rfl⟩ : syracuseStep 115699 = 173549) B173549
theorem B214019 : Blo 99781 214019 := bstep (se 1 (by rfl) ⟨160514, by rfl⟩ : syracuseStep 214019 = 321029) B321029
theorem B148483 : Blo 99781 148483 := bstep (se 1 (by rfl) ⟨111362, by rfl⟩ : syracuseStep 148483 = 222725) B222725
theorem B115843 : Blo 99781 115843 := bstep (se 1 (by rfl) ⟨86882, by rfl⟩ : syracuseStep 115843 = 173765) B173765
theorem B345329 : Blo 99781 345329 := bstep (se 2 (by rfl) ⟨129498, by rfl⟩ : syracuseStep 345329 = 258997) B258997
theorem B279811 : Blo 99781 279811 := bstep (se 1 (by rfl) ⟨209858, by rfl⟩ : syracuseStep 279811 = 419717) B419717
theorem B115987 : Blo 99781 115987 := bstep (se 1 (by rfl) ⟨86990, by rfl⟩ : syracuseStep 115987 = 173981) B173981
theorem B116131 : Blo 99781 116131 := bstep (se 1 (by rfl) ⟨87098, by rfl⟩ : syracuseStep 116131 = 174197) B174197
theorem B1295797 : Blo 99781 1295797 := bstep (se 5 (by rfl) ⟨60740, by rfl⟩ : syracuseStep 1295797 = 121481) B121481
theorem B214481 : Blo 99781 214481 := bstep (se 2 (by rfl) ⟨80430, by rfl⟩ : syracuseStep 214481 = 160861) B160861
theorem B509489 : Blo 99781 509489 := bstep (se 2 (by rfl) ⟨191058, by rfl⟩ : syracuseStep 509489 = 382117) B382117
theorem B116275 : Blo 99781 116275 := bstep (se 1 (by rfl) ⟨87206, by rfl⟩ : syracuseStep 116275 = 174413) B174413
theorem B575045 : Blo 99781 575045 := bstep (se 4 (by rfl) ⟨53910, by rfl⟩ : syracuseStep 575045 = 107821) B107821
theorem B1164941 : Blo 99781 1164941 := bstep (se 3 (by rfl) ⟨218426, by rfl⟩ : syracuseStep 1164941 = 436853) B436853
theorem B116419 : Blo 99781 116419 := bstep (se 1 (by rfl) ⟨87314, by rfl⟩ : syracuseStep 116419 = 174629) B174629
theorem B345869 : Blo 99781 345869 := bstep (se 3 (by rfl) ⟨64850, by rfl⟩ : syracuseStep 345869 = 129701) B129701
theorem B345923 : Blo 99781 345923 := bstep (se 1 (by rfl) ⟨259442, by rfl⟩ : syracuseStep 345923 = 518885) B518885
theorem B116563 : Blo 99781 116563 := bstep (se 1 (by rfl) ⟨87422, by rfl⟩ : syracuseStep 116563 = 174845) B174845
theorem B182179 : Blo 99781 182179 := bstep (se 1 (by rfl) ⟨136634, by rfl⟩ : syracuseStep 182179 = 273269) B273269
theorem B116707 : Blo 99781 116707 := bstep (se 1 (by rfl) ⟨87530, by rfl⟩ : syracuseStep 116707 = 175061) B175061
theorem B968773 : Blo 99781 968773 := bstep (se 4 (by rfl) ⟨90822, by rfl⟩ : syracuseStep 968773 = 181645) B181645
theorem B182353 : Blo 99781 182353 := bstep (se 2 (by rfl) ⟨68382, by rfl⟩ : syracuseStep 182353 = 136765) B136765
theorem B346193 : Blo 99781 346193 := bstep (se 2 (by rfl) ⟨129822, by rfl⟩ : syracuseStep 346193 = 259645) B259645
theorem B149681 : Blo 99781 149681 := bstep (se 2 (by rfl) ⟨56130, by rfl⟩ : syracuseStep 149681 = 112261) B112261
theorem B149699 : Blo 99781 149699 := bstep (se 1 (by rfl) ⟨112274, by rfl⟩ : syracuseStep 149699 = 224549) B224549
theorem B706765 : Blo 99781 706765 := bstep (se 3 (by rfl) ⟨132518, by rfl⟩ : syracuseStep 706765 = 265037) B265037
theorem B149729 : Blo 99781 149729 := bstep (se 2 (by rfl) ⟨56148, by rfl⟩ : syracuseStep 149729 = 112297) B112297
theorem B149747 : Blo 99781 149747 := bstep (se 1 (by rfl) ⟨112310, by rfl⟩ : syracuseStep 149747 = 224621) B224621
theorem B149777 : Blo 99781 149777 := bstep (se 2 (by rfl) ⟨56166, by rfl⟩ : syracuseStep 149777 = 112333) B112333
theorem B149795 : Blo 99781 149795 := bstep (se 1 (by rfl) ⟨112346, by rfl⟩ : syracuseStep 149795 = 224693) B224693
theorem B149825 : Blo 99781 149825 := bstep (se 2 (by rfl) ⟨56184, by rfl⟩ : syracuseStep 149825 = 112369) B112369
theorem B149843 : Blo 99781 149843 := bstep (se 1 (by rfl) ⟨112382, by rfl⟩ : syracuseStep 149843 = 224765) B224765
theorem B149873 : Blo 99781 149873 := bstep (se 2 (by rfl) ⟨56202, by rfl⟩ : syracuseStep 149873 = 112405) B112405
theorem B149891 : Blo 99781 149891 := bstep (se 1 (by rfl) ⟨112418, by rfl⟩ : syracuseStep 149891 = 224837) B224837
theorem B149921 : Blo 99781 149921 := bstep (se 2 (by rfl) ⟨56220, by rfl⟩ : syracuseStep 149921 = 112441) B112441
theorem B149939 : Blo 99781 149939 := bstep (se 1 (by rfl) ⟨112454, by rfl⟩ : syracuseStep 149939 = 224909) B224909
theorem B149969 : Blo 99781 149969 := bstep (se 2 (by rfl) ⟨56238, by rfl⟩ : syracuseStep 149969 = 112477) B112477
theorem B149987 : Blo 99781 149987 := bstep (se 1 (by rfl) ⟨112490, by rfl⟩ : syracuseStep 149987 = 224981) B224981
theorem B150017 : Blo 99781 150017 := bstep (se 2 (by rfl) ⟨56256, by rfl⟩ : syracuseStep 150017 = 112513) B112513
theorem B150035 : Blo 99781 150035 := bstep (se 1 (by rfl) ⟨112526, by rfl⟩ : syracuseStep 150035 = 225053) B225053
theorem B150065 : Blo 99781 150065 := bstep (se 2 (by rfl) ⟨56274, by rfl⟩ : syracuseStep 150065 = 112549) B112549
theorem B150083 : Blo 99781 150083 := bstep (se 1 (by rfl) ⟨112562, by rfl⟩ : syracuseStep 150083 = 225125) B225125
theorem B150113 : Blo 99781 150113 := bstep (se 2 (by rfl) ⟨56292, by rfl⟩ : syracuseStep 150113 = 112585) B112585
theorem B346733 : Blo 99781 346733 := bstep (se 3 (by rfl) ⟨65012, by rfl⟩ : syracuseStep 346733 = 130025) B130025
theorem B379505 : Blo 99781 379505 := bstep (se 2 (by rfl) ⟨142314, by rfl⟩ : syracuseStep 379505 = 284629) B284629
theorem B150131 : Blo 99781 150131 := bstep (se 1 (by rfl) ⟨112598, by rfl⟩ : syracuseStep 150131 = 225197) B225197
theorem B150161 : Blo 99781 150161 := bstep (se 2 (by rfl) ⟨56310, by rfl⟩ : syracuseStep 150161 = 112621) B112621
theorem B150179 : Blo 99781 150179 := bstep (se 1 (by rfl) ⟨112634, by rfl⟩ : syracuseStep 150179 = 225269) B225269
theorem B346787 : Blo 99781 346787 := bstep (se 1 (by rfl) ⟨260090, by rfl⟩ : syracuseStep 346787 = 520181) B520181
theorem B150209 : Blo 99781 150209 := bstep (se 2 (by rfl) ⟨56328, by rfl⟩ : syracuseStep 150209 = 112657) B112657
theorem B150227 : Blo 99781 150227 := bstep (se 1 (by rfl) ⟨112670, by rfl⟩ : syracuseStep 150227 = 225341) B225341
theorem B215779 : Blo 99781 215779 := bstep (se 1 (by rfl) ⟨161834, by rfl⟩ : syracuseStep 215779 = 323669) B323669
theorem B150257 : Blo 99781 150257 := bstep (se 2 (by rfl) ⟨56346, by rfl⟩ : syracuseStep 150257 = 112693) B112693
theorem B150275 : Blo 99781 150275 := bstep (se 1 (by rfl) ⟨112706, by rfl⟩ : syracuseStep 150275 = 225413) B225413
theorem B150305 : Blo 99781 150305 := bstep (se 2 (by rfl) ⟨56364, by rfl⟩ : syracuseStep 150305 = 112729) B112729
theorem B150323 : Blo 99781 150323 := bstep (se 1 (by rfl) ⟨112742, by rfl⟩ : syracuseStep 150323 = 225485) B225485
theorem B150353 : Blo 99781 150353 := bstep (se 2 (by rfl) ⟨56382, by rfl⟩ : syracuseStep 150353 = 112765) B112765
theorem B150371 : Blo 99781 150371 := bstep (se 1 (by rfl) ⟨112778, by rfl⟩ : syracuseStep 150371 = 225557) B225557
theorem B150401 : Blo 99781 150401 := bstep (se 2 (by rfl) ⟨56400, by rfl⟩ : syracuseStep 150401 = 112801) B112801
theorem B150419 : Blo 99781 150419 := bstep (se 1 (by rfl) ⟨112814, by rfl⟩ : syracuseStep 150419 = 225629) B225629
theorem B150449 : Blo 99781 150449 := bstep (se 2 (by rfl) ⟨56418, by rfl⟩ : syracuseStep 150449 = 112837) B112837
theorem B347057 : Blo 99781 347057 := bstep (se 2 (by rfl) ⟨130146, by rfl⟩ : syracuseStep 347057 = 260293) B260293
theorem B150467 : Blo 99781 150467 := bstep (se 1 (by rfl) ⟨112850, by rfl⟩ : syracuseStep 150467 = 225701) B225701
theorem B150497 : Blo 99781 150497 := bstep (se 2 (by rfl) ⟨56436, by rfl⟩ : syracuseStep 150497 = 112873) B112873
theorem B510947 : Blo 99781 510947 := bstep (se 1 (by rfl) ⟨383210, by rfl⟩ : syracuseStep 510947 = 766421) B766421
theorem B216035 : Blo 99781 216035 := bstep (se 1 (by rfl) ⟨162026, by rfl⟩ : syracuseStep 216035 = 324053) B324053
theorem B117731 : Blo 99781 117731 := bstep (se 1 (by rfl) ⟨88298, by rfl⟩ : syracuseStep 117731 = 176597) B176597
theorem B150515 : Blo 99781 150515 := bstep (se 1 (by rfl) ⟨112886, by rfl⟩ : syracuseStep 150515 = 225773) B225773
theorem B150545 : Blo 99781 150545 := bstep (se 2 (by rfl) ⟨56454, by rfl⟩ : syracuseStep 150545 = 112909) B112909
theorem B150563 : Blo 99781 150563 := bstep (se 1 (by rfl) ⟨112922, by rfl⟩ : syracuseStep 150563 = 225845) B225845
theorem B150593 : Blo 99781 150593 := bstep (se 2 (by rfl) ⟨56472, by rfl⟩ : syracuseStep 150593 = 112945) B112945
theorem B150611 : Blo 99781 150611 := bstep (se 1 (by rfl) ⟨112958, by rfl⟩ : syracuseStep 150611 = 225917) B225917
theorem B150641 : Blo 99781 150641 := bstep (se 2 (by rfl) ⟨56490, by rfl⟩ : syracuseStep 150641 = 112981) B112981
theorem B150659 : Blo 99781 150659 := bstep (se 1 (by rfl) ⟨112994, by rfl⟩ : syracuseStep 150659 = 225989) B225989
theorem B150689 : Blo 99781 150689 := bstep (se 2 (by rfl) ⟨56508, by rfl⟩ : syracuseStep 150689 = 113017) B113017
theorem B150707 : Blo 99781 150707 := bstep (se 1 (by rfl) ⟨113030, by rfl⟩ : syracuseStep 150707 = 226061) B226061
theorem B150737 : Blo 99781 150737 := bstep (se 2 (by rfl) ⟨56526, by rfl⟩ : syracuseStep 150737 = 113053) B113053
theorem B150755 : Blo 99781 150755 := bstep (se 1 (by rfl) ⟨113066, by rfl⟩ : syracuseStep 150755 = 226133) B226133
theorem B150785 : Blo 99781 150785 := bstep (se 2 (by rfl) ⟨56544, by rfl⟩ : syracuseStep 150785 = 113089) B113089
theorem B380173 : Blo 99781 380173 := bstep (se 3 (by rfl) ⟨71282, by rfl⟩ : syracuseStep 380173 = 142565) B142565
theorem B150803 : Blo 99781 150803 := bstep (se 1 (by rfl) ⟨113102, by rfl⟩ : syracuseStep 150803 = 226205) B226205
theorem B150833 : Blo 99781 150833 := bstep (se 2 (by rfl) ⟨56562, by rfl⟩ : syracuseStep 150833 = 113125) B113125
theorem B150851 : Blo 99781 150851 := bstep (se 1 (by rfl) ⟨113138, by rfl⟩ : syracuseStep 150851 = 226277) B226277
theorem B150881 : Blo 99781 150881 := bstep (se 2 (by rfl) ⟨56580, by rfl⟩ : syracuseStep 150881 = 113161) B113161
theorem B871793 : Blo 99781 871793 := bstep (se 2 (by rfl) ⟨326922, by rfl⟩ : syracuseStep 871793 = 653845) B653845
theorem B150899 : Blo 99781 150899 := bstep (se 1 (by rfl) ⟨113174, by rfl⟩ : syracuseStep 150899 = 226349) B226349
theorem B150929 : Blo 99781 150929 := bstep (se 2 (by rfl) ⟨56598, by rfl⟩ : syracuseStep 150929 = 113197) B113197
theorem B150947 : Blo 99781 150947 := bstep (se 1 (by rfl) ⟨113210, by rfl⟩ : syracuseStep 150947 = 226421) B226421
theorem B150977 : Blo 99781 150977 := bstep (se 2 (by rfl) ⟨56616, by rfl⟩ : syracuseStep 150977 = 113233) B113233
theorem B347597 : Blo 99781 347597 := bstep (se 3 (by rfl) ⟨65174, by rfl⟩ : syracuseStep 347597 = 130349) B130349
theorem B150995 : Blo 99781 150995 := bstep (se 1 (by rfl) ⟨113246, by rfl⟩ : syracuseStep 150995 = 226493) B226493
theorem B151025 : Blo 99781 151025 := bstep (se 2 (by rfl) ⟨56634, by rfl⟩ : syracuseStep 151025 = 113269) B113269
theorem B151043 : Blo 99781 151043 := bstep (se 1 (by rfl) ⟨113282, by rfl⟩ : syracuseStep 151043 = 226565) B226565
theorem B347651 : Blo 99781 347651 := bstep (se 1 (by rfl) ⟨260738, by rfl⟩ : syracuseStep 347651 = 521477) B521477
theorem B151073 : Blo 99781 151073 := bstep (se 2 (by rfl) ⟨56652, by rfl⟩ : syracuseStep 151073 = 113305) B113305
theorem B151091 : Blo 99781 151091 := bstep (se 1 (by rfl) ⟨113318, by rfl⟩ : syracuseStep 151091 = 226637) B226637
theorem B151121 : Blo 99781 151121 := bstep (se 2 (by rfl) ⟨56670, by rfl⟩ : syracuseStep 151121 = 113341) B113341
theorem B151139 : Blo 99781 151139 := bstep (se 1 (by rfl) ⟨113354, by rfl⟩ : syracuseStep 151139 = 226709) B226709
theorem B4247153 : Blo 99781 4247153 := bstep (se 2 (by rfl) ⟨1592682, by rfl⟩ : syracuseStep 4247153 = 3185365) B3185365
theorem B151169 : Blo 99781 151169 := bstep (se 2 (by rfl) ⟨56688, by rfl⟩ : syracuseStep 151169 = 113377) B113377
theorem B151187 : Blo 99781 151187 := bstep (se 1 (by rfl) ⟨113390, by rfl⟩ : syracuseStep 151187 = 226781) B226781
theorem B151217 : Blo 99781 151217 := bstep (se 2 (by rfl) ⟨56706, by rfl⟩ : syracuseStep 151217 = 113413) B113413
theorem B151235 : Blo 99781 151235 := bstep (se 1 (by rfl) ⟨113426, by rfl⟩ : syracuseStep 151235 = 226853) B226853
theorem B151265 : Blo 99781 151265 := bstep (se 2 (by rfl) ⟨56724, by rfl⟩ : syracuseStep 151265 = 113449) B113449
theorem B151283 : Blo 99781 151283 := bstep (se 1 (by rfl) ⟨113462, by rfl⟩ : syracuseStep 151283 = 226925) B226925
theorem B511757 : Blo 99781 511757 := bstep (se 3 (by rfl) ⟨95954, by rfl⟩ : syracuseStep 511757 = 191909) B191909
theorem B151313 : Blo 99781 151313 := bstep (se 2 (by rfl) ⟨56742, by rfl⟩ : syracuseStep 151313 = 113485) B113485
theorem B347921 : Blo 99781 347921 := bstep (se 2 (by rfl) ⟨130470, by rfl⟩ : syracuseStep 347921 = 260941) B260941
theorem B151331 : Blo 99781 151331 := bstep (se 1 (by rfl) ⟨113498, by rfl⟩ : syracuseStep 151331 = 226997) B226997
theorem B347939 : Blo 99781 347939 := bstep (se 1 (by rfl) ⟨260954, by rfl⟩ : syracuseStep 347939 = 521909) B521909
theorem B151361 : Blo 99781 151361 := bstep (se 2 (by rfl) ⟨56760, by rfl⟩ : syracuseStep 151361 = 113521) B113521
theorem B151379 : Blo 99781 151379 := bstep (se 1 (by rfl) ⟨113534, by rfl⟩ : syracuseStep 151379 = 227069) B227069
theorem B151409 : Blo 99781 151409 := bstep (se 2 (by rfl) ⟨56778, by rfl⟩ : syracuseStep 151409 = 113557) B113557
theorem B151427 : Blo 99781 151427 := bstep (se 1 (by rfl) ⟨113570, by rfl⟩ : syracuseStep 151427 = 227141) B227141
theorem B151457 : Blo 99781 151457 := bstep (se 2 (by rfl) ⟨56796, by rfl⟩ : syracuseStep 151457 = 113593) B113593
theorem B217009 : Blo 99781 217009 := bstep (se 2 (by rfl) ⟨81378, by rfl⟩ : syracuseStep 217009 = 162757) B162757
theorem B151475 : Blo 99781 151475 := bstep (se 1 (by rfl) ⟨113606, by rfl⟩ : syracuseStep 151475 = 227213) B227213
theorem B151505 : Blo 99781 151505 := bstep (se 2 (by rfl) ⟨56814, by rfl⟩ : syracuseStep 151505 = 113629) B113629
theorem B151523 : Blo 99781 151523 := bstep (se 1 (by rfl) ⟨113642, by rfl⟩ : syracuseStep 151523 = 227285) B227285
theorem B151553 : Blo 99781 151553 := bstep (se 2 (by rfl) ⟨56832, by rfl⟩ : syracuseStep 151553 = 113665) B113665
theorem B151571 : Blo 99781 151571 := bstep (se 1 (by rfl) ⟨113678, by rfl⟩ : syracuseStep 151571 = 227357) B227357
theorem B380963 : Blo 99781 380963 := bstep (se 1 (by rfl) ⟨285722, by rfl⟩ : syracuseStep 380963 = 571445) B571445
theorem B151601 : Blo 99781 151601 := bstep (se 2 (by rfl) ⟨56850, by rfl⟩ : syracuseStep 151601 = 113701) B113701
theorem B151619 : Blo 99781 151619 := bstep (se 1 (by rfl) ⟨113714, by rfl⟩ : syracuseStep 151619 = 227429) B227429
theorem B151649 : Blo 99781 151649 := bstep (se 2 (by rfl) ⟨56868, by rfl⟩ : syracuseStep 151649 = 113737) B113737
theorem B315505 : Blo 99781 315505 := bstep (se 2 (by rfl) ⟨118314, by rfl⟩ : syracuseStep 315505 = 236629) B236629
theorem B151667 : Blo 99781 151667 := bstep (se 1 (by rfl) ⟨113750, by rfl⟩ : syracuseStep 151667 = 227501) B227501
theorem B151697 : Blo 99781 151697 := bstep (se 2 (by rfl) ⟨56886, by rfl⟩ : syracuseStep 151697 = 113773) B113773
theorem B151715 : Blo 99781 151715 := bstep (se 1 (by rfl) ⟨113786, by rfl⟩ : syracuseStep 151715 = 227573) B227573
theorem B446627 : Blo 99781 446627 := bstep (se 1 (by rfl) ⟨334970, by rfl⟩ : syracuseStep 446627 = 669941) B669941
theorem B151745 : Blo 99781 151745 := bstep (se 2 (by rfl) ⟨56904, by rfl⟩ : syracuseStep 151745 = 113809) B113809
theorem B151763 : Blo 99781 151763 := bstep (se 1 (by rfl) ⟨113822, by rfl⟩ : syracuseStep 151763 = 227645) B227645
theorem B151793 : Blo 99781 151793 := bstep (se 2 (by rfl) ⟨56922, by rfl⟩ : syracuseStep 151793 = 113845) B113845
theorem B151811 : Blo 99781 151811 := bstep (se 1 (by rfl) ⟨113858, by rfl⟩ : syracuseStep 151811 = 227717) B227717
theorem B151841 : Blo 99781 151841 := bstep (se 2 (by rfl) ⟨56940, by rfl⟩ : syracuseStep 151841 = 113881) B113881
theorem B348461 : Blo 99781 348461 := bstep (se 3 (by rfl) ⟨65336, by rfl⟩ : syracuseStep 348461 = 130673) B130673
theorem B151859 : Blo 99781 151859 := bstep (se 1 (by rfl) ⟨113894, by rfl⟩ : syracuseStep 151859 = 227789) B227789
theorem B151889 : Blo 99781 151889 := bstep (se 2 (by rfl) ⟨56958, by rfl⟩ : syracuseStep 151889 = 113917) B113917
theorem B151907 : Blo 99781 151907 := bstep (se 1 (by rfl) ⟨113930, by rfl⟩ : syracuseStep 151907 = 227861) B227861
theorem B348515 : Blo 99781 348515 := bstep (se 1 (by rfl) ⟨261386, by rfl⟩ : syracuseStep 348515 = 522773) B522773
theorem B151937 : Blo 99781 151937 := bstep (se 2 (by rfl) ⟨56976, by rfl⟩ : syracuseStep 151937 = 113953) B113953
theorem B151955 : Blo 99781 151955 := bstep (se 1 (by rfl) ⟨113966, by rfl⟩ : syracuseStep 151955 = 227933) B227933
theorem B151985 : Blo 99781 151985 := bstep (se 2 (by rfl) ⟨56994, by rfl⟩ : syracuseStep 151985 = 113989) B113989
theorem B152003 : Blo 99781 152003 := bstep (se 1 (by rfl) ⟨114002, by rfl⟩ : syracuseStep 152003 = 228005) B228005
theorem B152033 : Blo 99781 152033 := bstep (se 2 (by rfl) ⟨57012, by rfl⟩ : syracuseStep 152033 = 114025) B114025
theorem B1167857 : Blo 99781 1167857 := bstep (se 2 (by rfl) ⟨437946, by rfl⟩ : syracuseStep 1167857 = 875893) B875893
theorem B152051 : Blo 99781 152051 := bstep (se 1 (by rfl) ⟨114038, by rfl⟩ : syracuseStep 152051 = 228077) B228077
theorem B152081 : Blo 99781 152081 := bstep (se 2 (by rfl) ⟨57030, by rfl⟩ : syracuseStep 152081 = 114061) B114061
theorem B152099 : Blo 99781 152099 := bstep (se 1 (by rfl) ⟨114074, by rfl⟩ : syracuseStep 152099 = 228149) B228149
theorem B152129 : Blo 99781 152129 := bstep (se 2 (by rfl) ⟨57048, by rfl⟩ : syracuseStep 152129 = 114097) B114097
theorem B217667 : Blo 99781 217667 := bstep (se 1 (by rfl) ⟨163250, by rfl⟩ : syracuseStep 217667 = 326501) B326501
theorem B152147 : Blo 99781 152147 := bstep (se 1 (by rfl) ⟨114110, by rfl⟩ : syracuseStep 152147 = 228221) B228221
theorem B643697 : Blo 99781 643697 := bstep (se 2 (by rfl) ⟨241386, by rfl⟩ : syracuseStep 643697 = 482773) B482773
theorem B152177 : Blo 99781 152177 := bstep (se 2 (by rfl) ⟨57066, by rfl⟩ : syracuseStep 152177 = 114133) B114133
theorem B348785 : Blo 99781 348785 := bstep (se 2 (by rfl) ⟨130794, by rfl⟩ : syracuseStep 348785 = 261589) B261589
theorem B152195 : Blo 99781 152195 := bstep (se 1 (by rfl) ⟨114146, by rfl⟩ : syracuseStep 152195 = 228293) B228293
theorem B152225 : Blo 99781 152225 := bstep (se 2 (by rfl) ⟨57084, by rfl⟩ : syracuseStep 152225 = 114169) B114169
theorem B381617 : Blo 99781 381617 := bstep (se 2 (by rfl) ⟨143106, by rfl⟩ : syracuseStep 381617 = 286213) B286213
theorem B152243 : Blo 99781 152243 := bstep (se 1 (by rfl) ⟨114182, by rfl⟩ : syracuseStep 152243 = 228365) B228365
theorem B152273 : Blo 99781 152273 := bstep (se 2 (by rfl) ⟨57102, by rfl⟩ : syracuseStep 152273 = 114205) B114205
theorem B185041 : Blo 99781 185041 := bstep (se 2 (by rfl) ⟨69390, by rfl⟩ : syracuseStep 185041 = 138781) B138781
theorem B152291 : Blo 99781 152291 := bstep (se 1 (by rfl) ⟨114218, by rfl⟩ : syracuseStep 152291 = 228437) B228437
theorem B152321 : Blo 99781 152321 := bstep (se 2 (by rfl) ⟨57120, by rfl⟩ : syracuseStep 152321 = 114241) B114241
theorem B152339 : Blo 99781 152339 := bstep (se 1 (by rfl) ⟨114254, by rfl⟩ : syracuseStep 152339 = 228509) B228509
theorem B152369 : Blo 99781 152369 := bstep (se 2 (by rfl) ⟨57138, by rfl⟩ : syracuseStep 152369 = 114277) B114277
theorem B152387 : Blo 99781 152387 := bstep (se 1 (by rfl) ⟨114290, by rfl⟩ : syracuseStep 152387 = 228581) B228581
theorem B152417 : Blo 99781 152417 := bstep (se 2 (by rfl) ⟨57156, by rfl⟩ : syracuseStep 152417 = 114313) B114313
theorem B152435 : Blo 99781 152435 := bstep (se 1 (by rfl) ⟨114326, by rfl⟩ : syracuseStep 152435 = 228653) B228653
theorem B152465 : Blo 99781 152465 := bstep (se 2 (by rfl) ⟨57174, by rfl⟩ : syracuseStep 152465 = 114349) B114349
theorem B152483 : Blo 99781 152483 := bstep (se 1 (by rfl) ⟨114362, by rfl⟩ : syracuseStep 152483 = 228725) B228725
theorem B152513 : Blo 99781 152513 := bstep (se 2 (by rfl) ⟨57192, by rfl⟩ : syracuseStep 152513 = 114385) B114385
theorem B152531 : Blo 99781 152531 := bstep (se 1 (by rfl) ⟨114398, by rfl⟩ : syracuseStep 152531 = 228797) B228797
theorem B152561 : Blo 99781 152561 := bstep (se 2 (by rfl) ⟨57210, by rfl⟩ : syracuseStep 152561 = 114421) B114421
theorem B152579 : Blo 99781 152579 := bstep (se 1 (by rfl) ⟨114434, by rfl⟩ : syracuseStep 152579 = 228869) B228869
theorem B152609 : Blo 99781 152609 := bstep (se 2 (by rfl) ⟨57228, by rfl⟩ : syracuseStep 152609 = 114457) B114457
theorem B152627 : Blo 99781 152627 := bstep (se 1 (by rfl) ⟨114470, by rfl⟩ : syracuseStep 152627 = 228941) B228941
theorem B152657 : Blo 99781 152657 := bstep (se 2 (by rfl) ⟨57246, by rfl⟩ : syracuseStep 152657 = 114493) B114493
theorem B152675 : Blo 99781 152675 := bstep (se 1 (by rfl) ⟨114506, by rfl⟩ : syracuseStep 152675 = 229013) B229013
theorem B152705 : Blo 99781 152705 := bstep (se 2 (by rfl) ⟨57264, by rfl⟩ : syracuseStep 152705 = 114529) B114529
theorem B349325 : Blo 99781 349325 := bstep (se 3 (by rfl) ⟨65498, by rfl⟩ : syracuseStep 349325 = 130997) B130997
theorem B152723 : Blo 99781 152723 := bstep (se 1 (by rfl) ⟨114542, by rfl⟩ : syracuseStep 152723 = 229085) B229085
theorem B152753 : Blo 99781 152753 := bstep (se 2 (by rfl) ⟨57282, by rfl⟩ : syracuseStep 152753 = 114565) B114565
theorem B152771 : Blo 99781 152771 := bstep (se 1 (by rfl) ⟨114578, by rfl⟩ : syracuseStep 152771 = 229157) B229157
theorem B349379 : Blo 99781 349379 := bstep (se 1 (by rfl) ⟨262034, by rfl⟩ : syracuseStep 349379 = 524069) B524069
theorem B152801 : Blo 99781 152801 := bstep (se 2 (by rfl) ⟨57300, by rfl⟩ : syracuseStep 152801 = 114601) B114601
theorem B939235 : Blo 99781 939235 := bstep (se 1 (by rfl) ⟨704426, by rfl⟩ : syracuseStep 939235 = 1408853) B1408853
theorem B152819 : Blo 99781 152819 := bstep (se 1 (by rfl) ⟨114614, by rfl⟩ : syracuseStep 152819 = 229229) B229229
theorem B152849 : Blo 99781 152849 := bstep (se 2 (by rfl) ⟨57318, by rfl⟩ : syracuseStep 152849 = 114637) B114637
theorem B152867 : Blo 99781 152867 := bstep (se 1 (by rfl) ⟨114650, by rfl⟩ : syracuseStep 152867 = 229301) B229301
theorem B152897 : Blo 99781 152897 := bstep (se 2 (by rfl) ⟨57336, by rfl⟩ : syracuseStep 152897 = 114673) B114673
theorem B152915 : Blo 99781 152915 := bstep (se 1 (by rfl) ⟨114686, by rfl⟩ : syracuseStep 152915 = 229373) B229373
theorem B152945 : Blo 99781 152945 := bstep (se 2 (by rfl) ⟨57354, by rfl⟩ : syracuseStep 152945 = 114709) B114709
theorem B152947 : Blo 99781 152947 := bstep (se 1 (by rfl) ⟨114710, by rfl⟩ : syracuseStep 152947 = 229421) B229421
theorem B152963 : Blo 99781 152963 := bstep (se 1 (by rfl) ⟨114722, by rfl⟩ : syracuseStep 152963 = 229445) B229445
theorem B218513 : Blo 99781 218513 := bstep (se 2 (by rfl) ⟨81942, by rfl⟩ : syracuseStep 218513 = 163885) B163885
theorem B152993 : Blo 99781 152993 := bstep (se 2 (by rfl) ⟨57372, by rfl⟩ : syracuseStep 152993 = 114745) B114745
theorem B153011 : Blo 99781 153011 := bstep (se 1 (by rfl) ⟨114758, by rfl⟩ : syracuseStep 153011 = 229517) B229517
theorem B153041 : Blo 99781 153041 := bstep (se 2 (by rfl) ⟨57390, by rfl⟩ : syracuseStep 153041 = 114781) B114781
theorem B349649 : Blo 99781 349649 := bstep (se 2 (by rfl) ⟨131118, by rfl⟩ : syracuseStep 349649 = 262237) B262237
theorem B153059 : Blo 99781 153059 := bstep (se 1 (by rfl) ⟨114794, by rfl⟩ : syracuseStep 153059 = 229589) B229589
theorem B185827 : Blo 99781 185827 := bstep (se 1 (by rfl) ⟨139370, by rfl⟩ : syracuseStep 185827 = 278741) B278741
theorem B153089 : Blo 99781 153089 := bstep (se 2 (by rfl) ⟨57408, by rfl⟩ : syracuseStep 153089 = 114817) B114817
theorem B153107 : Blo 99781 153107 := bstep (se 1 (by rfl) ⟨114830, by rfl⟩ : syracuseStep 153107 = 229661) B229661
theorem B153137 : Blo 99781 153137 := bstep (se 2 (by rfl) ⟨57426, by rfl⟩ : syracuseStep 153137 = 114853) B114853
theorem B153155 : Blo 99781 153155 := bstep (se 1 (by rfl) ⟨114866, by rfl⟩ : syracuseStep 153155 = 229733) B229733
theorem B153185 : Blo 99781 153185 := bstep (se 2 (by rfl) ⟨57444, by rfl⟩ : syracuseStep 153185 = 114889) B114889
theorem B153203 : Blo 99781 153203 := bstep (se 1 (by rfl) ⟨114902, by rfl⟩ : syracuseStep 153203 = 229805) B229805
theorem B153233 : Blo 99781 153233 := bstep (se 2 (by rfl) ⟨57462, by rfl⟩ : syracuseStep 153233 = 114925) B114925
theorem B153251 : Blo 99781 153251 := bstep (se 1 (by rfl) ⟨114938, by rfl⟩ : syracuseStep 153251 = 229877) B229877
theorem B153281 : Blo 99781 153281 := bstep (se 2 (by rfl) ⟨57480, by rfl⟩ : syracuseStep 153281 = 114961) B114961
theorem B153299 : Blo 99781 153299 := bstep (se 1 (by rfl) ⟨114974, by rfl⟩ : syracuseStep 153299 = 229949) B229949
theorem B284401 : Blo 99781 284401 := bstep (se 2 (by rfl) ⟨106650, by rfl⟩ : syracuseStep 284401 = 213301) B213301
theorem B153329 : Blo 99781 153329 := bstep (se 2 (by rfl) ⟨57498, by rfl⟩ : syracuseStep 153329 = 114997) B114997
theorem B153347 : Blo 99781 153347 := bstep (se 1 (by rfl) ⟨115010, by rfl⟩ : syracuseStep 153347 = 230021) B230021
theorem B874253 : Blo 99781 874253 := bstep (se 3 (by rfl) ⟨163922, by rfl⟩ : syracuseStep 874253 = 327845) B327845
theorem B153377 : Blo 99781 153377 := bstep (se 2 (by rfl) ⟨57516, by rfl⟩ : syracuseStep 153377 = 115033) B115033
theorem B153395 : Blo 99781 153395 := bstep (se 1 (by rfl) ⟨115046, by rfl⟩ : syracuseStep 153395 = 230093) B230093
theorem B153425 : Blo 99781 153425 := bstep (se 2 (by rfl) ⟨57534, by rfl⟩ : syracuseStep 153425 = 115069) B115069
theorem B153443 : Blo 99781 153443 := bstep (se 1 (by rfl) ⟨115082, by rfl⟩ : syracuseStep 153443 = 230165) B230165
theorem B153473 : Blo 99781 153473 := bstep (se 2 (by rfl) ⟨57552, by rfl⟩ : syracuseStep 153473 = 115105) B115105
theorem B153491 : Blo 99781 153491 := bstep (se 1 (by rfl) ⟨115118, by rfl⟩ : syracuseStep 153491 = 230237) B230237
theorem B153521 : Blo 99781 153521 := bstep (se 2 (by rfl) ⟨57570, by rfl⟩ : syracuseStep 153521 = 115141) B115141
theorem B153539 : Blo 99781 153539 := bstep (se 1 (by rfl) ⟨115154, by rfl⟩ : syracuseStep 153539 = 230309) B230309
theorem B153569 : Blo 99781 153569 := bstep (se 2 (by rfl) ⟨57588, by rfl⟩ : syracuseStep 153569 = 115177) B115177
theorem B350189 : Blo 99781 350189 := bstep (se 3 (by rfl) ⟨65660, by rfl⟩ : syracuseStep 350189 = 131321) B131321
theorem B153587 : Blo 99781 153587 := bstep (se 1 (by rfl) ⟨115190, by rfl⟩ : syracuseStep 153587 = 230381) B230381
theorem B153617 : Blo 99781 153617 := bstep (se 2 (by rfl) ⟨57606, by rfl⟩ : syracuseStep 153617 = 115213) B115213
theorem B153635 : Blo 99781 153635 := bstep (se 1 (by rfl) ⟨115226, by rfl⟩ : syracuseStep 153635 = 230453) B230453
theorem B350243 : Blo 99781 350243 := bstep (se 1 (by rfl) ⟨262682, by rfl⟩ : syracuseStep 350243 = 525365) B525365
theorem B153665 : Blo 99781 153665 := bstep (se 2 (by rfl) ⟨57624, by rfl⟩ : syracuseStep 153665 = 115249) B115249
theorem B153683 : Blo 99781 153683 := bstep (se 1 (by rfl) ⟨115262, by rfl⟩ : syracuseStep 153683 = 230525) B230525
theorem B383075 : Blo 99781 383075 := bstep (se 1 (by rfl) ⟨287306, by rfl⟩ : syracuseStep 383075 = 574613) B574613
theorem B383089 : Blo 99781 383089 := bstep (se 2 (by rfl) ⟨143658, by rfl⟩ : syracuseStep 383089 = 287317) B287317
theorem B153713 : Blo 99781 153713 := bstep (se 2 (by rfl) ⟨57642, by rfl⟩ : syracuseStep 153713 = 115285) B115285
theorem B153731 : Blo 99781 153731 := bstep (se 1 (by rfl) ⟨115298, by rfl⟩ : syracuseStep 153731 = 230597) B230597
theorem B153761 : Blo 99781 153761 := bstep (se 2 (by rfl) ⟨57660, by rfl⟩ : syracuseStep 153761 = 115321) B115321
theorem B153779 : Blo 99781 153779 := bstep (se 1 (by rfl) ⟨115334, by rfl⟩ : syracuseStep 153779 = 230669) B230669
theorem B153793 : Blo 99781 153793 := bstep (se 2 (by rfl) ⟨57672, by rfl⟩ : syracuseStep 153793 = 115345) B115345
theorem B284867 : Blo 99781 284867 := bstep (se 1 (by rfl) ⟨213650, by rfl⟩ : syracuseStep 284867 = 427301) B427301
theorem B547013 : Blo 99781 547013 := bstep (se 4 (by rfl) ⟨51282, by rfl⟩ : syracuseStep 547013 = 102565) B102565
theorem B153809 : Blo 99781 153809 := bstep (se 2 (by rfl) ⟨57678, by rfl⟩ : syracuseStep 153809 = 115357) B115357
theorem B153827 : Blo 99781 153827 := bstep (se 1 (by rfl) ⟨115370, by rfl⟩ : syracuseStep 153827 = 230741) B230741
theorem B153857 : Blo 99781 153857 := bstep (se 2 (by rfl) ⟨57696, by rfl⟩ : syracuseStep 153857 = 115393) B115393
theorem B153875 : Blo 99781 153875 := bstep (se 1 (by rfl) ⟨115406, by rfl⟩ : syracuseStep 153875 = 230813) B230813
theorem B153905 : Blo 99781 153905 := bstep (se 2 (by rfl) ⟨57714, by rfl⟩ : syracuseStep 153905 = 115429) B115429
theorem B153923 : Blo 99781 153923 := bstep (se 1 (by rfl) ⟨115442, by rfl⟩ : syracuseStep 153923 = 230885) B230885
theorem B153953 : Blo 99781 153953 := bstep (se 2 (by rfl) ⟨57732, by rfl⟩ : syracuseStep 153953 = 115465) B115465
theorem B153971 : Blo 99781 153971 := bstep (se 1 (by rfl) ⟨115478, by rfl⟩ : syracuseStep 153971 = 230957) B230957
theorem B186769 : Blo 99781 186769 := bstep (se 2 (by rfl) ⟨70038, by rfl⟩ : syracuseStep 186769 = 140077) B140077
theorem B154001 : Blo 99781 154001 := bstep (se 2 (by rfl) ⟨57750, by rfl⟩ : syracuseStep 154001 = 115501) B115501
theorem B154019 : Blo 99781 154019 := bstep (se 1 (by rfl) ⟨115514, by rfl⟩ : syracuseStep 154019 = 231029) B231029
theorem B154049 : Blo 99781 154049 := bstep (se 2 (by rfl) ⟨57768, by rfl⟩ : syracuseStep 154049 = 115537) B115537
theorem B154067 : Blo 99781 154067 := bstep (se 1 (by rfl) ⟨115550, by rfl⟩ : syracuseStep 154067 = 231101) B231101
theorem B154097 : Blo 99781 154097 := bstep (se 2 (by rfl) ⟨57786, by rfl⟩ : syracuseStep 154097 = 115573) B115573
theorem B154115 : Blo 99781 154115 := bstep (se 1 (by rfl) ⟨115586, by rfl⟩ : syracuseStep 154115 = 231173) B231173
theorem B154145 : Blo 99781 154145 := bstep (se 2 (by rfl) ⟨57804, by rfl⟩ : syracuseStep 154145 = 115609) B115609
theorem B154163 : Blo 99781 154163 := bstep (se 1 (by rfl) ⟨115622, by rfl⟩ : syracuseStep 154163 = 231245) B231245
theorem B154193 : Blo 99781 154193 := bstep (se 2 (by rfl) ⟨57822, by rfl⟩ : syracuseStep 154193 = 115645) B115645
theorem B154211 : Blo 99781 154211 := bstep (se 1 (by rfl) ⟨115658, by rfl⟩ : syracuseStep 154211 = 231317) B231317
theorem B514673 : Blo 99781 514673 := bstep (se 2 (by rfl) ⟨193002, by rfl⟩ : syracuseStep 514673 = 386005) B386005
theorem B154241 : Blo 99781 154241 := bstep (se 2 (by rfl) ⟨57840, by rfl⟩ : syracuseStep 154241 = 115681) B115681
theorem B154259 : Blo 99781 154259 := bstep (se 1 (by rfl) ⟨115694, by rfl⟩ : syracuseStep 154259 = 231389) B231389
theorem B580259 : Blo 99781 580259 := bstep (se 1 (by rfl) ⟨435194, by rfl⟩ : syracuseStep 580259 = 870389) B870389
theorem B154289 : Blo 99781 154289 := bstep (se 2 (by rfl) ⟨57858, by rfl⟩ : syracuseStep 154289 = 115717) B115717
theorem B154307 : Blo 99781 154307 := bstep (se 1 (by rfl) ⟨115730, by rfl⟩ : syracuseStep 154307 = 231461) B231461
theorem B154337 : Blo 99781 154337 := bstep (se 2 (by rfl) ⟨57876, by rfl⟩ : syracuseStep 154337 = 115753) B115753
theorem B154355 : Blo 99781 154355 := bstep (se 1 (by rfl) ⟨115766, by rfl⟩ : syracuseStep 154355 = 231533) B231533
theorem B154385 : Blo 99781 154385 := bstep (se 2 (by rfl) ⟨57894, by rfl⟩ : syracuseStep 154385 = 115789) B115789
theorem B154403 : Blo 99781 154403 := bstep (se 1 (by rfl) ⟨115802, by rfl⟩ : syracuseStep 154403 = 231605) B231605
theorem B154433 : Blo 99781 154433 := bstep (se 2 (by rfl) ⟨57912, by rfl⟩ : syracuseStep 154433 = 115825) B115825
theorem B154451 : Blo 99781 154451 := bstep (se 1 (by rfl) ⟨115838, by rfl⟩ : syracuseStep 154451 = 231677) B231677
theorem B154481 : Blo 99781 154481 := bstep (se 2 (by rfl) ⟨57930, by rfl⟩ : syracuseStep 154481 = 115861) B115861
theorem B154499 : Blo 99781 154499 := bstep (se 1 (by rfl) ⟨115874, by rfl⟩ : syracuseStep 154499 = 231749) B231749
theorem B154529 : Blo 99781 154529 := bstep (se 2 (by rfl) ⟨57948, by rfl⟩ : syracuseStep 154529 = 115897) B115897
theorem B154547 : Blo 99781 154547 := bstep (se 1 (by rfl) ⟨115910, by rfl⟩ : syracuseStep 154547 = 231821) B231821
theorem B154577 : Blo 99781 154577 := bstep (se 2 (by rfl) ⟨57966, by rfl⟩ : syracuseStep 154577 = 115933) B115933
theorem B154595 : Blo 99781 154595 := bstep (se 1 (by rfl) ⟨115946, by rfl⟩ : syracuseStep 154595 = 231893) B231893
theorem B285677 : Blo 99781 285677 := bstep (se 3 (by rfl) ⟨53564, by rfl⟩ : syracuseStep 285677 = 107129) B107129
theorem B154625 : Blo 99781 154625 := bstep (se 2 (by rfl) ⟨57984, by rfl⟩ : syracuseStep 154625 = 115969) B115969
theorem B646157 : Blo 99781 646157 := bstep (se 3 (by rfl) ⟨121154, by rfl⟩ : syracuseStep 646157 = 242309) B242309
theorem B154643 : Blo 99781 154643 := bstep (se 1 (by rfl) ⟨115982, by rfl⟩ : syracuseStep 154643 = 231965) B231965
theorem B154673 : Blo 99781 154673 := bstep (se 2 (by rfl) ⟨58002, by rfl⟩ : syracuseStep 154673 = 116005) B116005
theorem B154691 : Blo 99781 154691 := bstep (se 1 (by rfl) ⟨116018, by rfl⟩ : syracuseStep 154691 = 232037) B232037
theorem B154721 : Blo 99781 154721 := bstep (se 2 (by rfl) ⟨58020, by rfl⟩ : syracuseStep 154721 = 116041) B116041
theorem B154739 : Blo 99781 154739 := bstep (se 1 (by rfl) ⟨116054, by rfl⟩ : syracuseStep 154739 = 232109) B232109
theorem B154769 : Blo 99781 154769 := bstep (se 2 (by rfl) ⟨58038, by rfl⟩ : syracuseStep 154769 = 116077) B116077
theorem B285859 : Blo 99781 285859 := bstep (se 1 (by rfl) ⟨214394, by rfl⟩ : syracuseStep 285859 = 428789) B428789
theorem B154787 : Blo 99781 154787 := bstep (se 1 (by rfl) ⟨116090, by rfl⟩ : syracuseStep 154787 = 232181) B232181
theorem B154817 : Blo 99781 154817 := bstep (se 2 (by rfl) ⟨58056, by rfl⟩ : syracuseStep 154817 = 116113) B116113
theorem B285905 : Blo 99781 285905 := bstep (se 2 (by rfl) ⟨107214, by rfl⟩ : syracuseStep 285905 = 214429) B214429
theorem B154835 : Blo 99781 154835 := bstep (se 1 (by rfl) ⟨116126, by rfl⟩ : syracuseStep 154835 = 232253) B232253
theorem B154865 : Blo 99781 154865 := bstep (se 2 (by rfl) ⟨58074, by rfl⟩ : syracuseStep 154865 = 116149) B116149
theorem B154883 : Blo 99781 154883 := bstep (se 1 (by rfl) ⟨116162, by rfl⟩ : syracuseStep 154883 = 232325) B232325
theorem B580877 : Blo 99781 580877 := bstep (se 3 (by rfl) ⟨108914, by rfl⟩ : syracuseStep 580877 = 217829) B217829
theorem B154913 : Blo 99781 154913 := bstep (se 2 (by rfl) ⟨58092, by rfl⟩ : syracuseStep 154913 = 116185) B116185
theorem B154931 : Blo 99781 154931 := bstep (se 1 (by rfl) ⟨116198, by rfl⟩ : syracuseStep 154931 = 232397) B232397
theorem B154961 : Blo 99781 154961 := bstep (se 2 (by rfl) ⟨58110, by rfl⟩ : syracuseStep 154961 = 116221) B116221
theorem B154979 : Blo 99781 154979 := bstep (se 1 (by rfl) ⟨116234, by rfl⟩ : syracuseStep 154979 = 232469) B232469
theorem B155009 : Blo 99781 155009 := bstep (se 2 (by rfl) ⟨58128, by rfl⟩ : syracuseStep 155009 = 116257) B116257
theorem B155027 : Blo 99781 155027 := bstep (se 1 (by rfl) ⟨116270, by rfl⟩ : syracuseStep 155027 = 232541) B232541
theorem B155057 : Blo 99781 155057 := bstep (se 2 (by rfl) ⟨58146, by rfl⟩ : syracuseStep 155057 = 116293) B116293
theorem B155075 : Blo 99781 155075 := bstep (se 1 (by rfl) ⟨116306, by rfl⟩ : syracuseStep 155075 = 232613) B232613
theorem B155105 : Blo 99781 155105 := bstep (se 2 (by rfl) ⟨58164, by rfl⟩ : syracuseStep 155105 = 116329) B116329
theorem B155123 : Blo 99781 155123 := bstep (se 1 (by rfl) ⟨116342, by rfl⟩ : syracuseStep 155123 = 232685) B232685
theorem B155153 : Blo 99781 155153 := bstep (se 2 (by rfl) ⟨58182, by rfl⟩ : syracuseStep 155153 = 116365) B116365
theorem B384547 : Blo 99781 384547 := bstep (se 1 (by rfl) ⟨288410, by rfl⟩ : syracuseStep 384547 = 576821) B576821
theorem B155171 : Blo 99781 155171 := bstep (se 1 (by rfl) ⟨116378, by rfl⟩ : syracuseStep 155171 = 232757) B232757
theorem B253489 : Blo 99781 253489 := bstep (se 2 (by rfl) ⟨95058, by rfl⟩ : syracuseStep 253489 = 190117) B190117
theorem B155201 : Blo 99781 155201 := bstep (se 2 (by rfl) ⟨58200, by rfl⟩ : syracuseStep 155201 = 116401) B116401
theorem B155219 : Blo 99781 155219 := bstep (se 1 (by rfl) ⟨116414, by rfl⟩ : syracuseStep 155219 = 232829) B232829
theorem B155249 : Blo 99781 155249 := bstep (se 2 (by rfl) ⟨58218, by rfl⟩ : syracuseStep 155249 = 116437) B116437
theorem B155267 : Blo 99781 155267 := bstep (se 1 (by rfl) ⟨116450, by rfl⟩ : syracuseStep 155267 = 232901) B232901
theorem B155297 : Blo 99781 155297 := bstep (se 2 (by rfl) ⟨58236, by rfl⟩ : syracuseStep 155297 = 116473) B116473
theorem B155315 : Blo 99781 155315 := bstep (se 1 (by rfl) ⟨116486, by rfl⟩ : syracuseStep 155315 = 232973) B232973
theorem B155345 : Blo 99781 155345 := bstep (se 2 (by rfl) ⟨58254, by rfl⟩ : syracuseStep 155345 = 116509) B116509
theorem B483043 : Blo 99781 483043 := bstep (se 1 (by rfl) ⟨362282, by rfl⟩ : syracuseStep 483043 = 724565) B724565
theorem B155363 : Blo 99781 155363 := bstep (se 1 (by rfl) ⟨116522, by rfl⟩ : syracuseStep 155363 = 233045) B233045
theorem B155393 : Blo 99781 155393 := bstep (se 2 (by rfl) ⟨58272, by rfl⟩ : syracuseStep 155393 = 116545) B116545
theorem B155411 : Blo 99781 155411 := bstep (se 1 (by rfl) ⟨116558, by rfl⟩ : syracuseStep 155411 = 233117) B233117
theorem B548657 : Blo 99781 548657 := bstep (se 2 (by rfl) ⟨205746, by rfl⟩ : syracuseStep 548657 = 411493) B411493
theorem B155441 : Blo 99781 155441 := bstep (se 2 (by rfl) ⟨58290, by rfl⟩ : syracuseStep 155441 = 116581) B116581
theorem B253763 : Blo 99781 253763 := bstep (se 1 (by rfl) ⟨190322, by rfl⟩ : syracuseStep 253763 = 380645) B380645
theorem B155459 : Blo 99781 155459 := bstep (se 1 (by rfl) ⟨116594, by rfl⟩ : syracuseStep 155459 = 233189) B233189
theorem B155489 : Blo 99781 155489 := bstep (se 2 (by rfl) ⟨58308, by rfl⟩ : syracuseStep 155489 = 116617) B116617
theorem B155507 : Blo 99781 155507 := bstep (se 1 (by rfl) ⟨116630, by rfl⟩ : syracuseStep 155507 = 233261) B233261
theorem B548741 : Blo 99781 548741 := bstep (se 4 (by rfl) ⟨51444, by rfl⟩ : syracuseStep 548741 = 102889) B102889
theorem B155537 : Blo 99781 155537 := bstep (se 2 (by rfl) ⟨58326, by rfl⟩ : syracuseStep 155537 = 116653) B116653
theorem B155555 : Blo 99781 155555 := bstep (se 1 (by rfl) ⟨116666, by rfl⟩ : syracuseStep 155555 = 233333) B233333
theorem B155585 : Blo 99781 155585 := bstep (se 2 (by rfl) ⟨58344, by rfl⟩ : syracuseStep 155585 = 116689) B116689
theorem B155603 : Blo 99781 155603 := bstep (se 1 (by rfl) ⟨116702, by rfl⟩ : syracuseStep 155603 = 233405) B233405
theorem B155633 : Blo 99781 155633 := bstep (se 2 (by rfl) ⟨58362, by rfl⟩ : syracuseStep 155633 = 116725) B116725
theorem B253955 : Blo 99781 253955 := bstep (se 1 (by rfl) ⟨190466, by rfl⟩ : syracuseStep 253955 = 380933) B380933
theorem B155651 : Blo 99781 155651 := bstep (se 1 (by rfl) ⟨116738, by rfl⟩ : syracuseStep 155651 = 233477) B233477
theorem B516131 : Blo 99781 516131 := bstep (se 1 (by rfl) ⟨387098, by rfl⟩ : syracuseStep 516131 = 774197) B774197
theorem B221297 : Blo 99781 221297 := bstep (se 2 (by rfl) ⟨82986, by rfl⟩ : syracuseStep 221297 = 165973) B165973
theorem B319697 : Blo 99781 319697 := bstep (se 2 (by rfl) ⟨119886, by rfl⟩ : syracuseStep 319697 = 239773) B239773
theorem B745699 : Blo 99781 745699 := bstep (se 1 (by rfl) ⟨559274, by rfl⟩ : syracuseStep 745699 = 1118549) B1118549
theorem B319747 : Blo 99781 319747 := bstep (se 1 (by rfl) ⟨239810, by rfl⟩ : syracuseStep 319747 = 479621) B479621
theorem B549347 : Blo 99781 549347 := bstep (se 1 (by rfl) ⟨412010, by rfl⟩ : syracuseStep 549347 = 824021) B824021
theorem B287363 : Blo 99781 287363 := bstep (se 1 (by rfl) ⟨215522, by rfl⟩ : syracuseStep 287363 = 431045) B431045
theorem B516941 : Blo 99781 516941 := bstep (se 3 (by rfl) ⟨96926, by rfl⟩ : syracuseStep 516941 = 193853) B193853
theorem B254897 : Blo 99781 254897 := bstep (se 2 (by rfl) ⟨95586, by rfl⟩ : syracuseStep 254897 = 191173) B191173
theorem B3761093 : Blo 99781 3761093 := bstep (se 4 (by rfl) ⟨352602, by rfl⟩ : syracuseStep 3761093 = 705205) B705205
theorem B254947 : Blo 99781 254947 := bstep (se 1 (by rfl) ⟨191210, by rfl⟩ : syracuseStep 254947 = 382421) B382421
theorem B320593 : Blo 99781 320593 := bstep (se 2 (by rfl) ⟨120222, by rfl⟩ : syracuseStep 320593 = 240445) B240445
theorem B255089 : Blo 99781 255089 := bstep (se 2 (by rfl) ⟨95658, by rfl⟩ : syracuseStep 255089 = 191317) B191317
theorem B124211 : Blo 99781 124211 := bstep (se 1 (by rfl) ⟨93158, by rfl⟩ : syracuseStep 124211 = 186317) B186317
theorem B189859 : Blo 99781 189859 := bstep (se 1 (by rfl) ⟨142394, by rfl⟩ : syracuseStep 189859 = 284789) B284789
theorem B583109 : Blo 99781 583109 := bstep (se 4 (by rfl) ⟨54666, by rfl⟩ : syracuseStep 583109 = 109333) B109333
theorem B190019 : Blo 99781 190019 := bstep (se 1 (by rfl) ⟨142514, by rfl⟩ : syracuseStep 190019 = 285029) B285029
theorem B353987 : Blo 99781 353987 := bstep (se 1 (by rfl) ⟨265490, by rfl⟩ : syracuseStep 353987 = 530981) B530981
theorem B386765 : Blo 99781 386765 := bstep (se 3 (by rfl) ⟨72518, by rfl⟩ : syracuseStep 386765 = 145037) B145037
theorem B288593 : Blo 99781 288593 := bstep (se 2 (by rfl) ⟨108222, by rfl⟩ : syracuseStep 288593 = 216445) B216445
theorem B124787 : Blo 99781 124787 := bstep (se 1 (by rfl) ⟨93590, by rfl⟩ : syracuseStep 124787 = 187181) B187181
theorem B256081 : Blo 99781 256081 := bstep (se 2 (by rfl) ⟨96030, by rfl⟩ : syracuseStep 256081 = 192061) B192061
theorem B583793 : Blo 99781 583793 := bstep (se 2 (by rfl) ⟨218922, by rfl⟩ : syracuseStep 583793 = 437845) B437845
theorem B780515 : Blo 99781 780515 := bstep (se 1 (by rfl) ⟨585386, by rfl⟩ : syracuseStep 780515 = 1170773) B1170773
theorem B485617 : Blo 99781 485617 := bstep (se 2 (by rfl) ⟨182106, by rfl⟩ : syracuseStep 485617 = 364213) B364213
theorem B4483349 : Blo 99781 4483349 := bstep (se 6 (by rfl) ⟨105078, by rfl⟩ : syracuseStep 4483349 = 210157) B210157
theorem B256355 : Blo 99781 256355 := bstep (se 1 (by rfl) ⟨192266, by rfl⟩ : syracuseStep 256355 = 384533) B384533
theorem B256547 : Blo 99781 256547 := bstep (se 1 (by rfl) ⟨192410, by rfl⟩ : syracuseStep 256547 = 384821) B384821
theorem B322157 : Blo 99781 322157 := bstep (se 3 (by rfl) ⟨60404, by rfl⟩ : syracuseStep 322157 = 120809) B120809
theorem B191089 : Blo 99781 191089 := bstep (se 2 (by rfl) ⟨71658, by rfl⟩ : syracuseStep 191089 = 143317) B143317
theorem B158611 : Blo 99781 158611 := bstep (se 1 (by rfl) ⟨118958, by rfl⟩ : syracuseStep 158611 = 237917) B237917
theorem B290051 : Blo 99781 290051 := bstep (se 1 (by rfl) ⟨217538, by rfl⟩ : syracuseStep 290051 = 435077) B435077
theorem B1371491 : Blo 99781 1371491 := bstep (se 1 (by rfl) ⟨1028618, by rfl⟩ : syracuseStep 1371491 = 2057237) B2057237
theorem B617827 : Blo 99781 617827 := bstep (se 1 (by rfl) ⟨463370, by rfl⟩ : syracuseStep 617827 = 926741) B926741
theorem B224657 : Blo 99781 224657 := bstep (se 2 (by rfl) ⟨84246, by rfl⟩ : syracuseStep 224657 = 168493) B168493
theorem B126355 : Blo 99781 126355 := bstep (se 1 (by rfl) ⟨94766, by rfl⟩ : syracuseStep 126355 = 189533) B189533
theorem B224675 : Blo 99781 224675 := bstep (se 1 (by rfl) ⟨168506, by rfl⟩ : syracuseStep 224675 = 337013) B337013
theorem B585157 : Blo 99781 585157 := bstep (se 4 (by rfl) ⟨54858, by rfl⟩ : syracuseStep 585157 = 109717) B109717
theorem B257489 : Blo 99781 257489 := bstep (se 2 (by rfl) ⟨96558, by rfl⟩ : syracuseStep 257489 = 193117) B193117
theorem B126451 : Blo 99781 126451 := bstep (se 1 (by rfl) ⟨94838, by rfl⟩ : syracuseStep 126451 = 189677) B189677
theorem B257539 : Blo 99781 257539 := bstep (se 1 (by rfl) ⟨193154, by rfl⟩ : syracuseStep 257539 = 386309) B386309
theorem B585251 : Blo 99781 585251 := bstep (se 1 (by rfl) ⟨438938, by rfl⟩ : syracuseStep 585251 = 877877) B877877
theorem B192145 : Blo 99781 192145 := bstep (se 2 (by rfl) ⟨72054, by rfl⟩ : syracuseStep 192145 = 144109) B144109
theorem B257681 : Blo 99781 257681 := bstep (se 2 (by rfl) ⟨96630, by rfl⟩ : syracuseStep 257681 = 193261) B193261
theorem B650915 : Blo 99781 650915 := bstep (se 1 (by rfl) ⟨488186, by rfl⟩ : syracuseStep 650915 = 976373) B976373
theorem B224945 : Blo 99781 224945 := bstep (se 2 (by rfl) ⟨84354, by rfl⟩ : syracuseStep 224945 = 168709) B168709
theorem B519857 : Blo 99781 519857 := bstep (se 2 (by rfl) ⟨194946, by rfl⟩ : syracuseStep 519857 = 389893) B389893
theorem B224963 : Blo 99781 224963 := bstep (se 1 (by rfl) ⟨168722, by rfl⟩ : syracuseStep 224963 = 337445) B337445
theorem B585413 : Blo 99781 585413 := bstep (se 4 (by rfl) ⟨54882, by rfl⟩ : syracuseStep 585413 = 109765) B109765
theorem B1175309 : Blo 99781 1175309 := bstep (se 3 (by rfl) ⟨220370, by rfl⟩ : syracuseStep 1175309 = 440741) B440741
theorem B487309 : Blo 99781 487309 := bstep (se 3 (by rfl) ⟨91370, by rfl⟩ : syracuseStep 487309 = 182741) B182741
theorem B225233 : Blo 99781 225233 := bstep (se 2 (by rfl) ⟨84462, by rfl⟩ : syracuseStep 225233 = 168925) B168925
theorem B225251 : Blo 99781 225251 := bstep (se 1 (by rfl) ⟨168938, by rfl⟩ : syracuseStep 225251 = 337877) B337877
theorem B126947 : Blo 99781 126947 := bstep (se 1 (by rfl) ⟨95210, by rfl⟩ : syracuseStep 126947 = 190421) B190421
theorem B192547 : Blo 99781 192547 := bstep (se 1 (by rfl) ⟨144410, by rfl⟩ : syracuseStep 192547 = 288821) B288821
theorem B290861 : Blo 99781 290861 := bstep (se 3 (by rfl) ⟨54536, by rfl⟩ : syracuseStep 290861 = 109073) B109073
theorem B192593 : Blo 99781 192593 := bstep (se 2 (by rfl) ⟨72222, by rfl⟩ : syracuseStep 192593 = 144445) B144445
theorem B291053 : Blo 99781 291053 := bstep (se 3 (by rfl) ⟨54572, by rfl⟩ : syracuseStep 291053 = 109145) B109145
theorem B225521 : Blo 99781 225521 := bstep (se 2 (by rfl) ⟨84570, by rfl⟩ : syracuseStep 225521 = 169141) B169141
theorem B225539 : Blo 99781 225539 := bstep (se 1 (by rfl) ⟨169154, by rfl⟩ : syracuseStep 225539 = 338309) B338309
theorem B323939 : Blo 99781 323939 := bstep (se 1 (by rfl) ⟨242954, by rfl⟩ : syracuseStep 323939 = 485909) B485909
theorem B192881 : Blo 99781 192881 := bstep (se 2 (by rfl) ⟨72330, by rfl⟩ : syracuseStep 192881 = 144661) B144661
theorem B487907 : Blo 99781 487907 := bstep (se 1 (by rfl) ⟨365930, by rfl⟩ : syracuseStep 487907 = 731861) B731861
theorem B225809 : Blo 99781 225809 := bstep (se 2 (by rfl) ⟨84678, by rfl⟩ : syracuseStep 225809 = 169357) B169357
theorem B225827 : Blo 99781 225827 := bstep (se 1 (by rfl) ⟨169370, by rfl⟩ : syracuseStep 225827 = 338741) B338741
theorem B389681 : Blo 99781 389681 := bstep (se 2 (by rfl) ⟨146130, by rfl⟩ : syracuseStep 389681 = 292261) B292261
theorem B258673 : Blo 99781 258673 := bstep (se 2 (by rfl) ⟨97002, by rfl⟩ : syracuseStep 258673 = 194005) B194005
theorem B127651 : Blo 99781 127651 := bstep (se 1 (by rfl) ⟨95738, by rfl⟩ : syracuseStep 127651 = 191477) B191477
theorem B160451 : Blo 99781 160451 := bstep (se 1 (by rfl) ⟨120338, by rfl⟩ : syracuseStep 160451 = 240677) B240677
theorem B160483 : Blo 99781 160483 := bstep (se 1 (by rfl) ⟨120362, by rfl⟩ : syracuseStep 160483 = 240725) B240725
theorem B127747 : Blo 99781 127747 := bstep (se 1 (by rfl) ⟨95810, by rfl⟩ : syracuseStep 127747 = 191621) B191621
theorem B226097 : Blo 99781 226097 := bstep (se 2 (by rfl) ⟨84786, by rfl⟩ : syracuseStep 226097 = 169573) B169573
theorem B226115 : Blo 99781 226115 := bstep (se 1 (by rfl) ⟨169586, by rfl⟩ : syracuseStep 226115 = 339173) B339173
theorem B258947 : Blo 99781 258947 := bstep (se 1 (by rfl) ⟨194210, by rfl⟩ : syracuseStep 258947 = 388421) B388421
theorem B488369 : Blo 99781 488369 := bstep (se 2 (by rfl) ⟨183138, by rfl⟩ : syracuseStep 488369 = 366277) B366277
theorem B1373237 : Blo 99781 1373237 := bstep (se 5 (by rfl) ⟨64370, by rfl⟩ : syracuseStep 1373237 = 128741) B128741
theorem B193603 : Blo 99781 193603 := bstep (se 1 (by rfl) ⟨145202, by rfl⟩ : syracuseStep 193603 = 290405) B290405
theorem B259139 : Blo 99781 259139 := bstep (se 1 (by rfl) ⟨194354, by rfl⟩ : syracuseStep 259139 = 388709) B388709
theorem B226385 : Blo 99781 226385 := bstep (se 2 (by rfl) ⟨84894, by rfl⟩ : syracuseStep 226385 = 169789) B169789
theorem B226403 : Blo 99781 226403 := bstep (se 1 (by rfl) ⟨169802, by rfl⟩ : syracuseStep 226403 = 339605) B339605
theorem B521315 : Blo 99781 521315 := bstep (se 1 (by rfl) ⟨390986, by rfl⟩ : syracuseStep 521315 = 781973) B781973
theorem B292045 : Blo 99781 292045 := bstep (se 3 (by rfl) ⟨54758, by rfl⟩ : syracuseStep 292045 = 109517) B109517
theorem B193745 : Blo 99781 193745 := bstep (se 2 (by rfl) ⟨72654, by rfl⟩ : syracuseStep 193745 = 145309) B145309
theorem B128243 : Blo 99781 128243 := bstep (se 1 (by rfl) ⟨96182, by rfl⟩ : syracuseStep 128243 = 192365) B192365
theorem B226673 : Blo 99781 226673 := bstep (se 2 (by rfl) ⟨85002, by rfl⟩ : syracuseStep 226673 = 170005) B170005
theorem B226691 : Blo 99781 226691 := bstep (se 1 (by rfl) ⟨170018, by rfl⟩ : syracuseStep 226691 = 340037) B340037
theorem B194051 : Blo 99781 194051 := bstep (se 1 (by rfl) ⟨145538, by rfl⟩ : syracuseStep 194051 = 291077) B291077
theorem B161411 : Blo 99781 161411 := bstep (se 1 (by rfl) ⟨121058, by rfl⟩ : syracuseStep 161411 = 242117) B242117
theorem B226961 : Blo 99781 226961 := bstep (se 2 (by rfl) ⟨85110, by rfl⟩ : syracuseStep 226961 = 170221) B170221
theorem B226979 : Blo 99781 226979 := bstep (se 1 (by rfl) ⟨170234, by rfl⟩ : syracuseStep 226979 = 340469) B340469
theorem B554701 : Blo 99781 554701 := bstep (se 3 (by rfl) ⟨104006, by rfl⟩ : syracuseStep 554701 = 208013) B208013
theorem B161489 : Blo 99781 161489 := bstep (se 2 (by rfl) ⟨60558, by rfl⟩ : syracuseStep 161489 = 121117) B121117
theorem B194339 : Blo 99781 194339 := bstep (se 1 (by rfl) ⟨145754, by rfl⟩ : syracuseStep 194339 = 291509) B291509
theorem B522125 : Blo 99781 522125 := bstep (se 3 (by rfl) ⟨97898, by rfl⟩ : syracuseStep 522125 = 195797) B195797
theorem B161713 : Blo 99781 161713 := bstep (se 2 (by rfl) ⟨60642, by rfl⟩ : syracuseStep 161713 = 121285) B121285
theorem B227249 : Blo 99781 227249 := bstep (se 2 (by rfl) ⟨85218, by rfl⟩ : syracuseStep 227249 = 170437) B170437
theorem B128947 : Blo 99781 128947 := bstep (se 1 (by rfl) ⟨96710, by rfl⟩ : syracuseStep 128947 = 193421) B193421
theorem B227267 : Blo 99781 227267 := bstep (se 1 (by rfl) ⟨170450, by rfl⟩ : syracuseStep 227267 = 340901) B340901
theorem B391139 : Blo 99781 391139 := bstep (se 1 (by rfl) ⟨293354, by rfl⟩ : syracuseStep 391139 = 586709) B586709
theorem B260081 : Blo 99781 260081 := bstep (se 2 (by rfl) ⟨97530, by rfl⟩ : syracuseStep 260081 = 195061) B195061
theorem B129043 : Blo 99781 129043 := bstep (se 1 (by rfl) ⟨96782, by rfl⟩ : syracuseStep 129043 = 193565) B193565
theorem B260131 : Blo 99781 260131 := bstep (se 1 (by rfl) ⟨195098, by rfl⟩ : syracuseStep 260131 = 390197) B390197
theorem B325745 : Blo 99781 325745 := bstep (se 2 (by rfl) ⟨122154, by rfl⟩ : syracuseStep 325745 = 244309) B244309
theorem B325795 : Blo 99781 325795 := bstep (se 1 (by rfl) ⟨244346, by rfl⟩ : syracuseStep 325795 = 488693) B488693
theorem B260273 : Blo 99781 260273 := bstep (se 2 (by rfl) ⟨97602, by rfl⟩ : syracuseStep 260273 = 195205) B195205
theorem B1308869 : Blo 99781 1308869 := bstep (se 4 (by rfl) ⟨122706, by rfl⟩ : syracuseStep 1308869 = 245413) B245413
theorem B227537 : Blo 99781 227537 := bstep (se 2 (by rfl) ⟨85326, by rfl⟩ : syracuseStep 227537 = 170653) B170653
theorem B227555 : Blo 99781 227555 := bstep (se 1 (by rfl) ⟨170666, by rfl⟩ : syracuseStep 227555 = 341333) B341333
theorem B981233 : Blo 99781 981233 := bstep (se 2 (by rfl) ⟨367962, by rfl⟩ : syracuseStep 981233 = 735925) B735925
theorem B227825 : Blo 99781 227825 := bstep (se 2 (by rfl) ⟨85434, by rfl⟩ : syracuseStep 227825 = 170869) B170869
theorem B227843 : Blo 99781 227843 := bstep (se 1 (by rfl) ⟨170882, by rfl⟩ : syracuseStep 227843 = 341765) B341765
theorem B129539 : Blo 99781 129539 := bstep (se 1 (by rfl) ⟨97154, by rfl⟩ : syracuseStep 129539 = 194309) B194309
theorem B752141 : Blo 99781 752141 := bstep (se 3 (by rfl) ⟨141026, by rfl⟩ : syracuseStep 752141 = 282053) B282053
theorem B1309283 : Blo 99781 1309283 := bstep (se 1 (by rfl) ⟨981962, by rfl⟩ : syracuseStep 1309283 = 1963925) B1963925
theorem B588485 : Blo 99781 588485 := bstep (se 4 (by rfl) ⟨55170, by rfl⟩ : syracuseStep 588485 = 110341) B110341
theorem B195281 : Blo 99781 195281 := bstep (se 2 (by rfl) ⟨73230, by rfl⟩ : syracuseStep 195281 = 146461) B146461
theorem B228113 : Blo 99781 228113 := bstep (se 2 (by rfl) ⟨85542, by rfl⟩ : syracuseStep 228113 = 171085) B171085
theorem B228131 : Blo 99781 228131 := bstep (se 1 (by rfl) ⟨171098, by rfl⟩ : syracuseStep 228131 = 342197) B342197
theorem B326513 : Blo 99781 326513 := bstep (se 2 (by rfl) ⟨122442, by rfl⟩ : syracuseStep 326513 = 244885) B244885
theorem B293777 : Blo 99781 293777 := bstep (se 2 (by rfl) ⟨110166, by rfl⟩ : syracuseStep 293777 = 220333) B220333
theorem B392141 : Blo 99781 392141 := bstep (se 3 (by rfl) ⟨73526, by rfl⟩ : syracuseStep 392141 = 147053) B147053
theorem B228401 : Blo 99781 228401 := bstep (se 2 (by rfl) ⟨85650, by rfl⟩ : syracuseStep 228401 = 171301) B171301
theorem B228419 : Blo 99781 228419 := bstep (se 1 (by rfl) ⟨171314, by rfl⟩ : syracuseStep 228419 = 342629) B342629
theorem B293969 : Blo 99781 293969 := bstep (se 2 (by rfl) ⟨110238, by rfl⟩ : syracuseStep 293969 = 220477) B220477
theorem B588941 : Blo 99781 588941 := bstep (se 3 (by rfl) ⟨110426, by rfl⟩ : syracuseStep 588941 = 220853) B220853
theorem B261265 : Blo 99781 261265 := bstep (se 2 (by rfl) ⟨97974, by rfl⟩ : syracuseStep 261265 = 195949) B195949
theorem B130243 : Blo 99781 130243 := bstep (se 1 (by rfl) ⟨97682, by rfl⟩ : syracuseStep 130243 = 195365) B195365
theorem B130339 : Blo 99781 130339 := bstep (se 1 (by rfl) ⟨97754, by rfl⟩ : syracuseStep 130339 = 195509) B195509
theorem B228689 : Blo 99781 228689 := bstep (se 2 (by rfl) ⟨85758, by rfl⟩ : syracuseStep 228689 = 171517) B171517
theorem B228707 : Blo 99781 228707 := bstep (se 1 (by rfl) ⟨171530, by rfl⟩ : syracuseStep 228707 = 343061) B343061
theorem B327025 : Blo 99781 327025 := bstep (se 2 (by rfl) ⟨122634, by rfl⟩ : syracuseStep 327025 = 245269) B245269
theorem B1441165 : Blo 99781 1441165 := bstep (se 3 (by rfl) ⟨270218, by rfl⟩ : syracuseStep 1441165 = 540437) B540437
theorem B261539 : Blo 99781 261539 := bstep (se 1 (by rfl) ⟨196154, by rfl⟩ : syracuseStep 261539 = 392309) B392309
theorem B785861 : Blo 99781 785861 := bstep (se 4 (by rfl) ⟨73674, by rfl⟩ : syracuseStep 785861 = 147349) B147349
theorem B2227733 : Blo 99781 2227733 := bstep (se 6 (by rfl) ⟨52212, by rfl⟩ : syracuseStep 2227733 = 104425) B104425
theorem B196177 : Blo 99781 196177 := bstep (se 2 (by rfl) ⟨73566, by rfl⟩ : syracuseStep 196177 = 147133) B147133
theorem B261731 : Blo 99781 261731 := bstep (se 1 (by rfl) ⟨196298, by rfl⟩ : syracuseStep 261731 = 392597) B392597
theorem B228977 : Blo 99781 228977 := bstep (se 2 (by rfl) ⟨85866, by rfl⟩ : syracuseStep 228977 = 171733) B171733
theorem B228995 : Blo 99781 228995 := bstep (se 1 (by rfl) ⟨171746, by rfl⟩ : syracuseStep 228995 = 343493) B343493
theorem B163475 : Blo 99781 163475 := bstep (se 1 (by rfl) ⟨122606, by rfl⟩ : syracuseStep 163475 = 245213) B245213
theorem B196337 : Blo 99781 196337 := bstep (se 2 (by rfl) ⟨73626, by rfl⟩ : syracuseStep 196337 = 147253) B147253
theorem B130835 : Blo 99781 130835 := bstep (se 1 (by rfl) ⟨98126, by rfl⟩ : syracuseStep 130835 = 196253) B196253
theorem B163667 : Blo 99781 163667 := bstep (se 1 (by rfl) ⟨122750, by rfl⟩ : syracuseStep 163667 = 245501) B245501
theorem B229265 : Blo 99781 229265 := bstep (se 2 (by rfl) ⟨85974, by rfl⟩ : syracuseStep 229265 = 171949) B171949
theorem B229283 : Blo 99781 229283 := bstep (se 1 (by rfl) ⟨171962, by rfl⟩ : syracuseStep 229283 = 343925) B343925
theorem B163795 : Blo 99781 163795 := bstep (se 1 (by rfl) ⟨122846, by rfl⟩ : syracuseStep 163795 = 245693) B245693
theorem B229427 : Blo 99781 229427 := bstep (se 1 (by rfl) ⟨172070, by rfl⟩ : syracuseStep 229427 = 344141) B344141
theorem B393281 : Blo 99781 393281 := bstep (se 2 (by rfl) ⟨147480, by rfl⟩ : syracuseStep 393281 = 294961) B294961
theorem B229463 : Blo 99781 229463 := bstep (se 1 (by rfl) ⟨172097, by rfl⟩ : syracuseStep 229463 = 344195) B344195
theorem B131159 : Blo 99781 131159 := bstep (se 1 (by rfl) ⟨98369, by rfl⟩ : syracuseStep 131159 = 196739) B196739
theorem B884915 : Blo 99781 884915 := bstep (se 1 (by rfl) ⟨663686, by rfl⟩ : syracuseStep 884915 = 1327373) B1327373
theorem B196823 : Blo 99781 196823 := bstep (se 1 (by rfl) ⟨147617, by rfl⟩ : syracuseStep 196823 = 295235) B295235
theorem B229643 : Blo 99781 229643 := bstep (se 1 (by rfl) ⟨172232, by rfl⟩ : syracuseStep 229643 = 344465) B344465
theorem B590125 : Blo 99781 590125 := bstep (se 3 (by rfl) ⟨110648, by rfl⟩ : syracuseStep 590125 = 221297) B221297
theorem B229697 : Blo 99781 229697 := bstep (se 2 (by rfl) ⟨86136, by rfl⟩ : syracuseStep 229697 = 172273) B172273
theorem B426329 : Blo 99781 426329 := bstep (se 2 (by rfl) ⟨159873, by rfl⟩ : syracuseStep 426329 = 319747) B319747
theorem B328153 : Blo 99781 328153 := bstep (se 2 (by rfl) ⟨123057, by rfl⟩ : syracuseStep 328153 = 246115) B246115
theorem B229913 : Blo 99781 229913 := bstep (se 2 (by rfl) ⟨86217, by rfl⟩ : syracuseStep 229913 = 172435) B172435
theorem B230003 : Blo 99781 230003 := bstep (se 1 (by rfl) ⟨172502, by rfl⟩ : syracuseStep 230003 = 345005) B345005
theorem B230039 : Blo 99781 230039 := bstep (se 1 (by rfl) ⟨172529, by rfl⟩ : syracuseStep 230039 = 345059) B345059
theorem B230219 : Blo 99781 230219 := bstep (se 1 (by rfl) ⟨172664, by rfl⟩ : syracuseStep 230219 = 345329) B345329
theorem B230273 : Blo 99781 230273 := bstep (se 2 (by rfl) ⟨86352, by rfl⟩ : syracuseStep 230273 = 172705) B172705
theorem B361361 : Blo 99781 361361 := bstep (se 2 (by rfl) ⟨135510, by rfl⟩ : syracuseStep 361361 = 271021) B271021
theorem B328769 : Blo 99781 328769 := bstep (se 2 (by rfl) ⟨123288, by rfl⟩ : syracuseStep 328769 = 246577) B246577
theorem B230489 : Blo 99781 230489 := bstep (se 2 (by rfl) ⟨86433, by rfl⟩ : syracuseStep 230489 = 172867) B172867
theorem B230579 : Blo 99781 230579 := bstep (se 1 (by rfl) ⟨172934, by rfl⟩ : syracuseStep 230579 = 345869) B345869
theorem B230615 : Blo 99781 230615 := bstep (se 1 (by rfl) ⟨172961, by rfl⟩ : syracuseStep 230615 = 345923) B345923
theorem B885977 : Blo 99781 885977 := bstep (se 2 (by rfl) ⟨332241, by rfl⟩ : syracuseStep 885977 = 664483) B664483
theorem B787805 : Blo 99781 787805 := bstep (se 3 (by rfl) ⟨147713, by rfl⟩ : syracuseStep 787805 = 295427) B295427
theorem B230795 : Blo 99781 230795 := bstep (se 1 (by rfl) ⟨173096, by rfl⟩ : syracuseStep 230795 = 346193) B346193
theorem B656819 : Blo 99781 656819 := bstep (se 1 (by rfl) ⟨492614, by rfl⟩ : syracuseStep 656819 = 985229) B985229
theorem B427457 : Blo 99781 427457 := bstep (se 2 (by rfl) ⟨160296, by rfl⟩ : syracuseStep 427457 = 320593) B320593
theorem B230849 : Blo 99781 230849 := bstep (se 2 (by rfl) ⟨86568, by rfl⟩ : syracuseStep 230849 = 173137) B173137
theorem B99787 : Blo 99781 99787 := bstep (se 1 (by rfl) ⟨74840, by rfl⟩ : syracuseStep 99787 = 149681) B149681
theorem B99799 : Blo 99781 99799 := bstep (se 1 (by rfl) ⟨74849, by rfl⟩ : syracuseStep 99799 = 149699) B149699
theorem B99819 : Blo 99781 99819 := bstep (se 1 (by rfl) ⟨74864, by rfl⟩ : syracuseStep 99819 = 149729) B149729
theorem B99831 : Blo 99781 99831 := bstep (se 1 (by rfl) ⟨74873, by rfl⟩ : syracuseStep 99831 = 149747) B149747
theorem B99851 : Blo 99781 99851 := bstep (se 1 (by rfl) ⟨74888, by rfl⟩ : syracuseStep 99851 = 149777) B149777
theorem B99863 : Blo 99781 99863 := bstep (se 1 (by rfl) ⟨74897, by rfl⟩ : syracuseStep 99863 = 149795) B149795
theorem B99883 : Blo 99781 99883 := bstep (se 1 (by rfl) ⟨74912, by rfl⟩ : syracuseStep 99883 = 149825) B149825
theorem B99895 : Blo 99781 99895 := bstep (se 1 (by rfl) ⟨74921, by rfl⟩ : syracuseStep 99895 = 149843) B149843
theorem B99915 : Blo 99781 99915 := bstep (se 1 (by rfl) ⟨74936, by rfl⟩ : syracuseStep 99915 = 149873) B149873
theorem B99927 : Blo 99781 99927 := bstep (se 1 (by rfl) ⟨74945, by rfl⟩ : syracuseStep 99927 = 149891) B149891
theorem B99947 : Blo 99781 99947 := bstep (se 1 (by rfl) ⟨74960, by rfl⟩ : syracuseStep 99947 = 149921) B149921
theorem B99959 : Blo 99781 99959 := bstep (se 1 (by rfl) ⟨74969, by rfl⟩ : syracuseStep 99959 = 149939) B149939
theorem B99979 : Blo 99781 99979 := bstep (se 1 (by rfl) ⟨74984, by rfl⟩ : syracuseStep 99979 = 149969) B149969
theorem B99991 : Blo 99781 99991 := bstep (se 1 (by rfl) ⟨74993, by rfl⟩ : syracuseStep 99991 = 149987) B149987
theorem B231065 : Blo 99781 231065 := bstep (se 2 (by rfl) ⟨86649, by rfl⟩ : syracuseStep 231065 = 173299) B173299
theorem B100011 : Blo 99781 100011 := bstep (se 1 (by rfl) ⟨75008, by rfl⟩ : syracuseStep 100011 = 150017) B150017
theorem B100023 : Blo 99781 100023 := bstep (se 1 (by rfl) ⟨75017, by rfl⟩ : syracuseStep 100023 = 150035) B150035
theorem B100043 : Blo 99781 100043 := bstep (se 1 (by rfl) ⟨75032, by rfl⟩ : syracuseStep 100043 = 150065) B150065
theorem B100055 : Blo 99781 100055 := bstep (se 1 (by rfl) ⟨75041, by rfl⟩ : syracuseStep 100055 = 150083) B150083
theorem B100075 : Blo 99781 100075 := bstep (se 1 (by rfl) ⟨75056, by rfl⟩ : syracuseStep 100075 = 150113) B150113
theorem B231155 : Blo 99781 231155 := bstep (se 1 (by rfl) ⟨173366, by rfl⟩ : syracuseStep 231155 = 346733) B346733
theorem B100087 : Blo 99781 100087 := bstep (se 1 (by rfl) ⟨75065, by rfl⟩ : syracuseStep 100087 = 150131) B150131
theorem B100107 : Blo 99781 100107 := bstep (se 1 (by rfl) ⟨75080, by rfl⟩ : syracuseStep 100107 = 150161) B150161
theorem B100119 : Blo 99781 100119 := bstep (se 1 (by rfl) ⟨75089, by rfl⟩ : syracuseStep 100119 = 150179) B150179
theorem B231191 : Blo 99781 231191 := bstep (se 1 (by rfl) ⟨173393, by rfl⟩ : syracuseStep 231191 = 346787) B346787
theorem B100139 : Blo 99781 100139 := bstep (se 1 (by rfl) ⟨75104, by rfl⟩ : syracuseStep 100139 = 150209) B150209
theorem B3573557 : Blo 99781 3573557 := bstep (se 5 (by rfl) ⟨167510, by rfl⟩ : syracuseStep 3573557 = 335021) B335021
theorem B100151 : Blo 99781 100151 := bstep (se 1 (by rfl) ⟨75113, by rfl⟩ : syracuseStep 100151 = 150227) B150227
theorem B100171 : Blo 99781 100171 := bstep (se 1 (by rfl) ⟨75128, by rfl⟩ : syracuseStep 100171 = 150257) B150257
theorem B100183 : Blo 99781 100183 := bstep (se 1 (by rfl) ⟨75137, by rfl⟩ : syracuseStep 100183 = 150275) B150275
theorem B100203 : Blo 99781 100203 := bstep (se 1 (by rfl) ⟨75152, by rfl⟩ : syracuseStep 100203 = 150305) B150305
theorem B100215 : Blo 99781 100215 := bstep (se 1 (by rfl) ⟨75161, by rfl⟩ : syracuseStep 100215 = 150323) B150323
theorem B100235 : Blo 99781 100235 := bstep (se 1 (by rfl) ⟨75176, by rfl⟩ : syracuseStep 100235 = 150353) B150353
theorem B100247 : Blo 99781 100247 := bstep (se 1 (by rfl) ⟨75185, by rfl⟩ : syracuseStep 100247 = 150371) B150371
theorem B100267 : Blo 99781 100267 := bstep (se 1 (by rfl) ⟨75200, by rfl⟩ : syracuseStep 100267 = 150401) B150401
theorem B100279 : Blo 99781 100279 := bstep (se 1 (by rfl) ⟨75209, by rfl⟩ : syracuseStep 100279 = 150419) B150419
theorem B100299 : Blo 99781 100299 := bstep (se 1 (by rfl) ⟨75224, by rfl⟩ : syracuseStep 100299 = 150449) B150449
theorem B231371 : Blo 99781 231371 := bstep (se 1 (by rfl) ⟨173528, by rfl⟩ : syracuseStep 231371 = 347057) B347057
theorem B100311 : Blo 99781 100311 := bstep (se 1 (by rfl) ⟨75233, by rfl⟩ : syracuseStep 100311 = 150467) B150467
theorem B526297 : Blo 99781 526297 := bstep (se 2 (by rfl) ⟨197361, by rfl⟩ : syracuseStep 526297 = 394723) B394723
theorem B100331 : Blo 99781 100331 := bstep (se 1 (by rfl) ⟨75248, by rfl⟩ : syracuseStep 100331 = 150497) B150497
theorem B100343 : Blo 99781 100343 := bstep (se 1 (by rfl) ⟨75257, by rfl⟩ : syracuseStep 100343 = 150515) B150515
theorem B231425 : Blo 99781 231425 := bstep (se 2 (by rfl) ⟨86784, by rfl⟩ : syracuseStep 231425 = 173569) B173569
theorem B100363 : Blo 99781 100363 := bstep (se 1 (by rfl) ⟨75272, by rfl⟩ : syracuseStep 100363 = 150545) B150545
theorem B100375 : Blo 99781 100375 := bstep (se 1 (by rfl) ⟨75281, by rfl⟩ : syracuseStep 100375 = 150563) B150563
theorem B100395 : Blo 99781 100395 := bstep (se 1 (by rfl) ⟨75296, by rfl⟩ : syracuseStep 100395 = 150593) B150593
theorem B100407 : Blo 99781 100407 := bstep (se 1 (by rfl) ⟨75305, by rfl⟩ : syracuseStep 100407 = 150611) B150611
theorem B100427 : Blo 99781 100427 := bstep (se 1 (by rfl) ⟨75320, by rfl⟩ : syracuseStep 100427 = 150641) B150641
theorem B100439 : Blo 99781 100439 := bstep (se 1 (by rfl) ⟨75329, by rfl⟩ : syracuseStep 100439 = 150659) B150659
theorem B100459 : Blo 99781 100459 := bstep (se 1 (by rfl) ⟨75344, by rfl⟩ : syracuseStep 100459 = 150689) B150689
theorem B100471 : Blo 99781 100471 := bstep (se 1 (by rfl) ⟨75353, by rfl⟩ : syracuseStep 100471 = 150707) B150707
theorem B100491 : Blo 99781 100491 := bstep (se 1 (by rfl) ⟨75368, by rfl⟩ : syracuseStep 100491 = 150737) B150737
theorem B100503 : Blo 99781 100503 := bstep (se 1 (by rfl) ⟨75377, by rfl⟩ : syracuseStep 100503 = 150755) B150755
theorem B100523 : Blo 99781 100523 := bstep (se 1 (by rfl) ⟨75392, by rfl⟩ : syracuseStep 100523 = 150785) B150785
theorem B100535 : Blo 99781 100535 := bstep (se 1 (by rfl) ⟨75401, by rfl⟩ : syracuseStep 100535 = 150803) B150803
theorem B100555 : Blo 99781 100555 := bstep (se 1 (by rfl) ⟨75416, by rfl⟩ : syracuseStep 100555 = 150833) B150833
theorem B100567 : Blo 99781 100567 := bstep (se 1 (by rfl) ⟨75425, by rfl⟩ : syracuseStep 100567 = 150851) B150851
theorem B231641 : Blo 99781 231641 := bstep (se 2 (by rfl) ⟨86865, by rfl⟩ : syracuseStep 231641 = 173731) B173731
theorem B100587 : Blo 99781 100587 := bstep (se 1 (by rfl) ⟨75440, by rfl⟩ : syracuseStep 100587 = 150881) B150881
theorem B100599 : Blo 99781 100599 := bstep (se 1 (by rfl) ⟨75449, by rfl⟩ : syracuseStep 100599 = 150899) B150899
theorem B100619 : Blo 99781 100619 := bstep (se 1 (by rfl) ⟨75464, by rfl⟩ : syracuseStep 100619 = 150929) B150929
theorem B100631 : Blo 99781 100631 := bstep (se 1 (by rfl) ⟨75473, by rfl⟩ : syracuseStep 100631 = 150947) B150947
theorem B100651 : Blo 99781 100651 := bstep (se 1 (by rfl) ⟨75488, by rfl⟩ : syracuseStep 100651 = 150977) B150977
theorem B231731 : Blo 99781 231731 := bstep (se 1 (by rfl) ⟨173798, by rfl⟩ : syracuseStep 231731 = 347597) B347597
theorem B100663 : Blo 99781 100663 := bstep (se 1 (by rfl) ⟨75497, by rfl⟩ : syracuseStep 100663 = 150995) B150995
theorem B919873 : Blo 99781 919873 := bstep (se 2 (by rfl) ⟨344952, by rfl⟩ : syracuseStep 919873 = 689905) B689905
theorem B100683 : Blo 99781 100683 := bstep (se 1 (by rfl) ⟨75512, by rfl⟩ : syracuseStep 100683 = 151025) B151025
theorem B100695 : Blo 99781 100695 := bstep (se 1 (by rfl) ⟨75521, by rfl⟩ : syracuseStep 100695 = 151043) B151043
theorem B231767 : Blo 99781 231767 := bstep (se 1 (by rfl) ⟨173825, by rfl⟩ : syracuseStep 231767 = 347651) B347651
theorem B100715 : Blo 99781 100715 := bstep (se 1 (by rfl) ⟨75536, by rfl⟩ : syracuseStep 100715 = 151073) B151073
theorem B100727 : Blo 99781 100727 := bstep (se 1 (by rfl) ⟨75545, by rfl⟩ : syracuseStep 100727 = 151091) B151091
theorem B100747 : Blo 99781 100747 := bstep (se 1 (by rfl) ⟨75560, by rfl⟩ : syracuseStep 100747 = 151121) B151121
theorem B100759 : Blo 99781 100759 := bstep (se 1 (by rfl) ⟨75569, by rfl⟩ : syracuseStep 100759 = 151139) B151139
theorem B100779 : Blo 99781 100779 := bstep (se 1 (by rfl) ⟨75584, by rfl⟩ : syracuseStep 100779 = 151169) B151169
theorem B526771 : Blo 99781 526771 := bstep (se 1 (by rfl) ⟨395078, by rfl⟩ : syracuseStep 526771 = 790157) B790157
theorem B100791 : Blo 99781 100791 := bstep (se 1 (by rfl) ⟨75593, by rfl⟩ : syracuseStep 100791 = 151187) B151187
theorem B100811 : Blo 99781 100811 := bstep (se 1 (by rfl) ⟨75608, by rfl⟩ : syracuseStep 100811 = 151217) B151217
theorem B100823 : Blo 99781 100823 := bstep (se 1 (by rfl) ⟨75617, by rfl⟩ : syracuseStep 100823 = 151235) B151235
theorem B100843 : Blo 99781 100843 := bstep (se 1 (by rfl) ⟨75632, by rfl⟩ : syracuseStep 100843 = 151265) B151265
theorem B100855 : Blo 99781 100855 := bstep (se 1 (by rfl) ⟨75641, by rfl⟩ : syracuseStep 100855 = 151283) B151283
theorem B100875 : Blo 99781 100875 := bstep (se 1 (by rfl) ⟨75656, by rfl⟩ : syracuseStep 100875 = 151313) B151313
theorem B231947 : Blo 99781 231947 := bstep (se 1 (by rfl) ⟨173960, by rfl⟩ : syracuseStep 231947 = 347921) B347921
theorem B100887 : Blo 99781 100887 := bstep (se 1 (by rfl) ⟨75665, by rfl⟩ : syracuseStep 100887 = 151331) B151331
theorem B231959 : Blo 99781 231959 := bstep (se 1 (by rfl) ⟨173969, by rfl⟩ : syracuseStep 231959 = 347939) B347939
theorem B100907 : Blo 99781 100907 := bstep (se 1 (by rfl) ⟨75680, by rfl⟩ : syracuseStep 100907 = 151361) B151361
theorem B100919 : Blo 99781 100919 := bstep (se 1 (by rfl) ⟨75689, by rfl⟩ : syracuseStep 100919 = 151379) B151379
theorem B232001 : Blo 99781 232001 := bstep (se 2 (by rfl) ⟨87000, by rfl⟩ : syracuseStep 232001 = 174001) B174001
theorem B100939 : Blo 99781 100939 := bstep (se 1 (by rfl) ⟨75704, by rfl⟩ : syracuseStep 100939 = 151409) B151409
theorem B100951 : Blo 99781 100951 := bstep (se 1 (by rfl) ⟨75713, by rfl⟩ : syracuseStep 100951 = 151427) B151427
theorem B100971 : Blo 99781 100971 := bstep (se 1 (by rfl) ⟨75728, by rfl⟩ : syracuseStep 100971 = 151457) B151457
theorem B100983 : Blo 99781 100983 := bstep (se 1 (by rfl) ⟨75737, by rfl⟩ : syracuseStep 100983 = 151475) B151475
theorem B101003 : Blo 99781 101003 := bstep (se 1 (by rfl) ⟨75752, by rfl⟩ : syracuseStep 101003 = 151505) B151505
theorem B101015 : Blo 99781 101015 := bstep (se 1 (by rfl) ⟨75761, by rfl⟩ : syracuseStep 101015 = 151523) B151523
theorem B101035 : Blo 99781 101035 := bstep (se 1 (by rfl) ⟨75776, by rfl⟩ : syracuseStep 101035 = 151553) B151553
theorem B101047 : Blo 99781 101047 := bstep (se 1 (by rfl) ⟨75785, by rfl⟩ : syracuseStep 101047 = 151571) B151571
theorem B101067 : Blo 99781 101067 := bstep (se 1 (by rfl) ⟨75800, by rfl⟩ : syracuseStep 101067 = 151601) B151601
theorem B101079 : Blo 99781 101079 := bstep (se 1 (by rfl) ⟨75809, by rfl⟩ : syracuseStep 101079 = 151619) B151619
theorem B101099 : Blo 99781 101099 := bstep (se 1 (by rfl) ⟨75824, by rfl⟩ : syracuseStep 101099 = 151649) B151649
theorem B101111 : Blo 99781 101111 := bstep (se 1 (by rfl) ⟨75833, by rfl⟩ : syracuseStep 101111 = 151667) B151667
theorem B101131 : Blo 99781 101131 := bstep (se 1 (by rfl) ⟨75848, by rfl⟩ : syracuseStep 101131 = 151697) B151697
theorem B101143 : Blo 99781 101143 := bstep (se 1 (by rfl) ⟨75857, by rfl⟩ : syracuseStep 101143 = 151715) B151715
theorem B297751 : Blo 99781 297751 := bstep (se 1 (by rfl) ⟨223313, by rfl⟩ : syracuseStep 297751 = 446627) B446627
theorem B232217 : Blo 99781 232217 := bstep (se 2 (by rfl) ⟨87081, by rfl⟩ : syracuseStep 232217 = 174163) B174163
theorem B101163 : Blo 99781 101163 := bstep (se 1 (by rfl) ⟨75872, by rfl⟩ : syracuseStep 101163 = 151745) B151745
theorem B101175 : Blo 99781 101175 := bstep (se 1 (by rfl) ⟨75881, by rfl⟩ : syracuseStep 101175 = 151763) B151763
theorem B101195 : Blo 99781 101195 := bstep (se 1 (by rfl) ⟨75896, by rfl⟩ : syracuseStep 101195 = 151793) B151793
theorem B101207 : Blo 99781 101207 := bstep (se 1 (by rfl) ⟨75905, by rfl⟩ : syracuseStep 101207 = 151811) B151811
theorem B101227 : Blo 99781 101227 := bstep (se 1 (by rfl) ⟨75920, by rfl⟩ : syracuseStep 101227 = 151841) B151841
theorem B232307 : Blo 99781 232307 := bstep (se 1 (by rfl) ⟨174230, by rfl⟩ : syracuseStep 232307 = 348461) B348461
theorem B101239 : Blo 99781 101239 := bstep (se 1 (by rfl) ⟨75929, by rfl⟩ : syracuseStep 101239 = 151859) B151859
theorem B101259 : Blo 99781 101259 := bstep (se 1 (by rfl) ⟨75944, by rfl⟩ : syracuseStep 101259 = 151889) B151889
theorem B101271 : Blo 99781 101271 := bstep (se 1 (by rfl) ⟨75953, by rfl⟩ : syracuseStep 101271 = 151907) B151907
theorem B232343 : Blo 99781 232343 := bstep (se 1 (by rfl) ⟨174257, by rfl⟩ : syracuseStep 232343 = 348515) B348515
theorem B101291 : Blo 99781 101291 := bstep (se 1 (by rfl) ⟨75968, by rfl⟩ : syracuseStep 101291 = 151937) B151937
theorem B363437 : Blo 99781 363437 := bstep (se 3 (by rfl) ⟨68144, by rfl⟩ : syracuseStep 363437 = 136289) B136289
theorem B101303 : Blo 99781 101303 := bstep (se 1 (by rfl) ⟨75977, by rfl⟩ : syracuseStep 101303 = 151955) B151955
theorem B101323 : Blo 99781 101323 := bstep (se 1 (by rfl) ⟨75992, by rfl⟩ : syracuseStep 101323 = 151985) B151985
theorem B101335 : Blo 99781 101335 := bstep (se 1 (by rfl) ⟨76001, by rfl⟩ : syracuseStep 101335 = 152003) B152003
theorem B101355 : Blo 99781 101355 := bstep (se 1 (by rfl) ⟨76016, by rfl⟩ : syracuseStep 101355 = 152033) B152033
theorem B101367 : Blo 99781 101367 := bstep (se 1 (by rfl) ⟨76025, by rfl⟩ : syracuseStep 101367 = 152051) B152051
theorem B101387 : Blo 99781 101387 := bstep (se 1 (by rfl) ⟨76040, by rfl⟩ : syracuseStep 101387 = 152081) B152081
theorem B101399 : Blo 99781 101399 := bstep (se 1 (by rfl) ⟨76049, by rfl⟩ : syracuseStep 101399 = 152099) B152099
theorem B101419 : Blo 99781 101419 := bstep (se 1 (by rfl) ⟨76064, by rfl⟩ : syracuseStep 101419 = 152129) B152129
theorem B101431 : Blo 99781 101431 := bstep (se 1 (by rfl) ⟨76073, by rfl⟩ : syracuseStep 101431 = 152147) B152147
theorem B429131 : Blo 99781 429131 := bstep (se 1 (by rfl) ⟨321848, by rfl⟩ : syracuseStep 429131 = 643697) B643697
theorem B101451 : Blo 99781 101451 := bstep (se 1 (by rfl) ⟨76088, by rfl⟩ : syracuseStep 101451 = 152177) B152177
theorem B232523 : Blo 99781 232523 := bstep (se 1 (by rfl) ⟨174392, by rfl⟩ : syracuseStep 232523 = 348785) B348785
theorem B101463 : Blo 99781 101463 := bstep (se 1 (by rfl) ⟨76097, by rfl⟩ : syracuseStep 101463 = 152195) B152195
theorem B101483 : Blo 99781 101483 := bstep (se 1 (by rfl) ⟨76112, by rfl⟩ : syracuseStep 101483 = 152225) B152225
theorem B101495 : Blo 99781 101495 := bstep (se 1 (by rfl) ⟨76121, by rfl⟩ : syracuseStep 101495 = 152243) B152243
theorem B232577 : Blo 99781 232577 := bstep (se 2 (by rfl) ⟨87216, by rfl⟩ : syracuseStep 232577 = 174433) B174433
theorem B101515 : Blo 99781 101515 := bstep (se 1 (by rfl) ⟨76136, by rfl⟩ : syracuseStep 101515 = 152273) B152273
theorem B101527 : Blo 99781 101527 := bstep (se 1 (by rfl) ⟨76145, by rfl⟩ : syracuseStep 101527 = 152291) B152291
theorem B101547 : Blo 99781 101547 := bstep (se 1 (by rfl) ⟨76160, by rfl⟩ : syracuseStep 101547 = 152321) B152321
theorem B101559 : Blo 99781 101559 := bstep (se 1 (by rfl) ⟨76169, by rfl⟩ : syracuseStep 101559 = 152339) B152339
theorem B101579 : Blo 99781 101579 := bstep (se 1 (by rfl) ⟨76184, by rfl⟩ : syracuseStep 101579 = 152369) B152369
theorem B101591 : Blo 99781 101591 := bstep (se 1 (by rfl) ⟨76193, by rfl⟩ : syracuseStep 101591 = 152387) B152387
theorem B101611 : Blo 99781 101611 := bstep (se 1 (by rfl) ⟨76208, by rfl⟩ : syracuseStep 101611 = 152417) B152417
theorem B101623 : Blo 99781 101623 := bstep (se 1 (by rfl) ⟨76217, by rfl⟩ : syracuseStep 101623 = 152435) B152435
theorem B101643 : Blo 99781 101643 := bstep (se 1 (by rfl) ⟨76232, by rfl⟩ : syracuseStep 101643 = 152465) B152465
theorem B101655 : Blo 99781 101655 := bstep (se 1 (by rfl) ⟨76241, by rfl⟩ : syracuseStep 101655 = 152483) B152483
theorem B101675 : Blo 99781 101675 := bstep (se 1 (by rfl) ⟨76256, by rfl⟩ : syracuseStep 101675 = 152513) B152513
theorem B101687 : Blo 99781 101687 := bstep (se 1 (by rfl) ⟨76265, by rfl⟩ : syracuseStep 101687 = 152531) B152531
theorem B101707 : Blo 99781 101707 := bstep (se 1 (by rfl) ⟨76280, by rfl⟩ : syracuseStep 101707 = 152561) B152561
theorem B101719 : Blo 99781 101719 := bstep (se 1 (by rfl) ⟨76289, by rfl⟩ : syracuseStep 101719 = 152579) B152579
theorem B232793 : Blo 99781 232793 := bstep (se 2 (by rfl) ⟨87297, by rfl⟩ : syracuseStep 232793 = 174595) B174595
theorem B101739 : Blo 99781 101739 := bstep (se 1 (by rfl) ⟨76304, by rfl⟩ : syracuseStep 101739 = 152609) B152609
theorem B101751 : Blo 99781 101751 := bstep (se 1 (by rfl) ⟨76313, by rfl⟩ : syracuseStep 101751 = 152627) B152627
theorem B101771 : Blo 99781 101771 := bstep (se 1 (by rfl) ⟨76328, by rfl⟩ : syracuseStep 101771 = 152657) B152657
theorem B101783 : Blo 99781 101783 := bstep (se 1 (by rfl) ⟨76337, by rfl⟩ : syracuseStep 101783 = 152675) B152675
theorem B101803 : Blo 99781 101803 := bstep (se 1 (by rfl) ⟨76352, by rfl⟩ : syracuseStep 101803 = 152705) B152705
theorem B232883 : Blo 99781 232883 := bstep (se 1 (by rfl) ⟨174662, by rfl⟩ : syracuseStep 232883 = 349325) B349325
theorem B101815 : Blo 99781 101815 := bstep (se 1 (by rfl) ⟨76361, by rfl⟩ : syracuseStep 101815 = 152723) B152723
theorem B101835 : Blo 99781 101835 := bstep (se 1 (by rfl) ⟨76376, by rfl⟩ : syracuseStep 101835 = 152753) B152753
theorem B101847 : Blo 99781 101847 := bstep (se 1 (by rfl) ⟨76385, by rfl⟩ : syracuseStep 101847 = 152771) B152771
theorem B232919 : Blo 99781 232919 := bstep (se 1 (by rfl) ⟨174689, by rfl⟩ : syracuseStep 232919 = 349379) B349379
theorem B331229 : Blo 99781 331229 := bstep (se 3 (by rfl) ⟨62105, by rfl⟩ : syracuseStep 331229 = 124211) B124211
theorem B101867 : Blo 99781 101867 := bstep (se 1 (by rfl) ⟨76400, by rfl⟩ : syracuseStep 101867 = 152801) B152801
theorem B101879 : Blo 99781 101879 := bstep (se 1 (by rfl) ⟨76409, by rfl⟩ : syracuseStep 101879 = 152819) B152819
theorem B101899 : Blo 99781 101899 := bstep (se 1 (by rfl) ⟨76424, by rfl⟩ : syracuseStep 101899 = 152849) B152849
theorem B101911 : Blo 99781 101911 := bstep (se 1 (by rfl) ⟨76433, by rfl⟩ : syracuseStep 101911 = 152867) B152867
theorem B101931 : Blo 99781 101931 := bstep (se 1 (by rfl) ⟨76448, by rfl⟩ : syracuseStep 101931 = 152897) B152897
theorem B101943 : Blo 99781 101943 := bstep (se 1 (by rfl) ⟨76457, by rfl⟩ : syracuseStep 101943 = 152915) B152915
theorem B101963 : Blo 99781 101963 := bstep (se 1 (by rfl) ⟨76472, by rfl⟩ : syracuseStep 101963 = 152945) B152945
theorem B101975 : Blo 99781 101975 := bstep (se 1 (by rfl) ⟨76481, by rfl⟩ : syracuseStep 101975 = 152963) B152963
theorem B101995 : Blo 99781 101995 := bstep (se 1 (by rfl) ⟨76496, by rfl⟩ : syracuseStep 101995 = 152993) B152993
theorem B102007 : Blo 99781 102007 := bstep (se 1 (by rfl) ⟨76505, by rfl⟩ : syracuseStep 102007 = 153011) B153011
theorem B102027 : Blo 99781 102027 := bstep (se 1 (by rfl) ⟨76520, by rfl⟩ : syracuseStep 102027 = 153041) B153041
theorem B233099 : Blo 99781 233099 := bstep (se 1 (by rfl) ⟨174824, by rfl⟩ : syracuseStep 233099 = 349649) B349649
theorem B102039 : Blo 99781 102039 := bstep (se 1 (by rfl) ⟨76529, by rfl⟩ : syracuseStep 102039 = 153059) B153059
theorem B102059 : Blo 99781 102059 := bstep (se 1 (by rfl) ⟨76544, by rfl⟩ : syracuseStep 102059 = 153089) B153089
theorem B102071 : Blo 99781 102071 := bstep (se 1 (by rfl) ⟨76553, by rfl⟩ : syracuseStep 102071 = 153107) B153107
theorem B233153 : Blo 99781 233153 := bstep (se 2 (by rfl) ⟨87432, by rfl⟩ : syracuseStep 233153 = 174865) B174865
theorem B102091 : Blo 99781 102091 := bstep (se 1 (by rfl) ⟨76568, by rfl⟩ : syracuseStep 102091 = 153137) B153137
theorem B102103 : Blo 99781 102103 := bstep (se 1 (by rfl) ⟨76577, by rfl⟩ : syracuseStep 102103 = 153155) B153155
theorem B102123 : Blo 99781 102123 := bstep (se 1 (by rfl) ⟨76592, by rfl⟩ : syracuseStep 102123 = 153185) B153185
theorem B102135 : Blo 99781 102135 := bstep (se 1 (by rfl) ⟨76601, by rfl⟩ : syracuseStep 102135 = 153203) B153203
theorem B102155 : Blo 99781 102155 := bstep (se 1 (by rfl) ⟨76616, by rfl⟩ : syracuseStep 102155 = 153233) B153233
theorem B102167 : Blo 99781 102167 := bstep (se 1 (by rfl) ⟨76625, by rfl⟩ : syracuseStep 102167 = 153251) B153251
theorem B102187 : Blo 99781 102187 := bstep (se 1 (by rfl) ⟨76640, by rfl⟩ : syracuseStep 102187 = 153281) B153281
theorem B102199 : Blo 99781 102199 := bstep (se 1 (by rfl) ⟨76649, by rfl⟩ : syracuseStep 102199 = 153299) B153299
theorem B102219 : Blo 99781 102219 := bstep (se 1 (by rfl) ⟨76664, by rfl⟩ : syracuseStep 102219 = 153329) B153329
theorem B102231 : Blo 99781 102231 := bstep (se 1 (by rfl) ⟨76673, by rfl⟩ : syracuseStep 102231 = 153347) B153347
theorem B102251 : Blo 99781 102251 := bstep (se 1 (by rfl) ⟨76688, by rfl⟩ : syracuseStep 102251 = 153377) B153377
theorem B1118069 : Blo 99781 1118069 := bstep (se 5 (by rfl) ⟨52409, by rfl⟩ : syracuseStep 1118069 = 104819) B104819
theorem B102263 : Blo 99781 102263 := bstep (se 1 (by rfl) ⟨76697, by rfl⟩ : syracuseStep 102263 = 153395) B153395
theorem B102283 : Blo 99781 102283 := bstep (se 1 (by rfl) ⟨76712, by rfl⟩ : syracuseStep 102283 = 153425) B153425
theorem B102295 : Blo 99781 102295 := bstep (se 1 (by rfl) ⟨76721, by rfl⟩ : syracuseStep 102295 = 153443) B153443
theorem B233369 : Blo 99781 233369 := bstep (se 2 (by rfl) ⟨87513, by rfl⟩ : syracuseStep 233369 = 175027) B175027
theorem B102315 : Blo 99781 102315 := bstep (se 1 (by rfl) ⟨76736, by rfl⟩ : syracuseStep 102315 = 153473) B153473
theorem B102327 : Blo 99781 102327 := bstep (se 1 (by rfl) ⟨76745, by rfl⟩ : syracuseStep 102327 = 153491) B153491
theorem B102347 : Blo 99781 102347 := bstep (se 1 (by rfl) ⟨76760, by rfl⟩ : syracuseStep 102347 = 153521) B153521
theorem B102359 : Blo 99781 102359 := bstep (se 1 (by rfl) ⟨76769, by rfl⟩ : syracuseStep 102359 = 153539) B153539
theorem B102379 : Blo 99781 102379 := bstep (se 1 (by rfl) ⟨76784, by rfl⟩ : syracuseStep 102379 = 153569) B153569
theorem B233459 : Blo 99781 233459 := bstep (se 1 (by rfl) ⟨175094, by rfl⟩ : syracuseStep 233459 = 350189) B350189
theorem B102391 : Blo 99781 102391 := bstep (se 1 (by rfl) ⟨76793, by rfl⟩ : syracuseStep 102391 = 153587) B153587
theorem B102411 : Blo 99781 102411 := bstep (se 1 (by rfl) ⟨76808, by rfl⟩ : syracuseStep 102411 = 153617) B153617
theorem B102423 : Blo 99781 102423 := bstep (se 1 (by rfl) ⟨76817, by rfl⟩ : syracuseStep 102423 = 153635) B153635
theorem B233495 : Blo 99781 233495 := bstep (se 1 (by rfl) ⟨175121, by rfl⟩ : syracuseStep 233495 = 350243) B350243
theorem B102443 : Blo 99781 102443 := bstep (se 1 (by rfl) ⟨76832, by rfl⟩ : syracuseStep 102443 = 153665) B153665
theorem B102455 : Blo 99781 102455 := bstep (se 1 (by rfl) ⟨76841, by rfl⟩ : syracuseStep 102455 = 153683) B153683
theorem B102475 : Blo 99781 102475 := bstep (se 1 (by rfl) ⟨76856, by rfl⟩ : syracuseStep 102475 = 153713) B153713
theorem B102487 : Blo 99781 102487 := bstep (se 1 (by rfl) ⟨76865, by rfl⟩ : syracuseStep 102487 = 153731) B153731
theorem B462941 : Blo 99781 462941 := bstep (se 3 (by rfl) ⟨86801, by rfl⟩ : syracuseStep 462941 = 173603) B173603
theorem B102507 : Blo 99781 102507 := bstep (se 1 (by rfl) ⟨76880, by rfl⟩ : syracuseStep 102507 = 153761) B153761
theorem B102519 : Blo 99781 102519 := bstep (se 1 (by rfl) ⟨76889, by rfl⟩ : syracuseStep 102519 = 153779) B153779
theorem B364675 : Blo 99781 364675 := bstep (se 1 (by rfl) ⟨273506, by rfl⟩ : syracuseStep 364675 = 547013) B547013
theorem B102539 : Blo 99781 102539 := bstep (se 1 (by rfl) ⟨76904, by rfl⟩ : syracuseStep 102539 = 153809) B153809
theorem B102551 : Blo 99781 102551 := bstep (se 1 (by rfl) ⟨76913, by rfl⟩ : syracuseStep 102551 = 153827) B153827
theorem B102571 : Blo 99781 102571 := bstep (se 1 (by rfl) ⟨76928, by rfl⟩ : syracuseStep 102571 = 153857) B153857
theorem B102583 : Blo 99781 102583 := bstep (se 1 (by rfl) ⟨76937, by rfl⟩ : syracuseStep 102583 = 153875) B153875
theorem B102603 : Blo 99781 102603 := bstep (se 1 (by rfl) ⟨76952, by rfl⟩ : syracuseStep 102603 = 153905) B153905
theorem B102615 : Blo 99781 102615 := bstep (se 1 (by rfl) ⟨76961, by rfl⟩ : syracuseStep 102615 = 153923) B153923
theorem B102635 : Blo 99781 102635 := bstep (se 1 (by rfl) ⟨76976, by rfl⟩ : syracuseStep 102635 = 153953) B153953
theorem B102647 : Blo 99781 102647 := bstep (se 1 (by rfl) ⟨76985, by rfl⟩ : syracuseStep 102647 = 153971) B153971
theorem B102667 : Blo 99781 102667 := bstep (se 1 (by rfl) ⟨77000, by rfl⟩ : syracuseStep 102667 = 154001) B154001
theorem B102679 : Blo 99781 102679 := bstep (se 1 (by rfl) ⟨77009, by rfl⟩ : syracuseStep 102679 = 154019) B154019
theorem B102699 : Blo 99781 102699 := bstep (se 1 (by rfl) ⟨77024, by rfl⟩ : syracuseStep 102699 = 154049) B154049
theorem B102711 : Blo 99781 102711 := bstep (se 1 (by rfl) ⟨77033, by rfl⟩ : syracuseStep 102711 = 154067) B154067
theorem B102731 : Blo 99781 102731 := bstep (se 1 (by rfl) ⟨77048, by rfl⟩ : syracuseStep 102731 = 154097) B154097
theorem B102743 : Blo 99781 102743 := bstep (se 1 (by rfl) ⟨77057, by rfl⟩ : syracuseStep 102743 = 154115) B154115
theorem B430429 : Blo 99781 430429 := bstep (se 3 (by rfl) ⟨80705, by rfl⟩ : syracuseStep 430429 = 161411) B161411
theorem B102763 : Blo 99781 102763 := bstep (se 1 (by rfl) ⟨77072, by rfl⟩ : syracuseStep 102763 = 154145) B154145
theorem B102775 : Blo 99781 102775 := bstep (se 1 (by rfl) ⟨77081, by rfl⟩ : syracuseStep 102775 = 154163) B154163
theorem B102795 : Blo 99781 102795 := bstep (se 1 (by rfl) ⟨77096, by rfl⟩ : syracuseStep 102795 = 154193) B154193
theorem B102807 : Blo 99781 102807 := bstep (se 1 (by rfl) ⟨77105, by rfl⟩ : syracuseStep 102807 = 154211) B154211
theorem B102827 : Blo 99781 102827 := bstep (se 1 (by rfl) ⟨77120, by rfl⟩ : syracuseStep 102827 = 154241) B154241
theorem B102839 : Blo 99781 102839 := bstep (se 1 (by rfl) ⟨77129, by rfl⟩ : syracuseStep 102839 = 154259) B154259
theorem B102859 : Blo 99781 102859 := bstep (se 1 (by rfl) ⟨77144, by rfl⟩ : syracuseStep 102859 = 154289) B154289
theorem B102871 : Blo 99781 102871 := bstep (se 1 (by rfl) ⟨77153, by rfl⟩ : syracuseStep 102871 = 154307) B154307
theorem B823769 : Blo 99781 823769 := bstep (se 2 (by rfl) ⟨308913, by rfl⟩ : syracuseStep 823769 = 617827) B617827
theorem B102891 : Blo 99781 102891 := bstep (se 1 (by rfl) ⟨77168, by rfl⟩ : syracuseStep 102891 = 154337) B154337
theorem B102903 : Blo 99781 102903 := bstep (se 1 (by rfl) ⟨77177, by rfl⟩ : syracuseStep 102903 = 154355) B154355
theorem B102923 : Blo 99781 102923 := bstep (se 1 (by rfl) ⟨77192, by rfl⟩ : syracuseStep 102923 = 154385) B154385
theorem B102935 : Blo 99781 102935 := bstep (se 1 (by rfl) ⟨77201, by rfl⟩ : syracuseStep 102935 = 154403) B154403
theorem B168473 : Blo 99781 168473 := bstep (se 2 (by rfl) ⟨63177, by rfl⟩ : syracuseStep 168473 = 126355) B126355
theorem B102955 : Blo 99781 102955 := bstep (se 1 (by rfl) ⟨77216, by rfl⟩ : syracuseStep 102955 = 154433) B154433
theorem B102967 : Blo 99781 102967 := bstep (se 1 (by rfl) ⟨77225, by rfl⟩ : syracuseStep 102967 = 154451) B154451
theorem B102987 : Blo 99781 102987 := bstep (se 1 (by rfl) ⟨77240, by rfl⟩ : syracuseStep 102987 = 154481) B154481
theorem B102999 : Blo 99781 102999 := bstep (se 1 (by rfl) ⟨77249, by rfl⟩ : syracuseStep 102999 = 154499) B154499
theorem B103019 : Blo 99781 103019 := bstep (se 1 (by rfl) ⟨77264, by rfl⟩ : syracuseStep 103019 = 154529) B154529
theorem B103031 : Blo 99781 103031 := bstep (se 1 (by rfl) ⟨77273, by rfl⟩ : syracuseStep 103031 = 154547) B154547
theorem B103051 : Blo 99781 103051 := bstep (se 1 (by rfl) ⟨77288, by rfl⟩ : syracuseStep 103051 = 154577) B154577
theorem B103063 : Blo 99781 103063 := bstep (se 1 (by rfl) ⟨77297, by rfl⟩ : syracuseStep 103063 = 154595) B154595
theorem B168601 : Blo 99781 168601 := bstep (se 2 (by rfl) ⟨63225, by rfl⟩ : syracuseStep 168601 = 126451) B126451
theorem B103083 : Blo 99781 103083 := bstep (se 1 (by rfl) ⟨77312, by rfl⟩ : syracuseStep 103083 = 154625) B154625
theorem B430771 : Blo 99781 430771 := bstep (se 1 (by rfl) ⟨323078, by rfl⟩ : syracuseStep 430771 = 646157) B646157
theorem B103095 : Blo 99781 103095 := bstep (se 1 (by rfl) ⟨77321, by rfl⟩ : syracuseStep 103095 = 154643) B154643
theorem B103115 : Blo 99781 103115 := bstep (se 1 (by rfl) ⟨77336, by rfl⟩ : syracuseStep 103115 = 154673) B154673
theorem B103127 : Blo 99781 103127 := bstep (se 1 (by rfl) ⟨77345, by rfl⟩ : syracuseStep 103127 = 154691) B154691
theorem B103147 : Blo 99781 103147 := bstep (se 1 (by rfl) ⟨77360, by rfl⟩ : syracuseStep 103147 = 154721) B154721
theorem B103159 : Blo 99781 103159 := bstep (se 1 (by rfl) ⟨77369, by rfl⟩ : syracuseStep 103159 = 154739) B154739
theorem B103179 : Blo 99781 103179 := bstep (se 1 (by rfl) ⟨77384, by rfl⟩ : syracuseStep 103179 = 154769) B154769
theorem B103191 : Blo 99781 103191 := bstep (se 1 (by rfl) ⟨77393, by rfl⟩ : syracuseStep 103191 = 154787) B154787
theorem B103211 : Blo 99781 103211 := bstep (se 1 (by rfl) ⟨77408, by rfl⟩ : syracuseStep 103211 = 154817) B154817
theorem B103223 : Blo 99781 103223 := bstep (se 1 (by rfl) ⟨77417, by rfl⟩ : syracuseStep 103223 = 154835) B154835
theorem B103243 : Blo 99781 103243 := bstep (se 1 (by rfl) ⟨77432, by rfl⟩ : syracuseStep 103243 = 154865) B154865
theorem B103255 : Blo 99781 103255 := bstep (se 1 (by rfl) ⟨77441, by rfl⟩ : syracuseStep 103255 = 154883) B154883
theorem B103275 : Blo 99781 103275 := bstep (se 1 (by rfl) ⟨77456, by rfl⟩ : syracuseStep 103275 = 154913) B154913
theorem B103287 : Blo 99781 103287 := bstep (se 1 (by rfl) ⟨77465, by rfl⟩ : syracuseStep 103287 = 154931) B154931
theorem B103307 : Blo 99781 103307 := bstep (se 1 (by rfl) ⟨77480, by rfl⟩ : syracuseStep 103307 = 154961) B154961
theorem B103319 : Blo 99781 103319 := bstep (se 1 (by rfl) ⟨77489, by rfl⟩ : syracuseStep 103319 = 154979) B154979
theorem B103339 : Blo 99781 103339 := bstep (se 1 (by rfl) ⟨77504, by rfl⟩ : syracuseStep 103339 = 155009) B155009
theorem B103351 : Blo 99781 103351 := bstep (se 1 (by rfl) ⟨77513, by rfl⟩ : syracuseStep 103351 = 155027) B155027
theorem B103371 : Blo 99781 103371 := bstep (se 1 (by rfl) ⟨77528, by rfl⟩ : syracuseStep 103371 = 155057) B155057
theorem B103383 : Blo 99781 103383 := bstep (se 1 (by rfl) ⟨77537, by rfl⟩ : syracuseStep 103383 = 155075) B155075
theorem B332765 : Blo 99781 332765 := bstep (se 3 (by rfl) ⟨62393, by rfl⟩ : syracuseStep 332765 = 124787) B124787
theorem B103403 : Blo 99781 103403 := bstep (se 1 (by rfl) ⟨77552, by rfl⟩ : syracuseStep 103403 = 155105) B155105
theorem B103415 : Blo 99781 103415 := bstep (se 1 (by rfl) ⟨77561, by rfl⟩ : syracuseStep 103415 = 155123) B155123
theorem B103435 : Blo 99781 103435 := bstep (se 1 (by rfl) ⟨77576, by rfl⟩ : syracuseStep 103435 = 155153) B155153
theorem B103447 : Blo 99781 103447 := bstep (se 1 (by rfl) ⟨77585, by rfl⟩ : syracuseStep 103447 = 155171) B155171
theorem B103467 : Blo 99781 103467 := bstep (se 1 (by rfl) ⟨77600, by rfl⟩ : syracuseStep 103467 = 155201) B155201
theorem B103479 : Blo 99781 103479 := bstep (se 1 (by rfl) ⟨77609, by rfl⟩ : syracuseStep 103479 = 155219) B155219
theorem B103499 : Blo 99781 103499 := bstep (se 1 (by rfl) ⟨77624, by rfl⟩ : syracuseStep 103499 = 155249) B155249
theorem B103511 : Blo 99781 103511 := bstep (se 1 (by rfl) ⟨77633, by rfl⟩ : syracuseStep 103511 = 155267) B155267
theorem B103531 : Blo 99781 103531 := bstep (se 1 (by rfl) ⟨77648, by rfl⟩ : syracuseStep 103531 = 155297) B155297
theorem B103543 : Blo 99781 103543 := bstep (se 1 (by rfl) ⟨77657, by rfl⟩ : syracuseStep 103543 = 155315) B155315
theorem B660611 : Blo 99781 660611 := bstep (se 1 (by rfl) ⟨495458, by rfl⟩ : syracuseStep 660611 = 990917) B990917
theorem B103563 : Blo 99781 103563 := bstep (se 1 (by rfl) ⟨77672, by rfl⟩ : syracuseStep 103563 = 155345) B155345
theorem B103575 : Blo 99781 103575 := bstep (se 1 (by rfl) ⟨77681, by rfl⟩ : syracuseStep 103575 = 155363) B155363
theorem B103595 : Blo 99781 103595 := bstep (se 1 (by rfl) ⟨77696, by rfl⟩ : syracuseStep 103595 = 155393) B155393
theorem B103607 : Blo 99781 103607 := bstep (se 1 (by rfl) ⟨77705, by rfl⟩ : syracuseStep 103607 = 155411) B155411
theorem B365771 : Blo 99781 365771 := bstep (se 1 (by rfl) ⟨274328, by rfl⟩ : syracuseStep 365771 = 548657) B548657
theorem B103627 : Blo 99781 103627 := bstep (se 1 (by rfl) ⟨77720, by rfl⟩ : syracuseStep 103627 = 155441) B155441
theorem B169175 : Blo 99781 169175 := bstep (se 1 (by rfl) ⟨126881, by rfl⟩ : syracuseStep 169175 = 253763) B253763
theorem B103639 : Blo 99781 103639 := bstep (se 1 (by rfl) ⟨77729, by rfl⟩ : syracuseStep 103639 = 155459) B155459
theorem B103659 : Blo 99781 103659 := bstep (se 1 (by rfl) ⟨77744, by rfl⟩ : syracuseStep 103659 = 155489) B155489
theorem B103671 : Blo 99781 103671 := bstep (se 1 (by rfl) ⟨77753, by rfl⟩ : syracuseStep 103671 = 155507) B155507
theorem B103691 : Blo 99781 103691 := bstep (se 1 (by rfl) ⟨77768, by rfl⟩ : syracuseStep 103691 = 155537) B155537
theorem B103703 : Blo 99781 103703 := bstep (se 1 (by rfl) ⟨77777, by rfl⟩ : syracuseStep 103703 = 155555) B155555
theorem B103723 : Blo 99781 103723 := bstep (se 1 (by rfl) ⟨77792, by rfl⟩ : syracuseStep 103723 = 155585) B155585
theorem B103735 : Blo 99781 103735 := bstep (se 1 (by rfl) ⟨77801, by rfl⟩ : syracuseStep 103735 = 155603) B155603
theorem B103755 : Blo 99781 103755 := bstep (se 1 (by rfl) ⟨77816, by rfl⟩ : syracuseStep 103755 = 155633) B155633
theorem B169303 : Blo 99781 169303 := bstep (se 1 (by rfl) ⟨126977, by rfl⟩ : syracuseStep 169303 = 253955) B253955
theorem B103767 : Blo 99781 103767 := bstep (se 1 (by rfl) ⟨77825, by rfl⟩ : syracuseStep 103767 = 155651) B155651
theorem B791909 : Blo 99781 791909 := bstep (se 4 (by rfl) ⟨74241, by rfl⟩ : syracuseStep 791909 = 148483) B148483
theorem B1054529 : Blo 99781 1054529 := bstep (se 2 (by rfl) ⟨395448, by rfl⟩ : syracuseStep 1054529 = 790897) B790897
theorem B759617 : Blo 99781 759617 := bstep (se 2 (by rfl) ⟨284856, by rfl⟩ : syracuseStep 759617 = 569713) B569713
theorem B169931 : Blo 99781 169931 := bstep (se 1 (by rfl) ⟨127448, by rfl⟩ : syracuseStep 169931 = 254897) B254897
theorem B170059 : Blo 99781 170059 := bstep (se 1 (by rfl) ⟨127544, by rfl⟩ : syracuseStep 170059 = 255089) B255089
theorem B170201 : Blo 99781 170201 := bstep (se 2 (by rfl) ⟨63825, by rfl⟩ : syracuseStep 170201 = 127651) B127651
theorem B170329 : Blo 99781 170329 := bstep (se 2 (by rfl) ⟨63873, by rfl⟩ : syracuseStep 170329 = 127747) B127747
theorem B235991 : Blo 99781 235991 := bstep (se 1 (by rfl) ⟨176993, by rfl⟩ : syracuseStep 235991 = 353987) B353987
theorem B2988899 : Blo 99781 2988899 := bstep (se 1 (by rfl) ⟨2241674, by rfl⟩ : syracuseStep 2988899 = 4483349) B4483349
theorem B170903 : Blo 99781 170903 := bstep (se 1 (by rfl) ⟨128177, by rfl⟩ : syracuseStep 170903 = 256355) B256355
theorem B498649 : Blo 99781 498649 := bstep (se 2 (by rfl) ⟨186993, by rfl⟩ : syracuseStep 498649 = 373987) B373987
theorem B1252313 : Blo 99781 1252313 := bstep (se 2 (by rfl) ⟨469617, by rfl⟩ : syracuseStep 1252313 = 939235) B939235
theorem B171031 : Blo 99781 171031 := bstep (se 1 (by rfl) ⟨128273, by rfl⟩ : syracuseStep 171031 = 256547) B256547
theorem B990301 : Blo 99781 990301 := bstep (se 3 (by rfl) ⟨185681, by rfl⟩ : syracuseStep 990301 = 371363) B371363
theorem B171659 : Blo 99781 171659 := bstep (se 1 (by rfl) ⟨128744, by rfl⟩ : syracuseStep 171659 = 257489) B257489
theorem B761561 : Blo 99781 761561 := bstep (se 2 (by rfl) ⟨285585, by rfl⟩ : syracuseStep 761561 = 571171) B571171
theorem B171787 : Blo 99781 171787 := bstep (se 1 (by rfl) ⟨128840, by rfl⟩ : syracuseStep 171787 = 257681) B257681
theorem B433943 : Blo 99781 433943 := bstep (se 1 (by rfl) ⟨325457, by rfl⟩ : syracuseStep 433943 = 650915) B650915
theorem B270155 : Blo 99781 270155 := bstep (se 1 (by rfl) ⟨202616, by rfl⟩ : syracuseStep 270155 = 405233) B405233
theorem B171929 : Blo 99781 171929 := bstep (se 2 (by rfl) ⟨64473, by rfl⟩ : syracuseStep 171929 = 128947) B128947
theorem B172057 : Blo 99781 172057 := bstep (se 2 (by rfl) ⟨64521, by rfl⟩ : syracuseStep 172057 = 129043) B129043
theorem B1646743 : Blo 99781 1646743 := bstep (se 1 (by rfl) ⟨1235057, by rfl⟩ : syracuseStep 1646743 = 2470115) B2470115
theorem B434393 : Blo 99781 434393 := bstep (se 2 (by rfl) ⟨162897, by rfl⟩ : syracuseStep 434393 = 325795) B325795
theorem B205057 : Blo 99781 205057 := bstep (se 2 (by rfl) ⟨76896, by rfl⟩ : syracuseStep 205057 = 153793) B153793
theorem B598373 : Blo 99781 598373 := bstep (se 4 (by rfl) ⟨56097, by rfl⟩ : syracuseStep 598373 = 112195) B112195
theorem B205259 : Blo 99781 205259 := bstep (se 1 (by rfl) ⟨153944, by rfl⟩ : syracuseStep 205259 = 307889) B307889
theorem B106967 : Blo 99781 106967 := bstep (se 1 (by rfl) ⟨80225, by rfl⟩ : syracuseStep 106967 = 160451) B160451
theorem B172631 : Blo 99781 172631 := bstep (se 1 (by rfl) ⟨129473, by rfl⟩ : syracuseStep 172631 = 258947) B258947
theorem B172759 : Blo 99781 172759 := bstep (se 1 (by rfl) ⟨129569, by rfl⟩ : syracuseStep 172759 = 259139) B259139
theorem B107659 : Blo 99781 107659 := bstep (se 1 (by rfl) ⟨80744, by rfl⟩ : syracuseStep 107659 = 161489) B161489
theorem B369809 : Blo 99781 369809 := bstep (se 2 (by rfl) ⟨138678, by rfl⟩ : syracuseStep 369809 = 277357) B277357
theorem B337175 : Blo 99781 337175 := bstep (se 1 (by rfl) ⟨252881, by rfl⟩ : syracuseStep 337175 = 505763) B505763
theorem B173387 : Blo 99781 173387 := bstep (se 1 (by rfl) ⟨130040, by rfl⟩ : syracuseStep 173387 = 260081) B260081
theorem B173515 : Blo 99781 173515 := bstep (se 1 (by rfl) ⟨130136, by rfl⟩ : syracuseStep 173515 = 260273) B260273
theorem B4793813 : Blo 99781 4793813 := bstep (se 7 (by rfl) ⟨56177, by rfl⟩ : syracuseStep 4793813 = 112355) B112355
theorem B370241 : Blo 99781 370241 := bstep (se 2 (by rfl) ⟨138840, by rfl⟩ : syracuseStep 370241 = 277681) B277681
theorem B173657 : Blo 99781 173657 := bstep (se 2 (by rfl) ⟨65121, by rfl⟩ : syracuseStep 173657 = 130243) B130243
theorem B501427 : Blo 99781 501427 := bstep (se 1 (by rfl) ⟨376070, by rfl⟩ : syracuseStep 501427 = 752141) B752141
theorem B173785 : Blo 99781 173785 := bstep (se 2 (by rfl) ⟨65169, by rfl⟩ : syracuseStep 173785 = 130339) B130339
theorem B337715 : Blo 99781 337715 := bstep (se 1 (by rfl) ⟨253286, by rfl⟩ : syracuseStep 337715 = 506573) B506573
theorem B436033 : Blo 99781 436033 := bstep (se 2 (by rfl) ⟨163512, by rfl⟩ : syracuseStep 436033 = 327025) B327025
theorem B337985 : Blo 99781 337985 := bstep (se 2 (by rfl) ⟨126744, by rfl⟩ : syracuseStep 337985 = 253489) B253489
theorem B174359 : Blo 99781 174359 := bstep (se 1 (by rfl) ⟨130769, by rfl⟩ : syracuseStep 174359 = 261539) B261539
theorem B1485155 : Blo 99781 1485155 := bstep (se 1 (by rfl) ⟨1113866, by rfl⟩ : syracuseStep 1485155 = 2227733) B2227733
theorem B174487 : Blo 99781 174487 := bstep (se 1 (by rfl) ⟨130865, by rfl⟩ : syracuseStep 174487 = 261731) B261731
theorem B108983 : Blo 99781 108983 := bstep (se 1 (by rfl) ⟨81737, by rfl⟩ : syracuseStep 108983 = 163475) B163475
theorem B109111 : Blo 99781 109111 := bstep (se 1 (by rfl) ⟨81833, by rfl⟩ : syracuseStep 109111 = 163667) B163667
theorem B338525 : Blo 99781 338525 := bstep (se 3 (by rfl) ⟨63473, by rfl⟩ : syracuseStep 338525 = 126947) B126947
theorem B371479 : Blo 99781 371479 := bstep (se 1 (by rfl) ⟨278609, by rfl⟩ : syracuseStep 371479 = 557219) B557219
theorem B994265 : Blo 99781 994265 := bstep (se 2 (by rfl) ⟨372849, by rfl⟩ : syracuseStep 994265 = 745699) B745699
theorem B175115 : Blo 99781 175115 := bstep (se 1 (by rfl) ⟨131336, by rfl⟩ : syracuseStep 175115 = 262673) B262673
theorem B764963 : Blo 99781 764963 := bstep (se 1 (by rfl) ⟨573722, by rfl⟩ : syracuseStep 764963 = 1147445) B1147445
theorem B109675 : Blo 99781 109675 := bstep (se 1 (by rfl) ⟨82256, by rfl⟩ : syracuseStep 109675 = 164513) B164513
theorem B470195 : Blo 99781 470195 := bstep (se 1 (by rfl) ⟨352646, by rfl⟩ : syracuseStep 470195 = 705293) B705293
theorem B1682693 : Blo 99781 1682693 := bstep (se 4 (by rfl) ⟨157752, by rfl⟩ : syracuseStep 1682693 = 315505) B315505
theorem B437521 : Blo 99781 437521 := bstep (se 2 (by rfl) ⟨164070, by rfl⟩ : syracuseStep 437521 = 328141) B328141
theorem B109847 : Blo 99781 109847 := bstep (se 1 (by rfl) ⟨82385, by rfl⟩ : syracuseStep 109847 = 164771) B164771
theorem B142679 : Blo 99781 142679 := bstep (se 1 (by rfl) ⟨107009, by rfl⟩ : syracuseStep 142679 = 214019) B214019
theorem B109931 : Blo 99781 109931 := bstep (se 1 (by rfl) ⟨82448, by rfl⟩ : syracuseStep 109931 = 164897) B164897
theorem B142987 : Blo 99781 142987 := bstep (se 1 (by rfl) ⟨107240, by rfl⟩ : syracuseStep 142987 = 214481) B214481
theorem B110219 : Blo 99781 110219 := bstep (se 1 (by rfl) ⟨82664, by rfl⟩ : syracuseStep 110219 = 165329) B165329
theorem B339659 : Blo 99781 339659 := bstep (se 1 (by rfl) ⟨254744, by rfl⟩ : syracuseStep 339659 = 509489) B509489
theorem B339929 : Blo 99781 339929 := bstep (se 2 (by rfl) ⟨127473, by rfl⟩ : syracuseStep 339929 = 254947) B254947
theorem B373081 : Blo 99781 373081 := bstep (se 2 (by rfl) ⟨139905, by rfl⟩ : syracuseStep 373081 = 279811) B279811
theorem B373123 : Blo 99781 373123 := bstep (se 1 (by rfl) ⟨279842, by rfl⟩ : syracuseStep 373123 = 559685) B559685
theorem B569987 : Blo 99781 569987 := bstep (se 1 (by rfl) ⟨427490, by rfl⟩ : syracuseStep 569987 = 854981) B854981
theorem B340631 : Blo 99781 340631 := bstep (se 1 (by rfl) ⟨255473, by rfl⟩ : syracuseStep 340631 = 510947) B510947
theorem B144023 : Blo 99781 144023 := bstep (se 1 (by rfl) ⟨108017, by rfl⟩ : syracuseStep 144023 = 216035) B216035
theorem B996101 : Blo 99781 996101 := bstep (se 4 (by rfl) ⟨93384, by rfl⟩ : syracuseStep 996101 = 186769) B186769
theorem B144217 : Blo 99781 144217 := bstep (se 2 (by rfl) ⟨54081, by rfl⟩ : syracuseStep 144217 = 108163) B108163
theorem B2831435 : Blo 99781 2831435 := bstep (se 1 (by rfl) ⟨2123576, by rfl⟩ : syracuseStep 2831435 = 4247153) B4247153
theorem B734309 : Blo 99781 734309 := bstep (se 4 (by rfl) ⟨68841, by rfl⟩ : syracuseStep 734309 = 137683) B137683
theorem B341171 : Blo 99781 341171 := bstep (se 1 (by rfl) ⟨255878, by rfl⟩ : syracuseStep 341171 = 511757) B511757
theorem B406873 : Blo 99781 406873 := bstep (se 2 (by rfl) ⟨152577, by rfl⟩ : syracuseStep 406873 = 305155) B305155
theorem B1291697 : Blo 99781 1291697 := bstep (se 2 (by rfl) ⟨484386, by rfl⟩ : syracuseStep 1291697 = 968773) B968773
theorem B341441 : Blo 99781 341441 := bstep (se 2 (by rfl) ⟨128040, by rfl⟩ : syracuseStep 341441 = 256081) B256081
theorem B243137 : Blo 99781 243137 := bstep (se 2 (by rfl) ⟨91176, by rfl⟩ : syracuseStep 243137 = 182353) B182353
theorem B439769 : Blo 99781 439769 := bstep (se 2 (by rfl) ⟨164913, by rfl⟩ : syracuseStep 439769 = 329827) B329827
theorem B144985 : Blo 99781 144985 := bstep (se 2 (by rfl) ⟨54369, by rfl⟩ : syracuseStep 144985 = 108739) B108739
theorem B112279 : Blo 99781 112279 := bstep (se 1 (by rfl) ⟨84209, by rfl⟩ : syracuseStep 112279 = 168419) B168419
theorem B407261 : Blo 99781 407261 := bstep (se 3 (by rfl) ⟨76361, by rfl⟩ : syracuseStep 407261 = 152723) B152723
theorem B112459 : Blo 99781 112459 := bstep (se 1 (by rfl) ⟨84344, by rfl⟩ : syracuseStep 112459 = 168689) B168689
theorem B309143 : Blo 99781 309143 := bstep (se 1 (by rfl) ⟨231857, by rfl⟩ : syracuseStep 309143 = 463715) B463715
theorem B112567 : Blo 99781 112567 := bstep (se 1 (by rfl) ⟨84425, by rfl⟩ : syracuseStep 112567 = 168851) B168851
theorem B341981 : Blo 99781 341981 := bstep (se 3 (by rfl) ⟨64121, by rfl⟩ : syracuseStep 341981 = 128243) B128243
theorem B112747 : Blo 99781 112747 := bstep (se 1 (by rfl) ⟨84560, by rfl⟩ : syracuseStep 112747 = 169121) B169121
theorem B112855 : Blo 99781 112855 := bstep (se 1 (by rfl) ⟨84641, by rfl⟩ : syracuseStep 112855 = 169283) B169283
theorem B833753 : Blo 99781 833753 := bstep (se 2 (by rfl) ⟨312657, by rfl⟩ : syracuseStep 833753 = 625315) B625315
theorem B440579 : Blo 99781 440579 := bstep (se 1 (by rfl) ⟨330434, by rfl⟩ : syracuseStep 440579 = 660869) B660869
theorem B145675 : Blo 99781 145675 := bstep (se 1 (by rfl) ⟨109256, by rfl⟩ : syracuseStep 145675 = 218513) B218513
theorem B113035 : Blo 99781 113035 := bstep (se 1 (by rfl) ⟨84776, by rfl⟩ : syracuseStep 113035 = 169553) B169553
theorem B1325489 : Blo 99781 1325489 := bstep (se 2 (by rfl) ⟨497058, by rfl⟩ : syracuseStep 1325489 = 994117) B994117
theorem B113143 : Blo 99781 113143 := bstep (se 1 (by rfl) ⟨84857, by rfl⟩ : syracuseStep 113143 = 169715) B169715
theorem B211481 : Blo 99781 211481 := bstep (se 2 (by rfl) ⟨79305, by rfl⟩ : syracuseStep 211481 = 158611) B158611
theorem B309835 : Blo 99781 309835 := bstep (se 1 (by rfl) ⟨232376, by rfl⟩ : syracuseStep 309835 = 464753) B464753
theorem B113323 : Blo 99781 113323 := bstep (se 1 (by rfl) ⟨84992, by rfl⟩ : syracuseStep 113323 = 169985) B169985
theorem B113431 : Blo 99781 113431 := bstep (se 1 (by rfl) ⟨85073, by rfl⟩ : syracuseStep 113431 = 170147) B170147
theorem B113611 : Blo 99781 113611 := bstep (se 1 (by rfl) ⟨85208, by rfl⟩ : syracuseStep 113611 = 170417) B170417
theorem B506897 : Blo 99781 506897 := bstep (se 2 (by rfl) ⟨190086, by rfl⟩ : syracuseStep 506897 = 380173) B380173
theorem B113719 : Blo 99781 113719 := bstep (se 1 (by rfl) ⟨85289, by rfl⟩ : syracuseStep 113719 = 170579) B170579
theorem B343115 : Blo 99781 343115 := bstep (se 1 (by rfl) ⟨257336, by rfl⟩ : syracuseStep 343115 = 514673) B514673
theorem B507059 : Blo 99781 507059 := bstep (se 1 (by rfl) ⟨380294, by rfl⟩ : syracuseStep 507059 = 760589) B760589
theorem B113899 : Blo 99781 113899 := bstep (se 1 (by rfl) ⟨85424, by rfl⟩ : syracuseStep 113899 = 170849) B170849
theorem B114007 : Blo 99781 114007 := bstep (se 1 (by rfl) ⟨85505, by rfl⟩ : syracuseStep 114007 = 171011) B171011
theorem B343385 : Blo 99781 343385 := bstep (se 2 (by rfl) ⟨128769, by rfl⟩ : syracuseStep 343385 = 257539) B257539
theorem B114187 : Blo 99781 114187 := bstep (se 1 (by rfl) ⟨85640, by rfl⟩ : syracuseStep 114187 = 171281) B171281
theorem B114295 : Blo 99781 114295 := bstep (se 1 (by rfl) ⟨85721, by rfl⟩ : syracuseStep 114295 = 171443) B171443
theorem B179915 : Blo 99781 179915 := bstep (se 1 (by rfl) ⟨134936, by rfl⟩ : syracuseStep 179915 = 269873) B269873
theorem B114475 : Blo 99781 114475 := bstep (se 1 (by rfl) ⟨85856, by rfl⟩ : syracuseStep 114475 = 171713) B171713
theorem B180083 : Blo 99781 180083 := bstep (se 1 (by rfl) ⟨135062, by rfl⟩ : syracuseStep 180083 = 270125) B270125
theorem B114583 : Blo 99781 114583 := bstep (se 1 (by rfl) ⟨85937, by rfl⟩ : syracuseStep 114583 = 171875) B171875
theorem B344087 : Blo 99781 344087 := bstep (se 1 (by rfl) ⟨258065, by rfl⟩ : syracuseStep 344087 = 516131) B516131
theorem B114763 : Blo 99781 114763 := bstep (se 1 (by rfl) ⟨86072, by rfl⟩ : syracuseStep 114763 = 172145) B172145
theorem B213131 : Blo 99781 213131 := bstep (se 1 (by rfl) ⟨159848, by rfl⟩ : syracuseStep 213131 = 319697) B319697
theorem B114871 : Blo 99781 114871 := bstep (se 1 (by rfl) ⟨86153, by rfl⟩ : syracuseStep 114871 = 172307) B172307
theorem B770309 : Blo 99781 770309 := bstep (se 4 (by rfl) ⟨72216, by rfl⟩ : syracuseStep 770309 = 144433) B144433
theorem B115051 : Blo 99781 115051 := bstep (se 1 (by rfl) ⟨86288, by rfl⟩ : syracuseStep 115051 = 172577) B172577
theorem B115159 : Blo 99781 115159 := bstep (se 1 (by rfl) ⟨86369, by rfl⟩ : syracuseStep 115159 = 172739) B172739
theorem B344627 : Blo 99781 344627 := bstep (se 1 (by rfl) ⟨258470, by rfl⟩ : syracuseStep 344627 = 516941) B516941
theorem B442955 : Blo 99781 442955 := bstep (se 1 (by rfl) ⟨332216, by rfl⟩ : syracuseStep 442955 = 664433) B664433
theorem B2507395 : Blo 99781 2507395 := bstep (se 1 (by rfl) ⟨1880546, by rfl⟩ : syracuseStep 2507395 = 3761093) B3761093
theorem B115339 : Blo 99781 115339 := bstep (se 1 (by rfl) ⟨86504, by rfl⟩ : syracuseStep 115339 = 173009) B173009
theorem B115447 : Blo 99781 115447 := bstep (se 1 (by rfl) ⟨86585, by rfl⟩ : syracuseStep 115447 = 173171) B173171
theorem B344897 : Blo 99781 344897 := bstep (se 2 (by rfl) ⟨129336, by rfl⟩ : syracuseStep 344897 = 258673) B258673
theorem B1753973 : Blo 99781 1753973 := bstep (se 5 (by rfl) ⟨82217, by rfl⟩ : syracuseStep 1753973 = 164435) B164435
theorem B115627 : Blo 99781 115627 := bstep (se 1 (by rfl) ⟨86720, by rfl⟩ : syracuseStep 115627 = 173441) B173441
theorem B246721 : Blo 99781 246721 := bstep (se 2 (by rfl) ⟨92520, by rfl⟩ : syracuseStep 246721 = 185041) B185041
theorem B213977 : Blo 99781 213977 := bstep (se 2 (by rfl) ⟨80241, by rfl⟩ : syracuseStep 213977 = 160483) B160483
theorem B115735 : Blo 99781 115735 := bstep (se 1 (by rfl) ⟨86801, by rfl⟩ : syracuseStep 115735 = 173603) B173603
theorem B509003 : Blo 99781 509003 := bstep (se 1 (by rfl) ⟨381752, by rfl⟩ : syracuseStep 509003 = 763505) B763505
theorem B115915 : Blo 99781 115915 := bstep (se 1 (by rfl) ⟨86936, by rfl⟩ : syracuseStep 115915 = 173873) B173873
theorem B541997 : Blo 99781 541997 := bstep (se 3 (by rfl) ⟨101624, by rfl⟩ : syracuseStep 541997 = 203249) B203249
theorem B116023 : Blo 99781 116023 := bstep (se 1 (by rfl) ⟨87017, by rfl⟩ : syracuseStep 116023 = 174035) B174035
theorem B345437 : Blo 99781 345437 := bstep (se 3 (by rfl) ⟨64769, by rfl⟩ : syracuseStep 345437 = 129539) B129539
theorem B116203 : Blo 99781 116203 := bstep (se 1 (by rfl) ⟨87152, by rfl⟩ : syracuseStep 116203 = 174305) B174305
theorem B116311 : Blo 99781 116311 := bstep (se 1 (by rfl) ⟨87233, by rfl⟩ : syracuseStep 116311 = 174467) B174467
theorem B181963 : Blo 99781 181963 := bstep (se 1 (by rfl) ⟨136472, by rfl⟩ : syracuseStep 181963 = 272945) B272945
theorem B214771 : Blo 99781 214771 := bstep (se 1 (by rfl) ⟨161078, by rfl⟩ : syracuseStep 214771 = 322157) B322157
theorem B116491 : Blo 99781 116491 := bstep (se 1 (by rfl) ⟨87368, by rfl⟩ : syracuseStep 116491 = 174737) B174737
theorem B280385 : Blo 99781 280385 := bstep (se 2 (by rfl) ⟨105144, by rfl⟩ : syracuseStep 280385 = 210289) B210289
theorem B116599 : Blo 99781 116599 := bstep (se 1 (by rfl) ⟨87449, by rfl⟩ : syracuseStep 116599 = 174899) B174899
theorem B575363 : Blo 99781 575363 := bstep (se 1 (by rfl) ⟨431522, by rfl⟩ : syracuseStep 575363 = 863045) B863045
theorem B247769 : Blo 99781 247769 := bstep (se 2 (by rfl) ⟨92913, by rfl⟩ : syracuseStep 247769 = 185827) B185827
theorem B182425 : Blo 99781 182425 := bstep (se 2 (by rfl) ⟨68409, by rfl⟩ : syracuseStep 182425 = 136819) B136819
theorem B1132805 : Blo 99781 1132805 := bstep (se 4 (by rfl) ⟨106200, by rfl⟩ : syracuseStep 1132805 = 212401) B212401
theorem B149771 : Blo 99781 149771 := bstep (se 1 (by rfl) ⟨112328, by rfl⟩ : syracuseStep 149771 = 224657) B224657
theorem B739601 : Blo 99781 739601 := bstep (se 2 (by rfl) ⟨277350, by rfl⟩ : syracuseStep 739601 = 554701) B554701
theorem B149783 : Blo 99781 149783 := bstep (se 1 (by rfl) ⟨112337, by rfl⟩ : syracuseStep 149783 = 224675) B224675
theorem B379187 : Blo 99781 379187 := bstep (se 1 (by rfl) ⟨284390, by rfl⟩ : syracuseStep 379187 = 568781) B568781
theorem B379201 : Blo 99781 379201 := bstep (se 2 (by rfl) ⟨142200, by rfl⟩ : syracuseStep 379201 = 284401) B284401
theorem B575819 : Blo 99781 575819 := bstep (se 1 (by rfl) ⟨431864, by rfl⟩ : syracuseStep 575819 = 863729) B863729
theorem B149849 : Blo 99781 149849 := bstep (se 2 (by rfl) ⟨56193, by rfl⟩ : syracuseStep 149849 = 112387) B112387
theorem B149963 : Blo 99781 149963 := bstep (se 1 (by rfl) ⟨112472, by rfl⟩ : syracuseStep 149963 = 224945) B224945
theorem B346571 : Blo 99781 346571 := bstep (se 1 (by rfl) ⟨259928, by rfl⟩ : syracuseStep 346571 = 519857) B519857
theorem B149975 : Blo 99781 149975 := bstep (se 1 (by rfl) ⟨112481, by rfl⟩ : syracuseStep 149975 = 224963) B224963
theorem B150041 : Blo 99781 150041 := bstep (se 2 (by rfl) ⟨56265, by rfl⟩ : syracuseStep 150041 = 112531) B112531
theorem B215617 : Blo 99781 215617 := bstep (se 2 (by rfl) ⟨80856, by rfl⟩ : syracuseStep 215617 = 161713) B161713
theorem B313949 : Blo 99781 313949 := bstep (se 3 (by rfl) ⟨58865, by rfl⟩ : syracuseStep 313949 = 117731) B117731
theorem B772739 : Blo 99781 772739 := bstep (se 1 (by rfl) ⟨579554, by rfl⟩ : syracuseStep 772739 = 1159109) B1159109
theorem B150155 : Blo 99781 150155 := bstep (se 1 (by rfl) ⟨112616, by rfl⟩ : syracuseStep 150155 = 225233) B225233
theorem B150167 : Blo 99781 150167 := bstep (se 1 (by rfl) ⟨112625, by rfl⟩ : syracuseStep 150167 = 225251) B225251
theorem B182987 : Blo 99781 182987 := bstep (se 1 (by rfl) ⟨137240, by rfl⟩ : syracuseStep 182987 = 274481) B274481
theorem B150233 : Blo 99781 150233 := bstep (se 2 (by rfl) ⟨56337, by rfl⟩ : syracuseStep 150233 = 112675) B112675
theorem B346841 : Blo 99781 346841 := bstep (se 2 (by rfl) ⟨130065, by rfl⟩ : syracuseStep 346841 = 260131) B260131
theorem B510785 : Blo 99781 510785 := bstep (se 2 (by rfl) ⟨191544, by rfl⟩ : syracuseStep 510785 = 383089) B383089
theorem B150347 : Blo 99781 150347 := bstep (se 1 (by rfl) ⟨112760, by rfl⟩ : syracuseStep 150347 = 225521) B225521
theorem B150359 : Blo 99781 150359 := bstep (se 1 (by rfl) ⟨112769, by rfl⟩ : syracuseStep 150359 = 225539) B225539
theorem B215959 : Blo 99781 215959 := bstep (se 1 (by rfl) ⟨161969, by rfl⟩ : syracuseStep 215959 = 323939) B323939
theorem B150425 : Blo 99781 150425 := bstep (se 2 (by rfl) ⟨56409, by rfl⟩ : syracuseStep 150425 = 112819) B112819
theorem B150539 : Blo 99781 150539 := bstep (se 1 (by rfl) ⟨112904, by rfl⟩ : syracuseStep 150539 = 225809) B225809
theorem B150551 : Blo 99781 150551 := bstep (se 1 (by rfl) ⟨112913, by rfl⟩ : syracuseStep 150551 = 225827) B225827
theorem B150617 : Blo 99781 150617 := bstep (se 2 (by rfl) ⟨56481, by rfl⟩ : syracuseStep 150617 = 112963) B112963
theorem B150731 : Blo 99781 150731 := bstep (se 1 (by rfl) ⟨113048, by rfl⟩ : syracuseStep 150731 = 226097) B226097
theorem B150743 : Blo 99781 150743 := bstep (se 1 (by rfl) ⟨113057, by rfl⟩ : syracuseStep 150743 = 226115) B226115
theorem B150809 : Blo 99781 150809 := bstep (se 2 (by rfl) ⟨56553, by rfl⟩ : syracuseStep 150809 = 113107) B113107
theorem B150923 : Blo 99781 150923 := bstep (se 1 (by rfl) ⟨113192, by rfl⟩ : syracuseStep 150923 = 226385) B226385
theorem B150935 : Blo 99781 150935 := bstep (se 1 (by rfl) ⟨113201, by rfl⟩ : syracuseStep 150935 = 226403) B226403
theorem B347543 : Blo 99781 347543 := bstep (se 1 (by rfl) ⟨260657, by rfl⟩ : syracuseStep 347543 = 521315) B521315
theorem B151001 : Blo 99781 151001 := bstep (se 2 (by rfl) ⟨56625, by rfl⟩ : syracuseStep 151001 = 113251) B113251
theorem B183809 : Blo 99781 183809 := bstep (se 2 (by rfl) ⟨68928, by rfl⟩ : syracuseStep 183809 = 137857) B137857
theorem B151115 : Blo 99781 151115 := bstep (se 1 (by rfl) ⟨113336, by rfl⟩ : syracuseStep 151115 = 226673) B226673
theorem B151127 : Blo 99781 151127 := bstep (se 1 (by rfl) ⟨113345, by rfl⟩ : syracuseStep 151127 = 226691) B226691
theorem B151193 : Blo 99781 151193 := bstep (se 2 (by rfl) ⟨56697, by rfl⟩ : syracuseStep 151193 = 113395) B113395
theorem B184025 : Blo 99781 184025 := bstep (se 2 (by rfl) ⟨69009, by rfl⟩ : syracuseStep 184025 = 138019) B138019
theorem B151307 : Blo 99781 151307 := bstep (se 1 (by rfl) ⟨113480, by rfl⟩ : syracuseStep 151307 = 226961) B226961
theorem B151319 : Blo 99781 151319 := bstep (se 1 (by rfl) ⟨113489, by rfl⟩ : syracuseStep 151319 = 226979) B226979
theorem B151385 : Blo 99781 151385 := bstep (se 2 (by rfl) ⟨56769, by rfl⟩ : syracuseStep 151385 = 113539) B113539
theorem B348083 : Blo 99781 348083 := bstep (se 1 (by rfl) ⟨261062, by rfl⟩ : syracuseStep 348083 = 522125) B522125
theorem B151499 : Blo 99781 151499 := bstep (se 1 (by rfl) ⟨113624, by rfl⟩ : syracuseStep 151499 = 227249) B227249
theorem B151511 : Blo 99781 151511 := bstep (se 1 (by rfl) ⟨113633, by rfl⟩ : syracuseStep 151511 = 227267) B227267
theorem B151577 : Blo 99781 151577 := bstep (se 2 (by rfl) ⟨56841, by rfl⟩ : syracuseStep 151577 = 113683) B113683
theorem B217163 : Blo 99781 217163 := bstep (se 1 (by rfl) ⟨162872, by rfl⟩ : syracuseStep 217163 = 325745) B325745
theorem B872579 : Blo 99781 872579 := bstep (se 1 (by rfl) ⟨654434, by rfl⟩ : syracuseStep 872579 = 1308869) B1308869
theorem B151691 : Blo 99781 151691 := bstep (se 1 (by rfl) ⟨113768, by rfl⟩ : syracuseStep 151691 = 227537) B227537
theorem B151703 : Blo 99781 151703 := bstep (se 1 (by rfl) ⟨113777, by rfl⟩ : syracuseStep 151703 = 227555) B227555
theorem B348353 : Blo 99781 348353 := bstep (se 2 (by rfl) ⟨130632, by rfl⟩ : syracuseStep 348353 = 261265) B261265
theorem B381131 : Blo 99781 381131 := bstep (se 1 (by rfl) ⟨285848, by rfl⟩ : syracuseStep 381131 = 571697) B571697
theorem B151769 : Blo 99781 151769 := bstep (se 2 (by rfl) ⟨56913, by rfl⟩ : syracuseStep 151769 = 113827) B113827
theorem B381145 : Blo 99781 381145 := bstep (se 2 (by rfl) ⟨142929, by rfl⟩ : syracuseStep 381145 = 285859) B285859
theorem B151883 : Blo 99781 151883 := bstep (se 1 (by rfl) ⟨113912, by rfl⟩ : syracuseStep 151883 = 227825) B227825
theorem B151895 : Blo 99781 151895 := bstep (se 1 (by rfl) ⟨113921, by rfl⟩ : syracuseStep 151895 = 227843) B227843
theorem B872855 : Blo 99781 872855 := bstep (se 1 (by rfl) ⟨654641, by rfl⟩ : syracuseStep 872855 = 1309283) B1309283
theorem B151961 : Blo 99781 151961 := bstep (se 2 (by rfl) ⟨56985, by rfl⟩ : syracuseStep 151961 = 113971) B113971
theorem B152075 : Blo 99781 152075 := bstep (se 1 (by rfl) ⟨114056, by rfl⟩ : syracuseStep 152075 = 228113) B228113
theorem B1921553 : Blo 99781 1921553 := bstep (se 2 (by rfl) ⟨720582, by rfl⟩ : syracuseStep 1921553 = 1441165) B1441165
theorem B152087 : Blo 99781 152087 := bstep (se 1 (by rfl) ⟨114065, by rfl⟩ : syracuseStep 152087 = 228131) B228131
theorem B217675 : Blo 99781 217675 := bstep (se 1 (by rfl) ⟨163256, by rfl⟩ : syracuseStep 217675 = 326513) B326513
theorem B152153 : Blo 99781 152153 := bstep (se 2 (by rfl) ⟨57057, by rfl⟩ : syracuseStep 152153 = 114115) B114115
theorem B184961 : Blo 99781 184961 := bstep (se 2 (by rfl) ⟨69360, by rfl⟩ : syracuseStep 184961 = 138721) B138721
theorem B152267 : Blo 99781 152267 := bstep (se 1 (by rfl) ⟨114200, by rfl⟩ : syracuseStep 152267 = 228401) B228401
theorem B152279 : Blo 99781 152279 := bstep (se 1 (by rfl) ⟨114209, by rfl⟩ : syracuseStep 152279 = 228419) B228419
theorem B512729 : Blo 99781 512729 := bstep (se 2 (by rfl) ⟨192273, by rfl⟩ : syracuseStep 512729 = 384547) B384547
theorem B348893 : Blo 99781 348893 := bstep (se 3 (by rfl) ⟨65417, by rfl⟩ : syracuseStep 348893 = 130835) B130835
theorem B774917 : Blo 99781 774917 := bstep (se 4 (by rfl) ⟨72648, by rfl⟩ : syracuseStep 774917 = 145297) B145297
theorem B152345 : Blo 99781 152345 := bstep (se 2 (by rfl) ⟨57129, by rfl⟩ : syracuseStep 152345 = 114259) B114259
theorem B971621 : Blo 99781 971621 := bstep (se 4 (by rfl) ⟨91089, by rfl⟩ : syracuseStep 971621 = 182179) B182179
theorem B152459 : Blo 99781 152459 := bstep (se 1 (by rfl) ⟨114344, by rfl⟩ : syracuseStep 152459 = 228689) B228689
theorem B152471 : Blo 99781 152471 := bstep (se 1 (by rfl) ⟨114353, by rfl⟩ : syracuseStep 152471 = 228707) B228707
theorem B644057 : Blo 99781 644057 := bstep (se 2 (by rfl) ⟨241521, by rfl⟩ : syracuseStep 644057 = 483043) B483043
theorem B152537 : Blo 99781 152537 := bstep (se 2 (by rfl) ⟨57201, by rfl⟩ : syracuseStep 152537 = 114403) B114403
theorem B1463309 : Blo 99781 1463309 := bstep (se 3 (by rfl) ⟨274370, by rfl⟩ : syracuseStep 1463309 = 548741) B548741
theorem B152651 : Blo 99781 152651 := bstep (se 1 (by rfl) ⟨114488, by rfl⟩ : syracuseStep 152651 = 228977) B228977
theorem B152663 : Blo 99781 152663 := bstep (se 1 (by rfl) ⟨114497, by rfl⟩ : syracuseStep 152663 = 228995) B228995
theorem B382103 : Blo 99781 382103 := bstep (se 1 (by rfl) ⟨286577, by rfl⟩ : syracuseStep 382103 = 573155) B573155
theorem B152729 : Blo 99781 152729 := bstep (se 2 (by rfl) ⟨57273, by rfl⟩ : syracuseStep 152729 = 114547) B114547
theorem B152843 : Blo 99781 152843 := bstep (se 1 (by rfl) ⟨114632, by rfl⟩ : syracuseStep 152843 = 229265) B229265
theorem B152855 : Blo 99781 152855 := bstep (se 1 (by rfl) ⟨114641, by rfl⟩ : syracuseStep 152855 = 229283) B229283
theorem B218393 : Blo 99781 218393 := bstep (se 2 (by rfl) ⟨81897, by rfl⟩ : syracuseStep 218393 = 163795) B163795
theorem B152921 : Blo 99781 152921 := bstep (se 2 (by rfl) ⟨57345, by rfl⟩ : syracuseStep 152921 = 114691) B114691
theorem B153035 : Blo 99781 153035 := bstep (se 1 (by rfl) ⟨114776, by rfl⟩ : syracuseStep 153035 = 229553) B229553
theorem B153047 : Blo 99781 153047 := bstep (se 1 (by rfl) ⟨114785, by rfl⟩ : syracuseStep 153047 = 229571) B229571
theorem B153113 : Blo 99781 153113 := bstep (se 2 (by rfl) ⟨57417, by rfl⟩ : syracuseStep 153113 = 114835) B114835
theorem B448051 : Blo 99781 448051 := bstep (se 1 (by rfl) ⟨336038, by rfl⟩ : syracuseStep 448051 = 672077) B672077
theorem B185971 : Blo 99781 185971 := bstep (se 1 (by rfl) ⟨139478, by rfl⟩ : syracuseStep 185971 = 278957) B278957
theorem B153227 : Blo 99781 153227 := bstep (se 1 (by rfl) ⟨114920, by rfl⟩ : syracuseStep 153227 = 229841) B229841
theorem B153239 : Blo 99781 153239 := bstep (se 1 (by rfl) ⟨114929, by rfl⟩ : syracuseStep 153239 = 229859) B229859
theorem B218803 : Blo 99781 218803 := bstep (se 1 (by rfl) ⟨164102, by rfl⟩ : syracuseStep 218803 = 328205) B328205
theorem B153305 : Blo 99781 153305 := bstep (se 2 (by rfl) ⟨57489, by rfl⟩ : syracuseStep 153305 = 114979) B114979
theorem B153419 : Blo 99781 153419 := bstep (se 1 (by rfl) ⟨115064, by rfl⟩ : syracuseStep 153419 = 230129) B230129
theorem B350027 : Blo 99781 350027 := bstep (se 1 (by rfl) ⟨262520, by rfl⟩ : syracuseStep 350027 = 525041) B525041
theorem B153431 : Blo 99781 153431 := bstep (se 1 (by rfl) ⟨115073, by rfl⟩ : syracuseStep 153431 = 230147) B230147
theorem B153497 : Blo 99781 153497 := bstep (se 2 (by rfl) ⟨57561, by rfl⟩ : syracuseStep 153497 = 115123) B115123
theorem B776141 : Blo 99781 776141 := bstep (se 3 (by rfl) ⟨145526, by rfl⟩ : syracuseStep 776141 = 291053) B291053
theorem B153611 : Blo 99781 153611 := bstep (se 1 (by rfl) ⟨115208, by rfl⟩ : syracuseStep 153611 = 230417) B230417
theorem B153623 : Blo 99781 153623 := bstep (se 1 (by rfl) ⟨115217, by rfl⟩ : syracuseStep 153623 = 230435) B230435
theorem B153689 : Blo 99781 153689 := bstep (se 2 (by rfl) ⟨57633, by rfl⟩ : syracuseStep 153689 = 115267) B115267
theorem B219329 : Blo 99781 219329 := bstep (se 2 (by rfl) ⟨82248, by rfl⟩ : syracuseStep 219329 = 164497) B164497
theorem B153803 : Blo 99781 153803 := bstep (se 1 (by rfl) ⟨115352, by rfl⟩ : syracuseStep 153803 = 230705) B230705
theorem B153815 : Blo 99781 153815 := bstep (se 1 (by rfl) ⟨115361, by rfl⟩ : syracuseStep 153815 = 230723) B230723
theorem B153881 : Blo 99781 153881 := bstep (se 2 (by rfl) ⟨57705, by rfl⟩ : syracuseStep 153881 = 115411) B115411
theorem B514349 : Blo 99781 514349 := bstep (se 3 (by rfl) ⟨96440, by rfl⟩ : syracuseStep 514349 = 192881) B192881
theorem B383363 : Blo 99781 383363 := bstep (se 1 (by rfl) ⟨287522, by rfl⟩ : syracuseStep 383363 = 575045) B575045
theorem B153995 : Blo 99781 153995 := bstep (se 1 (by rfl) ⟨115496, by rfl⟩ : syracuseStep 153995 = 230993) B230993
theorem B154007 : Blo 99781 154007 := bstep (se 1 (by rfl) ⟨115505, by rfl⟩ : syracuseStep 154007 = 231011) B231011
theorem B776627 : Blo 99781 776627 := bstep (se 1 (by rfl) ⟨582470, by rfl⟩ : syracuseStep 776627 = 1164941) B1164941
theorem B154073 : Blo 99781 154073 := bstep (se 2 (by rfl) ⟨57777, by rfl⟩ : syracuseStep 154073 = 115555) B115555
theorem B1104401 : Blo 99781 1104401 := bstep (se 2 (by rfl) ⟨414150, by rfl⟩ : syracuseStep 1104401 = 828301) B828301
theorem B154187 : Blo 99781 154187 := bstep (se 1 (by rfl) ⟨115640, by rfl⟩ : syracuseStep 154187 = 231281) B231281
theorem B154199 : Blo 99781 154199 := bstep (se 1 (by rfl) ⟨115649, by rfl⟩ : syracuseStep 154199 = 231299) B231299
theorem B1464925 : Blo 99781 1464925 := bstep (se 3 (by rfl) ⟨274673, by rfl⟩ : syracuseStep 1464925 = 549347) B549347
theorem B154265 : Blo 99781 154265 := bstep (se 2 (by rfl) ⟨57849, by rfl⟩ : syracuseStep 154265 = 115699) B115699
theorem B154379 : Blo 99781 154379 := bstep (se 1 (by rfl) ⟨115784, by rfl⟩ : syracuseStep 154379 = 231569) B231569
theorem B154391 : Blo 99781 154391 := bstep (se 1 (by rfl) ⟨115793, by rfl⟩ : syracuseStep 154391 = 231587) B231587
theorem B219991 : Blo 99781 219991 := bstep (se 1 (by rfl) ⟨164993, by rfl⟩ : syracuseStep 219991 = 329987) B329987
theorem B154457 : Blo 99781 154457 := bstep (se 2 (by rfl) ⟨57921, by rfl⟩ : syracuseStep 154457 = 115843) B115843
theorem B580445 : Blo 99781 580445 := bstep (se 3 (by rfl) ⟨108833, by rfl⟩ : syracuseStep 580445 = 217667) B217667
theorem B220033 : Blo 99781 220033 := bstep (se 2 (by rfl) ⟨82512, by rfl⟩ : syracuseStep 220033 = 165025) B165025
theorem B154571 : Blo 99781 154571 := bstep (se 1 (by rfl) ⟨115928, by rfl⟩ : syracuseStep 154571 = 231857) B231857
theorem B154583 : Blo 99781 154583 := bstep (se 1 (by rfl) ⟨115937, by rfl⟩ : syracuseStep 154583 = 231875) B231875
theorem B154649 : Blo 99781 154649 := bstep (se 2 (by rfl) ⟨57993, by rfl⟩ : syracuseStep 154649 = 115987) B115987
theorem B613441 : Blo 99781 613441 := bstep (se 2 (by rfl) ⟨230040, by rfl⟩ : syracuseStep 613441 = 460081) B460081
theorem B253003 : Blo 99781 253003 := bstep (se 1 (by rfl) ⟨189752, by rfl⟩ : syracuseStep 253003 = 379505) B379505
theorem B220249 : Blo 99781 220249 := bstep (se 2 (by rfl) ⟨82593, by rfl⟩ : syracuseStep 220249 = 165187) B165187
theorem B154763 : Blo 99781 154763 := bstep (se 1 (by rfl) ⟨116072, by rfl⟩ : syracuseStep 154763 = 232145) B232145
theorem B154775 : Blo 99781 154775 := bstep (se 1 (by rfl) ⟨116081, by rfl⟩ : syracuseStep 154775 = 232163) B232163
theorem B253145 : Blo 99781 253145 := bstep (se 2 (by rfl) ⟨94929, by rfl⟩ : syracuseStep 253145 = 189859) B189859
theorem B154841 : Blo 99781 154841 := bstep (se 2 (by rfl) ⟨58065, by rfl⟩ : syracuseStep 154841 = 116131) B116131
theorem B1727729 : Blo 99781 1727729 := bstep (se 2 (by rfl) ⟨647898, by rfl⟩ : syracuseStep 1727729 = 1295797) B1295797
theorem B154955 : Blo 99781 154955 := bstep (se 1 (by rfl) ⟨116216, by rfl⟩ : syracuseStep 154955 = 232433) B232433
theorem B154967 : Blo 99781 154967 := bstep (se 1 (by rfl) ⟨116225, by rfl⟩ : syracuseStep 154967 = 232451) B232451
theorem B155033 : Blo 99781 155033 := bstep (se 2 (by rfl) ⟨58137, by rfl⟩ : syracuseStep 155033 = 116275) B116275
theorem B155147 : Blo 99781 155147 := bstep (se 1 (by rfl) ⟨116360, by rfl⟩ : syracuseStep 155147 = 232721) B232721
theorem B155159 : Blo 99781 155159 := bstep (se 1 (by rfl) ⟨116369, by rfl⟩ : syracuseStep 155159 = 232739) B232739
theorem B581195 : Blo 99781 581195 := bstep (se 1 (by rfl) ⟨435896, by rfl⟩ : syracuseStep 581195 = 871793) B871793
theorem B155225 : Blo 99781 155225 := bstep (se 2 (by rfl) ⟨58209, by rfl⟩ : syracuseStep 155225 = 116419) B116419
theorem B155339 : Blo 99781 155339 := bstep (se 1 (by rfl) ⟨116504, by rfl⟩ : syracuseStep 155339 = 233009) B233009
theorem B155351 : Blo 99781 155351 := bstep (se 1 (by rfl) ⟨116513, by rfl⟩ : syracuseStep 155351 = 233027) B233027
theorem B286429 : Blo 99781 286429 := bstep (se 3 (by rfl) ⟨53705, by rfl⟩ : syracuseStep 286429 = 107411) B107411
theorem B286487 : Blo 99781 286487 := bstep (se 1 (by rfl) ⟨214865, by rfl⟩ : syracuseStep 286487 = 429731) B429731
theorem B155417 : Blo 99781 155417 := bstep (se 2 (by rfl) ⟨58281, by rfl⟩ : syracuseStep 155417 = 116563) B116563
theorem B778085 : Blo 99781 778085 := bstep (se 4 (by rfl) ⟨72945, by rfl⟩ : syracuseStep 778085 = 145891) B145891
theorem B155531 : Blo 99781 155531 := bstep (se 1 (by rfl) ⟨116648, by rfl⟩ : syracuseStep 155531 = 233297) B233297
theorem B155543 : Blo 99781 155543 := bstep (se 1 (by rfl) ⟨116657, by rfl⟩ : syracuseStep 155543 = 233315) B233315
theorem B155609 : Blo 99781 155609 := bstep (se 2 (by rfl) ⟨58353, by rfl⟩ : syracuseStep 155609 = 116707) B116707
theorem B253975 : Blo 99781 253975 := bstep (se 1 (by rfl) ⟨190481, by rfl⟩ : syracuseStep 253975 = 380963) B380963
theorem B647261 : Blo 99781 647261 := bstep (se 3 (by rfl) ⟨121361, by rfl⟩ : syracuseStep 647261 = 242723) B242723
theorem B942353 : Blo 99781 942353 := bstep (se 2 (by rfl) ⟨353382, by rfl⟩ : syracuseStep 942353 = 706765) B706765
theorem B811309 : Blo 99781 811309 := bstep (se 3 (by rfl) ⟨152120, by rfl⟩ : syracuseStep 811309 = 304241) B304241
theorem B647489 : Blo 99781 647489 := bstep (se 2 (by rfl) ⟨242808, by rfl⟩ : syracuseStep 647489 = 485617) B485617
theorem B778571 : Blo 99781 778571 := bstep (se 1 (by rfl) ⟨583928, by rfl⟩ : syracuseStep 778571 = 1167857) B1167857
theorem B254411 : Blo 99781 254411 := bstep (se 1 (by rfl) ⟨190808, by rfl⟩ : syracuseStep 254411 = 381617) B381617
theorem B156439 : Blo 99781 156439 := bstep (se 1 (by rfl) ⟨117329, by rfl⟩ : syracuseStep 156439 = 234659) B234659
theorem B254785 : Blo 99781 254785 := bstep (se 2 (by rfl) ⟨95544, by rfl⟩ : syracuseStep 254785 = 191089) B191089
theorem B746417 : Blo 99781 746417 := bstep (se 2 (by rfl) ⟨279906, by rfl⟩ : syracuseStep 746417 = 559813) B559813
theorem B287705 : Blo 99781 287705 := bstep (se 2 (by rfl) ⟨107889, by rfl⟩ : syracuseStep 287705 = 215779) B215779
theorem B451601 : Blo 99781 451601 := bstep (se 2 (by rfl) ⟨169350, by rfl⟩ : syracuseStep 451601 = 338701) B338701
theorem B287819 : Blo 99781 287819 := bstep (se 1 (by rfl) ⟨215864, by rfl⟩ : syracuseStep 287819 = 431729) B431729
theorem B582835 : Blo 99781 582835 := bstep (se 1 (by rfl) ⟨437126, by rfl⟩ : syracuseStep 582835 = 874253) B874253
theorem B255383 : Blo 99781 255383 := bstep (se 1 (by rfl) ⟨191537, by rfl⟩ : syracuseStep 255383 = 383075) B383075
theorem B386477 : Blo 99781 386477 := bstep (se 3 (by rfl) ⟨72464, by rfl⟩ : syracuseStep 386477 = 144929) B144929
theorem B189911 : Blo 99781 189911 := bstep (se 1 (by rfl) ⟨142433, by rfl⟩ : syracuseStep 189911 = 284867) B284867
theorem B386839 : Blo 99781 386839 := bstep (se 1 (by rfl) ⟨290129, by rfl⟩ : syracuseStep 386839 = 580259) B580259
theorem B780209 : Blo 99781 780209 := bstep (se 2 (by rfl) ⟨292578, by rfl⟩ : syracuseStep 780209 = 585157) B585157
theorem B157643 : Blo 99781 157643 := bstep (se 1 (by rfl) ⟨118232, by rfl⟩ : syracuseStep 157643 = 236465) B236465
theorem B190451 : Blo 99781 190451 := bstep (se 1 (by rfl) ⟨142838, by rfl⟩ : syracuseStep 190451 = 285677) B285677
theorem B878627 : Blo 99781 878627 := bstep (se 1 (by rfl) ⟨658970, by rfl⟩ : syracuseStep 878627 = 1317941) B1317941
theorem B518237 : Blo 99781 518237 := bstep (se 3 (by rfl) ⟨97169, by rfl⟩ : syracuseStep 518237 = 194339) B194339
theorem B354397 : Blo 99781 354397 := bstep (se 3 (by rfl) ⟨66449, by rfl⟩ : syracuseStep 354397 = 132899) B132899
theorem B190603 : Blo 99781 190603 := bstep (se 1 (by rfl) ⟨142952, by rfl⟩ : syracuseStep 190603 = 285905) B285905
theorem B288947 : Blo 99781 288947 := bstep (se 1 (by rfl) ⟨216710, by rfl⟩ : syracuseStep 288947 = 433421) B433421
theorem B387251 : Blo 99781 387251 := bstep (se 1 (by rfl) ⟨290438, by rfl⟩ : syracuseStep 387251 = 580877) B580877
theorem B223411 : Blo 99781 223411 := bstep (se 1 (by rfl) ⟨167558, by rfl⟩ : syracuseStep 223411 = 335117) B335117
theorem B256193 : Blo 99781 256193 := bstep (se 2 (by rfl) ⟨96072, by rfl⟩ : syracuseStep 256193 = 192145) B192145
theorem B190937 : Blo 99781 190937 := bstep (se 2 (by rfl) ⟨71601, by rfl⟩ : syracuseStep 190937 = 143203) B143203
theorem B649745 : Blo 99781 649745 := bstep (se 2 (by rfl) ⟨243654, by rfl⟩ : syracuseStep 649745 = 487309) B487309
theorem B289345 : Blo 99781 289345 := bstep (se 2 (by rfl) ⟨108504, by rfl⟩ : syracuseStep 289345 = 217009) B217009
theorem B584293 : Blo 99781 584293 := bstep (se 4 (by rfl) ⟨54777, by rfl⟩ : syracuseStep 584293 = 109555) B109555
theorem B256729 : Blo 99781 256729 := bstep (se 2 (by rfl) ⟨96273, by rfl⟩ : syracuseStep 256729 = 192547) B192547
theorem B191575 : Blo 99781 191575 := bstep (se 1 (by rfl) ⟨143681, by rfl⟩ : syracuseStep 191575 = 287363) B287363
theorem B224407 : Blo 99781 224407 := bstep (se 1 (by rfl) ⟨168305, by rfl⟩ : syracuseStep 224407 = 336611) B336611
theorem B224513 : Blo 99781 224513 := bstep (se 2 (by rfl) ⟨84192, by rfl⟩ : syracuseStep 224513 = 168385) B168385
theorem B945413 : Blo 99781 945413 := bstep (se 4 (by rfl) ⟨88632, by rfl⟩ : syracuseStep 945413 = 177265) B177265
theorem B224729 : Blo 99781 224729 := bstep (se 2 (by rfl) ⟨84273, by rfl⟩ : syracuseStep 224729 = 168547) B168547
theorem B224819 : Blo 99781 224819 := bstep (se 1 (by rfl) ⟨168614, by rfl⟩ : syracuseStep 224819 = 337229) B337229
theorem B224855 : Blo 99781 224855 := bstep (se 1 (by rfl) ⟨168641, by rfl⟩ : syracuseStep 224855 = 337283) B337283
theorem B388739 : Blo 99781 388739 := bstep (se 1 (by rfl) ⟨291554, by rfl⟩ : syracuseStep 388739 = 583109) B583109
theorem B126679 : Blo 99781 126679 := bstep (se 1 (by rfl) ⟨95009, by rfl⟩ : syracuseStep 126679 = 190019) B190019
theorem B913157 : Blo 99781 913157 := bstep (se 4 (by rfl) ⟨85608, by rfl⟩ : syracuseStep 913157 = 171217) B171217
theorem B225035 : Blo 99781 225035 := bstep (se 1 (by rfl) ⟨168776, by rfl⟩ : syracuseStep 225035 = 337553) B337553
theorem B257843 : Blo 99781 257843 := bstep (se 1 (by rfl) ⟨193382, by rfl⟩ : syracuseStep 257843 = 386765) B386765
theorem B225089 : Blo 99781 225089 := bstep (se 2 (by rfl) ⟨84408, by rfl⟩ : syracuseStep 225089 = 168817) B168817
theorem B192395 : Blo 99781 192395 := bstep (se 1 (by rfl) ⟨144296, by rfl⟩ : syracuseStep 192395 = 288593) B288593
theorem B192449 : Blo 99781 192449 := bstep (se 2 (by rfl) ⟨72168, by rfl⟩ : syracuseStep 192449 = 144337) B144337
theorem B225305 : Blo 99781 225305 := bstep (se 2 (by rfl) ⟨84489, by rfl⟩ : syracuseStep 225305 = 168979) B168979
theorem B389195 : Blo 99781 389195 := bstep (se 1 (by rfl) ⟨291896, by rfl⟩ : syracuseStep 389195 = 583793) B583793
theorem B258137 : Blo 99781 258137 := bstep (se 2 (by rfl) ⟨96801, by rfl⟩ : syracuseStep 258137 = 193603) B193603
theorem B225395 : Blo 99781 225395 := bstep (se 1 (by rfl) ⟨169046, by rfl⟩ : syracuseStep 225395 = 338093) B338093
theorem B225431 : Blo 99781 225431 := bstep (se 1 (by rfl) ⟨169073, by rfl⟩ : syracuseStep 225431 = 338147) B338147
theorem B520343 : Blo 99781 520343 := bstep (se 1 (by rfl) ⟨390257, by rfl⟩ : syracuseStep 520343 = 780515) B780515
theorem B389393 : Blo 99781 389393 := bstep (se 2 (by rfl) ⟨146022, by rfl⟩ : syracuseStep 389393 = 292045) B292045
theorem B225611 : Blo 99781 225611 := bstep (se 1 (by rfl) ⟨169208, by rfl⟩ : syracuseStep 225611 = 338417) B338417
theorem B225665 : Blo 99781 225665 := bstep (se 2 (by rfl) ⟨84624, by rfl⟩ : syracuseStep 225665 = 169249) B169249
theorem B225881 : Blo 99781 225881 := bstep (se 2 (by rfl) ⟨84705, by rfl⟩ : syracuseStep 225881 = 169411) B169411
theorem B815717 : Blo 99781 815717 := bstep (se 4 (by rfl) ⟨76473, by rfl⟩ : syracuseStep 815717 = 152947) B152947
theorem B455341 : Blo 99781 455341 := bstep (se 3 (by rfl) ⟨85376, by rfl⟩ : syracuseStep 455341 = 170753) B170753
theorem B225971 : Blo 99781 225971 := bstep (se 1 (by rfl) ⟨169478, by rfl⟩ : syracuseStep 225971 = 338957) B338957
theorem B226007 : Blo 99781 226007 := bstep (se 1 (by rfl) ⟨169505, by rfl⟩ : syracuseStep 226007 = 339011) B339011
theorem B881425 : Blo 99781 881425 := bstep (se 2 (by rfl) ⟨330534, by rfl⟩ : syracuseStep 881425 = 661069) B661069
theorem B193367 : Blo 99781 193367 := bstep (se 1 (by rfl) ⟨145025, by rfl⟩ : syracuseStep 193367 = 290051) B290051
theorem B226187 : Blo 99781 226187 := bstep (se 1 (by rfl) ⟨169640, by rfl⟩ : syracuseStep 226187 = 339281) B339281
theorem B914327 : Blo 99781 914327 := bstep (se 1 (by rfl) ⟨685745, by rfl⟩ : syracuseStep 914327 = 1371491) B1371491
theorem B226241 : Blo 99781 226241 := bstep (se 2 (by rfl) ⟨84840, by rfl⟩ : syracuseStep 226241 = 169681) B169681
theorem B291863 : Blo 99781 291863 := bstep (se 1 (by rfl) ⟨218897, by rfl⟩ : syracuseStep 291863 = 437795) B437795
theorem B390167 : Blo 99781 390167 := bstep (se 1 (by rfl) ⟨292625, by rfl⟩ : syracuseStep 390167 = 585251) B585251
theorem B390275 : Blo 99781 390275 := bstep (se 1 (by rfl) ⟨292706, by rfl⟩ : syracuseStep 390275 = 585413) B585413
theorem B226457 : Blo 99781 226457 := bstep (se 2 (by rfl) ⟨84921, by rfl⟩ : syracuseStep 226457 = 169843) B169843
theorem B783539 : Blo 99781 783539 := bstep (se 1 (by rfl) ⟨587654, by rfl⟩ : syracuseStep 783539 = 1175309) B1175309
theorem B390365 : Blo 99781 390365 := bstep (se 3 (by rfl) ⟨73193, by rfl⟩ : syracuseStep 390365 = 146387) B146387
theorem B226547 : Blo 99781 226547 := bstep (se 1 (by rfl) ⟨169910, by rfl⟩ : syracuseStep 226547 = 339821) B339821
theorem B226583 : Blo 99781 226583 := bstep (se 1 (by rfl) ⟨169937, by rfl⟩ : syracuseStep 226583 = 339875) B339875
theorem B193907 : Blo 99781 193907 := bstep (se 1 (by rfl) ⟨145430, by rfl⟩ : syracuseStep 193907 = 290861) B290861
theorem B128395 : Blo 99781 128395 := bstep (se 1 (by rfl) ⟨96296, by rfl⟩ : syracuseStep 128395 = 192593) B192593
theorem B226763 : Blo 99781 226763 := bstep (se 1 (by rfl) ⟨170072, by rfl⟩ : syracuseStep 226763 = 340145) B340145
theorem B226817 : Blo 99781 226817 := bstep (se 2 (by rfl) ⟨85056, by rfl⟩ : syracuseStep 226817 = 170113) B170113
theorem B783917 : Blo 99781 783917 := bstep (se 3 (by rfl) ⟨146984, by rfl⟩ : syracuseStep 783917 = 293969) B293969
theorem B882251 : Blo 99781 882251 := bstep (se 1 (by rfl) ⟨661688, by rfl⟩ : syracuseStep 882251 = 1323377) B1323377
theorem B325271 : Blo 99781 325271 := bstep (se 1 (by rfl) ⟨243953, by rfl⟩ : syracuseStep 325271 = 487907) B487907
theorem B259787 : Blo 99781 259787 := bstep (se 1 (by rfl) ⟨194840, by rfl⟩ : syracuseStep 259787 = 389681) B389681
theorem B227033 : Blo 99781 227033 := bstep (se 2 (by rfl) ⟨85137, by rfl⟩ : syracuseStep 227033 = 170275) B170275
theorem B227123 : Blo 99781 227123 := bstep (se 1 (by rfl) ⟨170342, by rfl⟩ : syracuseStep 227123 = 340685) B340685
theorem B227159 : Blo 99781 227159 := bstep (se 1 (by rfl) ⟨170369, by rfl⟩ : syracuseStep 227159 = 340739) B340739
theorem B194393 : Blo 99781 194393 := bstep (se 2 (by rfl) ⟨72897, by rfl⟩ : syracuseStep 194393 = 145795) B145795
theorem B325579 : Blo 99781 325579 := bstep (se 1 (by rfl) ⟨244184, by rfl⟩ : syracuseStep 325579 = 488369) B488369
theorem B227339 : Blo 99781 227339 := bstep (se 1 (by rfl) ⟨170504, by rfl⟩ : syracuseStep 227339 = 341009) B341009
theorem B915491 : Blo 99781 915491 := bstep (se 1 (by rfl) ⟨686618, by rfl⟩ : syracuseStep 915491 = 1373237) B1373237
theorem B227393 : Blo 99781 227393 := bstep (se 2 (by rfl) ⟨85272, by rfl⟩ : syracuseStep 227393 = 170545) B170545
theorem B129163 : Blo 99781 129163 := bstep (se 1 (by rfl) ⟨96872, by rfl⟩ : syracuseStep 129163 = 193745) B193745
theorem B227609 : Blo 99781 227609 := bstep (se 2 (by rfl) ⟨85353, by rfl⟩ : syracuseStep 227609 = 170707) B170707
theorem B293195 : Blo 99781 293195 := bstep (se 1 (by rfl) ⟨219896, by rfl⟩ : syracuseStep 293195 = 439793) B439793
theorem B129367 : Blo 99781 129367 := bstep (se 1 (by rfl) ⟨97025, by rfl⟩ : syracuseStep 129367 = 194051) B194051
theorem B227699 : Blo 99781 227699 := bstep (se 1 (by rfl) ⟨170774, by rfl⟩ : syracuseStep 227699 = 341549) B341549
theorem B227735 : Blo 99781 227735 := bstep (se 1 (by rfl) ⟨170801, by rfl⟩ : syracuseStep 227735 = 341603) B341603
theorem B227915 : Blo 99781 227915 := bstep (se 1 (by rfl) ⟨170936, by rfl⟩ : syracuseStep 227915 = 341873) B341873
theorem B227969 : Blo 99781 227969 := bstep (se 2 (by rfl) ⟨85488, by rfl⟩ : syracuseStep 227969 = 170977) B170977
theorem B260759 : Blo 99781 260759 := bstep (se 1 (by rfl) ⟨195569, by rfl⟩ : syracuseStep 260759 = 391139) B391139
theorem B1080013 : Blo 99781 1080013 := bstep (se 3 (by rfl) ⟨202502, by rfl⟩ : syracuseStep 1080013 = 405005) B405005
theorem B654155 : Blo 99781 654155 := bstep (se 1 (by rfl) ⟨490616, by rfl⟩ : syracuseStep 654155 = 981233) B981233
theorem B228185 : Blo 99781 228185 := bstep (se 2 (by rfl) ⟨85569, by rfl⟩ : syracuseStep 228185 = 171139) B171139
theorem B228275 : Blo 99781 228275 := bstep (se 1 (by rfl) ⟨171206, by rfl⟩ : syracuseStep 228275 = 342413) B342413
theorem B228311 : Blo 99781 228311 := bstep (se 1 (by rfl) ⟨171233, by rfl⟩ : syracuseStep 228311 = 342467) B342467
theorem B1145987 : Blo 99781 1145987 := bstep (se 1 (by rfl) ⟨859490, by rfl⟩ : syracuseStep 1145987 = 1718981) B1718981
theorem B392323 : Blo 99781 392323 := bstep (se 1 (by rfl) ⟨294242, by rfl⟩ : syracuseStep 392323 = 588485) B588485
theorem B228491 : Blo 99781 228491 := bstep (se 1 (by rfl) ⟨171368, by rfl⟩ : syracuseStep 228491 = 342737) B342737
theorem B130187 : Blo 99781 130187 := bstep (se 1 (by rfl) ⟨97640, by rfl⟩ : syracuseStep 130187 = 195281) B195281
theorem B228545 : Blo 99781 228545 := bstep (se 2 (by rfl) ⟨85704, by rfl⟩ : syracuseStep 228545 = 171409) B171409
theorem B195851 : Blo 99781 195851 := bstep (se 1 (by rfl) ⟨146888, by rfl⟩ : syracuseStep 195851 = 293777) B293777
theorem B490769 : Blo 99781 490769 := bstep (se 2 (by rfl) ⟨184038, by rfl⟩ : syracuseStep 490769 = 368077) B368077
theorem B261427 : Blo 99781 261427 := bstep (se 1 (by rfl) ⟨196070, by rfl⟩ : syracuseStep 261427 = 392141) B392141
theorem B228761 : Blo 99781 228761 := bstep (se 2 (by rfl) ⟨85785, by rfl⟩ : syracuseStep 228761 = 171571) B171571
theorem B392627 : Blo 99781 392627 := bstep (se 1 (by rfl) ⟨294470, by rfl⟩ : syracuseStep 392627 = 588941) B588941
theorem B196033 : Blo 99781 196033 := bstep (se 2 (by rfl) ⟨73512, by rfl⟩ : syracuseStep 196033 = 147025) B147025
theorem B261569 : Blo 99781 261569 := bstep (se 2 (by rfl) ⟨98088, by rfl⟩ : syracuseStep 261569 = 196177) B196177
theorem B228851 : Blo 99781 228851 := bstep (se 1 (by rfl) ⟨171638, by rfl⟩ : syracuseStep 228851 = 343277) B343277
theorem B228887 : Blo 99781 228887 := bstep (se 1 (by rfl) ⟨171665, by rfl⟩ : syracuseStep 228887 = 343331) B343331
theorem B523907 : Blo 99781 523907 := bstep (se 1 (by rfl) ⟨392930, by rfl⟩ : syracuseStep 523907 = 785861) B785861
theorem B229067 : Blo 99781 229067 := bstep (se 1 (by rfl) ⟨171800, by rfl⟩ : syracuseStep 229067 = 343601) B343601
theorem B229121 : Blo 99781 229121 := bstep (se 2 (by rfl) ⟨85920, by rfl⟩ : syracuseStep 229121 = 171841) B171841
theorem B130891 : Blo 99781 130891 := bstep (se 1 (by rfl) ⟨98168, by rfl⟩ : syracuseStep 130891 = 196337) B196337
theorem B196481 : Blo 99781 196481 := bstep (se 2 (by rfl) ⟨73680, by rfl⟩ : syracuseStep 196481 = 147361) B147361
theorem B1343411 : Blo 99781 1343411 := bstep (se 1 (by rfl) ⟨1007558, by rfl⟩ : syracuseStep 1343411 = 2015117) B2015117
theorem B294835 : Blo 99781 294835 := bstep (se 1 (by rfl) ⟨221126, by rfl⟩ : syracuseStep 294835 = 442253) B442253
theorem B360395 : Blo 99781 360395 := bstep (se 1 (by rfl) ⟨270296, by rfl⟩ : syracuseStep 360395 = 540593) B540593
theorem B229337 : Blo 99781 229337 := bstep (se 2 (by rfl) ⟨86001, by rfl⟩ : syracuseStep 229337 = 172003) B172003
theorem B229391 : Blo 99781 229391 := bstep (se 1 (by rfl) ⟨172043, by rfl⟩ : syracuseStep 229391 = 344087) B344087
theorem B229409 : Blo 99781 229409 := bstep (se 2 (by rfl) ⟨86028, by rfl⟩ : syracuseStep 229409 = 172057) B172057
theorem B262187 : Blo 99781 262187 := bstep (se 1 (by rfl) ⟨196640, by rfl⟩ : syracuseStep 262187 = 393281) B393281
theorem B589943 : Blo 99781 589943 := bstep (se 1 (by rfl) ⟨442457, by rfl⟩ : syracuseStep 589943 = 884915) B884915
theorem B131215 : Blo 99781 131215 := bstep (se 1 (by rfl) ⟨98411, by rfl⟩ : syracuseStep 131215 = 196823) B196823
theorem B2195657 : Blo 99781 2195657 := bstep (se 2 (by rfl) ⟨823371, by rfl⟩ : syracuseStep 2195657 = 1646743) B1646743
theorem B40337621 : Blo 99781 40337621 := bstep (se 7 (by rfl) ⟨472706, by rfl⟩ : syracuseStep 40337621 = 945413) B945413
theorem B2326877 : Blo 99781 2326877 := bstep (se 3 (by rfl) ⟨436289, by rfl⟩ : syracuseStep 2326877 = 872579) B872579
theorem B229751 : Blo 99781 229751 := bstep (se 1 (by rfl) ⟨172313, by rfl⟩ : syracuseStep 229751 = 344627) B344627
theorem B1081745 : Blo 99781 1081745 := bstep (se 2 (by rfl) ⟨405654, by rfl⟩ : syracuseStep 1081745 = 811309) B811309
theorem B786833 : Blo 99781 786833 := bstep (se 2 (by rfl) ⟨295062, by rfl⟩ : syracuseStep 786833 = 590125) B590125
theorem B229931 : Blo 99781 229931 := bstep (se 1 (by rfl) ⟨172448, by rfl⟩ : syracuseStep 229931 = 344897) B344897
theorem B590651 : Blo 99781 590651 := bstep (se 1 (by rfl) ⟨442988, by rfl⟩ : syracuseStep 590651 = 885977) B885977
theorem B3343193 : Blo 99781 3343193 := bstep (se 2 (by rfl) ⟨1253697, by rfl⟩ : syracuseStep 3343193 = 2507395) B2507395
theorem B361331 : Blo 99781 361331 := bstep (se 1 (by rfl) ⟨270998, by rfl⟩ : syracuseStep 361331 = 541997) B541997
theorem B230291 : Blo 99781 230291 := bstep (se 1 (by rfl) ⟨172718, by rfl⟩ : syracuseStep 230291 = 345437) B345437
theorem B525203 : Blo 99781 525203 := bstep (se 1 (by rfl) ⟨393902, by rfl⟩ : syracuseStep 525203 = 787805) B787805
theorem B230345 : Blo 99781 230345 := bstep (se 2 (by rfl) ⟨86379, by rfl⟩ : syracuseStep 230345 = 172759) B172759
theorem B328961 : Blo 99781 328961 := bstep (se 2 (by rfl) ⟨123360, by rfl⟩ : syracuseStep 328961 = 246721) B246721
theorem B165179 : Blo 99781 165179 := bstep (se 1 (by rfl) ⟨123884, by rfl⟩ : syracuseStep 165179 = 247769) B247769
theorem B755203 : Blo 99781 755203 := bstep (se 1 (by rfl) ⟨566402, by rfl⟩ : syracuseStep 755203 = 1132805) B1132805
theorem B99847 : Blo 99781 99847 := bstep (se 1 (by rfl) ⟨74885, by rfl⟩ : syracuseStep 99847 = 149771) B149771
theorem B493067 : Blo 99781 493067 := bstep (se 1 (by rfl) ⟨369800, by rfl⟩ : syracuseStep 493067 = 739601) B739601
theorem B99855 : Blo 99781 99855 := bstep (se 1 (by rfl) ⟨74891, by rfl⟩ : syracuseStep 99855 = 149783) B149783
theorem B1181213 : Blo 99781 1181213 := bstep (se 3 (by rfl) ⟨221477, by rfl⟩ : syracuseStep 1181213 = 442955) B442955
theorem B99899 : Blo 99781 99899 := bstep (se 1 (by rfl) ⟨74924, by rfl⟩ : syracuseStep 99899 = 149849) B149849
theorem B99975 : Blo 99781 99975 := bstep (se 1 (by rfl) ⟨74981, by rfl⟩ : syracuseStep 99975 = 149963) B149963
theorem B231047 : Blo 99781 231047 := bstep (se 1 (by rfl) ⟨173285, by rfl⟩ : syracuseStep 231047 = 346571) B346571
theorem B99983 : Blo 99781 99983 := bstep (se 1 (by rfl) ⟨74987, by rfl⟩ : syracuseStep 99983 = 149975) B149975
theorem B493229 : Blo 99781 493229 := bstep (se 3 (by rfl) ⟨92480, by rfl⟩ : syracuseStep 493229 = 184961) B184961
theorem B100027 : Blo 99781 100027 := bstep (se 1 (by rfl) ⟨75020, by rfl⟩ : syracuseStep 100027 = 150041) B150041
theorem B100103 : Blo 99781 100103 := bstep (se 1 (by rfl) ⟨75077, by rfl⟩ : syracuseStep 100103 = 150155) B150155
theorem B100111 : Blo 99781 100111 := bstep (se 1 (by rfl) ⟨75083, by rfl⟩ : syracuseStep 100111 = 150167) B150167
theorem B100155 : Blo 99781 100155 := bstep (se 1 (by rfl) ⟨75116, by rfl⟩ : syracuseStep 100155 = 150233) B150233
theorem B231227 : Blo 99781 231227 := bstep (se 1 (by rfl) ⟨173420, by rfl⟩ : syracuseStep 231227 = 346841) B346841
theorem B100231 : Blo 99781 100231 := bstep (se 1 (by rfl) ⟨75173, by rfl⟩ : syracuseStep 100231 = 150347) B150347
theorem B100239 : Blo 99781 100239 := bstep (se 1 (by rfl) ⟨75179, by rfl⟩ : syracuseStep 100239 = 150359) B150359
theorem B231353 : Blo 99781 231353 := bstep (se 2 (by rfl) ⟨86757, by rfl⟩ : syracuseStep 231353 = 173515) B173515
theorem B100283 : Blo 99781 100283 := bstep (se 1 (by rfl) ⟨75212, by rfl⟩ : syracuseStep 100283 = 150425) B150425
theorem B100359 : Blo 99781 100359 := bstep (se 1 (by rfl) ⟨75269, by rfl⟩ : syracuseStep 100359 = 150539) B150539
theorem B100367 : Blo 99781 100367 := bstep (se 1 (by rfl) ⟨75275, by rfl⟩ : syracuseStep 100367 = 150551) B150551
theorem B100411 : Blo 99781 100411 := bstep (se 1 (by rfl) ⟨75308, by rfl⟩ : syracuseStep 100411 = 150617) B150617
theorem B100487 : Blo 99781 100487 := bstep (se 1 (by rfl) ⟨75365, by rfl⟩ : syracuseStep 100487 = 150731) B150731
theorem B100495 : Blo 99781 100495 := bstep (se 1 (by rfl) ⟨75371, by rfl⟩ : syracuseStep 100495 = 150743) B150743
theorem B100539 : Blo 99781 100539 := bstep (se 1 (by rfl) ⟨75404, by rfl⟩ : syracuseStep 100539 = 150809) B150809
theorem B100615 : Blo 99781 100615 := bstep (se 1 (by rfl) ⟨75461, by rfl⟩ : syracuseStep 100615 = 150923) B150923
theorem B100623 : Blo 99781 100623 := bstep (se 1 (by rfl) ⟨75467, by rfl⟩ : syracuseStep 100623 = 150935) B150935
theorem B231695 : Blo 99781 231695 := bstep (se 1 (by rfl) ⟨173771, by rfl⟩ : syracuseStep 231695 = 347543) B347543
theorem B231713 : Blo 99781 231713 := bstep (se 2 (by rfl) ⟨86892, by rfl⟩ : syracuseStep 231713 = 173785) B173785
theorem B100667 : Blo 99781 100667 := bstep (se 1 (by rfl) ⟨75500, by rfl⟩ : syracuseStep 100667 = 151001) B151001
theorem B100743 : Blo 99781 100743 := bstep (se 1 (by rfl) ⟨75557, by rfl⟩ : syracuseStep 100743 = 151115) B151115
theorem B100751 : Blo 99781 100751 := bstep (se 1 (by rfl) ⟨75563, by rfl⟩ : syracuseStep 100751 = 151127) B151127
theorem B100795 : Blo 99781 100795 := bstep (se 1 (by rfl) ⟨75596, by rfl⟩ : syracuseStep 100795 = 151193) B151193
theorem B100871 : Blo 99781 100871 := bstep (se 1 (by rfl) ⟨75653, by rfl⟩ : syracuseStep 100871 = 151307) B151307
theorem B100879 : Blo 99781 100879 := bstep (se 1 (by rfl) ⟨75659, by rfl⟩ : syracuseStep 100879 = 151319) B151319
theorem B100923 : Blo 99781 100923 := bstep (se 1 (by rfl) ⟨75692, by rfl⟩ : syracuseStep 100923 = 151385) B151385
theorem B232055 : Blo 99781 232055 := bstep (se 1 (by rfl) ⟨174041, by rfl⟩ : syracuseStep 232055 = 348083) B348083
theorem B100999 : Blo 99781 100999 := bstep (se 1 (by rfl) ⟨75749, by rfl⟩ : syracuseStep 100999 = 151499) B151499
theorem B101007 : Blo 99781 101007 := bstep (se 1 (by rfl) ⟨75755, by rfl⟩ : syracuseStep 101007 = 151511) B151511
theorem B101051 : Blo 99781 101051 := bstep (se 1 (by rfl) ⟨75788, by rfl⟩ : syracuseStep 101051 = 151577) B151577
theorem B101127 : Blo 99781 101127 := bstep (se 1 (by rfl) ⟨75845, by rfl⟩ : syracuseStep 101127 = 151691) B151691
theorem B101135 : Blo 99781 101135 := bstep (se 1 (by rfl) ⟨75851, by rfl⟩ : syracuseStep 101135 = 151703) B151703
theorem B232235 : Blo 99781 232235 := bstep (se 1 (by rfl) ⟨174176, by rfl⟩ : syracuseStep 232235 = 348353) B348353
theorem B101179 : Blo 99781 101179 := bstep (se 1 (by rfl) ⟨75884, by rfl⟩ : syracuseStep 101179 = 151769) B151769
theorem B101255 : Blo 99781 101255 := bstep (se 1 (by rfl) ⟨75941, by rfl⟩ : syracuseStep 101255 = 151883) B151883
theorem B101263 : Blo 99781 101263 := bstep (se 1 (by rfl) ⟨75947, by rfl⟩ : syracuseStep 101263 = 151895) B151895
theorem B297881 : Blo 99781 297881 := bstep (se 2 (by rfl) ⟨111705, by rfl⟩ : syracuseStep 297881 = 223411) B223411
theorem B101307 : Blo 99781 101307 := bstep (se 1 (by rfl) ⟨75980, by rfl⟩ : syracuseStep 101307 = 151961) B151961
theorem B101383 : Blo 99781 101383 := bstep (se 1 (by rfl) ⟨76037, by rfl⟩ : syracuseStep 101383 = 152075) B152075
theorem B1281035 : Blo 99781 1281035 := bstep (se 1 (by rfl) ⟨960776, by rfl⟩ : syracuseStep 1281035 = 1921553) B1921553
theorem B101391 : Blo 99781 101391 := bstep (se 1 (by rfl) ⟨76043, by rfl⟩ : syracuseStep 101391 = 152087) B152087
theorem B101435 : Blo 99781 101435 := bstep (se 1 (by rfl) ⟨76076, by rfl⟩ : syracuseStep 101435 = 152153) B152153
theorem B101511 : Blo 99781 101511 := bstep (se 1 (by rfl) ⟨76133, by rfl⟩ : syracuseStep 101511 = 152267) B152267
theorem B101519 : Blo 99781 101519 := bstep (se 1 (by rfl) ⟨76139, by rfl⟩ : syracuseStep 101519 = 152279) B152279
theorem B232595 : Blo 99781 232595 := bstep (se 1 (by rfl) ⟨174446, by rfl⟩ : syracuseStep 232595 = 348893) B348893
theorem B101563 : Blo 99781 101563 := bstep (se 1 (by rfl) ⟨76172, by rfl⟩ : syracuseStep 101563 = 152345) B152345
theorem B232649 : Blo 99781 232649 := bstep (se 2 (by rfl) ⟨87243, by rfl⟩ : syracuseStep 232649 = 174487) B174487
theorem B101639 : Blo 99781 101639 := bstep (se 1 (by rfl) ⟨76229, by rfl⟩ : syracuseStep 101639 = 152459) B152459
theorem B101647 : Blo 99781 101647 := bstep (se 1 (by rfl) ⟨76235, by rfl⟩ : syracuseStep 101647 = 152471) B152471
theorem B429371 : Blo 99781 429371 := bstep (se 1 (by rfl) ⟨322028, by rfl⟩ : syracuseStep 429371 = 644057) B644057
theorem B101691 : Blo 99781 101691 := bstep (se 1 (by rfl) ⟨76268, by rfl⟩ : syracuseStep 101691 = 152537) B152537
theorem B101767 : Blo 99781 101767 := bstep (se 1 (by rfl) ⟨76325, by rfl⟩ : syracuseStep 101767 = 152651) B152651
theorem B101775 : Blo 99781 101775 := bstep (se 1 (by rfl) ⟨76331, by rfl⟩ : syracuseStep 101775 = 152663) B152663
theorem B101819 : Blo 99781 101819 := bstep (se 1 (by rfl) ⟨76364, by rfl⟩ : syracuseStep 101819 = 152729) B152729
theorem B101895 : Blo 99781 101895 := bstep (se 1 (by rfl) ⟨76421, by rfl⟩ : syracuseStep 101895 = 152843) B152843
theorem B101903 : Blo 99781 101903 := bstep (se 1 (by rfl) ⟨76427, by rfl⟩ : syracuseStep 101903 = 152855) B152855
theorem B101947 : Blo 99781 101947 := bstep (se 1 (by rfl) ⟨76460, by rfl⟩ : syracuseStep 101947 = 152921) B152921
theorem B527939 : Blo 99781 527939 := bstep (se 1 (by rfl) ⟨395954, by rfl⟩ : syracuseStep 527939 = 791909) B791909
theorem B102023 : Blo 99781 102023 := bstep (se 1 (by rfl) ⟨76517, by rfl⟩ : syracuseStep 102023 = 153035) B153035
theorem B102031 : Blo 99781 102031 := bstep (se 1 (by rfl) ⟨76523, by rfl⟩ : syracuseStep 102031 = 153047) B153047
theorem B102075 : Blo 99781 102075 := bstep (se 1 (by rfl) ⟨76556, by rfl⟩ : syracuseStep 102075 = 153113) B153113
theorem B495305 : Blo 99781 495305 := bstep (se 2 (by rfl) ⟨185739, by rfl⟩ : syracuseStep 495305 = 371479) B371479
theorem B397001 : Blo 99781 397001 := bstep (se 2 (by rfl) ⟨148875, by rfl⟩ : syracuseStep 397001 = 297751) B297751
theorem B102151 : Blo 99781 102151 := bstep (se 1 (by rfl) ⟨76613, by rfl⟩ : syracuseStep 102151 = 153227) B153227
theorem B102159 : Blo 99781 102159 := bstep (se 1 (by rfl) ⟨76619, by rfl⟩ : syracuseStep 102159 = 153239) B153239
theorem B102203 : Blo 99781 102203 := bstep (se 1 (by rfl) ⟨76652, by rfl⟩ : syracuseStep 102203 = 153305) B153305
theorem B102279 : Blo 99781 102279 := bstep (se 1 (by rfl) ⟨76709, by rfl⟩ : syracuseStep 102279 = 153419) B153419
theorem B233351 : Blo 99781 233351 := bstep (se 1 (by rfl) ⟨175013, by rfl⟩ : syracuseStep 233351 = 350027) B350027
theorem B102287 : Blo 99781 102287 := bstep (se 1 (by rfl) ⟨76715, by rfl⟩ : syracuseStep 102287 = 153431) B153431
theorem B102331 : Blo 99781 102331 := bstep (se 1 (by rfl) ⟨76748, by rfl⟩ : syracuseStep 102331 = 153497) B153497
theorem B102407 : Blo 99781 102407 := bstep (se 1 (by rfl) ⟨76805, by rfl⟩ : syracuseStep 102407 = 153611) B153611
theorem B102415 : Blo 99781 102415 := bstep (se 1 (by rfl) ⟨76811, by rfl⟩ : syracuseStep 102415 = 153623) B153623
theorem B102459 : Blo 99781 102459 := bstep (se 1 (by rfl) ⟨76844, by rfl⟩ : syracuseStep 102459 = 153689) B153689
theorem B102535 : Blo 99781 102535 := bstep (se 1 (by rfl) ⟨76901, by rfl⟩ : syracuseStep 102535 = 153803) B153803
theorem B102543 : Blo 99781 102543 := bstep (se 1 (by rfl) ⟨76907, by rfl⟩ : syracuseStep 102543 = 153815) B153815
theorem B102587 : Blo 99781 102587 := bstep (se 1 (by rfl) ⟨76940, by rfl⟩ : syracuseStep 102587 = 153881) B153881
theorem B299209 : Blo 99781 299209 := bstep (se 2 (by rfl) ⟨112203, by rfl⟩ : syracuseStep 299209 = 224407) B224407
theorem B102663 : Blo 99781 102663 := bstep (se 1 (by rfl) ⟨76997, by rfl⟩ : syracuseStep 102663 = 153995) B153995
theorem B102671 : Blo 99781 102671 := bstep (se 1 (by rfl) ⟨77003, by rfl⟩ : syracuseStep 102671 = 154007) B154007
theorem B102715 : Blo 99781 102715 := bstep (se 1 (by rfl) ⟨77036, by rfl⟩ : syracuseStep 102715 = 154073) B154073
theorem B102791 : Blo 99781 102791 := bstep (se 1 (by rfl) ⟨77093, by rfl⟩ : syracuseStep 102791 = 154187) B154187
theorem B102799 : Blo 99781 102799 := bstep (se 1 (by rfl) ⟨77099, by rfl⟩ : syracuseStep 102799 = 154199) B154199
theorem B102843 : Blo 99781 102843 := bstep (se 1 (by rfl) ⟨77132, by rfl⟩ : syracuseStep 102843 = 154265) B154265
theorem B102919 : Blo 99781 102919 := bstep (se 1 (by rfl) ⟨77189, by rfl⟩ : syracuseStep 102919 = 154379) B154379
theorem B102927 : Blo 99781 102927 := bstep (se 1 (by rfl) ⟨77195, by rfl⟩ : syracuseStep 102927 = 154391) B154391
theorem B102971 : Blo 99781 102971 := bstep (se 1 (by rfl) ⟨77228, by rfl⟩ : syracuseStep 102971 = 154457) B154457
theorem B103047 : Blo 99781 103047 := bstep (se 1 (by rfl) ⟨77285, by rfl⟩ : syracuseStep 103047 = 154571) B154571
theorem B103055 : Blo 99781 103055 := bstep (se 1 (by rfl) ⟨77291, by rfl⟩ : syracuseStep 103055 = 154583) B154583
theorem B103099 : Blo 99781 103099 := bstep (se 1 (by rfl) ⟨77324, by rfl⟩ : syracuseStep 103099 = 154649) B154649
theorem B103175 : Blo 99781 103175 := bstep (se 1 (by rfl) ⟨77381, by rfl⟩ : syracuseStep 103175 = 154763) B154763
theorem B103183 : Blo 99781 103183 := bstep (se 1 (by rfl) ⟨77387, by rfl⟩ : syracuseStep 103183 = 154775) B154775
theorem B168763 : Blo 99781 168763 := bstep (se 1 (by rfl) ⟨126572, by rfl⟩ : syracuseStep 168763 = 253145) B253145
theorem B103227 : Blo 99781 103227 := bstep (se 1 (by rfl) ⟨77420, by rfl⟩ : syracuseStep 103227 = 154841) B154841
theorem B1151819 : Blo 99781 1151819 := bstep (se 1 (by rfl) ⟨863864, by rfl⟩ : syracuseStep 1151819 = 1727729) B1727729
theorem B103303 : Blo 99781 103303 := bstep (se 1 (by rfl) ⟨77477, by rfl⟩ : syracuseStep 103303 = 154955) B154955
theorem B103311 : Blo 99781 103311 := bstep (se 1 (by rfl) ⟨77483, by rfl⟩ : syracuseStep 103311 = 154967) B154967
theorem B103355 : Blo 99781 103355 := bstep (se 1 (by rfl) ⟨77516, by rfl⟩ : syracuseStep 103355 = 155033) B155033
theorem B168905 : Blo 99781 168905 := bstep (se 2 (by rfl) ⟨63339, by rfl⟩ : syracuseStep 168905 = 126679) B126679
theorem B103431 : Blo 99781 103431 := bstep (se 1 (by rfl) ⟨77573, by rfl⟩ : syracuseStep 103431 = 155147) B155147
theorem B103439 : Blo 99781 103439 := bstep (se 1 (by rfl) ⟨77579, by rfl⟩ : syracuseStep 103439 = 155159) B155159
theorem B103483 : Blo 99781 103483 := bstep (se 1 (by rfl) ⟨77612, by rfl⟩ : syracuseStep 103483 = 155225) B155225
theorem B824381 : Blo 99781 824381 := bstep (se 3 (by rfl) ⟨154571, by rfl⟩ : syracuseStep 824381 = 309143) B309143
theorem B103559 : Blo 99781 103559 := bstep (se 1 (by rfl) ⟨77669, by rfl⟩ : syracuseStep 103559 = 155339) B155339
theorem B103567 : Blo 99781 103567 := bstep (se 1 (by rfl) ⟨77675, by rfl⟩ : syracuseStep 103567 = 155351) B155351
theorem B103611 : Blo 99781 103611 := bstep (se 1 (by rfl) ⟨77708, by rfl⟩ : syracuseStep 103611 = 155417) B155417
theorem B103687 : Blo 99781 103687 := bstep (se 1 (by rfl) ⟨77765, by rfl⟩ : syracuseStep 103687 = 155531) B155531
theorem B103695 : Blo 99781 103695 := bstep (se 1 (by rfl) ⟨77771, by rfl⟩ : syracuseStep 103695 = 155543) B155543
theorem B103739 : Blo 99781 103739 := bstep (se 1 (by rfl) ⟨77804, by rfl⟩ : syracuseStep 103739 = 155609) B155609
theorem B431507 : Blo 99781 431507 := bstep (se 1 (by rfl) ⟨323630, by rfl⟩ : syracuseStep 431507 = 647261) B647261
theorem B628235 : Blo 99781 628235 := bstep (se 1 (by rfl) ⟨471176, by rfl⟩ : syracuseStep 628235 = 942353) B942353
theorem B431659 : Blo 99781 431659 := bstep (se 1 (by rfl) ⟨323744, by rfl⟩ : syracuseStep 431659 = 647489) B647489
theorem B398915 : Blo 99781 398915 := bstep (se 1 (by rfl) ⟨299186, by rfl⟩ : syracuseStep 398915 = 598373) B598373
theorem B169607 : Blo 99781 169607 := bstep (se 1 (by rfl) ⟨127205, by rfl⟩ : syracuseStep 169607 = 254411) B254411
theorem B497441 : Blo 99781 497441 := bstep (se 2 (by rfl) ⟨186540, by rfl⟩ : syracuseStep 497441 = 373081) B373081
theorem B497497 : Blo 99781 497497 := bstep (se 2 (by rfl) ⟨186561, by rfl⟩ : syracuseStep 497497 = 373123) B373123
theorem B497611 : Blo 99781 497611 := bstep (se 1 (by rfl) ⟨373208, by rfl⟩ : syracuseStep 497611 = 746417) B746417
theorem B301067 : Blo 99781 301067 := bstep (se 1 (by rfl) ⟨225800, by rfl⟩ : syracuseStep 301067 = 451601) B451601
theorem B170255 : Blo 99781 170255 := bstep (se 1 (by rfl) ⟨127691, by rfl⟩ : syracuseStep 170255 = 255383) B255383
theorem B629309 : Blo 99781 629309 := bstep (se 3 (by rfl) ⟨117995, by rfl⟩ : syracuseStep 629309 = 235991) B235991
theorem B105095 : Blo 99781 105095 := bstep (se 1 (by rfl) ⟨78821, by rfl⟩ : syracuseStep 105095 = 157643) B157643
theorem B170795 : Blo 99781 170795 := bstep (se 1 (by rfl) ⟨128096, by rfl⟩ : syracuseStep 170795 = 256193) B256193
theorem B990103 : Blo 99781 990103 := bstep (se 1 (by rfl) ⟨742577, by rfl⟩ : syracuseStep 990103 = 1485155) B1485155
theorem B433163 : Blo 99781 433163 := bstep (se 1 (by rfl) ⟨324872, by rfl⟩ : syracuseStep 433163 = 649745) B649745
theorem B171193 : Blo 99781 171193 := bstep (se 2 (by rfl) ⟨64197, by rfl⟩ : syracuseStep 171193 = 128395) B128395
theorem B662843 : Blo 99781 662843 := bstep (se 1 (by rfl) ⟨497132, by rfl⟩ : syracuseStep 662843 = 994265) B994265
theorem B597401 : Blo 99781 597401 := bstep (se 2 (by rfl) ⟨224025, by rfl⟩ : syracuseStep 597401 = 448051) B448051
theorem B1121795 : Blo 99781 1121795 := bstep (se 1 (by rfl) ⟨841346, by rfl⟩ : syracuseStep 1121795 = 1682693) B1682693
theorem B171895 : Blo 99781 171895 := bstep (se 1 (by rfl) ⟨128921, by rfl⟩ : syracuseStep 171895 = 257843) B257843
theorem B434105 : Blo 99781 434105 := bstep (se 2 (by rfl) ⟨162789, by rfl⟩ : syracuseStep 434105 = 325579) B325579
theorem B172091 : Blo 99781 172091 := bstep (se 1 (by rfl) ⟨129068, by rfl⟩ : syracuseStep 172091 = 258137) B258137
theorem B172217 : Blo 99781 172217 := bstep (se 2 (by rfl) ⟨64581, by rfl⟩ : syracuseStep 172217 = 129163) B129163
theorem B172489 : Blo 99781 172489 := bstep (se 2 (by rfl) ⟨64683, by rfl⟩ : syracuseStep 172489 = 129367) B129367
theorem B664067 : Blo 99781 664067 := bstep (se 1 (by rfl) ⟨498050, by rfl⟩ : syracuseStep 664067 = 996101) B996101
theorem B861131 : Blo 99781 861131 := bstep (se 1 (by rfl) ⟨645848, by rfl⟩ : syracuseStep 861131 = 1291697) B1291697
theorem B173191 : Blo 99781 173191 := bstep (se 1 (by rfl) ⟨129893, by rfl⟩ : syracuseStep 173191 = 259787) B259787
theorem B271507 : Blo 99781 271507 := bstep (se 1 (by rfl) ⟨203630, by rfl⟩ : syracuseStep 271507 = 407261) B407261
theorem B664865 : Blo 99781 664865 := bstep (se 2 (by rfl) ⟨249324, by rfl⟩ : syracuseStep 664865 = 498649) B498649
theorem B337337 : Blo 99781 337337 := bstep (se 2 (by rfl) ⟨126501, by rfl⟩ : syracuseStep 337337 = 253003) B253003
theorem B1320401 : Blo 99781 1320401 := bstep (se 2 (by rfl) ⟨495150, by rfl⟩ : syracuseStep 1320401 = 990301) B990301
theorem B140987 : Blo 99781 140987 := bstep (se 1 (by rfl) ⟨105740, by rfl⟩ : syracuseStep 140987 = 211481) B211481
theorem B173839 : Blo 99781 173839 := bstep (se 1 (by rfl) ⟨130379, by rfl⟩ : syracuseStep 173839 = 260759) B260759
theorem B436103 : Blo 99781 436103 := bstep (se 1 (by rfl) ⟨327077, by rfl⟩ : syracuseStep 436103 = 654155) B654155
theorem B337931 : Blo 99781 337931 := bstep (se 1 (by rfl) ⟨253448, by rfl⟩ : syracuseStep 337931 = 506897) B506897
theorem B763991 : Blo 99781 763991 := bstep (se 1 (by rfl) ⟨572993, by rfl⟩ : syracuseStep 763991 = 1145987) B1145987
theorem B338039 : Blo 99781 338039 := bstep (se 1 (by rfl) ⟨253529, by rfl⟩ : syracuseStep 338039 = 507059) B507059
theorem B174379 : Blo 99781 174379 := bstep (se 1 (by rfl) ⟨130784, by rfl⟩ : syracuseStep 174379 = 261569) B261569
theorem B174521 : Blo 99781 174521 := bstep (se 2 (by rfl) ⟨65445, by rfl⟩ : syracuseStep 174521 = 130891) B130891
theorem B895607 : Blo 99781 895607 := bstep (se 1 (by rfl) ⟨671705, by rfl⟩ : syracuseStep 895607 = 1343411) B1343411
theorem B240263 : Blo 99781 240263 := bstep (se 1 (by rfl) ⟨180197, by rfl⟩ : syracuseStep 240263 = 360395) B360395
theorem B338633 : Blo 99781 338633 := bstep (se 2 (by rfl) ⟨126987, by rfl⟩ : syracuseStep 338633 = 253975) B253975
theorem B142087 : Blo 99781 142087 := bstep (se 1 (by rfl) ⟨106565, by rfl⟩ : syracuseStep 142087 = 213131) B213131
theorem B240907 : Blo 99781 240907 := bstep (se 1 (by rfl) ⟨180680, by rfl⟩ : syracuseStep 240907 = 361361) B361361
theorem B437537 : Blo 99781 437537 := bstep (se 2 (by rfl) ⟨164076, by rfl⟩ : syracuseStep 437537 = 328153) B328153
theorem B142651 : Blo 99781 142651 := bstep (se 1 (by rfl) ⟨106988, by rfl⟩ : syracuseStep 142651 = 213977) B213977
theorem B339335 : Blo 99781 339335 := bstep (se 1 (by rfl) ⟨254501, by rfl⟩ : syracuseStep 339335 = 509003) B509003
theorem B437879 : Blo 99781 437879 := bstep (se 1 (by rfl) ⟨328409, by rfl⟩ : syracuseStep 437879 = 656819) B656819
theorem B208585 : Blo 99781 208585 := bstep (se 2 (by rfl) ⟨78219, by rfl⟩ : syracuseStep 208585 = 156439) B156439
theorem B339713 : Blo 99781 339713 := bstep (se 2 (by rfl) ⟨127392, by rfl⟩ : syracuseStep 339713 = 254785) B254785
theorem B1093637 : Blo 99781 1093637 := bstep (se 4 (by rfl) ⟨102528, by rfl⟩ : syracuseStep 1093637 = 205057) B205057
theorem B143545 : Blo 99781 143545 := bstep (se 2 (by rfl) ⟨53829, by rfl⟩ : syracuseStep 143545 = 107659) B107659
theorem B2175245 : Blo 99781 2175245 := bstep (se 3 (by rfl) ⟨407858, by rfl⟩ : syracuseStep 2175245 = 815717) B815717
theorem B209299 : Blo 99781 209299 := bstep (se 1 (by rfl) ⟨156974, by rfl⟩ : syracuseStep 209299 = 313949) B313949
theorem B340523 : Blo 99781 340523 := bstep (se 1 (by rfl) ⟨255392, by rfl⟩ : syracuseStep 340523 = 510785) B510785
theorem B242291 : Blo 99781 242291 := bstep (se 1 (by rfl) ⟨181718, by rfl⟩ : syracuseStep 242291 = 363437) B363437
theorem B668569 : Blo 99781 668569 := bstep (se 2 (by rfl) ⟨250713, by rfl⟩ : syracuseStep 668569 = 501427) B501427
theorem B242617 : Blo 99781 242617 := bstep (se 2 (by rfl) ⟨90981, by rfl⟩ : syracuseStep 242617 = 181963) B181963
theorem B701729 : Blo 99781 701729 := bstep (se 2 (by rfl) ⟨263148, by rfl⟩ : syracuseStep 701729 = 526297) B526297
theorem B144775 : Blo 99781 144775 := bstep (se 1 (by rfl) ⟨108581, by rfl⟩ : syracuseStep 144775 = 217163) B217163
theorem B308627 : Blo 99781 308627 := bstep (se 1 (by rfl) ⟨231470, by rfl⟩ : syracuseStep 308627 = 462941) B462941
theorem B472529 : Blo 99781 472529 := bstep (se 2 (by rfl) ⟨177198, by rfl⟩ : syracuseStep 472529 = 354397) B354397
theorem B243233 : Blo 99781 243233 := bstep (se 2 (by rfl) ⟨91212, by rfl⟩ : syracuseStep 243233 = 182425) B182425
theorem B112315 : Blo 99781 112315 := bstep (se 1 (by rfl) ⟨84236, by rfl⟩ : syracuseStep 112315 = 168473) B168473
theorem B505601 : Blo 99781 505601 := bstep (se 2 (by rfl) ⟨189600, by rfl⟩ : syracuseStep 505601 = 379201) B379201
theorem B1226497 : Blo 99781 1226497 := bstep (se 2 (by rfl) ⟨459936, by rfl⟩ : syracuseStep 1226497 = 919873) B919873
theorem B341819 : Blo 99781 341819 := bstep (se 1 (by rfl) ⟨256364, by rfl⟩ : syracuseStep 341819 = 512729) B512729
theorem B702361 : Blo 99781 702361 := bstep (se 2 (by rfl) ⟨263385, by rfl⟩ : syracuseStep 702361 = 526771) B526771
theorem B145481 : Blo 99781 145481 := bstep (se 2 (by rfl) ⟨54555, by rfl⟩ : syracuseStep 145481 = 109111) B109111
theorem B440407 : Blo 99781 440407 := bstep (se 1 (by rfl) ⟨330305, by rfl⟩ : syracuseStep 440407 = 660611) B660611
theorem B243847 : Blo 99781 243847 := bstep (se 1 (by rfl) ⟨182885, by rfl⟩ : syracuseStep 243847 = 365771) B365771
theorem B112783 : Blo 99781 112783 := bstep (se 1 (by rfl) ⟨84587, by rfl⟩ : syracuseStep 112783 = 169175) B169175
theorem B145595 : Blo 99781 145595 := bstep (se 1 (by rfl) ⟨109196, by rfl⟩ : syracuseStep 145595 = 218393) B218393
theorem B342305 : Blo 99781 342305 := bstep (se 2 (by rfl) ⟨128364, by rfl⟩ : syracuseStep 342305 = 256729) B256729
theorem B703019 : Blo 99781 703019 := bstep (se 1 (by rfl) ⟨527264, by rfl⟩ : syracuseStep 703019 = 1054529) B1054529
theorem B506411 : Blo 99781 506411 := bstep (se 1 (by rfl) ⟨379808, by rfl⟩ : syracuseStep 506411 = 759617) B759617
theorem B113287 : Blo 99781 113287 := bstep (se 1 (by rfl) ⟨84965, by rfl⟩ : syracuseStep 113287 = 169931) B169931
theorem B146233 : Blo 99781 146233 := bstep (se 2 (by rfl) ⟨54837, by rfl⟩ : syracuseStep 146233 = 109675) B109675
theorem B113467 : Blo 99781 113467 := bstep (se 1 (by rfl) ⟨85100, by rfl⟩ : syracuseStep 113467 = 170201) B170201
theorem B342899 : Blo 99781 342899 := bstep (se 1 (by rfl) ⟨257174, by rfl⟩ : syracuseStep 342899 = 514349) B514349
theorem B113935 : Blo 99781 113935 := bstep (se 1 (by rfl) ⟨85451, by rfl⟩ : syracuseStep 113935 = 170903) B170903
theorem B834875 : Blo 99781 834875 := bstep (se 1 (by rfl) ⟨626156, by rfl⟩ : syracuseStep 834875 = 1252313) B1252313
theorem B114439 : Blo 99781 114439 := bstep (se 1 (by rfl) ⟨85829, by rfl⟩ : syracuseStep 114439 = 171659) B171659
theorem B507707 : Blo 99781 507707 := bstep (se 1 (by rfl) ⟨380780, by rfl⟩ : syracuseStep 507707 = 761561) B761561
theorem B114619 : Blo 99781 114619 := bstep (se 1 (by rfl) ⟨85964, by rfl⟩ : syracuseStep 114619 = 171929) B171929
theorem B507869 : Blo 99781 507869 := bstep (se 3 (by rfl) ⟨95225, by rfl⟩ : syracuseStep 507869 = 190451) B190451
theorem B508193 : Blo 99781 508193 := bstep (se 2 (by rfl) ⟨190572, by rfl⟩ : syracuseStep 508193 = 381145) B381145
theorem B115087 : Blo 99781 115087 := bstep (se 1 (by rfl) ⟨86315, by rfl⟩ : syracuseStep 115087 = 172631) B172631
theorem B573905 : Blo 99781 573905 := bstep (se 2 (by rfl) ⟨215214, by rfl⟩ : syracuseStep 573905 = 430429) B430429
theorem B246539 : Blo 99781 246539 := bstep (se 1 (by rfl) ⟨184904, by rfl⟩ : syracuseStep 246539 = 369809) B369809
theorem B115591 : Blo 99781 115591 := bstep (se 1 (by rfl) ⟨86693, by rfl⟩ : syracuseStep 115591 = 173387) B173387
theorem B607121 : Blo 99781 607121 := bstep (se 2 (by rfl) ⟨227670, by rfl⟩ : syracuseStep 607121 = 455341) B455341
theorem B574361 : Blo 99781 574361 := bstep (se 2 (by rfl) ⟨215385, by rfl⟩ : syracuseStep 574361 = 430771) B430771
theorem B3195875 : Blo 99781 3195875 := bstep (se 1 (by rfl) ⟨2396906, by rfl⟩ : syracuseStep 3195875 = 4793813) B4793813
theorem B246827 : Blo 99781 246827 := bstep (se 1 (by rfl) ⟨185120, by rfl⟩ : syracuseStep 246827 = 370241) B370241
theorem B115771 : Blo 99781 115771 := bstep (se 1 (by rfl) ⟨86828, by rfl⟩ : syracuseStep 115771 = 173657) B173657
theorem B509165 : Blo 99781 509165 := bstep (se 3 (by rfl) ⟨95468, by rfl⟩ : syracuseStep 509165 = 190937) B190937
theorem B345491 : Blo 99781 345491 := bstep (se 1 (by rfl) ⟨259118, by rfl⟩ : syracuseStep 345491 = 518237) B518237
theorem B116239 : Blo 99781 116239 := bstep (se 1 (by rfl) ⟨87179, by rfl⟩ : syracuseStep 116239 = 174359) B174359
theorem B542497 : Blo 99781 542497 := bstep (se 2 (by rfl) ⟨203436, by rfl⟩ : syracuseStep 542497 = 406873) B406873
theorem B116743 : Blo 99781 116743 := bstep (se 1 (by rfl) ⟨87557, by rfl⟩ : syracuseStep 116743 = 175115) B175115
theorem B509975 : Blo 99781 509975 := bstep (se 1 (by rfl) ⟨382481, by rfl⟩ : syracuseStep 509975 = 764963) B764963
theorem B313463 : Blo 99781 313463 := bstep (se 1 (by rfl) ⟨235097, by rfl⟩ : syracuseStep 313463 = 470195) B470195
theorem B247961 : Blo 99781 247961 := bstep (se 2 (by rfl) ⟨92985, by rfl⟩ : syracuseStep 247961 = 185971) B185971
theorem B149675 : Blo 99781 149675 := bstep (se 1 (by rfl) ⟨112256, by rfl⟩ : syracuseStep 149675 = 224513) B224513
theorem B149705 : Blo 99781 149705 := bstep (se 2 (by rfl) ⟨56139, by rfl⟩ : syracuseStep 149705 = 112279) B112279
theorem B149819 : Blo 99781 149819 := bstep (se 1 (by rfl) ⟨112364, by rfl⟩ : syracuseStep 149819 = 224729) B224729
theorem B149879 : Blo 99781 149879 := bstep (se 1 (by rfl) ⟨112409, by rfl⟩ : syracuseStep 149879 = 224819) B224819
theorem B149903 : Blo 99781 149903 := bstep (se 1 (by rfl) ⟨112427, by rfl⟩ : syracuseStep 149903 = 224855) B224855
theorem B149945 : Blo 99781 149945 := bstep (se 2 (by rfl) ⟨56229, by rfl⟩ : syracuseStep 149945 = 112459) B112459
theorem B608771 : Blo 99781 608771 := bstep (se 1 (by rfl) ⟨456578, by rfl⟩ : syracuseStep 608771 = 913157) B913157
theorem B150023 : Blo 99781 150023 := bstep (se 1 (by rfl) ⟨112517, by rfl⟩ : syracuseStep 150023 = 225035) B225035
theorem B150059 : Blo 99781 150059 := bstep (se 1 (by rfl) ⟨112544, by rfl⟩ : syracuseStep 150059 = 225089) B225089
theorem B150089 : Blo 99781 150089 := bstep (se 2 (by rfl) ⟨56283, by rfl⟩ : syracuseStep 150089 = 112567) B112567
theorem B150203 : Blo 99781 150203 := bstep (se 1 (by rfl) ⟨112652, by rfl⟩ : syracuseStep 150203 = 225305) B225305
theorem B9358037 : Blo 99781 9358037 := bstep (se 7 (by rfl) ⟨109664, by rfl⟩ : syracuseStep 9358037 = 219329) B219329
theorem B150263 : Blo 99781 150263 := bstep (se 1 (by rfl) ⟨112697, by rfl⟩ : syracuseStep 150263 = 225395) B225395
theorem B150287 : Blo 99781 150287 := bstep (se 1 (by rfl) ⟨112715, by rfl⟩ : syracuseStep 150287 = 225431) B225431
theorem B346895 : Blo 99781 346895 := bstep (se 1 (by rfl) ⟨260171, by rfl⟩ : syracuseStep 346895 = 520343) B520343
theorem B150329 : Blo 99781 150329 := bstep (se 2 (by rfl) ⟨56373, by rfl⟩ : syracuseStep 150329 = 112747) B112747
theorem B150407 : Blo 99781 150407 := bstep (se 1 (by rfl) ⟨112805, by rfl⟩ : syracuseStep 150407 = 225611) B225611
theorem B150443 : Blo 99781 150443 := bstep (se 1 (by rfl) ⟨112832, by rfl⟩ : syracuseStep 150443 = 225665) B225665
theorem B150473 : Blo 99781 150473 := bstep (se 2 (by rfl) ⟨56427, by rfl⟩ : syracuseStep 150473 = 112855) B112855
theorem B347165 : Blo 99781 347165 := bstep (se 3 (by rfl) ⟨65093, by rfl⟩ : syracuseStep 347165 = 130187) B130187
theorem B150587 : Blo 99781 150587 := bstep (se 1 (by rfl) ⟨112940, by rfl⟩ : syracuseStep 150587 = 225881) B225881
theorem B379991 : Blo 99781 379991 := bstep (se 1 (by rfl) ⟨284993, by rfl⟩ : syracuseStep 379991 = 569987) B569987
theorem B150647 : Blo 99781 150647 := bstep (se 1 (by rfl) ⟨112985, by rfl⟩ : syracuseStep 150647 = 225971) B225971
theorem B150671 : Blo 99781 150671 := bstep (se 1 (by rfl) ⟨113003, by rfl⟩ : syracuseStep 150671 = 226007) B226007
theorem B150713 : Blo 99781 150713 := bstep (se 2 (by rfl) ⟨56517, by rfl⟩ : syracuseStep 150713 = 113035) B113035
theorem B150791 : Blo 99781 150791 := bstep (se 1 (by rfl) ⟨113093, by rfl⟩ : syracuseStep 150791 = 226187) B226187
theorem B609551 : Blo 99781 609551 := bstep (se 1 (by rfl) ⟨457163, by rfl⟩ : syracuseStep 609551 = 914327) B914327
theorem B150827 : Blo 99781 150827 := bstep (se 1 (by rfl) ⟨113120, by rfl⟩ : syracuseStep 150827 = 226241) B226241
theorem B150857 : Blo 99781 150857 := bstep (se 2 (by rfl) ⟨56571, by rfl⟩ : syracuseStep 150857 = 113143) B113143
theorem B1887623 : Blo 99781 1887623 := bstep (se 1 (by rfl) ⟨1415717, by rfl⟩ : syracuseStep 1887623 = 2831435) B2831435
theorem B413113 : Blo 99781 413113 := bstep (se 2 (by rfl) ⟨154917, by rfl⟩ : syracuseStep 413113 = 309835) B309835
theorem B150971 : Blo 99781 150971 := bstep (se 1 (by rfl) ⟨113228, by rfl⟩ : syracuseStep 150971 = 226457) B226457
theorem B1953233 : Blo 99781 1953233 := bstep (se 2 (by rfl) ⟨732462, by rfl⟩ : syracuseStep 1953233 = 1464925) B1464925
theorem B151031 : Blo 99781 151031 := bstep (se 1 (by rfl) ⟨113273, by rfl⟩ : syracuseStep 151031 = 226547) B226547
theorem B151055 : Blo 99781 151055 := bstep (se 1 (by rfl) ⟨113291, by rfl⟩ : syracuseStep 151055 = 226583) B226583
theorem B151097 : Blo 99781 151097 := bstep (se 2 (by rfl) ⟨56661, by rfl⟩ : syracuseStep 151097 = 113323) B113323
theorem B380477 : Blo 99781 380477 := bstep (se 3 (by rfl) ⟨71339, by rfl⟩ : syracuseStep 380477 = 142679) B142679
theorem B151175 : Blo 99781 151175 := bstep (se 1 (by rfl) ⟨113381, by rfl⟩ : syracuseStep 151175 = 226763) B226763
theorem B151211 : Blo 99781 151211 := bstep (se 1 (by rfl) ⟨113408, by rfl⟩ : syracuseStep 151211 = 226817) B226817
theorem B151241 : Blo 99781 151241 := bstep (se 2 (by rfl) ⟨56715, by rfl⟩ : syracuseStep 151241 = 113431) B113431
theorem B216847 : Blo 99781 216847 := bstep (se 1 (by rfl) ⟨162635, by rfl⟩ : syracuseStep 216847 = 325271) B325271
theorem B151355 : Blo 99781 151355 := bstep (se 1 (by rfl) ⟨113516, by rfl⟩ : syracuseStep 151355 = 227033) B227033
theorem B151415 : Blo 99781 151415 := bstep (se 1 (by rfl) ⟨113561, by rfl⟩ : syracuseStep 151415 = 227123) B227123
theorem B151439 : Blo 99781 151439 := bstep (se 1 (by rfl) ⟨113579, by rfl⟩ : syracuseStep 151439 = 227159) B227159
theorem B151481 : Blo 99781 151481 := bstep (se 2 (by rfl) ⟨56805, by rfl⟩ : syracuseStep 151481 = 113611) B113611
theorem B151559 : Blo 99781 151559 := bstep (se 1 (by rfl) ⟨113669, by rfl⟩ : syracuseStep 151559 = 227339) B227339
theorem B610327 : Blo 99781 610327 := bstep (se 1 (by rfl) ⟨457745, by rfl⟩ : syracuseStep 610327 = 915491) B915491
theorem B151595 : Blo 99781 151595 := bstep (se 1 (by rfl) ⟨113696, by rfl⟩ : syracuseStep 151595 = 227393) B227393
theorem B151625 : Blo 99781 151625 := bstep (se 2 (by rfl) ⟨56859, by rfl⟩ : syracuseStep 151625 = 113719) B113719
theorem B151739 : Blo 99781 151739 := bstep (se 1 (by rfl) ⟨113804, by rfl⟩ : syracuseStep 151739 = 227609) B227609
theorem B151799 : Blo 99781 151799 := bstep (se 1 (by rfl) ⟨113849, by rfl⟩ : syracuseStep 151799 = 227699) B227699
theorem B151823 : Blo 99781 151823 := bstep (se 1 (by rfl) ⟨113867, by rfl⟩ : syracuseStep 151823 = 227735) B227735
theorem B151865 : Blo 99781 151865 := bstep (se 2 (by rfl) ⟨56949, by rfl⟩ : syracuseStep 151865 = 113899) B113899
theorem B151943 : Blo 99781 151943 := bstep (se 1 (by rfl) ⟨113957, by rfl⟩ : syracuseStep 151943 = 227915) B227915
theorem B348569 : Blo 99781 348569 := bstep (se 2 (by rfl) ⟨130713, by rfl⟩ : syracuseStep 348569 = 261427) B261427
theorem B151979 : Blo 99781 151979 := bstep (se 1 (by rfl) ⟨113984, by rfl⟩ : syracuseStep 151979 = 227969) B227969
theorem B152009 : Blo 99781 152009 := bstep (se 2 (by rfl) ⟨57003, by rfl⟩ : syracuseStep 152009 = 114007) B114007
theorem B479773 : Blo 99781 479773 := bstep (se 3 (by rfl) ⟨89957, by rfl⟩ : syracuseStep 479773 = 179915) B179915
theorem B152123 : Blo 99781 152123 := bstep (se 1 (by rfl) ⟨114092, by rfl⟩ : syracuseStep 152123 = 228185) B228185
theorem B152183 : Blo 99781 152183 := bstep (se 1 (by rfl) ⟨114137, by rfl⟩ : syracuseStep 152183 = 228275) B228275
theorem B152207 : Blo 99781 152207 := bstep (se 1 (by rfl) ⟨114155, by rfl⟩ : syracuseStep 152207 = 228311) B228311
theorem B152249 : Blo 99781 152249 := bstep (se 2 (by rfl) ⟨57093, by rfl⟩ : syracuseStep 152249 = 114187) B114187
theorem B152327 : Blo 99781 152327 := bstep (se 1 (by rfl) ⟨114245, by rfl⟩ : syracuseStep 152327 = 228491) B228491
theorem B152363 : Blo 99781 152363 := bstep (se 1 (by rfl) ⟨114272, by rfl⟩ : syracuseStep 152363 = 228545) B228545
theorem B152393 : Blo 99781 152393 := bstep (se 2 (by rfl) ⟨57147, by rfl⟩ : syracuseStep 152393 = 114295) B114295
theorem B152507 : Blo 99781 152507 := bstep (se 1 (by rfl) ⟨114380, by rfl⟩ : syracuseStep 152507 = 228761) B228761
theorem B381905 : Blo 99781 381905 := bstep (se 2 (by rfl) ⟨143214, by rfl⟩ : syracuseStep 381905 = 286429) B286429
theorem B152567 : Blo 99781 152567 := bstep (se 1 (by rfl) ⟨114425, by rfl⟩ : syracuseStep 152567 = 228851) B228851
theorem B152591 : Blo 99781 152591 := bstep (se 1 (by rfl) ⟨114443, by rfl⟩ : syracuseStep 152591 = 228887) B228887
theorem B513053 : Blo 99781 513053 := bstep (se 3 (by rfl) ⟨96197, by rfl⟩ : syracuseStep 513053 = 192395) B192395
theorem B152633 : Blo 99781 152633 := bstep (se 2 (by rfl) ⟨57237, by rfl⟩ : syracuseStep 152633 = 114475) B114475
theorem B349271 : Blo 99781 349271 := bstep (se 1 (by rfl) ⟨261953, by rfl⟩ : syracuseStep 349271 = 523907) B523907
theorem B152711 : Blo 99781 152711 := bstep (se 1 (by rfl) ⟨114533, by rfl⟩ : syracuseStep 152711 = 229067) B229067
theorem B152747 : Blo 99781 152747 := bstep (se 1 (by rfl) ⟨114560, by rfl⟩ : syracuseStep 152747 = 229121) B229121
theorem B152777 : Blo 99781 152777 := bstep (se 2 (by rfl) ⟨57291, by rfl⟩ : syracuseStep 152777 = 114583) B114583
theorem B120055 : Blo 99781 120055 := bstep (se 1 (by rfl) ⟨90041, by rfl⟩ : syracuseStep 120055 = 180083) B180083
theorem B152891 : Blo 99781 152891 := bstep (se 1 (by rfl) ⟨114668, by rfl⟩ : syracuseStep 152891 = 229337) B229337
theorem B152951 : Blo 99781 152951 := bstep (se 1 (by rfl) ⟨114713, by rfl⟩ : syracuseStep 152951 = 229427) B229427
theorem B152975 : Blo 99781 152975 := bstep (se 1 (by rfl) ⟨114731, by rfl⟩ : syracuseStep 152975 = 229463) B229463
theorem B153017 : Blo 99781 153017 := bstep (se 2 (by rfl) ⟨57381, by rfl⟩ : syracuseStep 153017 = 114763) B114763
theorem B513539 : Blo 99781 513539 := bstep (se 1 (by rfl) ⟨385154, by rfl⟩ : syracuseStep 513539 = 770309) B770309
theorem B153095 : Blo 99781 153095 := bstep (se 1 (by rfl) ⟨114821, by rfl⟩ : syracuseStep 153095 = 229643) B229643
theorem B153131 : Blo 99781 153131 := bstep (se 1 (by rfl) ⟨114848, by rfl⟩ : syracuseStep 153131 = 229697) B229697
theorem B284219 : Blo 99781 284219 := bstep (se 1 (by rfl) ⟨213164, by rfl⟩ : syracuseStep 284219 = 426329) B426329
theorem B349757 : Blo 99781 349757 := bstep (se 3 (by rfl) ⟨65579, by rfl⟩ : syracuseStep 349757 = 131159) B131159
theorem B153161 : Blo 99781 153161 := bstep (se 2 (by rfl) ⟨57435, by rfl⟩ : syracuseStep 153161 = 114871) B114871
theorem B153275 : Blo 99781 153275 := bstep (se 1 (by rfl) ⟨114956, by rfl⟩ : syracuseStep 153275 = 229913) B229913
theorem B153335 : Blo 99781 153335 := bstep (se 1 (by rfl) ⟨115001, by rfl⟩ : syracuseStep 153335 = 230003) B230003
theorem B153359 : Blo 99781 153359 := bstep (se 1 (by rfl) ⟨115019, by rfl⟩ : syracuseStep 153359 = 230039) B230039
theorem B153401 : Blo 99781 153401 := bstep (se 2 (by rfl) ⟨57525, by rfl⟩ : syracuseStep 153401 = 115051) B115051
theorem B153479 : Blo 99781 153479 := bstep (se 1 (by rfl) ⟨115109, by rfl⟩ : syracuseStep 153479 = 230219) B230219
theorem B1169315 : Blo 99781 1169315 := bstep (se 1 (by rfl) ⟨876986, by rfl⟩ : syracuseStep 1169315 = 1753973) B1753973
theorem B153515 : Blo 99781 153515 := bstep (se 1 (by rfl) ⟨115136, by rfl⟩ : syracuseStep 153515 = 230273) B230273
theorem B153545 : Blo 99781 153545 := bstep (se 2 (by rfl) ⟨57579, by rfl⟩ : syracuseStep 153545 = 115159) B115159
theorem B219179 : Blo 99781 219179 := bstep (se 1 (by rfl) ⟨164384, by rfl⟩ : syracuseStep 219179 = 328769) B328769
theorem B153659 : Blo 99781 153659 := bstep (se 1 (by rfl) ⟨115244, by rfl⟩ : syracuseStep 153659 = 230489) B230489
theorem B153719 : Blo 99781 153719 := bstep (se 1 (by rfl) ⟨115289, by rfl⟩ : syracuseStep 153719 = 230579) B230579
theorem B153743 : Blo 99781 153743 := bstep (se 1 (by rfl) ⟨115307, by rfl⟩ : syracuseStep 153743 = 230615) B230615
theorem B153785 : Blo 99781 153785 := bstep (se 2 (by rfl) ⟨57669, by rfl⟩ : syracuseStep 153785 = 115339) B115339
theorem B153863 : Blo 99781 153863 := bstep (se 1 (by rfl) ⟨115397, by rfl⟩ : syracuseStep 153863 = 230795) B230795
theorem B284971 : Blo 99781 284971 := bstep (se 1 (by rfl) ⟨213728, by rfl⟩ : syracuseStep 284971 = 427457) B427457
theorem B153899 : Blo 99781 153899 := bstep (se 1 (by rfl) ⟨115424, by rfl⟩ : syracuseStep 153899 = 230849) B230849
theorem B153929 : Blo 99781 153929 := bstep (se 2 (by rfl) ⟨57723, by rfl⟩ : syracuseStep 153929 = 115447) B115447
theorem B154043 : Blo 99781 154043 := bstep (se 1 (by rfl) ⟨115532, by rfl⟩ : syracuseStep 154043 = 231065) B231065
theorem B154103 : Blo 99781 154103 := bstep (se 1 (by rfl) ⟨115577, by rfl⟩ : syracuseStep 154103 = 231155) B231155
theorem B154127 : Blo 99781 154127 := bstep (se 1 (by rfl) ⟨115595, by rfl⟩ : syracuseStep 154127 = 231191) B231191
theorem B2382371 : Blo 99781 2382371 := bstep (se 1 (by rfl) ⟨1786778, by rfl⟩ : syracuseStep 2382371 = 3573557) B3573557
theorem B186923 : Blo 99781 186923 := bstep (se 1 (by rfl) ⟨140192, by rfl⟩ : syracuseStep 186923 = 280385) B280385
theorem B154169 : Blo 99781 154169 := bstep (se 2 (by rfl) ⟨57813, by rfl⟩ : syracuseStep 154169 = 115627) B115627
theorem B285245 : Blo 99781 285245 := bstep (se 3 (by rfl) ⟨53483, by rfl⟩ : syracuseStep 285245 = 106967) B106967
theorem B383575 : Blo 99781 383575 := bstep (se 1 (by rfl) ⟨287681, by rfl⟩ : syracuseStep 383575 = 575363) B575363
theorem B154247 : Blo 99781 154247 := bstep (se 1 (by rfl) ⟨115685, by rfl⟩ : syracuseStep 154247 = 231371) B231371
theorem B154283 : Blo 99781 154283 := bstep (se 1 (by rfl) ⟨115712, by rfl⟩ : syracuseStep 154283 = 231425) B231425
theorem B154313 : Blo 99781 154313 := bstep (se 2 (by rfl) ⟨57867, by rfl⟩ : syracuseStep 154313 = 115735) B115735
theorem B154427 : Blo 99781 154427 := bstep (se 1 (by rfl) ⟨115820, by rfl⟩ : syracuseStep 154427 = 231641) B231641
theorem B252791 : Blo 99781 252791 := bstep (se 1 (by rfl) ⟨189593, by rfl⟩ : syracuseStep 252791 = 379187) B379187
theorem B154487 : Blo 99781 154487 := bstep (se 1 (by rfl) ⟨115865, by rfl⟩ : syracuseStep 154487 = 231731) B231731
theorem B383879 : Blo 99781 383879 := bstep (se 1 (by rfl) ⟨287909, by rfl⟩ : syracuseStep 383879 = 575819) B575819
theorem B154511 : Blo 99781 154511 := bstep (se 1 (by rfl) ⟨115883, by rfl⟩ : syracuseStep 154511 = 231767) B231767
theorem B777113 : Blo 99781 777113 := bstep (se 2 (by rfl) ⟨291417, by rfl⟩ : syracuseStep 777113 = 582835) B582835
theorem B154553 : Blo 99781 154553 := bstep (se 2 (by rfl) ⟨57957, by rfl⟩ : syracuseStep 154553 = 115915) B115915
theorem B154631 : Blo 99781 154631 := bstep (se 1 (by rfl) ⟨115973, by rfl⟩ : syracuseStep 154631 = 231947) B231947
theorem B154639 : Blo 99781 154639 := bstep (se 1 (by rfl) ⟨115979, by rfl⟩ : syracuseStep 154639 = 231959) B231959
theorem B154667 : Blo 99781 154667 := bstep (se 1 (by rfl) ⟨116000, by rfl⟩ : syracuseStep 154667 = 232001) B232001
theorem B384061 : Blo 99781 384061 := bstep (se 3 (by rfl) ⟨72011, by rfl⟩ : syracuseStep 384061 = 144023) B144023
theorem B154697 : Blo 99781 154697 := bstep (se 2 (by rfl) ⟨58011, by rfl⟩ : syracuseStep 154697 = 116023) B116023
theorem B515159 : Blo 99781 515159 := bstep (se 1 (by rfl) ⟨386369, by rfl⟩ : syracuseStep 515159 = 772739) B772739
theorem B121991 : Blo 99781 121991 := bstep (se 1 (by rfl) ⟨91493, by rfl⟩ : syracuseStep 121991 = 182987) B182987
theorem B154811 : Blo 99781 154811 := bstep (se 1 (by rfl) ⟨116108, by rfl⟩ : syracuseStep 154811 = 232217) B232217
theorem B154871 : Blo 99781 154871 := bstep (se 1 (by rfl) ⟨116153, by rfl⟩ : syracuseStep 154871 = 232307) B232307
theorem B154895 : Blo 99781 154895 := bstep (se 1 (by rfl) ⟨116171, by rfl⟩ : syracuseStep 154895 = 232343) B232343
theorem B154937 : Blo 99781 154937 := bstep (se 2 (by rfl) ⟨58101, by rfl⟩ : syracuseStep 154937 = 116203) B116203
theorem B286087 : Blo 99781 286087 := bstep (se 1 (by rfl) ⟨214565, by rfl⟩ : syracuseStep 286087 = 429131) B429131
theorem B155015 : Blo 99781 155015 := bstep (se 1 (by rfl) ⟨116261, by rfl⟩ : syracuseStep 155015 = 232523) B232523
theorem B155051 : Blo 99781 155051 := bstep (se 1 (by rfl) ⟨116288, by rfl⟩ : syracuseStep 155051 = 232577) B232577
theorem B155081 : Blo 99781 155081 := bstep (se 2 (by rfl) ⟨58155, by rfl⟩ : syracuseStep 155081 = 116311) B116311
theorem B155195 : Blo 99781 155195 := bstep (se 1 (by rfl) ⟨116396, by rfl⟩ : syracuseStep 155195 = 232793) B232793
theorem B515645 : Blo 99781 515645 := bstep (se 3 (by rfl) ⟨96683, by rfl⟩ : syracuseStep 515645 = 193367) B193367
theorem B155255 : Blo 99781 155255 := bstep (se 1 (by rfl) ⟨116441, by rfl⟩ : syracuseStep 155255 = 232883) B232883
theorem B155279 : Blo 99781 155279 := bstep (se 1 (by rfl) ⟨116459, by rfl⟩ : syracuseStep 155279 = 232919) B232919
theorem B220819 : Blo 99781 220819 := bstep (se 1 (by rfl) ⟨165614, by rfl⟩ : syracuseStep 220819 = 331229) B331229
theorem B286361 : Blo 99781 286361 := bstep (se 2 (by rfl) ⟨107385, by rfl⟩ : syracuseStep 286361 = 214771) B214771
theorem B122539 : Blo 99781 122539 := bstep (se 1 (by rfl) ⟨91904, by rfl⟩ : syracuseStep 122539 = 183809) B183809
theorem B155321 : Blo 99781 155321 := bstep (se 2 (by rfl) ⟨58245, by rfl⟩ : syracuseStep 155321 = 116491) B116491
theorem B581377 : Blo 99781 581377 := bstep (se 2 (by rfl) ⟨218016, by rfl⟩ : syracuseStep 581377 = 436033) B436033
theorem B155399 : Blo 99781 155399 := bstep (se 1 (by rfl) ⟨116549, by rfl⟩ : syracuseStep 155399 = 233099) B233099
theorem B155435 : Blo 99781 155435 := bstep (se 1 (by rfl) ⟨116576, by rfl⟩ : syracuseStep 155435 = 233153) B233153
theorem B122683 : Blo 99781 122683 := bstep (se 1 (by rfl) ⟨92012, by rfl⟩ : syracuseStep 122683 = 184025) B184025
theorem B155465 : Blo 99781 155465 := bstep (se 2 (by rfl) ⟨58299, by rfl⟩ : syracuseStep 155465 = 116599) B116599
theorem B745379 : Blo 99781 745379 := bstep (se 1 (by rfl) ⟨559034, by rfl⟩ : syracuseStep 745379 = 1118069) B1118069
theorem B155579 : Blo 99781 155579 := bstep (se 1 (by rfl) ⟨116684, by rfl⟩ : syracuseStep 155579 = 233369) B233369
theorem B155639 : Blo 99781 155639 := bstep (se 1 (by rfl) ⟨116729, by rfl⟩ : syracuseStep 155639 = 233459) B233459
theorem B155663 : Blo 99781 155663 := bstep (se 1 (by rfl) ⟨116747, by rfl⟩ : syracuseStep 155663 = 233495) B233495
theorem B254087 : Blo 99781 254087 := bstep (se 1 (by rfl) ⟨190565, by rfl⟩ : syracuseStep 254087 = 381131) B381131
theorem B254137 : Blo 99781 254137 := bstep (se 2 (by rfl) ⟨95301, by rfl⟩ : syracuseStep 254137 = 190603) B190603
theorem B581903 : Blo 99781 581903 := bstep (se 1 (by rfl) ⟨436427, by rfl⟩ : syracuseStep 581903 = 872855) B872855
theorem B549179 : Blo 99781 549179 := bstep (se 1 (by rfl) ⟨411884, by rfl⟩ : syracuseStep 549179 = 823769) B823769
theorem B516611 : Blo 99781 516611 := bstep (se 1 (by rfl) ⟨387458, by rfl⟩ : syracuseStep 516611 = 774917) B774917
theorem B647747 : Blo 99781 647747 := bstep (se 1 (by rfl) ⟨485810, by rfl⟩ : syracuseStep 647747 = 971621) B971621
theorem B221843 : Blo 99781 221843 := bstep (se 1 (by rfl) ⟨166382, by rfl⟩ : syracuseStep 221843 = 332765) B332765
theorem B975539 : Blo 99781 975539 := bstep (se 1 (by rfl) ⟨731654, by rfl⟩ : syracuseStep 975539 = 1463309) B1463309
theorem B287489 : Blo 99781 287489 := bstep (se 2 (by rfl) ⟨107808, by rfl⟩ : syracuseStep 287489 = 215617) B215617
theorem B385793 : Blo 99781 385793 := bstep (se 2 (by rfl) ⟨144672, by rfl⟩ : syracuseStep 385793 = 289345) B289345
theorem B254735 : Blo 99781 254735 := bstep (se 1 (by rfl) ⟨191051, by rfl⟩ : syracuseStep 254735 = 382103) B382103
theorem B779057 : Blo 99781 779057 := bstep (se 2 (by rfl) ⟨292146, by rfl⟩ : syracuseStep 779057 = 584293) B584293
theorem B287945 : Blo 99781 287945 := bstep (se 2 (by rfl) ⟨107979, by rfl⟩ : syracuseStep 287945 = 215959) B215959
theorem B517427 : Blo 99781 517427 := bstep (se 1 (by rfl) ⟨388070, by rfl⟩ : syracuseStep 517427 = 776141) B776141
theorem B255433 : Blo 99781 255433 := bstep (se 2 (by rfl) ⟨95787, by rfl⟩ : syracuseStep 255433 = 191575) B191575
theorem B255575 : Blo 99781 255575 := bstep (se 1 (by rfl) ⟨191681, by rfl⟩ : syracuseStep 255575 = 383363) B383363
theorem B517751 : Blo 99781 517751 := bstep (se 1 (by rfl) ⟨388313, by rfl⟩ : syracuseStep 517751 = 776627) B776627
theorem B583361 : Blo 99781 583361 := bstep (se 2 (by rfl) ⟨218760, by rfl⟩ : syracuseStep 583361 = 437521) B437521
theorem B386963 : Blo 99781 386963 := bstep (se 1 (by rfl) ⟨290222, by rfl⟩ : syracuseStep 386963 = 580445) B580445
theorem B1992599 : Blo 99781 1992599 := bstep (se 1 (by rfl) ⟨1494449, by rfl⟩ : syracuseStep 1992599 = 2988899) B2988899
theorem B2189429 : Blo 99781 2189429 := bstep (se 5 (by rfl) ⟨102629, by rfl⟩ : syracuseStep 2189429 = 205259) B205259
theorem B190649 : Blo 99781 190649 := bstep (se 2 (by rfl) ⟨71493, by rfl⟩ : syracuseStep 190649 = 142987) B142987
theorem B387463 : Blo 99781 387463 := bstep (se 1 (by rfl) ⟨290597, by rfl⟩ : syracuseStep 387463 = 581195) B581195
theorem B190991 : Blo 99781 190991 := bstep (se 1 (by rfl) ⟨143243, by rfl⟩ : syracuseStep 190991 = 286487) B286487
theorem B289295 : Blo 99781 289295 := bstep (se 1 (by rfl) ⟨216971, by rfl⟩ : syracuseStep 289295 = 433943) B433943
theorem B518723 : Blo 99781 518723 := bstep (se 1 (by rfl) ⟨389042, by rfl⟩ : syracuseStep 518723 = 778085) B778085
theorem B289595 : Blo 99781 289595 := bstep (se 1 (by rfl) ⟨217196, by rfl⟩ : syracuseStep 289595 = 434393) B434393
theorem B486233 : Blo 99781 486233 := bstep (se 2 (by rfl) ⟨182337, by rfl⟩ : syracuseStep 486233 = 364675) B364675
theorem B519047 : Blo 99781 519047 := bstep (se 1 (by rfl) ⟨389285, by rfl⟩ : syracuseStep 519047 = 778571) B778571
theorem B191803 : Blo 99781 191803 := bstep (se 1 (by rfl) ⟨143852, by rfl⟩ : syracuseStep 191803 = 287705) B287705
theorem B191879 : Blo 99781 191879 := bstep (se 1 (by rfl) ⟨143909, by rfl⟩ : syracuseStep 191879 = 287819) B287819
theorem B290233 : Blo 99781 290233 := bstep (se 2 (by rfl) ⟨108837, by rfl⟩ : syracuseStep 290233 = 217675) B217675
theorem B224783 : Blo 99781 224783 := bstep (se 1 (by rfl) ⟨168587, by rfl⟩ : syracuseStep 224783 = 337175) B337175
theorem B224801 : Blo 99781 224801 := bstep (se 2 (by rfl) ⟨84300, by rfl⟩ : syracuseStep 224801 = 168601) B168601
theorem B257651 : Blo 99781 257651 := bstep (se 1 (by rfl) ⟨193238, by rfl⟩ : syracuseStep 257651 = 386477) B386477
theorem B126607 : Blo 99781 126607 := bstep (se 1 (by rfl) ⟨94955, by rfl⟩ : syracuseStep 126607 = 189911) B189911
theorem B1175233 : Blo 99781 1175233 := bstep (se 2 (by rfl) ⟨440712, by rfl⟩ : syracuseStep 1175233 = 881425) B881425
theorem B192289 : Blo 99781 192289 := bstep (se 2 (by rfl) ⟨72108, by rfl⟩ : syracuseStep 192289 = 144217) B144217
theorem B3534637 : Blo 99781 3534637 := bstep (se 3 (by rfl) ⟨662744, by rfl⟩ : syracuseStep 3534637 = 1325489) B1325489
theorem B290621 : Blo 99781 290621 := bstep (se 3 (by rfl) ⟨54491, by rfl⟩ : syracuseStep 290621 = 108983) B108983
theorem B225143 : Blo 99781 225143 := bstep (se 1 (by rfl) ⟨168857, by rfl⟩ : syracuseStep 225143 = 337715) B337715
theorem B520139 : Blo 99781 520139 := bstep (se 1 (by rfl) ⟨390104, by rfl⟩ : syracuseStep 520139 = 780209) B780209
theorem B585751 : Blo 99781 585751 := bstep (se 1 (by rfl) ⟨439313, by rfl⟩ : syracuseStep 585751 = 878627) B878627
theorem B225323 : Blo 99781 225323 := bstep (se 1 (by rfl) ⟨168992, by rfl⟩ : syracuseStep 225323 = 337985) B337985
theorem B2945069 : Blo 99781 2945069 := bstep (se 3 (by rfl) ⟨552200, by rfl⟩ : syracuseStep 2945069 = 1104401) B1104401
theorem B192631 : Blo 99781 192631 := bstep (se 1 (by rfl) ⟨144473, by rfl⟩ : syracuseStep 192631 = 288947) B288947
theorem B258167 : Blo 99781 258167 := bstep (se 1 (by rfl) ⟨193625, by rfl⟩ : syracuseStep 258167 = 387251) B387251
theorem B225683 : Blo 99781 225683 := bstep (se 1 (by rfl) ⟨169262, by rfl⟩ : syracuseStep 225683 = 338525) B338525
theorem B225737 : Blo 99781 225737 := bstep (se 2 (by rfl) ⟨84651, by rfl⟩ : syracuseStep 225737 = 169303) B169303
theorem B193313 : Blo 99781 193313 := bstep (se 2 (by rfl) ⟨72492, by rfl⟩ : syracuseStep 193313 = 144985) B144985
theorem B291737 : Blo 99781 291737 := bstep (se 2 (by rfl) ⟨109401, by rfl⟩ : syracuseStep 291737 = 218803) B218803
theorem B259159 : Blo 99781 259159 := bstep (se 1 (by rfl) ⟨194369, by rfl⟩ : syracuseStep 259159 = 388739) B388739
theorem B226439 : Blo 99781 226439 := bstep (se 1 (by rfl) ⟨169829, by rfl⟩ : syracuseStep 226439 = 339659) B339659
theorem B128299 : Blo 99781 128299 := bstep (se 1 (by rfl) ⟨96224, by rfl⟩ : syracuseStep 128299 = 192449) B192449
theorem B226619 : Blo 99781 226619 := bstep (se 1 (by rfl) ⟨169964, by rfl⟩ : syracuseStep 226619 = 339929) B339929
theorem B259463 : Blo 99781 259463 := bstep (se 1 (by rfl) ⟨194597, by rfl⟩ : syracuseStep 259463 = 389195) B389195
theorem B226745 : Blo 99781 226745 := bstep (se 2 (by rfl) ⟨85029, by rfl⟩ : syracuseStep 226745 = 170059) B170059
theorem B259595 : Blo 99781 259595 := bstep (se 1 (by rfl) ⟨194696, by rfl⟩ : syracuseStep 259595 = 389393) B389393
theorem B194233 : Blo 99781 194233 := bstep (se 2 (by rfl) ⟨72837, by rfl⟩ : syracuseStep 194233 = 145675) B145675
theorem B227087 : Blo 99781 227087 := bstep (se 1 (by rfl) ⟨170315, by rfl⟩ : syracuseStep 227087 = 340631) B340631
theorem B227105 : Blo 99781 227105 := bstep (se 2 (by rfl) ⟨85164, by rfl⟩ : syracuseStep 227105 = 170329) B170329
theorem B194575 : Blo 99781 194575 := bstep (se 1 (by rfl) ⟨145931, by rfl⟩ : syracuseStep 194575 = 291863) B291863
theorem B260111 : Blo 99781 260111 := bstep (se 1 (by rfl) ⟨195083, by rfl⟩ : syracuseStep 260111 = 390167) B390167
theorem B292925 : Blo 99781 292925 := bstep (se 3 (by rfl) ⟨54923, by rfl⟩ : syracuseStep 292925 = 109847) B109847
theorem B489539 : Blo 99781 489539 := bstep (se 1 (by rfl) ⟨367154, by rfl⟩ : syracuseStep 489539 = 734309) B734309
theorem B260183 : Blo 99781 260183 := bstep (se 1 (by rfl) ⟨195137, by rfl⟩ : syracuseStep 260183 = 390275) B390275
theorem B227447 : Blo 99781 227447 := bstep (se 1 (by rfl) ⟨170585, by rfl⟩ : syracuseStep 227447 = 341171) B341171
theorem B522359 : Blo 99781 522359 := bstep (se 1 (by rfl) ⟨391769, by rfl⟩ : syracuseStep 522359 = 783539) B783539
theorem B260243 : Blo 99781 260243 := bstep (se 1 (by rfl) ⟨195182, by rfl⟩ : syracuseStep 260243 = 390365) B390365
theorem B129271 : Blo 99781 129271 := bstep (se 1 (by rfl) ⟨96953, by rfl⟩ : syracuseStep 129271 = 193907) B193907
theorem B1440017 : Blo 99781 1440017 := bstep (se 2 (by rfl) ⟨540006, by rfl⟩ : syracuseStep 1440017 = 1080013) B1080013
theorem B293149 : Blo 99781 293149 := bstep (se 3 (by rfl) ⟨54965, by rfl⟩ : syracuseStep 293149 = 109931) B109931
theorem B227627 : Blo 99781 227627 := bstep (se 1 (by rfl) ⟨170720, by rfl⟩ : syracuseStep 227627 = 341441) B341441
theorem B162091 : Blo 99781 162091 := bstep (se 1 (by rfl) ⟨121568, by rfl⟩ : syracuseStep 162091 = 243137) B243137
theorem B293179 : Blo 99781 293179 := bstep (se 1 (by rfl) ⟨219884, by rfl⟩ : syracuseStep 293179 = 439769) B439769
theorem B522611 : Blo 99781 522611 := bstep (se 1 (by rfl) ⟨391958, by rfl⟩ : syracuseStep 522611 = 783917) B783917
theorem B588167 : Blo 99781 588167 := bstep (se 1 (by rfl) ⟨441125, by rfl⟩ : syracuseStep 588167 = 882251) B882251
theorem B293321 : Blo 99781 293321 := bstep (se 2 (by rfl) ⟨109995, by rfl⟩ : syracuseStep 293321 = 219991) B219991
theorem B293377 : Blo 99781 293377 := bstep (se 2 (by rfl) ⟨110016, by rfl⟩ : syracuseStep 293377 = 220033) B220033
theorem B129595 : Blo 99781 129595 := bstep (se 1 (by rfl) ⟨97196, by rfl⟩ : syracuseStep 129595 = 194393) B194393
theorem B227987 : Blo 99781 227987 := bstep (se 1 (by rfl) ⟨170990, by rfl⟩ : syracuseStep 227987 = 341981) B341981
theorem B228041 : Blo 99781 228041 := bstep (se 2 (by rfl) ⟨85515, by rfl⟩ : syracuseStep 228041 = 171031) B171031
theorem B817921 : Blo 99781 817921 := bstep (se 2 (by rfl) ⟨306720, by rfl⟩ : syracuseStep 817921 = 613441) B613441
theorem B293665 : Blo 99781 293665 := bstep (se 2 (by rfl) ⟨110124, by rfl⟩ : syracuseStep 293665 = 220249) B220249
theorem B2063141 : Blo 99781 2063141 := bstep (se 4 (by rfl) ⟨193419, by rfl⟩ : syracuseStep 2063141 = 386839) B386839
theorem B555835 : Blo 99781 555835 := bstep (se 1 (by rfl) ⟨416876, by rfl⟩ : syracuseStep 555835 = 833753) B833753
theorem B293719 : Blo 99781 293719 := bstep (se 1 (by rfl) ⟨220289, by rfl⟩ : syracuseStep 293719 = 440579) B440579
theorem B523097 : Blo 99781 523097 := bstep (se 2 (by rfl) ⟨196161, by rfl⟩ : syracuseStep 523097 = 392323) B392323
theorem B195463 : Blo 99781 195463 := bstep (se 1 (by rfl) ⟨146597, by rfl⟩ : syracuseStep 195463 = 293195) B293195
theorem B293917 : Blo 99781 293917 := bstep (se 3 (by rfl) ⟨55109, by rfl⟩ : syracuseStep 293917 = 110219) B110219
theorem B261377 : Blo 99781 261377 := bstep (se 2 (by rfl) ⟨98016, by rfl⟩ : syracuseStep 261377 = 196033) B196033
theorem B228743 : Blo 99781 228743 := bstep (se 1 (by rfl) ⟨171557, by rfl⟩ : syracuseStep 228743 = 343115) B343115
theorem B130567 : Blo 99781 130567 := bstep (se 1 (by rfl) ⟨97925, by rfl⟩ : syracuseStep 130567 = 195851) B195851
theorem B327179 : Blo 99781 327179 := bstep (se 1 (by rfl) ⟨245384, by rfl⟩ : syracuseStep 327179 = 490769) B490769
theorem B720413 : Blo 99781 720413 := bstep (se 3 (by rfl) ⟨135077, by rfl⟩ : syracuseStep 720413 = 270155) B270155
theorem B228923 : Blo 99781 228923 := bstep (se 1 (by rfl) ⟨171692, by rfl⟩ : syracuseStep 228923 = 343385) B343385
theorem B261751 : Blo 99781 261751 := bstep (se 1 (by rfl) ⟨196313, by rfl⟩ : syracuseStep 261751 = 392627) B392627
theorem B229049 : Blo 99781 229049 := bstep (se 2 (by rfl) ⟨85893, by rfl⟩ : syracuseStep 229049 = 171787) B171787
theorem B393113 : Blo 99781 393113 := bstep (se 2 (by rfl) ⟨147417, by rfl⟩ : syracuseStep 393113 = 294835) B294835
theorem B130987 : Blo 99781 130987 := bstep (se 1 (by rfl) ⟨98240, by rfl⟩ : syracuseStep 130987 = 196481) B196481
theorem B393295 : Blo 99781 393295 := bstep (se 1 (by rfl) ⟨294971, by rfl⟩ : syracuseStep 393295 = 589943) B589943
theorem B721163 : Blo 99781 721163 := bstep (se 1 (by rfl) ⟨540872, by rfl⟩ : syracuseStep 721163 = 1081745) B1081745
theorem B524555 : Blo 99781 524555 := bstep (se 1 (by rfl) ⟨393416, by rfl⟩ : syracuseStep 524555 = 786833) B786833
theorem B459245 : Blo 99781 459245 := bstep (se 3 (by rfl) ⟨86108, by rfl⟩ : syracuseStep 459245 = 172217) B172217
theorem B164359 : Blo 99781 164359 := bstep (se 1 (by rfl) ⟨123269, by rfl⟩ : syracuseStep 164359 = 246539) B246539
theorem B393767 : Blo 99781 393767 := bstep (se 1 (by rfl) ⟨295325, by rfl⟩ : syracuseStep 393767 = 590651) B590651
theorem B2228795 : Blo 99781 2228795 := bstep (se 1 (by rfl) ⟨1671596, by rfl⟩ : syracuseStep 2228795 = 3343193) B3343193
theorem B229985 : Blo 99781 229985 := bstep (se 2 (by rfl) ⟨86244, by rfl⟩ : syracuseStep 229985 = 172489) B172489
theorem B2130583 : Blo 99781 2130583 := bstep (se 1 (by rfl) ⟨1597937, by rfl⟩ : syracuseStep 2130583 = 3195875) B3195875
theorem B230327 : Blo 99781 230327 := bstep (se 1 (by rfl) ⟨172745, by rfl⟩ : syracuseStep 230327 = 345491) B345491
theorem B328711 : Blo 99781 328711 := bstep (se 1 (by rfl) ⟨246533, by rfl⟩ : syracuseStep 328711 = 493067) B493067
theorem B787475 : Blo 99781 787475 := bstep (se 1 (by rfl) ⟨590606, by rfl⟩ : syracuseStep 787475 = 1181213) B1181213
theorem B165307 : Blo 99781 165307 := bstep (se 1 (by rfl) ⟨123980, by rfl⟩ : syracuseStep 165307 = 247961) B247961
theorem B99783 : Blo 99781 99783 := bstep (se 1 (by rfl) ⟨74837, by rfl⟩ : syracuseStep 99783 = 149675) B149675
theorem B99803 : Blo 99781 99803 := bstep (se 1 (by rfl) ⟨74852, by rfl⟩ : syracuseStep 99803 = 149705) B149705
theorem B230921 : Blo 99781 230921 := bstep (se 2 (by rfl) ⟨86595, by rfl⟩ : syracuseStep 230921 = 173191) B173191
theorem B362009 : Blo 99781 362009 := bstep (se 2 (by rfl) ⟨135753, by rfl⟩ : syracuseStep 362009 = 271507) B271507
theorem B99879 : Blo 99781 99879 := bstep (se 1 (by rfl) ⟨74909, by rfl⟩ : syracuseStep 99879 = 149819) B149819
theorem B99919 : Blo 99781 99919 := bstep (se 1 (by rfl) ⟨74939, by rfl⟩ : syracuseStep 99919 = 149879) B149879
theorem B99935 : Blo 99781 99935 := bstep (se 1 (by rfl) ⟨74951, by rfl⟩ : syracuseStep 99935 = 149903) B149903
theorem B99963 : Blo 99781 99963 := bstep (se 1 (by rfl) ⟨74972, by rfl⟩ : syracuseStep 99963 = 149945) B149945
theorem B100015 : Blo 99781 100015 := bstep (se 1 (by rfl) ⟨75011, by rfl⟩ : syracuseStep 100015 = 150023) B150023
theorem B100039 : Blo 99781 100039 := bstep (se 1 (by rfl) ⟨75029, by rfl⟩ : syracuseStep 100039 = 150059) B150059
theorem B100059 : Blo 99781 100059 := bstep (se 1 (by rfl) ⟨75044, by rfl⟩ : syracuseStep 100059 = 150089) B150089
theorem B100135 : Blo 99781 100135 := bstep (se 1 (by rfl) ⟨75101, by rfl⟩ : syracuseStep 100135 = 150203) B150203
theorem B100175 : Blo 99781 100175 := bstep (se 1 (by rfl) ⟨75131, by rfl⟩ : syracuseStep 100175 = 150263) B150263
theorem B100191 : Blo 99781 100191 := bstep (se 1 (by rfl) ⟨75143, by rfl⟩ : syracuseStep 100191 = 150287) B150287
theorem B231263 : Blo 99781 231263 := bstep (se 1 (by rfl) ⟨173447, by rfl⟩ : syracuseStep 231263 = 346895) B346895
theorem B100219 : Blo 99781 100219 := bstep (se 1 (by rfl) ⟨75164, by rfl⟩ : syracuseStep 100219 = 150329) B150329
theorem B100271 : Blo 99781 100271 := bstep (se 1 (by rfl) ⟨75203, by rfl⟩ : syracuseStep 100271 = 150407) B150407
theorem B198587 : Blo 99781 198587 := bstep (se 1 (by rfl) ⟨148940, by rfl⟩ : syracuseStep 198587 = 297881) B297881
theorem B100295 : Blo 99781 100295 := bstep (se 1 (by rfl) ⟨75221, by rfl⟩ : syracuseStep 100295 = 150443) B150443
theorem B100315 : Blo 99781 100315 := bstep (se 1 (by rfl) ⟨75236, by rfl⟩ : syracuseStep 100315 = 150473) B150473
theorem B854023 : Blo 99781 854023 := bstep (se 1 (by rfl) ⟨640517, by rfl⟩ : syracuseStep 854023 = 1281035) B1281035
theorem B231443 : Blo 99781 231443 := bstep (se 1 (by rfl) ⟨173582, by rfl⟩ : syracuseStep 231443 = 347165) B347165
theorem B100391 : Blo 99781 100391 := bstep (se 1 (by rfl) ⟨75293, by rfl⟩ : syracuseStep 100391 = 150587) B150587
theorem B100431 : Blo 99781 100431 := bstep (se 1 (by rfl) ⟨75323, by rfl⟩ : syracuseStep 100431 = 150647) B150647
theorem B100447 : Blo 99781 100447 := bstep (se 1 (by rfl) ⟨75335, by rfl⟩ : syracuseStep 100447 = 150671) B150671
theorem B100475 : Blo 99781 100475 := bstep (se 1 (by rfl) ⟨75356, by rfl⟩ : syracuseStep 100475 = 150713) B150713
theorem B100527 : Blo 99781 100527 := bstep (se 1 (by rfl) ⟨75395, by rfl⟩ : syracuseStep 100527 = 150791) B150791
theorem B100551 : Blo 99781 100551 := bstep (se 1 (by rfl) ⟨75413, by rfl⟩ : syracuseStep 100551 = 150827) B150827
theorem B100571 : Blo 99781 100571 := bstep (se 1 (by rfl) ⟨75428, by rfl⟩ : syracuseStep 100571 = 150857) B150857
theorem B100647 : Blo 99781 100647 := bstep (se 1 (by rfl) ⟨75485, by rfl⟩ : syracuseStep 100647 = 150971) B150971
theorem B100687 : Blo 99781 100687 := bstep (se 1 (by rfl) ⟨75515, by rfl⟩ : syracuseStep 100687 = 151031) B151031
theorem B100703 : Blo 99781 100703 := bstep (se 1 (by rfl) ⟨75527, by rfl⟩ : syracuseStep 100703 = 151055) B151055
theorem B231785 : Blo 99781 231785 := bstep (se 2 (by rfl) ⟨86919, by rfl⟩ : syracuseStep 231785 = 173839) B173839
theorem B100731 : Blo 99781 100731 := bstep (se 1 (by rfl) ⟨75548, by rfl⟩ : syracuseStep 100731 = 151097) B151097
theorem B723329 : Blo 99781 723329 := bstep (se 2 (by rfl) ⟨271248, by rfl⟩ : syracuseStep 723329 = 542497) B542497
theorem B100783 : Blo 99781 100783 := bstep (se 1 (by rfl) ⟨75587, by rfl⟩ : syracuseStep 100783 = 151175) B151175
theorem B100807 : Blo 99781 100807 := bstep (se 1 (by rfl) ⟨75605, by rfl⟩ : syracuseStep 100807 = 151211) B151211
theorem B100827 : Blo 99781 100827 := bstep (se 1 (by rfl) ⟨75620, by rfl⟩ : syracuseStep 100827 = 151241) B151241
theorem B330203 : Blo 99781 330203 := bstep (se 1 (by rfl) ⟨247652, by rfl⟩ : syracuseStep 330203 = 495305) B495305
theorem B100903 : Blo 99781 100903 := bstep (se 1 (by rfl) ⟨75677, by rfl⟩ : syracuseStep 100903 = 151355) B151355
theorem B100943 : Blo 99781 100943 := bstep (se 1 (by rfl) ⟨75707, by rfl⟩ : syracuseStep 100943 = 151415) B151415
theorem B100959 : Blo 99781 100959 := bstep (se 1 (by rfl) ⟨75719, by rfl⟩ : syracuseStep 100959 = 151439) B151439
theorem B100987 : Blo 99781 100987 := bstep (se 1 (by rfl) ⟨75740, by rfl⟩ : syracuseStep 100987 = 151481) B151481
theorem B101039 : Blo 99781 101039 := bstep (se 1 (by rfl) ⟨75779, by rfl⟩ : syracuseStep 101039 = 151559) B151559
theorem B101063 : Blo 99781 101063 := bstep (se 1 (by rfl) ⟨75797, by rfl⟩ : syracuseStep 101063 = 151595) B151595
theorem B101083 : Blo 99781 101083 := bstep (se 1 (by rfl) ⟨75812, by rfl⟩ : syracuseStep 101083 = 151625) B151625
theorem B658205 : Blo 99781 658205 := bstep (se 3 (by rfl) ⟨123413, by rfl⟩ : syracuseStep 658205 = 246827) B246827
theorem B101159 : Blo 99781 101159 := bstep (se 1 (by rfl) ⟨75869, by rfl⟩ : syracuseStep 101159 = 151739) B151739
theorem B2558789 : Blo 99781 2558789 := bstep (se 4 (by rfl) ⟨239886, by rfl⟩ : syracuseStep 2558789 = 479773) B479773
theorem B101199 : Blo 99781 101199 := bstep (se 1 (by rfl) ⟨75899, by rfl⟩ : syracuseStep 101199 = 151799) B151799
theorem B101215 : Blo 99781 101215 := bstep (se 1 (by rfl) ⟨75911, by rfl⟩ : syracuseStep 101215 = 151823) B151823
theorem B101243 : Blo 99781 101243 := bstep (se 1 (by rfl) ⟨75932, by rfl⟩ : syracuseStep 101243 = 151865) B151865
theorem B101295 : Blo 99781 101295 := bstep (se 1 (by rfl) ⟨75971, by rfl⟩ : syracuseStep 101295 = 151943) B151943
theorem B232379 : Blo 99781 232379 := bstep (se 1 (by rfl) ⟨174284, by rfl⟩ : syracuseStep 232379 = 348569) B348569
theorem B101319 : Blo 99781 101319 := bstep (se 1 (by rfl) ⟨75989, by rfl⟩ : syracuseStep 101319 = 151979) B151979
theorem B101339 : Blo 99781 101339 := bstep (se 1 (by rfl) ⟨76004, by rfl⟩ : syracuseStep 101339 = 152009) B152009
theorem B101415 : Blo 99781 101415 := bstep (se 1 (by rfl) ⟨76061, by rfl⟩ : syracuseStep 101415 = 152123) B152123
theorem B232505 : Blo 99781 232505 := bstep (se 2 (by rfl) ⟨87189, by rfl⟩ : syracuseStep 232505 = 174379) B174379
theorem B101455 : Blo 99781 101455 := bstep (se 1 (by rfl) ⟨76091, by rfl⟩ : syracuseStep 101455 = 152183) B152183
theorem B101471 : Blo 99781 101471 := bstep (se 1 (by rfl) ⟨76103, by rfl⟩ : syracuseStep 101471 = 152207) B152207
theorem B101499 : Blo 99781 101499 := bstep (se 1 (by rfl) ⟨76124, by rfl⟩ : syracuseStep 101499 = 152249) B152249
theorem B101551 : Blo 99781 101551 := bstep (se 1 (by rfl) ⟨76163, by rfl⟩ : syracuseStep 101551 = 152327) B152327
theorem B101575 : Blo 99781 101575 := bstep (se 1 (by rfl) ⟨76181, by rfl⟩ : syracuseStep 101575 = 152363) B152363
theorem B101595 : Blo 99781 101595 := bstep (se 1 (by rfl) ⟨76196, by rfl⟩ : syracuseStep 101595 = 152393) B152393
theorem B101671 : Blo 99781 101671 := bstep (se 1 (by rfl) ⟨76253, by rfl⟩ : syracuseStep 101671 = 152507) B152507
theorem B101711 : Blo 99781 101711 := bstep (se 1 (by rfl) ⟨76283, by rfl⟩ : syracuseStep 101711 = 152567) B152567
theorem B101727 : Blo 99781 101727 := bstep (se 1 (by rfl) ⟨76295, by rfl⟩ : syracuseStep 101727 = 152591) B152591
theorem B101755 : Blo 99781 101755 := bstep (se 1 (by rfl) ⟨76316, by rfl⟩ : syracuseStep 101755 = 152633) B152633
theorem B232847 : Blo 99781 232847 := bstep (se 1 (by rfl) ⟨174635, by rfl⟩ : syracuseStep 232847 = 349271) B349271
theorem B101807 : Blo 99781 101807 := bstep (se 1 (by rfl) ⟨76355, by rfl⟩ : syracuseStep 101807 = 152711) B152711
theorem B101831 : Blo 99781 101831 := bstep (se 1 (by rfl) ⟨76373, by rfl⟩ : syracuseStep 101831 = 152747) B152747
theorem B101851 : Blo 99781 101851 := bstep (se 1 (by rfl) ⟨76388, by rfl⟩ : syracuseStep 101851 = 152777) B152777
theorem B101927 : Blo 99781 101927 := bstep (se 1 (by rfl) ⟨76445, by rfl⟩ : syracuseStep 101927 = 152891) B152891
theorem B101967 : Blo 99781 101967 := bstep (se 1 (by rfl) ⟨76475, by rfl⟩ : syracuseStep 101967 = 152951) B152951
theorem B101983 : Blo 99781 101983 := bstep (se 1 (by rfl) ⟨76487, by rfl⟩ : syracuseStep 101983 = 152975) B152975
theorem B102011 : Blo 99781 102011 := bstep (se 1 (by rfl) ⟨76508, by rfl⟩ : syracuseStep 102011 = 153017) B153017
theorem B102063 : Blo 99781 102063 := bstep (se 1 (by rfl) ⟨76547, by rfl⟩ : syracuseStep 102063 = 153095) B153095
theorem B102087 : Blo 99781 102087 := bstep (se 1 (by rfl) ⟨76565, by rfl⟩ : syracuseStep 102087 = 153131) B153131
theorem B233171 : Blo 99781 233171 := bstep (se 1 (by rfl) ⟨174878, by rfl⟩ : syracuseStep 233171 = 349757) B349757
theorem B265943 : Blo 99781 265943 := bstep (se 1 (by rfl) ⟨199457, by rfl⟩ : syracuseStep 265943 = 398915) B398915
theorem B102107 : Blo 99781 102107 := bstep (se 1 (by rfl) ⟨76580, by rfl⟩ : syracuseStep 102107 = 153161) B153161
theorem B102183 : Blo 99781 102183 := bstep (se 1 (by rfl) ⟨76637, by rfl⟩ : syracuseStep 102183 = 153275) B153275
theorem B102223 : Blo 99781 102223 := bstep (se 1 (by rfl) ⟨76667, by rfl⟩ : syracuseStep 102223 = 153335) B153335
theorem B102239 : Blo 99781 102239 := bstep (se 1 (by rfl) ⟨76679, by rfl⟩ : syracuseStep 102239 = 153359) B153359
theorem B331627 : Blo 99781 331627 := bstep (se 1 (by rfl) ⟨248720, by rfl⟩ : syracuseStep 331627 = 497441) B497441
theorem B102267 : Blo 99781 102267 := bstep (se 1 (by rfl) ⟨76700, by rfl⟩ : syracuseStep 102267 = 153401) B153401
theorem B102319 : Blo 99781 102319 := bstep (se 1 (by rfl) ⟨76739, by rfl⟩ : syracuseStep 102319 = 153479) B153479
theorem B102343 : Blo 99781 102343 := bstep (se 1 (by rfl) ⟨76757, by rfl⟩ : syracuseStep 102343 = 153515) B153515
theorem B102363 : Blo 99781 102363 := bstep (se 1 (by rfl) ⟨76772, by rfl⟩ : syracuseStep 102363 = 153545) B153545
theorem B4362245 : Blo 99781 4362245 := bstep (se 4 (by rfl) ⟨408960, by rfl⟩ : syracuseStep 4362245 = 817921) B817921
theorem B200711 : Blo 99781 200711 := bstep (se 1 (by rfl) ⟨150533, by rfl⟩ : syracuseStep 200711 = 301067) B301067
theorem B102439 : Blo 99781 102439 := bstep (se 1 (by rfl) ⟨76829, by rfl⟩ : syracuseStep 102439 = 153659) B153659
theorem B102479 : Blo 99781 102479 := bstep (se 1 (by rfl) ⟨76859, by rfl⟩ : syracuseStep 102479 = 153719) B153719
theorem B102495 : Blo 99781 102495 := bstep (se 1 (by rfl) ⟨76871, by rfl⟩ : syracuseStep 102495 = 153743) B153743
theorem B102523 : Blo 99781 102523 := bstep (se 1 (by rfl) ⟨76892, by rfl⟩ : syracuseStep 102523 = 153785) B153785
theorem B102575 : Blo 99781 102575 := bstep (se 1 (by rfl) ⟨76931, by rfl⟩ : syracuseStep 102575 = 153863) B153863
theorem B102599 : Blo 99781 102599 := bstep (se 1 (by rfl) ⟨76949, by rfl⟩ : syracuseStep 102599 = 153899) B153899
theorem B102619 : Blo 99781 102619 := bstep (se 1 (by rfl) ⟨76964, by rfl⟩ : syracuseStep 102619 = 153929) B153929
theorem B102695 : Blo 99781 102695 := bstep (se 1 (by rfl) ⟨77021, by rfl⟩ : syracuseStep 102695 = 154043) B154043
theorem B102735 : Blo 99781 102735 := bstep (se 1 (by rfl) ⟨77051, by rfl⟩ : syracuseStep 102735 = 154103) B154103
theorem B102751 : Blo 99781 102751 := bstep (se 1 (by rfl) ⟨77063, by rfl⟩ : syracuseStep 102751 = 154127) B154127
theorem B102779 : Blo 99781 102779 := bstep (se 1 (by rfl) ⟨77084, by rfl⟩ : syracuseStep 102779 = 154169) B154169
theorem B102831 : Blo 99781 102831 := bstep (se 1 (by rfl) ⟨77123, by rfl⟩ : syracuseStep 102831 = 154247) B154247
theorem B102855 : Blo 99781 102855 := bstep (se 1 (by rfl) ⟨77141, by rfl⟩ : syracuseStep 102855 = 154283) B154283
theorem B1315277 : Blo 99781 1315277 := bstep (se 3 (by rfl) ⟨246614, by rfl⟩ : syracuseStep 1315277 = 493229) B493229
theorem B102875 : Blo 99781 102875 := bstep (se 1 (by rfl) ⟨77156, by rfl⟩ : syracuseStep 102875 = 154313) B154313
theorem B102951 : Blo 99781 102951 := bstep (se 1 (by rfl) ⟨77213, by rfl⟩ : syracuseStep 102951 = 154427) B154427
theorem B168527 : Blo 99781 168527 := bstep (se 1 (by rfl) ⟨126395, by rfl⟩ : syracuseStep 168527 = 252791) B252791
theorem B102991 : Blo 99781 102991 := bstep (se 1 (by rfl) ⟨77243, by rfl⟩ : syracuseStep 102991 = 154487) B154487
theorem B103007 : Blo 99781 103007 := bstep (se 1 (by rfl) ⟨77255, by rfl⟩ : syracuseStep 103007 = 154511) B154511
theorem B103035 : Blo 99781 103035 := bstep (se 1 (by rfl) ⟨77276, by rfl⟩ : syracuseStep 103035 = 154553) B154553
theorem B103087 : Blo 99781 103087 := bstep (se 1 (by rfl) ⟨77315, by rfl⟩ : syracuseStep 103087 = 154631) B154631
theorem B103111 : Blo 99781 103111 := bstep (se 1 (by rfl) ⟨77333, by rfl⟩ : syracuseStep 103111 = 154667) B154667
theorem B103131 : Blo 99781 103131 := bstep (se 1 (by rfl) ⟨77348, by rfl⟩ : syracuseStep 103131 = 154697) B154697
theorem B103207 : Blo 99781 103207 := bstep (se 1 (by rfl) ⟨77405, by rfl⟩ : syracuseStep 103207 = 154811) B154811
theorem B103247 : Blo 99781 103247 := bstep (se 1 (by rfl) ⟨77435, by rfl⟩ : syracuseStep 103247 = 154871) B154871
theorem B103263 : Blo 99781 103263 := bstep (se 1 (by rfl) ⟨77447, by rfl⟩ : syracuseStep 103263 = 154895) B154895
theorem B168809 : Blo 99781 168809 := bstep (se 2 (by rfl) ⟨63303, by rfl⟩ : syracuseStep 168809 = 126607) B126607
theorem B103291 : Blo 99781 103291 := bstep (se 1 (by rfl) ⟨77468, by rfl⟩ : syracuseStep 103291 = 154937) B154937
theorem B103343 : Blo 99781 103343 := bstep (se 1 (by rfl) ⟨77507, by rfl⟩ : syracuseStep 103343 = 155015) B155015
theorem B398267 : Blo 99781 398267 := bstep (se 1 (by rfl) ⟨298700, by rfl⟩ : syracuseStep 398267 = 597401) B597401
theorem B103367 : Blo 99781 103367 := bstep (se 1 (by rfl) ⟨77525, by rfl⟩ : syracuseStep 103367 = 155051) B155051
theorem B103387 : Blo 99781 103387 := bstep (se 1 (by rfl) ⟨77540, by rfl⟩ : syracuseStep 103387 = 155081) B155081
theorem B103463 : Blo 99781 103463 := bstep (se 1 (by rfl) ⟨77597, by rfl⟩ : syracuseStep 103463 = 155195) B155195
theorem B103503 : Blo 99781 103503 := bstep (se 1 (by rfl) ⟨77627, by rfl⟩ : syracuseStep 103503 = 155255) B155255
theorem B103519 : Blo 99781 103519 := bstep (se 1 (by rfl) ⟨77639, by rfl⟩ : syracuseStep 103519 = 155279) B155279
theorem B103547 : Blo 99781 103547 := bstep (se 1 (by rfl) ⟨77660, by rfl⟩ : syracuseStep 103547 = 155321) B155321
theorem B103599 : Blo 99781 103599 := bstep (se 1 (by rfl) ⟨77699, by rfl⟩ : syracuseStep 103599 = 155399) B155399
theorem B103623 : Blo 99781 103623 := bstep (se 1 (by rfl) ⟨77717, by rfl⟩ : syracuseStep 103623 = 155435) B155435
theorem B103643 : Blo 99781 103643 := bstep (se 1 (by rfl) ⟨77732, by rfl⟩ : syracuseStep 103643 = 155465) B155465
theorem B496919 : Blo 99781 496919 := bstep (se 1 (by rfl) ⟨372689, by rfl⟩ : syracuseStep 496919 = 745379) B745379
theorem B103719 : Blo 99781 103719 := bstep (se 1 (by rfl) ⟨77789, by rfl⟩ : syracuseStep 103719 = 155579) B155579
theorem B103759 : Blo 99781 103759 := bstep (se 1 (by rfl) ⟨77819, by rfl⟩ : syracuseStep 103759 = 155639) B155639
theorem B103775 : Blo 99781 103775 := bstep (se 1 (by rfl) ⟨77831, by rfl⟩ : syracuseStep 103775 = 155663) B155663
theorem B824741 : Blo 99781 824741 := bstep (se 4 (by rfl) ⟨77319, by rfl⟩ : syracuseStep 824741 = 154639) B154639
theorem B169391 : Blo 99781 169391 := bstep (se 1 (by rfl) ⟨127043, by rfl⟩ : syracuseStep 169391 = 254087) B254087
theorem B366119 : Blo 99781 366119 := bstep (se 1 (by rfl) ⟨274589, by rfl⟩ : syracuseStep 366119 = 549179) B549179
theorem B693821 : Blo 99781 693821 := bstep (se 3 (by rfl) ⟨130091, by rfl⟩ : syracuseStep 693821 = 260183) B260183
theorem B398945 : Blo 99781 398945 := bstep (se 2 (by rfl) ⟨149604, by rfl⟩ : syracuseStep 398945 = 299209) B299209
theorem B431831 : Blo 99781 431831 := bstep (se 1 (by rfl) ⟨323873, by rfl⟩ : syracuseStep 431831 = 647747) B647747
theorem B169823 : Blo 99781 169823 := bstep (se 1 (by rfl) ⟨127367, by rfl⟩ : syracuseStep 169823 = 254735) B254735
theorem B170383 : Blo 99781 170383 := bstep (se 1 (by rfl) ⟨127787, by rfl⟩ : syracuseStep 170383 = 255575) B255575
theorem B891425 : Blo 99781 891425 := bstep (se 2 (by rfl) ⟨334284, by rfl⟩ : syracuseStep 891425 = 668569) B668569
theorem B171065 : Blo 99781 171065 := bstep (se 2 (by rfl) ⟨64149, by rfl⟩ : syracuseStep 171065 = 128299) B128299
theorem B597071 : Blo 99781 597071 := bstep (se 1 (by rfl) ⟨447803, by rfl⟩ : syracuseStep 597071 = 895607) B895607
theorem B171767 : Blo 99781 171767 := bstep (se 1 (by rfl) ⟨128825, by rfl⟩ : syracuseStep 171767 = 257651) B257651
theorem B663329 : Blo 99781 663329 := bstep (se 2 (by rfl) ⟨248748, by rfl⟩ : syracuseStep 663329 = 497497) B497497
theorem B663481 : Blo 99781 663481 := bstep (se 2 (by rfl) ⟨248805, by rfl⟩ : syracuseStep 663481 = 497611) B497611
theorem B729091 : Blo 99781 729091 := bstep (se 1 (by rfl) ⟨546818, by rfl⟩ : syracuseStep 729091 = 1093637) B1093637
theorem B172111 : Blo 99781 172111 := bstep (se 1 (by rfl) ⟨129083, by rfl⟩ : syracuseStep 172111 = 258167) B258167
theorem B1450163 : Blo 99781 1450163 := bstep (se 1 (by rfl) ⟨1087622, by rfl⟩ : syracuseStep 1450163 = 2175245) B2175245
theorem B172361 : Blo 99781 172361 := bstep (se 2 (by rfl) ⟨64635, by rfl⟩ : syracuseStep 172361 = 129271) B129271
theorem B172793 : Blo 99781 172793 := bstep (se 2 (by rfl) ⟨64797, by rfl⟩ : syracuseStep 172793 = 129595) B129595
theorem B467819 : Blo 99781 467819 := bstep (se 1 (by rfl) ⟨350864, by rfl⟩ : syracuseStep 467819 = 701729) B701729
theorem B172975 : Blo 99781 172975 := bstep (se 1 (by rfl) ⟨129731, by rfl⟩ : syracuseStep 172975 = 259463) B259463
theorem B205751 : Blo 99781 205751 := bstep (se 1 (by rfl) ⟨154313, by rfl⟩ : syracuseStep 205751 = 308627) B308627
theorem B173063 : Blo 99781 173063 := bstep (se 1 (by rfl) ⟨129797, by rfl⟩ : syracuseStep 173063 = 259595) B259595
theorem B337067 : Blo 99781 337067 := bstep (se 1 (by rfl) ⟨252800, by rfl⟩ : syracuseStep 337067 = 505601) B505601
theorem B1320137 : Blo 99781 1320137 := bstep (se 2 (by rfl) ⟨495051, by rfl⟩ : syracuseStep 1320137 = 990103) B990103
theorem B173407 : Blo 99781 173407 := bstep (se 1 (by rfl) ⟨130055, by rfl⟩ : syracuseStep 173407 = 260111) B260111
theorem B173495 : Blo 99781 173495 := bstep (se 1 (by rfl) ⟨130121, by rfl⟩ : syracuseStep 173495 = 260243) B260243
theorem B960011 : Blo 99781 960011 := bstep (se 1 (by rfl) ⟨720008, by rfl⟩ : syracuseStep 960011 = 1440017) B1440017
theorem B468679 : Blo 99781 468679 := bstep (se 1 (by rfl) ⟨351509, by rfl⟩ : syracuseStep 468679 = 703019) B703019
theorem B337607 : Blo 99781 337607 := bstep (se 1 (by rfl) ⟨253205, by rfl⟩ : syracuseStep 337607 = 506411) B506411
theorem B1058669 : Blo 99781 1058669 := bstep (se 3 (by rfl) ⟨198500, by rfl⟩ : syracuseStep 1058669 = 397001) B397001
theorem B174089 : Blo 99781 174089 := bstep (se 2 (by rfl) ⟨65283, by rfl⟩ : syracuseStep 174089 = 130567) B130567
theorem B174251 : Blo 99781 174251 := bstep (se 1 (by rfl) ⟨130688, by rfl⟩ : syracuseStep 174251 = 261377) B261377
theorem B1387037 : Blo 99781 1387037 := bstep (se 3 (by rfl) ⟨260069, by rfl⟩ : syracuseStep 1387037 = 520139) B520139
theorem B338471 : Blo 99781 338471 := bstep (se 1 (by rfl) ⟨253853, by rfl⟩ : syracuseStep 338471 = 507707) B507707
theorem B174649 : Blo 99781 174649 := bstep (se 2 (by rfl) ⟨65493, by rfl⟩ : syracuseStep 174649 = 130987) B130987
theorem B338579 : Blo 99781 338579 := bstep (se 1 (by rfl) ⟨253934, by rfl⟩ : syracuseStep 338579 = 507869) B507869
theorem B174791 : Blo 99781 174791 := bstep (se 1 (by rfl) ⟨131093, by rfl⟩ : syracuseStep 174791 = 262187) B262187
theorem B174953 : Blo 99781 174953 := bstep (se 2 (by rfl) ⟨65607, by rfl⟩ : syracuseStep 174953 = 131215) B131215
theorem B338795 : Blo 99781 338795 := bstep (se 1 (by rfl) ⟨254096, by rfl⟩ : syracuseStep 338795 = 508193) B508193
theorem B1551251 : Blo 99781 1551251 := bstep (se 1 (by rfl) ⟨1163438, by rfl⟩ : syracuseStep 1551251 = 2326877) B2326877
theorem B338849 : Blo 99781 338849 := bstep (se 2 (by rfl) ⟨127068, by rfl⟩ : syracuseStep 338849 = 254137) B254137
theorem B240887 : Blo 99781 240887 := bstep (se 1 (by rfl) ⟨180665, by rfl⟩ : syracuseStep 240887 = 361331) B361331
theorem B404747 : Blo 99781 404747 := bstep (se 1 (by rfl) ⟨303560, by rfl⟩ : syracuseStep 404747 = 607121) B607121
theorem B339443 : Blo 99781 339443 := bstep (se 1 (by rfl) ⟨254582, by rfl⟩ : syracuseStep 339443 = 509165) B509165
theorem B339983 : Blo 99781 339983 := bstep (se 1 (by rfl) ⟨254987, by rfl⟩ : syracuseStep 339983 = 509975) B509975
theorem B208975 : Blo 99781 208975 := bstep (se 1 (by rfl) ⟨156731, by rfl⟩ : syracuseStep 208975 = 313463) B313463
theorem B405847 : Blo 99781 405847 := bstep (se 1 (by rfl) ⟨304385, by rfl⟩ : syracuseStep 405847 = 608771) B608771
theorem B6238691 : Blo 99781 6238691 := bstep (se 1 (by rfl) ⟨4679018, by rfl⟩ : syracuseStep 6238691 = 9358037) B9358037
theorem B340577 : Blo 99781 340577 := bstep (se 2 (by rfl) ⟨127716, by rfl⟩ : syracuseStep 340577 = 255433) B255433
theorem B406205 : Blo 99781 406205 := bstep (se 3 (by rfl) ⟨76163, by rfl⟩ : syracuseStep 406205 = 152327) B152327
theorem B406367 : Blo 99781 406367 := bstep (se 1 (by rfl) ⟨304775, by rfl⟩ : syracuseStep 406367 = 609551) B609551
theorem B1258415 : Blo 99781 1258415 := bstep (se 1 (by rfl) ⟨943811, by rfl⟩ : syracuseStep 1258415 = 1887623) B1887623
theorem B407405 : Blo 99781 407405 := bstep (se 3 (by rfl) ⟨76388, by rfl⟩ : syracuseStep 407405 = 152777) B152777
theorem B767879 : Blo 99781 767879 := bstep (se 1 (by rfl) ⟨575909, by rfl⟩ : syracuseStep 767879 = 1151819) B1151819
theorem B112603 : Blo 99781 112603 := bstep (se 1 (by rfl) ⟨84452, by rfl⟩ : syracuseStep 112603 = 168905) B168905
theorem B342035 : Blo 99781 342035 := bstep (se 1 (by rfl) ⟨256526, by rfl⟩ : syracuseStep 342035 = 513053) B513053
theorem B440477 : Blo 99781 440477 := bstep (se 3 (by rfl) ⟨82589, by rfl⟩ : syracuseStep 440477 = 165179) B165179
theorem B342359 : Blo 99781 342359 := bstep (se 1 (by rfl) ⟨256769, by rfl⟩ : syracuseStep 342359 = 513539) B513539
theorem B113071 : Blo 99781 113071 := bstep (se 1 (by rfl) ⟨84803, by rfl⟩ : syracuseStep 113071 = 169607) B169607
theorem B146119 : Blo 99781 146119 := bstep (se 1 (by rfl) ⟨109589, by rfl⟩ : syracuseStep 146119 = 219179) B219179
theorem B113503 : Blo 99781 113503 := bstep (se 1 (by rfl) ⟨85127, by rfl⟩ : syracuseStep 113503 = 170255) B170255
theorem B539621 : Blo 99781 539621 := bstep (se 4 (by rfl) ⟨50589, by rfl⟩ : syracuseStep 539621 = 101179) B101179
theorem B1588247 : Blo 99781 1588247 := bstep (se 1 (by rfl) ⟨1191185, by rfl⟩ : syracuseStep 1588247 = 2382371) B2382371
theorem B375965 : Blo 99781 375965 := bstep (se 3 (by rfl) ⟨70493, by rfl⟩ : syracuseStep 375965 = 140987) B140987
theorem B113863 : Blo 99781 113863 := bstep (se 1 (by rfl) ⟨85397, by rfl⟩ : syracuseStep 113863 = 170795) B170795
theorem B343439 : Blo 99781 343439 := bstep (se 1 (by rfl) ⟨257579, by rfl⟩ : syracuseStep 343439 = 515159) B515159
theorem B441895 : Blo 99781 441895 := bstep (se 1 (by rfl) ⟨331421, by rfl⟩ : syracuseStep 441895 = 662843) B662843
theorem B343763 : Blo 99781 343763 := bstep (se 1 (by rfl) ⟨257822, by rfl⟩ : syracuseStep 343763 = 515645) B515645
theorem B114727 : Blo 99781 114727 := bstep (se 1 (by rfl) ⟨86045, by rfl⟩ : syracuseStep 114727 = 172091) B172091
theorem B344407 : Blo 99781 344407 := bstep (se 1 (by rfl) ⟨258305, by rfl⟩ : syracuseStep 344407 = 516611) B516611
theorem B442711 : Blo 99781 442711 := bstep (se 1 (by rfl) ⟨332033, by rfl⟩ : syracuseStep 442711 = 664067) B664067
theorem B147895 : Blo 99781 147895 := bstep (se 1 (by rfl) ⟨110921, by rfl⟩ : syracuseStep 147895 = 221843) B221843
theorem B279065 : Blo 99781 279065 := bstep (se 2 (by rfl) ⟨104649, by rfl⟩ : syracuseStep 279065 = 209299) B209299
theorem B574087 : Blo 99781 574087 := bstep (se 1 (by rfl) ⟨430565, by rfl⟩ : syracuseStep 574087 = 861131) B861131
theorem B443243 : Blo 99781 443243 := bstep (se 1 (by rfl) ⟨332432, by rfl⟩ : syracuseStep 443243 = 664865) B664865
theorem B344951 : Blo 99781 344951 := bstep (se 1 (by rfl) ⟨258713, by rfl⟩ : syracuseStep 344951 = 517427) B517427
theorem B345167 : Blo 99781 345167 := bstep (se 1 (by rfl) ⟨258875, by rfl⟩ : syracuseStep 345167 = 517751) B517751
theorem B1328399 : Blo 99781 1328399 := bstep (se 1 (by rfl) ⟨996299, by rfl⟩ : syracuseStep 1328399 = 1992599) B1992599
theorem B509327 : Blo 99781 509327 := bstep (se 1 (by rfl) ⟨381995, by rfl⟩ : syracuseStep 509327 = 763991) B763991
theorem B1459619 : Blo 99781 1459619 := bstep (se 1 (by rfl) ⟨1094714, by rfl⟩ : syracuseStep 1459619 = 2189429) B2189429
theorem B345545 : Blo 99781 345545 := bstep (se 2 (by rfl) ⟨129579, by rfl⟩ : syracuseStep 345545 = 259159) B259159
theorem B116347 : Blo 99781 116347 := bstep (se 1 (by rfl) ⟨87260, by rfl⟩ : syracuseStep 116347 = 174521) B174521
theorem B280253 : Blo 99781 280253 := bstep (se 3 (by rfl) ⟨52547, by rfl⟩ : syracuseStep 280253 = 105095) B105095
theorem B345815 : Blo 99781 345815 := bstep (se 1 (by rfl) ⟨259361, by rfl⟩ : syracuseStep 345815 = 518723) B518723
theorem B346031 : Blo 99781 346031 := bstep (se 1 (by rfl) ⟨259523, by rfl⟩ : syracuseStep 346031 = 519047) B519047
theorem B575545 : Blo 99781 575545 := bstep (se 2 (by rfl) ⟨215829, by rfl⟩ : syracuseStep 575545 = 431659) B431659
theorem B772253 : Blo 99781 772253 := bstep (se 3 (by rfl) ⟨144797, by rfl⟩ : syracuseStep 772253 = 289595) B289595
theorem B149753 : Blo 99781 149753 := bstep (se 2 (by rfl) ⟨56157, by rfl⟩ : syracuseStep 149753 = 112315) B112315
theorem B149855 : Blo 99781 149855 := bstep (se 1 (by rfl) ⟨112391, by rfl⟩ : syracuseStep 149855 = 224783) B224783
theorem B149867 : Blo 99781 149867 := bstep (se 1 (by rfl) ⟨112400, by rfl⟩ : syracuseStep 149867 = 224801) B224801
theorem B936481 : Blo 99781 936481 := bstep (se 2 (by rfl) ⟨351180, by rfl⟩ : syracuseStep 936481 = 702361) B702361
theorem B150095 : Blo 99781 150095 := bstep (se 1 (by rfl) ⟨112571, by rfl⟩ : syracuseStep 150095 = 225143) B225143
theorem B150215 : Blo 99781 150215 := bstep (se 1 (by rfl) ⟨112661, by rfl⟩ : syracuseStep 150215 = 225323) B225323
theorem B150377 : Blo 99781 150377 := bstep (se 2 (by rfl) ⟨56391, by rfl⟩ : syracuseStep 150377 = 112783) B112783
theorem B150455 : Blo 99781 150455 := bstep (se 1 (by rfl) ⟨112841, by rfl⟩ : syracuseStep 150455 = 225683) B225683
theorem B150491 : Blo 99781 150491 := bstep (se 1 (by rfl) ⟨112868, by rfl⟩ : syracuseStep 150491 = 225737) B225737
theorem B379961 : Blo 99781 379961 := bstep (se 2 (by rfl) ⟨142485, by rfl⟩ : syracuseStep 379961 = 284971) B284971
theorem B216121 : Blo 99781 216121 := bstep (se 2 (by rfl) ⟨81045, by rfl⟩ : syracuseStep 216121 = 162091) B162091
theorem B150959 : Blo 99781 150959 := bstep (se 1 (by rfl) ⟨113219, by rfl⟩ : syracuseStep 150959 = 226439) B226439
theorem B511433 : Blo 99781 511433 := bstep (se 2 (by rfl) ⟨191787, by rfl⟩ : syracuseStep 511433 = 383575) B383575
theorem B151049 : Blo 99781 151049 := bstep (se 2 (by rfl) ⟨56643, by rfl⟩ : syracuseStep 151049 = 113287) B113287
theorem B151079 : Blo 99781 151079 := bstep (se 1 (by rfl) ⟨113309, by rfl⟩ : syracuseStep 151079 = 226619) B226619
theorem B151163 : Blo 99781 151163 := bstep (se 1 (by rfl) ⟨113372, by rfl⟩ : syracuseStep 151163 = 226745) B226745
theorem B315019 : Blo 99781 315019 := bstep (se 1 (by rfl) ⟨236264, by rfl⟩ : syracuseStep 315019 = 472529) B472529
theorem B151289 : Blo 99781 151289 := bstep (se 2 (by rfl) ⟨56733, by rfl⟩ : syracuseStep 151289 = 113467) B113467
theorem B741113 : Blo 99781 741113 := bstep (se 2 (by rfl) ⟨277917, by rfl⟩ : syracuseStep 741113 = 555835) B555835
theorem B151391 : Blo 99781 151391 := bstep (se 1 (by rfl) ⟨113543, by rfl⟩ : syracuseStep 151391 = 227087) B227087
theorem B151403 : Blo 99781 151403 := bstep (se 1 (by rfl) ⟨113552, by rfl⟩ : syracuseStep 151403 = 227105) B227105
theorem B872477 : Blo 99781 872477 := bstep (se 3 (by rfl) ⟨163589, by rfl⟩ : syracuseStep 872477 = 327179) B327179
theorem B151631 : Blo 99781 151631 := bstep (se 1 (by rfl) ⟨113723, by rfl⟩ : syracuseStep 151631 = 227447) B227447
theorem B348239 : Blo 99781 348239 := bstep (se 1 (by rfl) ⟨261179, by rfl⟩ : syracuseStep 348239 = 522359) B522359
theorem B512081 : Blo 99781 512081 := bstep (se 2 (by rfl) ⟨192030, by rfl⟩ : syracuseStep 512081 = 384061) B384061
theorem B151751 : Blo 99781 151751 := bstep (se 1 (by rfl) ⟨113813, by rfl⟩ : syracuseStep 151751 = 227627) B227627
theorem B348407 : Blo 99781 348407 := bstep (se 1 (by rfl) ⟨261305, by rfl⟩ : syracuseStep 348407 = 522611) B522611
theorem B151913 : Blo 99781 151913 := bstep (se 2 (by rfl) ⟨56967, by rfl⟩ : syracuseStep 151913 = 113935) B113935
theorem B151991 : Blo 99781 151991 := bstep (se 1 (by rfl) ⟨113993, by rfl⟩ : syracuseStep 151991 = 227987) B227987
theorem B152027 : Blo 99781 152027 := bstep (se 1 (by rfl) ⟨114020, by rfl⟩ : syracuseStep 152027 = 228041) B228041
theorem B381449 : Blo 99781 381449 := bstep (se 2 (by rfl) ⟨143043, by rfl⟩ : syracuseStep 381449 = 286087) B286087
theorem B348731 : Blo 99781 348731 := bstep (se 1 (by rfl) ⟨261548, by rfl⟩ : syracuseStep 348731 = 523097) B523097
theorem B349001 : Blo 99781 349001 := bstep (se 2 (by rfl) ⟨130875, by rfl⟩ : syracuseStep 349001 = 261751) B261751
theorem B152495 : Blo 99781 152495 := bstep (se 1 (by rfl) ⟨114371, by rfl⟩ : syracuseStep 152495 = 228743) B228743
theorem B775169 : Blo 99781 775169 := bstep (se 2 (by rfl) ⟨290688, by rfl⟩ : syracuseStep 775169 = 581377) B581377
theorem B152585 : Blo 99781 152585 := bstep (se 2 (by rfl) ⟨57219, by rfl⟩ : syracuseStep 152585 = 114439) B114439
theorem B480275 : Blo 99781 480275 := bstep (se 1 (by rfl) ⟨360206, by rfl⟩ : syracuseStep 480275 = 720413) B720413
theorem B152615 : Blo 99781 152615 := bstep (se 1 (by rfl) ⟨114461, by rfl⟩ : syracuseStep 152615 = 228923) B228923
theorem B152699 : Blo 99781 152699 := bstep (se 1 (by rfl) ⟨114524, by rfl⟩ : syracuseStep 152699 = 229049) B229049
theorem B152825 : Blo 99781 152825 := bstep (se 2 (by rfl) ⟨57309, by rfl⟩ : syracuseStep 152825 = 114619) B114619
theorem B152927 : Blo 99781 152927 := bstep (se 1 (by rfl) ⟨114695, by rfl⟩ : syracuseStep 152927 = 229391) B229391
theorem B152939 : Blo 99781 152939 := bstep (se 1 (by rfl) ⟨114704, by rfl⟩ : syracuseStep 152939 = 229409) B229409
theorem B1463771 : Blo 99781 1463771 := bstep (se 1 (by rfl) ⟨1097828, by rfl⟩ : syracuseStep 1463771 = 2195657) B2195657
theorem B26891747 : Blo 99781 26891747 := bstep (se 1 (by rfl) ⟨20168810, by rfl⟩ : syracuseStep 26891747 = 40337621) B40337621
theorem B153167 : Blo 99781 153167 := bstep (se 1 (by rfl) ⟨114875, by rfl⟩ : syracuseStep 153167 = 229751) B229751
theorem B382603 : Blo 99781 382603 := bstep (se 1 (by rfl) ⟨286952, by rfl⟩ : syracuseStep 382603 = 573905) B573905
theorem B153287 : Blo 99781 153287 := bstep (se 1 (by rfl) ⟨114965, by rfl⟩ : syracuseStep 153287 = 229931) B229931
theorem B153449 : Blo 99781 153449 := bstep (se 2 (by rfl) ⟨57543, by rfl⟩ : syracuseStep 153449 = 115087) B115087
theorem B153527 : Blo 99781 153527 := bstep (se 1 (by rfl) ⟨115145, by rfl⟩ : syracuseStep 153527 = 230291) B230291
theorem B350135 : Blo 99781 350135 := bstep (se 1 (by rfl) ⟨262601, by rfl⟩ : syracuseStep 350135 = 525203) B525203
theorem B382907 : Blo 99781 382907 := bstep (se 1 (by rfl) ⟨287180, by rfl⟩ : syracuseStep 382907 = 574361) B574361
theorem B153563 : Blo 99781 153563 := bstep (se 1 (by rfl) ⟨115172, by rfl⟩ : syracuseStep 153563 = 230345) B230345
theorem B154031 : Blo 99781 154031 := bstep (se 1 (by rfl) ⟨115523, by rfl⟩ : syracuseStep 154031 = 231047) B231047
theorem B154121 : Blo 99781 154121 := bstep (se 2 (by rfl) ⟨57795, by rfl⟩ : syracuseStep 154121 = 115591) B115591
theorem B154151 : Blo 99781 154151 := bstep (se 1 (by rfl) ⟨115613, by rfl⟩ : syracuseStep 154151 = 231227) B231227
theorem B154235 : Blo 99781 154235 := bstep (se 1 (by rfl) ⟨115676, by rfl⟩ : syracuseStep 154235 = 231353) B231353
theorem B154361 : Blo 99781 154361 := bstep (se 2 (by rfl) ⟨57885, by rfl⟩ : syracuseStep 154361 = 115771) B115771
theorem B154463 : Blo 99781 154463 := bstep (se 1 (by rfl) ⟨115847, by rfl⟩ : syracuseStep 154463 = 231695) B231695
theorem B154475 : Blo 99781 154475 := bstep (se 1 (by rfl) ⟨115856, by rfl⟩ : syracuseStep 154475 = 231713) B231713
theorem B154703 : Blo 99781 154703 := bstep (se 1 (by rfl) ⟨116027, by rfl⟩ : syracuseStep 154703 = 232055) B232055
theorem B154823 : Blo 99781 154823 := bstep (se 1 (by rfl) ⟨116117, by rfl⟩ : syracuseStep 154823 = 232235) B232235
theorem B1006937 : Blo 99781 1006937 := bstep (se 2 (by rfl) ⟨377601, by rfl⟩ : syracuseStep 1006937 = 755203) B755203
theorem B154985 : Blo 99781 154985 := bstep (se 2 (by rfl) ⟨58119, by rfl⟩ : syracuseStep 154985 = 116239) B116239
theorem B253327 : Blo 99781 253327 := bstep (se 1 (by rfl) ⟨189995, by rfl⟩ : syracuseStep 253327 = 379991) B379991
theorem B515501 : Blo 99781 515501 := bstep (se 3 (by rfl) ⟨96656, by rfl⟩ : syracuseStep 515501 = 193313) B193313
theorem B155063 : Blo 99781 155063 := bstep (se 1 (by rfl) ⟨116297, by rfl⟩ : syracuseStep 155063 = 232595) B232595
theorem B155099 : Blo 99781 155099 := bstep (se 1 (by rfl) ⟨116324, by rfl⟩ : syracuseStep 155099 = 232649) B232649
theorem B286247 : Blo 99781 286247 := bstep (se 1 (by rfl) ⟨214685, by rfl⟩ : syracuseStep 286247 = 429371) B429371
theorem B1302155 : Blo 99781 1302155 := bstep (se 1 (by rfl) ⟨976616, by rfl⟩ : syracuseStep 1302155 = 1953233) B1953233
theorem B253651 : Blo 99781 253651 := bstep (se 1 (by rfl) ⟨190238, by rfl⟩ : syracuseStep 253651 = 380477) B380477
theorem B351959 : Blo 99781 351959 := bstep (se 1 (by rfl) ⟨263969, by rfl⟩ : syracuseStep 351959 = 527939) B527939
theorem B155567 : Blo 99781 155567 := bstep (se 1 (by rfl) ⟨116675, by rfl⟩ : syracuseStep 155567 = 233351) B233351
theorem B155657 : Blo 99781 155657 := bstep (se 2 (by rfl) ⟨58371, by rfl⟩ : syracuseStep 155657 = 116743) B116743
theorem B516617 : Blo 99781 516617 := bstep (se 2 (by rfl) ⟨193731, by rfl⟩ : syracuseStep 516617 = 387463) B387463
theorem B254603 : Blo 99781 254603 := bstep (se 1 (by rfl) ⟨190952, by rfl⟩ : syracuseStep 254603 = 381905) B381905
theorem B877229 : Blo 99781 877229 := bstep (se 3 (by rfl) ⟨164480, by rfl⟩ : syracuseStep 877229 = 328961) B328961
theorem B549587 : Blo 99781 549587 := bstep (se 1 (by rfl) ⟨412190, by rfl⟩ : syracuseStep 549587 = 824381) B824381
theorem B287671 : Blo 99781 287671 := bstep (se 1 (by rfl) ⟨215753, by rfl⟩ : syracuseStep 287671 = 431507) B431507
theorem B418823 : Blo 99781 418823 := bstep (se 1 (by rfl) ⟨314117, by rfl⟩ : syracuseStep 418823 = 628235) B628235
theorem B189449 : Blo 99781 189449 := bstep (se 2 (by rfl) ⟨71043, by rfl⟩ : syracuseStep 189449 = 142087) B142087
theorem B189479 : Blo 99781 189479 := bstep (se 1 (by rfl) ⟨142109, by rfl⟩ : syracuseStep 189479 = 284219) B284219
theorem B779543 : Blo 99781 779543 := bstep (se 1 (by rfl) ⟨584657, by rfl⟩ : syracuseStep 779543 = 1169315) B1169315
theorem B321209 : Blo 99781 321209 := bstep (se 2 (by rfl) ⟨120453, by rfl⟩ : syracuseStep 321209 = 240907) B240907
theorem B124615 : Blo 99781 124615 := bstep (se 1 (by rfl) ⟨93461, by rfl⟩ : syracuseStep 124615 = 186923) B186923
theorem B190163 : Blo 99781 190163 := bstep (se 1 (by rfl) ⟨142622, by rfl⟩ : syracuseStep 190163 = 285245) B285245
theorem B419539 : Blo 99781 419539 := bstep (se 1 (by rfl) ⟨314654, by rfl⟩ : syracuseStep 419539 = 629309) B629309
theorem B190201 : Blo 99781 190201 := bstep (se 2 (by rfl) ⟨71325, by rfl⟩ : syracuseStep 190201 = 142651) B142651
theorem B255737 : Blo 99781 255737 := bstep (se 2 (by rfl) ⟨95901, by rfl⟩ : syracuseStep 255737 = 191803) B191803
theorem B550817 : Blo 99781 550817 := bstep (se 2 (by rfl) ⟨206556, by rfl⟩ : syracuseStep 550817 = 413113) B413113
theorem B386977 : Blo 99781 386977 := bstep (se 2 (by rfl) ⟨145116, by rfl⟩ : syracuseStep 386977 = 290233) B290233
theorem B255919 : Blo 99781 255919 := bstep (se 1 (by rfl) ⟨191939, by rfl⟩ : syracuseStep 255919 = 383879) B383879
theorem B518075 : Blo 99781 518075 := bstep (se 1 (by rfl) ⟨388556, by rfl⟩ : syracuseStep 518075 = 777113) B777113
theorem B288775 : Blo 99781 288775 := bstep (se 1 (by rfl) ⟨216581, by rfl⟩ : syracuseStep 288775 = 433163) B433163
theorem B1566977 : Blo 99781 1566977 := bstep (se 2 (by rfl) ⟨587616, by rfl⟩ : syracuseStep 1566977 = 1175233) B1175233
theorem B747863 : Blo 99781 747863 := bstep (se 1 (by rfl) ⟨560897, by rfl⟩ : syracuseStep 747863 = 1121795) B1121795
theorem B289129 : Blo 99781 289129 := bstep (se 2 (by rfl) ⟨108423, by rfl⟩ : syracuseStep 289129 = 216847) B216847
theorem B256385 : Blo 99781 256385 := bstep (se 2 (by rfl) ⟨96144, by rfl⟩ : syracuseStep 256385 = 192289) B192289
theorem B4712849 : Blo 99781 4712849 := bstep (se 2 (by rfl) ⟨1767318, by rfl⟩ : syracuseStep 4712849 = 3534637) B3534637
theorem B190907 : Blo 99781 190907 := bstep (se 1 (by rfl) ⟨143180, by rfl⟩ : syracuseStep 190907 = 286361) B286361
theorem B289403 : Blo 99781 289403 := bstep (se 1 (by rfl) ⟨217052, by rfl⟩ : syracuseStep 289403 = 434105) B434105
theorem B813769 : Blo 99781 813769 := bstep (se 2 (by rfl) ⟨305163, by rfl⟩ : syracuseStep 813769 = 610327) B610327
theorem B781001 : Blo 99781 781001 := bstep (se 2 (by rfl) ⟨292875, by rfl⟩ : syracuseStep 781001 = 585751) B585751
theorem B256841 : Blo 99781 256841 := bstep (se 2 (by rfl) ⟨96315, by rfl⟩ : syracuseStep 256841 = 192631) B192631
theorem B387935 : Blo 99781 387935 := bstep (se 1 (by rfl) ⟨290951, by rfl⟩ : syracuseStep 387935 = 581903) B581903
theorem B387949 : Blo 99781 387949 := bstep (se 3 (by rfl) ⟨72740, by rfl⟩ : syracuseStep 387949 = 145481) B145481
theorem B191393 : Blo 99781 191393 := bstep (se 2 (by rfl) ⟨71772, by rfl⟩ : syracuseStep 191393 = 143545) B143545
theorem B650359 : Blo 99781 650359 := bstep (se 1 (by rfl) ⟨487769, by rfl⟩ : syracuseStep 650359 = 975539) B975539
theorem B388253 : Blo 99781 388253 := bstep (se 3 (by rfl) ⟨72797, by rfl⟩ : syracuseStep 388253 = 145595) B145595
theorem B191659 : Blo 99781 191659 := bstep (se 1 (by rfl) ⟨143744, by rfl⟩ : syracuseStep 191659 = 287489) B287489
theorem B257195 : Blo 99781 257195 := bstep (se 1 (by rfl) ⟨192896, by rfl⟩ : syracuseStep 257195 = 385793) B385793
theorem B519371 : Blo 99781 519371 := bstep (se 1 (by rfl) ⟨389528, by rfl⟩ : syracuseStep 519371 = 779057) B779057
theorem B191963 : Blo 99781 191963 := bstep (se 1 (by rfl) ⟨143972, by rfl⟩ : syracuseStep 191963 = 287945) B287945
theorem B224891 : Blo 99781 224891 := bstep (se 1 (by rfl) ⟨168668, by rfl⟩ : syracuseStep 224891 = 337337) B337337
theorem B880267 : Blo 99781 880267 := bstep (se 1 (by rfl) ⟨660200, by rfl⟩ : syracuseStep 880267 = 1320401) B1320401
theorem B225017 : Blo 99781 225017 := bstep (se 2 (by rfl) ⟨84381, by rfl⟩ : syracuseStep 225017 = 168763) B168763
theorem B388907 : Blo 99781 388907 := bstep (se 1 (by rfl) ⟨291680, by rfl⟩ : syracuseStep 388907 = 583361) B583361
theorem B323489 : Blo 99781 323489 := bstep (se 2 (by rfl) ⟨121308, by rfl⟩ : syracuseStep 323489 = 242617) B242617
theorem B290735 : Blo 99781 290735 := bstep (se 1 (by rfl) ⟨218051, by rfl⟩ : syracuseStep 290735 = 436103) B436103
theorem B257975 : Blo 99781 257975 := bstep (se 1 (by rfl) ⟨193481, by rfl⟩ : syracuseStep 257975 = 386963) B386963
theorem B225287 : Blo 99781 225287 := bstep (se 1 (by rfl) ⟨168965, by rfl⟩ : syracuseStep 225287 = 337931) B337931
theorem B225359 : Blo 99781 225359 := bstep (se 1 (by rfl) ⟨169019, by rfl⟩ : syracuseStep 225359 = 338039) B338039
theorem B127099 : Blo 99781 127099 := bstep (se 1 (by rfl) ⟨95324, by rfl⟩ : syracuseStep 127099 = 190649) B190649
theorem B160073 : Blo 99781 160073 := bstep (se 2 (by rfl) ⟨60027, by rfl⟩ : syracuseStep 160073 = 120055) B120055
theorem B127327 : Blo 99781 127327 := bstep (se 1 (by rfl) ⟨95495, by rfl⟩ : syracuseStep 127327 = 190991) B190991
theorem B192863 : Blo 99781 192863 := bstep (se 1 (by rfl) ⟨144647, by rfl⟩ : syracuseStep 192863 = 289295) B289295
theorem B160175 : Blo 99781 160175 := bstep (se 1 (by rfl) ⟨120131, by rfl⟩ : syracuseStep 160175 = 240263) B240263
theorem B225755 : Blo 99781 225755 := bstep (se 1 (by rfl) ⟨169316, by rfl⟩ : syracuseStep 225755 = 338633) B338633
theorem B193033 : Blo 99781 193033 := bstep (se 2 (by rfl) ⟨72387, by rfl⟩ : syracuseStep 193033 = 144775) B144775
theorem B324155 : Blo 99781 324155 := bstep (se 1 (by rfl) ⟨243116, by rfl⟩ : syracuseStep 324155 = 486233) B486233
theorem B291691 : Blo 99781 291691 := bstep (se 1 (by rfl) ⟨218768, by rfl⟩ : syracuseStep 291691 = 437537) B437537
theorem B258977 : Blo 99781 258977 := bstep (se 2 (by rfl) ⟨97116, by rfl⟩ : syracuseStep 258977 = 194233) B194233
theorem B226223 : Blo 99781 226223 := bstep (se 1 (by rfl) ⟨169667, by rfl⟩ : syracuseStep 226223 = 339335) B339335
theorem B127919 : Blo 99781 127919 := bstep (se 1 (by rfl) ⟨95939, by rfl⟩ : syracuseStep 127919 = 191879) B191879
theorem B1635329 : Blo 99781 1635329 := bstep (se 2 (by rfl) ⟨613248, by rfl⟩ : syracuseStep 1635329 = 1226497) B1226497
theorem B291919 : Blo 99781 291919 := bstep (se 1 (by rfl) ⟨218939, by rfl⟩ : syracuseStep 291919 = 437879) B437879
theorem B226475 : Blo 99781 226475 := bstep (se 1 (by rfl) ⟨169856, by rfl⟩ : syracuseStep 226475 = 339713) B339713
theorem B193747 : Blo 99781 193747 := bstep (se 1 (by rfl) ⟨145310, by rfl⟩ : syracuseStep 193747 = 290621) B290621
theorem B259433 : Blo 99781 259433 := bstep (se 2 (by rfl) ⟨97287, by rfl⟩ : syracuseStep 259433 = 194575) B194575
theorem B1963379 : Blo 99781 1963379 := bstep (se 1 (by rfl) ⟨1472534, by rfl⟩ : syracuseStep 1963379 = 2945069) B2945069
theorem B587209 : Blo 99781 587209 := bstep (se 2 (by rfl) ⟨220203, by rfl⟩ : syracuseStep 587209 = 440407) B440407
theorem B325129 : Blo 99781 325129 := bstep (se 2 (by rfl) ⟨121923, by rfl⟩ : syracuseStep 325129 = 243847) B243847
theorem B325309 : Blo 99781 325309 := bstep (se 3 (by rfl) ⟨60995, by rfl⟩ : syracuseStep 325309 = 121991) B121991
theorem B227015 : Blo 99781 227015 := bstep (se 1 (by rfl) ⟨170261, by rfl⟩ : syracuseStep 227015 = 340523) B340523
theorem B390865 : Blo 99781 390865 := bstep (se 2 (by rfl) ⟨146574, by rfl⟩ : syracuseStep 390865 = 293149) B293149
theorem B161527 : Blo 99781 161527 := bstep (se 1 (by rfl) ⟨121145, by rfl⟩ : syracuseStep 161527 = 242291) B242291
theorem B390905 : Blo 99781 390905 := bstep (se 2 (by rfl) ⟨146589, by rfl⟩ : syracuseStep 390905 = 293179) B293179
theorem B194491 : Blo 99781 194491 := bstep (se 1 (by rfl) ⟨145868, by rfl⟩ : syracuseStep 194491 = 291737) B291737
theorem B391169 : Blo 99781 391169 := bstep (se 2 (by rfl) ⟨146688, by rfl⟩ : syracuseStep 391169 = 293377) B293377
theorem B162155 : Blo 99781 162155 := bstep (se 1 (by rfl) ⟨121616, by rfl⟩ : syracuseStep 162155 = 243233) B243233
theorem B391553 : Blo 99781 391553 := bstep (se 2 (by rfl) ⟨146832, by rfl⟩ : syracuseStep 391553 = 293665) B293665
theorem B1112453 : Blo 99781 1112453 := bstep (se 4 (by rfl) ⟨104292, by rfl⟩ : syracuseStep 1112453 = 208585) B208585
theorem B194977 : Blo 99781 194977 := bstep (se 2 (by rfl) ⟨73116, by rfl⟩ : syracuseStep 194977 = 146233) B146233
theorem B391625 : Blo 99781 391625 := bstep (se 2 (by rfl) ⟨146859, by rfl⟩ : syracuseStep 391625 = 293719) B293719
theorem B260617 : Blo 99781 260617 := bstep (se 2 (by rfl) ⟨97731, by rfl⟩ : syracuseStep 260617 = 195463) B195463
theorem B227879 : Blo 99781 227879 := bstep (se 1 (by rfl) ⟨170909, by rfl⟩ : syracuseStep 227879 = 341819) B341819
theorem B391889 : Blo 99781 391889 := bstep (se 2 (by rfl) ⟨146958, by rfl⟩ : syracuseStep 391889 = 293917) B293917
theorem B195283 : Blo 99781 195283 := bstep (se 1 (by rfl) ⟨146462, by rfl⟩ : syracuseStep 195283 = 292925) B292925
theorem B326359 : Blo 99781 326359 := bstep (se 1 (by rfl) ⟨244769, by rfl⟩ : syracuseStep 326359 = 489539) B489539
theorem B228203 : Blo 99781 228203 := bstep (se 1 (by rfl) ⟨171152, by rfl⟩ : syracuseStep 228203 = 342305) B342305
theorem B228257 : Blo 99781 228257 := bstep (se 2 (by rfl) ⟨85596, by rfl⟩ : syracuseStep 228257 = 171193) B171193
theorem B392111 : Blo 99781 392111 := bstep (se 1 (by rfl) ⟨294083, by rfl⟩ : syracuseStep 392111 = 588167) B588167
theorem B195547 : Blo 99781 195547 := bstep (se 1 (by rfl) ⟨146660, by rfl⟩ : syracuseStep 195547 = 293321) B293321
theorem B1375427 : Blo 99781 1375427 := bstep (se 1 (by rfl) ⟨1031570, by rfl⟩ : syracuseStep 1375427 = 2063141) B2063141
theorem B228599 : Blo 99781 228599 := bstep (se 1 (by rfl) ⟨171449, by rfl⟩ : syracuseStep 228599 = 342899) B342899
theorem B294425 : Blo 99781 294425 := bstep (se 2 (by rfl) ⟨110409, by rfl⟩ : syracuseStep 294425 = 220819) B220819
theorem B556583 : Blo 99781 556583 := bstep (se 1 (by rfl) ⟨417437, by rfl⟩ : syracuseStep 556583 = 834875) B834875
theorem B163385 : Blo 99781 163385 := bstep (se 2 (by rfl) ⟨61269, by rfl⟩ : syracuseStep 163385 = 122539) B122539
theorem B163577 : Blo 99781 163577 := bstep (se 2 (by rfl) ⟨61341, by rfl⟩ : syracuseStep 163577 = 122683) B122683
theorem B229193 : Blo 99781 229193 := bstep (se 2 (by rfl) ⟨85947, by rfl⟩ : syracuseStep 229193 = 171895) B171895
theorem B262075 : Blo 99781 262075 := bstep (se 1 (by rfl) ⟨196556, by rfl⟩ : syracuseStep 262075 = 393113) B393113
theorem B229481 : Blo 99781 229481 := bstep (se 2 (by rfl) ⟨86055, by rfl⟩ : syracuseStep 229481 = 172111) B172111
theorem B524393 : Blo 99781 524393 := bstep (se 2 (by rfl) ⟨196647, by rfl⟩ : syracuseStep 524393 = 393295) B393295
theorem B262511 : Blo 99781 262511 := bstep (se 1 (by rfl) ⟨196883, by rfl⟩ : syracuseStep 262511 = 393767) B393767
theorem B459209 : Blo 99781 459209 := bstep (se 2 (by rfl) ⟨172203, by rfl⟩ : syracuseStep 459209 = 344407) B344407
theorem B295495 : Blo 99781 295495 := bstep (se 1 (by rfl) ⟨221621, by rfl⟩ : syracuseStep 295495 = 443243) B443243
theorem B229967 : Blo 99781 229967 := bstep (se 1 (by rfl) ⟨172475, by rfl⟩ : syracuseStep 229967 = 344951) B344951
theorem B524983 : Blo 99781 524983 := bstep (se 1 (by rfl) ⟨393737, by rfl⟩ : syracuseStep 524983 = 787475) B787475
theorem B230111 : Blo 99781 230111 := bstep (se 1 (by rfl) ⟨172583, by rfl⟩ : syracuseStep 230111 = 345167) B345167
theorem B885599 : Blo 99781 885599 := bstep (se 1 (by rfl) ⟨664199, by rfl⟩ : syracuseStep 885599 = 1328399) B1328399
theorem B230363 : Blo 99781 230363 := bstep (se 1 (by rfl) ⟨172772, by rfl⟩ : syracuseStep 230363 = 345545) B345545
theorem B427133 : Blo 99781 427133 := bstep (se 3 (by rfl) ⟨80087, by rfl⟩ : syracuseStep 427133 = 160175) B160175
theorem B230543 : Blo 99781 230543 := bstep (se 1 (by rfl) ⟨172907, by rfl⟩ : syracuseStep 230543 = 345815) B345815
theorem B230633 : Blo 99781 230633 := bstep (se 2 (by rfl) ⟨86487, by rfl⟩ : syracuseStep 230633 = 172975) B172975
theorem B230687 : Blo 99781 230687 := bstep (se 1 (by rfl) ⟨173015, by rfl⟩ : syracuseStep 230687 = 346031) B346031
theorem B132391 : Blo 99781 132391 := bstep (se 1 (by rfl) ⟨99293, by rfl⟩ : syracuseStep 132391 = 198587) B198587
theorem B99835 : Blo 99781 99835 := bstep (se 1 (by rfl) ⟨74876, by rfl⟩ : syracuseStep 99835 = 149753) B149753
theorem B99903 : Blo 99781 99903 := bstep (se 1 (by rfl) ⟨74927, by rfl⟩ : syracuseStep 99903 = 149855) B149855
theorem B99911 : Blo 99781 99911 := bstep (se 1 (by rfl) ⟨74933, by rfl⟩ : syracuseStep 99911 = 149867) B149867
theorem B100063 : Blo 99781 100063 := bstep (se 1 (by rfl) ⟨75047, by rfl⟩ : syracuseStep 100063 = 150095) B150095
theorem B2361125 : Blo 99781 2361125 := bstep (se 4 (by rfl) ⟨221355, by rfl⟩ : syracuseStep 2361125 = 442711) B442711
theorem B231209 : Blo 99781 231209 := bstep (se 2 (by rfl) ⟨86703, by rfl⟩ : syracuseStep 231209 = 173407) B173407
theorem B100143 : Blo 99781 100143 := bstep (se 1 (by rfl) ⟨75107, by rfl⟩ : syracuseStep 100143 = 150215) B150215
theorem B1705859 : Blo 99781 1705859 := bstep (se 1 (by rfl) ⟨1279394, by rfl⟩ : syracuseStep 1705859 = 2558789) B2558789
theorem B100251 : Blo 99781 100251 := bstep (se 1 (by rfl) ⟨75188, by rfl⟩ : syracuseStep 100251 = 150377) B150377
theorem B100303 : Blo 99781 100303 := bstep (se 1 (by rfl) ⟨75227, by rfl⟩ : syracuseStep 100303 = 150455) B150455
theorem B100327 : Blo 99781 100327 := bstep (se 1 (by rfl) ⟨75245, by rfl⟩ : syracuseStep 100327 = 150491) B150491
theorem B624905 : Blo 99781 624905 := bstep (se 2 (by rfl) ⟨234339, by rfl⟩ : syracuseStep 624905 = 468679) B468679
theorem B166153 : Blo 99781 166153 := bstep (se 2 (by rfl) ⟨62307, by rfl⟩ : syracuseStep 166153 = 124615) B124615
theorem B559385 : Blo 99781 559385 := bstep (se 2 (by rfl) ⟨209769, by rfl⟩ : syracuseStep 559385 = 419539) B419539
theorem B100639 : Blo 99781 100639 := bstep (se 1 (by rfl) ⟨75479, by rfl⟩ : syracuseStep 100639 = 150959) B150959
theorem B788773 : Blo 99781 788773 := bstep (se 4 (by rfl) ⟨73947, by rfl⟩ : syracuseStep 788773 = 147895) B147895
theorem B100699 : Blo 99781 100699 := bstep (se 1 (by rfl) ⟨75524, by rfl⟩ : syracuseStep 100699 = 151049) B151049
theorem B100719 : Blo 99781 100719 := bstep (se 1 (by rfl) ⟨75539, by rfl⟩ : syracuseStep 100719 = 151079) B151079
theorem B100775 : Blo 99781 100775 := bstep (se 1 (by rfl) ⟨75581, by rfl⟩ : syracuseStep 100775 = 151163) B151163
theorem B100859 : Blo 99781 100859 := bstep (se 1 (by rfl) ⟨75644, by rfl⟩ : syracuseStep 100859 = 151289) B151289
theorem B494075 : Blo 99781 494075 := bstep (se 1 (by rfl) ⟨370556, by rfl⟩ : syracuseStep 494075 = 741113) B741113
theorem B100927 : Blo 99781 100927 := bstep (se 1 (by rfl) ⟨75695, by rfl⟩ : syracuseStep 100927 = 151391) B151391
theorem B100935 : Blo 99781 100935 := bstep (se 1 (by rfl) ⟨75701, by rfl⟩ : syracuseStep 100935 = 151403) B151403
theorem B133807 : Blo 99781 133807 := bstep (se 1 (by rfl) ⟨100355, by rfl⟩ : syracuseStep 133807 = 200711) B200711
theorem B16714421 : Blo 99781 16714421 := bstep (se 5 (by rfl) ⟨783488, by rfl⟩ : syracuseStep 16714421 = 1566977) B1566977
theorem B101087 : Blo 99781 101087 := bstep (se 1 (by rfl) ⟨75815, by rfl⟩ : syracuseStep 101087 = 151631) B151631
theorem B232159 : Blo 99781 232159 := bstep (se 1 (by rfl) ⟨174119, by rfl⟩ : syracuseStep 232159 = 348239) B348239
theorem B101167 : Blo 99781 101167 := bstep (se 1 (by rfl) ⟨75875, by rfl⟩ : syracuseStep 101167 = 151751) B151751
theorem B232271 : Blo 99781 232271 := bstep (se 1 (by rfl) ⟨174203, by rfl⟩ : syracuseStep 232271 = 348407) B348407
theorem B101275 : Blo 99781 101275 := bstep (se 1 (by rfl) ⟨75956, by rfl⟩ : syracuseStep 101275 = 151913) B151913
theorem B101327 : Blo 99781 101327 := bstep (se 1 (by rfl) ⟨75995, by rfl⟩ : syracuseStep 101327 = 151991) B151991
theorem B101351 : Blo 99781 101351 := bstep (se 1 (by rfl) ⟨76013, by rfl⟩ : syracuseStep 101351 = 152027) B152027
theorem B232487 : Blo 99781 232487 := bstep (se 1 (by rfl) ⟨174365, by rfl⟩ : syracuseStep 232487 = 348731) B348731
theorem B232667 : Blo 99781 232667 := bstep (se 1 (by rfl) ⟨174500, by rfl⟩ : syracuseStep 232667 = 349001) B349001
theorem B101663 : Blo 99781 101663 := bstep (se 1 (by rfl) ⟨76247, by rfl⟩ : syracuseStep 101663 = 152495) B152495
theorem B265511 : Blo 99781 265511 := bstep (se 1 (by rfl) ⟨199133, by rfl⟩ : syracuseStep 265511 = 398267) B398267
theorem B101723 : Blo 99781 101723 := bstep (se 1 (by rfl) ⟨76292, by rfl⟩ : syracuseStep 101723 = 152585) B152585
theorem B101743 : Blo 99781 101743 := bstep (se 1 (by rfl) ⟨76307, by rfl⟩ : syracuseStep 101743 = 152615) B152615
theorem B1248641 : Blo 99781 1248641 := bstep (se 2 (by rfl) ⟨468240, by rfl⟩ : syracuseStep 1248641 = 936481) B936481
theorem B232865 : Blo 99781 232865 := bstep (se 2 (by rfl) ⟨87324, by rfl⟩ : syracuseStep 232865 = 174649) B174649
theorem B101799 : Blo 99781 101799 := bstep (se 1 (by rfl) ⟨76349, by rfl⟩ : syracuseStep 101799 = 152699) B152699
theorem B101883 : Blo 99781 101883 := bstep (se 1 (by rfl) ⟨76412, by rfl⟩ : syracuseStep 101883 = 152825) B152825
theorem B101951 : Blo 99781 101951 := bstep (se 1 (by rfl) ⟨76463, by rfl⟩ : syracuseStep 101951 = 152927) B152927
theorem B101959 : Blo 99781 101959 := bstep (se 1 (by rfl) ⟨76469, by rfl⟩ : syracuseStep 101959 = 152939) B152939
theorem B17927831 : Blo 99781 17927831 := bstep (se 1 (by rfl) ⟨13445873, by rfl⟩ : syracuseStep 17927831 = 26891747) B26891747
theorem B462547 : Blo 99781 462547 := bstep (se 1 (by rfl) ⟨346910, by rfl⟩ : syracuseStep 462547 = 693821) B693821
theorem B102111 : Blo 99781 102111 := bstep (se 1 (by rfl) ⟨76583, by rfl⟩ : syracuseStep 102111 = 153167) B153167
theorem B265963 : Blo 99781 265963 := bstep (se 1 (by rfl) ⟨199472, by rfl⟩ : syracuseStep 265963 = 398945) B398945
theorem B102191 : Blo 99781 102191 := bstep (se 1 (by rfl) ⟨76643, by rfl⟩ : syracuseStep 102191 = 153287) B153287
theorem B102299 : Blo 99781 102299 := bstep (se 1 (by rfl) ⟨76724, by rfl⟩ : syracuseStep 102299 = 153449) B153449
theorem B102351 : Blo 99781 102351 := bstep (se 1 (by rfl) ⟨76763, by rfl⟩ : syracuseStep 102351 = 153527) B153527
theorem B233423 : Blo 99781 233423 := bstep (se 1 (by rfl) ⟨175067, by rfl⟩ : syracuseStep 233423 = 350135) B350135
theorem B102375 : Blo 99781 102375 := bstep (se 1 (by rfl) ⟨76781, by rfl⟩ : syracuseStep 102375 = 153563) B153563
theorem B102687 : Blo 99781 102687 := bstep (se 1 (by rfl) ⟨77015, by rfl⟩ : syracuseStep 102687 = 154031) B154031
theorem B102747 : Blo 99781 102747 := bstep (se 1 (by rfl) ⟨77060, by rfl⟩ : syracuseStep 102747 = 154121) B154121
theorem B102767 : Blo 99781 102767 := bstep (se 1 (by rfl) ⟨77075, by rfl⟩ : syracuseStep 102767 = 154151) B154151
theorem B102823 : Blo 99781 102823 := bstep (se 1 (by rfl) ⟨77117, by rfl⟩ : syracuseStep 102823 = 154235) B154235
theorem B102907 : Blo 99781 102907 := bstep (se 1 (by rfl) ⟨77180, by rfl⟩ : syracuseStep 102907 = 154361) B154361
theorem B102975 : Blo 99781 102975 := bstep (se 1 (by rfl) ⟨77231, by rfl⟩ : syracuseStep 102975 = 154463) B154463
theorem B102983 : Blo 99781 102983 := bstep (se 1 (by rfl) ⟨77237, by rfl⟩ : syracuseStep 102983 = 154475) B154475
theorem B103135 : Blo 99781 103135 := bstep (se 1 (by rfl) ⟨77351, by rfl⟩ : syracuseStep 103135 = 154703) B154703
theorem B398047 : Blo 99781 398047 := bstep (se 1 (by rfl) ⟨298535, by rfl⟩ : syracuseStep 398047 = 597071) B597071
theorem B103215 : Blo 99781 103215 := bstep (se 1 (by rfl) ⟨77411, by rfl⟩ : syracuseStep 103215 = 154823) B154823
theorem B103323 : Blo 99781 103323 := bstep (se 1 (by rfl) ⟨77492, by rfl⟩ : syracuseStep 103323 = 154985) B154985
theorem B103375 : Blo 99781 103375 := bstep (se 1 (by rfl) ⟨77531, by rfl⟩ : syracuseStep 103375 = 155063) B155063
theorem B103399 : Blo 99781 103399 := bstep (se 1 (by rfl) ⟨77549, by rfl⟩ : syracuseStep 103399 = 155099) B155099
theorem B103711 : Blo 99781 103711 := bstep (se 1 (by rfl) ⟨77783, by rfl⟩ : syracuseStep 103711 = 155567) B155567
theorem B103771 : Blo 99781 103771 := bstep (se 1 (by rfl) ⟨77828, by rfl⟩ : syracuseStep 103771 = 155657) B155657
theorem B169465 : Blo 99781 169465 := bstep (se 2 (by rfl) ⟨63549, by rfl⟩ : syracuseStep 169465 = 127099) B127099
theorem B5936885 : Blo 99781 5936885 := bstep (se 5 (by rfl) ⟨278291, by rfl⟩ : syracuseStep 5936885 = 556583) B556583
theorem B169735 : Blo 99781 169735 := bstep (se 1 (by rfl) ⟨127301, by rfl⟩ : syracuseStep 169735 = 254603) B254603
theorem B169769 : Blo 99781 169769 := bstep (se 2 (by rfl) ⟨63663, by rfl⟩ : syracuseStep 169769 = 127327) B127327
theorem B366391 : Blo 99781 366391 := bstep (se 1 (by rfl) ⟨274793, by rfl⟩ : syracuseStep 366391 = 549587) B549587
theorem B170491 : Blo 99781 170491 := bstep (se 1 (by rfl) ⟨127868, by rfl⟩ : syracuseStep 170491 = 255737) B255737
theorem B367211 : Blo 99781 367211 := bstep (se 1 (by rfl) ⟨275408, by rfl⟩ : syracuseStep 367211 = 550817) B550817
theorem B498575 : Blo 99781 498575 := bstep (se 1 (by rfl) ⟨373931, by rfl⟩ : syracuseStep 498575 = 747863) B747863
theorem B170923 : Blo 99781 170923 := bstep (se 1 (by rfl) ⟨128192, by rfl⟩ : syracuseStep 170923 = 256385) B256385
theorem B924691 : Blo 99781 924691 := bstep (se 1 (by rfl) ⟨693518, by rfl⟩ : syracuseStep 924691 = 1387037) B1387037
theorem B171227 : Blo 99781 171227 := bstep (se 1 (by rfl) ⟨128420, by rfl⟩ : syracuseStep 171227 = 256841) B256841
theorem B433505 : Blo 99781 433505 := bstep (se 2 (by rfl) ⟨162564, by rfl⟩ : syracuseStep 433505 = 325129) B325129
theorem B171463 : Blo 99781 171463 := bstep (se 1 (by rfl) ⟨128597, by rfl⟩ : syracuseStep 171463 = 257195) B257195
theorem B269831 : Blo 99781 269831 := bstep (se 1 (by rfl) ⟨202373, by rfl⟩ : syracuseStep 269831 = 404747) B404747
theorem B433745 : Blo 99781 433745 := bstep (se 2 (by rfl) ⟨162654, by rfl⟩ : syracuseStep 433745 = 325309) B325309
theorem B171983 : Blo 99781 171983 := bstep (se 1 (by rfl) ⟨128987, by rfl⟩ : syracuseStep 171983 = 257975) B257975
theorem B106715 : Blo 99781 106715 := bstep (se 1 (by rfl) ⟨80036, by rfl⟩ : syracuseStep 106715 = 160073) B160073
theorem B270803 : Blo 99781 270803 := bstep (se 1 (by rfl) ⟨203102, by rfl⟩ : syracuseStep 270803 = 406205) B406205
theorem B270911 : Blo 99781 270911 := bstep (se 1 (by rfl) ⟨203183, by rfl⟩ : syracuseStep 270911 = 406367) B406367
theorem B172651 : Blo 99781 172651 := bstep (se 1 (by rfl) ⟨129488, by rfl⟩ : syracuseStep 172651 = 258977) B258977
theorem B1090219 : Blo 99781 1090219 := bstep (se 1 (by rfl) ⟨817664, by rfl⟩ : syracuseStep 1090219 = 1635329) B1635329
theorem B172955 : Blo 99781 172955 := bstep (se 1 (by rfl) ⟨129716, by rfl⟩ : syracuseStep 172955 = 259433) B259433
theorem B435145 : Blo 99781 435145 := bstep (se 2 (by rfl) ⟨163179, by rfl⟩ : syracuseStep 435145 = 326359) B326359
theorem B271603 : Blo 99781 271603 := bstep (se 1 (by rfl) ⟨203702, by rfl⟩ : syracuseStep 271603 = 407405) B407405
theorem B108103 : Blo 99781 108103 := bstep (se 1 (by rfl) ⟨81077, by rfl⟩ : syracuseStep 108103 = 162155) B162155
theorem B337769 : Blo 99781 337769 := bstep (se 2 (by rfl) ⟨126663, by rfl⟩ : syracuseStep 337769 = 253327) B253327
theorem B436205 : Blo 99781 436205 := bstep (se 3 (by rfl) ⟨81788, by rfl⟩ : syracuseStep 436205 = 163577) B163577
theorem B1058831 : Blo 99781 1058831 := bstep (se 1 (by rfl) ⟨794123, by rfl⟩ : syracuseStep 1058831 = 1588247) B1588247
theorem B338201 : Blo 99781 338201 := bstep (se 2 (by rfl) ⟨126825, by rfl⟩ : syracuseStep 338201 = 253651) B253651
theorem B108923 : Blo 99781 108923 := bstep (se 1 (by rfl) ⟨81692, by rfl⟩ : syracuseStep 108923 = 163385) B163385
theorem B306163 : Blo 99781 306163 := bstep (se 1 (by rfl) ⟨229622, by rfl⟩ : syracuseStep 306163 = 459245) B459245
theorem B1485863 : Blo 99781 1485863 := bstep (se 1 (by rfl) ⟨1114397, by rfl⟩ : syracuseStep 1485863 = 2228795) B2228795
theorem B765449 : Blo 99781 765449 := bstep (se 2 (by rfl) ⟨287043, by rfl⟩ : syracuseStep 765449 = 574087) B574087
theorem B339551 : Blo 99781 339551 := bstep (se 1 (by rfl) ⟨254663, by rfl⟩ : syracuseStep 339551 = 509327) B509327
theorem B438281 : Blo 99781 438281 := bstep (se 2 (by rfl) ⟨164355, by rfl⟩ : syracuseStep 438281 = 328711) B328711
theorem B438803 : Blo 99781 438803 := bstep (se 1 (by rfl) ⟨329102, by rfl⟩ : syracuseStep 438803 = 658205) B658205
theorem B340955 : Blo 99781 340955 := bstep (se 1 (by rfl) ⟨255716, by rfl⟩ : syracuseStep 340955 = 511433) B511433
theorem B341117 : Blo 99781 341117 := bstep (se 3 (by rfl) ⟨63959, by rfl⟩ : syracuseStep 341117 = 127919) B127919
theorem B341225 : Blo 99781 341225 := bstep (se 2 (by rfl) ⟨127959, by rfl⟩ : syracuseStep 341225 = 255919) B255919
theorem B341387 : Blo 99781 341387 := bstep (se 1 (by rfl) ⟨256040, by rfl⟩ : syracuseStep 341387 = 512081) B512081
theorem B767393 : Blo 99781 767393 := bstep (se 2 (by rfl) ⟨287772, by rfl⟩ : syracuseStep 767393 = 575545) B575545
theorem B505277 : Blo 99781 505277 := bstep (se 3 (by rfl) ⟨94739, by rfl⟩ : syracuseStep 505277 = 189479) B189479
theorem B112351 : Blo 99781 112351 := bstep (se 1 (by rfl) ⟨84263, by rfl⟩ : syracuseStep 112351 = 168527) B168527
theorem B1325117 : Blo 99781 1325117 := bstep (se 3 (by rfl) ⟨248459, by rfl⟩ : syracuseStep 1325117 = 496919) B496919
theorem B112927 : Blo 99781 112927 := bstep (se 1 (by rfl) ⟨84695, by rfl⟩ : syracuseStep 112927 = 169391) B169391
theorem B244079 : Blo 99781 244079 := bstep (se 1 (by rfl) ⟨183059, by rfl⟩ : syracuseStep 244079 = 366119) B366119
theorem B4340101 : Blo 99781 4340101 := bstep (se 4 (by rfl) ⟨406884, by rfl⟩ : syracuseStep 4340101 = 813769) B813769
theorem B113215 : Blo 99781 113215 := bstep (se 1 (by rfl) ⟨84911, by rfl⟩ : syracuseStep 113215 = 169823) B169823
theorem B965357 : Blo 99781 965357 := bstep (se 3 (by rfl) ⟨181004, by rfl⟩ : syracuseStep 965357 = 362009) B362009
theorem B867145 : Blo 99781 867145 := bstep (se 2 (by rfl) ⟨325179, by rfl⟩ : syracuseStep 867145 = 650359) B650359
theorem B114043 : Blo 99781 114043 := bstep (se 1 (by rfl) ⟨85532, by rfl⟩ : syracuseStep 114043 = 171065) B171065
theorem B671291 : Blo 99781 671291 := bstep (se 1 (by rfl) ⟨503468, by rfl⟩ : syracuseStep 671291 = 1006937) B1006937
theorem B343667 : Blo 99781 343667 := bstep (se 1 (by rfl) ⟨257750, by rfl⟩ : syracuseStep 343667 = 515501) B515501
theorem B868103 : Blo 99781 868103 := bstep (se 1 (by rfl) ⟨651077, by rfl⟩ : syracuseStep 868103 = 1302155) B1302155
theorem B442169 : Blo 99781 442169 := bstep (se 2 (by rfl) ⟨165813, by rfl⟩ : syracuseStep 442169 = 331627) B331627
theorem B114511 : Blo 99781 114511 := bstep (se 1 (by rfl) ⟨85883, by rfl⟩ : syracuseStep 114511 = 171767) B171767
theorem B442219 : Blo 99781 442219 := bstep (se 1 (by rfl) ⟨331664, by rfl⟩ : syracuseStep 442219 = 663329) B663329
theorem B278633 : Blo 99781 278633 := bstep (se 2 (by rfl) ⟨104487, by rfl⟩ : syracuseStep 278633 = 208975) B208975
theorem B966775 : Blo 99781 966775 := bstep (se 1 (by rfl) ⟨725081, by rfl⟩ : syracuseStep 966775 = 1450163) B1450163
theorem B114907 : Blo 99781 114907 := bstep (se 1 (by rfl) ⟨86180, by rfl⟩ : syracuseStep 114907 = 172361) B172361
theorem B344411 : Blo 99781 344411 := bstep (se 1 (by rfl) ⟨258308, by rfl⟩ : syracuseStep 344411 = 516617) B516617
theorem B541129 : Blo 99781 541129 := bstep (se 2 (by rfl) ⟨202923, by rfl⟩ : syracuseStep 541129 = 405847) B405847
theorem B115195 : Blo 99781 115195 := bstep (se 1 (by rfl) ⟨86396, by rfl⟩ : syracuseStep 115195 = 172793) B172793
theorem B311879 : Blo 99781 311879 := bstep (se 1 (by rfl) ⟨233909, by rfl⟩ : syracuseStep 311879 = 467819) B467819
theorem B115375 : Blo 99781 115375 := bstep (se 1 (by rfl) ⟨86531, by rfl⟩ : syracuseStep 115375 = 173063) B173063
theorem B279215 : Blo 99781 279215 := bstep (se 1 (by rfl) ⟨209411, by rfl⟩ : syracuseStep 279215 = 418823) B418823
theorem B115663 : Blo 99781 115663 := bstep (se 1 (by rfl) ⟨86747, by rfl⟩ : syracuseStep 115663 = 173495) B173495
theorem B640007 : Blo 99781 640007 := bstep (se 1 (by rfl) ⟨480005, by rfl⟩ : syracuseStep 640007 = 960011) B960011
theorem B214139 : Blo 99781 214139 := bstep (se 1 (by rfl) ⟨160604, by rfl⟩ : syracuseStep 214139 = 321209) B321209
theorem B705779 : Blo 99781 705779 := bstep (se 1 (by rfl) ⟨529334, by rfl⟩ : syracuseStep 705779 = 1058669) B1058669
theorem B345383 : Blo 99781 345383 := bstep (se 1 (by rfl) ⟨259037, by rfl⟩ : syracuseStep 345383 = 518075) B518075
theorem B116059 : Blo 99781 116059 := bstep (se 1 (by rfl) ⟨87044, by rfl⟩ : syracuseStep 116059 = 174089) B174089
theorem B2377133 : Blo 99781 2377133 := bstep (se 3 (by rfl) ⟨445712, by rfl⟩ : syracuseStep 2377133 = 891425) B891425
theorem B116167 : Blo 99781 116167 := bstep (se 1 (by rfl) ⟨87125, by rfl⟩ : syracuseStep 116167 = 174251) B174251
theorem B116527 : Blo 99781 116527 := bstep (se 1 (by rfl) ⟨87395, by rfl⟩ : syracuseStep 116527 = 174791) B174791
theorem B116635 : Blo 99781 116635 := bstep (se 1 (by rfl) ⟨87476, by rfl⟩ : syracuseStep 116635 = 174953) B174953
theorem B1034167 : Blo 99781 1034167 := bstep (se 1 (by rfl) ⟨775625, by rfl⟩ : syracuseStep 1034167 = 1551251) B1551251
theorem B346247 : Blo 99781 346247 := bstep (se 1 (by rfl) ⟨259685, by rfl⟩ : syracuseStep 346247 = 519371) B519371
theorem B510137 : Blo 99781 510137 := bstep (se 2 (by rfl) ⟨191301, by rfl⟩ : syracuseStep 510137 = 382603) B382603
theorem B215369 : Blo 99781 215369 := bstep (se 2 (by rfl) ⟨80763, by rfl⟩ : syracuseStep 215369 = 161527) B161527
theorem B149927 : Blo 99781 149927 := bstep (se 1 (by rfl) ⟨112445, by rfl⟩ : syracuseStep 149927 = 224891) B224891
theorem B150011 : Blo 99781 150011 := bstep (se 1 (by rfl) ⟨112508, by rfl⟩ : syracuseStep 150011 = 225017) B225017
theorem B215659 : Blo 99781 215659 := bstep (se 1 (by rfl) ⟨161744, by rfl⟩ : syracuseStep 215659 = 323489) B323489
theorem B150137 : Blo 99781 150137 := bstep (se 2 (by rfl) ⟨56301, by rfl⟩ : syracuseStep 150137 = 112603) B112603
theorem B150191 : Blo 99781 150191 := bstep (se 1 (by rfl) ⟨112643, by rfl⟩ : syracuseStep 150191 = 225287) B225287
theorem B150239 : Blo 99781 150239 := bstep (se 1 (by rfl) ⟨112679, by rfl⟩ : syracuseStep 150239 = 225359) B225359
theorem B150503 : Blo 99781 150503 := bstep (se 1 (by rfl) ⟨112877, by rfl⟩ : syracuseStep 150503 = 225755) B225755
theorem B216103 : Blo 99781 216103 := bstep (se 1 (by rfl) ⟨162077, by rfl⟩ : syracuseStep 216103 = 324155) B324155
theorem B150761 : Blo 99781 150761 := bstep (se 2 (by rfl) ⟨56535, by rfl⟩ : syracuseStep 150761 = 113071) B113071
theorem B150815 : Blo 99781 150815 := bstep (se 1 (by rfl) ⟨113111, by rfl⟩ : syracuseStep 150815 = 226223) B226223
theorem B838943 : Blo 99781 838943 := bstep (se 1 (by rfl) ⟨629207, by rfl⟩ : syracuseStep 838943 = 1258415) B1258415
theorem B347489 : Blo 99781 347489 := bstep (se 2 (by rfl) ⟨130308, by rfl⟩ : syracuseStep 347489 = 260617) B260617
theorem B150983 : Blo 99781 150983 := bstep (se 1 (by rfl) ⟨113237, by rfl⟩ : syracuseStep 150983 = 226475) B226475
theorem B151337 : Blo 99781 151337 := bstep (se 2 (by rfl) ⟨56751, by rfl⟩ : syracuseStep 151337 = 113503) B113503
theorem B151343 : Blo 99781 151343 := bstep (se 1 (by rfl) ⟨113507, by rfl⟩ : syracuseStep 151343 = 227015) B227015
theorem B511919 : Blo 99781 511919 := bstep (se 1 (by rfl) ⟨383939, by rfl⟩ : syracuseStep 511919 = 767879) B767879
theorem B741635 : Blo 99781 741635 := bstep (se 1 (by rfl) ⟨556226, by rfl⟩ : syracuseStep 741635 = 1112453) B1112453
theorem B151817 : Blo 99781 151817 := bstep (se 2 (by rfl) ⟨56931, by rfl⟩ : syracuseStep 151817 = 113863) B113863
theorem B151919 : Blo 99781 151919 := bstep (se 1 (by rfl) ⟨113939, by rfl⟩ : syracuseStep 151919 = 227879) B227879
theorem B938557 : Blo 99781 938557 := bstep (se 3 (by rfl) ⟨175979, by rfl⟩ : syracuseStep 938557 = 351959) B351959
theorem B709181 : Blo 99781 709181 := bstep (se 3 (by rfl) ⟨132971, by rfl⟩ : syracuseStep 709181 = 265943) B265943
theorem B152135 : Blo 99781 152135 := bstep (se 1 (by rfl) ⟨114101, by rfl⟩ : syracuseStep 152135 = 228203) B228203
theorem B152171 : Blo 99781 152171 := bstep (se 1 (by rfl) ⟨114128, by rfl⟩ : syracuseStep 152171 = 228257) B228257
theorem B250643 : Blo 99781 250643 := bstep (se 1 (by rfl) ⟨187982, by rfl⟩ : syracuseStep 250643 = 375965) B375965
theorem B152399 : Blo 99781 152399 := bstep (se 1 (by rfl) ⟨114299, by rfl⟩ : syracuseStep 152399 = 228599) B228599
theorem B152795 : Blo 99781 152795 := bstep (se 1 (by rfl) ⟨114596, by rfl⟩ : syracuseStep 152795 = 229193) B229193
theorem B349433 : Blo 99781 349433 := bstep (se 2 (by rfl) ⟨131037, by rfl⟩ : syracuseStep 349433 = 262075) B262075
theorem B972121 : Blo 99781 972121 := bstep (se 2 (by rfl) ⟨364545, by rfl⟩ : syracuseStep 972121 = 729091) B729091
theorem B152969 : Blo 99781 152969 := bstep (se 2 (by rfl) ⟨57363, by rfl⟩ : syracuseStep 152969 = 114727) B114727
theorem B480775 : Blo 99781 480775 := bstep (se 1 (by rfl) ⟨360581, by rfl⟩ : syracuseStep 480775 = 721163) B721163
theorem B349703 : Blo 99781 349703 := bstep (se 1 (by rfl) ⟨262277, by rfl⟩ : syracuseStep 349703 = 524555) B524555
theorem B153323 : Blo 99781 153323 := bstep (se 1 (by rfl) ⟨114992, by rfl⟩ : syracuseStep 153323 = 229985) B229985
theorem B153551 : Blo 99781 153551 := bstep (se 1 (by rfl) ⟨115163, by rfl⟩ : syracuseStep 153551 = 230327) B230327
theorem B219145 : Blo 99781 219145 := bstep (se 2 (by rfl) ⟨82179, by rfl⟩ : syracuseStep 219145 = 164359) B164359
theorem B2840777 : Blo 99781 2840777 := bstep (se 2 (by rfl) ⟨1065291, by rfl⟩ : syracuseStep 2840777 = 2130583) B2130583
theorem B973079 : Blo 99781 973079 := bstep (se 1 (by rfl) ⟨729809, by rfl⟩ : syracuseStep 973079 = 1459619) B1459619
theorem B153947 : Blo 99781 153947 := bstep (se 1 (by rfl) ⟨115460, by rfl⟩ : syracuseStep 153947 = 230921) B230921
theorem B186835 : Blo 99781 186835 := bstep (se 1 (by rfl) ⟨140126, by rfl⟩ : syracuseStep 186835 = 280253) B280253
theorem B154175 : Blo 99781 154175 := bstep (se 1 (by rfl) ⟨115631, by rfl⟩ : syracuseStep 154175 = 231263) B231263
theorem B383561 : Blo 99781 383561 := bstep (se 2 (by rfl) ⟨143835, by rfl⟩ : syracuseStep 383561 = 287671) B287671
theorem B154295 : Blo 99781 154295 := bstep (se 1 (by rfl) ⟨115721, by rfl⟩ : syracuseStep 154295 = 231443) B231443
theorem B744173 : Blo 99781 744173 := bstep (se 3 (by rfl) ⟨139532, by rfl⟩ : syracuseStep 744173 = 279065) B279065
theorem B514835 : Blo 99781 514835 := bstep (se 1 (by rfl) ⟨386126, by rfl⟩ : syracuseStep 514835 = 772253) B772253
theorem B154523 : Blo 99781 154523 := bstep (se 1 (by rfl) ⟨115892, by rfl⟩ : syracuseStep 154523 = 231785) B231785
theorem B482219 : Blo 99781 482219 := bstep (se 1 (by rfl) ⟨361664, by rfl⟩ : syracuseStep 482219 = 723329) B723329
theorem B220409 : Blo 99781 220409 := bstep (se 2 (by rfl) ⟨82653, by rfl⟩ : syracuseStep 220409 = 165307) B165307
theorem B154919 : Blo 99781 154919 := bstep (se 1 (by rfl) ⟨116189, by rfl⟩ : syracuseStep 154919 = 232379) B232379
theorem B253307 : Blo 99781 253307 := bstep (se 1 (by rfl) ⟨189980, by rfl⟩ : syracuseStep 253307 = 379961) B379961
theorem B155003 : Blo 99781 155003 := bstep (se 1 (by rfl) ⟨116252, by rfl⟩ : syracuseStep 155003 = 232505) B232505
theorem B155129 : Blo 99781 155129 := bstep (se 2 (by rfl) ⟨58173, by rfl⟩ : syracuseStep 155129 = 116347) B116347
theorem B155231 : Blo 99781 155231 := bstep (se 1 (by rfl) ⟨116423, by rfl⟩ : syracuseStep 155231 = 232847) B232847
theorem B253601 : Blo 99781 253601 := bstep (se 2 (by rfl) ⟨95100, by rfl⟩ : syracuseStep 253601 = 190201) B190201
theorem B155447 : Blo 99781 155447 := bstep (se 1 (by rfl) ⟨116585, by rfl⟩ : syracuseStep 155447 = 233171) B233171
theorem B548669 : Blo 99781 548669 := bstep (se 3 (by rfl) ⟨102875, by rfl⟩ : syracuseStep 548669 = 205751) B205751
theorem B515969 : Blo 99781 515969 := bstep (se 2 (by rfl) ⟨193488, by rfl⟩ : syracuseStep 515969 = 386977) B386977
theorem B2908163 : Blo 99781 2908163 := bstep (se 1 (by rfl) ⟨2181122, by rfl⟩ : syracuseStep 2908163 = 4362245) B4362245
theorem B1138697 : Blo 99781 1138697 := bstep (se 2 (by rfl) ⟨427011, by rfl⟩ : syracuseStep 1138697 = 854023) B854023
theorem B385033 : Blo 99781 385033 := bstep (se 2 (by rfl) ⟨144387, by rfl⟩ : syracuseStep 385033 = 288775) B288775
theorem B581651 : Blo 99781 581651 := bstep (se 1 (by rfl) ⟨436238, by rfl⟩ : syracuseStep 581651 = 872477) B872477
theorem B876851 : Blo 99781 876851 := bstep (se 1 (by rfl) ⟨657638, by rfl⟩ : syracuseStep 876851 = 1315277) B1315277
theorem B254299 : Blo 99781 254299 := bstep (se 1 (by rfl) ⟨190724, by rfl⟩ : syracuseStep 254299 = 381449) B381449
theorem B385505 : Blo 99781 385505 := bstep (se 2 (by rfl) ⟨144564, by rfl⟩ : syracuseStep 385505 = 289129) B289129
theorem B516779 : Blo 99781 516779 := bstep (se 1 (by rfl) ⟨387584, by rfl⟩ : syracuseStep 516779 = 775169) B775169
theorem B320183 : Blo 99781 320183 := bstep (se 1 (by rfl) ⟨240137, by rfl⟩ : syracuseStep 320183 = 480275) B480275
theorem B549827 : Blo 99781 549827 := bstep (se 1 (by rfl) ⟨412370, by rfl⟩ : syracuseStep 549827 = 824741) B824741
theorem B975847 : Blo 99781 975847 := bstep (se 1 (by rfl) ⟨731885, by rfl⟩ : syracuseStep 975847 = 1463771) B1463771
theorem B287887 : Blo 99781 287887 := bstep (se 1 (by rfl) ⟨215915, by rfl⟩ : syracuseStep 287887 = 431831) B431831
theorem B517265 : Blo 99781 517265 := bstep (se 2 (by rfl) ⟨193974, by rfl⟩ : syracuseStep 517265 = 387949) B387949
theorem B255271 : Blo 99781 255271 := bstep (se 1 (by rfl) ⟨191453, by rfl⟩ : syracuseStep 255271 = 382907) B382907
theorem B288161 : Blo 99781 288161 := bstep (se 2 (by rfl) ⟨108060, by rfl⟩ : syracuseStep 288161 = 216121) B216121
theorem B255545 : Blo 99781 255545 := bstep (se 2 (by rfl) ⟨95829, by rfl⟩ : syracuseStep 255545 = 191659) B191659
theorem B1173689 : Blo 99781 1173689 := bstep (se 2 (by rfl) ⟨440133, by rfl⟩ : syracuseStep 1173689 = 880267) B880267
theorem B420025 : Blo 99781 420025 := bstep (se 2 (by rfl) ⟨157509, by rfl⟩ : syracuseStep 420025 = 315019) B315019
theorem B190831 : Blo 99781 190831 := bstep (se 1 (by rfl) ⟨143123, by rfl⟩ : syracuseStep 190831 = 286247) B286247
theorem B584819 : Blo 99781 584819 := bstep (se 1 (by rfl) ⟨438614, by rfl⟩ : syracuseStep 584819 = 877229) B877229
theorem B126299 : Blo 99781 126299 := bstep (se 1 (by rfl) ⟨94724, by rfl⟩ : syracuseStep 126299 = 189449) B189449
theorem B257377 : Blo 99781 257377 := bstep (se 2 (by rfl) ⟨96516, by rfl⟩ : syracuseStep 257377 = 193033) B193033
theorem B224711 : Blo 99781 224711 := bstep (se 1 (by rfl) ⟨168533, by rfl⟩ : syracuseStep 224711 = 337067) B337067
theorem B880091 : Blo 99781 880091 := bstep (se 1 (by rfl) ⟨660068, by rfl⟩ : syracuseStep 880091 = 1320137) B1320137
theorem B519695 : Blo 99781 519695 := bstep (se 1 (by rfl) ⟨389771, by rfl⟩ : syracuseStep 519695 = 779543) B779543
theorem B225071 : Blo 99781 225071 := bstep (se 1 (by rfl) ⟨168803, by rfl⟩ : syracuseStep 225071 = 337607) B337607
theorem B126775 : Blo 99781 126775 := bstep (se 1 (by rfl) ⟨95081, by rfl⟩ : syracuseStep 126775 = 190163) B190163
theorem B388921 : Blo 99781 388921 := bstep (se 2 (by rfl) ⟨145845, by rfl⟩ : syracuseStep 388921 = 291691) B291691
theorem B880541 : Blo 99781 880541 := bstep (se 3 (by rfl) ⟨165101, by rfl⟩ : syracuseStep 880541 = 330203) B330203
theorem B389225 : Blo 99781 389225 := bstep (se 2 (by rfl) ⟨145959, by rfl⟩ : syracuseStep 389225 = 291919) B291919
theorem B3141899 : Blo 99781 3141899 := bstep (se 1 (by rfl) ⟨2356424, by rfl⟩ : syracuseStep 3141899 = 4712849) B4712849
theorem B258329 : Blo 99781 258329 := bstep (se 2 (by rfl) ⟨96873, by rfl⟩ : syracuseStep 258329 = 193747) B193747
theorem B127271 : Blo 99781 127271 := bstep (se 1 (by rfl) ⟨95453, by rfl⟩ : syracuseStep 127271 = 190907) B190907
theorem B225647 : Blo 99781 225647 := bstep (se 1 (by rfl) ⟨169235, by rfl⟩ : syracuseStep 225647 = 338471) B338471
theorem B192935 : Blo 99781 192935 := bstep (se 1 (by rfl) ⟨144701, by rfl⟩ : syracuseStep 192935 = 289403) B289403
theorem B225719 : Blo 99781 225719 := bstep (se 1 (by rfl) ⟨169289, by rfl⟩ : syracuseStep 225719 = 338579) B338579
theorem B520667 : Blo 99781 520667 := bstep (se 1 (by rfl) ⟨390500, by rfl⟩ : syracuseStep 520667 = 781001) B781001
theorem B1045037 : Blo 99781 1045037 := bstep (se 3 (by rfl) ⟨195944, by rfl⟩ : syracuseStep 1045037 = 391889) B391889
theorem B258623 : Blo 99781 258623 := bstep (se 1 (by rfl) ⟨193967, by rfl⟩ : syracuseStep 258623 = 387935) B387935
theorem B225863 : Blo 99781 225863 := bstep (se 1 (by rfl) ⟨169397, by rfl⟩ : syracuseStep 225863 = 338795) B338795
theorem B782945 : Blo 99781 782945 := bstep (se 2 (by rfl) ⟨293604, by rfl⟩ : syracuseStep 782945 = 587209) B587209
theorem B225899 : Blo 99781 225899 := bstep (se 1 (by rfl) ⟨169424, by rfl⟩ : syracuseStep 225899 = 338849) B338849
theorem B127595 : Blo 99781 127595 := bstep (se 1 (by rfl) ⟨95696, by rfl⟩ : syracuseStep 127595 = 191393) B191393
theorem B258835 : Blo 99781 258835 := bstep (se 1 (by rfl) ⟨194126, by rfl⟩ : syracuseStep 258835 = 388253) B388253
theorem B160591 : Blo 99781 160591 := bstep (se 1 (by rfl) ⟨120443, by rfl⟩ : syracuseStep 160591 = 240887) B240887
theorem B521153 : Blo 99781 521153 := bstep (se 2 (by rfl) ⟨195432, by rfl⟩ : syracuseStep 521153 = 390865) B390865
theorem B127975 : Blo 99781 127975 := bstep (se 1 (by rfl) ⟨95981, by rfl⟩ : syracuseStep 127975 = 191963) B191963
theorem B226295 : Blo 99781 226295 := bstep (se 1 (by rfl) ⟨169721, by rfl⟩ : syracuseStep 226295 = 339443) B339443
theorem B259271 : Blo 99781 259271 := bstep (se 1 (by rfl) ⟨194453, by rfl⟩ : syracuseStep 259271 = 388907) B388907
theorem B259321 : Blo 99781 259321 := bstep (se 2 (by rfl) ⟨97245, by rfl⟩ : syracuseStep 259321 = 194491) B194491
theorem B193823 : Blo 99781 193823 := bstep (se 1 (by rfl) ⟨145367, by rfl⟩ : syracuseStep 193823 = 290735) B290735
theorem B226655 : Blo 99781 226655 := bstep (se 1 (by rfl) ⟨169991, by rfl⟩ : syracuseStep 226655 = 339983) B339983
theorem B128575 : Blo 99781 128575 := bstep (se 1 (by rfl) ⟨96431, by rfl⟩ : syracuseStep 128575 = 192863) B192863
theorem B4159127 : Blo 99781 4159127 := bstep (se 1 (by rfl) ⟨3119345, by rfl⟩ : syracuseStep 4159127 = 6238691) B6238691
theorem B227051 : Blo 99781 227051 := bstep (se 1 (by rfl) ⟨170288, by rfl⟩ : syracuseStep 227051 = 340577) B340577
theorem B3667805 : Blo 99781 3667805 := bstep (se 3 (by rfl) ⟨687713, by rfl⟩ : syracuseStep 3667805 = 1375427) B1375427
theorem B227177 : Blo 99781 227177 := bstep (se 2 (by rfl) ⟨85191, by rfl⟩ : syracuseStep 227177 = 170383) B170383
theorem B259969 : Blo 99781 259969 := bstep (se 2 (by rfl) ⟨97488, by rfl⟩ : syracuseStep 259969 = 194977) B194977
theorem B1308919 : Blo 99781 1308919 := bstep (se 1 (by rfl) ⟨981689, by rfl⟩ : syracuseStep 1308919 = 1963379) B1963379
theorem B194825 : Blo 99781 194825 := bstep (se 2 (by rfl) ⟨73059, by rfl⟩ : syracuseStep 194825 = 146119) B146119
theorem B260377 : Blo 99781 260377 := bstep (se 2 (by rfl) ⟨97641, by rfl⟩ : syracuseStep 260377 = 195283) B195283
theorem B1800629 : Blo 99781 1800629 := bstep (se 5 (by rfl) ⟨84404, by rfl⟩ : syracuseStep 1800629 = 168809) B168809
theorem B260603 : Blo 99781 260603 := bstep (se 1 (by rfl) ⟨195452, by rfl⟩ : syracuseStep 260603 = 390905) B390905
theorem B260729 : Blo 99781 260729 := bstep (se 2 (by rfl) ⟨97773, by rfl⟩ : syracuseStep 260729 = 195547) B195547
theorem B260779 : Blo 99781 260779 := bstep (se 1 (by rfl) ⟨195584, by rfl⟩ : syracuseStep 260779 = 391169) B391169
theorem B228023 : Blo 99781 228023 := bstep (se 1 (by rfl) ⟨171017, by rfl⟩ : syracuseStep 228023 = 342035) B342035
theorem B293651 : Blo 99781 293651 := bstep (se 1 (by rfl) ⟨220238, by rfl⟩ : syracuseStep 293651 = 440477) B440477
theorem B228239 : Blo 99781 228239 := bstep (se 1 (by rfl) ⟨171179, by rfl⟩ : syracuseStep 228239 = 342359) B342359
theorem B261035 : Blo 99781 261035 := bstep (se 1 (by rfl) ⟨195776, by rfl⟩ : syracuseStep 261035 = 391553) B391553
theorem B261083 : Blo 99781 261083 := bstep (se 1 (by rfl) ⟨195812, by rfl⟩ : syracuseStep 261083 = 391625) B391625
theorem B261407 : Blo 99781 261407 := bstep (se 1 (by rfl) ⟨196055, by rfl⟩ : syracuseStep 261407 = 392111) B392111
theorem B359747 : Blo 99781 359747 := bstep (se 1 (by rfl) ⟨269810, by rfl⟩ : syracuseStep 359747 = 539621) B539621
theorem B589193 : Blo 99781 589193 := bstep (se 2 (by rfl) ⟨220947, by rfl⟩ : syracuseStep 589193 = 441895) B441895
theorem B228959 : Blo 99781 228959 := bstep (se 1 (by rfl) ⟨171719, by rfl⟩ : syracuseStep 228959 = 343439) B343439
theorem B196283 : Blo 99781 196283 := bstep (se 1 (by rfl) ⟨147212, by rfl⟩ : syracuseStep 196283 = 294425) B294425
theorem B229175 : Blo 99781 229175 := bstep (se 1 (by rfl) ⟨171881, by rfl⟩ : syracuseStep 229175 = 343763) B343763
theorem B884641 : Blo 99781 884641 := bstep (se 2 (by rfl) ⟨331740, by rfl⟩ : syracuseStep 884641 = 663481) B663481
theorem B229607 : Blo 99781 229607 := bstep (se 1 (by rfl) ⟨172205, by rfl⟩ : syracuseStep 229607 = 344411) B344411
theorem B590399 : Blo 99781 590399 := bstep (se 1 (by rfl) ⟨442799, by rfl⟩ : syracuseStep 590399 = 885599) B885599
theorem B721505 : Blo 99781 721505 := bstep (se 2 (by rfl) ⟨270564, by rfl⟩ : syracuseStep 721505 = 541129) B541129
theorem B426671 : Blo 99781 426671 := bstep (se 1 (by rfl) ⟨320003, by rfl⟩ : syracuseStep 426671 = 640007) B640007
theorem B230201 : Blo 99781 230201 := bstep (se 2 (by rfl) ⟨86325, by rfl⟩ : syracuseStep 230201 = 172651) B172651
theorem B230255 : Blo 99781 230255 := bstep (se 1 (by rfl) ⟨172691, by rfl⟩ : syracuseStep 230255 = 345383) B345383
theorem B1574083 : Blo 99781 1574083 := bstep (se 1 (by rfl) ⟨1180562, by rfl⟩ : syracuseStep 1574083 = 2361125) B2361125
theorem B230831 : Blo 99781 230831 := bstep (se 1 (by rfl) ⟨173123, by rfl⟩ : syracuseStep 230831 = 346247) B346247
theorem B722429 : Blo 99781 722429 := bstep (se 3 (by rfl) ⟨135455, by rfl⟩ : syracuseStep 722429 = 270911) B270911
theorem B99951 : Blo 99781 99951 := bstep (se 1 (by rfl) ⟨74963, by rfl⟩ : syracuseStep 99951 = 149927) B149927
theorem B362137 : Blo 99781 362137 := bstep (se 2 (by rfl) ⟨135801, by rfl⟩ : syracuseStep 362137 = 271603) B271603
theorem B100007 : Blo 99781 100007 := bstep (se 1 (by rfl) ⟨75005, by rfl⟩ : syracuseStep 100007 = 150011) B150011
theorem B329383 : Blo 99781 329383 := bstep (se 1 (by rfl) ⟨247037, by rfl⟩ : syracuseStep 329383 = 494075) B494075
theorem B100091 : Blo 99781 100091 := bstep (se 1 (by rfl) ⟨75068, by rfl⟩ : syracuseStep 100091 = 150137) B150137
theorem B100127 : Blo 99781 100127 := bstep (se 1 (by rfl) ⟨75095, by rfl⟩ : syracuseStep 100127 = 150191) B150191
theorem B11142947 : Blo 99781 11142947 := bstep (se 1 (by rfl) ⟨8357210, by rfl⟩ : syracuseStep 11142947 = 16714421) B16714421
theorem B100159 : Blo 99781 100159 := bstep (se 1 (by rfl) ⟨75119, by rfl⟩ : syracuseStep 100159 = 150239) B150239
theorem B100335 : Blo 99781 100335 := bstep (se 1 (by rfl) ⟨75251, by rfl⟩ : syracuseStep 100335 = 150503) B150503
theorem B100507 : Blo 99781 100507 := bstep (se 1 (by rfl) ⟨75380, by rfl⟩ : syracuseStep 100507 = 150761) B150761
theorem B100543 : Blo 99781 100543 := bstep (se 1 (by rfl) ⟨75407, by rfl⟩ : syracuseStep 100543 = 150815) B150815
theorem B559295 : Blo 99781 559295 := bstep (se 1 (by rfl) ⟨419471, by rfl⟩ : syracuseStep 559295 = 838943) B838943
theorem B231659 : Blo 99781 231659 := bstep (se 1 (by rfl) ⟨173744, by rfl⟩ : syracuseStep 231659 = 347489) B347489
theorem B100655 : Blo 99781 100655 := bstep (se 1 (by rfl) ⟨75491, by rfl⟩ : syracuseStep 100655 = 150983) B150983
theorem B100891 : Blo 99781 100891 := bstep (se 1 (by rfl) ⟨75668, by rfl⟩ : syracuseStep 100891 = 151337) B151337
theorem B100895 : Blo 99781 100895 := bstep (se 1 (by rfl) ⟨75671, by rfl⟩ : syracuseStep 100895 = 151343) B151343
theorem B1378889 : Blo 99781 1378889 := bstep (se 2 (by rfl) ⟨517083, by rfl⟩ : syracuseStep 1378889 = 1034167) B1034167
theorem B494423 : Blo 99781 494423 := bstep (se 1 (by rfl) ⟨370817, by rfl⟩ : syracuseStep 494423 = 741635) B741635
theorem B101211 : Blo 99781 101211 := bstep (se 1 (by rfl) ⟨75908, by rfl⟩ : syracuseStep 101211 = 151817) B151817
theorem B101279 : Blo 99781 101279 := bstep (se 1 (by rfl) ⟨75959, by rfl⟩ : syracuseStep 101279 = 151919) B151919
theorem B560033 : Blo 99781 560033 := bstep (se 2 (by rfl) ⟨210012, by rfl⟩ : syracuseStep 560033 = 420025) B420025
theorem B1575973 : Blo 99781 1575973 := bstep (se 4 (by rfl) ⟨147747, by rfl⟩ : syracuseStep 1575973 = 295495) B295495
theorem B101423 : Blo 99781 101423 := bstep (se 1 (by rfl) ⟨76067, by rfl⟩ : syracuseStep 101423 = 152135) B152135
theorem B1051697 : Blo 99781 1051697 := bstep (se 2 (by rfl) ⟨394386, by rfl⟩ : syracuseStep 1051697 = 788773) B788773
theorem B101447 : Blo 99781 101447 := bstep (se 1 (by rfl) ⟨76085, by rfl⟩ : syracuseStep 101447 = 152171) B152171
theorem B167095 : Blo 99781 167095 := bstep (se 1 (by rfl) ⟨125321, by rfl⟩ : syracuseStep 167095 = 250643) B250643
theorem B101599 : Blo 99781 101599 := bstep (se 1 (by rfl) ⟨76199, by rfl⟩ : syracuseStep 101599 = 152399) B152399
theorem B101863 : Blo 99781 101863 := bstep (se 1 (by rfl) ⟨76397, by rfl⟩ : syracuseStep 101863 = 152795) B152795
theorem B232955 : Blo 99781 232955 := bstep (se 1 (by rfl) ⟨174716, by rfl⟩ : syracuseStep 232955 = 349433) B349433
theorem B101979 : Blo 99781 101979 := bstep (se 1 (by rfl) ⟨76484, by rfl⟩ : syracuseStep 101979 = 152969) B152969
theorem B233135 : Blo 99781 233135 := bstep (se 1 (by rfl) ⟨174851, by rfl⟩ : syracuseStep 233135 = 349703) B349703
theorem B102215 : Blo 99781 102215 := bstep (se 1 (by rfl) ⟨76661, by rfl⟩ : syracuseStep 102215 = 153323) B153323
theorem B102367 : Blo 99781 102367 := bstep (se 1 (by rfl) ⟨76775, by rfl⟩ : syracuseStep 102367 = 153551) B153551
theorem B102631 : Blo 99781 102631 := bstep (se 1 (by rfl) ⟨76973, by rfl⟩ : syracuseStep 102631 = 153947) B153947
theorem B102783 : Blo 99781 102783 := bstep (se 1 (by rfl) ⟨77087, by rfl⟩ : syracuseStep 102783 = 154175) B154175
theorem B102863 : Blo 99781 102863 := bstep (se 1 (by rfl) ⟨77147, by rfl⟩ : syracuseStep 102863 = 154295) B154295
theorem B496115 : Blo 99781 496115 := bstep (se 1 (by rfl) ⟨372086, by rfl⟩ : syracuseStep 496115 = 744173) B744173
theorem B332383 : Blo 99781 332383 := bstep (se 1 (by rfl) ⟨249287, by rfl⟩ : syracuseStep 332383 = 498575) B498575
theorem B103015 : Blo 99781 103015 := bstep (se 1 (by rfl) ⟨77261, by rfl⟩ : syracuseStep 103015 = 154523) B154523
theorem B103279 : Blo 99781 103279 := bstep (se 1 (by rfl) ⟨77459, by rfl⟩ : syracuseStep 103279 = 154919) B154919
theorem B168871 : Blo 99781 168871 := bstep (se 1 (by rfl) ⟨126653, by rfl⟩ : syracuseStep 168871 = 253307) B253307
theorem B103335 : Blo 99781 103335 := bstep (se 1 (by rfl) ⟨77501, by rfl⟩ : syracuseStep 103335 = 155003) B155003
theorem B103419 : Blo 99781 103419 := bstep (se 1 (by rfl) ⟨77564, by rfl⟩ : syracuseStep 103419 = 155129) B155129
theorem B103487 : Blo 99781 103487 := bstep (se 1 (by rfl) ⟨77615, by rfl⟩ : syracuseStep 103487 = 155231) B155231
theorem B169033 : Blo 99781 169033 := bstep (se 2 (by rfl) ⟨63387, by rfl⟩ : syracuseStep 169033 = 126775) B126775
theorem B169067 : Blo 99781 169067 := bstep (se 1 (by rfl) ⟨126800, by rfl⟩ : syracuseStep 169067 = 253601) B253601
theorem B103631 : Blo 99781 103631 := bstep (se 1 (by rfl) ⟨77723, by rfl⟩ : syracuseStep 103631 = 155447) B155447
theorem B365779 : Blo 99781 365779 := bstep (se 1 (by rfl) ⟨274334, by rfl⟩ : syracuseStep 365779 = 548669) B548669
theorem B1938775 : Blo 99781 1938775 := bstep (se 1 (by rfl) ⟨1454081, by rfl⟩ : syracuseStep 1938775 = 2908163) B2908163
theorem B759131 : Blo 99781 759131 := bstep (se 1 (by rfl) ⟨569348, by rfl⟩ : syracuseStep 759131 = 1138697) B1138697
theorem B366551 : Blo 99781 366551 := bstep (se 1 (by rfl) ⟨274913, by rfl⟩ : syracuseStep 366551 = 549827) B549827
theorem B1251409 : Blo 99781 1251409 := bstep (se 2 (by rfl) ⟨469278, by rfl⟩ : syracuseStep 1251409 = 938557) B938557
theorem B530729 : Blo 99781 530729 := bstep (se 2 (by rfl) ⟨199023, by rfl⟩ : syracuseStep 530729 = 398047) B398047
theorem B170363 : Blo 99781 170363 := bstep (se 1 (by rfl) ⟨127772, by rfl⟩ : syracuseStep 170363 = 255545) B255545
theorem B170633 : Blo 99781 170633 := bstep (se 2 (by rfl) ⟨63987, by rfl⟩ : syracuseStep 170633 = 127975) B127975
theorem B990575 : Blo 99781 990575 := bstep (se 1 (by rfl) ⟨742931, by rfl⟩ : syracuseStep 990575 = 1485863) B1485863
theorem B171433 : Blo 99781 171433 := bstep (se 2 (by rfl) ⟨64287, by rfl⟩ : syracuseStep 171433 = 128575) B128575
theorem B172219 : Blo 99781 172219 := bstep (se 1 (by rfl) ⟨129164, by rfl⟩ : syracuseStep 172219 = 258329) B258329
theorem B1745225 : Blo 99781 1745225 := bstep (se 2 (by rfl) ⟨654459, by rfl⟩ : syracuseStep 1745225 = 1308919) B1308919
theorem B696691 : Blo 99781 696691 := bstep (se 1 (by rfl) ⟨522518, by rfl⟩ : syracuseStep 696691 = 1045037) B1045037
theorem B172415 : Blo 99781 172415 := bstep (se 1 (by rfl) ⟨129311, by rfl⟩ : syracuseStep 172415 = 258623) B258623
theorem B172847 : Blo 99781 172847 := bstep (se 1 (by rfl) ⟨129635, by rfl⟩ : syracuseStep 172847 = 259271) B259271
theorem B336797 : Blo 99781 336797 := bstep (se 3 (by rfl) ⟨63149, by rfl⟩ : syracuseStep 336797 = 126299) B126299
theorem B336851 : Blo 99781 336851 := bstep (se 1 (by rfl) ⟨252638, by rfl⟩ : syracuseStep 336851 = 505277) B505277
theorem B1156193 : Blo 99781 1156193 := bstep (se 2 (by rfl) ⟨433572, by rfl⟩ : syracuseStep 1156193 = 867145) B867145
theorem B173735 : Blo 99781 173735 := bstep (se 1 (by rfl) ⟨130301, by rfl⟩ : syracuseStep 173735 = 260603) B260603
theorem B173819 : Blo 99781 173819 := bstep (se 1 (by rfl) ⟨130364, by rfl⟩ : syracuseStep 173819 = 260729) B260729
theorem B174023 : Blo 99781 174023 := bstep (se 1 (by rfl) ⟨130517, by rfl⟩ : syracuseStep 174023 = 261035) B261035
theorem B174055 : Blo 99781 174055 := bstep (se 1 (by rfl) ⟨130541, by rfl⟩ : syracuseStep 174055 = 261083) B261083
theorem B174271 : Blo 99781 174271 := bstep (se 1 (by rfl) ⟨130703, by rfl⟩ : syracuseStep 174271 = 261407) B261407
theorem B239831 : Blo 99781 239831 := bstep (se 1 (by rfl) ⟨179873, by rfl⟩ : syracuseStep 239831 = 359747) B359747
theorem B1289033 : Blo 99781 1289033 := bstep (se 2 (by rfl) ⟨483387, by rfl⟩ : syracuseStep 1289033 = 966775) B966775
theorem B175007 : Blo 99781 175007 := bstep (se 1 (by rfl) ⟨131255, by rfl⟩ : syracuseStep 175007 = 262511) B262511
theorem B306139 : Blo 99781 306139 := bstep (se 1 (by rfl) ⟨229604, by rfl⟩ : syracuseStep 306139 = 459209) B459209
theorem B207919 : Blo 99781 207919 := bstep (se 1 (by rfl) ⟨155939, by rfl⟩ : syracuseStep 207919 = 311879) B311879
theorem B339065 : Blo 99781 339065 := bstep (se 2 (by rfl) ⟨127149, by rfl⟩ : syracuseStep 339065 = 254299) B254299
theorem B142759 : Blo 99781 142759 := bstep (se 1 (by rfl) ⟨107069, by rfl⟩ : syracuseStep 142759 = 214139) B214139
theorem B339389 : Blo 99781 339389 := bstep (se 3 (by rfl) ⟨63635, by rfl⟩ : syracuseStep 339389 = 127271) B127271
theorem B470519 : Blo 99781 470519 := bstep (se 1 (by rfl) ⟨352889, by rfl⟩ : syracuseStep 470519 = 705779) B705779
theorem B1453625 : Blo 99781 1453625 := bstep (se 2 (by rfl) ⟨545109, by rfl⟩ : syracuseStep 1453625 = 1090219) B1090219
theorem B699977 : Blo 99781 699977 := bstep (se 2 (by rfl) ⟨262491, by rfl⟩ : syracuseStep 699977 = 524983) B524983
theorem B1584755 : Blo 99781 1584755 := bstep (se 1 (by rfl) ⟨1188566, by rfl⟩ : syracuseStep 1584755 = 2377133) B2377133
theorem B340091 : Blo 99781 340091 := bstep (se 1 (by rfl) ⟨255068, by rfl⟩ : syracuseStep 340091 = 510137) B510137
theorem B1388677 : Blo 99781 1388677 := bstep (se 4 (by rfl) ⟨130188, by rfl⟩ : syracuseStep 1388677 = 260377) B260377
theorem B372923 : Blo 99781 372923 := bstep (se 1 (by rfl) ⟨279692, by rfl⟩ : syracuseStep 372923 = 559385) B559385
theorem B143579 : Blo 99781 143579 := bstep (se 1 (by rfl) ⟨107684, by rfl⟩ : syracuseStep 143579 = 215369) B215369
theorem B340253 : Blo 99781 340253 := bstep (se 3 (by rfl) ⟨63797, by rfl⟩ : syracuseStep 340253 = 127595) B127595
theorem B340361 : Blo 99781 340361 := bstep (se 2 (by rfl) ⟨127635, by rfl⟩ : syracuseStep 340361 = 255271) B255271
theorem B176521 : Blo 99781 176521 := bstep (se 2 (by rfl) ⟨66195, by rfl⟩ : syracuseStep 176521 = 132391) B132391
theorem B144137 : Blo 99781 144137 := bstep (se 2 (by rfl) ⟨54051, by rfl⟩ : syracuseStep 144137 = 108103) B108103
theorem B177007 : Blo 99781 177007 := bstep (se 1 (by rfl) ⟨132755, by rfl⟩ : syracuseStep 177007 = 265511) B265511
theorem B832427 : Blo 99781 832427 := bstep (se 1 (by rfl) ⟨624320, by rfl⟩ : syracuseStep 832427 = 1248641) B1248641
theorem B341279 : Blo 99781 341279 := bstep (se 1 (by rfl) ⟨255959, by rfl⟩ : syracuseStep 341279 = 511919) B511919
theorem B472787 : Blo 99781 472787 := bstep (se 1 (by rfl) ⟨354590, by rfl⟩ : syracuseStep 472787 = 709181) B709181
theorem B178409 : Blo 99781 178409 := bstep (se 2 (by rfl) ⟨66903, by rfl⟩ : syracuseStep 178409 = 133807) B133807
theorem B309545 : Blo 99781 309545 := bstep (se 2 (by rfl) ⟨116079, by rfl⟩ : syracuseStep 309545 = 232159) B232159
theorem B113179 : Blo 99781 113179 := bstep (se 1 (by rfl) ⟨84884, by rfl⟩ : syracuseStep 113179 = 169769) B169769
theorem B343169 : Blo 99781 343169 := bstep (se 2 (by rfl) ⟨128688, by rfl⟩ : syracuseStep 343169 = 257377) B257377
theorem B343223 : Blo 99781 343223 := bstep (se 1 (by rfl) ⟨257417, by rfl⟩ : syracuseStep 343223 = 514835) B514835
theorem B114151 : Blo 99781 114151 := bstep (se 1 (by rfl) ⟨85613, by rfl⟩ : syracuseStep 114151 = 171227) B171227
theorem B146939 : Blo 99781 146939 := bstep (se 1 (by rfl) ⟨110204, by rfl⟩ : syracuseStep 146939 = 220409) B220409
theorem B179887 : Blo 99781 179887 := bstep (se 1 (by rfl) ⟨134915, by rfl⟩ : syracuseStep 179887 = 269831) B269831
theorem B343979 : Blo 99781 343979 := bstep (se 1 (by rfl) ⟨257984, by rfl⟩ : syracuseStep 343979 = 515969) B515969
theorem B114655 : Blo 99781 114655 := bstep (se 1 (by rfl) ⟨85991, by rfl⟩ : syracuseStep 114655 = 171983) B171983
theorem B180535 : Blo 99781 180535 := bstep (se 1 (by rfl) ⟨135401, by rfl⟩ : syracuseStep 180535 = 270803) B270803
theorem B344519 : Blo 99781 344519 := bstep (se 1 (by rfl) ⟨258389, by rfl⟩ : syracuseStep 344519 = 516779) B516779
theorem B213455 : Blo 99781 213455 := bstep (se 1 (by rfl) ⟨160091, by rfl⟩ : syracuseStep 213455 = 320183) B320183
theorem B115303 : Blo 99781 115303 := bstep (se 1 (by rfl) ⟨86477, by rfl⟩ : syracuseStep 115303 = 172955) B172955
theorem B344843 : Blo 99781 344843 := bstep (se 1 (by rfl) ⟨258632, by rfl⟩ : syracuseStep 344843 = 517265) B517265
theorem B345113 : Blo 99781 345113 := bstep (se 2 (by rfl) ⟨129417, by rfl⟩ : syracuseStep 345113 = 258835) B258835
theorem B214121 : Blo 99781 214121 := bstep (se 2 (by rfl) ⟨80295, by rfl⟩ : syracuseStep 214121 = 160591) B160591
theorem B705887 : Blo 99781 705887 := bstep (se 1 (by rfl) ⟨529415, by rfl⟩ : syracuseStep 705887 = 1058831) B1058831
theorem B345761 : Blo 99781 345761 := bstep (se 2 (by rfl) ⟨129660, by rfl⟩ : syracuseStep 345761 = 259321) B259321
theorem B1296161 : Blo 99781 1296161 := bstep (se 2 (by rfl) ⟨486060, by rfl⟩ : syracuseStep 1296161 = 972121) B972121
theorem B641033 : Blo 99781 641033 := bstep (se 2 (by rfl) ⟨240387, by rfl⟩ : syracuseStep 641033 = 480775) B480775
theorem B149801 : Blo 99781 149801 := bstep (se 2 (by rfl) ⟨56175, by rfl⟩ : syracuseStep 149801 = 112351) B112351
theorem B149807 : Blo 99781 149807 := bstep (se 1 (by rfl) ⟨112355, by rfl⟩ : syracuseStep 149807 = 224711) B224711
theorem B510299 : Blo 99781 510299 := bstep (se 1 (by rfl) ⟨382724, by rfl⟩ : syracuseStep 510299 = 765449) B765449
theorem B346463 : Blo 99781 346463 := bstep (se 1 (by rfl) ⟨259847, by rfl⟩ : syracuseStep 346463 = 519695) B519695
theorem B346625 : Blo 99781 346625 := bstep (se 2 (by rfl) ⟨129984, by rfl⟩ : syracuseStep 346625 = 259969) B259969
theorem B150047 : Blo 99781 150047 := bstep (se 1 (by rfl) ⟨112535, by rfl⟩ : syracuseStep 150047 = 225071) B225071
theorem B150431 : Blo 99781 150431 := bstep (se 1 (by rfl) ⟨112823, by rfl⟩ : syracuseStep 150431 = 225647) B225647
theorem B150479 : Blo 99781 150479 := bstep (se 1 (by rfl) ⟨112859, by rfl⟩ : syracuseStep 150479 = 225719) B225719
theorem B347111 : Blo 99781 347111 := bstep (se 1 (by rfl) ⟨260333, by rfl⟩ : syracuseStep 347111 = 520667) B520667
theorem B150569 : Blo 99781 150569 := bstep (se 2 (by rfl) ⟨56463, by rfl⟩ : syracuseStep 150569 = 112927) B112927
theorem B150575 : Blo 99781 150575 := bstep (se 1 (by rfl) ⟨112931, by rfl⟩ : syracuseStep 150575 = 225863) B225863
theorem B150599 : Blo 99781 150599 := bstep (se 1 (by rfl) ⟨112949, by rfl⟩ : syracuseStep 150599 = 225899) B225899
theorem B5786801 : Blo 99781 5786801 := bstep (se 2 (by rfl) ⟨2170050, by rfl⟩ : syracuseStep 5786801 = 4340101) B4340101
theorem B249113 : Blo 99781 249113 := bstep (se 2 (by rfl) ⟨93417, by rfl⟩ : syracuseStep 249113 = 186835) B186835
theorem B347435 : Blo 99781 347435 := bstep (se 1 (by rfl) ⟨260576, by rfl⟩ : syracuseStep 347435 = 521153) B521153
theorem B150863 : Blo 99781 150863 := bstep (se 1 (by rfl) ⟨113147, by rfl⟩ : syracuseStep 150863 = 226295) B226295
theorem B150953 : Blo 99781 150953 := bstep (se 2 (by rfl) ⟨56607, by rfl⟩ : syracuseStep 150953 = 113215) B113215
theorem B347705 : Blo 99781 347705 := bstep (se 2 (by rfl) ⟨130389, by rfl⟩ : syracuseStep 347705 = 260779) B260779
theorem B151103 : Blo 99781 151103 := bstep (se 1 (by rfl) ⟨113327, by rfl⟩ : syracuseStep 151103 = 226655) B226655
theorem B511595 : Blo 99781 511595 := bstep (se 1 (by rfl) ⟨383696, by rfl⟩ : syracuseStep 511595 = 767393) B767393
theorem B2772751 : Blo 99781 2772751 := bstep (se 1 (by rfl) ⟨2079563, by rfl⟩ : syracuseStep 2772751 = 4159127) B4159127
theorem B151367 : Blo 99781 151367 := bstep (se 1 (by rfl) ⟨113525, by rfl⟩ : syracuseStep 151367 = 227051) B227051
theorem B2445203 : Blo 99781 2445203 := bstep (se 1 (by rfl) ⟨1833902, by rfl⟩ : syracuseStep 2445203 = 3667805) B3667805
theorem B151451 : Blo 99781 151451 := bstep (se 1 (by rfl) ⟨113588, by rfl⟩ : syracuseStep 151451 = 227177) B227177
theorem B1232921 : Blo 99781 1232921 := bstep (se 2 (by rfl) ⟨462345, by rfl⟩ : syracuseStep 1232921 = 924691) B924691
theorem B1200419 : Blo 99781 1200419 := bstep (se 1 (by rfl) ⟨900314, by rfl⟩ : syracuseStep 1200419 = 1800629) B1800629
theorem B152015 : Blo 99781 152015 := bstep (se 1 (by rfl) ⟨114011, by rfl⟩ : syracuseStep 152015 = 228023) B228023
theorem B643571 : Blo 99781 643571 := bstep (se 1 (by rfl) ⟨482678, by rfl⟩ : syracuseStep 643571 = 965357) B965357
theorem B152057 : Blo 99781 152057 := bstep (se 2 (by rfl) ⟨57021, by rfl⟩ : syracuseStep 152057 = 114043) B114043
theorem B152159 : Blo 99781 152159 := bstep (se 1 (by rfl) ⟨114119, by rfl⟩ : syracuseStep 152159 = 228239) B228239
theorem B447527 : Blo 99781 447527 := bstep (se 1 (by rfl) ⟨335645, by rfl⟩ : syracuseStep 447527 = 671291) B671291
theorem B152639 : Blo 99781 152639 := bstep (se 1 (by rfl) ⟨114479, by rfl⟩ : syracuseStep 152639 = 228959) B228959
theorem B152681 : Blo 99781 152681 := bstep (se 2 (by rfl) ⟨57255, by rfl⟩ : syracuseStep 152681 = 114511) B114511
theorem B578735 : Blo 99781 578735 := bstep (se 1 (by rfl) ⟨434051, by rfl⟩ : syracuseStep 578735 = 868103) B868103
theorem B152783 : Blo 99781 152783 := bstep (se 1 (by rfl) ⟨114587, by rfl⟩ : syracuseStep 152783 = 229175) B229175
theorem B513377 : Blo 99781 513377 := bstep (se 2 (by rfl) ⟨192516, by rfl⟩ : syracuseStep 513377 = 385033) B385033
theorem B152987 : Blo 99781 152987 := bstep (se 1 (by rfl) ⟨114740, by rfl⟩ : syracuseStep 152987 = 229481) B229481
theorem B185755 : Blo 99781 185755 := bstep (se 1 (by rfl) ⟨139316, by rfl⟩ : syracuseStep 185755 = 278633) B278633
theorem B349595 : Blo 99781 349595 := bstep (se 1 (by rfl) ⟨262196, by rfl⟩ : syracuseStep 349595 = 524393) B524393
theorem B153209 : Blo 99781 153209 := bstep (se 2 (by rfl) ⟨57453, by rfl⟩ : syracuseStep 153209 = 114907) B114907
theorem B153311 : Blo 99781 153311 := bstep (se 1 (by rfl) ⟨114983, by rfl⟩ : syracuseStep 153311 = 229967) B229967
theorem B186143 : Blo 99781 186143 := bstep (se 1 (by rfl) ⟨139607, by rfl⟩ : syracuseStep 186143 = 279215) B279215
theorem B153407 : Blo 99781 153407 := bstep (se 1 (by rfl) ⟨115055, by rfl⟩ : syracuseStep 153407 = 230111) B230111
theorem B284573 : Blo 99781 284573 := bstep (se 3 (by rfl) ⟨53357, by rfl⟩ : syracuseStep 284573 = 106715) B106715
theorem B153575 : Blo 99781 153575 := bstep (se 1 (by rfl) ⟨115181, by rfl⟩ : syracuseStep 153575 = 230363) B230363
theorem B153593 : Blo 99781 153593 := bstep (se 2 (by rfl) ⟨57597, by rfl⟩ : syracuseStep 153593 = 115195) B115195
theorem B284755 : Blo 99781 284755 := bstep (se 1 (by rfl) ⟨213566, by rfl⟩ : syracuseStep 284755 = 427133) B427133
theorem B153695 : Blo 99781 153695 := bstep (se 1 (by rfl) ⟨115271, by rfl⟩ : syracuseStep 153695 = 230543) B230543
theorem B153755 : Blo 99781 153755 := bstep (se 1 (by rfl) ⟨115316, by rfl⟩ : syracuseStep 153755 = 230633) B230633
theorem B153791 : Blo 99781 153791 := bstep (se 1 (by rfl) ⟨115343, by rfl⟩ : syracuseStep 153791 = 230687) B230687
theorem B153833 : Blo 99781 153833 := bstep (se 2 (by rfl) ⟨57687, by rfl⟩ : syracuseStep 153833 = 115375) B115375
theorem B154139 : Blo 99781 154139 := bstep (se 1 (by rfl) ⟨115604, by rfl⟩ : syracuseStep 154139 = 231209) B231209
theorem B1137239 : Blo 99781 1137239 := bstep (se 1 (by rfl) ⟨852929, by rfl⟩ : syracuseStep 1137239 = 1705859) B1705859
theorem B580193 : Blo 99781 580193 := bstep (se 2 (by rfl) ⟨217572, by rfl⟩ : syracuseStep 580193 = 435145) B435145
theorem B154217 : Blo 99781 154217 := bstep (se 2 (by rfl) ⟨57831, by rfl⟩ : syracuseStep 154217 = 115663) B115663
theorem B1301129 : Blo 99781 1301129 := bstep (se 2 (by rfl) ⟨487923, by rfl⟩ : syracuseStep 1301129 = 975847) B975847
theorem B416603 : Blo 99781 416603 := bstep (se 1 (by rfl) ⟨312452, by rfl⟩ : syracuseStep 416603 = 624905) B624905
theorem B383849 : Blo 99781 383849 := bstep (se 2 (by rfl) ⟨143943, by rfl⟩ : syracuseStep 383849 = 287887) B287887
theorem B154745 : Blo 99781 154745 := bstep (se 2 (by rfl) ⟨58029, by rfl⟩ : syracuseStep 154745 = 116059) B116059
theorem B154847 : Blo 99781 154847 := bstep (se 1 (by rfl) ⟨116135, by rfl⟩ : syracuseStep 154847 = 232271) B232271
theorem B154889 : Blo 99781 154889 := bstep (se 2 (by rfl) ⟨58083, by rfl⟩ : syracuseStep 154889 = 116167) B116167
theorem B154991 : Blo 99781 154991 := bstep (se 1 (by rfl) ⟨116243, by rfl⟩ : syracuseStep 154991 = 232487) B232487
theorem B155111 : Blo 99781 155111 := bstep (se 1 (by rfl) ⟨116333, by rfl⟩ : syracuseStep 155111 = 232667) B232667
theorem B155243 : Blo 99781 155243 := bstep (se 1 (by rfl) ⟨116432, by rfl⟩ : syracuseStep 155243 = 232865) B232865
theorem B155369 : Blo 99781 155369 := bstep (se 2 (by rfl) ⟨58263, by rfl⟩ : syracuseStep 155369 = 116527) B116527
theorem B11951887 : Blo 99781 11951887 := bstep (se 1 (by rfl) ⟨8963915, by rfl⟩ : syracuseStep 11951887 = 17927831) B17927831
theorem B155513 : Blo 99781 155513 := bstep (se 2 (by rfl) ⟨58317, by rfl⟩ : syracuseStep 155513 = 116635) B116635
theorem B155615 : Blo 99781 155615 := bstep (se 1 (by rfl) ⟨116711, by rfl⟩ : syracuseStep 155615 = 233423) B233423
theorem B221537 : Blo 99781 221537 := bstep (se 2 (by rfl) ⟨83076, by rfl⟩ : syracuseStep 221537 = 166153) B166153
theorem B254441 : Blo 99781 254441 := bstep (se 2 (by rfl) ⟨95415, by rfl⟩ : syracuseStep 254441 = 190831) B190831
theorem B287545 : Blo 99781 287545 := bstep (se 2 (by rfl) ⟨107829, by rfl⟩ : syracuseStep 287545 = 215659) B215659
theorem B3957923 : Blo 99781 3957923 := bstep (se 1 (by rfl) ⟨2968442, by rfl⟩ : syracuseStep 3957923 = 5936885) B5936885
theorem B288137 : Blo 99781 288137 := bstep (se 2 (by rfl) ⟨108051, by rfl⟩ : syracuseStep 288137 = 216103) B216103
theorem B1893851 : Blo 99781 1893851 := bstep (se 1 (by rfl) ⟨1420388, by rfl⟩ : syracuseStep 1893851 = 2840777) B2840777
theorem B648719 : Blo 99781 648719 := bstep (se 1 (by rfl) ⟨486539, by rfl⟩ : syracuseStep 648719 = 973079) B973079
theorem B255707 : Blo 99781 255707 := bstep (se 1 (by rfl) ⟨191780, by rfl⟩ : syracuseStep 255707 = 383561) B383561
theorem B321479 : Blo 99781 321479 := bstep (se 1 (by rfl) ⟨241109, by rfl⟩ : syracuseStep 321479 = 482219) B482219
theorem B289003 : Blo 99781 289003 := bstep (se 1 (by rfl) ⟨216752, by rfl⟩ : syracuseStep 289003 = 433505) B433505
theorem B616729 : Blo 99781 616729 := bstep (se 2 (by rfl) ⟨231273, by rfl⟩ : syracuseStep 616729 = 462547) B462547
theorem B354617 : Blo 99781 354617 := bstep (se 2 (by rfl) ⟨132981, by rfl⟩ : syracuseStep 354617 = 265963) B265963
theorem B289163 : Blo 99781 289163 := bstep (se 1 (by rfl) ⟨216872, by rfl⟩ : syracuseStep 289163 = 433745) B433745
theorem B518561 : Blo 99781 518561 := bstep (se 2 (by rfl) ⟨194460, by rfl⟩ : syracuseStep 518561 = 388921) B388921
theorem B1632869 : Blo 99781 1632869 := bstep (se 4 (by rfl) ⟨153081, by rfl⟩ : syracuseStep 1632869 = 306163) B306163
theorem B387767 : Blo 99781 387767 := bstep (se 1 (by rfl) ⟨290825, by rfl⟩ : syracuseStep 387767 = 581651) B581651
theorem B3533645 : Blo 99781 3533645 := bstep (se 3 (by rfl) ⟨662558, by rfl⟩ : syracuseStep 3533645 = 1325117) B1325117
theorem B584567 : Blo 99781 584567 := bstep (se 1 (by rfl) ⟨438425, by rfl⟩ : syracuseStep 584567 = 876851) B876851
theorem B257003 : Blo 99781 257003 := bstep (se 1 (by rfl) ⟨192752, by rfl⟩ : syracuseStep 257003 = 385505) B385505
theorem B519533 : Blo 99781 519533 := bstep (se 3 (by rfl) ⟨97412, by rfl⟩ : syracuseStep 519533 = 194825) B194825
theorem B192107 : Blo 99781 192107 := bstep (se 1 (by rfl) ⟨144080, by rfl⟩ : syracuseStep 192107 = 288161) B288161
theorem B290461 : Blo 99781 290461 := bstep (se 3 (by rfl) ⟨54461, by rfl⟩ : syracuseStep 290461 = 108923) B108923
theorem B225179 : Blo 99781 225179 := bstep (se 1 (by rfl) ⟨168884, by rfl⟩ : syracuseStep 225179 = 337769) B337769
theorem B290803 : Blo 99781 290803 := bstep (se 1 (by rfl) ⟨218102, by rfl⟩ : syracuseStep 290803 = 436205) B436205
theorem B782459 : Blo 99781 782459 := bstep (se 1 (by rfl) ⟨586844, by rfl⟩ : syracuseStep 782459 = 1173689) B1173689
theorem B225467 : Blo 99781 225467 := bstep (se 1 (by rfl) ⟨169100, by rfl⟩ : syracuseStep 225467 = 338201) B338201
theorem B979229 : Blo 99781 979229 := bstep (se 3 (by rfl) ⟨183605, by rfl⟩ : syracuseStep 979229 = 367211) B367211
theorem B225953 : Blo 99781 225953 := bstep (se 2 (by rfl) ⟨84732, by rfl⟩ : syracuseStep 225953 = 169465) B169465
theorem B389879 : Blo 99781 389879 := bstep (se 1 (by rfl) ⟨292409, by rfl⟩ : syracuseStep 389879 = 584819) B584819
theorem B586727 : Blo 99781 586727 := bstep (se 1 (by rfl) ⟨440045, by rfl⟩ : syracuseStep 586727 = 880091) B880091
theorem B226313 : Blo 99781 226313 := bstep (se 2 (by rfl) ⟨84867, by rfl⟩ : syracuseStep 226313 = 169735) B169735
theorem B226367 : Blo 99781 226367 := bstep (se 1 (by rfl) ⟨169775, by rfl⟩ : syracuseStep 226367 = 339551) B339551
theorem B488521 : Blo 99781 488521 := bstep (se 2 (by rfl) ⟨183195, by rfl⟩ : syracuseStep 488521 = 366391) B366391
theorem B587027 : Blo 99781 587027 := bstep (se 1 (by rfl) ⟨440270, by rfl⟩ : syracuseStep 587027 = 880541) B880541
theorem B292187 : Blo 99781 292187 := bstep (se 1 (by rfl) ⟨219140, by rfl⟩ : syracuseStep 292187 = 438281) B438281
theorem B292193 : Blo 99781 292193 := bstep (se 2 (by rfl) ⟨109572, by rfl⟩ : syracuseStep 292193 = 219145) B219145
theorem B259483 : Blo 99781 259483 := bstep (se 1 (by rfl) ⟨194612, by rfl⟩ : syracuseStep 259483 = 389225) B389225
theorem B2094599 : Blo 99781 2094599 := bstep (se 1 (by rfl) ⟨1570949, by rfl⟩ : syracuseStep 2094599 = 3141899) B3141899
theorem B128623 : Blo 99781 128623 := bstep (se 1 (by rfl) ⟨96467, by rfl⟩ : syracuseStep 128623 = 192935) B192935
theorem B292535 : Blo 99781 292535 := bstep (se 1 (by rfl) ⟨219401, by rfl⟩ : syracuseStep 292535 = 438803) B438803
theorem B521963 : Blo 99781 521963 := bstep (se 1 (by rfl) ⟨391472, by rfl⟩ : syracuseStep 521963 = 782945) B782945
theorem B227303 : Blo 99781 227303 := bstep (se 1 (by rfl) ⟨170477, by rfl⟩ : syracuseStep 227303 = 340955) B340955
theorem B227321 : Blo 99781 227321 := bstep (se 2 (by rfl) ⟨85245, by rfl⟩ : syracuseStep 227321 = 170491) B170491
theorem B227411 : Blo 99781 227411 := bstep (se 1 (by rfl) ⟨170558, by rfl⟩ : syracuseStep 227411 = 341117) B341117
theorem B227483 : Blo 99781 227483 := bstep (se 1 (by rfl) ⟨170612, by rfl⟩ : syracuseStep 227483 = 341225) B341225
theorem B129215 : Blo 99781 129215 := bstep (se 1 (by rfl) ⟨96911, by rfl⟩ : syracuseStep 129215 = 193823) B193823
theorem B227591 : Blo 99781 227591 := bstep (se 1 (by rfl) ⟨170693, by rfl⟩ : syracuseStep 227591 = 341387) B341387
theorem B227897 : Blo 99781 227897 := bstep (se 2 (by rfl) ⟨85461, by rfl⟩ : syracuseStep 227897 = 170923) B170923
theorem B162719 : Blo 99781 162719 := bstep (se 1 (by rfl) ⟨122039, by rfl⟩ : syracuseStep 162719 = 244079) B244079
theorem B523421 : Blo 99781 523421 := bstep (se 3 (by rfl) ⟨98141, by rfl⟩ : syracuseStep 523421 = 196283) B196283
theorem B195767 : Blo 99781 195767 := bstep (se 1 (by rfl) ⟨146825, by rfl⟩ : syracuseStep 195767 = 293651) B293651
theorem B228617 : Blo 99781 228617 := bstep (se 2 (by rfl) ⟨85731, by rfl⟩ : syracuseStep 228617 = 171463) B171463
theorem B392795 : Blo 99781 392795 := bstep (se 1 (by rfl) ⟨294596, by rfl⟩ : syracuseStep 392795 = 589193) B589193
theorem B229111 : Blo 99781 229111 := bstep (se 1 (by rfl) ⟨171833, by rfl⟩ : syracuseStep 229111 = 343667) B343667
theorem B589625 : Blo 99781 589625 := bstep (se 2 (by rfl) ⟨221109, by rfl⟩ : syracuseStep 589625 = 442219) B442219
theorem B294779 : Blo 99781 294779 := bstep (se 1 (by rfl) ⟨221084, by rfl⟩ : syracuseStep 294779 = 442169) B442169
theorem B1179521 : Blo 99781 1179521 := bstep (se 2 (by rfl) ⟨442320, by rfl⟩ : syracuseStep 1179521 = 884641) B884641
theorem B229625 : Blo 99781 229625 := bstep (se 2 (by rfl) ⟨86109, by rfl⟩ : syracuseStep 229625 = 172219) B172219
theorem B229679 : Blo 99781 229679 := bstep (se 1 (by rfl) ⟨172259, by rfl⟩ : syracuseStep 229679 = 344519) B344519
theorem B393599 : Blo 99781 393599 := bstep (se 1 (by rfl) ⟨295199, by rfl⟩ : syracuseStep 393599 = 590399) B590399
theorem B229895 : Blo 99781 229895 := bstep (se 1 (by rfl) ⟨172421, by rfl⟩ : syracuseStep 229895 = 344843) B344843
theorem B230075 : Blo 99781 230075 := bstep (se 1 (by rfl) ⟨172556, by rfl⟩ : syracuseStep 230075 = 345113) B345113
theorem B230507 : Blo 99781 230507 := bstep (se 1 (by rfl) ⟨172880, by rfl⟩ : syracuseStep 230507 = 345761) B345761
theorem B427355 : Blo 99781 427355 := bstep (se 1 (by rfl) ⟨320516, by rfl⟩ : syracuseStep 427355 = 641033) B641033
theorem B99867 : Blo 99781 99867 := bstep (se 1 (by rfl) ⟨74900, by rfl⟩ : syracuseStep 99867 = 149801) B149801
theorem B99871 : Blo 99781 99871 := bstep (se 1 (by rfl) ⟨74903, by rfl⟩ : syracuseStep 99871 = 149807) B149807
theorem B230975 : Blo 99781 230975 := bstep (se 1 (by rfl) ⟨173231, by rfl⟩ : syracuseStep 230975 = 346463) B346463
theorem B231083 : Blo 99781 231083 := bstep (se 1 (by rfl) ⟨173312, by rfl⟩ : syracuseStep 231083 = 346625) B346625
theorem B100031 : Blo 99781 100031 := bstep (se 1 (by rfl) ⟨75023, by rfl⟩ : syracuseStep 100031 = 150047) B150047
theorem B919259 : Blo 99781 919259 := bstep (se 1 (by rfl) ⟨689444, by rfl⟩ : syracuseStep 919259 = 1378889) B1378889
theorem B329615 : Blo 99781 329615 := bstep (se 1 (by rfl) ⟨247211, by rfl⟩ : syracuseStep 329615 = 494423) B494423
theorem B100287 : Blo 99781 100287 := bstep (se 1 (by rfl) ⟨75215, by rfl⟩ : syracuseStep 100287 = 150431) B150431
theorem B100319 : Blo 99781 100319 := bstep (se 1 (by rfl) ⟨75239, by rfl⟩ : syracuseStep 100319 = 150479) B150479
theorem B231407 : Blo 99781 231407 := bstep (se 1 (by rfl) ⟨173555, by rfl⟩ : syracuseStep 231407 = 347111) B347111
theorem B100379 : Blo 99781 100379 := bstep (se 1 (by rfl) ⟨75284, by rfl⟩ : syracuseStep 100379 = 150569) B150569
theorem B100383 : Blo 99781 100383 := bstep (se 1 (by rfl) ⟨75287, by rfl⟩ : syracuseStep 100383 = 150575) B150575
theorem B100399 : Blo 99781 100399 := bstep (se 1 (by rfl) ⟨75299, by rfl⟩ : syracuseStep 100399 = 150599) B150599
theorem B231623 : Blo 99781 231623 := bstep (se 1 (by rfl) ⟨173717, by rfl⟩ : syracuseStep 231623 = 347435) B347435
theorem B100575 : Blo 99781 100575 := bstep (se 1 (by rfl) ⟨75431, by rfl⟩ : syracuseStep 100575 = 150863) B150863
theorem B100635 : Blo 99781 100635 := bstep (se 1 (by rfl) ⟨75476, by rfl⟩ : syracuseStep 100635 = 150953) B150953
theorem B231803 : Blo 99781 231803 := bstep (se 1 (by rfl) ⟨173852, by rfl⟩ : syracuseStep 231803 = 347705) B347705
theorem B100735 : Blo 99781 100735 := bstep (se 1 (by rfl) ⟨75551, by rfl⟩ : syracuseStep 100735 = 151103) B151103
theorem B100911 : Blo 99781 100911 := bstep (se 1 (by rfl) ⟨75683, by rfl⟩ : syracuseStep 100911 = 151367) B151367
theorem B100967 : Blo 99781 100967 := bstep (se 1 (by rfl) ⟨75725, by rfl⟩ : syracuseStep 100967 = 151451) B151451
theorem B232073 : Blo 99781 232073 := bstep (se 2 (by rfl) ⟨87027, by rfl⟩ : syracuseStep 232073 = 174055) B174055
theorem B821947 : Blo 99781 821947 := bstep (se 1 (by rfl) ⟨616460, by rfl⟩ : syracuseStep 821947 = 1232921) B1232921
theorem B232361 : Blo 99781 232361 := bstep (se 2 (by rfl) ⟨87135, by rfl⟩ : syracuseStep 232361 = 174271) B174271
theorem B101343 : Blo 99781 101343 := bstep (se 1 (by rfl) ⟨76007, by rfl⟩ : syracuseStep 101343 = 152015) B152015
theorem B429047 : Blo 99781 429047 := bstep (se 1 (by rfl) ⟨321785, by rfl⟩ : syracuseStep 429047 = 643571) B643571
theorem B330743 : Blo 99781 330743 := bstep (se 1 (by rfl) ⟨248057, by rfl⟩ : syracuseStep 330743 = 496115) B496115
theorem B101371 : Blo 99781 101371 := bstep (se 1 (by rfl) ⟨76028, by rfl⟩ : syracuseStep 101371 = 152057) B152057
theorem B822305 : Blo 99781 822305 := bstep (se 2 (by rfl) ⟨308364, by rfl⟩ : syracuseStep 822305 = 616729) B616729
theorem B101439 : Blo 99781 101439 := bstep (se 1 (by rfl) ⟨76079, by rfl⟩ : syracuseStep 101439 = 152159) B152159
theorem B298351 : Blo 99781 298351 := bstep (se 1 (by rfl) ⟨223763, by rfl⟩ : syracuseStep 298351 = 447527) B447527
theorem B101759 : Blo 99781 101759 := bstep (se 1 (by rfl) ⟨76319, by rfl⟩ : syracuseStep 101759 = 152639) B152639
theorem B101787 : Blo 99781 101787 := bstep (se 1 (by rfl) ⟨76340, by rfl⟩ : syracuseStep 101787 = 152681) B152681
theorem B101855 : Blo 99781 101855 := bstep (se 1 (by rfl) ⟨76391, by rfl⟩ : syracuseStep 101855 = 152783) B152783
theorem B101991 : Blo 99781 101991 := bstep (se 1 (by rfl) ⟨76493, by rfl⟩ : syracuseStep 101991 = 152987) B152987
theorem B233063 : Blo 99781 233063 := bstep (se 1 (by rfl) ⟨174797, by rfl⟩ : syracuseStep 233063 = 349595) B349595
theorem B102139 : Blo 99781 102139 := bstep (se 1 (by rfl) ⟨76604, by rfl⟩ : syracuseStep 102139 = 153209) B153209
theorem B102207 : Blo 99781 102207 := bstep (se 1 (by rfl) ⟨76655, by rfl⟩ : syracuseStep 102207 = 153311) B153311
theorem B102271 : Blo 99781 102271 := bstep (se 1 (by rfl) ⟨76703, by rfl⟩ : syracuseStep 102271 = 153407) B153407
theorem B102383 : Blo 99781 102383 := bstep (se 1 (by rfl) ⟨76787, by rfl⟩ : syracuseStep 102383 = 153575) B153575
theorem B102395 : Blo 99781 102395 := bstep (se 1 (by rfl) ⟨76796, by rfl⟩ : syracuseStep 102395 = 153593) B153593
theorem B2101297 : Blo 99781 2101297 := bstep (se 2 (by rfl) ⟨787986, by rfl⟩ : syracuseStep 2101297 = 1575973) B1575973
theorem B102463 : Blo 99781 102463 := bstep (se 1 (by rfl) ⟨76847, by rfl⟩ : syracuseStep 102463 = 153695) B153695
theorem B102503 : Blo 99781 102503 := bstep (se 1 (by rfl) ⟨76877, by rfl⟩ : syracuseStep 102503 = 153755) B153755
theorem B102527 : Blo 99781 102527 := bstep (se 1 (by rfl) ⟨76895, by rfl⟩ : syracuseStep 102527 = 153791) B153791
theorem B102555 : Blo 99781 102555 := bstep (se 1 (by rfl) ⟨76916, by rfl⟩ : syracuseStep 102555 = 153833) B153833
theorem B102759 : Blo 99781 102759 := bstep (se 1 (by rfl) ⟨77069, by rfl⟩ : syracuseStep 102759 = 154139) B154139
theorem B758159 : Blo 99781 758159 := bstep (se 1 (by rfl) ⟨568619, by rfl⟩ : syracuseStep 758159 = 1137239) B1137239
theorem B102811 : Blo 99781 102811 := bstep (se 1 (by rfl) ⟨77108, by rfl⟩ : syracuseStep 102811 = 154217) B154217
theorem B103163 : Blo 99781 103163 := bstep (se 1 (by rfl) ⟨77372, by rfl⟩ : syracuseStep 103163 = 154745) B154745
theorem B496381 : Blo 99781 496381 := bstep (se 3 (by rfl) ⟨93071, by rfl⟩ : syracuseStep 496381 = 186143) B186143
theorem B103231 : Blo 99781 103231 := bstep (se 1 (by rfl) ⟨77423, by rfl⟩ : syracuseStep 103231 = 154847) B154847
theorem B103259 : Blo 99781 103259 := bstep (se 1 (by rfl) ⟨77444, by rfl⟩ : syracuseStep 103259 = 154889) B154889
theorem B660383 : Blo 99781 660383 := bstep (se 1 (by rfl) ⟨495287, by rfl⟩ : syracuseStep 660383 = 990575) B990575
theorem B103327 : Blo 99781 103327 := bstep (se 1 (by rfl) ⟨77495, by rfl⟩ : syracuseStep 103327 = 154991) B154991
theorem B103407 : Blo 99781 103407 := bstep (se 1 (by rfl) ⟨77555, by rfl⟩ : syracuseStep 103407 = 155111) B155111
theorem B103495 : Blo 99781 103495 := bstep (se 1 (by rfl) ⟨77621, by rfl⟩ : syracuseStep 103495 = 155243) B155243
theorem B103579 : Blo 99781 103579 := bstep (se 1 (by rfl) ⟨77684, by rfl⟩ : syracuseStep 103579 = 155369) B155369
theorem B103675 : Blo 99781 103675 := bstep (se 1 (by rfl) ⟨77756, by rfl⟩ : syracuseStep 103675 = 155513) B155513
theorem B103743 : Blo 99781 103743 := bstep (se 1 (by rfl) ⟨77807, by rfl⟩ : syracuseStep 103743 = 155615) B155615
theorem B169627 : Blo 99781 169627 := bstep (se 1 (by rfl) ⟨127220, by rfl⟩ : syracuseStep 169627 = 254441) B254441
theorem B235361 : Blo 99781 235361 := bstep (se 2 (by rfl) ⟨88260, by rfl⟩ : syracuseStep 235361 = 176521) B176521
theorem B432479 : Blo 99781 432479 := bstep (se 1 (by rfl) ⟨324359, by rfl⟩ : syracuseStep 432479 = 648719) B648719
theorem B8395109 : Blo 99781 8395109 := bstep (se 4 (by rfl) ⟨787041, by rfl⟩ : syracuseStep 8395109 = 1574083) B1574083
theorem B170471 : Blo 99781 170471 := bstep (se 1 (by rfl) ⟨127853, by rfl⟩ : syracuseStep 170471 = 255707) B255707
theorem B236009 : Blo 99781 236009 := bstep (se 2 (by rfl) ⟨88503, by rfl⟩ : syracuseStep 236009 = 177007) B177007
theorem B236411 : Blo 99781 236411 := bstep (se 1 (by rfl) ⟨177308, by rfl⟩ : syracuseStep 236411 = 354617) B354617
theorem B1088579 : Blo 99781 1088579 := bstep (se 1 (by rfl) ⟨816434, by rfl⟩ : syracuseStep 1088579 = 1632869) B1632869
theorem B859355 : Blo 99781 859355 := bstep (se 1 (by rfl) ⟨644516, by rfl⟩ : syracuseStep 859355 = 1289033) B1289033
theorem B171335 : Blo 99781 171335 := bstep (se 1 (by rfl) ⟨128501, by rfl⟩ : syracuseStep 171335 = 257003) B257003
theorem B171497 : Blo 99781 171497 := bstep (se 2 (by rfl) ⟨64311, by rfl⟩ : syracuseStep 171497 = 128623) B128623
theorem B466651 : Blo 99781 466651 := bstep (se 1 (by rfl) ⟨349988, by rfl⟩ : syracuseStep 466651 = 699977) B699977
theorem B1056503 : Blo 99781 1056503 := bstep (se 1 (by rfl) ⟨792377, by rfl⟩ : syracuseStep 1056503 = 1584755) B1584755
theorem B664301 : Blo 99781 664301 := bstep (se 3 (by rfl) ⟨124556, by rfl⟩ : syracuseStep 664301 = 249113) B249113
theorem B1221925 : Blo 99781 1221925 := bstep (se 4 (by rfl) ⟨114555, by rfl⟩ : syracuseStep 1221925 = 229111) B229111
theorem B206363 : Blo 99781 206363 := bstep (se 1 (by rfl) ⟨154772, by rfl⟩ : syracuseStep 206363 = 309545) B309545
theorem B108479 : Blo 99781 108479 := bstep (se 1 (by rfl) ⟨81359, by rfl⟩ : syracuseStep 108479 = 162719) B162719
theorem B239849 : Blo 99781 239849 := bstep (se 2 (by rfl) ⟨89943, by rfl⟩ : syracuseStep 239849 = 179887) B179887
theorem B15935849 : Blo 99781 15935849 := bstep (se 2 (by rfl) ⟨5975943, by rfl⟩ : syracuseStep 15935849 = 11951887) B11951887
theorem B240713 : Blo 99781 240713 := bstep (se 2 (by rfl) ⟨90267, by rfl⟩ : syracuseStep 240713 = 180535) B180535
theorem B928921 : Blo 99781 928921 := bstep (se 2 (by rfl) ⟨348345, by rfl⟩ : syracuseStep 928921 = 696691) B696691
theorem B470591 : Blo 99781 470591 := bstep (se 1 (by rfl) ⟨352943, by rfl⟩ : syracuseStep 470591 = 705887) B705887
theorem B864107 : Blo 99781 864107 := bstep (se 1 (by rfl) ⟨648080, by rfl⟩ : syracuseStep 864107 = 1296161) B1296161
theorem B569213 : Blo 99781 569213 := bstep (se 3 (by rfl) ⟨106727, by rfl⟩ : syracuseStep 569213 = 213455) B213455
theorem B372863 : Blo 99781 372863 := bstep (se 1 (by rfl) ⟨279647, by rfl⟩ : syracuseStep 372863 = 559295) B559295
theorem B340199 : Blo 99781 340199 := bstep (se 1 (by rfl) ⟨255149, by rfl⟩ : syracuseStep 340199 = 510299) B510299
theorem B373355 : Blo 99781 373355 := bstep (se 1 (by rfl) ⟨280016, by rfl⟩ : syracuseStep 373355 = 560033) B560033
theorem B701131 : Blo 99781 701131 := bstep (se 1 (by rfl) ⟨525848, by rfl⟩ : syracuseStep 701131 = 1051697) B1051697
theorem B439177 : Blo 99781 439177 := bstep (se 2 (by rfl) ⟨164691, by rfl⟩ : syracuseStep 439177 = 329383) B329383
theorem B341063 : Blo 99781 341063 := bstep (se 1 (by rfl) ⟨255797, by rfl⟩ : syracuseStep 341063 = 511595) B511595
theorem B800279 : Blo 99781 800279 := bstep (se 1 (by rfl) ⟨600209, by rfl⟩ : syracuseStep 800279 = 1200419) B1200419
theorem B570989 : Blo 99781 570989 := bstep (se 3 (by rfl) ⟨107060, by rfl⟩ : syracuseStep 570989 = 214121) B214121
theorem B112711 : Blo 99781 112711 := bstep (se 1 (by rfl) ⟨84533, by rfl⟩ : syracuseStep 112711 = 169067) B169067
theorem B506087 : Blo 99781 506087 := bstep (se 1 (by rfl) ⟨379565, by rfl⟩ : syracuseStep 506087 = 759131) B759131
theorem B342251 : Blo 99781 342251 := bstep (se 1 (by rfl) ⟨256688, by rfl⟩ : syracuseStep 342251 = 513377) B513377
theorem B768365 : Blo 99781 768365 := bstep (se 3 (by rfl) ⟨144068, by rfl⟩ : syracuseStep 768365 = 288137) B288137
theorem B408185 : Blo 99781 408185 := bstep (se 2 (by rfl) ⟨153069, by rfl⟩ : syracuseStep 408185 = 306139) B306139
theorem B244367 : Blo 99781 244367 := bstep (se 1 (by rfl) ⟨183275, by rfl⟩ : syracuseStep 244367 = 366551) B366551
theorem B5585597 : Blo 99781 5585597 := bstep (se 3 (by rfl) ⟨1047299, by rfl⟩ : syracuseStep 5585597 = 2094599) B2094599
theorem B277225 : Blo 99781 277225 := bstep (se 2 (by rfl) ⟨103959, by rfl⟩ : syracuseStep 277225 = 207919) B207919
theorem B113575 : Blo 99781 113575 := bstep (se 1 (by rfl) ⟨85181, by rfl⟩ : syracuseStep 113575 = 170363) B170363
theorem B113755 : Blo 99781 113755 := bstep (se 1 (by rfl) ⟨85316, by rfl⟩ : syracuseStep 113755 = 170633) B170633
theorem B867419 : Blo 99781 867419 := bstep (se 1 (by rfl) ⟨650564, by rfl⟩ : syracuseStep 867419 = 1301129) B1301129
theorem B1851569 : Blo 99781 1851569 := bstep (se 2 (by rfl) ⟨694338, by rfl⟩ : syracuseStep 1851569 = 1388677) B1388677
theorem B1163483 : Blo 99781 1163483 := bstep (se 1 (by rfl) ⟨872612, by rfl⟩ : syracuseStep 1163483 = 1745225) B1745225
theorem B147691 : Blo 99781 147691 := bstep (se 1 (by rfl) ⟨110768, by rfl⟩ : syracuseStep 147691 = 221537) B221537
theorem B114943 : Blo 99781 114943 := bstep (se 1 (by rfl) ⟨86207, by rfl⟩ : syracuseStep 114943 = 172415) B172415
theorem B344573 : Blo 99781 344573 := bstep (se 3 (by rfl) ⟨64607, by rfl⟩ : syracuseStep 344573 = 129215) B129215
theorem B115231 : Blo 99781 115231 := bstep (se 1 (by rfl) ⟨86423, by rfl⟩ : syracuseStep 115231 = 172847) B172847
theorem B770795 : Blo 99781 770795 := bstep (se 1 (by rfl) ⟨578096, by rfl⟩ : syracuseStep 770795 = 1156193) B1156193
theorem B2638615 : Blo 99781 2638615 := bstep (se 1 (by rfl) ⟨1978961, by rfl⟩ : syracuseStep 2638615 = 3957923) B3957923
theorem B443177 : Blo 99781 443177 := bstep (se 2 (by rfl) ⟨166191, by rfl⟩ : syracuseStep 443177 = 332383) B332383
theorem B1262567 : Blo 99781 1262567 := bstep (se 1 (by rfl) ⟨946925, by rfl⟩ : syracuseStep 1262567 = 1893851) B1893851
theorem B115823 : Blo 99781 115823 := bstep (se 1 (by rfl) ⟨86867, by rfl⟩ : syracuseStep 115823 = 173735) B173735
theorem B115879 : Blo 99781 115879 := bstep (se 1 (by rfl) ⟨86909, by rfl⟩ : syracuseStep 115879 = 173819) B173819
theorem B214319 : Blo 99781 214319 := bstep (se 1 (by rfl) ⟨160739, by rfl⟩ : syracuseStep 214319 = 321479) B321479
theorem B116015 : Blo 99781 116015 := bstep (se 1 (by rfl) ⟨87011, by rfl⟩ : syracuseStep 116015 = 174023) B174023
theorem B345707 : Blo 99781 345707 := bstep (se 1 (by rfl) ⟨259280, by rfl⟩ : syracuseStep 345707 = 518561) B518561
theorem B345977 : Blo 99781 345977 := bstep (se 2 (by rfl) ⟨129741, by rfl⟩ : syracuseStep 345977 = 259483) B259483
theorem B247673 : Blo 99781 247673 := bstep (se 2 (by rfl) ⟨92877, by rfl⟩ : syracuseStep 247673 = 185755) B185755
theorem B116671 : Blo 99781 116671 := bstep (se 1 (by rfl) ⟨87503, by rfl⟩ : syracuseStep 116671 = 175007) B175007
theorem B9423053 : Blo 99781 9423053 := bstep (se 3 (by rfl) ⟨1766822, by rfl⟩ : syracuseStep 9423053 = 3533645) B3533645
theorem B346355 : Blo 99781 346355 := bstep (se 1 (by rfl) ⟨259766, by rfl⟩ : syracuseStep 346355 = 519533) B519533
theorem B313679 : Blo 99781 313679 := bstep (se 1 (by rfl) ⟨235259, by rfl⟩ : syracuseStep 313679 = 470519) B470519
theorem B969083 : Blo 99781 969083 := bstep (se 1 (by rfl) ⟨726812, by rfl⟩ : syracuseStep 969083 = 1453625) B1453625
theorem B150119 : Blo 99781 150119 := bstep (se 1 (by rfl) ⟨112589, by rfl⟩ : syracuseStep 150119 = 225179) B225179
theorem B379673 : Blo 99781 379673 := bstep (se 2 (by rfl) ⟨142377, by rfl⟩ : syracuseStep 379673 = 284755) B284755
theorem B150311 : Blo 99781 150311 := bstep (se 1 (by rfl) ⟨112733, by rfl⟩ : syracuseStep 150311 = 225467) B225467
theorem B248615 : Blo 99781 248615 := bstep (se 1 (by rfl) ⟨186461, by rfl⟩ : syracuseStep 248615 = 372923) B372923
theorem B150635 : Blo 99781 150635 := bstep (se 1 (by rfl) ⟨112976, by rfl⟩ : syracuseStep 150635 = 225953) B225953
theorem B150875 : Blo 99781 150875 := bstep (se 1 (by rfl) ⟨113156, by rfl⟩ : syracuseStep 150875 = 226313) B226313
theorem B150905 : Blo 99781 150905 := bstep (se 2 (by rfl) ⟨56589, by rfl⟩ : syracuseStep 150905 = 113179) B113179
theorem B150911 : Blo 99781 150911 := bstep (se 1 (by rfl) ⟨113183, by rfl⟩ : syracuseStep 150911 = 226367) B226367
theorem B413309 : Blo 99781 413309 := bstep (se 3 (by rfl) ⟨77495, by rfl⟩ : syracuseStep 413309 = 154991) B154991
theorem B315191 : Blo 99781 315191 := bstep (se 1 (by rfl) ⟨236393, by rfl⟩ : syracuseStep 315191 = 472787) B472787
theorem B347975 : Blo 99781 347975 := bstep (se 1 (by rfl) ⟨260981, by rfl⟩ : syracuseStep 347975 = 521963) B521963
theorem B151535 : Blo 99781 151535 := bstep (se 1 (by rfl) ⟨113651, by rfl⟩ : syracuseStep 151535 = 227303) B227303
theorem B151547 : Blo 99781 151547 := bstep (se 1 (by rfl) ⟨113660, by rfl⟩ : syracuseStep 151547 = 227321) B227321
theorem B151607 : Blo 99781 151607 := bstep (se 1 (by rfl) ⟨113705, by rfl⟩ : syracuseStep 151607 = 227411) B227411
theorem B151655 : Blo 99781 151655 := bstep (se 1 (by rfl) ⟨113741, by rfl⟩ : syracuseStep 151655 = 227483) B227483
theorem B118939 : Blo 99781 118939 := bstep (se 1 (by rfl) ⟨89204, by rfl⟩ : syracuseStep 118939 = 178409) B178409
theorem B151727 : Blo 99781 151727 := bstep (se 1 (by rfl) ⟨113795, by rfl⟩ : syracuseStep 151727 = 227591) B227591
theorem B151931 : Blo 99781 151931 := bstep (se 1 (by rfl) ⟨113948, by rfl⟩ : syracuseStep 151931 = 227897) B227897
theorem B152201 : Blo 99781 152201 := bstep (se 2 (by rfl) ⟨57075, by rfl⟩ : syracuseStep 152201 = 114151) B114151
theorem B348947 : Blo 99781 348947 := bstep (se 1 (by rfl) ⟨261710, by rfl⟩ : syracuseStep 348947 = 523421) B523421
theorem B152411 : Blo 99781 152411 := bstep (se 1 (by rfl) ⟨114308, by rfl⟩ : syracuseStep 152411 = 228617) B228617
theorem B152873 : Blo 99781 152873 := bstep (se 2 (by rfl) ⟨57327, by rfl⟩ : syracuseStep 152873 = 114655) B114655
theorem B153071 : Blo 99781 153071 := bstep (se 1 (by rfl) ⟨114803, by rfl⟩ : syracuseStep 153071 = 229607) B229607
theorem B284447 : Blo 99781 284447 := bstep (se 1 (by rfl) ⟨213335, by rfl⟩ : syracuseStep 284447 = 426671) B426671
theorem B153467 : Blo 99781 153467 := bstep (se 1 (by rfl) ⟨115100, by rfl⟩ : syracuseStep 153467 = 230201) B230201
theorem B382877 : Blo 99781 382877 := bstep (se 3 (by rfl) ⟨71789, by rfl⟩ : syracuseStep 382877 = 143579) B143579
theorem B153503 : Blo 99781 153503 := bstep (se 1 (by rfl) ⟨115127, by rfl⟩ : syracuseStep 153503 = 230255) B230255
theorem B2611277 : Blo 99781 2611277 := bstep (se 3 (by rfl) ⟨489614, by rfl⟩ : syracuseStep 2611277 = 979229) B979229
theorem B153737 : Blo 99781 153737 := bstep (se 2 (by rfl) ⟨57651, by rfl⟩ : syracuseStep 153737 = 115303) B115303
theorem B153887 : Blo 99781 153887 := bstep (se 1 (by rfl) ⟨115415, by rfl⟩ : syracuseStep 153887 = 230831) B230831
theorem B481619 : Blo 99781 481619 := bstep (se 1 (by rfl) ⟨361214, by rfl⟩ : syracuseStep 481619 = 722429) B722429
theorem B383393 : Blo 99781 383393 := bstep (se 2 (by rfl) ⟨143772, by rfl⟩ : syracuseStep 383393 = 287545) B287545
theorem B7428631 : Blo 99781 7428631 := bstep (se 1 (by rfl) ⟨5571473, by rfl⟩ : syracuseStep 7428631 = 11142947) B11142947
theorem B154439 : Blo 99781 154439 := bstep (se 1 (by rfl) ⟨115829, by rfl⟩ : syracuseStep 154439 = 231659) B231659
theorem B1924013 : Blo 99781 1924013 := bstep (se 3 (by rfl) ⟨360752, by rfl⟩ : syracuseStep 1924013 = 721505) B721505
theorem B384365 : Blo 99781 384365 := bstep (se 3 (by rfl) ⟨72068, by rfl⟩ : syracuseStep 384365 = 144137) B144137
theorem B3857867 : Blo 99781 3857867 := bstep (se 1 (by rfl) ⟨2893400, by rfl⟩ : syracuseStep 3857867 = 5786801) B5786801
theorem B482849 : Blo 99781 482849 := bstep (se 2 (by rfl) ⟨181068, by rfl⟩ : syracuseStep 482849 = 362137) B362137
theorem B155303 : Blo 99781 155303 := bstep (se 1 (by rfl) ⟨116477, by rfl⟩ : syracuseStep 155303 = 232955) B232955
theorem B155423 : Blo 99781 155423 := bstep (se 1 (by rfl) ⟨116567, by rfl⟩ : syracuseStep 155423 = 233135) B233135
theorem B1630135 : Blo 99781 1630135 := bstep (se 1 (by rfl) ⟨1222601, by rfl⟩ : syracuseStep 1630135 = 2445203) B2445203
theorem B385337 : Blo 99781 385337 := bstep (se 2 (by rfl) ⟨144501, by rfl⟩ : syracuseStep 385337 = 289003) B289003
theorem B385823 : Blo 99781 385823 := bstep (se 1 (by rfl) ⟨289367, by rfl⟩ : syracuseStep 385823 = 578735) B578735
theorem B779165 : Blo 99781 779165 := bstep (se 3 (by rfl) ⟨146093, by rfl⟩ : syracuseStep 779165 = 292187) B292187
theorem B189715 : Blo 99781 189715 := bstep (se 1 (by rfl) ⟨142286, by rfl⟩ : syracuseStep 189715 = 284573) B284573
theorem B353819 : Blo 99781 353819 := bstep (se 1 (by rfl) ⟨265364, by rfl⟩ : syracuseStep 353819 = 530729) B530729
theorem B222793 : Blo 99781 222793 := bstep (se 2 (by rfl) ⟨83547, by rfl⟩ : syracuseStep 222793 = 167095) B167095
theorem B386795 : Blo 99781 386795 := bstep (se 1 (by rfl) ⟨290096, by rfl⟩ : syracuseStep 386795 = 580193) B580193
theorem B190345 : Blo 99781 190345 := bstep (se 2 (by rfl) ⟨71379, by rfl⟩ : syracuseStep 190345 = 142759) B142759
theorem B255899 : Blo 99781 255899 := bstep (se 1 (by rfl) ⟨191924, by rfl⟩ : syracuseStep 255899 = 383849) B383849
theorem B387281 : Blo 99781 387281 := bstep (se 2 (by rfl) ⟨145230, by rfl⟩ : syracuseStep 387281 = 290461) B290461
theorem B3697001 : Blo 99781 3697001 := bstep (se 2 (by rfl) ⟨1386375, by rfl⟩ : syracuseStep 3697001 = 2772751) B2772751
theorem B387737 : Blo 99781 387737 := bstep (se 2 (by rfl) ⟨145401, by rfl⟩ : syracuseStep 387737 = 290803) B290803
theorem B224531 : Blo 99781 224531 := bstep (se 1 (by rfl) ⟨168398, by rfl⟩ : syracuseStep 224531 = 336797) B336797
theorem B224567 : Blo 99781 224567 := bstep (se 1 (by rfl) ⟨168425, by rfl⟩ : syracuseStep 224567 = 336851) B336851
theorem B225161 : Blo 99781 225161 := bstep (se 2 (by rfl) ⟨84435, by rfl⟩ : syracuseStep 225161 = 168871) B168871
theorem B225377 : Blo 99781 225377 := bstep (se 2 (by rfl) ⟨84516, by rfl⟩ : syracuseStep 225377 = 169033) B169033
theorem B651361 : Blo 99781 651361 := bstep (se 2 (by rfl) ⟨244260, by rfl⟩ : syracuseStep 651361 = 488521) B488521
theorem B159887 : Blo 99781 159887 := bstep (se 1 (by rfl) ⟨119915, by rfl⟩ : syracuseStep 159887 = 239831) B239831
theorem B192775 : Blo 99781 192775 := bstep (se 1 (by rfl) ⟨144581, by rfl⟩ : syracuseStep 192775 = 289163) B289163
theorem B487705 : Blo 99781 487705 := bstep (se 2 (by rfl) ⟨182889, by rfl⟩ : syracuseStep 487705 = 365779) B365779
theorem B2585033 : Blo 99781 2585033 := bstep (se 2 (by rfl) ⟨969387, by rfl⟩ : syracuseStep 2585033 = 1938775) B1938775
theorem B258511 : Blo 99781 258511 := bstep (se 1 (by rfl) ⟨193883, by rfl⟩ : syracuseStep 258511 = 387767) B387767
theorem B389711 : Blo 99781 389711 := bstep (se 1 (by rfl) ⟨292283, by rfl⟩ : syracuseStep 389711 = 584567) B584567
theorem B226043 : Blo 99781 226043 := bstep (se 1 (by rfl) ⟨169532, by rfl⟩ : syracuseStep 226043 = 339065) B339065
theorem B1110941 : Blo 99781 1110941 := bstep (se 3 (by rfl) ⟨208301, by rfl⟩ : syracuseStep 1110941 = 416603) B416603
theorem B226259 : Blo 99781 226259 := bstep (se 1 (by rfl) ⟨169694, by rfl⟩ : syracuseStep 226259 = 339389) B339389
theorem B128071 : Blo 99781 128071 := bstep (se 1 (by rfl) ⟨96053, by rfl⟩ : syracuseStep 128071 = 192107) B192107
theorem B226727 : Blo 99781 226727 := bstep (se 1 (by rfl) ⟨170045, by rfl⟩ : syracuseStep 226727 = 340091) B340091
theorem B521639 : Blo 99781 521639 := bstep (se 1 (by rfl) ⟨391229, by rfl⟩ : syracuseStep 521639 = 782459) B782459
theorem B1668545 : Blo 99781 1668545 := bstep (se 2 (by rfl) ⟨625704, by rfl⟩ : syracuseStep 1668545 = 1251409) B1251409
theorem B226835 : Blo 99781 226835 := bstep (se 1 (by rfl) ⟨170126, by rfl⟩ : syracuseStep 226835 = 340253) B340253
theorem B226907 : Blo 99781 226907 := bstep (se 1 (by rfl) ⟨170180, by rfl⟩ : syracuseStep 226907 = 340361) B340361
theorem B259919 : Blo 99781 259919 := bstep (se 1 (by rfl) ⟨194939, by rfl⟩ : syracuseStep 259919 = 389879) B389879
theorem B554951 : Blo 99781 554951 := bstep (se 1 (by rfl) ⟨416213, by rfl⟩ : syracuseStep 554951 = 832427) B832427
theorem B391151 : Blo 99781 391151 := bstep (se 1 (by rfl) ⟨293363, by rfl⟩ : syracuseStep 391151 = 586727) B586727
theorem B391351 : Blo 99781 391351 := bstep (se 1 (by rfl) ⟨293513, by rfl⟩ : syracuseStep 391351 = 587027) B587027
theorem B227519 : Blo 99781 227519 := bstep (se 1 (by rfl) ⟨170639, by rfl⟩ : syracuseStep 227519 = 341279) B341279
theorem B194795 : Blo 99781 194795 := bstep (se 1 (by rfl) ⟨146096, by rfl⟩ : syracuseStep 194795 = 292193) B292193
theorem B195023 : Blo 99781 195023 := bstep (se 1 (by rfl) ⟨146267, by rfl⟩ : syracuseStep 195023 = 292535) B292535
theorem B391837 : Blo 99781 391837 := bstep (se 3 (by rfl) ⟨73469, by rfl⟩ : syracuseStep 391837 = 146939) B146939
theorem B228577 : Blo 99781 228577 := bstep (se 2 (by rfl) ⟨85716, by rfl⟩ : syracuseStep 228577 = 171433) B171433
theorem B228779 : Blo 99781 228779 := bstep (se 1 (by rfl) ⟨171584, by rfl⟩ : syracuseStep 228779 = 343169) B343169
theorem B228815 : Blo 99781 228815 := bstep (se 1 (by rfl) ⟨171611, by rfl⟩ : syracuseStep 228815 = 343223) B343223
theorem B130511 : Blo 99781 130511 := bstep (se 1 (by rfl) ⟨97883, by rfl⟩ : syracuseStep 130511 = 195767) B195767
theorem B261863 : Blo 99781 261863 := bstep (se 1 (by rfl) ⟨196397, by rfl⟩ : syracuseStep 261863 = 392795) B392795
theorem B393083 : Blo 99781 393083 := bstep (se 1 (by rfl) ⟨294812, by rfl⟩ : syracuseStep 393083 = 589625) B589625
theorem B196519 : Blo 99781 196519 := bstep (se 1 (by rfl) ⟨147389, by rfl⟩ : syracuseStep 196519 = 294779) B294779
theorem B786347 : Blo 99781 786347 := bstep (se 1 (by rfl) ⟨589760, by rfl⟩ : syracuseStep 786347 = 1179521) B1179521
theorem B229319 : Blo 99781 229319 := bstep (se 1 (by rfl) ⟨171989, by rfl⟩ : syracuseStep 229319 = 343979) B343979
theorem B262399 : Blo 99781 262399 := bstep (se 1 (by rfl) ⟨196799, by rfl⟩ : syracuseStep 262399 = 393599) B393599
theorem B196921 : Blo 99781 196921 := bstep (se 2 (by rfl) ⟨73845, by rfl⟩ : syracuseStep 196921 = 147691) B147691
theorem B229715 : Blo 99781 229715 := bstep (se 1 (by rfl) ⟨172286, by rfl⟩ : syracuseStep 229715 = 344573) B344573
theorem B295451 : Blo 99781 295451 := bstep (se 1 (by rfl) ⟨221588, by rfl⟩ : syracuseStep 295451 = 443177) B443177
theorem B230471 : Blo 99781 230471 := bstep (se 1 (by rfl) ⟨172853, by rfl⟩ : syracuseStep 230471 = 345707) B345707
theorem B230651 : Blo 99781 230651 := bstep (se 1 (by rfl) ⟨172988, by rfl⟩ : syracuseStep 230651 = 345977) B345977
theorem B165115 : Blo 99781 165115 := bstep (se 1 (by rfl) ⟨123836, by rfl⟩ : syracuseStep 165115 = 247673) B247673
theorem B230903 : Blo 99781 230903 := bstep (se 1 (by rfl) ⟨173177, by rfl⟩ : syracuseStep 230903 = 346355) B346355
theorem B100079 : Blo 99781 100079 := bstep (se 1 (by rfl) ⟨75059, by rfl⟩ : syracuseStep 100079 = 150119) B150119
theorem B100207 : Blo 99781 100207 := bstep (se 1 (by rfl) ⟨75155, by rfl⟩ : syracuseStep 100207 = 150311) B150311
theorem B165743 : Blo 99781 165743 := bstep (se 1 (by rfl) ⟨124307, by rfl⟩ : syracuseStep 165743 = 248615) B248615
theorem B1771469 : Blo 99781 1771469 := bstep (se 3 (by rfl) ⟨332150, by rfl⟩ : syracuseStep 1771469 = 664301) B664301
theorem B100423 : Blo 99781 100423 := bstep (se 1 (by rfl) ⟨75317, by rfl⟩ : syracuseStep 100423 = 150635) B150635
theorem B100583 : Blo 99781 100583 := bstep (se 1 (by rfl) ⟨75437, by rfl⟩ : syracuseStep 100583 = 150875) B150875
theorem B100603 : Blo 99781 100603 := bstep (se 1 (by rfl) ⟨75452, by rfl⟩ : syracuseStep 100603 = 150905) B150905
theorem B100607 : Blo 99781 100607 := bstep (se 1 (by rfl) ⟨75455, by rfl⟩ : syracuseStep 100607 = 150911) B150911
theorem B231983 : Blo 99781 231983 := bstep (se 1 (by rfl) ⟨173987, by rfl⟩ : syracuseStep 231983 = 347975) B347975
theorem B101023 : Blo 99781 101023 := bstep (se 1 (by rfl) ⟨75767, by rfl⟩ : syracuseStep 101023 = 151535) B151535
theorem B101031 : Blo 99781 101031 := bstep (se 1 (by rfl) ⟨75773, by rfl⟩ : syracuseStep 101031 = 151547) B151547
theorem B101071 : Blo 99781 101071 := bstep (se 1 (by rfl) ⟨75803, by rfl⟩ : syracuseStep 101071 = 151607) B151607
theorem B101103 : Blo 99781 101103 := bstep (se 1 (by rfl) ⟨75827, by rfl⟩ : syracuseStep 101103 = 151655) B151655
theorem B101151 : Blo 99781 101151 := bstep (se 1 (by rfl) ⟨75863, by rfl⟩ : syracuseStep 101151 = 151727) B151727
theorem B101287 : Blo 99781 101287 := bstep (se 1 (by rfl) ⟨75965, by rfl⟩ : syracuseStep 101287 = 151931) B151931
theorem B101467 : Blo 99781 101467 := bstep (se 1 (by rfl) ⟨76100, by rfl⟩ : syracuseStep 101467 = 152201) B152201
theorem B232631 : Blo 99781 232631 := bstep (se 1 (by rfl) ⟨174473, by rfl⟩ : syracuseStep 232631 = 348947) B348947
theorem B101607 : Blo 99781 101607 := bstep (se 1 (by rfl) ⟨76205, by rfl⟩ : syracuseStep 101607 = 152411) B152411
theorem B101915 : Blo 99781 101915 := bstep (se 1 (by rfl) ⟨76436, by rfl⟩ : syracuseStep 101915 = 152873) B152873
theorem B102047 : Blo 99781 102047 := bstep (se 1 (by rfl) ⟨76535, by rfl⟩ : syracuseStep 102047 = 153071) B153071
theorem B1478533 : Blo 99781 1478533 := bstep (se 4 (by rfl) ⟨138612, by rfl⟩ : syracuseStep 1478533 = 277225) B277225
theorem B102311 : Blo 99781 102311 := bstep (se 1 (by rfl) ⟨76733, by rfl⟩ : syracuseStep 102311 = 153467) B153467
theorem B102335 : Blo 99781 102335 := bstep (se 1 (by rfl) ⟨76751, by rfl⟩ : syracuseStep 102335 = 153503) B153503
theorem B1740851 : Blo 99781 1740851 := bstep (se 1 (by rfl) ⟨1305638, by rfl⟩ : syracuseStep 1740851 = 2611277) B2611277
theorem B102491 : Blo 99781 102491 := bstep (se 1 (by rfl) ⟨76868, by rfl⟩ : syracuseStep 102491 = 153737) B153737
theorem B102591 : Blo 99781 102591 := bstep (se 1 (by rfl) ⟨76943, by rfl⟩ : syracuseStep 102591 = 153887) B153887
theorem B397801 : Blo 99781 397801 := bstep (se 2 (by rfl) ⟨149175, by rfl⟩ : syracuseStep 397801 = 298351) B298351
theorem B102959 : Blo 99781 102959 := bstep (se 1 (by rfl) ⟨77219, by rfl⟩ : syracuseStep 102959 = 154439) B154439
theorem B1282675 : Blo 99781 1282675 := bstep (se 1 (by rfl) ⟨962006, by rfl⟩ : syracuseStep 1282675 = 1924013) B1924013
theorem B725719 : Blo 99781 725719 := bstep (se 1 (by rfl) ⟨544289, by rfl⟩ : syracuseStep 725719 = 1088579) B1088579
theorem B103535 : Blo 99781 103535 := bstep (se 1 (by rfl) ⟨77651, by rfl⟩ : syracuseStep 103535 = 155303) B155303
theorem B1479869 : Blo 99781 1479869 := bstep (se 3 (by rfl) ⟨277475, by rfl⟩ : syracuseStep 1479869 = 554951) B554951
theorem B103615 : Blo 99781 103615 := bstep (se 1 (by rfl) ⟨77711, by rfl⟩ : syracuseStep 103615 = 155423) B155423
theorem B1153277 : Blo 99781 1153277 := bstep (se 3 (by rfl) ⟨216239, by rfl⟩ : syracuseStep 1153277 = 432479) B432479
theorem B661841 : Blo 99781 661841 := bstep (se 2 (by rfl) ⟨248190, by rfl⟩ : syracuseStep 661841 = 496381) B496381
theorem B137575 : Blo 99781 137575 := bstep (se 1 (by rfl) ⟨103181, by rfl⟩ : syracuseStep 137575 = 206363) B206363
theorem B235879 : Blo 99781 235879 := bstep (se 1 (by rfl) ⟨176909, by rfl⟩ : syracuseStep 235879 = 353819) B353819
theorem B137641 : Blo 99781 137641 := bstep (se 2 (by rfl) ⟨51615, by rfl⟩ : syracuseStep 137641 = 103231) B103231
theorem B170599 : Blo 99781 170599 := bstep (se 1 (by rfl) ⟨127949, by rfl⟩ : syracuseStep 170599 = 255899) B255899
theorem B170761 : Blo 99781 170761 := bstep (se 2 (by rfl) ⟨64035, by rfl⟩ : syracuseStep 170761 = 128071) B128071
theorem B2464667 : Blo 99781 2464667 := bstep (se 1 (by rfl) ⟨1848500, by rfl⟩ : syracuseStep 2464667 = 3697001) B3697001
theorem B10623899 : Blo 99781 10623899 := bstep (se 1 (by rfl) ⟨7967924, by rfl⟩ : syracuseStep 10623899 = 15935849) B15935849
theorem B106591 : Blo 99781 106591 := bstep (se 1 (by rfl) ⟨79943, by rfl⟩ : syracuseStep 106591 = 159887) B159887
theorem B1188229 : Blo 99781 1188229 := bstep (se 4 (by rfl) ⟨111396, by rfl⟩ : syracuseStep 1188229 = 222793) B222793
theorem B9904841 : Blo 99781 9904841 := bstep (se 2 (by rfl) ⟨3714315, by rfl⟩ : syracuseStep 9904841 = 7428631) B7428631
theorem B533519 : Blo 99781 533519 := bstep (se 1 (by rfl) ⟨400139, by rfl⟩ : syracuseStep 533519 = 800279) B800279
theorem B173279 : Blo 99781 173279 := bstep (se 1 (by rfl) ⟨129959, by rfl⟩ : syracuseStep 173279 = 259919) B259919
theorem B337391 : Blo 99781 337391 := bstep (se 1 (by rfl) ⟨253043, by rfl⟩ : syracuseStep 337391 = 506087) B506087
theorem B304769 : Blo 99781 304769 := bstep (se 2 (by rfl) ⟨114288, by rfl⟩ : syracuseStep 304769 = 228577) B228577
theorem B272123 : Blo 99781 272123 := bstep (se 1 (by rfl) ⟨204092, by rfl⟩ : syracuseStep 272123 = 408185) B408185
theorem B174575 : Blo 99781 174575 := bstep (se 1 (by rfl) ⟨130931, by rfl⟩ : syracuseStep 174575 = 261863) B261863
theorem B2173513 : Blo 99781 2173513 := bstep (se 2 (by rfl) ⟨815067, by rfl⟩ : syracuseStep 2173513 = 1630135) B1630135
theorem B994301 : Blo 99781 994301 := bstep (se 3 (by rfl) ⟨186431, by rfl⟩ : syracuseStep 994301 = 372863) B372863
theorem B142879 : Blo 99781 142879 := bstep (se 1 (by rfl) ⟨107159, by rfl⟩ : syracuseStep 142879 = 214319) B214319
theorem B3518153 : Blo 99781 3518153 := bstep (se 2 (by rfl) ⟨1319307, by rfl⟩ : syracuseStep 3518153 = 2638615) B2638615
theorem B210127 : Blo 99781 210127 := bstep (se 1 (by rfl) ⟨157595, by rfl⟩ : syracuseStep 210127 = 315191) B315191
theorem B505439 : Blo 99781 505439 := bstep (se 1 (by rfl) ⟨379079, by rfl⟩ : syracuseStep 505439 = 758159) B758159
theorem B308861 : Blo 99781 308861 := bstep (se 3 (by rfl) ⟨57911, by rfl⟩ : syracuseStep 308861 = 115823) B115823
theorem B2537365 : Blo 99781 2537365 := bstep (se 6 (by rfl) ⟨59469, by rfl⟩ : syracuseStep 2537365 = 118939) B118939
theorem B440255 : Blo 99781 440255 := bstep (se 1 (by rfl) ⟨330191, by rfl⟩ : syracuseStep 440255 = 660383) B660383
theorem B1095929 : Blo 99781 1095929 := bstep (se 2 (by rfl) ⟨410973, by rfl⟩ : syracuseStep 1095929 = 821947) B821947
theorem B113647 : Blo 99781 113647 := bstep (se 1 (by rfl) ⟨85235, by rfl⟩ : syracuseStep 113647 = 170471) B170471
theorem B572903 : Blo 99781 572903 := bstep (se 1 (by rfl) ⟨429677, by rfl⟩ : syracuseStep 572903 = 859355) B859355
theorem B114223 : Blo 99781 114223 := bstep (se 1 (by rfl) ⟨85667, by rfl⟩ : syracuseStep 114223 = 171335) B171335
theorem B2571911 : Blo 99781 2571911 := bstep (se 1 (by rfl) ⟨1928933, by rfl⟩ : syracuseStep 2571911 = 3857867) B3857867
theorem B114331 : Blo 99781 114331 := bstep (se 1 (by rfl) ⟨85748, by rfl⟩ : syracuseStep 114331 = 171497) B171497
theorem B704335 : Blo 99781 704335 := bstep (se 1 (by rfl) ⟨528251, by rfl⟩ : syracuseStep 704335 = 1056503) B1056503
theorem B2801729 : Blo 99781 2801729 := bstep (se 2 (by rfl) ⟨1050648, by rfl⟩ : syracuseStep 2801729 = 2101297) B2101297
theorem B868481 : Blo 99781 868481 := bstep (se 2 (by rfl) ⟨325680, by rfl⟩ : syracuseStep 868481 = 651361) B651361
theorem B344681 : Blo 99781 344681 := bstep (se 2 (by rfl) ⟨129255, by rfl⟩ : syracuseStep 344681 = 258511) B258511
theorem B836477 : Blo 99781 836477 := bstep (se 3 (by rfl) ⟨156839, by rfl⟩ : syracuseStep 836477 = 313679) B313679
theorem B934841 : Blo 99781 934841 := bstep (se 2 (by rfl) ⟨350565, by rfl⟩ : syracuseStep 934841 = 701131) B701131
theorem B149687 : Blo 99781 149687 := bstep (se 1 (by rfl) ⟨112265, by rfl⟩ : syracuseStep 149687 = 224531) B224531
theorem B149711 : Blo 99781 149711 := bstep (se 1 (by rfl) ⟨112283, by rfl⟩ : syracuseStep 149711 = 224567) B224567
theorem B313727 : Blo 99781 313727 := bstep (se 1 (by rfl) ⟨235295, by rfl⟩ : syracuseStep 313727 = 470591) B470591
theorem B576071 : Blo 99781 576071 := bstep (se 1 (by rfl) ⟨432053, by rfl⟩ : syracuseStep 576071 = 864107) B864107
theorem B379475 : Blo 99781 379475 := bstep (se 1 (by rfl) ⟨284606, by rfl⟩ : syracuseStep 379475 = 569213) B569213
theorem B150107 : Blo 99781 150107 := bstep (se 1 (by rfl) ⟨112580, by rfl⟩ : syracuseStep 150107 = 225161) B225161
theorem B150251 : Blo 99781 150251 := bstep (se 1 (by rfl) ⟨112688, by rfl⟩ : syracuseStep 150251 = 225377) B225377
theorem B150281 : Blo 99781 150281 := bstep (se 2 (by rfl) ⟨56355, by rfl⟩ : syracuseStep 150281 = 112711) B112711
theorem B1723355 : Blo 99781 1723355 := bstep (se 1 (by rfl) ⟨1292516, by rfl⟩ : syracuseStep 1723355 = 2585033) B2585033
theorem B248903 : Blo 99781 248903 := bstep (se 1 (by rfl) ⟨186677, by rfl⟩ : syracuseStep 248903 = 373355) B373355
theorem B150695 : Blo 99781 150695 := bstep (se 1 (by rfl) ⟨113021, by rfl⟩ : syracuseStep 150695 = 226043) B226043
theorem B740627 : Blo 99781 740627 := bstep (se 1 (by rfl) ⟨555470, by rfl⟩ : syracuseStep 740627 = 1110941) B1110941
theorem B150839 : Blo 99781 150839 := bstep (se 1 (by rfl) ⟨113129, by rfl⟩ : syracuseStep 150839 = 226259) B226259
theorem B151151 : Blo 99781 151151 := bstep (se 1 (by rfl) ⟨113363, by rfl⟩ : syracuseStep 151151 = 226727) B226727
theorem B347759 : Blo 99781 347759 := bstep (se 1 (by rfl) ⟨260819, by rfl⟩ : syracuseStep 347759 = 521639) B521639
theorem B151223 : Blo 99781 151223 := bstep (se 1 (by rfl) ⟨113417, by rfl⟩ : syracuseStep 151223 = 226835) B226835
theorem B151271 : Blo 99781 151271 := bstep (se 1 (by rfl) ⟨113453, by rfl⟩ : syracuseStep 151271 = 226907) B226907
theorem B380659 : Blo 99781 380659 := bstep (se 1 (by rfl) ⟨285494, by rfl⟩ : syracuseStep 380659 = 570989) B570989
theorem B348029 : Blo 99781 348029 := bstep (se 3 (by rfl) ⟨65255, by rfl⟩ : syracuseStep 348029 = 130511) B130511
theorem B151433 : Blo 99781 151433 := bstep (se 2 (by rfl) ⟨56787, by rfl⟩ : syracuseStep 151433 = 113575) B113575
theorem B151673 : Blo 99781 151673 := bstep (se 2 (by rfl) ⟨56877, by rfl⟩ : syracuseStep 151673 = 113755) B113755
theorem B151679 : Blo 99781 151679 := bstep (se 1 (by rfl) ⟨113759, by rfl⟩ : syracuseStep 151679 = 227519) B227519
theorem B512243 : Blo 99781 512243 := bstep (se 1 (by rfl) ⟨384182, by rfl⟩ : syracuseStep 512243 = 768365) B768365
theorem B1102157 : Blo 99781 1102157 := bstep (se 3 (by rfl) ⟨206654, by rfl⟩ : syracuseStep 1102157 = 413309) B413309
theorem B3723731 : Blo 99781 3723731 := bstep (se 1 (by rfl) ⟨2792798, by rfl⟩ : syracuseStep 3723731 = 5585597) B5585597
theorem B578279 : Blo 99781 578279 := bstep (se 1 (by rfl) ⟨433709, by rfl⟩ : syracuseStep 578279 = 867419) B867419
theorem B152519 : Blo 99781 152519 := bstep (se 1 (by rfl) ⟨114389, by rfl⟩ : syracuseStep 152519 = 228779) B228779
theorem B152543 : Blo 99781 152543 := bstep (se 1 (by rfl) ⟨114407, by rfl⟩ : syracuseStep 152543 = 228815) B228815
theorem B152879 : Blo 99781 152879 := bstep (se 1 (by rfl) ⟨114659, by rfl⟩ : syracuseStep 152879 = 229319) B229319
theorem B1234379 : Blo 99781 1234379 := bstep (se 1 (by rfl) ⟨925784, by rfl⟩ : syracuseStep 1234379 = 1851569) B1851569
theorem B775655 : Blo 99781 775655 := bstep (se 1 (by rfl) ⟨581741, by rfl⟩ : syracuseStep 775655 = 1163483) B1163483
theorem B153083 : Blo 99781 153083 := bstep (se 1 (by rfl) ⟨114812, by rfl⟩ : syracuseStep 153083 = 229625) B229625
theorem B153119 : Blo 99781 153119 := bstep (se 1 (by rfl) ⟨114839, by rfl⟩ : syracuseStep 153119 = 229679) B229679
theorem B153257 : Blo 99781 153257 := bstep (se 2 (by rfl) ⟨57471, by rfl⟩ : syracuseStep 153257 = 114943) B114943
theorem B153263 : Blo 99781 153263 := bstep (se 1 (by rfl) ⟨114947, by rfl⟩ : syracuseStep 153263 = 229895) B229895
theorem B153383 : Blo 99781 153383 := bstep (se 1 (by rfl) ⟨115037, by rfl⟩ : syracuseStep 153383 = 230075) B230075
theorem B513863 : Blo 99781 513863 := bstep (se 1 (by rfl) ⟨385397, by rfl⟩ : syracuseStep 513863 = 770795) B770795
theorem B841711 : Blo 99781 841711 := bstep (se 1 (by rfl) ⟨631283, by rfl⟩ : syracuseStep 841711 = 1262567) B1262567
theorem B153641 : Blo 99781 153641 := bstep (se 2 (by rfl) ⟨57615, by rfl⟩ : syracuseStep 153641 = 115231) B115231
theorem B153671 : Blo 99781 153671 := bstep (se 1 (by rfl) ⟨115253, by rfl⟩ : syracuseStep 153671 = 230507) B230507
theorem B284903 : Blo 99781 284903 := bstep (se 1 (by rfl) ⟨213677, by rfl⟩ : syracuseStep 284903 = 427355) B427355
theorem B153983 : Blo 99781 153983 := bstep (se 1 (by rfl) ⟨115487, by rfl⟩ : syracuseStep 153983 = 230975) B230975
theorem B154055 : Blo 99781 154055 := bstep (se 1 (by rfl) ⟨115541, by rfl⟩ : syracuseStep 154055 = 231083) B231083
theorem B612839 : Blo 99781 612839 := bstep (se 1 (by rfl) ⟨459629, by rfl⟩ : syracuseStep 612839 = 919259) B919259
theorem B219743 : Blo 99781 219743 := bstep (se 1 (by rfl) ⟨164807, by rfl⟩ : syracuseStep 219743 = 329615) B329615
theorem B154271 : Blo 99781 154271 := bstep (se 1 (by rfl) ⟨115703, by rfl⟩ : syracuseStep 154271 = 231407) B231407
theorem B154415 : Blo 99781 154415 := bstep (se 1 (by rfl) ⟨115811, by rfl⟩ : syracuseStep 154415 = 231623) B231623
theorem B6282035 : Blo 99781 6282035 := bstep (se 1 (by rfl) ⟨4711526, by rfl⟩ : syracuseStep 6282035 = 9423053) B9423053
theorem B154505 : Blo 99781 154505 := bstep (se 2 (by rfl) ⟨57939, by rfl⟩ : syracuseStep 154505 = 115879) B115879
theorem B646055 : Blo 99781 646055 := bstep (se 1 (by rfl) ⟨484541, by rfl⟩ : syracuseStep 646055 = 969083) B969083
theorem B154535 : Blo 99781 154535 := bstep (se 1 (by rfl) ⟨115901, by rfl⟩ : syracuseStep 154535 = 231803) B231803
theorem B252953 : Blo 99781 252953 := bstep (se 2 (by rfl) ⟨94857, by rfl⟩ : syracuseStep 252953 = 189715) B189715
theorem B1629233 : Blo 99781 1629233 := bstep (se 2 (by rfl) ⟨610962, by rfl⟩ : syracuseStep 1629233 = 1221925) B1221925
theorem B154715 : Blo 99781 154715 := bstep (se 1 (by rfl) ⟨116036, by rfl⟩ : syracuseStep 154715 = 232073) B232073
theorem B253115 : Blo 99781 253115 := bstep (se 1 (by rfl) ⟨189836, by rfl⟩ : syracuseStep 253115 = 379673) B379673
theorem B154907 : Blo 99781 154907 := bstep (se 1 (by rfl) ⟨116180, by rfl⟩ : syracuseStep 154907 = 232361) B232361
theorem B286031 : Blo 99781 286031 := bstep (se 1 (by rfl) ⟨214523, by rfl⟩ : syracuseStep 286031 = 429047) B429047
theorem B220495 : Blo 99781 220495 := bstep (se 1 (by rfl) ⟨165371, by rfl⟩ : syracuseStep 220495 = 330743) B330743
theorem B548203 : Blo 99781 548203 := bstep (se 1 (by rfl) ⟨411152, by rfl⟩ : syracuseStep 548203 = 822305) B822305
theorem B155375 : Blo 99781 155375 := bstep (se 1 (by rfl) ⟨116531, by rfl⟩ : syracuseStep 155375 = 233063) B233063
theorem B253793 : Blo 99781 253793 := bstep (se 2 (by rfl) ⟨95172, by rfl⟩ : syracuseStep 253793 = 190345) B190345
theorem B155561 : Blo 99781 155561 := bstep (se 2 (by rfl) ⟨58335, by rfl⟩ : syracuseStep 155561 = 116671) B116671
theorem B1237493 : Blo 99781 1237493 := bstep (se 5 (by rfl) ⟨58007, by rfl⟩ : syracuseStep 1237493 = 116015) B116015
theorem B189631 : Blo 99781 189631 := bstep (se 1 (by rfl) ⟨142223, by rfl⟩ : syracuseStep 189631 = 284447) B284447
theorem B156907 : Blo 99781 156907 := bstep (se 1 (by rfl) ⟨117680, by rfl⟩ : syracuseStep 156907 = 235361) B235361
theorem B255251 : Blo 99781 255251 := bstep (se 1 (by rfl) ⟨191438, by rfl⟩ : syracuseStep 255251 = 382877) B382877
theorem B1238561 : Blo 99781 1238561 := bstep (se 2 (by rfl) ⟨464460, by rfl⟩ : syracuseStep 1238561 = 928921) B928921
theorem B321079 : Blo 99781 321079 := bstep (se 1 (by rfl) ⟨240809, by rfl⟩ : syracuseStep 321079 = 481619) B481619
theorem B5596739 : Blo 99781 5596739 := bstep (se 1 (by rfl) ⟨4197554, by rfl⟩ : syracuseStep 5596739 = 8395109) B8395109
theorem B255595 : Blo 99781 255595 := bstep (se 1 (by rfl) ⟨191696, by rfl⟩ : syracuseStep 255595 = 383393) B383393
theorem B157339 : Blo 99781 157339 := bstep (se 1 (by rfl) ⟨118004, by rfl⟩ : syracuseStep 157339 = 236009) B236009
theorem B157607 : Blo 99781 157607 := bstep (se 1 (by rfl) ⟨118205, by rfl⟩ : syracuseStep 157607 = 236411) B236411
theorem B256243 : Blo 99781 256243 := bstep (se 1 (by rfl) ⟨192182, by rfl⟩ : syracuseStep 256243 = 384365) B384365
theorem B321899 : Blo 99781 321899 := bstep (se 1 (by rfl) ⟨241424, by rfl⟩ : syracuseStep 321899 = 482849) B482849
theorem B289277 : Blo 99781 289277 := bstep (se 3 (by rfl) ⟨54239, by rfl⟩ : syracuseStep 289277 = 108479) B108479
theorem B256891 : Blo 99781 256891 := bstep (se 1 (by rfl) ⟨192668, by rfl⟩ : syracuseStep 256891 = 385337) B385337
theorem B257033 : Blo 99781 257033 := bstep (se 2 (by rfl) ⟨96387, by rfl⟩ : syracuseStep 257033 = 192775) B192775
theorem B650273 : Blo 99781 650273 := bstep (se 2 (by rfl) ⟨243852, by rfl⟩ : syracuseStep 650273 = 487705) B487705
theorem B257215 : Blo 99781 257215 := bstep (se 1 (by rfl) ⟨192911, by rfl⟩ : syracuseStep 257215 = 385823) B385823
theorem B519443 : Blo 99781 519443 := bstep (se 1 (by rfl) ⟨389582, by rfl⟩ : syracuseStep 519443 = 779165) B779165
theorem B257863 : Blo 99781 257863 := bstep (se 1 (by rfl) ⟨193397, by rfl⟩ : syracuseStep 257863 = 386795) B386795
theorem B585569 : Blo 99781 585569 := bstep (se 2 (by rfl) ⟨219588, by rfl⟩ : syracuseStep 585569 = 439177) B439177
theorem B258187 : Blo 99781 258187 := bstep (se 1 (by rfl) ⟨193640, by rfl⟩ : syracuseStep 258187 = 387281) B387281
theorem B159899 : Blo 99781 159899 := bstep (se 1 (by rfl) ⟨119924, by rfl⟩ : syracuseStep 159899 = 239849) B239849
theorem B258491 : Blo 99781 258491 := bstep (se 1 (by rfl) ⟨193868, by rfl⟩ : syracuseStep 258491 = 387737) B387737
theorem B160475 : Blo 99781 160475 := bstep (se 1 (by rfl) ⟨120356, by rfl⟩ : syracuseStep 160475 = 240713) B240713
theorem B226169 : Blo 99781 226169 := bstep (se 2 (by rfl) ⟨84813, by rfl⟩ : syracuseStep 226169 = 169627) B169627
theorem B226799 : Blo 99781 226799 := bstep (se 1 (by rfl) ⟨170099, by rfl⟩ : syracuseStep 226799 = 340199) B340199
theorem B521801 : Blo 99781 521801 := bstep (se 2 (by rfl) ⟨195675, by rfl⟩ : syracuseStep 521801 = 391351) B391351
theorem B259807 : Blo 99781 259807 := bstep (se 1 (by rfl) ⟨194855, by rfl⟩ : syracuseStep 259807 = 389711) B389711
theorem B227375 : Blo 99781 227375 := bstep (se 1 (by rfl) ⟨170531, by rfl⟩ : syracuseStep 227375 = 341063) B341063
theorem B522449 : Blo 99781 522449 := bstep (se 2 (by rfl) ⟨195918, by rfl⟩ : syracuseStep 522449 = 391837) B391837
theorem B1112363 : Blo 99781 1112363 := bstep (se 1 (by rfl) ⟨834272, by rfl⟩ : syracuseStep 1112363 = 1668545) B1668545
theorem B2488805 : Blo 99781 2488805 := bstep (se 4 (by rfl) ⟨233325, by rfl⟩ : syracuseStep 2488805 = 466651) B466651
theorem B260767 : Blo 99781 260767 := bstep (se 1 (by rfl) ⟨195575, by rfl⟩ : syracuseStep 260767 = 391151) B391151
theorem B228167 : Blo 99781 228167 := bstep (se 1 (by rfl) ⟨171125, by rfl⟩ : syracuseStep 228167 = 342251) B342251
theorem B129863 : Blo 99781 129863 := bstep (se 1 (by rfl) ⟨97397, by rfl⟩ : syracuseStep 129863 = 194795) B194795
theorem B130015 : Blo 99781 130015 := bstep (se 1 (by rfl) ⟨97511, by rfl⟩ : syracuseStep 130015 = 195023) B195023
theorem B162911 : Blo 99781 162911 := bstep (se 1 (by rfl) ⟨122183, by rfl⟩ : syracuseStep 162911 = 244367) B244367
theorem B262025 : Blo 99781 262025 := bstep (se 2 (by rfl) ⟨98259, by rfl⟩ : syracuseStep 262025 = 196519) B196519
theorem B262055 : Blo 99781 262055 := bstep (se 1 (by rfl) ⟨196541, by rfl⟩ : syracuseStep 262055 = 393083) B393083
theorem B524231 : Blo 99781 524231 := bstep (se 1 (by rfl) ⟨393173, by rfl⟩ : syracuseStep 524231 = 786347) B786347
theorem B1867819 : Blo 99781 1867819 := bstep (se 1 (by rfl) ⟨1400864, by rfl⟩ : syracuseStep 1867819 = 2801729) B2801729
theorem B196967 : Blo 99781 196967 := bstep (se 1 (by rfl) ⟨147725, by rfl⟩ : syracuseStep 196967 = 295451) B295451
theorem B229787 : Blo 99781 229787 := bstep (se 1 (by rfl) ⟨172340, by rfl⟩ : syracuseStep 229787 = 344681) B344681
theorem B426397 : Blo 99781 426397 := bstep (se 3 (by rfl) ⟨79949, by rfl⟩ : syracuseStep 426397 = 159899) B159899
theorem B262561 : Blo 99781 262561 := bstep (se 2 (by rfl) ⟨98460, by rfl⟩ : syracuseStep 262561 = 196921) B196921
theorem B557651 : Blo 99781 557651 := bstep (se 1 (by rfl) ⟨418238, by rfl⟩ : syracuseStep 557651 = 836477) B836477
theorem B623227 : Blo 99781 623227 := bstep (se 1 (by rfl) ⟨467420, by rfl⟩ : syracuseStep 623227 = 934841) B934841
theorem B1180979 : Blo 99781 1180979 := bstep (se 1 (by rfl) ⟨885734, by rfl⟩ : syracuseStep 1180979 = 1771469) B1771469
theorem B99791 : Blo 99781 99791 := bstep (se 1 (by rfl) ⟨74843, by rfl⟩ : syracuseStep 99791 = 149687) B149687
theorem B99807 : Blo 99781 99807 := bstep (se 1 (by rfl) ⟨74855, by rfl⟩ : syracuseStep 99807 = 149711) B149711
theorem B100071 : Blo 99781 100071 := bstep (se 1 (by rfl) ⟨75053, by rfl⟩ : syracuseStep 100071 = 150107) B150107
theorem B100167 : Blo 99781 100167 := bstep (se 1 (by rfl) ⟨75125, by rfl⟩ : syracuseStep 100167 = 150251) B150251
theorem B100187 : Blo 99781 100187 := bstep (se 1 (by rfl) ⟨75140, by rfl⟩ : syracuseStep 100187 = 150281) B150281
theorem B427933 : Blo 99781 427933 := bstep (se 3 (by rfl) ⟨80237, by rfl⟩ : syracuseStep 427933 = 160475) B160475
theorem B1148903 : Blo 99781 1148903 := bstep (se 1 (by rfl) ⟨861677, by rfl⟩ : syracuseStep 1148903 = 1723355) B1723355
theorem B165935 : Blo 99781 165935 := bstep (se 1 (by rfl) ⟨124451, by rfl⟩ : syracuseStep 165935 = 248903) B248903
theorem B428105 : Blo 99781 428105 := bstep (se 2 (by rfl) ⟨160539, by rfl⟩ : syracuseStep 428105 = 321079) B321079
theorem B100463 : Blo 99781 100463 := bstep (se 1 (by rfl) ⟨75347, by rfl⟩ : syracuseStep 100463 = 150695) B150695
theorem B493751 : Blo 99781 493751 := bstep (se 1 (by rfl) ⟨370313, by rfl⟩ : syracuseStep 493751 = 740627) B740627
theorem B100559 : Blo 99781 100559 := bstep (se 1 (by rfl) ⟨75419, by rfl⟩ : syracuseStep 100559 = 150839) B150839
theorem B100767 : Blo 99781 100767 := bstep (se 1 (by rfl) ⟨75575, by rfl⟩ : syracuseStep 100767 = 151151) B151151
theorem B231839 : Blo 99781 231839 := bstep (se 1 (by rfl) ⟨173879, by rfl⟩ : syracuseStep 231839 = 347759) B347759
theorem B100815 : Blo 99781 100815 := bstep (se 1 (by rfl) ⟨75611, by rfl⟩ : syracuseStep 100815 = 151223) B151223
theorem B100847 : Blo 99781 100847 := bstep (se 1 (by rfl) ⟨75635, by rfl⟩ : syracuseStep 100847 = 151271) B151271
theorem B232019 : Blo 99781 232019 := bstep (se 1 (by rfl) ⟨174014, by rfl⟩ : syracuseStep 232019 = 348029) B348029
theorem B100955 : Blo 99781 100955 := bstep (se 1 (by rfl) ⟨75716, by rfl⟩ : syracuseStep 100955 = 151433) B151433
theorem B101115 : Blo 99781 101115 := bstep (se 1 (by rfl) ⟨75836, by rfl⟩ : syracuseStep 101115 = 151673) B151673
theorem B101119 : Blo 99781 101119 := bstep (se 1 (by rfl) ⟨75839, by rfl⟩ : syracuseStep 101119 = 151679) B151679
theorem B101679 : Blo 99781 101679 := bstep (se 1 (by rfl) ⟨76259, by rfl⟩ : syracuseStep 101679 = 152519) B152519
theorem B101695 : Blo 99781 101695 := bstep (se 1 (by rfl) ⟨76271, by rfl⟩ : syracuseStep 101695 = 152543) B152543
theorem B986579 : Blo 99781 986579 := bstep (se 1 (by rfl) ⟨739934, by rfl⟩ : syracuseStep 986579 = 1479869) B1479869
theorem B101919 : Blo 99781 101919 := bstep (se 1 (by rfl) ⟨76439, by rfl⟩ : syracuseStep 101919 = 152879) B152879
theorem B102055 : Blo 99781 102055 := bstep (se 1 (by rfl) ⟨76541, by rfl⟩ : syracuseStep 102055 = 153083) B153083
theorem B102079 : Blo 99781 102079 := bstep (se 1 (by rfl) ⟨76559, by rfl⟩ : syracuseStep 102079 = 153119) B153119
theorem B102171 : Blo 99781 102171 := bstep (se 1 (by rfl) ⟨76628, by rfl⟩ : syracuseStep 102171 = 153257) B153257
theorem B102175 : Blo 99781 102175 := bstep (se 1 (by rfl) ⟨76631, by rfl⟩ : syracuseStep 102175 = 153263) B153263
theorem B102255 : Blo 99781 102255 := bstep (se 1 (by rfl) ⟨76691, by rfl⟩ : syracuseStep 102255 = 153383) B153383
theorem B102427 : Blo 99781 102427 := bstep (se 1 (by rfl) ⟨76820, by rfl⟩ : syracuseStep 102427 = 153641) B153641
theorem B102447 : Blo 99781 102447 := bstep (se 1 (by rfl) ⟨76835, by rfl⟩ : syracuseStep 102447 = 153671) B153671
theorem B102655 : Blo 99781 102655 := bstep (se 1 (by rfl) ⟨76991, by rfl⟩ : syracuseStep 102655 = 153983) B153983
theorem B102703 : Blo 99781 102703 := bstep (se 1 (by rfl) ⟨77027, by rfl⟩ : syracuseStep 102703 = 154055) B154055
theorem B102847 : Blo 99781 102847 := bstep (se 1 (by rfl) ⟨77135, by rfl⟩ : syracuseStep 102847 = 154271) B154271
theorem B102943 : Blo 99781 102943 := bstep (se 1 (by rfl) ⟨77207, by rfl⟩ : syracuseStep 102943 = 154415) B154415
theorem B103003 : Blo 99781 103003 := bstep (se 1 (by rfl) ⟨77252, by rfl⟩ : syracuseStep 103003 = 154505) B154505
theorem B1643111 : Blo 99781 1643111 := bstep (se 1 (by rfl) ⟨1232333, by rfl⟩ : syracuseStep 1643111 = 2464667) B2464667
theorem B7082599 : Blo 99781 7082599 := bstep (se 1 (by rfl) ⟨5311949, by rfl⟩ : syracuseStep 7082599 = 10623899) B10623899
theorem B430703 : Blo 99781 430703 := bstep (se 1 (by rfl) ⟨323027, by rfl⟩ : syracuseStep 430703 = 646055) B646055
theorem B103023 : Blo 99781 103023 := bstep (se 1 (by rfl) ⟨77267, by rfl⟩ : syracuseStep 103023 = 154535) B154535
theorem B168635 : Blo 99781 168635 := bstep (se 1 (by rfl) ⟨126476, by rfl⟩ : syracuseStep 168635 = 252953) B252953
theorem B1086155 : Blo 99781 1086155 := bstep (se 1 (by rfl) ⟨814616, by rfl⟩ : syracuseStep 1086155 = 1629233) B1629233
theorem B103143 : Blo 99781 103143 := bstep (se 1 (by rfl) ⟨77357, by rfl⟩ : syracuseStep 103143 = 154715) B154715
theorem B168743 : Blo 99781 168743 := bstep (se 1 (by rfl) ⟨126557, by rfl⟩ : syracuseStep 168743 = 253115) B253115
theorem B103271 : Blo 99781 103271 := bstep (se 1 (by rfl) ⟨77453, by rfl⟩ : syracuseStep 103271 = 154907) B154907
theorem B103583 : Blo 99781 103583 := bstep (se 1 (by rfl) ⟨77687, by rfl⟩ : syracuseStep 103583 = 155375) B155375
theorem B1971377 : Blo 99781 1971377 := bstep (se 2 (by rfl) ⟨739266, by rfl⟩ : syracuseStep 1971377 = 1478533) B1478533
theorem B169195 : Blo 99781 169195 := bstep (se 1 (by rfl) ⟨126896, by rfl⟩ : syracuseStep 169195 = 253793) B253793
theorem B103707 : Blo 99781 103707 := bstep (se 1 (by rfl) ⟨77780, by rfl⟩ : syracuseStep 103707 = 155561) B155561
theorem B824995 : Blo 99781 824995 := bstep (se 1 (by rfl) ⟨618746, by rfl⟩ : syracuseStep 824995 = 1237493) B1237493
theorem B530401 : Blo 99781 530401 := bstep (se 2 (by rfl) ⟨198900, by rfl⟩ : syracuseStep 530401 = 397801) B397801
theorem B1710233 : Blo 99781 1710233 := bstep (se 2 (by rfl) ⟨641337, by rfl⟩ : syracuseStep 1710233 = 1282675) B1282675
theorem B170167 : Blo 99781 170167 := bstep (se 1 (by rfl) ⟨127625, by rfl⟩ : syracuseStep 170167 = 255251) B255251
theorem B858397 : Blo 99781 858397 := bstep (se 3 (by rfl) ⟨160949, by rfl⟩ : syracuseStep 858397 = 321899) B321899
theorem B825707 : Blo 99781 825707 := bstep (se 1 (by rfl) ⟨619280, by rfl⟩ : syracuseStep 825707 = 1238561) B1238561
theorem B105071 : Blo 99781 105071 := bstep (se 1 (by rfl) ⟨78803, by rfl⟩ : syracuseStep 105071 = 157607) B157607
theorem B662867 : Blo 99781 662867 := bstep (se 1 (by rfl) ⟨497150, by rfl⟩ : syracuseStep 662867 = 994301) B994301
theorem B171355 : Blo 99781 171355 := bstep (se 1 (by rfl) ⟨128516, by rfl⟩ : syracuseStep 171355 = 257033) B257033
theorem B3383153 : Blo 99781 3383153 := bstep (se 2 (by rfl) ⟨1268682, by rfl⟩ : syracuseStep 3383153 = 2537365) B2537365
theorem B1122281 : Blo 99781 1122281 := bstep (se 2 (by rfl) ⟨420855, by rfl⟩ : syracuseStep 1122281 = 841711) B841711
theorem B434429 : Blo 99781 434429 := bstep (se 3 (by rfl) ⟨81455, by rfl⟩ : syracuseStep 434429 = 162911) B162911
theorem B172327 : Blo 99781 172327 := bstep (se 1 (by rfl) ⟨129245, by rfl⟩ : syracuseStep 172327 = 258491) B258491
theorem B336959 : Blo 99781 336959 := bstep (se 1 (by rfl) ⟨252719, by rfl⟩ : syracuseStep 336959 = 505439) B505439
theorem B205907 : Blo 99781 205907 := bstep (se 1 (by rfl) ⟨154430, by rfl⟩ : syracuseStep 205907 = 308861) B308861
theorem B173353 : Blo 99781 173353 := bstep (se 2 (by rfl) ⟨65007, by rfl⟩ : syracuseStep 173353 = 130015) B130015
theorem B730619 : Blo 99781 730619 := bstep (se 1 (by rfl) ⟨547964, by rfl⟩ : syracuseStep 730619 = 1095929) B1095929
theorem B730937 : Blo 99781 730937 := bstep (se 2 (by rfl) ⟨274101, by rfl⟩ : syracuseStep 730937 = 548203) B548203
theorem B1714607 : Blo 99781 1714607 := bstep (se 1 (by rfl) ⟨1285955, by rfl⟩ : syracuseStep 1714607 = 2571911) B2571911
theorem B174683 : Blo 99781 174683 := bstep (se 1 (by rfl) ⟨131012, by rfl⟩ : syracuseStep 174683 = 262025) B262025
theorem B174703 : Blo 99781 174703 := bstep (se 1 (by rfl) ⟨131027, by rfl⟩ : syracuseStep 174703 = 262055) B262055
theorem B142121 : Blo 99781 142121 := bstep (se 2 (by rfl) ⟨53295, by rfl⟩ : syracuseStep 142121 = 106591) B106591
theorem B1584305 : Blo 99781 1584305 := bstep (se 2 (by rfl) ⟨594114, by rfl⟩ : syracuseStep 1584305 = 1188229) B1188229
theorem B110495 : Blo 99781 110495 := bstep (se 1 (by rfl) ⟨82871, by rfl⟩ : syracuseStep 110495 = 165743) B165743
theorem B1258021 : Blo 99781 1258021 := bstep (se 4 (by rfl) ⟨117939, by rfl⟩ : syracuseStep 1258021 = 235879) B235879
theorem B340793 : Blo 99781 340793 := bstep (se 2 (by rfl) ⟨127797, by rfl⟩ : syracuseStep 340793 = 255595) B255595
theorem B209785 : Blo 99781 209785 := bstep (se 2 (by rfl) ⟨78669, by rfl⟩ : syracuseStep 209785 = 157339) B157339
theorem B1160567 : Blo 99781 1160567 := bstep (se 1 (by rfl) ⟨870425, by rfl⟩ : syracuseStep 1160567 = 1740851) B1740851
theorem B341495 : Blo 99781 341495 := bstep (se 1 (by rfl) ⟨256121, by rfl⟩ : syracuseStep 341495 = 512243) B512243
theorem B734771 : Blo 99781 734771 := bstep (se 1 (by rfl) ⟨551078, by rfl⟩ : syracuseStep 734771 = 1102157) B1102157
theorem B341657 : Blo 99781 341657 := bstep (se 2 (by rfl) ⟨128121, by rfl⟩ : syracuseStep 341657 = 256243) B256243
theorem B2898017 : Blo 99781 2898017 := bstep (se 2 (by rfl) ⟨1086756, by rfl⟩ : syracuseStep 2898017 = 2173513) B2173513
theorem B342521 : Blo 99781 342521 := bstep (se 2 (by rfl) ⟨128445, by rfl⟩ : syracuseStep 342521 = 256891) B256891
theorem B3291677 : Blo 99781 3291677 := bstep (se 3 (by rfl) ⟨617189, by rfl⟩ : syracuseStep 3291677 = 1234379) B1234379
theorem B342575 : Blo 99781 342575 := bstep (se 1 (by rfl) ⟨256931, by rfl⟩ : syracuseStep 342575 = 513863) B513863
theorem B768851 : Blo 99781 768851 := bstep (se 1 (by rfl) ⟨576638, by rfl⟩ : syracuseStep 768851 = 1153277) B1153277
theorem B441227 : Blo 99781 441227 := bstep (se 1 (by rfl) ⟨330920, by rfl⟩ : syracuseStep 441227 = 661841) B661841
theorem B342953 : Blo 99781 342953 := bstep (se 2 (by rfl) ⟨128607, by rfl⟩ : syracuseStep 342953 = 257215) B257215
theorem B408559 : Blo 99781 408559 := bstep (se 1 (by rfl) ⟨306419, by rfl⟩ : syracuseStep 408559 = 612839) B612839
theorem B146495 : Blo 99781 146495 := bstep (se 1 (by rfl) ⟨109871, by rfl⟩ : syracuseStep 146495 = 219743) B219743
theorem B507545 : Blo 99781 507545 := bstep (se 2 (by rfl) ⟨190329, by rfl⟩ : syracuseStep 507545 = 380659) B380659
theorem B343817 : Blo 99781 343817 := bstep (se 2 (by rfl) ⟨128931, by rfl⟩ : syracuseStep 343817 = 257863) B257863
theorem B344249 : Blo 99781 344249 := bstep (se 2 (by rfl) ⟨129093, by rfl⟩ : syracuseStep 344249 = 258187) B258187
theorem B6603227 : Blo 99781 6603227 := bstep (se 1 (by rfl) ⟨4952420, by rfl⟩ : syracuseStep 6603227 = 9904841) B9904841
theorem B115519 : Blo 99781 115519 := bstep (se 1 (by rfl) ⟨86639, by rfl⟩ : syracuseStep 115519 = 173279) B173279
theorem B967625 : Blo 99781 967625 := bstep (se 2 (by rfl) ⟨362859, by rfl⟩ : syracuseStep 967625 = 725719) B725719
theorem B836605 : Blo 99781 836605 := bstep (se 3 (by rfl) ⟨156863, by rfl⟩ : syracuseStep 836605 = 313727) B313727
theorem B181415 : Blo 99781 181415 := bstep (se 1 (by rfl) ⟨136061, by rfl⟩ : syracuseStep 181415 = 272123) B272123
theorem B836837 : Blo 99781 836837 := bstep (se 4 (by rfl) ⟨78453, by rfl⟩ : syracuseStep 836837 = 156907) B156907
theorem B280169 : Blo 99781 280169 := bstep (se 2 (by rfl) ⟨105063, by rfl⟩ : syracuseStep 280169 = 210127) B210127
theorem B116383 : Blo 99781 116383 := bstep (se 1 (by rfl) ⟨87287, by rfl⟩ : syracuseStep 116383 = 174575) B174575
theorem B346295 : Blo 99781 346295 := bstep (se 1 (by rfl) ⟨259721, by rfl⟩ : syracuseStep 346295 = 519443) B519443
theorem B346301 : Blo 99781 346301 := bstep (se 3 (by rfl) ⟨64931, by rfl⟩ : syracuseStep 346301 = 129863) B129863
theorem B346409 : Blo 99781 346409 := bstep (se 2 (by rfl) ⟨129903, by rfl⟩ : syracuseStep 346409 = 259807) B259807
theorem B2345435 : Blo 99781 2345435 := bstep (se 1 (by rfl) ⟨1759076, by rfl⟩ : syracuseStep 2345435 = 3518153) B3518153
theorem B183433 : Blo 99781 183433 := bstep (se 2 (by rfl) ⟨68787, by rfl⟩ : syracuseStep 183433 = 137575) B137575
theorem B183521 : Blo 99781 183521 := bstep (se 2 (by rfl) ⟨68820, by rfl⟩ : syracuseStep 183521 = 137641) B137641
theorem B150779 : Blo 99781 150779 := bstep (se 1 (by rfl) ⟨113084, by rfl⟩ : syracuseStep 150779 = 226169) B226169
theorem B347689 : Blo 99781 347689 := bstep (se 2 (by rfl) ⟨130383, by rfl⟩ : syracuseStep 347689 = 260767) B260767
theorem B151199 : Blo 99781 151199 := bstep (se 1 (by rfl) ⟨113399, by rfl⟩ : syracuseStep 151199 = 226799) B226799
theorem B347867 : Blo 99781 347867 := bstep (se 1 (by rfl) ⟨260900, by rfl⟩ : syracuseStep 347867 = 521801) B521801
theorem B151529 : Blo 99781 151529 := bstep (se 2 (by rfl) ⟨56823, by rfl⟩ : syracuseStep 151529 = 113647) B113647
theorem B151583 : Blo 99781 151583 := bstep (se 1 (by rfl) ⟨113687, by rfl⟩ : syracuseStep 151583 = 227375) B227375
theorem B348299 : Blo 99781 348299 := bstep (se 1 (by rfl) ⟨261224, by rfl⟩ : syracuseStep 348299 = 522449) B522449
theorem B741575 : Blo 99781 741575 := bstep (se 1 (by rfl) ⟨556181, by rfl⟩ : syracuseStep 741575 = 1112363) B1112363
theorem B1659203 : Blo 99781 1659203 := bstep (se 1 (by rfl) ⟨1244402, by rfl⟩ : syracuseStep 1659203 = 2488805) B2488805
theorem B152111 : Blo 99781 152111 := bstep (se 1 (by rfl) ⟨114083, by rfl⟩ : syracuseStep 152111 = 228167) B228167
theorem B152297 : Blo 99781 152297 := bstep (se 2 (by rfl) ⟨57111, by rfl⟩ : syracuseStep 152297 = 114223) B114223
theorem B152441 : Blo 99781 152441 := bstep (se 2 (by rfl) ⟨57165, by rfl⟩ : syracuseStep 152441 = 114331) B114331
theorem B381935 : Blo 99781 381935 := bstep (se 1 (by rfl) ⟨286451, by rfl⟩ : syracuseStep 381935 = 572903) B572903
theorem B939113 : Blo 99781 939113 := bstep (se 2 (by rfl) ⟨352167, by rfl⟩ : syracuseStep 939113 = 704335) B704335
theorem B349487 : Blo 99781 349487 := bstep (se 1 (by rfl) ⟨262115, by rfl⟩ : syracuseStep 349487 = 524231) B524231
theorem B578987 : Blo 99781 578987 := bstep (se 1 (by rfl) ⟨434240, by rfl⟩ : syracuseStep 578987 = 868481) B868481
theorem B153143 : Blo 99781 153143 := bstep (se 1 (by rfl) ⟨114857, by rfl⟩ : syracuseStep 153143 = 229715) B229715
theorem B349865 : Blo 99781 349865 := bstep (se 2 (by rfl) ⟨131199, by rfl⟩ : syracuseStep 349865 = 262399) B262399
theorem B22763477 : Blo 99781 22763477 := bstep (se 7 (by rfl) ⟨266759, by rfl⟩ : syracuseStep 22763477 = 533519) B533519
theorem B153647 : Blo 99781 153647 := bstep (se 1 (by rfl) ⟨115235, by rfl⟩ : syracuseStep 153647 = 230471) B230471
theorem B153767 : Blo 99781 153767 := bstep (se 1 (by rfl) ⟨115325, by rfl⟩ : syracuseStep 153767 = 230651) B230651
theorem B153935 : Blo 99781 153935 := bstep (se 1 (by rfl) ⟨115451, by rfl⟩ : syracuseStep 153935 = 230903) B230903
theorem B252841 : Blo 99781 252841 := bstep (se 2 (by rfl) ⟨94815, by rfl⟩ : syracuseStep 252841 = 189631) B189631
theorem B220153 : Blo 99781 220153 := bstep (se 2 (by rfl) ⟨82557, by rfl⟩ : syracuseStep 220153 = 165115) B165115
theorem B154655 : Blo 99781 154655 := bstep (se 1 (by rfl) ⟨115991, by rfl⟩ : syracuseStep 154655 = 231983) B231983
theorem B384047 : Blo 99781 384047 := bstep (se 1 (by rfl) ⟨288035, by rfl⟩ : syracuseStep 384047 = 576071) B576071
theorem B252983 : Blo 99781 252983 := bstep (se 1 (by rfl) ⟨189737, by rfl⟩ : syracuseStep 252983 = 379475) B379475
theorem B155087 : Blo 99781 155087 := bstep (se 1 (by rfl) ⟨116315, by rfl⟩ : syracuseStep 155087 = 232631) B232631
theorem B2482487 : Blo 99781 2482487 := bstep (se 1 (by rfl) ⟨1861865, by rfl⟩ : syracuseStep 2482487 = 3723731) B3723731
theorem B385519 : Blo 99781 385519 := bstep (se 1 (by rfl) ⟨289139, by rfl⟩ : syracuseStep 385519 = 578279) B578279
theorem B517103 : Blo 99781 517103 := bstep (se 1 (by rfl) ⟨387827, by rfl⟩ : syracuseStep 517103 = 775655) B775655
theorem B189935 : Blo 99781 189935 := bstep (se 1 (by rfl) ⟨142451, by rfl⟩ : syracuseStep 189935 = 284903) B284903
theorem B812717 : Blo 99781 812717 := bstep (se 3 (by rfl) ⟨152384, by rfl⟩ : syracuseStep 812717 = 304769) B304769
theorem B4188023 : Blo 99781 4188023 := bstep (se 1 (by rfl) ⟨3141017, by rfl⟩ : syracuseStep 4188023 = 6282035) B6282035
theorem B190505 : Blo 99781 190505 := bstep (se 2 (by rfl) ⟨71439, by rfl⟩ : syracuseStep 190505 = 142879) B142879
theorem B190687 : Blo 99781 190687 := bstep (se 1 (by rfl) ⟨143015, by rfl⟩ : syracuseStep 190687 = 286031) B286031
theorem B224927 : Blo 99781 224927 := bstep (se 1 (by rfl) ⟨168695, by rfl⟩ : syracuseStep 224927 = 337391) B337391
theorem B3731159 : Blo 99781 3731159 := bstep (se 1 (by rfl) ⟨2798369, by rfl⟩ : syracuseStep 3731159 = 5596739) B5596739
theorem B192851 : Blo 99781 192851 := bstep (se 1 (by rfl) ⟨144638, by rfl⟩ : syracuseStep 192851 = 289277) B289277
theorem B390379 : Blo 99781 390379 := bstep (se 1 (by rfl) ⟨292784, by rfl⟩ : syracuseStep 390379 = 585569) B585569
theorem B1734061 : Blo 99781 1734061 := bstep (se 3 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 1734061 = 650273) B650273
theorem B227465 : Blo 99781 227465 := bstep (se 2 (by rfl) ⟨85299, by rfl⟩ : syracuseStep 227465 = 170599) B170599
theorem B227681 : Blo 99781 227681 := bstep (se 2 (by rfl) ⟨85380, by rfl⟩ : syracuseStep 227681 = 170761) B170761
theorem B293503 : Blo 99781 293503 := bstep (se 1 (by rfl) ⟨220127, by rfl⟩ : syracuseStep 293503 = 440255) B440255
theorem B293993 : Blo 99781 293993 := bstep (se 2 (by rfl) ⟨110247, by rfl⟩ : syracuseStep 293993 = 220495) B220495
theorem B2490425 : Blo 99781 2490425 := bstep (se 2 (by rfl) ⟨933909, by rfl⟩ : syracuseStep 2490425 = 1867819) B1867819
theorem B229499 : Blo 99781 229499 := bstep (se 1 (by rfl) ⟨172124, by rfl⟩ : syracuseStep 229499 = 344249) B344249
theorem B131311 : Blo 99781 131311 := bstep (se 1 (by rfl) ⟨98483, by rfl⟩ : syracuseStep 131311 = 196967) B196967
theorem B229769 : Blo 99781 229769 := bstep (se 2 (by rfl) ⟨86163, by rfl⟩ : syracuseStep 229769 = 172327) B172327
theorem B557891 : Blo 99781 557891 := bstep (se 1 (by rfl) ⟨418418, by rfl⟩ : syracuseStep 557891 = 836837) B836837
theorem B2196341 : Blo 99781 2196341 := bstep (se 5 (by rfl) ⟨102953, by rfl⟩ : syracuseStep 2196341 = 205907) B205907
theorem B787319 : Blo 99781 787319 := bstep (se 1 (by rfl) ⟨590489, by rfl⟩ : syracuseStep 787319 = 1180979) B1180979
theorem B1115473 : Blo 99781 1115473 := bstep (se 2 (by rfl) ⟨418302, by rfl⟩ : syracuseStep 1115473 = 836605) B836605
theorem B329167 : Blo 99781 329167 := bstep (se 1 (by rfl) ⟨246875, by rfl⟩ : syracuseStep 329167 = 493751) B493751
theorem B230863 : Blo 99781 230863 := bstep (se 1 (by rfl) ⟨173147, by rfl⟩ : syracuseStep 230863 = 346295) B346295
theorem B230867 : Blo 99781 230867 := bstep (se 1 (by rfl) ⟨173150, by rfl⟩ : syracuseStep 230867 = 346301) B346301
theorem B230939 : Blo 99781 230939 := bstep (se 1 (by rfl) ⟨173204, by rfl⟩ : syracuseStep 230939 = 346409) B346409
theorem B231137 : Blo 99781 231137 := bstep (se 2 (by rfl) ⟨86676, by rfl⟩ : syracuseStep 231137 = 173353) B173353
theorem B100519 : Blo 99781 100519 := bstep (se 1 (by rfl) ⟨75389, by rfl⟩ : syracuseStep 100519 = 150779) B150779
theorem B657719 : Blo 99781 657719 := bstep (se 1 (by rfl) ⟨493289, by rfl⟩ : syracuseStep 657719 = 986579) B986579
theorem B100799 : Blo 99781 100799 := bstep (se 1 (by rfl) ⟨75599, by rfl⟩ : syracuseStep 100799 = 151199) B151199
theorem B231911 : Blo 99781 231911 := bstep (se 1 (by rfl) ⟨173933, by rfl⟩ : syracuseStep 231911 = 347867) B347867
theorem B101019 : Blo 99781 101019 := bstep (se 1 (by rfl) ⟨75764, by rfl⟩ : syracuseStep 101019 = 151529) B151529
theorem B101055 : Blo 99781 101055 := bstep (se 1 (by rfl) ⟨75791, by rfl⟩ : syracuseStep 101055 = 151583) B151583
theorem B232199 : Blo 99781 232199 := bstep (se 1 (by rfl) ⟨174149, by rfl⟩ : syracuseStep 232199 = 348299) B348299
theorem B494383 : Blo 99781 494383 := bstep (se 1 (by rfl) ⟨370787, by rfl⟩ : syracuseStep 494383 = 741575) B741575
theorem B101407 : Blo 99781 101407 := bstep (se 1 (by rfl) ⟨76055, by rfl⟩ : syracuseStep 101407 = 152111) B152111
theorem B724103 : Blo 99781 724103 := bstep (se 1 (by rfl) ⟨543077, by rfl⟩ : syracuseStep 724103 = 1086155) B1086155
theorem B101531 : Blo 99781 101531 := bstep (se 1 (by rfl) ⟨76148, by rfl⟩ : syracuseStep 101531 = 152297) B152297
theorem B101627 : Blo 99781 101627 := bstep (se 1 (by rfl) ⟨76220, by rfl⟩ : syracuseStep 101627 = 152441) B152441
theorem B626075 : Blo 99781 626075 := bstep (se 1 (by rfl) ⟨469556, by rfl⟩ : syracuseStep 626075 = 939113) B939113
theorem B1314251 : Blo 99781 1314251 := bstep (se 1 (by rfl) ⟨985688, by rfl⟩ : syracuseStep 1314251 = 1971377) B1971377
theorem B232937 : Blo 99781 232937 := bstep (se 2 (by rfl) ⟨87351, by rfl⟩ : syracuseStep 232937 = 174703) B174703
theorem B232991 : Blo 99781 232991 := bstep (se 1 (by rfl) ⟨174743, by rfl⟩ : syracuseStep 232991 = 349487) B349487
theorem B102095 : Blo 99781 102095 := bstep (se 1 (by rfl) ⟨76571, by rfl⟩ : syracuseStep 102095 = 153143) B153143
theorem B233243 : Blo 99781 233243 := bstep (se 1 (by rfl) ⟨174932, by rfl⟩ : syracuseStep 233243 = 349865) B349865
theorem B102431 : Blo 99781 102431 := bstep (se 1 (by rfl) ⟨76823, by rfl⟩ : syracuseStep 102431 = 153647) B153647
theorem B102511 : Blo 99781 102511 := bstep (se 1 (by rfl) ⟨76883, by rfl⟩ : syracuseStep 102511 = 153767) B153767
theorem B102623 : Blo 99781 102623 := bstep (se 1 (by rfl) ⟨76967, by rfl⟩ : syracuseStep 102623 = 153935) B153935
theorem B103103 : Blo 99781 103103 := bstep (se 1 (by rfl) ⟨77327, by rfl⟩ : syracuseStep 103103 = 154655) B154655
theorem B168655 : Blo 99781 168655 := bstep (se 1 (by rfl) ⟨126491, by rfl⟩ : syracuseStep 168655 = 252983) B252983
theorem B463585 : Blo 99781 463585 := bstep (se 2 (by rfl) ⟨173844, by rfl⟩ : syracuseStep 463585 = 347689) B347689
theorem B103391 : Blo 99781 103391 := bstep (se 1 (by rfl) ⟨77543, by rfl⟩ : syracuseStep 103391 = 155087) B155087
theorem B1677361 : Blo 99781 1677361 := bstep (se 2 (by rfl) ⟨629010, by rfl⟩ : syracuseStep 1677361 = 1258021) B1258021
theorem B9443465 : Blo 99781 9443465 := bstep (se 2 (by rfl) ⟨3541299, by rfl⟩ : syracuseStep 9443465 = 7082599) B7082599
theorem B2792015 : Blo 99781 2792015 := bstep (se 1 (by rfl) ⟨2094011, by rfl⟩ : syracuseStep 2792015 = 4188023) B4188023
theorem B1056203 : Blo 99781 1056203 := bstep (se 1 (by rfl) ⟨792152, by rfl⟩ : syracuseStep 1056203 = 1584305) B1584305
theorem B337121 : Blo 99781 337121 := bstep (se 2 (by rfl) ⟨126420, by rfl⟩ : syracuseStep 337121 = 252841) B252841
theorem B338363 : Blo 99781 338363 := bstep (se 1 (by rfl) ⟨253772, by rfl⟩ : syracuseStep 338363 = 507545) B507545
theorem B4402151 : Blo 99781 4402151 := bstep (se 1 (by rfl) ⟨3301613, by rfl⟩ : syracuseStep 4402151 = 6603227) B6603227
theorem B568529 : Blo 99781 568529 := bstep (se 2 (by rfl) ⟨213198, by rfl⟩ : syracuseStep 568529 = 426397) B426397
theorem B830969 : Blo 99781 830969 := bstep (se 2 (by rfl) ⟨311613, by rfl⟩ : syracuseStep 830969 = 623227) B623227
theorem B765935 : Blo 99781 765935 := bstep (se 1 (by rfl) ⟨574451, by rfl⟩ : syracuseStep 765935 = 1148903) B1148903
theorem B1487069 : Blo 99781 1487069 := bstep (se 3 (by rfl) ⟨278825, by rfl⟩ : syracuseStep 1487069 = 557651) B557651
theorem B570577 : Blo 99781 570577 := bstep (se 2 (by rfl) ⟨213966, by rfl⟩ : syracuseStep 570577 = 427933) B427933
theorem B1095407 : Blo 99781 1095407 := bstep (se 1 (by rfl) ⟨821555, by rfl⟩ : syracuseStep 1095407 = 1643111) B1643111
theorem B112423 : Blo 99781 112423 := bstep (se 1 (by rfl) ⟨84317, by rfl⟩ : syracuseStep 112423 = 168635) B168635
theorem B112495 : Blo 99781 112495 := bstep (se 1 (by rfl) ⟨84371, by rfl⟩ : syracuseStep 112495 = 168743) B168743
theorem B244577 : Blo 99781 244577 := bstep (se 2 (by rfl) ⟨91716, by rfl⟩ : syracuseStep 244577 = 183433) B183433
theorem B441911 : Blo 99781 441911 := bstep (se 1 (by rfl) ⟨331433, by rfl⟩ : syracuseStep 441911 = 662867) B662867
theorem B60702605 : Blo 99781 60702605 := bstep (se 3 (by rfl) ⟨11381738, by rfl⟩ : syracuseStep 60702605 = 22763477) B22763477
theorem B442493 : Blo 99781 442493 := bstep (se 3 (by rfl) ⟨82967, by rfl⟩ : syracuseStep 442493 = 165935) B165935
theorem B1654991 : Blo 99781 1654991 := bstep (se 1 (by rfl) ⟨1241243, by rfl⟩ : syracuseStep 1654991 = 2482487) B2482487
theorem B344735 : Blo 99781 344735 := bstep (se 1 (by rfl) ⟨258551, by rfl⟩ : syracuseStep 344735 = 517103) B517103
theorem B541811 : Blo 99781 541811 := bstep (se 1 (by rfl) ⟨406358, by rfl⟩ : syracuseStep 541811 = 812717) B812717
theorem B279713 : Blo 99781 279713 := bstep (se 2 (by rfl) ⟨104892, by rfl⟩ : syracuseStep 279713 = 209785) B209785
theorem B280189 : Blo 99781 280189 := bstep (se 3 (by rfl) ⟨52535, by rfl⟩ : syracuseStep 280189 = 105071) B105071
theorem B116455 : Blo 99781 116455 := bstep (se 1 (by rfl) ⟨87341, by rfl⟩ : syracuseStep 116455 = 174683) B174683
theorem B2312081 : Blo 99781 2312081 := bstep (se 2 (by rfl) ⟨867030, by rfl⟩ : syracuseStep 2312081 = 1734061) B1734061
theorem B378989 : Blo 99781 378989 := bstep (se 3 (by rfl) ⟨71060, by rfl⟩ : syracuseStep 378989 = 142121) B142121
theorem B1099993 : Blo 99781 1099993 := bstep (se 2 (by rfl) ⟨412497, by rfl⟩ : syracuseStep 1099993 = 824995) B824995
theorem B149951 : Blo 99781 149951 := bstep (se 1 (by rfl) ⟨112463, by rfl⟩ : syracuseStep 149951 = 224927) B224927
theorem B707201 : Blo 99781 707201 := bstep (se 2 (by rfl) ⟨265200, by rfl⟩ : syracuseStep 707201 = 530401) B530401
theorem B773711 : Blo 99781 773711 := bstep (se 1 (by rfl) ⟨580283, by rfl⟩ : syracuseStep 773711 = 1160567) B1160567
theorem B544745 : Blo 99781 544745 := bstep (se 2 (by rfl) ⟨204279, by rfl⟩ : syracuseStep 544745 = 408559) B408559
theorem B151643 : Blo 99781 151643 := bstep (se 1 (by rfl) ⟨113732, by rfl⟩ : syracuseStep 151643 = 227465) B227465
theorem B151787 : Blo 99781 151787 := bstep (se 1 (by rfl) ⟨113840, by rfl⟩ : syracuseStep 151787 = 227681) B227681
theorem B512567 : Blo 99781 512567 := bstep (se 1 (by rfl) ⟨384425, by rfl⟩ : syracuseStep 512567 = 768851) B768851
theorem B153191 : Blo 99781 153191 := bstep (se 1 (by rfl) ⟨114893, by rfl⟩ : syracuseStep 153191 = 229787) B229787
theorem B350081 : Blo 99781 350081 := bstep (se 2 (by rfl) ⟨131280, by rfl⟩ : syracuseStep 350081 = 262561) B262561
theorem B645083 : Blo 99781 645083 := bstep (se 1 (by rfl) ⟨483812, by rfl⟩ : syracuseStep 645083 = 967625) B967625
theorem B514025 : Blo 99781 514025 := bstep (se 2 (by rfl) ⟨192759, by rfl⟩ : syracuseStep 514025 = 385519) B385519
theorem B120943 : Blo 99781 120943 := bstep (se 1 (by rfl) ⟨90707, by rfl⟩ : syracuseStep 120943 = 181415) B181415
theorem B186779 : Blo 99781 186779 := bstep (se 1 (by rfl) ⟨140084, by rfl⟩ : syracuseStep 186779 = 280169) B280169
theorem B154025 : Blo 99781 154025 := bstep (se 2 (by rfl) ⟨57759, by rfl⟩ : syracuseStep 154025 = 115519) B115519
theorem B154559 : Blo 99781 154559 := bstep (se 1 (by rfl) ⟨115919, by rfl⟩ : syracuseStep 154559 = 231839) B231839
theorem B1563623 : Blo 99781 1563623 := bstep (se 1 (by rfl) ⟨1172717, by rfl⟩ : syracuseStep 1563623 = 2345435) B2345435
theorem B154679 : Blo 99781 154679 := bstep (se 1 (by rfl) ⟨116009, by rfl⟩ : syracuseStep 154679 = 232019) B232019
theorem B122347 : Blo 99781 122347 := bstep (se 1 (by rfl) ⟨91760, by rfl⟩ : syracuseStep 122347 = 183521) B183521
theorem B155177 : Blo 99781 155177 := bstep (se 2 (by rfl) ⟨58191, by rfl⟩ : syracuseStep 155177 = 116383) B116383
theorem B1106135 : Blo 99781 1106135 := bstep (se 1 (by rfl) ⟨829601, by rfl⟩ : syracuseStep 1106135 = 1659203) B1659203
theorem B254249 : Blo 99781 254249 := bstep (se 2 (by rfl) ⟨95343, by rfl⟩ : syracuseStep 254249 = 190687) B190687
theorem B287135 : Blo 99781 287135 := bstep (se 1 (by rfl) ⟨215351, by rfl⟩ : syracuseStep 287135 = 430703) B430703
theorem B254623 : Blo 99781 254623 := bstep (se 1 (by rfl) ⟨190967, by rfl⟩ : syracuseStep 254623 = 381935) B381935
theorem B385991 : Blo 99781 385991 := bstep (se 1 (by rfl) ⟨289493, by rfl⟩ : syracuseStep 385991 = 578987) B578987
theorem B1140155 : Blo 99781 1140155 := bstep (se 1 (by rfl) ⟨855116, by rfl⟩ : syracuseStep 1140155 = 1710233) B1710233
theorem B550471 : Blo 99781 550471 := bstep (se 1 (by rfl) ⟨412853, by rfl⟩ : syracuseStep 550471 = 825707) B825707
theorem B256031 : Blo 99781 256031 := bstep (se 1 (by rfl) ⟨192023, by rfl⟩ : syracuseStep 256031 = 384047) B384047
theorem B2255435 : Blo 99781 2255435 := bstep (se 1 (by rfl) ⟨1691576, by rfl⟩ : syracuseStep 2255435 = 3383153) B3383153
theorem B748187 : Blo 99781 748187 := bstep (se 1 (by rfl) ⟨561140, by rfl⟩ : syracuseStep 748187 = 1122281) B1122281
theorem B289619 : Blo 99781 289619 := bstep (se 1 (by rfl) ⟨217214, by rfl⟩ : syracuseStep 289619 = 434429) B434429
theorem B1141613 : Blo 99781 1141613 := bstep (se 3 (by rfl) ⟨214052, by rfl⟩ : syracuseStep 1141613 = 428105) B428105
theorem B224639 : Blo 99781 224639 := bstep (se 1 (by rfl) ⟨168479, by rfl⟩ : syracuseStep 224639 = 336959) B336959
theorem B126623 : Blo 99781 126623 := bstep (se 1 (by rfl) ⟨94967, by rfl⟩ : syracuseStep 126623 = 189935) B189935
theorem B487079 : Blo 99781 487079 := bstep (se 1 (by rfl) ⟨365309, by rfl⟩ : syracuseStep 487079 = 730619) B730619
theorem B487291 : Blo 99781 487291 := bstep (se 1 (by rfl) ⟨365468, by rfl⟩ : syracuseStep 487291 = 730937) B730937
theorem B127003 : Blo 99781 127003 := bstep (se 1 (by rfl) ⟨95252, by rfl⟩ : syracuseStep 127003 = 190505) B190505
theorem B1143071 : Blo 99781 1143071 := bstep (se 1 (by rfl) ⟨857303, by rfl⟩ : syracuseStep 1143071 = 1714607) B1714607
theorem B225593 : Blo 99781 225593 := bstep (se 2 (by rfl) ⟨84597, by rfl⟩ : syracuseStep 225593 = 169195) B169195
theorem B520505 : Blo 99781 520505 := bstep (se 2 (by rfl) ⟨195189, by rfl⟩ : syracuseStep 520505 = 390379) B390379
theorem B1176605 : Blo 99781 1176605 := bstep (se 3 (by rfl) ⟨220613, by rfl⟩ : syracuseStep 1176605 = 441227) B441227
theorem B2487439 : Blo 99781 2487439 := bstep (se 1 (by rfl) ⟨1865579, by rfl⟩ : syracuseStep 2487439 = 3731159) B3731159
theorem B390653 : Blo 99781 390653 := bstep (se 3 (by rfl) ⟨73247, by rfl⟩ : syracuseStep 390653 = 146495) B146495
theorem B128567 : Blo 99781 128567 := bstep (se 1 (by rfl) ⟨96425, by rfl⟩ : syracuseStep 128567 = 192851) B192851
theorem B226889 : Blo 99781 226889 := bstep (se 2 (by rfl) ⟨85083, by rfl⟩ : syracuseStep 226889 = 170167) B170167
theorem B1144529 : Blo 99781 1144529 := bstep (se 2 (by rfl) ⟨429198, by rfl⟩ : syracuseStep 1144529 = 858397) B858397
theorem B227195 : Blo 99781 227195 := bstep (se 1 (by rfl) ⟨170396, by rfl⟩ : syracuseStep 227195 = 340793) B340793
theorem B391337 : Blo 99781 391337 := bstep (se 2 (by rfl) ⟨146751, by rfl⟩ : syracuseStep 391337 = 293503) B293503
theorem B227663 : Blo 99781 227663 := bstep (se 1 (by rfl) ⟨170747, by rfl⟩ : syracuseStep 227663 = 341495) B341495
theorem B489847 : Blo 99781 489847 := bstep (se 1 (by rfl) ⟨367385, by rfl⟩ : syracuseStep 489847 = 734771) B734771
theorem B227771 : Blo 99781 227771 := bstep (se 1 (by rfl) ⟨170828, by rfl⟩ : syracuseStep 227771 = 341657) B341657
theorem B293537 : Blo 99781 293537 := bstep (se 2 (by rfl) ⟨110076, by rfl⟩ : syracuseStep 293537 = 220153) B220153
theorem B1932011 : Blo 99781 1932011 := bstep (se 1 (by rfl) ⟨1449008, by rfl⟩ : syracuseStep 1932011 = 2898017) B2898017
theorem B228347 : Blo 99781 228347 := bstep (se 1 (by rfl) ⟨171260, by rfl⟩ : syracuseStep 228347 = 342521) B342521
theorem B2194451 : Blo 99781 2194451 := bstep (se 1 (by rfl) ⟨1645838, by rfl⟩ : syracuseStep 2194451 = 3291677) B3291677
theorem B228383 : Blo 99781 228383 := bstep (se 1 (by rfl) ⟨171287, by rfl⟩ : syracuseStep 228383 = 342575) B342575
theorem B228473 : Blo 99781 228473 := bstep (se 2 (by rfl) ⟨85677, by rfl⟩ : syracuseStep 228473 = 171355) B171355
theorem B228635 : Blo 99781 228635 := bstep (se 1 (by rfl) ⟨171476, by rfl⟩ : syracuseStep 228635 = 342953) B342953
theorem B195995 : Blo 99781 195995 := bstep (se 1 (by rfl) ⟨146996, by rfl⟩ : syracuseStep 195995 = 293993) B293993
theorem B294653 : Blo 99781 294653 := bstep (se 3 (by rfl) ⟨55247, by rfl⟩ : syracuseStep 294653 = 110495) B110495
theorem B229211 : Blo 99781 229211 := bstep (se 1 (by rfl) ⟨171908, by rfl⟩ : syracuseStep 229211 = 343817) B343817
theorem B294995 : Blo 99781 294995 := bstep (se 1 (by rfl) ⟨221246, by rfl⟩ : syracuseStep 294995 = 442493) B442493
theorem B229823 : Blo 99781 229823 := bstep (se 1 (by rfl) ⟨172367, by rfl⟩ : syracuseStep 229823 = 344735) B344735
theorem B524879 : Blo 99781 524879 := bstep (se 1 (by rfl) ⟨393659, by rfl⟩ : syracuseStep 524879 = 787319) B787319
theorem B361207 : Blo 99781 361207 := bstep (se 1 (by rfl) ⟨270905, by rfl⟩ : syracuseStep 361207 = 541811) B541811
theorem B1541387 : Blo 99781 1541387 := bstep (se 1 (by rfl) ⟨1156040, by rfl⟩ : syracuseStep 1541387 = 2312081) B2312081
theorem B99967 : Blo 99781 99967 := bstep (se 1 (by rfl) ⟨74975, by rfl⟩ : syracuseStep 99967 = 149951) B149951
theorem B363163 : Blo 99781 363163 := bstep (se 1 (by rfl) ⟨272372, by rfl⟩ : syracuseStep 363163 = 544745) B544745
theorem B101095 : Blo 99781 101095 := bstep (se 1 (by rfl) ⟨75821, by rfl⟩ : syracuseStep 101095 = 151643) B151643
theorem B101191 : Blo 99781 101191 := bstep (se 1 (by rfl) ⟨75893, by rfl⟩ : syracuseStep 101191 = 151787) B151787
theorem B659177 : Blo 99781 659177 := bstep (se 2 (by rfl) ⟨247191, by rfl⟩ : syracuseStep 659177 = 494383) B494383
theorem B102127 : Blo 99781 102127 := bstep (se 1 (by rfl) ⟨76595, by rfl⟩ : syracuseStep 102127 = 153191) B153191
theorem B233387 : Blo 99781 233387 := bstep (se 1 (by rfl) ⟨175040, by rfl⟩ : syracuseStep 233387 = 350081) B350081
theorem B430055 : Blo 99781 430055 := bstep (se 1 (by rfl) ⟨322541, by rfl⟩ : syracuseStep 430055 = 645083) B645083
theorem B6295643 : Blo 99781 6295643 := bstep (se 1 (by rfl) ⟨4721732, by rfl⟩ : syracuseStep 6295643 = 9443465) B9443465
theorem B102683 : Blo 99781 102683 := bstep (se 1 (by rfl) ⟨77012, by rfl⟩ : syracuseStep 102683 = 154025) B154025
theorem B103039 : Blo 99781 103039 := bstep (se 1 (by rfl) ⟨77279, by rfl⟩ : syracuseStep 103039 = 154559) B154559
theorem B103119 : Blo 99781 103119 := bstep (se 1 (by rfl) ⟨77339, by rfl⟩ : syracuseStep 103119 = 154679) B154679
theorem B103451 : Blo 99781 103451 := bstep (se 1 (by rfl) ⟨77588, by rfl⟩ : syracuseStep 103451 = 155177) B155177
theorem B169337 : Blo 99781 169337 := bstep (se 2 (by rfl) ⟨63501, by rfl⟩ : syracuseStep 169337 = 127003) B127003
theorem B169499 : Blo 99781 169499 := bstep (se 1 (by rfl) ⟨127124, by rfl⟩ : syracuseStep 169499 = 254249) B254249
theorem B760103 : Blo 99781 760103 := bstep (se 1 (by rfl) ⟨570077, by rfl⟩ : syracuseStep 760103 = 1140155) B1140155
theorem B170687 : Blo 99781 170687 := bstep (se 1 (by rfl) ⟨128015, by rfl⟩ : syracuseStep 170687 = 256031) B256031
theorem B3316585 : Blo 99781 3316585 := bstep (se 2 (by rfl) ⟨1243719, by rfl⟩ : syracuseStep 3316585 = 2487439) B2487439
theorem B760769 : Blo 99781 760769 := bstep (se 2 (by rfl) ⟨285288, by rfl⟩ : syracuseStep 760769 = 570577) B570577
theorem B498791 : Blo 99781 498791 := bstep (se 1 (by rfl) ⟨374093, by rfl⟩ : syracuseStep 498791 = 748187) B748187
theorem B761075 : Blo 99781 761075 := bstep (se 1 (by rfl) ⟨570806, by rfl⟩ : syracuseStep 761075 = 1141613) B1141613
theorem B2236481 : Blo 99781 2236481 := bstep (se 2 (by rfl) ⟨838680, by rfl⟩ : syracuseStep 2236481 = 1677361) B1677361
theorem B991379 : Blo 99781 991379 := bstep (se 1 (by rfl) ⟨743534, by rfl⟩ : syracuseStep 991379 = 1487069) B1487069
theorem B762047 : Blo 99781 762047 := bstep (se 1 (by rfl) ⟨571535, by rfl⟩ : syracuseStep 762047 = 1143071) B1143071
theorem B763019 : Blo 99781 763019 := bstep (se 1 (by rfl) ⟨572264, by rfl⟩ : syracuseStep 763019 = 1144529) B1144529
theorem B730271 : Blo 99781 730271 := bstep (se 1 (by rfl) ⟨547703, by rfl⟩ : syracuseStep 730271 = 1095407) B1095407
theorem B337661 : Blo 99781 337661 := bstep (se 3 (by rfl) ⟨63311, by rfl⟩ : syracuseStep 337661 = 126623) B126623
theorem B1288007 : Blo 99781 1288007 := bstep (se 1 (by rfl) ⟨966005, by rfl⟩ : syracuseStep 1288007 = 1932011) B1932011
theorem B175081 : Blo 99781 175081 := bstep (se 2 (by rfl) ⟨65655, by rfl⟩ : syracuseStep 175081 = 131311) B131311
theorem B371927 : Blo 99781 371927 := bstep (se 1 (by rfl) ⟨278945, by rfl⟩ : syracuseStep 371927 = 557891) B557891
theorem B339497 : Blo 99781 339497 := bstep (se 2 (by rfl) ⟨127311, by rfl⟩ : syracuseStep 339497 = 254623) B254623
theorem B438479 : Blo 99781 438479 := bstep (se 1 (by rfl) ⟨328859, by rfl⟩ : syracuseStep 438479 = 657719) B657719
theorem B471467 : Blo 99781 471467 := bstep (se 1 (by rfl) ⟨353600, by rfl⟩ : syracuseStep 471467 = 707201) B707201
theorem B1487297 : Blo 99781 1487297 := bstep (se 2 (by rfl) ⟨557736, by rfl⟩ : syracuseStep 1487297 = 1115473) B1115473
theorem B438889 : Blo 99781 438889 := bstep (se 2 (by rfl) ⟨164583, by rfl⟩ : syracuseStep 438889 = 329167) B329167
theorem B307817 : Blo 99781 307817 := bstep (se 2 (by rfl) ⟨115431, by rfl⟩ : syracuseStep 307817 = 230863) B230863
theorem B733961 : Blo 99781 733961 := bstep (se 2 (by rfl) ⟨275235, by rfl⟩ : syracuseStep 733961 = 550471) B550471
theorem B373585 : Blo 99781 373585 := bstep (se 2 (by rfl) ⟨140094, by rfl⟩ : syracuseStep 373585 = 280189) B280189
theorem B341711 : Blo 99781 341711 := bstep (se 1 (by rfl) ⟨256283, by rfl⟩ : syracuseStep 341711 = 512567) B512567
theorem B342683 : Blo 99781 342683 := bstep (se 1 (by rfl) ⟨257012, by rfl⟩ : syracuseStep 342683 = 514025) B514025
theorem B342845 : Blo 99781 342845 := bstep (se 3 (by rfl) ⟨64283, by rfl⟩ : syracuseStep 342845 = 128567) B128567
theorem B704135 : Blo 99781 704135 := bstep (se 1 (by rfl) ⟨528101, by rfl⟩ : syracuseStep 704135 = 1056203) B1056203
theorem B737423 : Blo 99781 737423 := bstep (se 1 (by rfl) ⟨553067, by rfl⟩ : syracuseStep 737423 = 1106135) B1106135
theorem B2934767 : Blo 99781 2934767 := bstep (se 1 (by rfl) ⟨2201075, by rfl⟩ : syracuseStep 2934767 = 4402151) B4402151
theorem B379019 : Blo 99781 379019 := bstep (se 1 (by rfl) ⟨284264, by rfl⟩ : syracuseStep 379019 = 568529) B568529
theorem B149759 : Blo 99781 149759 := bstep (se 1 (by rfl) ⟨112319, by rfl⟩ : syracuseStep 149759 = 224639) B224639
theorem B149897 : Blo 99781 149897 := bstep (se 2 (by rfl) ⟨56211, by rfl⟩ : syracuseStep 149897 = 112423) B112423
theorem B149993 : Blo 99781 149993 := bstep (se 2 (by rfl) ⟨56247, by rfl⟩ : syracuseStep 149993 = 112495) B112495
theorem B510623 : Blo 99781 510623 := bstep (se 1 (by rfl) ⟨382967, by rfl⟩ : syracuseStep 510623 = 765935) B765935
theorem B150395 : Blo 99781 150395 := bstep (se 1 (by rfl) ⟨112796, by rfl⟩ : syracuseStep 150395 = 225593) B225593
theorem B347003 : Blo 99781 347003 := bstep (se 1 (by rfl) ⟨260252, by rfl⟩ : syracuseStep 347003 = 520505) B520505
theorem B151259 : Blo 99781 151259 := bstep (se 1 (by rfl) ⟨113444, by rfl⟩ : syracuseStep 151259 = 226889) B226889
theorem B151463 : Blo 99781 151463 := bstep (se 1 (by rfl) ⟨113597, by rfl⟩ : syracuseStep 151463 = 227195) B227195
theorem B151775 : Blo 99781 151775 := bstep (se 1 (by rfl) ⟨113831, by rfl⟩ : syracuseStep 151775 = 227663) B227663
theorem B151847 : Blo 99781 151847 := bstep (se 1 (by rfl) ⟨113885, by rfl⟩ : syracuseStep 151847 = 227771) B227771
theorem B152231 : Blo 99781 152231 := bstep (se 1 (by rfl) ⟨114173, by rfl⟩ : syracuseStep 152231 = 228347) B228347
theorem B1462967 : Blo 99781 1462967 := bstep (se 1 (by rfl) ⟨1097225, by rfl⟩ : syracuseStep 1462967 = 2194451) B2194451
theorem B152255 : Blo 99781 152255 := bstep (se 1 (by rfl) ⟨114191, by rfl⟩ : syracuseStep 152255 = 228383) B228383
theorem B152315 : Blo 99781 152315 := bstep (se 1 (by rfl) ⟨114236, by rfl⟩ : syracuseStep 152315 = 228473) B228473
theorem B152423 : Blo 99781 152423 := bstep (se 1 (by rfl) ⟨114317, by rfl⟩ : syracuseStep 152423 = 228635) B228635
theorem B152807 : Blo 99781 152807 := bstep (se 1 (by rfl) ⟨114605, by rfl⟩ : syracuseStep 152807 = 229211) B229211
theorem B1660283 : Blo 99781 1660283 := bstep (se 1 (by rfl) ⟨1245212, by rfl⟩ : syracuseStep 1660283 = 2490425) B2490425
theorem B152999 : Blo 99781 152999 := bstep (se 1 (by rfl) ⟨114749, by rfl⟩ : syracuseStep 152999 = 229499) B229499
theorem B1103327 : Blo 99781 1103327 := bstep (se 1 (by rfl) ⟨827495, by rfl⟩ : syracuseStep 1103327 = 1654991) B1654991
theorem B153179 : Blo 99781 153179 := bstep (se 1 (by rfl) ⟨114884, by rfl⟩ : syracuseStep 153179 = 229769) B229769
theorem B1464227 : Blo 99781 1464227 := bstep (se 1 (by rfl) ⟨1098170, by rfl⟩ : syracuseStep 1464227 = 2196341) B2196341
theorem B645029 : Blo 99781 645029 := bstep (se 4 (by rfl) ⟨60471, by rfl⟩ : syracuseStep 645029 = 120943) B120943
theorem B186475 : Blo 99781 186475 := bstep (se 1 (by rfl) ⟨139856, by rfl⟩ : syracuseStep 186475 = 279713) B279713
theorem B153911 : Blo 99781 153911 := bstep (se 1 (by rfl) ⟨115433, by rfl⟩ : syracuseStep 153911 = 230867) B230867
theorem B153959 : Blo 99781 153959 := bstep (se 1 (by rfl) ⟨115469, by rfl⟩ : syracuseStep 153959 = 230939) B230939
theorem B154091 : Blo 99781 154091 := bstep (se 1 (by rfl) ⟨115568, by rfl⟩ : syracuseStep 154091 = 231137) B231137
theorem B252659 : Blo 99781 252659 := bstep (se 1 (by rfl) ⟨189494, by rfl⟩ : syracuseStep 252659 = 378989) B378989
theorem B154607 : Blo 99781 154607 := bstep (se 1 (by rfl) ⟨115955, by rfl⟩ : syracuseStep 154607 = 231911) B231911
theorem B154799 : Blo 99781 154799 := bstep (se 1 (by rfl) ⟨116099, by rfl⟩ : syracuseStep 154799 = 232199) B232199
theorem B482735 : Blo 99781 482735 := bstep (se 1 (by rfl) ⟨362051, by rfl⟩ : syracuseStep 482735 = 724103) B724103
theorem B417383 : Blo 99781 417383 := bstep (se 1 (by rfl) ⟨313037, by rfl⟩ : syracuseStep 417383 = 626075) B626075
theorem B876167 : Blo 99781 876167 := bstep (se 1 (by rfl) ⟨657125, by rfl⟩ : syracuseStep 876167 = 1314251) B1314251
theorem B155273 : Blo 99781 155273 := bstep (se 2 (by rfl) ⟨58227, by rfl⟩ : syracuseStep 155273 = 116455) B116455
theorem B155291 : Blo 99781 155291 := bstep (se 1 (by rfl) ⟨116468, by rfl⟩ : syracuseStep 155291 = 232937) B232937
theorem B155327 : Blo 99781 155327 := bstep (se 1 (by rfl) ⟨116495, by rfl⟩ : syracuseStep 155327 = 232991) B232991
theorem B515807 : Blo 99781 515807 := bstep (se 1 (by rfl) ⟨386855, by rfl⟩ : syracuseStep 515807 = 773711) B773711
theorem B155495 : Blo 99781 155495 := bstep (se 1 (by rfl) ⟨116621, by rfl⟩ : syracuseStep 155495 = 233243) B233243
theorem B1466657 : Blo 99781 1466657 := bstep (se 2 (by rfl) ⟨549996, by rfl⟩ : syracuseStep 1466657 = 1099993) B1099993
theorem B124519 : Blo 99781 124519 := bstep (se 1 (by rfl) ⟨93389, by rfl⟩ : syracuseStep 124519 = 186779) B186779
theorem B1861343 : Blo 99781 1861343 := bstep (se 1 (by rfl) ⟨1396007, by rfl⟩ : syracuseStep 1861343 = 2792015) B2792015
theorem B1042415 : Blo 99781 1042415 := bstep (se 1 (by rfl) ⟨781811, by rfl⟩ : syracuseStep 1042415 = 1563623) B1563623
theorem B649721 : Blo 99781 649721 := bstep (se 2 (by rfl) ⟨243645, by rfl⟩ : syracuseStep 649721 = 487291) B487291
theorem B191423 : Blo 99781 191423 := bstep (se 1 (by rfl) ⟨143567, by rfl⟩ : syracuseStep 191423 = 287135) B287135
theorem B257327 : Blo 99781 257327 := bstep (se 1 (by rfl) ⟨192995, by rfl⟩ : syracuseStep 257327 = 385991) B385991
theorem B224747 : Blo 99781 224747 := bstep (se 1 (by rfl) ⟨168560, by rfl⟩ : syracuseStep 224747 = 337121) B337121
theorem B224873 : Blo 99781 224873 := bstep (se 2 (by rfl) ⟨84327, by rfl⟩ : syracuseStep 224873 = 168655) B168655
theorem B618113 : Blo 99781 618113 := bstep (se 2 (by rfl) ⟨231792, by rfl⟩ : syracuseStep 618113 = 463585) B463585
theorem B225575 : Blo 99781 225575 := bstep (se 1 (by rfl) ⟨169181, by rfl⟩ : syracuseStep 225575 = 338363) B338363
theorem B1503623 : Blo 99781 1503623 := bstep (se 1 (by rfl) ⟨1127717, by rfl⟩ : syracuseStep 1503623 = 2255435) B2255435
theorem B193079 : Blo 99781 193079 := bstep (se 1 (by rfl) ⟨144809, by rfl⟩ : syracuseStep 193079 = 289619) B289619
theorem B652205 : Blo 99781 652205 := bstep (se 3 (by rfl) ⟨122288, by rfl⟩ : syracuseStep 652205 = 244577) B244577
theorem B553979 : Blo 99781 553979 := bstep (se 1 (by rfl) ⟨415484, by rfl⟩ : syracuseStep 553979 = 830969) B830969
theorem B324719 : Blo 99781 324719 := bstep (se 1 (by rfl) ⟨243539, by rfl⟩ : syracuseStep 324719 = 487079) B487079
theorem B653129 : Blo 99781 653129 := bstep (se 2 (by rfl) ⟨244923, by rfl⟩ : syracuseStep 653129 = 489847) B489847
theorem B784403 : Blo 99781 784403 := bstep (se 1 (by rfl) ⟨588302, by rfl⟩ : syracuseStep 784403 = 1176605) B1176605
theorem B260435 : Blo 99781 260435 := bstep (se 1 (by rfl) ⟨195326, by rfl⟩ : syracuseStep 260435 = 390653) B390653
theorem B260891 : Blo 99781 260891 := bstep (se 1 (by rfl) ⟨195668, by rfl⟩ : syracuseStep 260891 = 391337) B391337
theorem B195691 : Blo 99781 195691 := bstep (se 1 (by rfl) ⟨146768, by rfl⟩ : syracuseStep 195691 = 293537) B293537
theorem B163129 : Blo 99781 163129 := bstep (se 2 (by rfl) ⟨61173, by rfl⟩ : syracuseStep 163129 = 122347) B122347
theorem B130663 : Blo 99781 130663 := bstep (se 1 (by rfl) ⟨97997, by rfl⟩ : syracuseStep 130663 = 195995) B195995
theorem B294607 : Blo 99781 294607 := bstep (se 1 (by rfl) ⟨220955, by rfl⟩ : syracuseStep 294607 = 441911) B441911
theorem B196435 : Blo 99781 196435 := bstep (se 1 (by rfl) ⟨147326, by rfl⟩ : syracuseStep 196435 = 294653) B294653
theorem B40468403 : Blo 99781 40468403 := bstep (se 1 (by rfl) ⟨30351302, by rfl⟩ : syracuseStep 40468403 = 60702605) B60702605
theorem B196663 : Blo 99781 196663 := bstep (se 1 (by rfl) ⟨147497, by rfl⟩ : syracuseStep 196663 = 294995) B294995
theorem B491615 : Blo 99781 491615 := bstep (se 1 (by rfl) ⟨368711, by rfl⟩ : syracuseStep 491615 = 737423) B737423
theorem B99839 : Blo 99781 99839 := bstep (se 1 (by rfl) ⟨74879, by rfl⟩ : syracuseStep 99839 = 149759) B149759
theorem B99931 : Blo 99781 99931 := bstep (se 1 (by rfl) ⟨74948, by rfl⟩ : syracuseStep 99931 = 149897) B149897
theorem B99995 : Blo 99781 99995 := bstep (se 1 (by rfl) ⟨74996, by rfl⟩ : syracuseStep 99995 = 149993) B149993
theorem B100263 : Blo 99781 100263 := bstep (se 1 (by rfl) ⟨75197, by rfl⟩ : syracuseStep 100263 = 150395) B150395
theorem B231335 : Blo 99781 231335 := bstep (se 1 (by rfl) ⟨173501, by rfl⟩ : syracuseStep 231335 = 347003) B347003
theorem B166025 : Blo 99781 166025 := bstep (se 2 (by rfl) ⟨62259, by rfl⟩ : syracuseStep 166025 = 124519) B124519
theorem B100839 : Blo 99781 100839 := bstep (se 1 (by rfl) ⟨75629, by rfl⟩ : syracuseStep 100839 = 151259) B151259
theorem B100975 : Blo 99781 100975 := bstep (se 1 (by rfl) ⟨75731, by rfl⟩ : syracuseStep 100975 = 151463) B151463
theorem B4197095 : Blo 99781 4197095 := bstep (se 1 (by rfl) ⟨3147821, by rfl⟩ : syracuseStep 4197095 = 6295643) B6295643
theorem B101183 : Blo 99781 101183 := bstep (se 1 (by rfl) ⟨75887, by rfl⟩ : syracuseStep 101183 = 151775) B151775
theorem B101231 : Blo 99781 101231 := bstep (se 1 (by rfl) ⟨75923, by rfl⟩ : syracuseStep 101231 = 151847) B151847
theorem B101487 : Blo 99781 101487 := bstep (se 1 (by rfl) ⟨76115, by rfl⟩ : syracuseStep 101487 = 152231) B152231
theorem B101503 : Blo 99781 101503 := bstep (se 1 (by rfl) ⟨76127, by rfl⟩ : syracuseStep 101503 = 152255) B152255
theorem B101543 : Blo 99781 101543 := bstep (se 1 (by rfl) ⟨76157, by rfl⟩ : syracuseStep 101543 = 152315) B152315
theorem B101615 : Blo 99781 101615 := bstep (se 1 (by rfl) ⟨76211, by rfl⟩ : syracuseStep 101615 = 152423) B152423
theorem B101871 : Blo 99781 101871 := bstep (se 1 (by rfl) ⟨76403, by rfl⟩ : syracuseStep 101871 = 152807) B152807
theorem B101999 : Blo 99781 101999 := bstep (se 1 (by rfl) ⟨76499, by rfl⟩ : syracuseStep 101999 = 152999) B152999
theorem B102119 : Blo 99781 102119 := bstep (se 1 (by rfl) ⟨76589, by rfl⟩ : syracuseStep 102119 = 153179) B153179
theorem B430019 : Blo 99781 430019 := bstep (se 1 (by rfl) ⟨322514, by rfl⟩ : syracuseStep 430019 = 645029) B645029
theorem B233441 : Blo 99781 233441 := bstep (se 2 (by rfl) ⟨87540, by rfl⟩ : syracuseStep 233441 = 175081) B175081
theorem B102607 : Blo 99781 102607 := bstep (se 1 (by rfl) ⟨76955, by rfl⟩ : syracuseStep 102607 = 153911) B153911
theorem B102639 : Blo 99781 102639 := bstep (se 1 (by rfl) ⟨76979, by rfl⟩ : syracuseStep 102639 = 153959) B153959
theorem B102727 : Blo 99781 102727 := bstep (se 1 (by rfl) ⟨77045, by rfl⟩ : syracuseStep 102727 = 154091) B154091
theorem B168439 : Blo 99781 168439 := bstep (se 1 (by rfl) ⟨126329, by rfl⟩ : syracuseStep 168439 = 252659) B252659
theorem B103071 : Blo 99781 103071 := bstep (se 1 (by rfl) ⟨77303, by rfl⟩ : syracuseStep 103071 = 154607) B154607
theorem B332527 : Blo 99781 332527 := bstep (se 1 (by rfl) ⟨249395, by rfl⟩ : syracuseStep 332527 = 498791) B498791
theorem B103199 : Blo 99781 103199 := bstep (se 1 (by rfl) ⟨77399, by rfl⟩ : syracuseStep 103199 = 154799) B154799
theorem B103515 : Blo 99781 103515 := bstep (se 1 (by rfl) ⟨77636, by rfl⟩ : syracuseStep 103515 = 155273) B155273
theorem B103527 : Blo 99781 103527 := bstep (se 1 (by rfl) ⟨77645, by rfl⟩ : syracuseStep 103527 = 155291) B155291
theorem B103551 : Blo 99781 103551 := bstep (se 1 (by rfl) ⟨77663, by rfl⟩ : syracuseStep 103551 = 155327) B155327
theorem B103663 : Blo 99781 103663 := bstep (se 1 (by rfl) ⟨77747, by rfl⟩ : syracuseStep 103663 = 155495) B155495
theorem B660919 : Blo 99781 660919 := bstep (se 1 (by rfl) ⟨495689, by rfl⟩ : syracuseStep 660919 = 991379) B991379
theorem B498113 : Blo 99781 498113 := bstep (se 2 (by rfl) ⟨186792, by rfl⟩ : syracuseStep 498113 = 373585) B373585
theorem B858671 : Blo 99781 858671 := bstep (se 1 (by rfl) ⟨644003, by rfl⟩ : syracuseStep 858671 = 1288007) B1288007
theorem B694943 : Blo 99781 694943 := bstep (se 1 (by rfl) ⟨521207, by rfl⟩ : syracuseStep 694943 = 1042415) B1042415
theorem B433147 : Blo 99781 433147 := bstep (se 1 (by rfl) ⟨324860, by rfl⟩ : syracuseStep 433147 = 649721) B649721
theorem B171551 : Blo 99781 171551 := bstep (se 1 (by rfl) ⟨128663, by rfl⟩ : syracuseStep 171551 = 257327) B257327
theorem B991531 : Blo 99781 991531 := bstep (se 1 (by rfl) ⟨743648, by rfl⟩ : syracuseStep 991531 = 1487297) B1487297
theorem B205211 : Blo 99781 205211 := bstep (se 1 (by rfl) ⟨153908, by rfl⟩ : syracuseStep 205211 = 307817) B307817
theorem B434803 : Blo 99781 434803 := bstep (se 1 (by rfl) ⟨326102, by rfl⟩ : syracuseStep 434803 = 652205) B652205
theorem B369319 : Blo 99781 369319 := bstep (se 1 (by rfl) ⟨276989, by rfl⟩ : syracuseStep 369319 = 553979) B553979
theorem B435419 : Blo 99781 435419 := bstep (se 1 (by rfl) ⟨326564, by rfl⟩ : syracuseStep 435419 = 653129) B653129
theorem B173623 : Blo 99781 173623 := bstep (se 1 (by rfl) ⟨130217, by rfl⟩ : syracuseStep 173623 = 260435) B260435
theorem B173927 : Blo 99781 173927 := bstep (se 1 (by rfl) ⟨130445, by rfl⟩ : syracuseStep 173927 = 260891) B260891
theorem B174217 : Blo 99781 174217 := bstep (se 2 (by rfl) ⟨65331, by rfl⟩ : syracuseStep 174217 = 130663) B130663
theorem B469423 : Blo 99781 469423 := bstep (se 1 (by rfl) ⟨352067, by rfl⟩ : syracuseStep 469423 = 704135) B704135
theorem B26978935 : Blo 99781 26978935 := bstep (se 1 (by rfl) ⟨20234201, by rfl⟩ : syracuseStep 26978935 = 40468403) B40468403
theorem B4009661 : Blo 99781 4009661 := bstep (se 3 (by rfl) ⟨751811, by rfl⟩ : syracuseStep 4009661 = 1503623) B1503623
theorem B1257245 : Blo 99781 1257245 := bstep (se 3 (by rfl) ⟨235733, by rfl⟩ : syracuseStep 1257245 = 471467) B471467
theorem B340415 : Blo 99781 340415 := bstep (se 1 (by rfl) ⟨255311, by rfl⟩ : syracuseStep 340415 = 510623) B510623
theorem B439451 : Blo 99781 439451 := bstep (se 1 (by rfl) ⟨329588, by rfl⟩ : syracuseStep 439451 = 659177) B659177
theorem B4110365 : Blo 99781 4110365 := bstep (se 3 (by rfl) ⟨770693, by rfl⟩ : syracuseStep 4110365 = 1541387) B1541387
theorem B112891 : Blo 99781 112891 := bstep (se 1 (by rfl) ⟨84668, by rfl⟩ : syracuseStep 112891 = 169337) B169337
theorem B735551 : Blo 99781 735551 := bstep (se 1 (by rfl) ⟨551663, by rfl⟩ : syracuseStep 735551 = 1103327) B1103327
theorem B112999 : Blo 99781 112999 := bstep (se 1 (by rfl) ⟨84749, by rfl⟩ : syracuseStep 112999 = 169499) B169499
theorem B506735 : Blo 99781 506735 := bstep (se 1 (by rfl) ⟨380051, by rfl⟩ : syracuseStep 506735 = 760103) B760103
theorem B113791 : Blo 99781 113791 := bstep (se 1 (by rfl) ⟨85343, by rfl⟩ : syracuseStep 113791 = 170687) B170687
theorem B507179 : Blo 99781 507179 := bstep (se 1 (by rfl) ⟨380384, by rfl⟩ : syracuseStep 507179 = 760769) B760769
theorem B507383 : Blo 99781 507383 := bstep (se 1 (by rfl) ⟨380537, by rfl⟩ : syracuseStep 507383 = 761075) B761075
theorem B278255 : Blo 99781 278255 := bstep (se 1 (by rfl) ⟨208691, by rfl⟩ : syracuseStep 278255 = 417383) B417383
theorem B343871 : Blo 99781 343871 := bstep (se 1 (by rfl) ⟨257903, by rfl⟩ : syracuseStep 343871 = 515807) B515807
theorem B1490987 : Blo 99781 1490987 := bstep (se 1 (by rfl) ⟨1118240, by rfl⟩ : syracuseStep 1490987 = 2236481) B2236481
theorem B508031 : Blo 99781 508031 := bstep (se 1 (by rfl) ⟨381023, by rfl⟩ : syracuseStep 508031 = 762047) B762047
theorem B508679 : Blo 99781 508679 := bstep (se 1 (by rfl) ⟨381509, by rfl⟩ : syracuseStep 508679 = 763019) B763019
theorem B247951 : Blo 99781 247951 := bstep (se 1 (by rfl) ⟨185963, by rfl⟩ : syracuseStep 247951 = 371927) B371927
theorem B149831 : Blo 99781 149831 := bstep (se 1 (by rfl) ⟨112373, by rfl⟩ : syracuseStep 149831 = 224747) B224747
theorem B149915 : Blo 99781 149915 := bstep (se 1 (by rfl) ⟨112436, by rfl⟩ : syracuseStep 149915 = 224873) B224873
theorem B412075 : Blo 99781 412075 := bstep (se 1 (by rfl) ⟨309056, by rfl⟩ : syracuseStep 412075 = 618113) B618113
theorem B510461 : Blo 99781 510461 := bstep (se 3 (by rfl) ⟨95711, by rfl⟩ : syracuseStep 510461 = 191423) B191423
theorem B248633 : Blo 99781 248633 := bstep (se 2 (by rfl) ⟨93237, by rfl⟩ : syracuseStep 248633 = 186475) B186475
theorem B150383 : Blo 99781 150383 := bstep (se 1 (by rfl) ⟨112787, by rfl⟩ : syracuseStep 150383 = 225575) B225575
theorem B216479 : Blo 99781 216479 := bstep (se 1 (by rfl) ⟨162359, by rfl⟩ : syracuseStep 216479 = 324719) B324719
theorem B217505 : Blo 99781 217505 := bstep (se 2 (by rfl) ⟨81564, by rfl⟩ : syracuseStep 217505 = 163129) B163129
theorem B153215 : Blo 99781 153215 := bstep (se 1 (by rfl) ⟨114911, by rfl⟩ : syracuseStep 153215 = 229823) B229823
theorem B349919 : Blo 99781 349919 := bstep (se 1 (by rfl) ⟨262439, by rfl⟩ : syracuseStep 349919 = 524879) B524879
theorem B481609 : Blo 99781 481609 := bstep (se 2 (by rfl) ⟨180603, by rfl⟩ : syracuseStep 481609 = 361207) B361207
theorem B1956511 : Blo 99781 1956511 := bstep (se 1 (by rfl) ⟨1467383, by rfl⟩ : syracuseStep 1956511 = 2934767) B2934767
theorem B252679 : Blo 99781 252679 := bstep (se 1 (by rfl) ⟨189509, by rfl⟩ : syracuseStep 252679 = 379019) B379019
theorem B1957229 : Blo 99781 1957229 := bstep (se 3 (by rfl) ⟨366980, by rfl⟩ : syracuseStep 1957229 = 733961) B733961
theorem B155591 : Blo 99781 155591 := bstep (se 1 (by rfl) ⟨116693, by rfl⟩ : syracuseStep 155591 = 233387) B233387
theorem B286703 : Blo 99781 286703 := bstep (se 1 (by rfl) ⟨215027, by rfl⟩ : syracuseStep 286703 = 430055) B430055
theorem B975311 : Blo 99781 975311 := bstep (se 1 (by rfl) ⟨731483, by rfl⟩ : syracuseStep 975311 = 1462967) B1462967
theorem B484217 : Blo 99781 484217 := bstep (se 2 (by rfl) ⟨181581, by rfl⟩ : syracuseStep 484217 = 363163) B363163
theorem B1106855 : Blo 99781 1106855 := bstep (se 1 (by rfl) ⟨830141, by rfl⟩ : syracuseStep 1106855 = 1660283) B1660283
theorem B976151 : Blo 99781 976151 := bstep (se 1 (by rfl) ⟨732113, by rfl⟩ : syracuseStep 976151 = 1464227) B1464227
theorem B321823 : Blo 99781 321823 := bstep (se 1 (by rfl) ⟨241367, by rfl⟩ : syracuseStep 321823 = 482735) B482735
theorem B584111 : Blo 99781 584111 := bstep (se 1 (by rfl) ⟨438083, by rfl⟩ : syracuseStep 584111 = 876167) B876167
theorem B977771 : Blo 99781 977771 := bstep (se 1 (by rfl) ⟨733328, by rfl⟩ : syracuseStep 977771 = 1466657) B1466657
theorem B486847 : Blo 99781 486847 := bstep (se 1 (by rfl) ⟨365135, by rfl⟩ : syracuseStep 486847 = 730271) B730271
theorem B585185 : Blo 99781 585185 := bstep (se 2 (by rfl) ⟨219444, by rfl⟩ : syracuseStep 585185 = 438889) B438889
theorem B1240895 : Blo 99781 1240895 := bstep (se 1 (by rfl) ⟨930671, by rfl⟩ : syracuseStep 1240895 = 1861343) B1861343
theorem B225107 : Blo 99781 225107 := bstep (se 1 (by rfl) ⟨168830, by rfl⟩ : syracuseStep 225107 = 337661) B337661
theorem B226331 : Blo 99781 226331 := bstep (se 1 (by rfl) ⟨169748, by rfl⟩ : syracuseStep 226331 = 339497) B339497
theorem B292319 : Blo 99781 292319 := bstep (se 1 (by rfl) ⟨219239, by rfl⟩ : syracuseStep 292319 = 438479) B438479
theorem B128719 : Blo 99781 128719 := bstep (se 1 (by rfl) ⟨96539, by rfl⟩ : syracuseStep 128719 = 193079) B193079
theorem B227807 : Blo 99781 227807 := bstep (se 1 (by rfl) ⟨170855, by rfl⟩ : syracuseStep 227807 = 341711) B341711
theorem B4422113 : Blo 99781 4422113 := bstep (se 2 (by rfl) ⟨1658292, by rfl⟩ : syracuseStep 4422113 = 3316585) B3316585
theorem B522935 : Blo 99781 522935 := bstep (se 1 (by rfl) ⟨392201, by rfl⟩ : syracuseStep 522935 = 784403) B784403
theorem B260921 : Blo 99781 260921 := bstep (se 2 (by rfl) ⟨97845, by rfl⟩ : syracuseStep 260921 = 195691) B195691
theorem B228455 : Blo 99781 228455 := bstep (se 1 (by rfl) ⟨171341, by rfl⟩ : syracuseStep 228455 = 342683) B342683
theorem B228563 : Blo 99781 228563 := bstep (se 1 (by rfl) ⟨171422, by rfl⟩ : syracuseStep 228563 = 342845) B342845
theorem B392809 : Blo 99781 392809 := bstep (se 2 (by rfl) ⟨147303, by rfl⟩ : syracuseStep 392809 = 294607) B294607
theorem B261913 : Blo 99781 261913 := bstep (se 2 (by rfl) ⟨98217, by rfl⟩ : syracuseStep 261913 = 196435) B196435
theorem B327743 : Blo 99781 327743 := bstep (se 1 (by rfl) ⟨245807, by rfl⟩ : syracuseStep 327743 = 491615) B491615
theorem B262217 : Blo 99781 262217 := bstep (se 2 (by rfl) ⟨98331, by rfl⟩ : syracuseStep 262217 = 196663) B196663
theorem B492425 : Blo 99781 492425 := bstep (se 2 (by rfl) ⟨184659, by rfl⟩ : syracuseStep 492425 = 369319) B369319
theorem B99887 : Blo 99781 99887 := bstep (se 1 (by rfl) ⟨74915, by rfl⟩ : syracuseStep 99887 = 149831) B149831
theorem B99943 : Blo 99781 99943 := bstep (se 1 (by rfl) ⟨74957, by rfl⟩ : syracuseStep 99943 = 149915) B149915
theorem B165755 : Blo 99781 165755 := bstep (se 1 (by rfl) ⟨124316, by rfl⟩ : syracuseStep 165755 = 248633) B248633
theorem B100255 : Blo 99781 100255 := bstep (se 1 (by rfl) ⟨75191, by rfl⟩ : syracuseStep 100255 = 150383) B150383
theorem B231497 : Blo 99781 231497 := bstep (se 2 (by rfl) ⟨86811, by rfl⟩ : syracuseStep 231497 = 173623) B173623
theorem B232289 : Blo 99781 232289 := bstep (se 2 (by rfl) ⟨87108, by rfl⟩ : syracuseStep 232289 = 174217) B174217
theorem B429097 : Blo 99781 429097 := bstep (se 2 (by rfl) ⟨160911, by rfl⟩ : syracuseStep 429097 = 321823) B321823
theorem B625897 : Blo 99781 625897 := bstep (se 2 (by rfl) ⟨234711, by rfl⟩ : syracuseStep 625897 = 469423) B469423
theorem B102143 : Blo 99781 102143 := bstep (se 1 (by rfl) ⟨76607, by rfl⟩ : syracuseStep 102143 = 153215) B153215
theorem B233279 : Blo 99781 233279 := bstep (se 1 (by rfl) ⟨174959, by rfl⟩ : syracuseStep 233279 = 349919) B349919
theorem B332075 : Blo 99781 332075 := bstep (se 1 (by rfl) ⟨249056, by rfl⟩ : syracuseStep 332075 = 498113) B498113
theorem B463295 : Blo 99781 463295 := bstep (se 1 (by rfl) ⟨347471, by rfl⟩ : syracuseStep 463295 = 694943) B694943
theorem B103727 : Blo 99781 103727 := bstep (se 1 (by rfl) ⟨77795, by rfl⟩ : syracuseStep 103727 = 155591) B155591
theorem B171625 : Blo 99781 171625 := bstep (se 2 (by rfl) ⟨64359, by rfl⟩ : syracuseStep 171625 = 128719) B128719
theorem B827263 : Blo 99781 827263 := bstep (se 1 (by rfl) ⟨620447, by rfl⟩ : syracuseStep 827263 = 1240895) B1240895
theorem B1352477 : Blo 99781 1352477 := bstep (se 3 (by rfl) ⟨253589, by rfl⟩ : syracuseStep 1352477 = 507179) B507179
theorem B336905 : Blo 99781 336905 := bstep (se 2 (by rfl) ⟨126339, by rfl⟩ : syracuseStep 336905 = 252679) B252679
theorem B173947 : Blo 99781 173947 := bstep (se 1 (by rfl) ⟨130460, by rfl⟩ : syracuseStep 173947 = 260921) B260921
theorem B337823 : Blo 99781 337823 := bstep (se 1 (by rfl) ⟨253367, by rfl⟩ : syracuseStep 337823 = 506735) B506735
theorem B338255 : Blo 99781 338255 := bstep (se 1 (by rfl) ⟨253691, by rfl⟩ : syracuseStep 338255 = 507383) B507383
theorem B338687 : Blo 99781 338687 := bstep (se 1 (by rfl) ⟨254015, by rfl⟩ : syracuseStep 338687 = 508031) B508031
theorem B3975965 : Blo 99781 3975965 := bstep (se 3 (by rfl) ⟨745493, by rfl⟩ : syracuseStep 3975965 = 1490987) B1490987
theorem B1322041 : Blo 99781 1322041 := bstep (se 2 (by rfl) ⟨495765, by rfl⟩ : syracuseStep 1322041 = 991531) B991531
theorem B339119 : Blo 99781 339119 := bstep (se 1 (by rfl) ⟨254339, by rfl⟩ : syracuseStep 339119 = 508679) B508679
theorem B1322405 : Blo 99781 1322405 := bstep (se 4 (by rfl) ⟨123975, by rfl⟩ : syracuseStep 1322405 = 247951) B247951
theorem B110683 : Blo 99781 110683 := bstep (se 1 (by rfl) ⟨83012, by rfl⟩ : syracuseStep 110683 = 166025) B166025
theorem B340307 : Blo 99781 340307 := bstep (se 1 (by rfl) ⟨255230, by rfl⟩ : syracuseStep 340307 = 510461) B510461
theorem B2568581 : Blo 99781 2568581 := bstep (se 4 (by rfl) ⟨240804, by rfl⟩ : syracuseStep 2568581 = 481609) B481609
theorem B2798063 : Blo 99781 2798063 := bstep (se 1 (by rfl) ⟨2098547, by rfl⟩ : syracuseStep 2798063 = 4197095) B4197095
theorem B145003 : Blo 99781 145003 := bstep (se 1 (by rfl) ⟨108752, by rfl⟩ : syracuseStep 145003 = 217505) B217505
theorem B572447 : Blo 99781 572447 := bstep (se 1 (by rfl) ⟨429335, by rfl⟩ : syracuseStep 572447 = 858671) B858671
theorem B114367 : Blo 99781 114367 := bstep (se 1 (by rfl) ⟨85775, by rfl⟩ : syracuseStep 114367 = 171551) B171551
theorem B737903 : Blo 99781 737903 := bstep (se 1 (by rfl) ⟨553427, by rfl⟩ : syracuseStep 737903 = 1106855) B1106855
theorem B443369 : Blo 99781 443369 := bstep (se 2 (by rfl) ⟨166263, by rfl⟩ : syracuseStep 443369 = 332527) B332527
theorem B115951 : Blo 99781 115951 := bstep (se 1 (by rfl) ⟨86963, by rfl⟩ : syracuseStep 115951 = 173927) B173927
theorem B2673107 : Blo 99781 2673107 := bstep (se 1 (by rfl) ⟨2004830, by rfl⟩ : syracuseStep 2673107 = 4009661) B4009661
theorem B838163 : Blo 99781 838163 := bstep (se 1 (by rfl) ⟨628622, by rfl⟩ : syracuseStep 838163 = 1257245) B1257245
theorem B150071 : Blo 99781 150071 := bstep (se 1 (by rfl) ⟨112553, by rfl⟩ : syracuseStep 150071 = 225107) B225107
theorem B150521 : Blo 99781 150521 := bstep (se 2 (by rfl) ⟨56445, by rfl⟩ : syracuseStep 150521 = 112891) B112891
theorem B150665 : Blo 99781 150665 := bstep (se 2 (by rfl) ⟨56499, by rfl⟩ : syracuseStep 150665 = 112999) B112999
theorem B150887 : Blo 99781 150887 := bstep (se 1 (by rfl) ⟨113165, by rfl⟩ : syracuseStep 150887 = 226331) B226331
theorem B2608681 : Blo 99781 2608681 := bstep (se 2 (by rfl) ⟨978255, by rfl⟩ : syracuseStep 2608681 = 1956511) B1956511
theorem B577277 : Blo 99781 577277 := bstep (se 3 (by rfl) ⟨108239, by rfl⟩ : syracuseStep 577277 = 216479) B216479
theorem B1560493 : Blo 99781 1560493 := bstep (se 3 (by rfl) ⟨292592, by rfl⟩ : syracuseStep 1560493 = 585185) B585185
theorem B577529 : Blo 99781 577529 := bstep (se 2 (by rfl) ⟨216573, by rfl⟩ : syracuseStep 577529 = 433147) B433147
theorem B2740243 : Blo 99781 2740243 := bstep (se 1 (by rfl) ⟨2055182, by rfl⟩ : syracuseStep 2740243 = 4110365) B4110365
theorem B151721 : Blo 99781 151721 := bstep (se 2 (by rfl) ⟨56895, by rfl⟩ : syracuseStep 151721 = 113791) B113791
theorem B151871 : Blo 99781 151871 := bstep (se 1 (by rfl) ⟨113903, by rfl⟩ : syracuseStep 151871 = 227807) B227807
theorem B348623 : Blo 99781 348623 := bstep (se 1 (by rfl) ⟨261467, by rfl⟩ : syracuseStep 348623 = 522935) B522935
theorem B152303 : Blo 99781 152303 := bstep (se 1 (by rfl) ⟨114227, by rfl⟩ : syracuseStep 152303 = 228455) B228455
theorem B152375 : Blo 99781 152375 := bstep (se 1 (by rfl) ⟨114281, by rfl⟩ : syracuseStep 152375 = 228563) B228563
theorem B349217 : Blo 99781 349217 := bstep (se 2 (by rfl) ⟨130956, by rfl⟩ : syracuseStep 349217 = 261913) B261913
theorem B185503 : Blo 99781 185503 := bstep (se 1 (by rfl) ⟨139127, by rfl⟩ : syracuseStep 185503 = 278255) B278255
theorem B579737 : Blo 99781 579737 := bstep (se 2 (by rfl) ⟨217401, by rfl⟩ : syracuseStep 579737 = 434803) B434803
theorem B547229 : Blo 99781 547229 := bstep (se 3 (by rfl) ⟨102605, by rfl⟩ : syracuseStep 547229 = 205211) B205211
theorem B154223 : Blo 99781 154223 := bstep (se 1 (by rfl) ⟨115667, by rfl⟩ : syracuseStep 154223 = 231335) B231335
theorem B286679 : Blo 99781 286679 := bstep (se 1 (by rfl) ⟨215009, by rfl⟩ : syracuseStep 286679 = 430019) B430019
theorem B155627 : Blo 99781 155627 := bstep (se 1 (by rfl) ⟨116720, by rfl⟩ : syracuseStep 155627 = 233441) B233441
theorem B549433 : Blo 99781 549433 := bstep (se 2 (by rfl) ⟨206037, by rfl⟩ : syracuseStep 549433 = 412075) B412075
theorem B35971913 : Blo 99781 35971913 := bstep (se 2 (by rfl) ⟨13489467, by rfl⟩ : syracuseStep 35971913 = 26978935) B26978935
theorem B649129 : Blo 99781 649129 := bstep (se 2 (by rfl) ⟨243423, by rfl⟩ : syracuseStep 649129 = 486847) B486847
theorem B1304819 : Blo 99781 1304819 := bstep (se 1 (by rfl) ⟨978614, by rfl⟩ : syracuseStep 1304819 = 1957229) B1957229
theorem B191135 : Blo 99781 191135 := bstep (se 1 (by rfl) ⟨143351, by rfl⟩ : syracuseStep 191135 = 286703) B286703
theorem B650207 : Blo 99781 650207 := bstep (se 1 (by rfl) ⟨487655, by rfl⟩ : syracuseStep 650207 = 975311) B975311
theorem B322811 : Blo 99781 322811 := bstep (se 1 (by rfl) ⟨242108, by rfl⟩ : syracuseStep 322811 = 484217) B484217
theorem B224585 : Blo 99781 224585 := bstep (se 2 (by rfl) ⟨84219, by rfl⟩ : syracuseStep 224585 = 168439) B168439
theorem B290279 : Blo 99781 290279 := bstep (se 1 (by rfl) ⟨217709, by rfl⟩ : syracuseStep 290279 = 435419) B435419
theorem B650767 : Blo 99781 650767 := bstep (se 1 (by rfl) ⟨488075, by rfl⟩ : syracuseStep 650767 = 976151) B976151
theorem B389407 : Blo 99781 389407 := bstep (se 1 (by rfl) ⟨292055, by rfl⟩ : syracuseStep 389407 = 584111) B584111
theorem B651847 : Blo 99781 651847 := bstep (se 1 (by rfl) ⟨488885, by rfl⟩ : syracuseStep 651847 = 977771) B977771
theorem B881225 : Blo 99781 881225 := bstep (se 2 (by rfl) ⟨330459, by rfl⟩ : syracuseStep 881225 = 660919) B660919
theorem B226943 : Blo 99781 226943 := bstep (se 1 (by rfl) ⟨170207, by rfl⟩ : syracuseStep 226943 = 340415) B340415
theorem B292967 : Blo 99781 292967 := bstep (se 1 (by rfl) ⟨219725, by rfl⟩ : syracuseStep 292967 = 439451) B439451
theorem B194879 : Blo 99781 194879 := bstep (se 1 (by rfl) ⟨146159, by rfl⟩ : syracuseStep 194879 = 292319) B292319
theorem B490367 : Blo 99781 490367 := bstep (se 1 (by rfl) ⟨367775, by rfl⟩ : syracuseStep 490367 = 735551) B735551
theorem B2948075 : Blo 99781 2948075 := bstep (se 1 (by rfl) ⟨2211056, by rfl⟩ : syracuseStep 2948075 = 4422113) B4422113
theorem B523745 : Blo 99781 523745 := bstep (se 2 (by rfl) ⟨196404, by rfl⟩ : syracuseStep 523745 = 392809) B392809
theorem B229247 : Blo 99781 229247 := bstep (se 1 (by rfl) ⟨171935, by rfl⟩ : syracuseStep 229247 = 343871) B343871
theorem B491935 : Blo 99781 491935 := bstep (se 1 (by rfl) ⟨368951, by rfl⟩ : syracuseStep 491935 = 737903) B737903
theorem B328283 : Blo 99781 328283 := bstep (se 1 (by rfl) ⟨246212, by rfl⟩ : syracuseStep 328283 = 492425) B492425
theorem B295579 : Blo 99781 295579 := bstep (se 1 (by rfl) ⟨221684, by rfl⟩ : syracuseStep 295579 = 443369) B443369
theorem B558775 : Blo 99781 558775 := bstep (se 1 (by rfl) ⟨419081, by rfl⟩ : syracuseStep 558775 = 838163) B838163
theorem B100047 : Blo 99781 100047 := bstep (se 1 (by rfl) ⟨75035, by rfl⟩ : syracuseStep 100047 = 150071) B150071
theorem B100347 : Blo 99781 100347 := bstep (se 1 (by rfl) ⟨75260, by rfl⟩ : syracuseStep 100347 = 150521) B150521
theorem B3606605 : Blo 99781 3606605 := bstep (se 3 (by rfl) ⟨676238, by rfl⟩ : syracuseStep 3606605 = 1352477) B1352477
theorem B100443 : Blo 99781 100443 := bstep (se 1 (by rfl) ⟨75332, by rfl⟩ : syracuseStep 100443 = 150665) B150665
theorem B100591 : Blo 99781 100591 := bstep (se 1 (by rfl) ⟨75443, by rfl⟩ : syracuseStep 100591 = 150887) B150887
theorem B231929 : Blo 99781 231929 := bstep (se 2 (by rfl) ⟨86973, by rfl⟩ : syracuseStep 231929 = 173947) B173947
theorem B101147 : Blo 99781 101147 := bstep (se 1 (by rfl) ⟨75860, by rfl⟩ : syracuseStep 101147 = 151721) B151721
theorem B101247 : Blo 99781 101247 := bstep (se 1 (by rfl) ⟨75935, by rfl⟩ : syracuseStep 101247 = 151871) B151871
theorem B232415 : Blo 99781 232415 := bstep (se 1 (by rfl) ⟨174311, by rfl⟩ : syracuseStep 232415 = 348623) B348623
theorem B101535 : Blo 99781 101535 := bstep (se 1 (by rfl) ⟨76151, by rfl⟩ : syracuseStep 101535 = 152303) B152303
theorem B101583 : Blo 99781 101583 := bstep (se 1 (by rfl) ⟨76187, by rfl⟩ : syracuseStep 101583 = 152375) B152375
theorem B232811 : Blo 99781 232811 := bstep (se 1 (by rfl) ⟨174608, by rfl⟩ : syracuseStep 232811 = 349217) B349217
theorem B364819 : Blo 99781 364819 := bstep (se 1 (by rfl) ⟨273614, by rfl⟩ : syracuseStep 364819 = 547229) B547229
theorem B102815 : Blo 99781 102815 := bstep (se 1 (by rfl) ⟨77111, by rfl⟩ : syracuseStep 102815 = 154223) B154223
theorem B3478241 : Blo 99781 3478241 := bstep (se 2 (by rfl) ⟨1304340, by rfl⟩ : syracuseStep 3478241 = 2608681) B2608681
theorem B103751 : Blo 99781 103751 := bstep (se 1 (by rfl) ⟨77813, by rfl⟩ : syracuseStep 103751 = 155627) B155627
theorem B433471 : Blo 99781 433471 := bstep (se 1 (by rfl) ⟨325103, by rfl⟩ : syracuseStep 433471 = 650207) B650207
theorem B1712387 : Blo 99781 1712387 := bstep (se 1 (by rfl) ⟨1284290, by rfl⟩ : syracuseStep 1712387 = 2568581) B2568581
theorem B764477 : Blo 99781 764477 := bstep (se 3 (by rfl) ⟨143339, by rfl⟩ : syracuseStep 764477 = 286679) B286679
theorem B174811 : Blo 99781 174811 := bstep (se 1 (by rfl) ⟨131108, by rfl⟩ : syracuseStep 174811 = 262217) B262217
theorem B732577 : Blo 99781 732577 := bstep (se 2 (by rfl) ⟨274716, by rfl⟩ : syracuseStep 732577 = 549433) B549433
theorem B1782071 : Blo 99781 1782071 := bstep (se 1 (by rfl) ⟨1336553, by rfl⟩ : syracuseStep 1782071 = 2673107) B2673107
theorem B865505 : Blo 99781 865505 := bstep (se 2 (by rfl) ⟨324564, by rfl⟩ : syracuseStep 865505 = 649129) B649129
theorem B308863 : Blo 99781 308863 := bstep (se 1 (by rfl) ⟨231647, by rfl⟩ : syracuseStep 308863 = 463295) B463295
theorem B572129 : Blo 99781 572129 := bstep (se 2 (by rfl) ⟨214548, by rfl⟩ : syracuseStep 572129 = 429097) B429097
theorem B834529 : Blo 99781 834529 := bstep (se 2 (by rfl) ⟨312948, by rfl⟩ : syracuseStep 834529 = 625897) B625897
theorem B867689 : Blo 99781 867689 := bstep (se 2 (by rfl) ⟨325383, by rfl⟩ : syracuseStep 867689 = 650767) B650767
theorem B442013 : Blo 99781 442013 := bstep (se 3 (by rfl) ⟨82877, by rfl⟩ : syracuseStep 442013 = 165755) B165755
theorem B2080657 : Blo 99781 2080657 := bstep (se 2 (by rfl) ⟨780246, by rfl⟩ : syracuseStep 2080657 = 1560493) B1560493
theorem B3653657 : Blo 99781 3653657 := bstep (se 2 (by rfl) ⟨1370121, by rfl⟩ : syracuseStep 3653657 = 2740243) B2740243
theorem B147577 : Blo 99781 147577 := bstep (se 2 (by rfl) ⟨55341, by rfl⟩ : syracuseStep 147577 = 110683) B110683
theorem B869129 : Blo 99781 869129 := bstep (se 2 (by rfl) ⟨325923, by rfl⟩ : syracuseStep 869129 = 651847) B651847
theorem B869879 : Blo 99781 869879 := bstep (se 1 (by rfl) ⟨652409, by rfl⟩ : syracuseStep 869879 = 1304819) B1304819
theorem B247337 : Blo 99781 247337 := bstep (se 2 (by rfl) ⟨92751, by rfl⟩ : syracuseStep 247337 = 185503) B185503
theorem B215207 : Blo 99781 215207 := bstep (se 1 (by rfl) ⟨161405, by rfl⟩ : syracuseStep 215207 = 322811) B322811
theorem B149723 : Blo 99781 149723 := bstep (se 1 (by rfl) ⟨112292, by rfl⟩ : syracuseStep 149723 = 224585) B224585
theorem B151295 : Blo 99781 151295 := bstep (se 1 (by rfl) ⟨113471, by rfl⟩ : syracuseStep 151295 = 226943) B226943
theorem B4412069 : Blo 99781 4412069 := bstep (se 4 (by rfl) ⟨413631, by rfl⟩ : syracuseStep 4412069 = 827263) B827263
theorem B381631 : Blo 99781 381631 := bstep (se 1 (by rfl) ⟨286223, by rfl⟩ : syracuseStep 381631 = 572447) B572447
theorem B152489 : Blo 99781 152489 := bstep (se 2 (by rfl) ⟨57183, by rfl⟩ : syracuseStep 152489 = 114367) B114367
theorem B349163 : Blo 99781 349163 := bstep (se 1 (by rfl) ⟨261872, by rfl⟩ : syracuseStep 349163 = 523745) B523745
theorem B152831 : Blo 99781 152831 := bstep (se 1 (by rfl) ⟨114623, by rfl⟩ : syracuseStep 152831 = 229247) B229247
theorem B218495 : Blo 99781 218495 := bstep (se 1 (by rfl) ⟨163871, by rfl⟩ : syracuseStep 218495 = 327743) B327743
theorem B154331 : Blo 99781 154331 := bstep (se 1 (by rfl) ⟨115748, by rfl⟩ : syracuseStep 154331 = 231497) B231497
theorem B154601 : Blo 99781 154601 := bstep (se 2 (by rfl) ⟨57975, by rfl⟩ : syracuseStep 154601 = 115951) B115951
theorem B154859 : Blo 99781 154859 := bstep (se 1 (by rfl) ⟨116144, by rfl⟩ : syracuseStep 154859 = 232289) B232289
theorem B384851 : Blo 99781 384851 := bstep (se 1 (by rfl) ⟨288638, by rfl⟩ : syracuseStep 384851 = 577277) B577277
theorem B155519 : Blo 99781 155519 := bstep (se 1 (by rfl) ⟨116639, by rfl⟩ : syracuseStep 155519 = 233279) B233279
theorem B385019 : Blo 99781 385019 := bstep (se 1 (by rfl) ⟨288764, by rfl⟩ : syracuseStep 385019 = 577529) B577529
theorem B221383 : Blo 99781 221383 := bstep (se 1 (by rfl) ⟨166037, by rfl⟩ : syracuseStep 221383 = 332075) B332075
theorem B1762721 : Blo 99781 1762721 := bstep (se 2 (by rfl) ⟨661020, by rfl⟩ : syracuseStep 1762721 = 1322041) B1322041
theorem B386491 : Blo 99781 386491 := bstep (se 1 (by rfl) ⟨289868, by rfl⟩ : syracuseStep 386491 = 579737) B579737
theorem B519209 : Blo 99781 519209 := bstep (se 2 (by rfl) ⟨194703, by rfl⟩ : syracuseStep 519209 = 389407) B389407
theorem B23981275 : Blo 99781 23981275 := bstep (se 1 (by rfl) ⟨17985956, by rfl⟩ : syracuseStep 23981275 = 35971913) B35971913
theorem B224603 : Blo 99781 224603 := bstep (se 1 (by rfl) ⟨168452, by rfl⟩ : syracuseStep 224603 = 336905) B336905
theorem B225215 : Blo 99781 225215 := bstep (se 1 (by rfl) ⟨168911, by rfl⟩ : syracuseStep 225215 = 337823) B337823
theorem B225503 : Blo 99781 225503 := bstep (se 1 (by rfl) ⟨169127, by rfl⟩ : syracuseStep 225503 = 338255) B338255
theorem B127423 : Blo 99781 127423 := bstep (se 1 (by rfl) ⟨95567, by rfl⟩ : syracuseStep 127423 = 191135) B191135
theorem B225791 : Blo 99781 225791 := bstep (se 1 (by rfl) ⟨169343, by rfl⟩ : syracuseStep 225791 = 338687) B338687
theorem B2650643 : Blo 99781 2650643 := bstep (se 1 (by rfl) ⟨1987982, by rfl⟩ : syracuseStep 2650643 = 3975965) B3975965
theorem B226079 : Blo 99781 226079 := bstep (se 1 (by rfl) ⟨169559, by rfl⟩ : syracuseStep 226079 = 339119) B339119
theorem B193337 : Blo 99781 193337 := bstep (se 2 (by rfl) ⟨72501, by rfl⟩ : syracuseStep 193337 = 145003) B145003
theorem B881603 : Blo 99781 881603 := bstep (se 1 (by rfl) ⟨661202, by rfl⟩ : syracuseStep 881603 = 1322405) B1322405
theorem B193519 : Blo 99781 193519 := bstep (se 1 (by rfl) ⟨145139, by rfl⟩ : syracuseStep 193519 = 290279) B290279
theorem B226871 : Blo 99781 226871 := bstep (se 1 (by rfl) ⟨170153, by rfl⟩ : syracuseStep 226871 = 340307) B340307
theorem B1865375 : Blo 99781 1865375 := bstep (se 1 (by rfl) ⟨1399031, by rfl⟩ : syracuseStep 1865375 = 2798063) B2798063
theorem B587483 : Blo 99781 587483 := bstep (se 1 (by rfl) ⟨440612, by rfl⟩ : syracuseStep 587483 = 881225) B881225
theorem B195311 : Blo 99781 195311 := bstep (se 1 (by rfl) ⟨146483, by rfl⟩ : syracuseStep 195311 = 292967) B292967
theorem B129919 : Blo 99781 129919 := bstep (se 1 (by rfl) ⟨97439, by rfl⟩ : syracuseStep 129919 = 194879) B194879
theorem B326911 : Blo 99781 326911 := bstep (se 1 (by rfl) ⟨245183, by rfl⟩ : syracuseStep 326911 = 490367) B490367
theorem B1965383 : Blo 99781 1965383 := bstep (se 1 (by rfl) ⟨1474037, by rfl⟩ : syracuseStep 1965383 = 2948075) B2948075
theorem B228833 : Blo 99781 228833 := bstep (se 2 (by rfl) ⟨85812, by rfl⟩ : syracuseStep 228833 = 171625) B171625
theorem B196769 : Blo 99781 196769 := bstep (se 2 (by rfl) ⟨73788, by rfl⟩ : syracuseStep 196769 = 147577) B147577
theorem B295177 : Blo 99781 295177 := bstep (se 2 (by rfl) ⟨110691, by rfl⟩ : syracuseStep 295177 = 221383) B221383
theorem B655913 : Blo 99781 655913 := bstep (se 2 (by rfl) ⟨245967, by rfl⟩ : syracuseStep 655913 = 491935) B491935
theorem B164891 : Blo 99781 164891 := bstep (se 1 (by rfl) ⟨123668, by rfl⟩ : syracuseStep 164891 = 247337) B247337
theorem B99815 : Blo 99781 99815 := bstep (se 1 (by rfl) ⟨74861, by rfl⟩ : syracuseStep 99815 = 149723) B149723
theorem B9275309 : Blo 99781 9275309 := bstep (se 3 (by rfl) ⟨1739120, by rfl⟩ : syracuseStep 9275309 = 3478241) B3478241
theorem B100863 : Blo 99781 100863 := bstep (se 1 (by rfl) ⟨75647, by rfl⟩ : syracuseStep 100863 = 151295) B151295
theorem B101659 : Blo 99781 101659 := bstep (se 1 (by rfl) ⟨76244, by rfl⟩ : syracuseStep 101659 = 152489) B152489
theorem B232775 : Blo 99781 232775 := bstep (se 1 (by rfl) ⟨174581, by rfl⟩ : syracuseStep 232775 = 349163) B349163
theorem B1576421 : Blo 99781 1576421 := bstep (se 4 (by rfl) ⟨147789, by rfl⟩ : syracuseStep 1576421 = 295579) B295579
theorem B101887 : Blo 99781 101887 := bstep (se 1 (by rfl) ⟨76415, by rfl⟩ : syracuseStep 101887 = 152831) B152831
theorem B233081 : Blo 99781 233081 := bstep (se 2 (by rfl) ⟨87405, by rfl⟩ : syracuseStep 233081 = 174811) B174811
theorem B102887 : Blo 99781 102887 := bstep (se 1 (by rfl) ⟨77165, by rfl⟩ : syracuseStep 102887 = 154331) B154331
theorem B103067 : Blo 99781 103067 := bstep (se 1 (by rfl) ⟨77300, by rfl⟩ : syracuseStep 103067 = 154601) B154601
theorem B103239 : Blo 99781 103239 := bstep (se 1 (by rfl) ⟨77429, by rfl⟩ : syracuseStep 103239 = 154859) B154859
theorem B103679 : Blo 99781 103679 := bstep (se 1 (by rfl) ⟨77759, by rfl⟩ : syracuseStep 103679 = 155519) B155519
theorem B169897 : Blo 99781 169897 := bstep (se 2 (by rfl) ⟨63711, by rfl⟩ : syracuseStep 169897 = 127423) B127423
theorem B1188047 : Blo 99781 1188047 := bstep (se 1 (by rfl) ⟨891035, by rfl⟩ : syracuseStep 1188047 = 1782071) B1782071
theorem B173225 : Blo 99781 173225 := bstep (se 2 (by rfl) ⟨64959, by rfl⟩ : syracuseStep 173225 = 129919) B129919
theorem B435881 : Blo 99781 435881 := bstep (se 2 (by rfl) ⟨163455, by rfl⟩ : syracuseStep 435881 = 326911) B326911
theorem B2435771 : Blo 99781 2435771 := bstep (se 1 (by rfl) ⟨1826828, by rfl⟩ : syracuseStep 2435771 = 3653657) B3653657
theorem B4566365 : Blo 99781 4566365 := bstep (se 3 (by rfl) ⟨856193, by rfl⟩ : syracuseStep 4566365 = 1712387) B1712387
theorem B2404403 : Blo 99781 2404403 := bstep (se 1 (by rfl) ⟨1803302, by rfl⟩ : syracuseStep 2404403 = 3606605) B3606605
theorem B143471 : Blo 99781 143471 := bstep (se 1 (by rfl) ⟨107603, by rfl⟩ : syracuseStep 143471 = 215207) B215207
theorem B508841 : Blo 99781 508841 := bstep (se 2 (by rfl) ⟨190815, by rfl⟩ : syracuseStep 508841 = 381631) B381631
theorem B509651 : Blo 99781 509651 := bstep (se 1 (by rfl) ⟨382238, by rfl⟩ : syracuseStep 509651 = 764477) B764477
theorem B346139 : Blo 99781 346139 := bstep (se 1 (by rfl) ⟨259604, by rfl⟩ : syracuseStep 346139 = 519209) B519209
theorem B411817 : Blo 99781 411817 := bstep (se 2 (by rfl) ⟨154431, by rfl⟩ : syracuseStep 411817 = 308863) B308863
theorem B149735 : Blo 99781 149735 := bstep (se 1 (by rfl) ⟨112301, by rfl⟩ : syracuseStep 149735 = 224603) B224603
theorem B150143 : Blo 99781 150143 := bstep (se 1 (by rfl) ⟨112607, by rfl⟩ : syracuseStep 150143 = 225215) B225215
theorem B150335 : Blo 99781 150335 := bstep (se 1 (by rfl) ⟨112751, by rfl⟩ : syracuseStep 150335 = 225503) B225503
theorem B150527 : Blo 99781 150527 := bstep (se 1 (by rfl) ⟨112895, by rfl⟩ : syracuseStep 150527 = 225791) B225791
theorem B150719 : Blo 99781 150719 := bstep (se 1 (by rfl) ⟨113039, by rfl⟩ : syracuseStep 150719 = 226079) B226079
theorem B577003 : Blo 99781 577003 := bstep (se 1 (by rfl) ⟨432752, by rfl⟩ : syracuseStep 577003 = 865505) B865505
theorem B151247 : Blo 99781 151247 := bstep (se 1 (by rfl) ⟨113435, by rfl⟩ : syracuseStep 151247 = 226871) B226871
theorem B577961 : Blo 99781 577961 := bstep (se 2 (by rfl) ⟨216735, by rfl⟩ : syracuseStep 577961 = 433471) B433471
theorem B381419 : Blo 99781 381419 := bstep (se 1 (by rfl) ⟨286064, by rfl⟩ : syracuseStep 381419 = 572129) B572129
theorem B11096837 : Blo 99781 11096837 := bstep (se 4 (by rfl) ⟨1040328, by rfl⟩ : syracuseStep 11096837 = 2080657) B2080657
theorem B578459 : Blo 99781 578459 := bstep (se 1 (by rfl) ⟨433844, by rfl⟩ : syracuseStep 578459 = 867689) B867689
theorem B152555 : Blo 99781 152555 := bstep (se 1 (by rfl) ⟨114416, by rfl⟩ : syracuseStep 152555 = 228833) B228833
theorem B218855 : Blo 99781 218855 := bstep (se 1 (by rfl) ⟨164141, by rfl⟩ : syracuseStep 218855 = 328283) B328283
theorem B579419 : Blo 99781 579419 := bstep (se 1 (by rfl) ⟨434564, by rfl⟩ : syracuseStep 579419 = 869129) B869129
theorem B579919 : Blo 99781 579919 := bstep (se 1 (by rfl) ⟨434939, by rfl⟩ : syracuseStep 579919 = 869879) B869879
theorem B154619 : Blo 99781 154619 := bstep (se 1 (by rfl) ⟨115964, by rfl⟩ : syracuseStep 154619 = 231929) B231929
theorem B515321 : Blo 99781 515321 := bstep (se 2 (by rfl) ⟨193245, by rfl⟩ : syracuseStep 515321 = 386491) B386491
theorem B154943 : Blo 99781 154943 := bstep (se 1 (by rfl) ⟨116207, by rfl⟩ : syracuseStep 154943 = 232415) B232415
theorem B155207 : Blo 99781 155207 := bstep (se 1 (by rfl) ⟨116405, by rfl⟩ : syracuseStep 155207 = 232811) B232811
theorem B745033 : Blo 99781 745033 := bstep (se 2 (by rfl) ⟨279387, by rfl⟩ : syracuseStep 745033 = 558775) B558775
theorem B2941379 : Blo 99781 2941379 := bstep (se 1 (by rfl) ⟨2206034, by rfl⟩ : syracuseStep 2941379 = 4412069) B4412069
theorem B582653 : Blo 99781 582653 := bstep (se 3 (by rfl) ⟨109247, by rfl⟩ : syracuseStep 582653 = 218495) B218495
theorem B31975033 : Blo 99781 31975033 := bstep (se 2 (by rfl) ⟨11990637, by rfl⟩ : syracuseStep 31975033 = 23981275) B23981275
theorem B976769 : Blo 99781 976769 := bstep (se 2 (by rfl) ⟨366288, by rfl⟩ : syracuseStep 976769 = 732577) B732577
theorem B256567 : Blo 99781 256567 := bstep (se 1 (by rfl) ⟨192425, by rfl⟩ : syracuseStep 256567 = 384851) B384851
theorem B256679 : Blo 99781 256679 := bstep (se 1 (by rfl) ⟨192509, by rfl⟩ : syracuseStep 256679 = 385019) B385019
theorem B486425 : Blo 99781 486425 := bstep (se 2 (by rfl) ⟨182409, by rfl⟩ : syracuseStep 486425 = 364819) B364819
theorem B1175147 : Blo 99781 1175147 := bstep (se 1 (by rfl) ⟨881360, by rfl⟩ : syracuseStep 1175147 = 1762721) B1762721
theorem B258025 : Blo 99781 258025 := bstep (se 2 (by rfl) ⟨96759, by rfl⟩ : syracuseStep 258025 = 193519) B193519
theorem B4714805 : Blo 99781 4714805 := bstep (se 5 (by rfl) ⟨221006, by rfl⟩ : syracuseStep 4714805 = 442013) B442013
theorem B520829 : Blo 99781 520829 := bstep (se 3 (by rfl) ⟨97655, by rfl⟩ : syracuseStep 520829 = 195311) B195311
theorem B1767095 : Blo 99781 1767095 := bstep (se 1 (by rfl) ⟨1325321, by rfl⟩ : syracuseStep 1767095 = 2650643) B2650643
theorem B128891 : Blo 99781 128891 := bstep (se 1 (by rfl) ⟨96668, by rfl⟩ : syracuseStep 128891 = 193337) B193337
theorem B587735 : Blo 99781 587735 := bstep (se 1 (by rfl) ⟨440801, by rfl⟩ : syracuseStep 587735 = 881603) B881603
theorem B1243583 : Blo 99781 1243583 := bstep (se 1 (by rfl) ⟨932687, by rfl⟩ : syracuseStep 1243583 = 1865375) B1865375
theorem B391655 : Blo 99781 391655 := bstep (se 1 (by rfl) ⟨293741, by rfl⟩ : syracuseStep 391655 = 587483) B587483
theorem B1112705 : Blo 99781 1112705 := bstep (se 2 (by rfl) ⟨417264, by rfl⟩ : syracuseStep 1112705 = 834529) B834529
theorem B1310255 : Blo 99781 1310255 := bstep (se 1 (by rfl) ⟨982691, by rfl⟩ : syracuseStep 1310255 = 1965383) B1965383
theorem B393569 : Blo 99781 393569 := bstep (se 2 (by rfl) ⟨147588, by rfl⟩ : syracuseStep 393569 = 295177) B295177
theorem B524717 : Blo 99781 524717 := bstep (se 3 (by rfl) ⟨98384, by rfl⟩ : syracuseStep 524717 = 196769) B196769
theorem B230759 : Blo 99781 230759 := bstep (se 1 (by rfl) ⟨173069, by rfl⟩ : syracuseStep 230759 = 346139) B346139
theorem B99823 : Blo 99781 99823 := bstep (se 1 (by rfl) ⟨74867, by rfl⟩ : syracuseStep 99823 = 149735) B149735
theorem B100095 : Blo 99781 100095 := bstep (se 1 (by rfl) ⟨75071, by rfl⟩ : syracuseStep 100095 = 150143) B150143
theorem B100223 : Blo 99781 100223 := bstep (se 1 (by rfl) ⟨75167, by rfl⟩ : syracuseStep 100223 = 150335) B150335
theorem B100351 : Blo 99781 100351 := bstep (se 1 (by rfl) ⟨75263, by rfl⟩ : syracuseStep 100351 = 150527) B150527
theorem B100479 : Blo 99781 100479 := bstep (se 1 (by rfl) ⟨75359, by rfl⟩ : syracuseStep 100479 = 150719) B150719
theorem B42633377 : Blo 99781 42633377 := bstep (se 2 (by rfl) ⟨15987516, by rfl⟩ : syracuseStep 42633377 = 31975033) B31975033
theorem B1050947 : Blo 99781 1050947 := bstep (se 1 (by rfl) ⟨788210, by rfl⟩ : syracuseStep 1050947 = 1576421) B1576421
theorem B1542557 : Blo 99781 1542557 := bstep (se 3 (by rfl) ⟨289229, by rfl⟩ : syracuseStep 1542557 = 578459) B578459
theorem B100831 : Blo 99781 100831 := bstep (se 1 (by rfl) ⟨75623, by rfl⟩ : syracuseStep 100831 = 151247) B151247
theorem B101703 : Blo 99781 101703 := bstep (se 1 (by rfl) ⟨76277, by rfl⟩ : syracuseStep 101703 = 152555) B152555
theorem B103079 : Blo 99781 103079 := bstep (se 1 (by rfl) ⟨77309, by rfl⟩ : syracuseStep 103079 = 154619) B154619
theorem B103295 : Blo 99781 103295 := bstep (se 1 (by rfl) ⟨77471, by rfl⟩ : syracuseStep 103295 = 154943) B154943
theorem B103471 : Blo 99781 103471 := bstep (se 1 (by rfl) ⟨77603, by rfl⟩ : syracuseStep 103471 = 155207) B155207
theorem B792031 : Blo 99781 792031 := bstep (se 1 (by rfl) ⟨594023, by rfl⟩ : syracuseStep 792031 = 1188047) B1188047
theorem B171119 : Blo 99781 171119 := bstep (se 1 (by rfl) ⟨128339, by rfl⟩ : syracuseStep 171119 = 256679) B256679
theorem B6495389 : Blo 99781 6495389 := bstep (se 3 (by rfl) ⟨1217885, by rfl⟩ : syracuseStep 6495389 = 2435771) B2435771
theorem B829055 : Blo 99781 829055 := bstep (se 1 (by rfl) ⟨621791, by rfl⟩ : syracuseStep 829055 = 1243583) B1243583
theorem B993377 : Blo 99781 993377 := bstep (se 2 (by rfl) ⟨372516, by rfl⟩ : syracuseStep 993377 = 745033) B745033
theorem B437275 : Blo 99781 437275 := bstep (se 1 (by rfl) ⟨327956, by rfl⟩ : syracuseStep 437275 = 655913) B655913
theorem B339227 : Blo 99781 339227 := bstep (se 1 (by rfl) ⟨254420, by rfl⟩ : syracuseStep 339227 = 508841) B508841
theorem B109927 : Blo 99781 109927 := bstep (se 1 (by rfl) ⟨82445, by rfl⟩ : syracuseStep 109927 = 164891) B164891
theorem B339767 : Blo 99781 339767 := bstep (se 1 (by rfl) ⟨254825, by rfl⟩ : syracuseStep 339767 = 509651) B509651
theorem B342089 : Blo 99781 342089 := bstep (se 2 (by rfl) ⟨128283, by rfl⟩ : syracuseStep 342089 = 256567) B256567
theorem B145903 : Blo 99781 145903 := bstep (se 1 (by rfl) ⟨109427, by rfl⟩ : syracuseStep 145903 = 218855) B218855
theorem B769337 : Blo 99781 769337 := bstep (se 2 (by rfl) ⟨288501, by rfl⟩ : syracuseStep 769337 = 577003) B577003
theorem B343547 : Blo 99781 343547 := bstep (se 1 (by rfl) ⟨257660, by rfl⟩ : syracuseStep 343547 = 515321) B515321
theorem B343709 : Blo 99781 343709 := bstep (se 3 (by rfl) ⟨64445, by rfl⟩ : syracuseStep 343709 = 128891) B128891
theorem B344033 : Blo 99781 344033 := bstep (se 2 (by rfl) ⟨129012, by rfl⟩ : syracuseStep 344033 = 258025) B258025
theorem B115483 : Blo 99781 115483 := bstep (se 1 (by rfl) ⟨86612, by rfl⟩ : syracuseStep 115483 = 173225) B173225
theorem B1297133 : Blo 99781 1297133 := bstep (se 3 (by rfl) ⟨243212, by rfl⟩ : syracuseStep 1297133 = 486425) B486425
theorem B347219 : Blo 99781 347219 := bstep (se 1 (by rfl) ⟨260414, by rfl⟩ : syracuseStep 347219 = 520829) B520829
theorem B773225 : Blo 99781 773225 := bstep (se 2 (by rfl) ⟨289959, by rfl⟩ : syracuseStep 773225 = 579919) B579919
theorem B741803 : Blo 99781 741803 := bstep (se 1 (by rfl) ⟨556352, by rfl⟩ : syracuseStep 741803 = 1112705) B1112705
theorem B873503 : Blo 99781 873503 := bstep (se 1 (by rfl) ⟨655127, by rfl⟩ : syracuseStep 873503 = 1310255) B1310255
theorem B382589 : Blo 99781 382589 := bstep (se 3 (by rfl) ⟨71735, by rfl⟩ : syracuseStep 382589 = 143471) B143471
theorem B12572813 : Blo 99781 12572813 := bstep (se 3 (by rfl) ⟨2357402, by rfl⟩ : syracuseStep 12572813 = 4714805) B4714805
theorem B6183539 : Blo 99781 6183539 := bstep (se 1 (by rfl) ⟨4637654, by rfl⟩ : syracuseStep 6183539 = 9275309) B9275309
theorem B155183 : Blo 99781 155183 := bstep (se 1 (by rfl) ⟨116387, by rfl⟩ : syracuseStep 155183 = 232775) B232775
theorem B155387 : Blo 99781 155387 := bstep (se 1 (by rfl) ⟨116540, by rfl⟩ : syracuseStep 155387 = 233081) B233081
theorem B549089 : Blo 99781 549089 := bstep (se 2 (by rfl) ⟨205908, by rfl⟩ : syracuseStep 549089 = 411817) B411817
theorem B385307 : Blo 99781 385307 := bstep (se 1 (by rfl) ⟨288980, by rfl⟩ : syracuseStep 385307 = 577961) B577961
theorem B254279 : Blo 99781 254279 := bstep (se 1 (by rfl) ⟨190709, by rfl⟩ : syracuseStep 254279 = 381419) B381419
theorem B7397891 : Blo 99781 7397891 := bstep (se 1 (by rfl) ⟨5548418, by rfl⟩ : syracuseStep 7397891 = 11096837) B11096837
theorem B386279 : Blo 99781 386279 := bstep (se 1 (by rfl) ⟨289709, by rfl⟩ : syracuseStep 386279 = 579419) B579419
theorem B1960919 : Blo 99781 1960919 := bstep (se 1 (by rfl) ⟨1470689, by rfl⟩ : syracuseStep 1960919 = 2941379) B2941379
theorem B388435 : Blo 99781 388435 := bstep (se 1 (by rfl) ⟨291326, by rfl⟩ : syracuseStep 388435 = 582653) B582653
theorem B290587 : Blo 99781 290587 := bstep (se 1 (by rfl) ⟨217940, by rfl⟩ : syracuseStep 290587 = 435881) B435881
theorem B651179 : Blo 99781 651179 := bstep (se 1 (by rfl) ⟨488384, by rfl⟩ : syracuseStep 651179 = 976769) B976769
theorem B3044243 : Blo 99781 3044243 := bstep (se 1 (by rfl) ⟨2283182, by rfl⟩ : syracuseStep 3044243 = 4566365) B4566365
theorem B783431 : Blo 99781 783431 := bstep (se 1 (by rfl) ⟨587573, by rfl⟩ : syracuseStep 783431 = 1175147) B1175147
theorem B226529 : Blo 99781 226529 := bstep (se 2 (by rfl) ⟨84948, by rfl⟩ : syracuseStep 226529 = 169897) B169897
theorem B1602935 : Blo 99781 1602935 := bstep (se 1 (by rfl) ⟨1202201, by rfl⟩ : syracuseStep 1602935 = 2404403) B2404403
theorem B1178063 : Blo 99781 1178063 := bstep (se 1 (by rfl) ⟨883547, by rfl⟩ : syracuseStep 1178063 = 1767095) B1767095
theorem B391823 : Blo 99781 391823 := bstep (se 1 (by rfl) ⟨293867, by rfl⟩ : syracuseStep 391823 = 587735) B587735
theorem B261103 : Blo 99781 261103 := bstep (se 1 (by rfl) ⟨195827, by rfl⟩ : syracuseStep 261103 = 391655) B391655
theorem B262379 : Blo 99781 262379 := bstep (se 1 (by rfl) ⟨196784, by rfl⟩ : syracuseStep 262379 = 393569) B393569
theorem B231479 : Blo 99781 231479 := bstep (se 1 (by rfl) ⟨173609, by rfl⟩ : syracuseStep 231479 = 347219) B347219
theorem B4330259 : Blo 99781 4330259 := bstep (se 1 (by rfl) ⟨3247694, by rfl⟩ : syracuseStep 4330259 = 6495389) B6495389
theorem B103455 : Blo 99781 103455 := bstep (se 1 (by rfl) ⟨77591, by rfl⟩ : syracuseStep 103455 = 155183) B155183
theorem B103591 : Blo 99781 103591 := bstep (se 1 (by rfl) ⟨77693, by rfl⟩ : syracuseStep 103591 = 155387) B155387
theorem B366059 : Blo 99781 366059 := bstep (se 1 (by rfl) ⟨274544, by rfl⟩ : syracuseStep 366059 = 549089) B549089
theorem B169519 : Blo 99781 169519 := bstep (se 1 (by rfl) ⟨127139, by rfl⟩ : syracuseStep 169519 = 254279) B254279
theorem B662251 : Blo 99781 662251 := bstep (se 1 (by rfl) ⟨496688, by rfl⟩ : syracuseStep 662251 = 993377) B993377
theorem B1056041 : Blo 99781 1056041 := bstep (se 2 (by rfl) ⟨396015, by rfl⟩ : syracuseStep 1056041 = 792031) B792031
theorem B1978141 : Blo 99781 1978141 := bstep (se 3 (by rfl) ⟨370901, by rfl⟩ : syracuseStep 1978141 = 741803) B741803
theorem B28422251 : Blo 99781 28422251 := bstep (se 1 (by rfl) ⟨21316688, by rfl⟩ : syracuseStep 28422251 = 42633377) B42633377
theorem B700631 : Blo 99781 700631 := bstep (se 1 (by rfl) ⟨525473, by rfl⟩ : syracuseStep 700631 = 1050947) B1050947
theorem B1028371 : Blo 99781 1028371 := bstep (se 1 (by rfl) ⟨771278, by rfl⟩ : syracuseStep 1028371 = 1542557) B1542557
theorem B864755 : Blo 99781 864755 := bstep (se 1 (by rfl) ⟨648566, by rfl⟩ : syracuseStep 864755 = 1297133) B1297133
theorem B114079 : Blo 99781 114079 := bstep (se 1 (by rfl) ⟨85559, by rfl⟩ : syracuseStep 114079 = 171119) B171119
theorem B4931927 : Blo 99781 4931927 := bstep (se 1 (by rfl) ⟨3698945, by rfl⟩ : syracuseStep 4931927 = 7397891) B7397891
theorem B151019 : Blo 99781 151019 := bstep (se 1 (by rfl) ⟨113264, by rfl⟩ : syracuseStep 151019 = 226529) B226529
theorem B1068623 : Blo 99781 1068623 := bstep (se 1 (by rfl) ⟨801467, by rfl⟩ : syracuseStep 1068623 = 1602935) B1602935
theorem B348137 : Blo 99781 348137 := bstep (se 2 (by rfl) ⟨130551, by rfl⟩ : syracuseStep 348137 = 261103) B261103
theorem B512891 : Blo 99781 512891 := bstep (se 1 (by rfl) ⟨384668, by rfl⟩ : syracuseStep 512891 = 769337) B769337
theorem B349811 : Blo 99781 349811 := bstep (se 1 (by rfl) ⟨262358, by rfl⟩ : syracuseStep 349811 = 524717) B524717
theorem B153839 : Blo 99781 153839 := bstep (se 1 (by rfl) ⟨115379, by rfl⟩ : syracuseStep 153839 = 230759) B230759
theorem B153977 : Blo 99781 153977 := bstep (se 2 (by rfl) ⟨57741, by rfl⟩ : syracuseStep 153977 = 115483) B115483
theorem B515483 : Blo 99781 515483 := bstep (se 1 (by rfl) ⟨386612, by rfl⟩ : syracuseStep 515483 = 773225) B773225
theorem B582335 : Blo 99781 582335 := bstep (se 1 (by rfl) ⟨436751, by rfl⟩ : syracuseStep 582335 = 873503) B873503
theorem B255059 : Blo 99781 255059 := bstep (se 1 (by rfl) ⟨191294, by rfl⟩ : syracuseStep 255059 = 382589) B382589
theorem B583033 : Blo 99781 583033 := bstep (se 2 (by rfl) ⟨218637, by rfl⟩ : syracuseStep 583033 = 437275) B437275
theorem B8381875 : Blo 99781 8381875 := bstep (se 1 (by rfl) ⟨6286406, by rfl⟩ : syracuseStep 8381875 = 12572813) B12572813
theorem B4122359 : Blo 99781 4122359 := bstep (se 1 (by rfl) ⟨3091769, by rfl⟩ : syracuseStep 4122359 = 6183539) B6183539
theorem B517913 : Blo 99781 517913 := bstep (se 2 (by rfl) ⟨194217, by rfl⟩ : syracuseStep 517913 = 388435) B388435
theorem B387449 : Blo 99781 387449 := bstep (se 2 (by rfl) ⟨145293, by rfl⟩ : syracuseStep 387449 = 290587) B290587
theorem B256871 : Blo 99781 256871 := bstep (se 1 (by rfl) ⟨192653, by rfl⟩ : syracuseStep 256871 = 385307) B385307
theorem B257519 : Blo 99781 257519 := bstep (se 1 (by rfl) ⟨193139, by rfl⟩ : syracuseStep 257519 = 386279) B386279
theorem B552703 : Blo 99781 552703 := bstep (se 1 (by rfl) ⟨414527, by rfl⟩ : syracuseStep 552703 = 829055) B829055
theorem B586277 : Blo 99781 586277 := bstep (se 4 (by rfl) ⟨54963, by rfl⟩ : syracuseStep 586277 = 109927) B109927
theorem B1307279 : Blo 99781 1307279 := bstep (se 1 (by rfl) ⟨980459, by rfl⟩ : syracuseStep 1307279 = 1960919) B1960919
theorem B226151 : Blo 99781 226151 := bstep (se 1 (by rfl) ⟨169613, by rfl⟩ : syracuseStep 226151 = 339227) B339227
theorem B226511 : Blo 99781 226511 := bstep (se 1 (by rfl) ⟨169883, by rfl⟩ : syracuseStep 226511 = 339767) B339767
theorem B2029495 : Blo 99781 2029495 := bstep (se 1 (by rfl) ⟨1522121, by rfl⟩ : syracuseStep 2029495 = 3044243) B3044243
theorem B194537 : Blo 99781 194537 := bstep (se 2 (by rfl) ⟨72951, by rfl⟩ : syracuseStep 194537 = 145903) B145903
theorem B522287 : Blo 99781 522287 := bstep (se 1 (by rfl) ⟨391715, by rfl⟩ : syracuseStep 522287 = 783431) B783431
theorem B228059 : Blo 99781 228059 := bstep (se 1 (by rfl) ⟨171044, by rfl⟩ : syracuseStep 228059 = 342089) B342089
theorem B785375 : Blo 99781 785375 := bstep (se 1 (by rfl) ⟨589031, by rfl⟩ : syracuseStep 785375 = 1178063) B1178063
theorem B261215 : Blo 99781 261215 := bstep (se 1 (by rfl) ⟨195911, by rfl⟩ : syracuseStep 261215 = 391823) B391823
theorem B229031 : Blo 99781 229031 := bstep (se 1 (by rfl) ⟨171773, by rfl⟩ : syracuseStep 229031 = 343547) B343547
theorem B229139 : Blo 99781 229139 := bstep (se 1 (by rfl) ⟨171854, by rfl⟩ : syracuseStep 229139 = 343709) B343709
theorem B1736477 : Blo 99781 1736477 := bstep (se 3 (by rfl) ⟨325589, by rfl⟩ : syracuseStep 1736477 = 651179) B651179
theorem B229355 : Blo 99781 229355 := bstep (se 1 (by rfl) ⟨172016, by rfl⟩ : syracuseStep 229355 = 344033) B344033
theorem B11175833 : Blo 99781 11175833 := bstep (se 2 (by rfl) ⟨4190937, by rfl⟩ : syracuseStep 11175833 = 8381875) B8381875
theorem B100679 : Blo 99781 100679 := bstep (se 1 (by rfl) ⟨75509, by rfl⟩ : syracuseStep 100679 = 151019) B151019
theorem B232091 : Blo 99781 232091 := bstep (se 1 (by rfl) ⟨174068, by rfl⟩ : syracuseStep 232091 = 348137) B348137
theorem B2886839 : Blo 99781 2886839 := bstep (se 1 (by rfl) ⟨2165129, by rfl⟩ : syracuseStep 2886839 = 4330259) B4330259
theorem B233207 : Blo 99781 233207 := bstep (se 1 (by rfl) ⟨174905, by rfl⟩ : syracuseStep 233207 = 349811) B349811
theorem B102559 : Blo 99781 102559 := bstep (se 1 (by rfl) ⟨76919, by rfl⟩ : syracuseStep 102559 = 153839) B153839
theorem B102651 : Blo 99781 102651 := bstep (se 1 (by rfl) ⟨76988, by rfl⟩ : syracuseStep 102651 = 153977) B153977
theorem B170039 : Blo 99781 170039 := bstep (se 1 (by rfl) ⟨127529, by rfl⟩ : syracuseStep 170039 = 255059) B255059
theorem B171247 : Blo 99781 171247 := bstep (se 1 (by rfl) ⟨128435, by rfl⟩ : syracuseStep 171247 = 256871) B256871
theorem B171679 : Blo 99781 171679 := bstep (se 1 (by rfl) ⟨128759, by rfl⟩ : syracuseStep 171679 = 257519) B257519
theorem B18948167 : Blo 99781 18948167 := bstep (se 1 (by rfl) ⟨14211125, by rfl⟩ : syracuseStep 18948167 = 28422251) B28422251
theorem B467087 : Blo 99781 467087 := bstep (se 1 (by rfl) ⟨350315, by rfl⟩ : syracuseStep 467087 = 700631) B700631
theorem B174143 : Blo 99781 174143 := bstep (se 1 (by rfl) ⟨130607, by rfl⟩ : syracuseStep 174143 = 261215) B261215
theorem B1157651 : Blo 99781 1157651 := bstep (se 1 (by rfl) ⟨868238, by rfl⟩ : syracuseStep 1157651 = 1736477) B1736477
theorem B174919 : Blo 99781 174919 := bstep (se 1 (by rfl) ⟨131189, by rfl⟩ : syracuseStep 174919 = 262379) B262379
theorem B3287951 : Blo 99781 3287951 := bstep (se 1 (by rfl) ⟨2465963, by rfl⟩ : syracuseStep 3287951 = 4931927) B4931927
theorem B341927 : Blo 99781 341927 := bstep (se 1 (by rfl) ⟨256445, by rfl⟩ : syracuseStep 341927 = 512891) B512891
theorem B244039 : Blo 99781 244039 := bstep (se 1 (by rfl) ⟨183029, by rfl⟩ : syracuseStep 244039 = 366059) B366059
theorem B704027 : Blo 99781 704027 := bstep (se 1 (by rfl) ⟨528020, by rfl⟩ : syracuseStep 704027 = 1056041) B1056041
theorem B343655 : Blo 99781 343655 := bstep (se 1 (by rfl) ⟨257741, by rfl⟩ : syracuseStep 343655 = 515483) B515483
theorem B736937 : Blo 99781 736937 := bstep (se 2 (by rfl) ⟨276351, by rfl⟩ : syracuseStep 736937 = 552703) B552703
theorem B2637521 : Blo 99781 2637521 := bstep (se 2 (by rfl) ⟨989070, by rfl⟩ : syracuseStep 2637521 = 1978141) B1978141
theorem B345275 : Blo 99781 345275 := bstep (se 1 (by rfl) ⟨258956, by rfl⟩ : syracuseStep 345275 = 517913) B517913
theorem B2705993 : Blo 99781 2705993 := bstep (se 2 (by rfl) ⟨1014747, by rfl⟩ : syracuseStep 2705993 = 2029495) B2029495
theorem B576503 : Blo 99781 576503 := bstep (se 1 (by rfl) ⟨432377, by rfl⟩ : syracuseStep 576503 = 864755) B864755
theorem B871519 : Blo 99781 871519 := bstep (se 1 (by rfl) ⟨653639, by rfl⟩ : syracuseStep 871519 = 1307279) B1307279
theorem B150767 : Blo 99781 150767 := bstep (se 1 (by rfl) ⟨113075, by rfl⟩ : syracuseStep 150767 = 226151) B226151
theorem B151007 : Blo 99781 151007 := bstep (se 1 (by rfl) ⟨113255, by rfl⟩ : syracuseStep 151007 = 226511) B226511
theorem B348191 : Blo 99781 348191 := bstep (se 1 (by rfl) ⟨261143, by rfl⟩ : syracuseStep 348191 = 522287) B522287
theorem B152039 : Blo 99781 152039 := bstep (se 1 (by rfl) ⟨114029, by rfl⟩ : syracuseStep 152039 = 228059) B228059
theorem B152105 : Blo 99781 152105 := bstep (se 2 (by rfl) ⟨57039, by rfl⟩ : syracuseStep 152105 = 114079) B114079
theorem B152687 : Blo 99781 152687 := bstep (se 1 (by rfl) ⟨114515, by rfl⟩ : syracuseStep 152687 = 229031) B229031
theorem B152759 : Blo 99781 152759 := bstep (se 1 (by rfl) ⟨114569, by rfl⟩ : syracuseStep 152759 = 229139) B229139
theorem B152903 : Blo 99781 152903 := bstep (se 1 (by rfl) ⟨114677, by rfl⟩ : syracuseStep 152903 = 229355) B229355
theorem B154319 : Blo 99781 154319 := bstep (se 1 (by rfl) ⟨115739, by rfl⟩ : syracuseStep 154319 = 231479) B231479
theorem B777377 : Blo 99781 777377 := bstep (se 2 (by rfl) ⟨291516, by rfl⟩ : syracuseStep 777377 = 583033) B583033
theorem B712415 : Blo 99781 712415 := bstep (se 1 (by rfl) ⟨534311, by rfl⟩ : syracuseStep 712415 = 1068623) B1068623
theorem B1371161 : Blo 99781 1371161 := bstep (se 2 (by rfl) ⟨514185, by rfl⟩ : syracuseStep 1371161 = 1028371) B1028371
theorem B388223 : Blo 99781 388223 := bstep (se 1 (by rfl) ⟨291167, by rfl⟩ : syracuseStep 388223 = 582335) B582335
theorem B2748239 : Blo 99781 2748239 := bstep (se 1 (by rfl) ⟨2061179, by rfl⟩ : syracuseStep 2748239 = 4122359) B4122359
theorem B258299 : Blo 99781 258299 := bstep (se 1 (by rfl) ⟨193724, by rfl⟩ : syracuseStep 258299 = 387449) B387449
theorem B226025 : Blo 99781 226025 := bstep (se 2 (by rfl) ⟨84759, by rfl⟩ : syracuseStep 226025 = 169519) B169519
theorem B390851 : Blo 99781 390851 := bstep (se 1 (by rfl) ⟨293138, by rfl⟩ : syracuseStep 390851 = 586277) B586277
theorem B883001 : Blo 99781 883001 := bstep (se 2 (by rfl) ⟨331125, by rfl⟩ : syracuseStep 883001 = 662251) B662251
theorem B129691 : Blo 99781 129691 := bstep (se 1 (by rfl) ⟨97268, by rfl⟩ : syracuseStep 129691 = 194537) B194537
theorem B523583 : Blo 99781 523583 := bstep (se 1 (by rfl) ⟨392687, by rfl⟩ : syracuseStep 523583 = 785375) B785375
theorem B1245565 : Blo 99781 1245565 := bstep (se 3 (by rfl) ⟨233543, by rfl⟩ : syracuseStep 1245565 = 467087) B467087
theorem B230183 : Blo 99781 230183 := bstep (se 1 (by rfl) ⟨172637, by rfl⟩ : syracuseStep 230183 = 345275) B345275
theorem B1803995 : Blo 99781 1803995 := bstep (se 1 (by rfl) ⟨1352996, by rfl⟩ : syracuseStep 1803995 = 2705993) B2705993
theorem B100511 : Blo 99781 100511 := bstep (se 1 (by rfl) ⟨75383, by rfl⟩ : syracuseStep 100511 = 150767) B150767
theorem B100671 : Blo 99781 100671 := bstep (se 1 (by rfl) ⟨75503, by rfl⟩ : syracuseStep 100671 = 151007) B151007
theorem B232127 : Blo 99781 232127 := bstep (se 1 (by rfl) ⟨174095, by rfl⟩ : syracuseStep 232127 = 348191) B348191
theorem B101359 : Blo 99781 101359 := bstep (se 1 (by rfl) ⟨76019, by rfl⟩ : syracuseStep 101359 = 152039) B152039
theorem B101403 : Blo 99781 101403 := bstep (se 1 (by rfl) ⟨76052, by rfl⟩ : syracuseStep 101403 = 152105) B152105
theorem B101791 : Blo 99781 101791 := bstep (se 1 (by rfl) ⟨76343, by rfl⟩ : syracuseStep 101791 = 152687) B152687
theorem B101839 : Blo 99781 101839 := bstep (se 1 (by rfl) ⟨76379, by rfl⟩ : syracuseStep 101839 = 152759) B152759
theorem B101935 : Blo 99781 101935 := bstep (se 1 (by rfl) ⟨76451, by rfl⟩ : syracuseStep 101935 = 152903) B152903
theorem B233225 : Blo 99781 233225 := bstep (se 2 (by rfl) ⟨87459, by rfl⟩ : syracuseStep 233225 = 174919) B174919
theorem B102879 : Blo 99781 102879 := bstep (se 1 (by rfl) ⟨77159, by rfl⟩ : syracuseStep 102879 = 154319) B154319
theorem B172199 : Blo 99781 172199 := bstep (se 1 (by rfl) ⟨129149, by rfl⟩ : syracuseStep 172199 = 258299) B258299
theorem B172921 : Blo 99781 172921 := bstep (se 2 (by rfl) ⟨64845, by rfl⟩ : syracuseStep 172921 = 129691) B129691
theorem B469351 : Blo 99781 469351 := bstep (se 1 (by rfl) ⟨352013, by rfl⟩ : syracuseStep 469351 = 704027) B704027
theorem B7450555 : Blo 99781 7450555 := bstep (se 1 (by rfl) ⟨5587916, by rfl⟩ : syracuseStep 7450555 = 11175833) B11175833
theorem B113359 : Blo 99781 113359 := bstep (se 1 (by rfl) ⟨85019, by rfl⟩ : syracuseStep 113359 = 170039) B170039
theorem B1162025 : Blo 99781 1162025 := bstep (se 2 (by rfl) ⟨435759, by rfl⟩ : syracuseStep 1162025 = 871519) B871519
theorem B12632111 : Blo 99781 12632111 := bstep (se 1 (by rfl) ⟨9474083, by rfl⟩ : syracuseStep 12632111 = 18948167) B18948167
theorem B116095 : Blo 99781 116095 := bstep (se 1 (by rfl) ⟨87071, by rfl⟩ : syracuseStep 116095 = 174143) B174143
theorem B771767 : Blo 99781 771767 := bstep (se 1 (by rfl) ⟨578825, by rfl⟩ : syracuseStep 771767 = 1157651) B1157651
theorem B150683 : Blo 99781 150683 := bstep (se 1 (by rfl) ⟨113012, by rfl⟩ : syracuseStep 150683 = 226025) B226025
theorem B349055 : Blo 99781 349055 := bstep (se 1 (by rfl) ⟨261791, by rfl⟩ : syracuseStep 349055 = 523583) B523583
theorem B1758347 : Blo 99781 1758347 := bstep (se 1 (by rfl) ⟨1318760, by rfl⟩ : syracuseStep 1758347 = 2637521) B2637521
theorem B154727 : Blo 99781 154727 := bstep (se 1 (by rfl) ⟨116045, by rfl⟩ : syracuseStep 154727 = 232091) B232091
theorem B384335 : Blo 99781 384335 := bstep (se 1 (by rfl) ⟨288251, by rfl⟩ : syracuseStep 384335 = 576503) B576503
theorem B1924559 : Blo 99781 1924559 := bstep (se 1 (by rfl) ⟨1443419, by rfl⟩ : syracuseStep 1924559 = 2886839) B2886839
theorem B155471 : Blo 99781 155471 := bstep (se 1 (by rfl) ⟨116603, by rfl⟩ : syracuseStep 155471 = 233207) B233207
theorem B518251 : Blo 99781 518251 := bstep (se 1 (by rfl) ⟨388688, by rfl⟩ : syracuseStep 518251 = 777377) B777377
theorem B2191967 : Blo 99781 2191967 := bstep (se 1 (by rfl) ⟨1643975, by rfl⟩ : syracuseStep 2191967 = 3287951) B3287951
theorem B914107 : Blo 99781 914107 := bstep (se 1 (by rfl) ⟨685580, by rfl⟩ : syracuseStep 914107 = 1371161) B1371161
theorem B258815 : Blo 99781 258815 := bstep (se 1 (by rfl) ⟨194111, by rfl⟩ : syracuseStep 258815 = 388223) B388223
theorem B1832159 : Blo 99781 1832159 := bstep (se 1 (by rfl) ⟨1374119, by rfl⟩ : syracuseStep 1832159 = 2748239) B2748239
theorem B325385 : Blo 99781 325385 := bstep (se 2 (by rfl) ⟨122019, by rfl⟩ : syracuseStep 325385 = 244039) B244039
theorem B260567 : Blo 99781 260567 := bstep (se 1 (by rfl) ⟨195425, by rfl⟩ : syracuseStep 260567 = 390851) B390851
theorem B227951 : Blo 99781 227951 := bstep (se 1 (by rfl) ⟨170963, by rfl⟩ : syracuseStep 227951 = 341927) B341927
theorem B588667 : Blo 99781 588667 := bstep (se 1 (by rfl) ⟨441500, by rfl⟩ : syracuseStep 588667 = 883001) B883001
theorem B228329 : Blo 99781 228329 := bstep (se 2 (by rfl) ⟨85623, by rfl⟩ : syracuseStep 228329 = 171247) B171247
theorem B1899773 : Blo 99781 1899773 := bstep (se 3 (by rfl) ⟨356207, by rfl⟩ : syracuseStep 1899773 = 712415) B712415
theorem B228905 : Blo 99781 228905 := bstep (se 2 (by rfl) ⟨85839, by rfl⟩ : syracuseStep 228905 = 171679) B171679
theorem B229103 : Blo 99781 229103 := bstep (se 1 (by rfl) ⟨171827, by rfl⟩ : syracuseStep 229103 = 343655) B343655
theorem B491291 : Blo 99781 491291 := bstep (se 1 (by rfl) ⟨368468, by rfl⟩ : syracuseStep 491291 = 736937) B736937
theorem B8421407 : Blo 99781 8421407 := bstep (se 1 (by rfl) ⟨6316055, by rfl⟩ : syracuseStep 8421407 = 12632111) B12632111
theorem B230561 : Blo 99781 230561 := bstep (se 2 (by rfl) ⟨86460, by rfl⟩ : syracuseStep 230561 = 172921) B172921
theorem B100455 : Blo 99781 100455 := bstep (se 1 (by rfl) ⟨75341, by rfl⟩ : syracuseStep 100455 = 150683) B150683
theorem B691001 : Blo 99781 691001 := bstep (se 2 (by rfl) ⟨259125, by rfl⟩ : syracuseStep 691001 = 518251) B518251
theorem B625801 : Blo 99781 625801 := bstep (se 2 (by rfl) ⟨234675, by rfl⟩ : syracuseStep 625801 = 469351) B469351
theorem B232703 : Blo 99781 232703 := bstep (se 1 (by rfl) ⟨174527, by rfl⟩ : syracuseStep 232703 = 349055) B349055
theorem B103151 : Blo 99781 103151 := bstep (se 1 (by rfl) ⟨77363, by rfl⟩ : syracuseStep 103151 = 154727) B154727
theorem B1283039 : Blo 99781 1283039 := bstep (se 1 (by rfl) ⟨962279, by rfl⟩ : syracuseStep 1283039 = 1924559) B1924559
theorem B103647 : Blo 99781 103647 := bstep (se 1 (by rfl) ⟨77735, by rfl⟩ : syracuseStep 103647 = 155471) B155471
theorem B9934073 : Blo 99781 9934073 := bstep (se 2 (by rfl) ⟨3725277, by rfl⟩ : syracuseStep 9934073 = 7450555) B7450555
theorem B1218809 : Blo 99781 1218809 := bstep (se 2 (by rfl) ⟨457053, by rfl⟩ : syracuseStep 1218809 = 914107) B914107
theorem B172543 : Blo 99781 172543 := bstep (se 1 (by rfl) ⟨129407, by rfl⟩ : syracuseStep 172543 = 258815) B258815
theorem B1221439 : Blo 99781 1221439 := bstep (se 1 (by rfl) ⟨916079, by rfl⟩ : syracuseStep 1221439 = 1832159) B1832159
theorem B173711 : Blo 99781 173711 := bstep (se 1 (by rfl) ⟨130283, by rfl⟩ : syracuseStep 173711 = 260567) B260567
theorem B114799 : Blo 99781 114799 := bstep (se 1 (by rfl) ⟨86099, by rfl⟩ : syracuseStep 114799 = 172199) B172199
theorem B1461311 : Blo 99781 1461311 := bstep (se 1 (by rfl) ⟨1095983, by rfl⟩ : syracuseStep 1461311 = 2191967) B2191967
theorem B151145 : Blo 99781 151145 := bstep (se 2 (by rfl) ⟨56679, by rfl⟩ : syracuseStep 151145 = 113359) B113359
theorem B216923 : Blo 99781 216923 := bstep (se 1 (by rfl) ⟨162692, by rfl⟩ : syracuseStep 216923 = 325385) B325385
theorem B151967 : Blo 99781 151967 := bstep (se 1 (by rfl) ⟨113975, by rfl⟩ : syracuseStep 151967 = 227951) B227951
theorem B774683 : Blo 99781 774683 := bstep (se 1 (by rfl) ⟨581012, by rfl⟩ : syracuseStep 774683 = 1162025) B1162025
theorem B152219 : Blo 99781 152219 := bstep (se 1 (by rfl) ⟨114164, by rfl⟩ : syracuseStep 152219 = 228329) B228329
theorem B1266515 : Blo 99781 1266515 := bstep (se 1 (by rfl) ⟨949886, by rfl⟩ : syracuseStep 1266515 = 1899773) B1899773
theorem B152603 : Blo 99781 152603 := bstep (se 1 (by rfl) ⟨114452, by rfl⟩ : syracuseStep 152603 = 228905) B228905
theorem B152735 : Blo 99781 152735 := bstep (se 1 (by rfl) ⟨114551, by rfl⟩ : syracuseStep 152735 = 229103) B229103
theorem B1660753 : Blo 99781 1660753 := bstep (se 2 (by rfl) ⟨622782, by rfl⟩ : syracuseStep 1660753 = 1245565) B1245565
theorem B153455 : Blo 99781 153455 := bstep (se 1 (by rfl) ⟨115091, by rfl⟩ : syracuseStep 153455 = 230183) B230183
theorem B514511 : Blo 99781 514511 := bstep (se 1 (by rfl) ⟨385883, by rfl⟩ : syracuseStep 514511 = 771767) B771767
theorem B1202663 : Blo 99781 1202663 := bstep (se 1 (by rfl) ⟨901997, by rfl⟩ : syracuseStep 1202663 = 1803995) B1803995
theorem B154751 : Blo 99781 154751 := bstep (se 1 (by rfl) ⟨116063, by rfl⟩ : syracuseStep 154751 = 232127) B232127
theorem B154793 : Blo 99781 154793 := bstep (se 2 (by rfl) ⟨58047, by rfl⟩ : syracuseStep 154793 = 116095) B116095
theorem B155483 : Blo 99781 155483 := bstep (se 1 (by rfl) ⟨116612, by rfl⟩ : syracuseStep 155483 = 233225) B233225
theorem B1172231 : Blo 99781 1172231 := bstep (se 1 (by rfl) ⟨879173, by rfl⟩ : syracuseStep 1172231 = 1758347) B1758347
theorem B256223 : Blo 99781 256223 := bstep (se 1 (by rfl) ⟨192167, by rfl⟩ : syracuseStep 256223 = 384335) B384335
theorem B784889 : Blo 99781 784889 := bstep (se 2 (by rfl) ⟨294333, by rfl⟩ : syracuseStep 784889 = 588667) B588667
theorem B327527 : Blo 99781 327527 := bstep (se 1 (by rfl) ⟨245645, by rfl⟩ : syracuseStep 327527 = 491291) B491291
theorem B230057 : Blo 99781 230057 := bstep (se 2 (by rfl) ⟨86271, by rfl⟩ : syracuseStep 230057 = 172543) B172543
theorem B460667 : Blo 99781 460667 := bstep (se 1 (by rfl) ⟨345500, by rfl⟩ : syracuseStep 460667 = 691001) B691001
theorem B100763 : Blo 99781 100763 := bstep (se 1 (by rfl) ⟨75572, by rfl⟩ : syracuseStep 100763 = 151145) B151145
theorem B101311 : Blo 99781 101311 := bstep (se 1 (by rfl) ⟨75983, by rfl⟩ : syracuseStep 101311 = 151967) B151967
theorem B101479 : Blo 99781 101479 := bstep (se 1 (by rfl) ⟨76109, by rfl⟩ : syracuseStep 101479 = 152219) B152219
theorem B855359 : Blo 99781 855359 := bstep (se 1 (by rfl) ⟨641519, by rfl⟩ : syracuseStep 855359 = 1283039) B1283039
theorem B101735 : Blo 99781 101735 := bstep (se 1 (by rfl) ⟨76301, by rfl⟩ : syracuseStep 101735 = 152603) B152603
theorem B101823 : Blo 99781 101823 := bstep (se 1 (by rfl) ⟨76367, by rfl⟩ : syracuseStep 101823 = 152735) B152735
theorem B6622715 : Blo 99781 6622715 := bstep (se 1 (by rfl) ⟨4967036, by rfl⟩ : syracuseStep 6622715 = 9934073) B9934073
theorem B102303 : Blo 99781 102303 := bstep (se 1 (by rfl) ⟨76727, by rfl⟩ : syracuseStep 102303 = 153455) B153455
theorem B103167 : Blo 99781 103167 := bstep (se 1 (by rfl) ⟨77375, by rfl⟩ : syracuseStep 103167 = 154751) B154751
theorem B103195 : Blo 99781 103195 := bstep (se 1 (by rfl) ⟨77396, by rfl⟩ : syracuseStep 103195 = 154793) B154793
theorem B103655 : Blo 99781 103655 := bstep (se 1 (by rfl) ⟨77741, by rfl⟩ : syracuseStep 103655 = 155483) B155483
theorem B170815 : Blo 99781 170815 := bstep (se 1 (by rfl) ⟨128111, by rfl⟩ : syracuseStep 170815 = 256223) B256223
theorem B8857349 : Blo 99781 8857349 := bstep (se 4 (by rfl) ⟨830376, by rfl⟩ : syracuseStep 8857349 = 1660753) B1660753
theorem B5614271 : Blo 99781 5614271 := bstep (se 1 (by rfl) ⟨4210703, by rfl⟩ : syracuseStep 5614271 = 8421407) B8421407
theorem B834401 : Blo 99781 834401 := bstep (se 2 (by rfl) ⟨312900, by rfl⟩ : syracuseStep 834401 = 625801) B625801
theorem B343007 : Blo 99781 343007 := bstep (se 1 (by rfl) ⟨257255, by rfl⟩ : syracuseStep 343007 = 514511) B514511
theorem B801775 : Blo 99781 801775 := bstep (se 1 (by rfl) ⟨601331, by rfl⟩ : syracuseStep 801775 = 1202663) B1202663
theorem B115807 : Blo 99781 115807 := bstep (se 1 (by rfl) ⟨86855, by rfl⟩ : syracuseStep 115807 = 173711) B173711
theorem B578461 : Blo 99781 578461 := bstep (se 3 (by rfl) ⟨108461, by rfl⟩ : syracuseStep 578461 = 216923) B216923
theorem B218351 : Blo 99781 218351 := bstep (se 1 (by rfl) ⟨163763, by rfl⟩ : syracuseStep 218351 = 327527) B327527
theorem B153065 : Blo 99781 153065 := bstep (se 2 (by rfl) ⟨57399, by rfl⟩ : syracuseStep 153065 = 114799) B114799
theorem B153707 : Blo 99781 153707 := bstep (se 1 (by rfl) ⟨115280, by rfl⟩ : syracuseStep 153707 = 230561) B230561
theorem B1628585 : Blo 99781 1628585 := bstep (se 2 (by rfl) ⟨610719, by rfl⟩ : syracuseStep 1628585 = 1221439) B1221439
theorem B974207 : Blo 99781 974207 := bstep (se 1 (by rfl) ⟨730655, by rfl⟩ : syracuseStep 974207 = 1461311) B1461311
theorem B155135 : Blo 99781 155135 := bstep (se 1 (by rfl) ⟨116351, by rfl⟩ : syracuseStep 155135 = 232703) B232703
theorem B516455 : Blo 99781 516455 := bstep (se 1 (by rfl) ⟨387341, by rfl⟩ : syracuseStep 516455 = 774683) B774683
theorem B844343 : Blo 99781 844343 := bstep (se 1 (by rfl) ⟨633257, by rfl⟩ : syracuseStep 844343 = 1266515) B1266515
theorem B812539 : Blo 99781 812539 := bstep (se 1 (by rfl) ⟨609404, by rfl⟩ : syracuseStep 812539 = 1218809) B1218809
theorem B781487 : Blo 99781 781487 := bstep (se 1 (by rfl) ⟨586115, by rfl⟩ : syracuseStep 781487 = 1172231) B1172231
theorem B523259 : Blo 99781 523259 := bstep (se 1 (by rfl) ⟨392444, by rfl⟩ : syracuseStep 523259 = 784889) B784889
theorem B1083385 : Blo 99781 1083385 := bstep (se 2 (by rfl) ⟨406269, by rfl⟩ : syracuseStep 1083385 = 812539) B812539
theorem B102043 : Blo 99781 102043 := bstep (se 1 (by rfl) ⟨76532, by rfl⟩ : syracuseStep 102043 = 153065) B153065
theorem B102471 : Blo 99781 102471 := bstep (se 1 (by rfl) ⟨76853, by rfl⟩ : syracuseStep 102471 = 153707) B153707
theorem B1085723 : Blo 99781 1085723 := bstep (se 1 (by rfl) ⟨814292, by rfl⟩ : syracuseStep 1085723 = 1628585) B1628585
theorem B103423 : Blo 99781 103423 := bstep (se 1 (by rfl) ⟨77567, by rfl⟩ : syracuseStep 103423 = 155135) B155135
theorem B562895 : Blo 99781 562895 := bstep (se 1 (by rfl) ⟨422171, by rfl⟩ : syracuseStep 562895 = 844343) B844343
theorem B5904899 : Blo 99781 5904899 := bstep (se 1 (by rfl) ⟨4428674, by rfl⟩ : syracuseStep 5904899 = 8857349) B8857349
theorem B3742847 : Blo 99781 3742847 := bstep (se 1 (by rfl) ⟨2807135, by rfl⟩ : syracuseStep 3742847 = 5614271) B5614271
theorem B307111 : Blo 99781 307111 := bstep (se 1 (by rfl) ⟨230333, by rfl⟩ : syracuseStep 307111 = 460667) B460667
theorem B570239 : Blo 99781 570239 := bstep (se 1 (by rfl) ⟨427679, by rfl⟩ : syracuseStep 570239 = 855359) B855359
theorem B145567 : Blo 99781 145567 := bstep (se 1 (by rfl) ⟨109175, by rfl⟩ : syracuseStep 145567 = 218351) B218351
theorem B344303 : Blo 99781 344303 := bstep (se 1 (by rfl) ⟨258227, by rfl⟩ : syracuseStep 344303 = 516455) B516455
theorem B771281 : Blo 99781 771281 := bstep (se 2 (by rfl) ⟨289230, by rfl⟩ : syracuseStep 771281 = 578461) B578461
theorem B1069033 : Blo 99781 1069033 := bstep (se 2 (by rfl) ⟨400887, by rfl⟩ : syracuseStep 1069033 = 801775) B801775
theorem B348839 : Blo 99781 348839 := bstep (se 1 (by rfl) ⟨261629, by rfl⟩ : syracuseStep 348839 = 523259) B523259
theorem B153371 : Blo 99781 153371 := bstep (se 1 (by rfl) ⟨115028, by rfl⟩ : syracuseStep 153371 = 230057) B230057
theorem B154409 : Blo 99781 154409 := bstep (se 2 (by rfl) ⟨57903, by rfl⟩ : syracuseStep 154409 = 115807) B115807
theorem B4415143 : Blo 99781 4415143 := bstep (se 1 (by rfl) ⟨3311357, by rfl⟩ : syracuseStep 4415143 = 6622715) B6622715
theorem B649471 : Blo 99781 649471 := bstep (se 1 (by rfl) ⟨487103, by rfl⟩ : syracuseStep 649471 = 974207) B974207
theorem B520991 : Blo 99781 520991 := bstep (se 1 (by rfl) ⟨390743, by rfl⟩ : syracuseStep 520991 = 781487) B781487
theorem B2225069 : Blo 99781 2225069 := bstep (se 3 (by rfl) ⟨417200, by rfl⟩ : syracuseStep 2225069 = 834401) B834401
theorem B227753 : Blo 99781 227753 := bstep (se 2 (by rfl) ⟨85407, by rfl⟩ : syracuseStep 227753 = 170815) B170815
theorem B228671 : Blo 99781 228671 := bstep (se 1 (by rfl) ⟨171503, by rfl⟩ : syracuseStep 228671 = 343007) B343007
theorem B229535 : Blo 99781 229535 := bstep (se 1 (by rfl) ⟨172151, by rfl⟩ : syracuseStep 229535 = 344303) B344303
theorem B1444513 : Blo 99781 1444513 := bstep (se 2 (by rfl) ⟨541692, by rfl⟩ : syracuseStep 1444513 = 1083385) B1083385
theorem B723815 : Blo 99781 723815 := bstep (se 1 (by rfl) ⟨542861, by rfl⟩ : syracuseStep 723815 = 1085723) B1085723
theorem B232559 : Blo 99781 232559 := bstep (se 1 (by rfl) ⟨174419, by rfl⟩ : syracuseStep 232559 = 348839) B348839
theorem B102247 : Blo 99781 102247 := bstep (se 1 (by rfl) ⟨76685, by rfl⟩ : syracuseStep 102247 = 153371) B153371
theorem B3936599 : Blo 99781 3936599 := bstep (se 1 (by rfl) ⟨2952449, by rfl⟩ : syracuseStep 3936599 = 5904899) B5904899
theorem B102939 : Blo 99781 102939 := bstep (se 1 (by rfl) ⟨77204, by rfl⟩ : syracuseStep 102939 = 154409) B154409
theorem B2495231 : Blo 99781 2495231 := bstep (se 1 (by rfl) ⟨1871423, by rfl⟩ : syracuseStep 2495231 = 3742847) B3742847
theorem B1483379 : Blo 99781 1483379 := bstep (se 1 (by rfl) ⟨1112534, by rfl⟩ : syracuseStep 1483379 = 2225069) B2225069
theorem B865961 : Blo 99781 865961 := bstep (se 2 (by rfl) ⟨324735, by rfl⟩ : syracuseStep 865961 = 649471) B649471
theorem B375263 : Blo 99781 375263 := bstep (se 1 (by rfl) ⟨281447, by rfl⟩ : syracuseStep 375263 = 562895) B562895
theorem B409481 : Blo 99781 409481 := bstep (se 2 (by rfl) ⟨153555, by rfl⟩ : syracuseStep 409481 = 307111) B307111
theorem B1425377 : Blo 99781 1425377 := bstep (se 2 (by rfl) ⟨534516, by rfl⟩ : syracuseStep 1425377 = 1069033) B1069033
theorem B347327 : Blo 99781 347327 := bstep (se 1 (by rfl) ⟨260495, by rfl⟩ : syracuseStep 347327 = 520991) B520991
theorem B380159 : Blo 99781 380159 := bstep (se 1 (by rfl) ⟨285119, by rfl⟩ : syracuseStep 380159 = 570239) B570239
theorem B151835 : Blo 99781 151835 := bstep (se 1 (by rfl) ⟨113876, by rfl⟩ : syracuseStep 151835 = 227753) B227753
theorem B152447 : Blo 99781 152447 := bstep (se 1 (by rfl) ⟨114335, by rfl⟩ : syracuseStep 152447 = 228671) B228671
theorem B5886857 : Blo 99781 5886857 := bstep (se 2 (by rfl) ⟨2207571, by rfl⟩ : syracuseStep 5886857 = 4415143) B4415143
theorem B514187 : Blo 99781 514187 := bstep (se 1 (by rfl) ⟨385640, by rfl⟩ : syracuseStep 514187 = 771281) B771281
theorem B194089 : Blo 99781 194089 := bstep (se 2 (by rfl) ⟨72783, by rfl⟩ : syracuseStep 194089 = 145567) B145567
theorem B231551 : Blo 99781 231551 := bstep (se 1 (by rfl) ⟨173663, by rfl⟩ : syracuseStep 231551 = 347327) B347327
theorem B101223 : Blo 99781 101223 := bstep (se 1 (by rfl) ⟨75917, by rfl⟩ : syracuseStep 101223 = 151835) B151835
theorem B2624399 : Blo 99781 2624399 := bstep (se 1 (by rfl) ⟨1968299, by rfl⟩ : syracuseStep 2624399 = 3936599) B3936599
theorem B101631 : Blo 99781 101631 := bstep (se 1 (by rfl) ⟨76223, by rfl⟩ : syracuseStep 101631 = 152447) B152447
theorem B988919 : Blo 99781 988919 := bstep (se 1 (by rfl) ⟨741689, by rfl⟩ : syracuseStep 988919 = 1483379) B1483379
theorem B272987 : Blo 99781 272987 := bstep (se 1 (by rfl) ⟨204740, by rfl⟩ : syracuseStep 272987 = 409481) B409481
theorem B342791 : Blo 99781 342791 := bstep (se 1 (by rfl) ⟨257093, by rfl⟩ : syracuseStep 342791 = 514187) B514187
theorem B577307 : Blo 99781 577307 := bstep (se 1 (by rfl) ⟨432980, by rfl⟩ : syracuseStep 577307 = 865961) B865961
theorem B250175 : Blo 99781 250175 := bstep (se 1 (by rfl) ⟨187631, by rfl⟩ : syracuseStep 250175 = 375263) B375263
theorem B153023 : Blo 99781 153023 := bstep (se 1 (by rfl) ⟨114767, by rfl⟩ : syracuseStep 153023 = 229535) B229535
theorem B482543 : Blo 99781 482543 := bstep (se 1 (by rfl) ⟨361907, by rfl⟩ : syracuseStep 482543 = 723815) B723815
theorem B155039 : Blo 99781 155039 := bstep (se 1 (by rfl) ⟨116279, by rfl⟩ : syracuseStep 155039 = 232559) B232559
theorem B253439 : Blo 99781 253439 := bstep (se 1 (by rfl) ⟨190079, by rfl⟩ : syracuseStep 253439 = 380159) B380159
theorem B1663487 : Blo 99781 1663487 := bstep (se 1 (by rfl) ⟨1247615, by rfl⟩ : syracuseStep 1663487 = 2495231) B2495231
theorem B3924571 : Blo 99781 3924571 := bstep (se 1 (by rfl) ⟨2943428, by rfl⟩ : syracuseStep 3924571 = 5886857) B5886857
theorem B1926017 : Blo 99781 1926017 := bstep (se 2 (by rfl) ⟨722256, by rfl⟩ : syracuseStep 1926017 = 1444513) B1444513
theorem B258785 : Blo 99781 258785 := bstep (se 2 (by rfl) ⟨97044, by rfl⟩ : syracuseStep 258785 = 194089) B194089
theorem B3801005 : Blo 99781 3801005 := bstep (se 3 (by rfl) ⟨712688, by rfl⟩ : syracuseStep 3801005 = 1425377) B1425377
theorem B102015 : Blo 99781 102015 := bstep (se 1 (by rfl) ⟨76511, by rfl⟩ : syracuseStep 102015 = 153023) B153023
theorem B659279 : Blo 99781 659279 := bstep (se 1 (by rfl) ⟨494459, by rfl⟩ : syracuseStep 659279 = 988919) B988919
theorem B103359 : Blo 99781 103359 := bstep (se 1 (by rfl) ⟨77519, by rfl⟩ : syracuseStep 103359 = 155039) B155039
theorem B168959 : Blo 99781 168959 := bstep (se 1 (by rfl) ⟨126719, by rfl⟩ : syracuseStep 168959 = 253439) B253439
theorem B1284011 : Blo 99781 1284011 := bstep (se 1 (by rfl) ⟨963008, by rfl⟩ : syracuseStep 1284011 = 1926017) B1926017
theorem B172523 : Blo 99781 172523 := bstep (se 1 (by rfl) ⟨129392, by rfl⟩ : syracuseStep 172523 = 258785) B258785
theorem B2534003 : Blo 99781 2534003 := bstep (se 1 (by rfl) ⟨1900502, by rfl⟩ : syracuseStep 2534003 = 3801005) B3801005
theorem B667133 : Blo 99781 667133 := bstep (se 3 (by rfl) ⟨125087, by rfl⟩ : syracuseStep 667133 = 250175) B250175
theorem B1749599 : Blo 99781 1749599 := bstep (se 1 (by rfl) ⟨1312199, by rfl⟩ : syracuseStep 1749599 = 2624399) B2624399
theorem B181991 : Blo 99781 181991 := bstep (se 1 (by rfl) ⟨136493, by rfl⟩ : syracuseStep 181991 = 272987) B272987
theorem B5232761 : Blo 99781 5232761 := bstep (se 2 (by rfl) ⟨1962285, by rfl⟩ : syracuseStep 5232761 = 3924571) B3924571
theorem B154367 : Blo 99781 154367 := bstep (se 1 (by rfl) ⟨115775, by rfl⟩ : syracuseStep 154367 = 231551) B231551
theorem B384871 : Blo 99781 384871 := bstep (se 1 (by rfl) ⟨288653, by rfl⟩ : syracuseStep 384871 = 577307) B577307
theorem B321695 : Blo 99781 321695 := bstep (se 1 (by rfl) ⟨241271, by rfl⟩ : syracuseStep 321695 = 482543) B482543
theorem B1108991 : Blo 99781 1108991 := bstep (se 1 (by rfl) ⟨831743, by rfl⟩ : syracuseStep 1108991 = 1663487) B1663487
theorem B228527 : Blo 99781 228527 := bstep (se 1 (by rfl) ⟨171395, by rfl⟩ : syracuseStep 228527 = 342791) B342791
theorem B856007 : Blo 99781 856007 := bstep (se 1 (by rfl) ⟨642005, by rfl⟩ : syracuseStep 856007 = 1284011) B1284011
theorem B102911 : Blo 99781 102911 := bstep (se 1 (by rfl) ⟨77183, by rfl⟩ : syracuseStep 102911 = 154367) B154367
theorem B439519 : Blo 99781 439519 := bstep (se 1 (by rfl) ⟨329639, by rfl⟩ : syracuseStep 439519 = 659279) B659279
theorem B112639 : Blo 99781 112639 := bstep (se 1 (by rfl) ⟨84479, by rfl⟩ : syracuseStep 112639 = 168959) B168959
theorem B3488507 : Blo 99781 3488507 := bstep (se 1 (by rfl) ⟨2616380, by rfl⟩ : syracuseStep 3488507 = 5232761) B5232761
theorem B115015 : Blo 99781 115015 := bstep (se 1 (by rfl) ⟨86261, by rfl⟩ : syracuseStep 115015 = 172523) B172523
theorem B214463 : Blo 99781 214463 := bstep (se 1 (by rfl) ⟨160847, by rfl⟩ : syracuseStep 214463 = 321695) B321695
theorem B1689335 : Blo 99781 1689335 := bstep (se 1 (by rfl) ⟨1267001, by rfl⟩ : syracuseStep 1689335 = 2534003) B2534003
theorem B739327 : Blo 99781 739327 := bstep (se 1 (by rfl) ⟨554495, by rfl⟩ : syracuseStep 739327 = 1108991) B1108991
theorem B444755 : Blo 99781 444755 := bstep (se 1 (by rfl) ⟨333566, by rfl⟩ : syracuseStep 444755 = 667133) B667133
theorem B1166399 : Blo 99781 1166399 := bstep (se 1 (by rfl) ⟨874799, by rfl⟩ : syracuseStep 1166399 = 1749599) B1749599
theorem B152351 : Blo 99781 152351 := bstep (se 1 (by rfl) ⟨114263, by rfl⟩ : syracuseStep 152351 = 228527) B228527
theorem B513161 : Blo 99781 513161 := bstep (se 2 (by rfl) ⟨192435, by rfl⟩ : syracuseStep 513161 = 384871) B384871
theorem B485309 : Blo 99781 485309 := bstep (se 3 (by rfl) ⟨90995, by rfl⟩ : syracuseStep 485309 = 181991) B181991
theorem B296503 : Blo 99781 296503 := bstep (se 1 (by rfl) ⟨222377, by rfl⟩ : syracuseStep 296503 = 444755) B444755
theorem B985769 : Blo 99781 985769 := bstep (se 2 (by rfl) ⟨369663, by rfl⟩ : syracuseStep 985769 = 739327) B739327
theorem B101567 : Blo 99781 101567 := bstep (se 1 (by rfl) ⟨76175, by rfl⟩ : syracuseStep 101567 = 152351) B152351
theorem B142975 : Blo 99781 142975 := bstep (se 1 (by rfl) ⟨107231, by rfl⟩ : syracuseStep 142975 = 214463) B214463
theorem B1126223 : Blo 99781 1126223 := bstep (se 1 (by rfl) ⟨844667, by rfl⟩ : syracuseStep 1126223 = 1689335) B1689335
theorem B570671 : Blo 99781 570671 := bstep (se 1 (by rfl) ⟨428003, by rfl⟩ : syracuseStep 570671 = 856007) B856007
theorem B342107 : Blo 99781 342107 := bstep (se 1 (by rfl) ⟨256580, by rfl⟩ : syracuseStep 342107 = 513161) B513161
theorem B1294157 : Blo 99781 1294157 := bstep (se 3 (by rfl) ⟨242654, by rfl⟩ : syracuseStep 1294157 = 485309) B485309
theorem B150185 : Blo 99781 150185 := bstep (se 2 (by rfl) ⟨56319, by rfl⟩ : syracuseStep 150185 = 112639) B112639
theorem B153353 : Blo 99781 153353 := bstep (se 2 (by rfl) ⟨57507, by rfl⟩ : syracuseStep 153353 = 115015) B115015
theorem B777599 : Blo 99781 777599 := bstep (se 1 (by rfl) ⟨583199, by rfl⟩ : syracuseStep 777599 = 1166399) B1166399
theorem B586025 : Blo 99781 586025 := bstep (se 2 (by rfl) ⟨219759, by rfl⟩ : syracuseStep 586025 = 439519) B439519
theorem B2325671 : Blo 99781 2325671 := bstep (se 1 (by rfl) ⟨1744253, by rfl⟩ : syracuseStep 2325671 = 3488507) B3488507
theorem B6325397 : Blo 99781 6325397 := bstep (se 6 (by rfl) ⟨148251, by rfl⟩ : syracuseStep 6325397 = 296503) B296503
theorem B100123 : Blo 99781 100123 := bstep (se 1 (by rfl) ⟨75092, by rfl⟩ : syracuseStep 100123 = 150185) B150185
theorem B657179 : Blo 99781 657179 := bstep (se 1 (by rfl) ⟨492884, by rfl⟩ : syracuseStep 657179 = 985769) B985769
theorem B102235 : Blo 99781 102235 := bstep (se 1 (by rfl) ⟨76676, by rfl⟩ : syracuseStep 102235 = 153353) B153353
theorem B762533 : Blo 99781 762533 := bstep (se 4 (by rfl) ⟨71487, by rfl⟩ : syracuseStep 762533 = 142975) B142975
theorem B1550447 : Blo 99781 1550447 := bstep (se 1 (by rfl) ⟨1162835, by rfl⟩ : syracuseStep 1550447 = 2325671) B2325671
theorem B862771 : Blo 99781 862771 := bstep (se 1 (by rfl) ⟨647078, by rfl⟩ : syracuseStep 862771 = 1294157) B1294157
theorem B380447 : Blo 99781 380447 := bstep (se 1 (by rfl) ⟨285335, by rfl⟩ : syracuseStep 380447 = 570671) B570671
theorem B518399 : Blo 99781 518399 := bstep (se 1 (by rfl) ⟨388799, by rfl⟩ : syracuseStep 518399 = 777599) B777599
theorem B750815 : Blo 99781 750815 := bstep (se 1 (by rfl) ⟨563111, by rfl⟩ : syracuseStep 750815 = 1126223) B1126223
theorem B390683 : Blo 99781 390683 := bstep (se 1 (by rfl) ⟨293012, by rfl⟩ : syracuseStep 390683 = 586025) B586025
theorem B228071 : Blo 99781 228071 := bstep (se 1 (by rfl) ⟨171053, by rfl⟩ : syracuseStep 228071 = 342107) B342107
theorem B1150361 : Blo 99781 1150361 := bstep (se 2 (by rfl) ⟨431385, by rfl⟩ : syracuseStep 1150361 = 862771) B862771
theorem B500543 : Blo 99781 500543 := bstep (se 1 (by rfl) ⟨375407, by rfl⟩ : syracuseStep 500543 = 750815) B750815
theorem B438119 : Blo 99781 438119 := bstep (se 1 (by rfl) ⟨328589, by rfl⟩ : syracuseStep 438119 = 657179) B657179
theorem B508355 : Blo 99781 508355 := bstep (se 1 (by rfl) ⟨381266, by rfl⟩ : syracuseStep 508355 = 762533) B762533
theorem B1033631 : Blo 99781 1033631 := bstep (se 1 (by rfl) ⟨775223, by rfl⟩ : syracuseStep 1033631 = 1550447) B1550447
theorem B345599 : Blo 99781 345599 := bstep (se 1 (by rfl) ⟨259199, by rfl⟩ : syracuseStep 345599 = 518399) B518399
theorem B152047 : Blo 99781 152047 := bstep (se 1 (by rfl) ⟨114035, by rfl⟩ : syracuseStep 152047 = 228071) B228071
theorem B4216931 : Blo 99781 4216931 := bstep (se 1 (by rfl) ⟨3162698, by rfl⟩ : syracuseStep 4216931 = 6325397) B6325397
theorem B253631 : Blo 99781 253631 := bstep (se 1 (by rfl) ⟨190223, by rfl⟩ : syracuseStep 253631 = 380447) B380447
theorem B260455 : Blo 99781 260455 := bstep (se 1 (by rfl) ⟨195341, by rfl⟩ : syracuseStep 260455 = 390683) B390683
theorem B689087 : Blo 99781 689087 := bstep (se 1 (by rfl) ⟨516815, by rfl⟩ : syracuseStep 689087 = 1033631) B1033631
theorem B230399 : Blo 99781 230399 := bstep (se 1 (by rfl) ⟨172799, by rfl⟩ : syracuseStep 230399 = 345599) B345599
theorem B169087 : Blo 99781 169087 := bstep (se 1 (by rfl) ⟨126815, by rfl⟩ : syracuseStep 169087 = 253631) B253631
theorem B333695 : Blo 99781 333695 := bstep (se 1 (by rfl) ⟨250271, by rfl⟩ : syracuseStep 333695 = 500543) B500543
theorem B338903 : Blo 99781 338903 := bstep (se 1 (by rfl) ⟨254177, by rfl⟩ : syracuseStep 338903 = 508355) B508355
theorem B766907 : Blo 99781 766907 := bstep (se 1 (by rfl) ⟨575180, by rfl⟩ : syracuseStep 766907 = 1150361) B1150361
theorem B347273 : Blo 99781 347273 := bstep (se 2 (by rfl) ⟨130227, by rfl⟩ : syracuseStep 347273 = 260455) B260455
theorem B810917 : Blo 99781 810917 := bstep (se 4 (by rfl) ⟨76023, by rfl⟩ : syracuseStep 810917 = 152047) B152047
theorem B2811287 : Blo 99781 2811287 := bstep (se 1 (by rfl) ⟨2108465, by rfl⟩ : syracuseStep 2811287 = 4216931) B4216931
theorem B292079 : Blo 99781 292079 := bstep (se 1 (by rfl) ⟨219059, by rfl⟩ : syracuseStep 292079 = 438119) B438119
theorem B459391 : Blo 99781 459391 := bstep (se 1 (by rfl) ⟨344543, by rfl⟩ : syracuseStep 459391 = 689087) B689087
theorem B231515 : Blo 99781 231515 := bstep (se 1 (by rfl) ⟨173636, by rfl⟩ : syracuseStep 231515 = 347273) B347273
theorem B1874191 : Blo 99781 1874191 := bstep (se 1 (by rfl) ⟨1405643, by rfl⟩ : syracuseStep 1874191 = 2811287) B2811287
theorem B540611 : Blo 99781 540611 := bstep (se 1 (by rfl) ⟨405458, by rfl⟩ : syracuseStep 540611 = 810917) B810917
theorem B511271 : Blo 99781 511271 := bstep (se 1 (by rfl) ⟨383453, by rfl⟩ : syracuseStep 511271 = 766907) B766907
theorem B153599 : Blo 99781 153599 := bstep (se 1 (by rfl) ⟨115199, by rfl⟩ : syracuseStep 153599 = 230399) B230399
theorem B222463 : Blo 99781 222463 := bstep (se 1 (by rfl) ⟨166847, by rfl⟩ : syracuseStep 222463 = 333695) B333695
theorem B225449 : Blo 99781 225449 := bstep (se 2 (by rfl) ⟨84543, by rfl⟩ : syracuseStep 225449 = 169087) B169087
theorem B225935 : Blo 99781 225935 := bstep (se 1 (by rfl) ⟨169451, by rfl⟩ : syracuseStep 225935 = 338903) B338903
theorem B194719 : Blo 99781 194719 := bstep (se 1 (by rfl) ⟨146039, by rfl⟩ : syracuseStep 194719 = 292079) B292079
theorem B296617 : Blo 99781 296617 := bstep (se 2 (by rfl) ⟨111231, by rfl⟩ : syracuseStep 296617 = 222463) B222463
theorem B102399 : Blo 99781 102399 := bstep (se 1 (by rfl) ⟨76799, by rfl⟩ : syracuseStep 102399 = 153599) B153599
theorem B2498921 : Blo 99781 2498921 := bstep (se 2 (by rfl) ⟨937095, by rfl⟩ : syracuseStep 2498921 = 1874191) B1874191
theorem B340847 : Blo 99781 340847 := bstep (se 1 (by rfl) ⟨255635, by rfl⟩ : syracuseStep 340847 = 511271) B511271
theorem B150299 : Blo 99781 150299 := bstep (se 1 (by rfl) ⟨112724, by rfl⟩ : syracuseStep 150299 = 225449) B225449
theorem B150623 : Blo 99781 150623 := bstep (se 1 (by rfl) ⟨112967, by rfl⟩ : syracuseStep 150623 = 225935) B225935
theorem B612521 : Blo 99781 612521 := bstep (se 2 (by rfl) ⟨229695, by rfl⟩ : syracuseStep 612521 = 459391) B459391
theorem B154343 : Blo 99781 154343 := bstep (se 1 (by rfl) ⟨115757, by rfl⟩ : syracuseStep 154343 = 231515) B231515
theorem B259625 : Blo 99781 259625 := bstep (se 2 (by rfl) ⟨97359, by rfl⟩ : syracuseStep 259625 = 194719) B194719
theorem B360407 : Blo 99781 360407 := bstep (se 1 (by rfl) ⟨270305, by rfl⟩ : syracuseStep 360407 = 540611) B540611
theorem B100199 : Blo 99781 100199 := bstep (se 1 (by rfl) ⟨75149, by rfl⟩ : syracuseStep 100199 = 150299) B150299
theorem B100415 : Blo 99781 100415 := bstep (se 1 (by rfl) ⟨75311, by rfl⟩ : syracuseStep 100415 = 150623) B150623
theorem B395489 : Blo 99781 395489 := bstep (se 2 (by rfl) ⟨148308, by rfl⟩ : syracuseStep 395489 = 296617) B296617
theorem B102895 : Blo 99781 102895 := bstep (se 1 (by rfl) ⟨77171, by rfl⟩ : syracuseStep 102895 = 154343) B154343
theorem B173083 : Blo 99781 173083 := bstep (se 1 (by rfl) ⟨129812, by rfl⟩ : syracuseStep 173083 = 259625) B259625
theorem B961085 : Blo 99781 961085 := bstep (se 3 (by rfl) ⟨180203, by rfl⟩ : syracuseStep 961085 = 360407) B360407
theorem B408347 : Blo 99781 408347 := bstep (se 1 (by rfl) ⟨306260, by rfl⟩ : syracuseStep 408347 = 612521) B612521
theorem B1665947 : Blo 99781 1665947 := bstep (se 1 (by rfl) ⟨1249460, by rfl⟩ : syracuseStep 1665947 = 2498921) B2498921
theorem B227231 : Blo 99781 227231 := bstep (se 1 (by rfl) ⟨170423, by rfl⟩ : syracuseStep 227231 = 340847) B340847
theorem B230777 : Blo 99781 230777 := bstep (se 2 (by rfl) ⟨86541, by rfl⟩ : syracuseStep 230777 = 173083) B173083
theorem B1054637 : Blo 99781 1054637 := bstep (se 3 (by rfl) ⟨197744, by rfl⟩ : syracuseStep 1054637 = 395489) B395489
theorem B272231 : Blo 99781 272231 := bstep (se 1 (by rfl) ⟨204173, by rfl⟩ : syracuseStep 272231 = 408347) B408347
theorem B640723 : Blo 99781 640723 := bstep (se 1 (by rfl) ⟨480542, by rfl⟩ : syracuseStep 640723 = 961085) B961085
theorem B151487 : Blo 99781 151487 := bstep (se 1 (by rfl) ⟨113615, by rfl⟩ : syracuseStep 151487 = 227231) B227231
theorem B1110631 : Blo 99781 1110631 := bstep (se 1 (by rfl) ⟨832973, by rfl⟩ : syracuseStep 1110631 = 1665947) B1665947
theorem B854297 : Blo 99781 854297 := bstep (se 2 (by rfl) ⟨320361, by rfl⟩ : syracuseStep 854297 = 640723) B640723
theorem B100991 : Blo 99781 100991 := bstep (se 1 (by rfl) ⟨75743, by rfl⟩ : syracuseStep 100991 = 151487) B151487
theorem B1480841 : Blo 99781 1480841 := bstep (se 2 (by rfl) ⟨555315, by rfl⟩ : syracuseStep 1480841 = 1110631) B1110631
theorem B703091 : Blo 99781 703091 := bstep (se 1 (by rfl) ⟨527318, by rfl⟩ : syracuseStep 703091 = 1054637) B1054637
theorem B181487 : Blo 99781 181487 := bstep (se 1 (by rfl) ⟨136115, by rfl⟩ : syracuseStep 181487 = 272231) B272231
theorem B153851 : Blo 99781 153851 := bstep (se 1 (by rfl) ⟨115388, by rfl⟩ : syracuseStep 153851 = 230777) B230777
theorem B987227 : Blo 99781 987227 := bstep (se 1 (by rfl) ⟨740420, by rfl⟩ : syracuseStep 987227 = 1480841) B1480841
theorem B102567 : Blo 99781 102567 := bstep (se 1 (by rfl) ⟨76925, by rfl⟩ : syracuseStep 102567 = 153851) B153851
theorem B1874909 : Blo 99781 1874909 := bstep (se 3 (by rfl) ⟨351545, by rfl⟩ : syracuseStep 1874909 = 703091) B703091
theorem B569531 : Blo 99781 569531 := bstep (se 1 (by rfl) ⟨427148, by rfl⟩ : syracuseStep 569531 = 854297) B854297
theorem B483965 : Blo 99781 483965 := bstep (se 3 (by rfl) ⟨90743, by rfl⟩ : syracuseStep 483965 = 181487) B181487
theorem B658151 : Blo 99781 658151 := bstep (se 1 (by rfl) ⟨493613, by rfl⟩ : syracuseStep 658151 = 987227) B987227
theorem B1249939 : Blo 99781 1249939 := bstep (se 1 (by rfl) ⟨937454, by rfl⟩ : syracuseStep 1249939 = 1874909) B1874909
theorem B379687 : Blo 99781 379687 := bstep (se 1 (by rfl) ⟨284765, by rfl⟩ : syracuseStep 379687 = 569531) B569531
theorem B322643 : Blo 99781 322643 := bstep (se 1 (by rfl) ⟨241982, by rfl⟩ : syracuseStep 322643 = 483965) B483965
theorem B860381 : Blo 99781 860381 := bstep (se 3 (by rfl) ⟨161321, by rfl⟩ : syracuseStep 860381 = 322643) B322643
theorem B438767 : Blo 99781 438767 := bstep (se 1 (by rfl) ⟨329075, by rfl⟩ : syracuseStep 438767 = 658151) B658151
theorem B506249 : Blo 99781 506249 := bstep (se 2 (by rfl) ⟨189843, by rfl⟩ : syracuseStep 506249 = 379687) B379687
theorem B1666585 : Blo 99781 1666585 := bstep (se 2 (by rfl) ⟨624969, by rfl⟩ : syracuseStep 1666585 = 1249939) B1249939
theorem B337499 : Blo 99781 337499 := bstep (se 1 (by rfl) ⟨253124, by rfl⟩ : syracuseStep 337499 = 506249) B506249
theorem B573587 : Blo 99781 573587 := bstep (se 1 (by rfl) ⟨430190, by rfl⟩ : syracuseStep 573587 = 860381) B860381
theorem B2222113 : Blo 99781 2222113 := bstep (se 2 (by rfl) ⟨833292, by rfl⟩ : syracuseStep 2222113 = 1666585) B1666585
theorem B292511 : Blo 99781 292511 := bstep (se 1 (by rfl) ⟨219383, by rfl⟩ : syracuseStep 292511 = 438767) B438767
theorem B2962817 : Blo 99781 2962817 := bstep (se 2 (by rfl) ⟨1111056, by rfl⟩ : syracuseStep 2962817 = 2222113) B2222113
theorem B382391 : Blo 99781 382391 := bstep (se 1 (by rfl) ⟨286793, by rfl⟩ : syracuseStep 382391 = 573587) B573587
theorem B780029 : Blo 99781 780029 := bstep (se 3 (by rfl) ⟨146255, by rfl⟩ : syracuseStep 780029 = 292511) B292511
theorem B224999 : Blo 99781 224999 := bstep (se 1 (by rfl) ⟨168749, by rfl⟩ : syracuseStep 224999 = 337499) B337499
theorem B1975211 : Blo 99781 1975211 := bstep (se 1 (by rfl) ⟨1481408, by rfl⟩ : syracuseStep 1975211 = 2962817) B2962817
theorem B149999 : Blo 99781 149999 := bstep (se 1 (by rfl) ⟨112499, by rfl⟩ : syracuseStep 149999 = 224999) B224999
theorem B254927 : Blo 99781 254927 := bstep (se 1 (by rfl) ⟨191195, by rfl⟩ : syracuseStep 254927 = 382391) B382391
theorem B520019 : Blo 99781 520019 := bstep (se 1 (by rfl) ⟨390014, by rfl⟩ : syracuseStep 520019 = 780029) B780029
theorem B99999 : Blo 99781 99999 := bstep (se 1 (by rfl) ⟨74999, by rfl⟩ : syracuseStep 99999 = 149999) B149999
theorem B1316807 : Blo 99781 1316807 := bstep (se 1 (by rfl) ⟨987605, by rfl⟩ : syracuseStep 1316807 = 1975211) B1975211
theorem B169951 : Blo 99781 169951 := bstep (se 1 (by rfl) ⟨127463, by rfl⟩ : syracuseStep 169951 = 254927) B254927
theorem B346679 : Blo 99781 346679 := bstep (se 1 (by rfl) ⟨260009, by rfl⟩ : syracuseStep 346679 = 520019) B520019
theorem B231119 : Blo 99781 231119 := bstep (se 1 (by rfl) ⟨173339, by rfl⟩ : syracuseStep 231119 = 346679) B346679
theorem B877871 : Blo 99781 877871 := bstep (se 1 (by rfl) ⟨658403, by rfl⟩ : syracuseStep 877871 = 1316807) B1316807
theorem B226601 : Blo 99781 226601 := bstep (se 2 (by rfl) ⟨84975, by rfl⟩ : syracuseStep 226601 = 169951) B169951
theorem B151067 : Blo 99781 151067 := bstep (se 1 (by rfl) ⟨113300, by rfl⟩ : syracuseStep 151067 = 226601) B226601
theorem B154079 : Blo 99781 154079 := bstep (se 1 (by rfl) ⟨115559, by rfl⟩ : syracuseStep 154079 = 231119) B231119
theorem B585247 : Blo 99781 585247 := bstep (se 1 (by rfl) ⟨438935, by rfl⟩ : syracuseStep 585247 = 877871) B877871
theorem B100711 : Blo 99781 100711 := bstep (se 1 (by rfl) ⟨75533, by rfl⟩ : syracuseStep 100711 = 151067) B151067
theorem B102719 : Blo 99781 102719 := bstep (se 1 (by rfl) ⟨77039, by rfl⟩ : syracuseStep 102719 = 154079) B154079
theorem B780329 : Blo 99781 780329 := bstep (se 2 (by rfl) ⟨292623, by rfl⟩ : syracuseStep 780329 = 585247) B585247
theorem B520219 : Blo 99781 520219 := bstep (se 1 (by rfl) ⟨390164, by rfl⟩ : syracuseStep 520219 = 780329) B780329
theorem B693625 : Blo 99781 693625 := bstep (se 2 (by rfl) ⟨260109, by rfl⟩ : syracuseStep 693625 = 520219) B520219
theorem B924833 : Blo 99781 924833 := bstep (se 2 (by rfl) ⟨346812, by rfl⟩ : syracuseStep 924833 = 693625) B693625
theorem B616555 : Blo 99781 616555 := bstep (se 1 (by rfl) ⟨462416, by rfl⟩ : syracuseStep 616555 = 924833) B924833
theorem B822073 : Blo 99781 822073 := bstep (se 2 (by rfl) ⟨308277, by rfl⟩ : syracuseStep 822073 = 616555) B616555
theorem B1096097 : Blo 99781 1096097 := bstep (se 2 (by rfl) ⟨411036, by rfl⟩ : syracuseStep 1096097 = 822073) B822073
theorem B2922925 : Blo 99781 2922925 := bstep (se 3 (by rfl) ⟨548048, by rfl⟩ : syracuseStep 2922925 = 1096097) B1096097
theorem B3897233 : Blo 99781 3897233 := bstep (se 2 (by rfl) ⟨1461462, by rfl⟩ : syracuseStep 3897233 = 2922925) B2922925
theorem B2598155 : Blo 99781 2598155 := bstep (se 1 (by rfl) ⟨1948616, by rfl⟩ : syracuseStep 2598155 = 3897233) B3897233
theorem B1732103 : Blo 99781 1732103 := bstep (se 1 (by rfl) ⟨1299077, by rfl⟩ : syracuseStep 1732103 = 2598155) B2598155
theorem B1154735 : Blo 99781 1154735 := bstep (se 1 (by rfl) ⟨866051, by rfl⟩ : syracuseStep 1154735 = 1732103) B1732103
theorem B769823 : Blo 99781 769823 := bstep (se 1 (by rfl) ⟨577367, by rfl⟩ : syracuseStep 769823 = 1154735) B1154735
theorem B513215 : Blo 99781 513215 := bstep (se 1 (by rfl) ⟨384911, by rfl⟩ : syracuseStep 513215 = 769823) B769823
theorem B342143 : Blo 99781 342143 := bstep (se 1 (by rfl) ⟨256607, by rfl⟩ : syracuseStep 342143 = 513215) B513215
theorem B228095 : Blo 99781 228095 := bstep (se 1 (by rfl) ⟨171071, by rfl⟩ : syracuseStep 228095 = 342143) B342143
theorem B152063 : Blo 99781 152063 := bstep (se 1 (by rfl) ⟨114047, by rfl⟩ : syracuseStep 152063 = 228095) B228095
theorem B101375 : Blo 99781 101375 := bstep (se 1 (by rfl) ⟨76031, by rfl⟩ : syracuseStep 101375 = 152063) B152063

theorem C0 (j : ℕ) (h1 : 24945 ≤ j) (h2 : j ≤ 25644) : Blo 99781 (4 * j + 3) := by
  interval_cases j
  · exact B99783
  · exact B99787
  · exact B99791
  · exact B99795
  · exact B99799
  · exact B99803
  · exact B99807
  · exact B99811
  · exact B99815
  · exact B99819
  · exact B99823
  · exact B99827
  · exact B99831
  · exact B99835
  · exact B99839
  · exact B99843
  · exact B99847
  · exact B99851
  · exact B99855
  · exact B99859
  · exact B99863
  · exact B99867
  · exact B99871
  · exact B99875
  · exact B99879
  · exact B99883
  · exact B99887
  · exact B99891
  · exact B99895
  · exact B99899
  · exact B99903
  · exact B99907
  · exact B99911
  · exact B99915
  · exact B99919
  · exact B99923
  · exact B99927
  · exact B99931
  · exact B99935
  · exact B99939
  · exact B99943
  · exact B99947
  · exact B99951
  · exact B99955
  · exact B99959
  · exact B99963
  · exact B99967
  · exact B99971
  · exact B99975
  · exact B99979
  · exact B99983
  · exact B99987
  · exact B99991
  · exact B99995
  · exact B99999
  · exact B100003
  · exact B100007
  · exact B100011
  · exact B100015
  · exact B100019
  · exact B100023
  · exact B100027
  · exact B100031
  · exact B100035
  · exact B100039
  · exact B100043
  · exact B100047
  · exact B100051
  · exact B100055
  · exact B100059
  · exact B100063
  · exact B100067
  · exact B100071
  · exact B100075
  · exact B100079
  · exact B100083
  · exact B100087
  · exact B100091
  · exact B100095
  · exact B100099
  · exact B100103
  · exact B100107
  · exact B100111
  · exact B100115
  · exact B100119
  · exact B100123
  · exact B100127
  · exact B100131
  · exact B100135
  · exact B100139
  · exact B100143
  · exact B100147
  · exact B100151
  · exact B100155
  · exact B100159
  · exact B100163
  · exact B100167
  · exact B100171
  · exact B100175
  · exact B100179
  · exact B100183
  · exact B100187
  · exact B100191
  · exact B100195
  · exact B100199
  · exact B100203
  · exact B100207
  · exact B100211
  · exact B100215
  · exact B100219
  · exact B100223
  · exact B100227
  · exact B100231
  · exact B100235
  · exact B100239
  · exact B100243
  · exact B100247
  · exact B100251
  · exact B100255
  · exact B100259
  · exact B100263
  · exact B100267
  · exact B100271
  · exact B100275
  · exact B100279
  · exact B100283
  · exact B100287
  · exact B100291
  · exact B100295
  · exact B100299
  · exact B100303
  · exact B100307
  · exact B100311
  · exact B100315
  · exact B100319
  · exact B100323
  · exact B100327
  · exact B100331
  · exact B100335
  · exact B100339
  · exact B100343
  · exact B100347
  · exact B100351
  · exact B100355
  · exact B100359
  · exact B100363
  · exact B100367
  · exact B100371
  · exact B100375
  · exact B100379
  · exact B100383
  · exact B100387
  · exact B100391
  · exact B100395
  · exact B100399
  · exact B100403
  · exact B100407
  · exact B100411
  · exact B100415
  · exact B100419
  · exact B100423
  · exact B100427
  · exact B100431
  · exact B100435
  · exact B100439
  · exact B100443
  · exact B100447
  · exact B100451
  · exact B100455
  · exact B100459
  · exact B100463
  · exact B100467
  · exact B100471
  · exact B100475
  · exact B100479
  · exact B100483
  · exact B100487
  · exact B100491
  · exact B100495
  · exact B100499
  · exact B100503
  · exact B100507
  · exact B100511
  · exact B100515
  · exact B100519
  · exact B100523
  · exact B100527
  · exact B100531
  · exact B100535
  · exact B100539
  · exact B100543
  · exact B100547
  · exact B100551
  · exact B100555
  · exact B100559
  · exact B100563
  · exact B100567
  · exact B100571
  · exact B100575
  · exact B100579
  · exact B100583
  · exact B100587
  · exact B100591
  · exact B100595
  · exact B100599
  · exact B100603
  · exact B100607
  · exact B100611
  · exact B100615
  · exact B100619
  · exact B100623
  · exact B100627
  · exact B100631
  · exact B100635
  · exact B100639
  · exact B100643
  · exact B100647
  · exact B100651
  · exact B100655
  · exact B100659
  · exact B100663
  · exact B100667
  · exact B100671
  · exact B100675
  · exact B100679
  · exact B100683
  · exact B100687
  · exact B100691
  · exact B100695
  · exact B100699
  · exact B100703
  · exact B100707
  · exact B100711
  · exact B100715
  · exact B100719
  · exact B100723
  · exact B100727
  · exact B100731
  · exact B100735
  · exact B100739
  · exact B100743
  · exact B100747
  · exact B100751
  · exact B100755
  · exact B100759
  · exact B100763
  · exact B100767
  · exact B100771
  · exact B100775
  · exact B100779
  · exact B100783
  · exact B100787
  · exact B100791
  · exact B100795
  · exact B100799
  · exact B100803
  · exact B100807
  · exact B100811
  · exact B100815
  · exact B100819
  · exact B100823
  · exact B100827
  · exact B100831
  · exact B100835
  · exact B100839
  · exact B100843
  · exact B100847
  · exact B100851
  · exact B100855
  · exact B100859
  · exact B100863
  · exact B100867
  · exact B100871
  · exact B100875
  · exact B100879
  · exact B100883
  · exact B100887
  · exact B100891
  · exact B100895
  · exact B100899
  · exact B100903
  · exact B100907
  · exact B100911
  · exact B100915
  · exact B100919
  · exact B100923
  · exact B100927
  · exact B100931
  · exact B100935
  · exact B100939
  · exact B100943
  · exact B100947
  · exact B100951
  · exact B100955
  · exact B100959
  · exact B100963
  · exact B100967
  · exact B100971
  · exact B100975
  · exact B100979
  · exact B100983
  · exact B100987
  · exact B100991
  · exact B100995
  · exact B100999
  · exact B101003
  · exact B101007
  · exact B101011
  · exact B101015
  · exact B101019
  · exact B101023
  · exact B101027
  · exact B101031
  · exact B101035
  · exact B101039
  · exact B101043
  · exact B101047
  · exact B101051
  · exact B101055
  · exact B101059
  · exact B101063
  · exact B101067
  · exact B101071
  · exact B101075
  · exact B101079
  · exact B101083
  · exact B101087
  · exact B101091
  · exact B101095
  · exact B101099
  · exact B101103
  · exact B101107
  · exact B101111
  · exact B101115
  · exact B101119
  · exact B101123
  · exact B101127
  · exact B101131
  · exact B101135
  · exact B101139
  · exact B101143
  · exact B101147
  · exact B101151
  · exact B101155
  · exact B101159
  · exact B101163
  · exact B101167
  · exact B101171
  · exact B101175
  · exact B101179
  · exact B101183
  · exact B101187
  · exact B101191
  · exact B101195
  · exact B101199
  · exact B101203
  · exact B101207
  · exact B101211
  · exact B101215
  · exact B101219
  · exact B101223
  · exact B101227
  · exact B101231
  · exact B101235
  · exact B101239
  · exact B101243
  · exact B101247
  · exact B101251
  · exact B101255
  · exact B101259
  · exact B101263
  · exact B101267
  · exact B101271
  · exact B101275
  · exact B101279
  · exact B101283
  · exact B101287
  · exact B101291
  · exact B101295
  · exact B101299
  · exact B101303
  · exact B101307
  · exact B101311
  · exact B101315
  · exact B101319
  · exact B101323
  · exact B101327
  · exact B101331
  · exact B101335
  · exact B101339
  · exact B101343
  · exact B101347
  · exact B101351
  · exact B101355
  · exact B101359
  · exact B101363
  · exact B101367
  · exact B101371
  · exact B101375
  · exact B101379
  · exact B101383
  · exact B101387
  · exact B101391
  · exact B101395
  · exact B101399
  · exact B101403
  · exact B101407
  · exact B101411
  · exact B101415
  · exact B101419
  · exact B101423
  · exact B101427
  · exact B101431
  · exact B101435
  · exact B101439
  · exact B101443
  · exact B101447
  · exact B101451
  · exact B101455
  · exact B101459
  · exact B101463
  · exact B101467
  · exact B101471
  · exact B101475
  · exact B101479
  · exact B101483
  · exact B101487
  · exact B101491
  · exact B101495
  · exact B101499
  · exact B101503
  · exact B101507
  · exact B101511
  · exact B101515
  · exact B101519
  · exact B101523
  · exact B101527
  · exact B101531
  · exact B101535
  · exact B101539
  · exact B101543
  · exact B101547
  · exact B101551
  · exact B101555
  · exact B101559
  · exact B101563
  · exact B101567
  · exact B101571
  · exact B101575
  · exact B101579
  · exact B101583
  · exact B101587
  · exact B101591
  · exact B101595
  · exact B101599
  · exact B101603
  · exact B101607
  · exact B101611
  · exact B101615
  · exact B101619
  · exact B101623
  · exact B101627
  · exact B101631
  · exact B101635
  · exact B101639
  · exact B101643
  · exact B101647
  · exact B101651
  · exact B101655
  · exact B101659
  · exact B101663
  · exact B101667
  · exact B101671
  · exact B101675
  · exact B101679
  · exact B101683
  · exact B101687
  · exact B101691
  · exact B101695
  · exact B101699
  · exact B101703
  · exact B101707
  · exact B101711
  · exact B101715
  · exact B101719
  · exact B101723
  · exact B101727
  · exact B101731
  · exact B101735
  · exact B101739
  · exact B101743
  · exact B101747
  · exact B101751
  · exact B101755
  · exact B101759
  · exact B101763
  · exact B101767
  · exact B101771
  · exact B101775
  · exact B101779
  · exact B101783
  · exact B101787
  · exact B101791
  · exact B101795
  · exact B101799
  · exact B101803
  · exact B101807
  · exact B101811
  · exact B101815
  · exact B101819
  · exact B101823
  · exact B101827
  · exact B101831
  · exact B101835
  · exact B101839
  · exact B101843
  · exact B101847
  · exact B101851
  · exact B101855
  · exact B101859
  · exact B101863
  · exact B101867
  · exact B101871
  · exact B101875
  · exact B101879
  · exact B101883
  · exact B101887
  · exact B101891
  · exact B101895
  · exact B101899
  · exact B101903
  · exact B101907
  · exact B101911
  · exact B101915
  · exact B101919
  · exact B101923
  · exact B101927
  · exact B101931
  · exact B101935
  · exact B101939
  · exact B101943
  · exact B101947
  · exact B101951
  · exact B101955
  · exact B101959
  · exact B101963
  · exact B101967
  · exact B101971
  · exact B101975
  · exact B101979
  · exact B101983
  · exact B101987
  · exact B101991
  · exact B101995
  · exact B101999
  · exact B102003
  · exact B102007
  · exact B102011
  · exact B102015
  · exact B102019
  · exact B102023
  · exact B102027
  · exact B102031
  · exact B102035
  · exact B102039
  · exact B102043
  · exact B102047
  · exact B102051
  · exact B102055
  · exact B102059
  · exact B102063
  · exact B102067
  · exact B102071
  · exact B102075
  · exact B102079
  · exact B102083
  · exact B102087
  · exact B102091
  · exact B102095
  · exact B102099
  · exact B102103
  · exact B102107
  · exact B102111
  · exact B102115
  · exact B102119
  · exact B102123
  · exact B102127
  · exact B102131
  · exact B102135
  · exact B102139
  · exact B102143
  · exact B102147
  · exact B102151
  · exact B102155
  · exact B102159
  · exact B102163
  · exact B102167
  · exact B102171
  · exact B102175
  · exact B102179
  · exact B102183
  · exact B102187
  · exact B102191
  · exact B102195
  · exact B102199
  · exact B102203
  · exact B102207
  · exact B102211
  · exact B102215
  · exact B102219
  · exact B102223
  · exact B102227
  · exact B102231
  · exact B102235
  · exact B102239
  · exact B102243
  · exact B102247
  · exact B102251
  · exact B102255
  · exact B102259
  · exact B102263
  · exact B102267
  · exact B102271
  · exact B102275
  · exact B102279
  · exact B102283
  · exact B102287
  · exact B102291
  · exact B102295
  · exact B102299
  · exact B102303
  · exact B102307
  · exact B102311
  · exact B102315
  · exact B102319
  · exact B102323
  · exact B102327
  · exact B102331
  · exact B102335
  · exact B102339
  · exact B102343
  · exact B102347
  · exact B102351
  · exact B102355
  · exact B102359
  · exact B102363
  · exact B102367
  · exact B102371
  · exact B102375
  · exact B102379
  · exact B102383
  · exact B102387
  · exact B102391
  · exact B102395
  · exact B102399
  · exact B102403
  · exact B102407
  · exact B102411
  · exact B102415
  · exact B102419
  · exact B102423
  · exact B102427
  · exact B102431
  · exact B102435
  · exact B102439
  · exact B102443
  · exact B102447
  · exact B102451
  · exact B102455
  · exact B102459
  · exact B102463
  · exact B102467
  · exact B102471
  · exact B102475
  · exact B102479
  · exact B102483
  · exact B102487
  · exact B102491
  · exact B102495
  · exact B102499
  · exact B102503
  · exact B102507
  · exact B102511
  · exact B102515
  · exact B102519
  · exact B102523
  · exact B102527
  · exact B102531
  · exact B102535
  · exact B102539
  · exact B102543
  · exact B102547
  · exact B102551
  · exact B102555
  · exact B102559
  · exact B102563
  · exact B102567
  · exact B102571
  · exact B102575
  · exact B102579

theorem C1 (j : ℕ) (h1 : 25645 ≤ j) (h2 : j ≤ 25944) : Blo 99781 (4 * j + 3) := by
  interval_cases j
  · exact B102583
  · exact B102587
  · exact B102591
  · exact B102595
  · exact B102599
  · exact B102603
  · exact B102607
  · exact B102611
  · exact B102615
  · exact B102619
  · exact B102623
  · exact B102627
  · exact B102631
  · exact B102635
  · exact B102639
  · exact B102643
  · exact B102647
  · exact B102651
  · exact B102655
  · exact B102659
  · exact B102663
  · exact B102667
  · exact B102671
  · exact B102675
  · exact B102679
  · exact B102683
  · exact B102687
  · exact B102691
  · exact B102695
  · exact B102699
  · exact B102703
  · exact B102707
  · exact B102711
  · exact B102715
  · exact B102719
  · exact B102723
  · exact B102727
  · exact B102731
  · exact B102735
  · exact B102739
  · exact B102743
  · exact B102747
  · exact B102751
  · exact B102755
  · exact B102759
  · exact B102763
  · exact B102767
  · exact B102771
  · exact B102775
  · exact B102779
  · exact B102783
  · exact B102787
  · exact B102791
  · exact B102795
  · exact B102799
  · exact B102803
  · exact B102807
  · exact B102811
  · exact B102815
  · exact B102819
  · exact B102823
  · exact B102827
  · exact B102831
  · exact B102835
  · exact B102839
  · exact B102843
  · exact B102847
  · exact B102851
  · exact B102855
  · exact B102859
  · exact B102863
  · exact B102867
  · exact B102871
  · exact B102875
  · exact B102879
  · exact B102883
  · exact B102887
  · exact B102891
  · exact B102895
  · exact B102899
  · exact B102903
  · exact B102907
  · exact B102911
  · exact B102915
  · exact B102919
  · exact B102923
  · exact B102927
  · exact B102931
  · exact B102935
  · exact B102939
  · exact B102943
  · exact B102947
  · exact B102951
  · exact B102955
  · exact B102959
  · exact B102963
  · exact B102967
  · exact B102971
  · exact B102975
  · exact B102979
  · exact B102983
  · exact B102987
  · exact B102991
  · exact B102995
  · exact B102999
  · exact B103003
  · exact B103007
  · exact B103011
  · exact B103015
  · exact B103019
  · exact B103023
  · exact B103027
  · exact B103031
  · exact B103035
  · exact B103039
  · exact B103043
  · exact B103047
  · exact B103051
  · exact B103055
  · exact B103059
  · exact B103063
  · exact B103067
  · exact B103071
  · exact B103075
  · exact B103079
  · exact B103083
  · exact B103087
  · exact B103091
  · exact B103095
  · exact B103099
  · exact B103103
  · exact B103107
  · exact B103111
  · exact B103115
  · exact B103119
  · exact B103123
  · exact B103127
  · exact B103131
  · exact B103135
  · exact B103139
  · exact B103143
  · exact B103147
  · exact B103151
  · exact B103155
  · exact B103159
  · exact B103163
  · exact B103167
  · exact B103171
  · exact B103175
  · exact B103179
  · exact B103183
  · exact B103187
  · exact B103191
  · exact B103195
  · exact B103199
  · exact B103203
  · exact B103207
  · exact B103211
  · exact B103215
  · exact B103219
  · exact B103223
  · exact B103227
  · exact B103231
  · exact B103235
  · exact B103239
  · exact B103243
  · exact B103247
  · exact B103251
  · exact B103255
  · exact B103259
  · exact B103263
  · exact B103267
  · exact B103271
  · exact B103275
  · exact B103279
  · exact B103283
  · exact B103287
  · exact B103291
  · exact B103295
  · exact B103299
  · exact B103303
  · exact B103307
  · exact B103311
  · exact B103315
  · exact B103319
  · exact B103323
  · exact B103327
  · exact B103331
  · exact B103335
  · exact B103339
  · exact B103343
  · exact B103347
  · exact B103351
  · exact B103355
  · exact B103359
  · exact B103363
  · exact B103367
  · exact B103371
  · exact B103375
  · exact B103379
  · exact B103383
  · exact B103387
  · exact B103391
  · exact B103395
  · exact B103399
  · exact B103403
  · exact B103407
  · exact B103411
  · exact B103415
  · exact B103419
  · exact B103423
  · exact B103427
  · exact B103431
  · exact B103435
  · exact B103439
  · exact B103443
  · exact B103447
  · exact B103451
  · exact B103455
  · exact B103459
  · exact B103463
  · exact B103467
  · exact B103471
  · exact B103475
  · exact B103479
  · exact B103483
  · exact B103487
  · exact B103491
  · exact B103495
  · exact B103499
  · exact B103503
  · exact B103507
  · exact B103511
  · exact B103515
  · exact B103519
  · exact B103523
  · exact B103527
  · exact B103531
  · exact B103535
  · exact B103539
  · exact B103543
  · exact B103547
  · exact B103551
  · exact B103555
  · exact B103559
  · exact B103563
  · exact B103567
  · exact B103571
  · exact B103575
  · exact B103579
  · exact B103583
  · exact B103587
  · exact B103591
  · exact B103595
  · exact B103599
  · exact B103603
  · exact B103607
  · exact B103611
  · exact B103615
  · exact B103619
  · exact B103623
  · exact B103627
  · exact B103631
  · exact B103635
  · exact B103639
  · exact B103643
  · exact B103647
  · exact B103651
  · exact B103655
  · exact B103659
  · exact B103663
  · exact B103667
  · exact B103671
  · exact B103675
  · exact B103679
  · exact B103683
  · exact B103687
  · exact B103691
  · exact B103695
  · exact B103699
  · exact B103703
  · exact B103707
  · exact B103711
  · exact B103715
  · exact B103719
  · exact B103723
  · exact B103727
  · exact B103731
  · exact B103735
  · exact B103739
  · exact B103743
  · exact B103747
  · exact B103751
  · exact B103755
  · exact B103759
  · exact B103763
  · exact B103767
  · exact B103771
  · exact B103775
  · exact B103779

theorem solution (m : ℕ) (hlo : 99781 ≤ m) (hhi : m ≤ 103781) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 24945 ≤ j := by omega
    have hj2 : j ≤ 25944 := by omega
    have hb : Blo 99781 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 25645 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
