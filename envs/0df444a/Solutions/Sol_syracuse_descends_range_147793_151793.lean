-- Prove2me | solution 1 for syracuse_descends_range_147793_151793
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:39.10274+00:00
-- url     : https://prove2.me/submissions/27dc4766-5b72-4201-b133-f188ed33fbb8

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


theorem B229421 : Blo 147793 229421 := bbase (se 3 (by rfl) ⟨43016, by rfl⟩ : syracuseStep 229421 = 86033) (by norm_num)
theorem B426181 : Blo 147793 426181 := bbase (se 4 (by rfl) ⟨39954, by rfl⟩ : syracuseStep 426181 = 79909) (by norm_num)
theorem B360821 : Blo 147793 360821 := bbase (se 5 (by rfl) ⟨16913, by rfl⟩ : syracuseStep 360821 = 33827) (by norm_num)
theorem B1147445 : Blo 147793 1147445 := bbase (se 5 (by rfl) ⟨53786, by rfl⟩ : syracuseStep 1147445 = 107573) (by norm_num)
theorem B852565 : Blo 147793 852565 := bbase (se 8 (by rfl) ⟨4995, by rfl⟩ : syracuseStep 852565 = 9991) (by norm_num)
theorem B17662805 : Blo 147793 17662805 := bbase (se 9 (by rfl) ⟨51746, by rfl⟩ : syracuseStep 17662805 = 103493) (by norm_num)
theorem B230285 : Blo 147793 230285 := bbase (se 3 (by rfl) ⟨43178, by rfl⟩ : syracuseStep 230285 = 86357) (by norm_num)
theorem B721813 : Blo 147793 721813 := bbase (se 6 (by rfl) ⟨16917, by rfl⟩ : syracuseStep 721813 = 33835) (by norm_num)
theorem B754757 : Blo 147793 754757 := bbase (se 4 (by rfl) ⟨70758, by rfl⟩ : syracuseStep 754757 = 141517) (by norm_num)
theorem B1213717 : Blo 147793 1213717 := bbase (se 6 (by rfl) ⟨28446, by rfl⟩ : syracuseStep 1213717 = 56893) (by norm_num)
theorem B427285 : Blo 147793 427285 := bbase (se 6 (by rfl) ⟨10014, by rfl⟩ : syracuseStep 427285 = 20029) (by norm_num)
theorem B460181 : Blo 147793 460181 := bbase (se 6 (by rfl) ⟨10785, by rfl⟩ : syracuseStep 460181 = 21571) (by norm_num)
theorem B1279637 : Blo 147793 1279637 := bbase (se 6 (by rfl) ⟨29991, by rfl⟩ : syracuseStep 1279637 = 59983) (by norm_num)
theorem B1640341 : Blo 147793 1640341 := bbase (se 6 (by rfl) ⟨38445, by rfl⟩ : syracuseStep 1640341 = 76891) (by norm_num)
theorem B526357 : Blo 147793 526357 := bbase (se 6 (by rfl) ⟨12336, by rfl⟩ : syracuseStep 526357 = 24673) (by norm_num)
theorem B756053 : Blo 147793 756053 := bbase (se 10 (by rfl) ⟨1107, by rfl⟩ : syracuseStep 756053 = 2215) (by norm_num)
theorem B166297 : Blo 147793 166297 := bbase (se 2 (by rfl) ⟨62361, by rfl⟩ : syracuseStep 166297 = 124723) (by norm_num)
theorem B166333 : Blo 147793 166333 := bbase (se 3 (by rfl) ⟨31187, by rfl⟩ : syracuseStep 166333 = 62375) (by norm_num)
theorem B166369 : Blo 147793 166369 := bbase (se 2 (by rfl) ⟨62388, by rfl⟩ : syracuseStep 166369 = 124777) (by norm_num)
theorem B166405 : Blo 147793 166405 := bbase (se 4 (by rfl) ⟨15600, by rfl⟩ : syracuseStep 166405 = 31201) (by norm_num)
theorem B854549 : Blo 147793 854549 := bbase (se 6 (by rfl) ⟨20028, by rfl⟩ : syracuseStep 854549 = 40057) (by norm_num)
theorem B166441 : Blo 147793 166441 := bbase (se 2 (by rfl) ⟨62415, by rfl⟩ : syracuseStep 166441 = 124831) (by norm_num)
theorem B166477 : Blo 147793 166477 := bbase (se 3 (by rfl) ⟨31214, by rfl⟩ : syracuseStep 166477 = 62429) (by norm_num)
theorem B166513 : Blo 147793 166513 := bbase (se 2 (by rfl) ⟨62442, by rfl⟩ : syracuseStep 166513 = 124885) (by norm_num)
theorem B166549 : Blo 147793 166549 := bbase (se 6 (by rfl) ⟨3903, by rfl⟩ : syracuseStep 166549 = 7807) (by norm_num)
theorem B166585 : Blo 147793 166585 := bbase (se 2 (by rfl) ⟨62469, by rfl⟩ : syracuseStep 166585 = 124939) (by norm_num)
theorem B166621 : Blo 147793 166621 := bbase (se 3 (by rfl) ⟨31241, by rfl⟩ : syracuseStep 166621 = 62483) (by norm_num)
theorem B428789 : Blo 147793 428789 := bbase (se 5 (by rfl) ⟨20099, by rfl⟩ : syracuseStep 428789 = 40199) (by norm_num)
theorem B166657 : Blo 147793 166657 := bbase (se 2 (by rfl) ⟨62496, by rfl⟩ : syracuseStep 166657 = 124993) (by norm_num)
theorem B166693 : Blo 147793 166693 := bbase (se 4 (by rfl) ⟨15627, by rfl⟩ : syracuseStep 166693 = 31255) (by norm_num)
theorem B166729 : Blo 147793 166729 := bbase (se 2 (by rfl) ⟨62523, by rfl⟩ : syracuseStep 166729 = 125047) (by norm_num)
theorem B166765 : Blo 147793 166765 := bbase (se 3 (by rfl) ⟨31268, by rfl⟩ : syracuseStep 166765 = 62537) (by norm_num)
theorem B166801 : Blo 147793 166801 := bbase (se 2 (by rfl) ⟨62550, by rfl⟩ : syracuseStep 166801 = 125101) (by norm_num)
theorem B166837 : Blo 147793 166837 := bbase (se 5 (by rfl) ⟨7820, by rfl⟩ : syracuseStep 166837 = 15641) (by norm_num)
theorem B166873 : Blo 147793 166873 := bbase (se 2 (by rfl) ⟨62577, by rfl⟩ : syracuseStep 166873 = 125155) (by norm_num)
theorem B166909 : Blo 147793 166909 := bbase (se 3 (by rfl) ⟨31295, by rfl⟩ : syracuseStep 166909 = 62591) (by norm_num)
theorem B166945 : Blo 147793 166945 := bbase (se 2 (by rfl) ⟨62604, by rfl⟩ : syracuseStep 166945 = 125209) (by norm_num)
theorem B166981 : Blo 147793 166981 := bbase (se 4 (by rfl) ⟨15654, by rfl⟩ : syracuseStep 166981 = 31309) (by norm_num)
theorem B167017 : Blo 147793 167017 := bbase (se 2 (by rfl) ⟨62631, by rfl⟩ : syracuseStep 167017 = 125263) (by norm_num)
theorem B167053 : Blo 147793 167053 := bbase (se 3 (by rfl) ⟨31322, by rfl⟩ : syracuseStep 167053 = 62645) (by norm_num)
theorem B1084565 : Blo 147793 1084565 := bbase (se 6 (by rfl) ⟨25419, by rfl⟩ : syracuseStep 1084565 = 50839) (by norm_num)
theorem B167089 : Blo 147793 167089 := bbase (se 2 (by rfl) ⟨62658, by rfl⟩ : syracuseStep 167089 = 125317) (by norm_num)
theorem B167125 : Blo 147793 167125 := bbase (se 7 (by rfl) ⟨1958, by rfl⟩ : syracuseStep 167125 = 3917) (by norm_num)
theorem B167161 : Blo 147793 167161 := bbase (se 2 (by rfl) ⟨62685, by rfl⟩ : syracuseStep 167161 = 125371) (by norm_num)
theorem B593173 : Blo 147793 593173 := bbase (se 6 (by rfl) ⟨13902, by rfl⟩ : syracuseStep 593173 = 27805) (by norm_num)
theorem B167197 : Blo 147793 167197 := bbase (se 3 (by rfl) ⟨31349, by rfl⟩ : syracuseStep 167197 = 62699) (by norm_num)
theorem B953653 : Blo 147793 953653 := bbase (se 5 (by rfl) ⟨44702, by rfl⟩ : syracuseStep 953653 = 89405) (by norm_num)
theorem B167233 : Blo 147793 167233 := bbase (se 2 (by rfl) ⟨62712, by rfl⟩ : syracuseStep 167233 = 125425) (by norm_num)
theorem B167269 : Blo 147793 167269 := bbase (se 4 (by rfl) ⟨15681, by rfl⟩ : syracuseStep 167269 = 31363) (by norm_num)
theorem B167305 : Blo 147793 167305 := bbase (se 2 (by rfl) ⟨62739, by rfl⟩ : syracuseStep 167305 = 125479) (by norm_num)
theorem B167341 : Blo 147793 167341 := bbase (se 3 (by rfl) ⟨31376, by rfl⟩ : syracuseStep 167341 = 62753) (by norm_num)
theorem B167377 : Blo 147793 167377 := bbase (se 2 (by rfl) ⟨62766, by rfl⟩ : syracuseStep 167377 = 125533) (by norm_num)
theorem B167413 : Blo 147793 167413 := bbase (se 5 (by rfl) ⟨7847, by rfl⟩ : syracuseStep 167413 = 15695) (by norm_num)
theorem B167449 : Blo 147793 167449 := bbase (se 2 (by rfl) ⟨62793, by rfl⟩ : syracuseStep 167449 = 125587) (by norm_num)
theorem B167485 : Blo 147793 167485 := bbase (se 3 (by rfl) ⟨31403, by rfl⟩ : syracuseStep 167485 = 62807) (by norm_num)
theorem B724565 : Blo 147793 724565 := bbase (se 8 (by rfl) ⟨4245, by rfl⟩ : syracuseStep 724565 = 8491) (by norm_num)
theorem B167521 : Blo 147793 167521 := bbase (se 2 (by rfl) ⟨62820, by rfl⟩ : syracuseStep 167521 = 125641) (by norm_num)
theorem B757349 : Blo 147793 757349 := bbase (se 4 (by rfl) ⟨71001, by rfl⟩ : syracuseStep 757349 = 142003) (by norm_num)
theorem B167557 : Blo 147793 167557 := bbase (se 4 (by rfl) ⟨15708, by rfl⟩ : syracuseStep 167557 = 31417) (by norm_num)
theorem B167593 : Blo 147793 167593 := bbase (se 2 (by rfl) ⟨62847, by rfl⟩ : syracuseStep 167593 = 125695) (by norm_num)
theorem B364213 : Blo 147793 364213 := bbase (se 5 (by rfl) ⟨17072, by rfl⟩ : syracuseStep 364213 = 34145) (by norm_num)
theorem B167629 : Blo 147793 167629 := bbase (se 3 (by rfl) ⟨31430, by rfl⟩ : syracuseStep 167629 = 62861) (by norm_num)
theorem B167665 : Blo 147793 167665 := bbase (se 2 (by rfl) ⟨62874, by rfl⟩ : syracuseStep 167665 = 125749) (by norm_num)
theorem B167701 : Blo 147793 167701 := bbase (se 6 (by rfl) ⟨3930, by rfl⟩ : syracuseStep 167701 = 7861) (by norm_num)
theorem B167737 : Blo 147793 167737 := bbase (se 2 (by rfl) ⟨62901, by rfl⟩ : syracuseStep 167737 = 125803) (by norm_num)
theorem B560981 : Blo 147793 560981 := bbase (se 9 (by rfl) ⟨1643, by rfl⟩ : syracuseStep 560981 = 3287) (by norm_num)
theorem B167773 : Blo 147793 167773 := bbase (se 3 (by rfl) ⟨31457, by rfl⟩ : syracuseStep 167773 = 62915) (by norm_num)
theorem B167809 : Blo 147793 167809 := bbase (se 2 (by rfl) ⟨62928, by rfl⟩ : syracuseStep 167809 = 125857) (by norm_num)
theorem B167845 : Blo 147793 167845 := bbase (se 4 (by rfl) ⟨15735, by rfl⟩ : syracuseStep 167845 = 31471) (by norm_num)
theorem B167881 : Blo 147793 167881 := bbase (se 2 (by rfl) ⟨62955, by rfl⟩ : syracuseStep 167881 = 125911) (by norm_num)
theorem B167917 : Blo 147793 167917 := bbase (se 3 (by rfl) ⟨31484, by rfl⟩ : syracuseStep 167917 = 62969) (by norm_num)
theorem B167953 : Blo 147793 167953 := bbase (se 2 (by rfl) ⟨62982, by rfl⟩ : syracuseStep 167953 = 125965) (by norm_num)
theorem B167989 : Blo 147793 167989 := bbase (se 5 (by rfl) ⟨7874, by rfl⟩ : syracuseStep 167989 = 15749) (by norm_num)
theorem B168025 : Blo 147793 168025 := bbase (se 2 (by rfl) ⟨63009, by rfl⟩ : syracuseStep 168025 = 126019) (by norm_num)
theorem B364637 : Blo 147793 364637 := bbase (se 3 (by rfl) ⟨68369, by rfl⟩ : syracuseStep 364637 = 136739) (by norm_num)
theorem B561269 : Blo 147793 561269 := bbase (se 5 (by rfl) ⟨26309, by rfl⟩ : syracuseStep 561269 = 52619) (by norm_num)
theorem B168061 : Blo 147793 168061 := bbase (se 3 (by rfl) ⟨31511, by rfl⟩ : syracuseStep 168061 = 63023) (by norm_num)
theorem B168097 : Blo 147793 168097 := bbase (se 2 (by rfl) ⟨63036, by rfl⟩ : syracuseStep 168097 = 126073) (by norm_num)
theorem B168133 : Blo 147793 168133 := bbase (se 4 (by rfl) ⟨15762, by rfl⟩ : syracuseStep 168133 = 31525) (by norm_num)
theorem B168169 : Blo 147793 168169 := bbase (se 2 (by rfl) ⟨63063, by rfl⟩ : syracuseStep 168169 = 126127) (by norm_num)
theorem B168205 : Blo 147793 168205 := bbase (se 3 (by rfl) ⟨31538, by rfl⟩ : syracuseStep 168205 = 63077) (by norm_num)
theorem B200989 : Blo 147793 200989 := bbase (se 3 (by rfl) ⟨37685, by rfl⟩ : syracuseStep 200989 = 75371) (by norm_num)
theorem B430373 : Blo 147793 430373 := bbase (se 4 (by rfl) ⟨40347, by rfl⟩ : syracuseStep 430373 = 80695) (by norm_num)
theorem B168241 : Blo 147793 168241 := bbase (se 2 (by rfl) ⟨63090, by rfl⟩ : syracuseStep 168241 = 126181) (by norm_num)
theorem B168277 : Blo 147793 168277 := bbase (se 10 (by rfl) ⟨246, by rfl⟩ : syracuseStep 168277 = 493) (by norm_num)
theorem B168313 : Blo 147793 168313 := bbase (se 2 (by rfl) ⟨63117, by rfl⟩ : syracuseStep 168313 = 126235) (by norm_num)
theorem B168349 : Blo 147793 168349 := bbase (se 3 (by rfl) ⟨31565, by rfl⟩ : syracuseStep 168349 = 63131) (by norm_num)
theorem B168385 : Blo 147793 168385 := bbase (se 2 (by rfl) ⟨63144, by rfl⟩ : syracuseStep 168385 = 126289) (by norm_num)
theorem B168421 : Blo 147793 168421 := bbase (se 4 (by rfl) ⟨15789, by rfl⟩ : syracuseStep 168421 = 31579) (by norm_num)
theorem B168457 : Blo 147793 168457 := bbase (se 2 (by rfl) ⟨63171, by rfl⟩ : syracuseStep 168457 = 126343) (by norm_num)
theorem B168493 : Blo 147793 168493 := bbase (se 3 (by rfl) ⟨31592, by rfl⟩ : syracuseStep 168493 = 63185) (by norm_num)
theorem B168529 : Blo 147793 168529 := bbase (se 2 (by rfl) ⟨63198, by rfl⟩ : syracuseStep 168529 = 126397) (by norm_num)
theorem B168565 : Blo 147793 168565 := bbase (se 5 (by rfl) ⟨7901, by rfl⟩ : syracuseStep 168565 = 15803) (by norm_num)
theorem B168601 : Blo 147793 168601 := bbase (se 2 (by rfl) ⟨63225, by rfl⟩ : syracuseStep 168601 = 126451) (by norm_num)
theorem B856757 : Blo 147793 856757 := bbase (se 5 (by rfl) ⟨40160, by rfl⟩ : syracuseStep 856757 = 80321) (by norm_num)
theorem B168637 : Blo 147793 168637 := bbase (se 3 (by rfl) ⟨31619, by rfl⟩ : syracuseStep 168637 = 63239) (by norm_num)
theorem B168673 : Blo 147793 168673 := bbase (se 2 (by rfl) ⟨63252, by rfl⟩ : syracuseStep 168673 = 126505) (by norm_num)
theorem B332549 : Blo 147793 332549 := bbase (se 4 (by rfl) ⟨31176, by rfl⟩ : syracuseStep 332549 = 62353) (by norm_num)
theorem B168709 : Blo 147793 168709 := bbase (se 4 (by rfl) ⟨15816, by rfl⟩ : syracuseStep 168709 = 31633) (by norm_num)
theorem B168745 : Blo 147793 168745 := bbase (se 2 (by rfl) ⟨63279, by rfl⟩ : syracuseStep 168745 = 126559) (by norm_num)
theorem B332621 : Blo 147793 332621 := bbase (se 3 (by rfl) ⟨62366, by rfl⟩ : syracuseStep 332621 = 124733) (by norm_num)
theorem B168781 : Blo 147793 168781 := bbase (se 3 (by rfl) ⟨31646, by rfl⟩ : syracuseStep 168781 = 63293) (by norm_num)
theorem B168817 : Blo 147793 168817 := bbase (se 2 (by rfl) ⟨63306, by rfl⟩ : syracuseStep 168817 = 126613) (by norm_num)
theorem B758645 : Blo 147793 758645 := bbase (se 5 (by rfl) ⟨35561, by rfl⟩ : syracuseStep 758645 = 71123) (by norm_num)
theorem B332693 : Blo 147793 332693 := bbase (se 6 (by rfl) ⟨7797, by rfl⟩ : syracuseStep 332693 = 15595) (by norm_num)
theorem B168853 : Blo 147793 168853 := bbase (se 6 (by rfl) ⟨3957, by rfl⟩ : syracuseStep 168853 = 7915) (by norm_num)
theorem B168889 : Blo 147793 168889 := bbase (se 2 (by rfl) ⟨63333, by rfl⟩ : syracuseStep 168889 = 126667) (by norm_num)
theorem B431045 : Blo 147793 431045 := bbase (se 4 (by rfl) ⟨40410, by rfl⟩ : syracuseStep 431045 = 80821) (by norm_num)
theorem B267221 : Blo 147793 267221 := bbase (se 7 (by rfl) ⟨3131, by rfl⟩ : syracuseStep 267221 = 6263) (by norm_num)
theorem B332765 : Blo 147793 332765 := bbase (se 3 (by rfl) ⟨62393, by rfl⟩ : syracuseStep 332765 = 124787) (by norm_num)
theorem B168925 : Blo 147793 168925 := bbase (se 3 (by rfl) ⟨31673, by rfl⟩ : syracuseStep 168925 = 63347) (by norm_num)
theorem B168961 : Blo 147793 168961 := bbase (se 2 (by rfl) ⟨63360, by rfl⟩ : syracuseStep 168961 = 126721) (by norm_num)
theorem B758821 : Blo 147793 758821 := bbase (se 4 (by rfl) ⟨71139, by rfl⟩ : syracuseStep 758821 = 142279) (by norm_num)
theorem B332837 : Blo 147793 332837 := bbase (se 4 (by rfl) ⟨31203, by rfl⟩ : syracuseStep 332837 = 62407) (by norm_num)
theorem B168997 : Blo 147793 168997 := bbase (se 4 (by rfl) ⟨15843, by rfl⟩ : syracuseStep 168997 = 31687) (by norm_num)
theorem B169033 : Blo 147793 169033 := bbase (se 2 (by rfl) ⟨63387, by rfl⟩ : syracuseStep 169033 = 126775) (by norm_num)
theorem B332909 : Blo 147793 332909 := bbase (se 3 (by rfl) ⟨62420, by rfl⟩ : syracuseStep 332909 = 124841) (by norm_num)
theorem B169069 : Blo 147793 169069 := bbase (se 3 (by rfl) ⟨31700, by rfl⟩ : syracuseStep 169069 = 63401) (by norm_num)
theorem B169105 : Blo 147793 169105 := bbase (se 2 (by rfl) ⟨63414, by rfl⟩ : syracuseStep 169105 = 126829) (by norm_num)
theorem B332981 : Blo 147793 332981 := bbase (se 5 (by rfl) ⟨15608, by rfl⟩ : syracuseStep 332981 = 31217) (by norm_num)
theorem B169141 : Blo 147793 169141 := bbase (se 5 (by rfl) ⟨7928, by rfl⟩ : syracuseStep 169141 = 15857) (by norm_num)
theorem B169177 : Blo 147793 169177 := bbase (se 2 (by rfl) ⟨63441, by rfl⟩ : syracuseStep 169177 = 126883) (by norm_num)
theorem B267509 : Blo 147793 267509 := bbase (se 5 (by rfl) ⟨12539, by rfl⟩ : syracuseStep 267509 = 25079) (by norm_num)
theorem B333053 : Blo 147793 333053 := bbase (se 3 (by rfl) ⟨62447, by rfl⟩ : syracuseStep 333053 = 124895) (by norm_num)
theorem B169213 : Blo 147793 169213 := bbase (se 3 (by rfl) ⟨31727, by rfl⟩ : syracuseStep 169213 = 63455) (by norm_num)
theorem B169249 : Blo 147793 169249 := bbase (se 2 (by rfl) ⟨63468, by rfl⟩ : syracuseStep 169249 = 126937) (by norm_num)
theorem B333125 : Blo 147793 333125 := bbase (se 4 (by rfl) ⟨31230, by rfl⟩ : syracuseStep 333125 = 62461) (by norm_num)
theorem B169285 : Blo 147793 169285 := bbase (se 4 (by rfl) ⟨15870, by rfl⟩ : syracuseStep 169285 = 31741) (by norm_num)
theorem B169321 : Blo 147793 169321 := bbase (se 2 (by rfl) ⟨63495, by rfl⟩ : syracuseStep 169321 = 126991) (by norm_num)
theorem B431477 : Blo 147793 431477 := bbase (se 5 (by rfl) ⟨20225, by rfl⟩ : syracuseStep 431477 = 40451) (by norm_num)
theorem B333197 : Blo 147793 333197 := bbase (se 3 (by rfl) ⟨62474, by rfl⟩ : syracuseStep 333197 = 124949) (by norm_num)
theorem B169357 : Blo 147793 169357 := bbase (se 3 (by rfl) ⟨31754, by rfl⟩ : syracuseStep 169357 = 63509) (by norm_num)
theorem B169393 : Blo 147793 169393 := bbase (se 2 (by rfl) ⟨63522, by rfl⟩ : syracuseStep 169393 = 127045) (by norm_num)
theorem B300493 : Blo 147793 300493 := bbase (se 3 (by rfl) ⟨56342, by rfl⟩ : syracuseStep 300493 = 112685) (by norm_num)
theorem B333269 : Blo 147793 333269 := bbase (se 7 (by rfl) ⟨3905, by rfl⟩ : syracuseStep 333269 = 7811) (by norm_num)
theorem B267733 : Blo 147793 267733 := bbase (se 7 (by rfl) ⟨3137, by rfl⟩ : syracuseStep 267733 = 6275) (by norm_num)
theorem B169429 : Blo 147793 169429 := bbase (se 7 (by rfl) ⟨1985, by rfl⟩ : syracuseStep 169429 = 3971) (by norm_num)
theorem B169465 : Blo 147793 169465 := bbase (se 2 (by rfl) ⟨63549, by rfl⟩ : syracuseStep 169465 = 127099) (by norm_num)
theorem B267797 : Blo 147793 267797 := bbase (se 6 (by rfl) ⟨6276, by rfl⟩ : syracuseStep 267797 = 12553) (by norm_num)
theorem B333341 : Blo 147793 333341 := bbase (se 3 (by rfl) ⟨62501, by rfl⟩ : syracuseStep 333341 = 125003) (by norm_num)
theorem B169501 : Blo 147793 169501 := bbase (se 3 (by rfl) ⟨31781, by rfl⟩ : syracuseStep 169501 = 63563) (by norm_num)
theorem B169537 : Blo 147793 169537 := bbase (se 2 (by rfl) ⟨63576, by rfl⟩ : syracuseStep 169537 = 127153) (by norm_num)
theorem B333413 : Blo 147793 333413 := bbase (se 4 (by rfl) ⟨31257, by rfl⟩ : syracuseStep 333413 = 62515) (by norm_num)
theorem B169573 : Blo 147793 169573 := bbase (se 4 (by rfl) ⟨15897, by rfl⟩ : syracuseStep 169573 = 31795) (by norm_num)
theorem B169609 : Blo 147793 169609 := bbase (se 2 (by rfl) ⟨63603, by rfl⟩ : syracuseStep 169609 = 127207) (by norm_num)
theorem B202405 : Blo 147793 202405 := bbase (se 4 (by rfl) ⟨18975, by rfl⟩ : syracuseStep 202405 = 37951) (by norm_num)
theorem B333485 : Blo 147793 333485 := bbase (se 3 (by rfl) ⟨62528, by rfl⟩ : syracuseStep 333485 = 125057) (by norm_num)
theorem B169645 : Blo 147793 169645 := bbase (se 3 (by rfl) ⟨31808, by rfl⟩ : syracuseStep 169645 = 63617) (by norm_num)
theorem B169681 : Blo 147793 169681 := bbase (se 2 (by rfl) ⟨63630, by rfl⟩ : syracuseStep 169681 = 127261) (by norm_num)
theorem B333557 : Blo 147793 333557 := bbase (se 5 (by rfl) ⟨15635, by rfl⟩ : syracuseStep 333557 = 31271) (by norm_num)
theorem B169717 : Blo 147793 169717 := bbase (se 5 (by rfl) ⟨7955, by rfl⟩ : syracuseStep 169717 = 15911) (by norm_num)
theorem B169753 : Blo 147793 169753 := bbase (se 2 (by rfl) ⟨63657, by rfl⟩ : syracuseStep 169753 = 127315) (by norm_num)
theorem B333629 : Blo 147793 333629 := bbase (se 3 (by rfl) ⟨62555, by rfl⟩ : syracuseStep 333629 = 125111) (by norm_num)
theorem B169789 : Blo 147793 169789 := bbase (se 3 (by rfl) ⟨31835, by rfl⟩ : syracuseStep 169789 = 63671) (by norm_num)
theorem B169825 : Blo 147793 169825 := bbase (se 2 (by rfl) ⟨63684, by rfl⟩ : syracuseStep 169825 = 127369) (by norm_num)
theorem B333701 : Blo 147793 333701 := bbase (se 4 (by rfl) ⟨31284, by rfl⟩ : syracuseStep 333701 = 62569) (by norm_num)
theorem B169861 : Blo 147793 169861 := bbase (se 4 (by rfl) ⟨15924, by rfl⟩ : syracuseStep 169861 = 31849) (by norm_num)
theorem B169897 : Blo 147793 169897 := bbase (se 2 (by rfl) ⟨63711, by rfl⟩ : syracuseStep 169897 = 127423) (by norm_num)
theorem B726965 : Blo 147793 726965 := bbase (se 5 (by rfl) ⟨34076, by rfl⟩ : syracuseStep 726965 = 68153) (by norm_num)
theorem B333773 : Blo 147793 333773 := bbase (se 3 (by rfl) ⟨62582, by rfl⟩ : syracuseStep 333773 = 125165) (by norm_num)
theorem B169933 : Blo 147793 169933 := bbase (se 3 (by rfl) ⟨31862, by rfl⟩ : syracuseStep 169933 = 63725) (by norm_num)
theorem B366557 : Blo 147793 366557 := bbase (se 3 (by rfl) ⟨68729, by rfl⟩ : syracuseStep 366557 = 137459) (by norm_num)
theorem B169969 : Blo 147793 169969 := bbase (se 2 (by rfl) ⟨63738, by rfl⟩ : syracuseStep 169969 = 127477) (by norm_num)
theorem B333845 : Blo 147793 333845 := bbase (se 6 (by rfl) ⟨7824, by rfl⟩ : syracuseStep 333845 = 15649) (by norm_num)
theorem B170005 : Blo 147793 170005 := bbase (se 6 (by rfl) ⟨3984, by rfl⟩ : syracuseStep 170005 = 7969) (by norm_num)
theorem B464933 : Blo 147793 464933 := bbase (se 4 (by rfl) ⟨43587, by rfl⟩ : syracuseStep 464933 = 87175) (by norm_num)
theorem B170041 : Blo 147793 170041 := bbase (se 2 (by rfl) ⟨63765, by rfl⟩ : syracuseStep 170041 = 127531) (by norm_num)
theorem B333917 : Blo 147793 333917 := bbase (se 3 (by rfl) ⟨62609, by rfl⟩ : syracuseStep 333917 = 125219) (by norm_num)
theorem B170077 : Blo 147793 170077 := bbase (se 3 (by rfl) ⟨31889, by rfl⟩ : syracuseStep 170077 = 63779) (by norm_num)
theorem B432229 : Blo 147793 432229 := bbase (se 4 (by rfl) ⟨40521, by rfl⟩ : syracuseStep 432229 = 81043) (by norm_num)
theorem B170113 : Blo 147793 170113 := bbase (se 2 (by rfl) ⟨63792, by rfl⟩ : syracuseStep 170113 = 127585) (by norm_num)
theorem B759941 : Blo 147793 759941 := bbase (se 4 (by rfl) ⟨71244, by rfl⟩ : syracuseStep 759941 = 142489) (by norm_num)
theorem B170141 : Blo 147793 170141 := bbase (se 3 (by rfl) ⟨31901, by rfl⟩ : syracuseStep 170141 = 63803) (by norm_num)
theorem B333989 : Blo 147793 333989 := bbase (se 4 (by rfl) ⟨31311, by rfl⟩ : syracuseStep 333989 = 62623) (by norm_num)
theorem B170149 : Blo 147793 170149 := bbase (se 4 (by rfl) ⟨15951, by rfl⟩ : syracuseStep 170149 = 31903) (by norm_num)
theorem B563381 : Blo 147793 563381 := bbase (se 5 (by rfl) ⟨26408, by rfl⟩ : syracuseStep 563381 = 52817) (by norm_num)
theorem B170185 : Blo 147793 170185 := bbase (se 2 (by rfl) ⟨63819, by rfl⟩ : syracuseStep 170185 = 127639) (by norm_num)
theorem B334061 : Blo 147793 334061 := bbase (se 3 (by rfl) ⟨62636, by rfl⟩ : syracuseStep 334061 = 125273) (by norm_num)
theorem B170221 : Blo 147793 170221 := bbase (se 3 (by rfl) ⟨31916, by rfl⟩ : syracuseStep 170221 = 63833) (by norm_num)
theorem B170257 : Blo 147793 170257 := bbase (se 2 (by rfl) ⟨63846, by rfl⟩ : syracuseStep 170257 = 127693) (by norm_num)
theorem B334133 : Blo 147793 334133 := bbase (se 5 (by rfl) ⟨15662, by rfl⟩ : syracuseStep 334133 = 31325) (by norm_num)
theorem B170293 : Blo 147793 170293 := bbase (se 5 (by rfl) ⟨7982, by rfl⟩ : syracuseStep 170293 = 15965) (by norm_num)
theorem B170329 : Blo 147793 170329 := bbase (se 2 (by rfl) ⟨63873, by rfl⟩ : syracuseStep 170329 = 127747) (by norm_num)
theorem B334205 : Blo 147793 334205 := bbase (se 3 (by rfl) ⟨62663, by rfl⟩ : syracuseStep 334205 = 125327) (by norm_num)
theorem B170365 : Blo 147793 170365 := bbase (se 3 (by rfl) ⟨31943, by rfl⟩ : syracuseStep 170365 = 63887) (by norm_num)
theorem B170401 : Blo 147793 170401 := bbase (se 2 (by rfl) ⟨63900, by rfl⟩ : syracuseStep 170401 = 127801) (by norm_num)
theorem B334277 : Blo 147793 334277 := bbase (se 4 (by rfl) ⟨31338, by rfl⟩ : syracuseStep 334277 = 62677) (by norm_num)
theorem B170437 : Blo 147793 170437 := bbase (se 4 (by rfl) ⟨15978, by rfl⟩ : syracuseStep 170437 = 31957) (by norm_num)
theorem B563669 : Blo 147793 563669 := bbase (se 7 (by rfl) ⟨6605, by rfl⟩ : syracuseStep 563669 = 13211) (by norm_num)
theorem B170473 : Blo 147793 170473 := bbase (se 2 (by rfl) ⟨63927, by rfl⟩ : syracuseStep 170473 = 127855) (by norm_num)
theorem B334349 : Blo 147793 334349 := bbase (se 3 (by rfl) ⟨62690, by rfl⟩ : syracuseStep 334349 = 125381) (by norm_num)
theorem B170509 : Blo 147793 170509 := bbase (se 3 (by rfl) ⟨31970, by rfl⟩ : syracuseStep 170509 = 63941) (by norm_num)
theorem B170545 : Blo 147793 170545 := bbase (se 2 (by rfl) ⟨63954, by rfl⟩ : syracuseStep 170545 = 127909) (by norm_num)
theorem B334421 : Blo 147793 334421 := bbase (se 8 (by rfl) ⟨1959, by rfl⟩ : syracuseStep 334421 = 3919) (by norm_num)
theorem B170581 : Blo 147793 170581 := bbase (se 8 (by rfl) ⟨999, by rfl⟩ : syracuseStep 170581 = 1999) (by norm_num)
theorem B170617 : Blo 147793 170617 := bbase (se 2 (by rfl) ⟨63981, by rfl⟩ : syracuseStep 170617 = 127963) (by norm_num)
theorem B334493 : Blo 147793 334493 := bbase (se 3 (by rfl) ⟨62717, by rfl⟩ : syracuseStep 334493 = 125435) (by norm_num)
theorem B170653 : Blo 147793 170653 := bbase (se 3 (by rfl) ⟨31997, by rfl⟩ : syracuseStep 170653 = 63995) (by norm_num)
theorem B170689 : Blo 147793 170689 := bbase (se 2 (by rfl) ⟨64008, by rfl⟩ : syracuseStep 170689 = 128017) (by norm_num)
theorem B334565 : Blo 147793 334565 := bbase (se 4 (by rfl) ⟨31365, by rfl⟩ : syracuseStep 334565 = 62731) (by norm_num)
theorem B170725 : Blo 147793 170725 := bbase (se 4 (by rfl) ⟨16005, by rfl⟩ : syracuseStep 170725 = 32011) (by norm_num)
theorem B170753 : Blo 147793 170753 := bbase (se 2 (by rfl) ⟨64032, by rfl⟩ : syracuseStep 170753 = 128065) (by norm_num)
theorem B170761 : Blo 147793 170761 := bbase (se 2 (by rfl) ⟨64035, by rfl⟩ : syracuseStep 170761 = 128071) (by norm_num)
theorem B334637 : Blo 147793 334637 := bbase (se 3 (by rfl) ⟨62744, by rfl⟩ : syracuseStep 334637 = 125489) (by norm_num)
theorem B334709 : Blo 147793 334709 := bbase (se 5 (by rfl) ⟨15689, by rfl⟩ : syracuseStep 334709 = 31379) (by norm_num)
theorem B334781 : Blo 147793 334781 := bbase (se 3 (by rfl) ⟨62771, by rfl⟩ : syracuseStep 334781 = 125543) (by norm_num)
theorem B203725 : Blo 147793 203725 := bbase (se 3 (by rfl) ⟨38198, by rfl⟩ : syracuseStep 203725 = 76397) (by norm_num)
theorem B334853 : Blo 147793 334853 := bbase (se 4 (by rfl) ⟨31392, by rfl⟩ : syracuseStep 334853 = 62785) (by norm_num)
theorem B629765 : Blo 147793 629765 := bbase (se 4 (by rfl) ⟨59040, by rfl⟩ : syracuseStep 629765 = 118081) (by norm_num)
theorem B334925 : Blo 147793 334925 := bbase (se 3 (by rfl) ⟨62798, by rfl⟩ : syracuseStep 334925 = 125597) (by norm_num)
theorem B334997 : Blo 147793 334997 := bbase (se 6 (by rfl) ⟨7851, by rfl⟩ : syracuseStep 334997 = 15703) (by norm_num)
theorem B171217 : Blo 147793 171217 := bbase (se 2 (by rfl) ⟨64206, by rfl⟩ : syracuseStep 171217 = 128413) (by norm_num)
theorem B335069 : Blo 147793 335069 := bbase (se 3 (by rfl) ⟨62825, by rfl⟩ : syracuseStep 335069 = 125651) (by norm_num)
theorem B236773 : Blo 147793 236773 := bbase (se 4 (by rfl) ⟨22197, by rfl⟩ : syracuseStep 236773 = 44395) (by norm_num)
theorem B204005 : Blo 147793 204005 := bbase (se 4 (by rfl) ⟨19125, by rfl⟩ : syracuseStep 204005 = 38251) (by norm_num)
theorem B335141 : Blo 147793 335141 := bbase (se 4 (by rfl) ⟨31419, by rfl⟩ : syracuseStep 335141 = 62839) (by norm_num)
theorem B499013 : Blo 147793 499013 := bbase (se 4 (by rfl) ⟨46782, by rfl⟩ : syracuseStep 499013 = 93565) (by norm_num)
theorem B335213 : Blo 147793 335213 := bbase (se 3 (by rfl) ⟨62852, by rfl⟩ : syracuseStep 335213 = 125705) (by norm_num)
theorem B761237 : Blo 147793 761237 := bbase (se 6 (by rfl) ⟨17841, by rfl⟩ : syracuseStep 761237 = 35683) (by norm_num)
theorem B335285 : Blo 147793 335285 := bbase (se 5 (by rfl) ⟨15716, by rfl⟩ : syracuseStep 335285 = 31433) (by norm_num)
theorem B335357 : Blo 147793 335357 := bbase (se 3 (by rfl) ⟨62879, by rfl⟩ : syracuseStep 335357 = 125759) (by norm_num)
theorem B335429 : Blo 147793 335429 := bbase (se 4 (by rfl) ⟨31446, by rfl⟩ : syracuseStep 335429 = 62893) (by norm_num)
theorem B564853 : Blo 147793 564853 := bbase (se 5 (by rfl) ⟨26477, by rfl⟩ : syracuseStep 564853 = 52955) (by norm_num)
theorem B302717 : Blo 147793 302717 := bbase (se 3 (by rfl) ⟨56759, by rfl⟩ : syracuseStep 302717 = 113519) (by norm_num)
theorem B335501 : Blo 147793 335501 := bbase (se 3 (by rfl) ⟨62906, by rfl⟩ : syracuseStep 335501 = 125813) (by norm_num)
theorem B1023637 : Blo 147793 1023637 := bbase (se 6 (by rfl) ⟨23991, by rfl⟩ : syracuseStep 1023637 = 47983) (by norm_num)
theorem B335573 : Blo 147793 335573 := bbase (se 7 (by rfl) ⟨3932, by rfl⟩ : syracuseStep 335573 = 7865) (by norm_num)
theorem B499445 : Blo 147793 499445 := bbase (se 5 (by rfl) ⟨23411, by rfl⟩ : syracuseStep 499445 = 46823) (by norm_num)
theorem B335645 : Blo 147793 335645 := bbase (se 3 (by rfl) ⟨62933, by rfl⟩ : syracuseStep 335645 = 125867) (by norm_num)
theorem B335717 : Blo 147793 335717 := bbase (se 4 (by rfl) ⟨31473, by rfl⟩ : syracuseStep 335717 = 62947) (by norm_num)
theorem B237421 : Blo 147793 237421 := bbase (se 3 (by rfl) ⟨44516, by rfl⟩ : syracuseStep 237421 = 89033) (by norm_num)
theorem B434069 : Blo 147793 434069 := bbase (se 6 (by rfl) ⟨10173, by rfl⟩ : syracuseStep 434069 = 20347) (by norm_num)
theorem B565157 : Blo 147793 565157 := bbase (se 4 (by rfl) ⟨52983, by rfl⟩ : syracuseStep 565157 = 105967) (by norm_num)
theorem B204709 : Blo 147793 204709 := bbase (se 4 (by rfl) ⟨19191, by rfl⟩ : syracuseStep 204709 = 38383) (by norm_num)
theorem B335789 : Blo 147793 335789 := bbase (se 3 (by rfl) ⟨62960, by rfl⟩ : syracuseStep 335789 = 125921) (by norm_num)
theorem B335861 : Blo 147793 335861 := bbase (se 5 (by rfl) ⟨15743, by rfl⟩ : syracuseStep 335861 = 31487) (by norm_num)
theorem B335933 : Blo 147793 335933 := bbase (se 3 (by rfl) ⟨62987, by rfl⟩ : syracuseStep 335933 = 125975) (by norm_num)
theorem B204925 : Blo 147793 204925 := bbase (se 3 (by rfl) ⟨38423, by rfl⟩ : syracuseStep 204925 = 76847) (by norm_num)
theorem B336005 : Blo 147793 336005 := bbase (se 4 (by rfl) ⟨31500, by rfl⟩ : syracuseStep 336005 = 63001) (by norm_num)
theorem B499877 : Blo 147793 499877 := bbase (se 4 (by rfl) ⟨46863, by rfl⟩ : syracuseStep 499877 = 93727) (by norm_num)
theorem B336077 : Blo 147793 336077 := bbase (se 3 (by rfl) ⟨63014, by rfl⟩ : syracuseStep 336077 = 126029) (by norm_num)
theorem B336149 : Blo 147793 336149 := bbase (se 6 (by rfl) ⟨7878, by rfl⟩ : syracuseStep 336149 = 15757) (by norm_num)
theorem B1089845 : Blo 147793 1089845 := bbase (se 5 (by rfl) ⟨51086, by rfl⟩ : syracuseStep 1089845 = 102173) (by norm_num)
theorem B336221 : Blo 147793 336221 := bbase (se 3 (by rfl) ⟨63041, by rfl⟩ : syracuseStep 336221 = 126083) (by norm_num)
theorem B336293 : Blo 147793 336293 := bbase (se 4 (by rfl) ⟨31527, by rfl⟩ : syracuseStep 336293 = 63055) (by norm_num)
theorem B336365 : Blo 147793 336365 := bbase (se 3 (by rfl) ⟨63068, by rfl⟩ : syracuseStep 336365 = 126137) (by norm_num)
theorem B336437 : Blo 147793 336437 := bbase (se 5 (by rfl) ⟨15770, by rfl⟩ : syracuseStep 336437 = 31541) (by norm_num)
theorem B500309 : Blo 147793 500309 := bbase (se 8 (by rfl) ⟨2931, by rfl⟩ : syracuseStep 500309 = 5863) (by norm_num)
theorem B336509 : Blo 147793 336509 := bbase (se 3 (by rfl) ⟨63095, by rfl⟩ : syracuseStep 336509 = 126191) (by norm_num)
theorem B762533 : Blo 147793 762533 := bbase (se 4 (by rfl) ⟨71487, by rfl⟩ : syracuseStep 762533 = 142975) (by norm_num)
theorem B336581 : Blo 147793 336581 := bbase (se 4 (by rfl) ⟨31554, by rfl⟩ : syracuseStep 336581 = 63109) (by norm_num)
theorem B238349 : Blo 147793 238349 := bbase (se 3 (by rfl) ⟨44690, by rfl⟩ : syracuseStep 238349 = 89381) (by norm_num)
theorem B336653 : Blo 147793 336653 := bbase (se 3 (by rfl) ⟨63122, by rfl⟩ : syracuseStep 336653 = 126245) (by norm_num)
theorem B2564885 : Blo 147793 2564885 := bbase (se 6 (by rfl) ⟨60114, by rfl⟩ : syracuseStep 2564885 = 120229) (by norm_num)
theorem B303925 : Blo 147793 303925 := bbase (se 5 (by rfl) ⟨14246, by rfl⟩ : syracuseStep 303925 = 28493) (by norm_num)
theorem B336725 : Blo 147793 336725 := bbase (se 9 (by rfl) ⟨986, by rfl⟩ : syracuseStep 336725 = 1973) (by norm_num)
theorem B336797 : Blo 147793 336797 := bbase (se 3 (by rfl) ⟨63149, by rfl⟩ : syracuseStep 336797 = 126299) (by norm_num)
theorem B304069 : Blo 147793 304069 := bbase (se 4 (by rfl) ⟨28506, by rfl⟩ : syracuseStep 304069 = 57013) (by norm_num)
theorem B533461 : Blo 147793 533461 := bbase (se 7 (by rfl) ⟨6251, by rfl⟩ : syracuseStep 533461 = 12503) (by norm_num)
theorem B336869 : Blo 147793 336869 := bbase (se 4 (by rfl) ⟨31581, by rfl⟩ : syracuseStep 336869 = 63163) (by norm_num)
theorem B500741 : Blo 147793 500741 := bbase (se 4 (by rfl) ⟨46944, by rfl⟩ : syracuseStep 500741 = 93889) (by norm_num)
theorem B336941 : Blo 147793 336941 := bbase (se 3 (by rfl) ⟨63176, by rfl⟩ : syracuseStep 336941 = 126353) (by norm_num)
theorem B533621 : Blo 147793 533621 := bbase (se 5 (by rfl) ⟨25013, by rfl⟩ : syracuseStep 533621 = 50027) (by norm_num)
theorem B337013 : Blo 147793 337013 := bbase (se 5 (by rfl) ⟨15797, by rfl⟩ : syracuseStep 337013 = 31595) (by norm_num)
theorem B337085 : Blo 147793 337085 := bbase (se 3 (by rfl) ⟨63203, by rfl⟩ : syracuseStep 337085 = 126407) (by norm_num)
theorem B238805 : Blo 147793 238805 := bbase (se 7 (by rfl) ⟨2798, by rfl⟩ : syracuseStep 238805 = 5597) (by norm_num)
theorem B337157 : Blo 147793 337157 := bbase (se 4 (by rfl) ⟨31608, by rfl⟩ : syracuseStep 337157 = 63217) (by norm_num)
theorem B337229 : Blo 147793 337229 := bbase (se 3 (by rfl) ⟨63230, by rfl⟩ : syracuseStep 337229 = 126461) (by norm_num)
theorem B763253 : Blo 147793 763253 := bbase (se 5 (by rfl) ⟨35777, by rfl⟩ : syracuseStep 763253 = 71555) (by norm_num)
theorem B337301 : Blo 147793 337301 := bbase (se 6 (by rfl) ⟨7905, by rfl⟩ : syracuseStep 337301 = 15811) (by norm_num)
theorem B501173 : Blo 147793 501173 := bbase (se 5 (by rfl) ⟨23492, by rfl⟩ : syracuseStep 501173 = 46985) (by norm_num)
theorem B2139605 : Blo 147793 2139605 := bbase (se 7 (by rfl) ⟨25073, by rfl⟩ : syracuseStep 2139605 = 50147) (by norm_num)
theorem B959957 : Blo 147793 959957 := bbase (se 7 (by rfl) ⟨11249, by rfl⟩ : syracuseStep 959957 = 22499) (by norm_num)
theorem B304597 : Blo 147793 304597 := bbase (se 7 (by rfl) ⟨3569, by rfl⟩ : syracuseStep 304597 = 7139) (by norm_num)
theorem B337373 : Blo 147793 337373 := bbase (se 3 (by rfl) ⟨63257, by rfl⟩ : syracuseStep 337373 = 126515) (by norm_num)
theorem B763397 : Blo 147793 763397 := bbase (se 4 (by rfl) ⟨71568, by rfl⟩ : syracuseStep 763397 = 143137) (by norm_num)
theorem B337445 : Blo 147793 337445 := bbase (se 4 (by rfl) ⟨31635, by rfl⟩ : syracuseStep 337445 = 63271) (by norm_num)
theorem B337517 : Blo 147793 337517 := bbase (se 3 (by rfl) ⟨63284, by rfl⟩ : syracuseStep 337517 = 126569) (by norm_num)
theorem B468629 : Blo 147793 468629 := bbase (se 6 (by rfl) ⟨10983, by rfl⟩ : syracuseStep 468629 = 21967) (by norm_num)
theorem B337589 : Blo 147793 337589 := bbase (se 5 (by rfl) ⟨15824, by rfl⟩ : syracuseStep 337589 = 31649) (by norm_num)
theorem B403157 : Blo 147793 403157 := bbase (se 7 (by rfl) ⟨4724, by rfl⟩ : syracuseStep 403157 = 9449) (by norm_num)
theorem B337661 : Blo 147793 337661 := bbase (se 3 (by rfl) ⟨63311, by rfl⟩ : syracuseStep 337661 = 126623) (by norm_num)
theorem B1124117 : Blo 147793 1124117 := bbase (se 6 (by rfl) ⟨26346, by rfl⟩ : syracuseStep 1124117 = 52693) (by norm_num)
theorem B337733 : Blo 147793 337733 := bbase (se 4 (by rfl) ⟨31662, by rfl⟩ : syracuseStep 337733 = 63325) (by norm_num)
theorem B501605 : Blo 147793 501605 := bbase (se 4 (by rfl) ⟨47025, by rfl⟩ : syracuseStep 501605 = 94051) (by norm_num)
theorem B337805 : Blo 147793 337805 := bbase (se 3 (by rfl) ⟨63338, by rfl⟩ : syracuseStep 337805 = 126677) (by norm_num)
theorem B763829 : Blo 147793 763829 := bbase (se 5 (by rfl) ⟨35804, by rfl⟩ : syracuseStep 763829 = 71609) (by norm_num)
theorem B337877 : Blo 147793 337877 := bbase (se 7 (by rfl) ⟨3959, by rfl⟩ : syracuseStep 337877 = 7919) (by norm_num)
theorem B567269 : Blo 147793 567269 := bbase (se 4 (by rfl) ⟨53181, by rfl⟩ : syracuseStep 567269 = 106363) (by norm_num)
theorem B337949 : Blo 147793 337949 := bbase (se 3 (by rfl) ⟨63365, by rfl⟩ : syracuseStep 337949 = 126731) (by norm_num)
theorem B632933 : Blo 147793 632933 := bbase (se 4 (by rfl) ⟨59337, by rfl⟩ : syracuseStep 632933 = 118675) (by norm_num)
theorem B338021 : Blo 147793 338021 := bbase (se 4 (by rfl) ⟨31689, by rfl⟩ : syracuseStep 338021 = 63379) (by norm_num)
theorem B206965 : Blo 147793 206965 := bbase (se 5 (by rfl) ⟨9701, by rfl⟩ : syracuseStep 206965 = 19403) (by norm_num)
theorem B338093 : Blo 147793 338093 := bbase (se 3 (by rfl) ⟨63392, by rfl⟩ : syracuseStep 338093 = 126785) (by norm_num)
theorem B338165 : Blo 147793 338165 := bbase (se 5 (by rfl) ⟨15851, by rfl⟩ : syracuseStep 338165 = 31703) (by norm_num)
theorem B567557 : Blo 147793 567557 := bbase (se 4 (by rfl) ⟨53208, by rfl⟩ : syracuseStep 567557 = 106417) (by norm_num)
theorem B502037 : Blo 147793 502037 := bbase (se 6 (by rfl) ⟨11766, by rfl⟩ : syracuseStep 502037 = 23533) (by norm_num)
theorem B338237 : Blo 147793 338237 := bbase (se 3 (by rfl) ⟨63419, by rfl⟩ : syracuseStep 338237 = 126839) (by norm_num)
theorem B338309 : Blo 147793 338309 := bbase (se 4 (by rfl) ⟨31716, by rfl⟩ : syracuseStep 338309 = 63433) (by norm_num)
theorem B338381 : Blo 147793 338381 := bbase (se 3 (by rfl) ⟨63446, by rfl⟩ : syracuseStep 338381 = 126893) (by norm_num)
theorem B338453 : Blo 147793 338453 := bbase (se 6 (by rfl) ⟨7932, by rfl⟩ : syracuseStep 338453 = 15865) (by norm_num)
theorem B305741 : Blo 147793 305741 := bbase (se 3 (by rfl) ⟨57326, by rfl⟩ : syracuseStep 305741 = 114653) (by norm_num)
theorem B240221 : Blo 147793 240221 := bbase (se 3 (by rfl) ⟨45041, by rfl⟩ : syracuseStep 240221 = 90083) (by norm_num)
theorem B338525 : Blo 147793 338525 := bbase (se 3 (by rfl) ⟨63473, by rfl⟩ : syracuseStep 338525 = 126947) (by norm_num)
theorem B305813 : Blo 147793 305813 := bbase (se 6 (by rfl) ⟨7167, by rfl⟩ : syracuseStep 305813 = 14335) (by norm_num)
theorem B338597 : Blo 147793 338597 := bbase (se 4 (by rfl) ⟨31743, by rfl⟩ : syracuseStep 338597 = 63487) (by norm_num)
theorem B1452725 : Blo 147793 1452725 := bbase (se 5 (by rfl) ⟨68096, by rfl⟩ : syracuseStep 1452725 = 136193) (by norm_num)
theorem B502469 : Blo 147793 502469 := bbase (se 4 (by rfl) ⟨47106, by rfl⟩ : syracuseStep 502469 = 94213) (by norm_num)
theorem B2730709 : Blo 147793 2730709 := bbase (se 7 (by rfl) ⟨32000, by rfl⟩ : syracuseStep 2730709 = 64001) (by norm_num)
theorem B338669 : Blo 147793 338669 := bbase (se 3 (by rfl) ⟨63500, by rfl⟩ : syracuseStep 338669 = 127001) (by norm_num)
theorem B338741 : Blo 147793 338741 := bbase (se 5 (by rfl) ⟨15878, by rfl⟩ : syracuseStep 338741 = 31757) (by norm_num)
theorem B240445 : Blo 147793 240445 := bbase (se 3 (by rfl) ⟨45083, by rfl⟩ : syracuseStep 240445 = 90167) (by norm_num)
theorem B273269 : Blo 147793 273269 := bbase (se 5 (by rfl) ⟨12809, by rfl⟩ : syracuseStep 273269 = 25619) (by norm_num)
theorem B338813 : Blo 147793 338813 := bbase (se 3 (by rfl) ⟨63527, by rfl⟩ : syracuseStep 338813 = 127055) (by norm_num)
theorem B338885 : Blo 147793 338885 := bbase (se 4 (by rfl) ⟨31770, by rfl⟩ : syracuseStep 338885 = 63541) (by norm_num)
theorem B306125 : Blo 147793 306125 := bbase (se 3 (by rfl) ⟨57398, by rfl⟩ : syracuseStep 306125 = 114797) (by norm_num)
theorem B338957 : Blo 147793 338957 := bbase (se 3 (by rfl) ⟨63554, by rfl⟩ : syracuseStep 338957 = 127109) (by norm_num)
theorem B339005 : Blo 147793 339005 := bbase (se 3 (by rfl) ⟨63563, by rfl⟩ : syracuseStep 339005 = 127127) (by norm_num)
theorem B339029 : Blo 147793 339029 := bbase (se 8 (by rfl) ⟨1986, by rfl⟩ : syracuseStep 339029 = 3973) (by norm_num)
theorem B502901 : Blo 147793 502901 := bbase (se 5 (by rfl) ⟨23573, by rfl⟩ : syracuseStep 502901 = 47147) (by norm_num)
theorem B339101 : Blo 147793 339101 := bbase (se 3 (by rfl) ⟨63581, by rfl⟩ : syracuseStep 339101 = 127163) (by norm_num)
theorem B765125 : Blo 147793 765125 := bbase (se 4 (by rfl) ⟨71730, by rfl⟩ : syracuseStep 765125 = 143461) (by norm_num)
theorem B339173 : Blo 147793 339173 := bbase (se 4 (by rfl) ⟨31797, by rfl⟩ : syracuseStep 339173 = 63595) (by norm_num)
theorem B339245 : Blo 147793 339245 := bbase (se 3 (by rfl) ⟨63608, by rfl⟩ : syracuseStep 339245 = 127217) (by norm_num)
theorem B339317 : Blo 147793 339317 := bbase (se 5 (by rfl) ⟨15905, by rfl⟩ : syracuseStep 339317 = 31811) (by norm_num)
theorem B437653 : Blo 147793 437653 := bbase (se 6 (by rfl) ⟨10257, by rfl⟩ : syracuseStep 437653 = 20515) (by norm_num)
theorem B568741 : Blo 147793 568741 := bbase (se 4 (by rfl) ⟨53319, by rfl⟩ : syracuseStep 568741 = 106639) (by norm_num)
theorem B339389 : Blo 147793 339389 := bbase (se 3 (by rfl) ⟨63635, by rfl⟩ : syracuseStep 339389 = 127271) (by norm_num)
theorem B339461 : Blo 147793 339461 := bbase (se 4 (by rfl) ⟨31824, by rfl⟩ : syracuseStep 339461 = 63649) (by norm_num)
theorem B503333 : Blo 147793 503333 := bbase (se 4 (by rfl) ⟨47187, by rfl⟩ : syracuseStep 503333 = 94375) (by norm_num)
theorem B339533 : Blo 147793 339533 := bbase (se 3 (by rfl) ⟨63662, by rfl⟩ : syracuseStep 339533 = 127325) (by norm_num)
theorem B339605 : Blo 147793 339605 := bbase (se 6 (by rfl) ⟨7959, by rfl⟩ : syracuseStep 339605 = 15919) (by norm_num)
theorem B569045 : Blo 147793 569045 := bbase (se 7 (by rfl) ⟨6668, by rfl⟩ : syracuseStep 569045 = 13337) (by norm_num)
theorem B339677 : Blo 147793 339677 := bbase (se 3 (by rfl) ⟨63689, by rfl⟩ : syracuseStep 339677 = 127379) (by norm_num)
theorem B339749 : Blo 147793 339749 := bbase (se 4 (by rfl) ⟨31851, by rfl⟩ : syracuseStep 339749 = 63703) (by norm_num)
theorem B634709 : Blo 147793 634709 := bbase (se 9 (by rfl) ⟨1859, by rfl⟩ : syracuseStep 634709 = 3719) (by norm_num)
theorem B339821 : Blo 147793 339821 := bbase (se 3 (by rfl) ⟨63716, by rfl⟩ : syracuseStep 339821 = 127433) (by norm_num)
theorem B339893 : Blo 147793 339893 := bbase (se 5 (by rfl) ⟨15932, by rfl⟩ : syracuseStep 339893 = 31865) (by norm_num)
theorem B503765 : Blo 147793 503765 := bbase (se 7 (by rfl) ⟨5903, by rfl⟩ : syracuseStep 503765 = 11807) (by norm_num)
theorem B1093621 : Blo 147793 1093621 := bbase (se 5 (by rfl) ⟨51263, by rfl⟩ : syracuseStep 1093621 = 102527) (by norm_num)
theorem B339965 : Blo 147793 339965 := bbase (se 3 (by rfl) ⟨63743, by rfl⟩ : syracuseStep 339965 = 127487) (by norm_num)
theorem B634949 : Blo 147793 634949 := bbase (se 4 (by rfl) ⟨59526, by rfl⟩ : syracuseStep 634949 = 119053) (by norm_num)
theorem B340037 : Blo 147793 340037 := bbase (se 4 (by rfl) ⟨31878, by rfl⟩ : syracuseStep 340037 = 63757) (by norm_num)
theorem B340109 : Blo 147793 340109 := bbase (se 3 (by rfl) ⟨63770, by rfl⟩ : syracuseStep 340109 = 127541) (by norm_num)
theorem B241861 : Blo 147793 241861 := bbase (se 4 (by rfl) ⟨22674, by rfl⟩ : syracuseStep 241861 = 45349) (by norm_num)
theorem B2699477 : Blo 147793 2699477 := bbase (se 7 (by rfl) ⟨31634, by rfl⟩ : syracuseStep 2699477 = 63269) (by norm_num)
theorem B340181 : Blo 147793 340181 := bbase (se 7 (by rfl) ⟨3986, by rfl⟩ : syracuseStep 340181 = 7973) (by norm_num)
theorem B340253 : Blo 147793 340253 := bbase (se 3 (by rfl) ⟨63797, by rfl⟩ : syracuseStep 340253 = 127595) (by norm_num)
theorem B340325 : Blo 147793 340325 := bbase (se 4 (by rfl) ⟨31905, by rfl⟩ : syracuseStep 340325 = 63811) (by norm_num)
theorem B504197 : Blo 147793 504197 := bbase (se 4 (by rfl) ⟨47268, by rfl⟩ : syracuseStep 504197 = 94537) (by norm_num)
theorem B340397 : Blo 147793 340397 := bbase (se 3 (by rfl) ⟨63824, by rfl⟩ : syracuseStep 340397 = 127649) (by norm_num)
theorem B242117 : Blo 147793 242117 := bbase (se 4 (by rfl) ⟨22698, by rfl⟩ : syracuseStep 242117 = 45397) (by norm_num)
theorem B766421 : Blo 147793 766421 := bbase (se 7 (by rfl) ⟨8981, by rfl⟩ : syracuseStep 766421 = 17963) (by norm_num)
theorem B340469 : Blo 147793 340469 := bbase (se 5 (by rfl) ⟨15959, by rfl⟩ : syracuseStep 340469 = 31919) (by norm_num)
theorem B1683989 : Blo 147793 1683989 := bbase (se 6 (by rfl) ⟨39468, by rfl⟩ : syracuseStep 1683989 = 78937) (by norm_num)
theorem B340541 : Blo 147793 340541 := bbase (se 3 (by rfl) ⟨63851, by rfl⟩ : syracuseStep 340541 = 127703) (by norm_num)
theorem B242309 : Blo 147793 242309 := bbase (se 4 (by rfl) ⟨22716, by rfl⟩ : syracuseStep 242309 = 45433) (by norm_num)
theorem B340613 : Blo 147793 340613 := bbase (se 4 (by rfl) ⟨31932, by rfl⟩ : syracuseStep 340613 = 63865) (by norm_num)
theorem B340685 : Blo 147793 340685 := bbase (se 3 (by rfl) ⟨63878, by rfl⟩ : syracuseStep 340685 = 127757) (by norm_num)
theorem B340757 : Blo 147793 340757 := bbase (se 6 (by rfl) ⟨7986, by rfl⟩ : syracuseStep 340757 = 15973) (by norm_num)
theorem B504629 : Blo 147793 504629 := bbase (se 5 (by rfl) ⟨23654, by rfl⟩ : syracuseStep 504629 = 47309) (by norm_num)
theorem B340829 : Blo 147793 340829 := bbase (se 3 (by rfl) ⟨63905, by rfl⟩ : syracuseStep 340829 = 127811) (by norm_num)
theorem B340901 : Blo 147793 340901 := bbase (se 4 (by rfl) ⟨31959, by rfl⟩ : syracuseStep 340901 = 63919) (by norm_num)
theorem B340973 : Blo 147793 340973 := bbase (se 3 (by rfl) ⟨63932, by rfl⟩ : syracuseStep 340973 = 127865) (by norm_num)
theorem B341045 : Blo 147793 341045 := bbase (se 5 (by rfl) ⟨15986, by rfl⟩ : syracuseStep 341045 = 31973) (by norm_num)
theorem B341117 : Blo 147793 341117 := bbase (se 3 (by rfl) ⟨63959, by rfl⟩ : syracuseStep 341117 = 127919) (by norm_num)
theorem B341189 : Blo 147793 341189 := bbase (se 4 (by rfl) ⟨31986, by rfl⟩ : syracuseStep 341189 = 63973) (by norm_num)
theorem B505061 : Blo 147793 505061 := bbase (se 4 (by rfl) ⟨47349, by rfl⟩ : syracuseStep 505061 = 94699) (by norm_num)
theorem B341261 : Blo 147793 341261 := bbase (se 3 (by rfl) ⟨63986, by rfl⟩ : syracuseStep 341261 = 127973) (by norm_num)
theorem B341333 : Blo 147793 341333 := bbase (se 13 (by rfl) ⟨62, by rfl⟩ : syracuseStep 341333 = 125) (by norm_num)
theorem B341405 : Blo 147793 341405 := bbase (se 3 (by rfl) ⟨64013, by rfl⟩ : syracuseStep 341405 = 128027) (by norm_num)
theorem B341477 : Blo 147793 341477 := bbase (se 4 (by rfl) ⟨32013, by rfl⟩ : syracuseStep 341477 = 64027) (by norm_num)
theorem B374341 : Blo 147793 374341 := bbase (se 4 (by rfl) ⟨35094, by rfl⟩ : syracuseStep 374341 = 70189) (by norm_num)
theorem B308861 : Blo 147793 308861 := bbase (se 3 (by rfl) ⟨57911, by rfl⟩ : syracuseStep 308861 = 115823) (by norm_num)
theorem B505493 : Blo 147793 505493 := bbase (se 6 (by rfl) ⟨11847, by rfl⟩ : syracuseStep 505493 = 23695) (by norm_num)
theorem B407189 : Blo 147793 407189 := bbase (se 6 (by rfl) ⟨9543, by rfl⟩ : syracuseStep 407189 = 19087) (by norm_num)
theorem B210613 : Blo 147793 210613 := bbase (se 5 (by rfl) ⟨9872, by rfl⟩ : syracuseStep 210613 = 19745) (by norm_num)
theorem B374453 : Blo 147793 374453 := bbase (se 5 (by rfl) ⟨17552, by rfl⟩ : syracuseStep 374453 = 35105) (by norm_num)
theorem B767717 : Blo 147793 767717 := bbase (se 4 (by rfl) ⟨71973, by rfl⟩ : syracuseStep 767717 = 143947) (by norm_num)
theorem B571157 : Blo 147793 571157 := bbase (se 6 (by rfl) ⟨13386, by rfl⟩ : syracuseStep 571157 = 26773) (by norm_num)
theorem B276245 : Blo 147793 276245 := bbase (se 6 (by rfl) ⟨6474, by rfl⟩ : syracuseStep 276245 = 12949) (by norm_num)
theorem B374645 : Blo 147793 374645 := bbase (se 5 (by rfl) ⟨17561, by rfl⟩ : syracuseStep 374645 = 35123) (by norm_num)
theorem B604037 : Blo 147793 604037 := bbase (se 4 (by rfl) ⟨56628, by rfl⟩ : syracuseStep 604037 = 113257) (by norm_num)
theorem B178157 : Blo 147793 178157 := bbase (se 3 (by rfl) ⟨33404, by rfl⟩ : syracuseStep 178157 = 66809) (by norm_num)
theorem B571445 : Blo 147793 571445 := bbase (se 5 (by rfl) ⟨26786, by rfl⟩ : syracuseStep 571445 = 53573) (by norm_num)
theorem B505925 : Blo 147793 505925 := bbase (se 4 (by rfl) ⟨47430, by rfl⟩ : syracuseStep 505925 = 94861) (by norm_num)
theorem B374989 : Blo 147793 374989 := bbase (se 3 (by rfl) ⟨70310, by rfl⟩ : syracuseStep 374989 = 140621) (by norm_num)
theorem B211205 : Blo 147793 211205 := bbase (se 4 (by rfl) ⟨19800, by rfl⟩ : syracuseStep 211205 = 39601) (by norm_num)
theorem B178465 : Blo 147793 178465 := bbase (se 2 (by rfl) ⟨66924, by rfl⟩ : syracuseStep 178465 = 133849) (by norm_num)
theorem B637237 : Blo 147793 637237 := bbase (se 5 (by rfl) ⟨29870, by rfl⟩ : syracuseStep 637237 = 59741) (by norm_num)
theorem B375101 : Blo 147793 375101 := bbase (se 3 (by rfl) ⟨70331, by rfl⟩ : syracuseStep 375101 = 140663) (by norm_num)
theorem B211285 : Blo 147793 211285 := bbase (se 10 (by rfl) ⟨309, by rfl⟩ : syracuseStep 211285 = 619) (by norm_num)
theorem B211405 : Blo 147793 211405 := bbase (se 3 (by rfl) ⟨39638, by rfl⟩ : syracuseStep 211405 = 79277) (by norm_num)
theorem B506357 : Blo 147793 506357 := bbase (se 5 (by rfl) ⟨23735, by rfl⟩ : syracuseStep 506357 = 47471) (by norm_num)
theorem B178681 : Blo 147793 178681 := bbase (se 2 (by rfl) ⟨67005, by rfl⟩ : syracuseStep 178681 = 134011) (by norm_num)
theorem B375293 : Blo 147793 375293 := bbase (se 3 (by rfl) ⟨70367, by rfl⟩ : syracuseStep 375293 = 140735) (by norm_num)
theorem B211501 : Blo 147793 211501 := bbase (se 3 (by rfl) ⟨39656, by rfl⟩ : syracuseStep 211501 = 79313) (by norm_num)
theorem B375637 : Blo 147793 375637 := bbase (se 9 (by rfl) ⟨1100, by rfl⟩ : syracuseStep 375637 = 2201) (by norm_num)
theorem B473957 : Blo 147793 473957 := bbase (se 4 (by rfl) ⟨44433, by rfl⟩ : syracuseStep 473957 = 88867) (by norm_num)
theorem B342893 : Blo 147793 342893 := bbase (se 3 (by rfl) ⟨64292, by rfl⟩ : syracuseStep 342893 = 128585) (by norm_num)
theorem B506789 : Blo 147793 506789 := bbase (se 4 (by rfl) ⟨47511, by rfl⟩ : syracuseStep 506789 = 95023) (by norm_num)
theorem B375749 : Blo 147793 375749 := bbase (se 4 (by rfl) ⟨35226, by rfl⟩ : syracuseStep 375749 = 70453) (by norm_num)
theorem B1424405 : Blo 147793 1424405 := bbase (se 6 (by rfl) ⟨33384, by rfl⟩ : syracuseStep 1424405 = 66769) (by norm_num)
theorem B1227797 : Blo 147793 1227797 := bbase (se 6 (by rfl) ⟨28776, by rfl⟩ : syracuseStep 1227797 = 57553) (by norm_num)
theorem B211997 : Blo 147793 211997 := bbase (se 3 (by rfl) ⟨39749, by rfl⟩ : syracuseStep 211997 = 79499) (by norm_num)
theorem B179281 : Blo 147793 179281 := bbase (se 2 (by rfl) ⟨67230, by rfl⟩ : syracuseStep 179281 = 134461) (by norm_num)
theorem B375941 : Blo 147793 375941 := bbase (se 4 (by rfl) ⟨35244, by rfl⟩ : syracuseStep 375941 = 70489) (by norm_num)
theorem B572629 : Blo 147793 572629 := bbase (se 7 (by rfl) ⟨6710, by rfl⟩ : syracuseStep 572629 = 13421) (by norm_num)
theorem B343325 : Blo 147793 343325 := bbase (se 3 (by rfl) ⟨64373, by rfl⟩ : syracuseStep 343325 = 128747) (by norm_num)
theorem B507221 : Blo 147793 507221 := bbase (se 11 (by rfl) ⟨371, by rfl⟩ : syracuseStep 507221 = 743) (by norm_num)
theorem B1457621 : Blo 147793 1457621 := bbase (se 7 (by rfl) ⟨17081, by rfl⟩ : syracuseStep 1457621 = 34163) (by norm_num)
theorem B376285 : Blo 147793 376285 := bbase (se 3 (by rfl) ⟨70553, by rfl⟩ : syracuseStep 376285 = 141107) (by norm_num)
theorem B572933 : Blo 147793 572933 := bbase (se 4 (by rfl) ⟨53712, by rfl⟩ : syracuseStep 572933 = 107425) (by norm_num)
theorem B212549 : Blo 147793 212549 := bbase (se 4 (by rfl) ⟨19926, by rfl⟩ : syracuseStep 212549 = 39853) (by norm_num)
theorem B376397 : Blo 147793 376397 := bbase (se 3 (by rfl) ⟨70574, by rfl⟩ : syracuseStep 376397 = 141149) (by norm_num)
theorem B638725 : Blo 147793 638725 := bbase (se 4 (by rfl) ⟨59880, by rfl⟩ : syracuseStep 638725 = 119761) (by norm_num)
theorem B507653 : Blo 147793 507653 := bbase (se 4 (by rfl) ⟨47592, by rfl⟩ : syracuseStep 507653 = 95185) (by norm_num)
theorem B376589 : Blo 147793 376589 := bbase (se 3 (by rfl) ⟨70610, by rfl⟩ : syracuseStep 376589 = 141221) (by norm_num)
theorem B638741 : Blo 147793 638741 := bbase (se 6 (by rfl) ⟨14970, by rfl⟩ : syracuseStep 638741 = 29941) (by norm_num)
theorem B540437 : Blo 147793 540437 := bbase (se 6 (by rfl) ⟨12666, by rfl⟩ : syracuseStep 540437 = 25333) (by norm_num)
theorem B376933 : Blo 147793 376933 := bbase (se 4 (by rfl) ⟨35337, by rfl⟩ : syracuseStep 376933 = 70675) (by norm_num)
theorem B508085 : Blo 147793 508085 := bbase (se 5 (by rfl) ⟨23816, by rfl⟩ : syracuseStep 508085 = 47633) (by norm_num)
theorem B180425 : Blo 147793 180425 := bbase (se 2 (by rfl) ⟨67659, by rfl⟩ : syracuseStep 180425 = 135319) (by norm_num)
theorem B377045 : Blo 147793 377045 := bbase (se 7 (by rfl) ⟨4418, by rfl⟩ : syracuseStep 377045 = 8837) (by norm_num)
theorem B606437 : Blo 147793 606437 := bbase (se 4 (by rfl) ⟨56853, by rfl⟩ : syracuseStep 606437 = 113707) (by norm_num)
theorem B180473 : Blo 147793 180473 := bbase (se 2 (by rfl) ⟨67677, by rfl⟩ : syracuseStep 180473 = 135355) (by norm_num)
theorem B1294613 : Blo 147793 1294613 := bbase (se 6 (by rfl) ⟨30342, by rfl⟩ : syracuseStep 1294613 = 60685) (by norm_num)
theorem B213301 : Blo 147793 213301 := bbase (se 5 (by rfl) ⟨9998, by rfl⟩ : syracuseStep 213301 = 19997) (by norm_num)
theorem B180569 : Blo 147793 180569 := bbase (se 2 (by rfl) ⟨67713, by rfl⟩ : syracuseStep 180569 = 135427) (by norm_num)
theorem B377237 : Blo 147793 377237 := bbase (se 6 (by rfl) ⟨8841, by rfl⟩ : syracuseStep 377237 = 17683) (by norm_num)
theorem B180733 : Blo 147793 180733 := bbase (se 3 (by rfl) ⟨33887, by rfl⟩ : syracuseStep 180733 = 67775) (by norm_num)
theorem B508517 : Blo 147793 508517 := bbase (se 4 (by rfl) ⟨47673, by rfl⟩ : syracuseStep 508517 = 95347) (by norm_num)
theorem B180949 : Blo 147793 180949 := bbase (se 7 (by rfl) ⟨2120, by rfl⟩ : syracuseStep 180949 = 4241) (by norm_num)
theorem B377581 : Blo 147793 377581 := bbase (se 3 (by rfl) ⟨70796, by rfl⟩ : syracuseStep 377581 = 141593) (by norm_num)
theorem B377693 : Blo 147793 377693 := bbase (se 3 (by rfl) ⟨70817, by rfl⟩ : syracuseStep 377693 = 141635) (by norm_num)
theorem B181117 : Blo 147793 181117 := bbase (se 3 (by rfl) ⟨33959, by rfl⟩ : syracuseStep 181117 = 67919) (by norm_num)
theorem B345061 : Blo 147793 345061 := bbase (se 4 (by rfl) ⟨32349, by rfl⟩ : syracuseStep 345061 = 64699) (by norm_num)
theorem B508949 : Blo 147793 508949 := bbase (se 6 (by rfl) ⟨11928, by rfl⟩ : syracuseStep 508949 = 23857) (by norm_num)
theorem B377885 : Blo 147793 377885 := bbase (se 3 (by rfl) ⟨70853, by rfl⟩ : syracuseStep 377885 = 141707) (by norm_num)
theorem B574517 : Blo 147793 574517 := bbase (se 5 (by rfl) ⟨26930, by rfl⟩ : syracuseStep 574517 = 53861) (by norm_num)
theorem B214093 : Blo 147793 214093 := bbase (se 3 (by rfl) ⟨40142, by rfl⟩ : syracuseStep 214093 = 80285) (by norm_num)
theorem B181397 : Blo 147793 181397 := bbase (se 6 (by rfl) ⟨4251, by rfl⟩ : syracuseStep 181397 = 8503) (by norm_num)
theorem B1131893 : Blo 147793 1131893 := bbase (se 5 (by rfl) ⟨53057, by rfl⟩ : syracuseStep 1131893 = 106115) (by norm_num)
theorem B378229 : Blo 147793 378229 := bbase (se 5 (by rfl) ⟨17729, by rfl⟩ : syracuseStep 378229 = 35459) (by norm_num)
theorem B181645 : Blo 147793 181645 := bbase (se 3 (by rfl) ⟨34058, by rfl⟩ : syracuseStep 181645 = 68117) (by norm_num)
theorem B607637 : Blo 147793 607637 := bbase (se 6 (by rfl) ⟨14241, by rfl⟩ : syracuseStep 607637 = 28483) (by norm_num)
theorem B214429 : Blo 147793 214429 := bbase (se 3 (by rfl) ⟨40205, by rfl⟩ : syracuseStep 214429 = 80411) (by norm_num)
theorem B1295797 : Blo 147793 1295797 := bbase (se 5 (by rfl) ⟨60740, by rfl⟩ : syracuseStep 1295797 = 121481) (by norm_num)
theorem B509381 : Blo 147793 509381 := bbase (se 4 (by rfl) ⟨47754, by rfl⟩ : syracuseStep 509381 = 95509) (by norm_num)
theorem B378341 : Blo 147793 378341 := bbase (se 4 (by rfl) ⟨35469, by rfl⟩ : syracuseStep 378341 = 70939) (by norm_num)
theorem B476725 : Blo 147793 476725 := bbase (se 5 (by rfl) ⟨22346, by rfl⟩ : syracuseStep 476725 = 44693) (by norm_num)
theorem B575045 : Blo 147793 575045 := bbase (se 4 (by rfl) ⟨53910, by rfl⟩ : syracuseStep 575045 = 107821) (by norm_num)
theorem B214645 : Blo 147793 214645 := bbase (se 5 (by rfl) ⟨10061, by rfl⟩ : syracuseStep 214645 = 20123) (by norm_num)
theorem B378533 : Blo 147793 378533 := bbase (se 4 (by rfl) ⟨35487, by rfl⟩ : syracuseStep 378533 = 70975) (by norm_num)
theorem B411493 : Blo 147793 411493 := bbase (se 4 (by rfl) ⟨38577, by rfl⟩ : syracuseStep 411493 = 77155) (by norm_num)
theorem B575333 : Blo 147793 575333 := bbase (se 4 (by rfl) ⟨53937, by rfl⟩ : syracuseStep 575333 = 107875) (by norm_num)
theorem B509813 : Blo 147793 509813 := bbase (se 5 (by rfl) ⟨23897, by rfl⟩ : syracuseStep 509813 = 47795) (by norm_num)
theorem B542629 : Blo 147793 542629 := bbase (se 4 (by rfl) ⟨50871, by rfl⟩ : syracuseStep 542629 = 101743) (by norm_num)
theorem B640997 : Blo 147793 640997 := bbase (se 4 (by rfl) ⟨60093, by rfl⟩ : syracuseStep 640997 = 120187) (by norm_num)
theorem B215021 : Blo 147793 215021 := bbase (se 3 (by rfl) ⟨40316, by rfl⟩ : syracuseStep 215021 = 80633) (by norm_num)
theorem B870389 : Blo 147793 870389 := bbase (se 5 (by rfl) ⟨40799, by rfl⟩ : syracuseStep 870389 = 81599) (by norm_num)
theorem B378877 : Blo 147793 378877 := bbase (se 3 (by rfl) ⟨71039, by rfl⟩ : syracuseStep 378877 = 142079) (by norm_num)
theorem B280597 : Blo 147793 280597 := bbase (se 6 (by rfl) ⟨6576, by rfl⟩ : syracuseStep 280597 = 13153) (by norm_num)
theorem B378989 : Blo 147793 378989 := bbase (se 3 (by rfl) ⟨71060, by rfl⟩ : syracuseStep 378989 = 142121) (by norm_num)
theorem B280741 : Blo 147793 280741 := bbase (se 4 (by rfl) ⟨26319, by rfl⟩ : syracuseStep 280741 = 52639) (by norm_num)
theorem B510245 : Blo 147793 510245 := bbase (se 4 (by rfl) ⟨47835, by rfl⟩ : syracuseStep 510245 = 95671) (by norm_num)
theorem B379181 : Blo 147793 379181 := bbase (se 3 (by rfl) ⟨71096, by rfl⟩ : syracuseStep 379181 = 142193) (by norm_num)
theorem B280901 : Blo 147793 280901 := bbase (se 4 (by rfl) ⟨26334, by rfl⟩ : syracuseStep 280901 = 52669) (by norm_num)
theorem B281045 : Blo 147793 281045 := bbase (se 7 (by rfl) ⟨3293, by rfl⟩ : syracuseStep 281045 = 6587) (by norm_num)
theorem B379525 : Blo 147793 379525 := bbase (se 4 (by rfl) ⟨35580, by rfl⟩ : syracuseStep 379525 = 71161) (by norm_num)
theorem B1067701 : Blo 147793 1067701 := bbase (se 5 (by rfl) ⟨50048, by rfl⟩ : syracuseStep 1067701 = 100097) (by norm_num)
theorem B510677 : Blo 147793 510677 := bbase (se 7 (by rfl) ⟨5984, by rfl⟩ : syracuseStep 510677 = 11969) (by norm_num)
theorem B281333 : Blo 147793 281333 := bbase (se 5 (by rfl) ⟨13187, by rfl⟩ : syracuseStep 281333 = 26375) (by norm_num)
theorem B379637 : Blo 147793 379637 := bbase (se 5 (by rfl) ⟨17795, by rfl⟩ : syracuseStep 379637 = 35591) (by norm_num)
theorem B150341 : Blo 147793 150341 := bbase (se 4 (by rfl) ⟨14094, by rfl⟩ : syracuseStep 150341 = 28189) (by norm_num)
theorem B281485 : Blo 147793 281485 := bbase (se 3 (by rfl) ⟨52778, by rfl⟩ : syracuseStep 281485 = 105557) (by norm_num)
theorem B379829 : Blo 147793 379829 := bbase (se 5 (by rfl) ⟨17804, by rfl⟩ : syracuseStep 379829 = 35609) (by norm_num)
theorem B511109 : Blo 147793 511109 := bbase (se 4 (by rfl) ⟨47916, by rfl⟩ : syracuseStep 511109 = 95833) (by norm_num)
theorem B150665 : Blo 147793 150665 := bbase (se 2 (by rfl) ⟨56499, by rfl⟩ : syracuseStep 150665 = 112999) (by norm_num)
theorem B183433 : Blo 147793 183433 := bbase (se 2 (by rfl) ⟨68787, by rfl⟩ : syracuseStep 183433 = 137575) (by norm_num)
theorem B183461 : Blo 147793 183461 := bbase (se 4 (by rfl) ⟨17199, by rfl⟩ : syracuseStep 183461 = 34399) (by norm_num)
theorem B281789 : Blo 147793 281789 := bbase (se 3 (by rfl) ⟨52835, by rfl⟩ : syracuseStep 281789 = 105671) (by norm_num)
theorem B380173 : Blo 147793 380173 := bbase (se 3 (by rfl) ⟨71282, by rfl⟩ : syracuseStep 380173 = 142565) (by norm_num)
theorem B380285 : Blo 147793 380285 := bbase (se 3 (by rfl) ⟨71303, by rfl⟩ : syracuseStep 380285 = 142607) (by norm_num)
theorem B151025 : Blo 147793 151025 := bbase (se 2 (by rfl) ⟨56634, by rfl⟩ : syracuseStep 151025 = 113269) (by norm_num)
theorem B511541 : Blo 147793 511541 := bbase (se 5 (by rfl) ⟨23978, by rfl⟩ : syracuseStep 511541 = 47957) (by norm_num)
theorem B380477 : Blo 147793 380477 := bbase (se 3 (by rfl) ⟨71339, by rfl⟩ : syracuseStep 380477 = 142679) (by norm_num)
theorem B249493 : Blo 147793 249493 := bbase (se 6 (by rfl) ⟨5847, by rfl⟩ : syracuseStep 249493 = 11695) (by norm_num)
theorem B249581 : Blo 147793 249581 := bbase (se 3 (by rfl) ⟨46796, by rfl⟩ : syracuseStep 249581 = 93593) (by norm_num)
theorem B249709 : Blo 147793 249709 := bbase (se 3 (by rfl) ⟨46820, by rfl⟩ : syracuseStep 249709 = 93641) (by norm_num)
theorem B380821 : Blo 147793 380821 := bbase (se 6 (by rfl) ⟨8925, by rfl⟩ : syracuseStep 380821 = 17851) (by norm_num)
theorem B282533 : Blo 147793 282533 := bbase (se 4 (by rfl) ⟨26487, by rfl⟩ : syracuseStep 282533 = 52975) (by norm_num)
theorem B282541 : Blo 147793 282541 := bbase (se 3 (by rfl) ⟨52976, by rfl⟩ : syracuseStep 282541 = 105953) (by norm_num)
theorem B249797 : Blo 147793 249797 := bbase (se 4 (by rfl) ⟨23418, by rfl⟩ : syracuseStep 249797 = 46837) (by norm_num)
theorem B511973 : Blo 147793 511973 := bbase (se 4 (by rfl) ⟨47997, by rfl⟩ : syracuseStep 511973 = 95995) (by norm_num)
theorem B380933 : Blo 147793 380933 := bbase (se 4 (by rfl) ⟨35712, by rfl⟩ : syracuseStep 380933 = 71425) (by norm_num)
theorem B282685 : Blo 147793 282685 := bbase (se 3 (by rfl) ⟨53003, by rfl⟩ : syracuseStep 282685 = 106007) (by norm_num)
theorem B249925 : Blo 147793 249925 := bbase (se 4 (by rfl) ⟨23430, by rfl⟩ : syracuseStep 249925 = 46861) (by norm_num)
theorem B413797 : Blo 147793 413797 := bbase (se 4 (by rfl) ⟨38793, by rfl⟩ : syracuseStep 413797 = 77587) (by norm_num)
theorem B2445461 : Blo 147793 2445461 := bbase (se 6 (by rfl) ⟨57315, by rfl⟩ : syracuseStep 2445461 = 114631) (by norm_num)
theorem B250013 : Blo 147793 250013 := bbase (se 3 (by rfl) ⟨46877, by rfl⟩ : syracuseStep 250013 = 93755) (by norm_num)
theorem B381125 : Blo 147793 381125 := bbase (se 4 (by rfl) ⟨35730, by rfl⟩ : syracuseStep 381125 = 71461) (by norm_num)
theorem B282845 : Blo 147793 282845 := bbase (se 3 (by rfl) ⟨53033, by rfl⟩ : syracuseStep 282845 = 106067) (by norm_num)
theorem B250141 : Blo 147793 250141 := bbase (se 3 (by rfl) ⟨46901, by rfl⟩ : syracuseStep 250141 = 93803) (by norm_num)
theorem B151877 : Blo 147793 151877 := bbase (se 4 (by rfl) ⟨14238, by rfl⟩ : syracuseStep 151877 = 28477) (by norm_num)
theorem B282989 : Blo 147793 282989 := bbase (se 3 (by rfl) ⟨53060, by rfl⟩ : syracuseStep 282989 = 106121) (by norm_num)
theorem B250229 : Blo 147793 250229 := bbase (se 5 (by rfl) ⟨11729, by rfl⟩ : syracuseStep 250229 = 23459) (by norm_num)
theorem B479621 : Blo 147793 479621 := bbase (se 4 (by rfl) ⟨44964, by rfl⟩ : syracuseStep 479621 = 89929) (by norm_num)
theorem B250357 : Blo 147793 250357 := bbase (se 5 (by rfl) ⟨11735, by rfl⟩ : syracuseStep 250357 = 23471) (by norm_num)
theorem B807413 : Blo 147793 807413 := bbase (se 5 (by rfl) ⟨37847, by rfl⟩ : syracuseStep 807413 = 75695) (by norm_num)
theorem B283133 : Blo 147793 283133 := bbase (se 3 (by rfl) ⟨53087, by rfl⟩ : syracuseStep 283133 = 106175) (by norm_num)
theorem B381469 : Blo 147793 381469 := bbase (se 3 (by rfl) ⟨71525, by rfl⟩ : syracuseStep 381469 = 143051) (by norm_num)
theorem B250445 : Blo 147793 250445 := bbase (se 3 (by rfl) ⟨46958, by rfl⟩ : syracuseStep 250445 = 93917) (by norm_num)
theorem B152177 : Blo 147793 152177 := bbase (se 2 (by rfl) ⟨57066, by rfl⟩ : syracuseStep 152177 = 114133) (by norm_num)
theorem B283277 : Blo 147793 283277 := bbase (se 3 (by rfl) ⟨53114, by rfl⟩ : syracuseStep 283277 = 106229) (by norm_num)
theorem B381581 : Blo 147793 381581 := bbase (se 3 (by rfl) ⟨71546, by rfl⟩ : syracuseStep 381581 = 143093) (by norm_num)
theorem B348845 : Blo 147793 348845 := bbase (se 3 (by rfl) ⟨65408, by rfl⟩ : syracuseStep 348845 = 130817) (by norm_num)
theorem B250573 : Blo 147793 250573 := bbase (se 3 (by rfl) ⟨46982, by rfl⟩ : syracuseStep 250573 = 93965) (by norm_num)
theorem B250661 : Blo 147793 250661 := bbase (se 4 (by rfl) ⟨23499, by rfl⟩ : syracuseStep 250661 = 46999) (by norm_num)
theorem B283429 : Blo 147793 283429 := bbase (se 4 (by rfl) ⟨26571, by rfl⟩ : syracuseStep 283429 = 53143) (by norm_num)
theorem B381773 : Blo 147793 381773 := bbase (se 3 (by rfl) ⟨71582, by rfl⟩ : syracuseStep 381773 = 143165) (by norm_num)
theorem B316261 : Blo 147793 316261 := bbase (se 4 (by rfl) ⟨29649, by rfl⟩ : syracuseStep 316261 = 59299) (by norm_num)
theorem B152437 : Blo 147793 152437 := bbase (se 5 (by rfl) ⟨7145, by rfl⟩ : syracuseStep 152437 = 14291) (by norm_num)
theorem B250789 : Blo 147793 250789 := bbase (se 4 (by rfl) ⟨23511, by rfl⟩ : syracuseStep 250789 = 47023) (by norm_num)
theorem B316381 : Blo 147793 316381 := bbase (se 3 (by rfl) ⟨59321, by rfl⟩ : syracuseStep 316381 = 118643) (by norm_num)
theorem B250877 : Blo 147793 250877 := bbase (se 3 (by rfl) ⟨47039, by rfl⟩ : syracuseStep 250877 = 94079) (by norm_num)
theorem B283733 : Blo 147793 283733 := bbase (se 8 (by rfl) ⟨1662, by rfl⟩ : syracuseStep 283733 = 3325) (by norm_num)
theorem B251005 : Blo 147793 251005 := bbase (se 3 (by rfl) ⟨47063, by rfl⟩ : syracuseStep 251005 = 94127) (by norm_num)
theorem B382117 : Blo 147793 382117 := bbase (se 4 (by rfl) ⟨35823, by rfl⟩ : syracuseStep 382117 = 71647) (by norm_num)
theorem B152777 : Blo 147793 152777 := bbase (se 2 (by rfl) ⟨57291, by rfl⟩ : syracuseStep 152777 = 114583) (by norm_num)
theorem B251093 : Blo 147793 251093 := bbase (se 7 (by rfl) ⟨2942, by rfl⟩ : syracuseStep 251093 = 5885) (by norm_num)
theorem B316637 : Blo 147793 316637 := bbase (se 3 (by rfl) ⟨59369, by rfl⟩ : syracuseStep 316637 = 118739) (by norm_num)
theorem B382229 : Blo 147793 382229 := bbase (se 6 (by rfl) ⟨8958, by rfl⟩ : syracuseStep 382229 = 17917) (by norm_num)
theorem B251221 : Blo 147793 251221 := bbase (se 15 (by rfl) ⟨11, by rfl⟩ : syracuseStep 251221 = 23) (by norm_num)
theorem B251309 : Blo 147793 251309 := bbase (se 3 (by rfl) ⟨47120, by rfl⟩ : syracuseStep 251309 = 94241) (by norm_num)
theorem B382421 : Blo 147793 382421 := bbase (se 7 (by rfl) ⟨4481, by rfl⟩ : syracuseStep 382421 = 8963) (by norm_num)
theorem B153101 : Blo 147793 153101 := bbase (se 3 (by rfl) ⟨28706, by rfl⟩ : syracuseStep 153101 = 57413) (by norm_num)
theorem B251437 : Blo 147793 251437 := bbase (se 3 (by rfl) ⟨47144, by rfl⟩ : syracuseStep 251437 = 94289) (by norm_num)
theorem B874037 : Blo 147793 874037 := bbase (se 5 (by rfl) ⟨40970, by rfl⟩ : syracuseStep 874037 = 81941) (by norm_num)
theorem B251525 : Blo 147793 251525 := bbase (se 4 (by rfl) ⟨23580, by rfl⟩ : syracuseStep 251525 = 47161) (by norm_num)
theorem B251653 : Blo 147793 251653 := bbase (se 4 (by rfl) ⟨23592, by rfl⟩ : syracuseStep 251653 = 47185) (by norm_num)
theorem B382765 : Blo 147793 382765 := bbase (se 3 (by rfl) ⟨71768, by rfl⟩ : syracuseStep 382765 = 143537) (by norm_num)
theorem B284485 : Blo 147793 284485 := bbase (se 4 (by rfl) ⟨26670, by rfl⟩ : syracuseStep 284485 = 53341) (by norm_num)
theorem B251741 : Blo 147793 251741 := bbase (se 3 (by rfl) ⟨47201, by rfl⟩ : syracuseStep 251741 = 94403) (by norm_num)
theorem B382877 : Blo 147793 382877 := bbase (se 3 (by rfl) ⟨71789, by rfl⟩ : syracuseStep 382877 = 143579) (by norm_num)
theorem B645029 : Blo 147793 645029 := bbase (se 4 (by rfl) ⟨60471, by rfl⟩ : syracuseStep 645029 = 120943) (by norm_num)
theorem B284629 : Blo 147793 284629 := bbase (se 7 (by rfl) ⟨3335, by rfl⟩ : syracuseStep 284629 = 6671) (by norm_num)
theorem B251869 : Blo 147793 251869 := bbase (se 3 (by rfl) ⟨47225, by rfl⟩ : syracuseStep 251869 = 94451) (by norm_num)
theorem B251957 : Blo 147793 251957 := bbase (se 5 (by rfl) ⟨11810, by rfl⟩ : syracuseStep 251957 = 23621) (by norm_num)
theorem B710741 : Blo 147793 710741 := bbase (se 8 (by rfl) ⟨4164, by rfl⟩ : syracuseStep 710741 = 8329) (by norm_num)
theorem B317525 : Blo 147793 317525 := bbase (se 8 (by rfl) ⟨1860, by rfl⟩ : syracuseStep 317525 = 3721) (by norm_num)
theorem B383069 : Blo 147793 383069 := bbase (se 3 (by rfl) ⟨71825, by rfl⟩ : syracuseStep 383069 = 143651) (by norm_num)
theorem B284789 : Blo 147793 284789 := bbase (se 5 (by rfl) ⟨13349, by rfl⟩ : syracuseStep 284789 = 26699) (by norm_num)
theorem B252029 : Blo 147793 252029 := bbase (se 3 (by rfl) ⟨47255, by rfl⟩ : syracuseStep 252029 = 94511) (by norm_num)
theorem B252085 : Blo 147793 252085 := bbase (se 5 (by rfl) ⟨11816, by rfl⟩ : syracuseStep 252085 = 23633) (by norm_num)
theorem B547013 : Blo 147793 547013 := bbase (se 4 (by rfl) ⟨51282, by rfl⟩ : syracuseStep 547013 = 102565) (by norm_num)
theorem B1038581 : Blo 147793 1038581 := bbase (se 5 (by rfl) ⟨48683, by rfl⟩ : syracuseStep 1038581 = 97367) (by norm_num)
theorem B284933 : Blo 147793 284933 := bbase (se 4 (by rfl) ⟨26712, by rfl⟩ : syracuseStep 284933 = 53425) (by norm_num)
theorem B252173 : Blo 147793 252173 := bbase (se 3 (by rfl) ⟨47282, by rfl⟩ : syracuseStep 252173 = 94565) (by norm_num)
theorem B317765 : Blo 147793 317765 := bbase (se 4 (by rfl) ⟨29790, by rfl⟩ : syracuseStep 317765 = 59581) (by norm_num)
theorem B252301 : Blo 147793 252301 := bbase (se 3 (by rfl) ⟨47306, by rfl⟩ : syracuseStep 252301 = 94613) (by norm_num)
theorem B383413 : Blo 147793 383413 := bbase (se 5 (by rfl) ⟨17972, by rfl⟩ : syracuseStep 383413 = 35945) (by norm_num)
theorem B252389 : Blo 147793 252389 := bbase (se 4 (by rfl) ⟨23661, by rfl⟩ : syracuseStep 252389 = 47323) (by norm_num)
theorem B186869 : Blo 147793 186869 := bbase (se 5 (by rfl) ⟨8759, by rfl⟩ : syracuseStep 186869 = 17519) (by norm_num)
theorem B285221 : Blo 147793 285221 := bbase (se 4 (by rfl) ⟨26739, by rfl⟩ : syracuseStep 285221 = 53479) (by norm_num)
theorem B383525 : Blo 147793 383525 := bbase (se 4 (by rfl) ⟨35955, by rfl⟩ : syracuseStep 383525 = 71911) (by norm_num)
theorem B252517 : Blo 147793 252517 := bbase (se 4 (by rfl) ⟨23673, by rfl⟩ : syracuseStep 252517 = 47347) (by norm_num)
theorem B252605 : Blo 147793 252605 := bbase (se 3 (by rfl) ⟨47363, by rfl⟩ : syracuseStep 252605 = 94727) (by norm_num)
theorem B285373 : Blo 147793 285373 := bbase (se 3 (by rfl) ⟨53507, by rfl⟩ : syracuseStep 285373 = 107015) (by norm_num)
theorem B187105 : Blo 147793 187105 := bbase (se 2 (by rfl) ⟨70164, by rfl⟩ : syracuseStep 187105 = 140329) (by norm_num)
theorem B383717 : Blo 147793 383717 := bbase (se 4 (by rfl) ⟨35973, by rfl⟩ : syracuseStep 383717 = 71947) (by norm_num)
theorem B318269 : Blo 147793 318269 := bbase (se 3 (by rfl) ⟨59675, by rfl⟩ : syracuseStep 318269 = 119351) (by norm_num)
theorem B252733 : Blo 147793 252733 := bbase (se 3 (by rfl) ⟨47387, by rfl⟩ : syracuseStep 252733 = 94775) (by norm_num)
theorem B187201 : Blo 147793 187201 := bbase (se 2 (by rfl) ⟨70200, by rfl⟩ : syracuseStep 187201 = 140401) (by norm_num)
theorem B318277 : Blo 147793 318277 := bbase (se 4 (by rfl) ⟨29838, by rfl⟩ : syracuseStep 318277 = 59677) (by norm_num)
theorem B252821 : Blo 147793 252821 := bbase (se 6 (by rfl) ⟨5925, by rfl⟩ : syracuseStep 252821 = 11851) (by norm_num)
theorem B187373 : Blo 147793 187373 := bbase (se 3 (by rfl) ⟨35132, by rfl⟩ : syracuseStep 187373 = 70265) (by norm_num)
theorem B285677 : Blo 147793 285677 := bbase (se 3 (by rfl) ⟨53564, by rfl⟩ : syracuseStep 285677 = 107129) (by norm_num)
theorem B252949 : Blo 147793 252949 := bbase (se 6 (by rfl) ⟨5928, by rfl⟩ : syracuseStep 252949 = 11857) (by norm_num)
theorem B187429 : Blo 147793 187429 := bbase (se 4 (by rfl) ⟨17571, by rfl⟩ : syracuseStep 187429 = 35143) (by norm_num)
theorem B384061 : Blo 147793 384061 := bbase (se 3 (by rfl) ⟨72011, by rfl⟩ : syracuseStep 384061 = 144023) (by norm_num)
theorem B253037 : Blo 147793 253037 := bbase (se 3 (by rfl) ⟨47444, by rfl⟩ : syracuseStep 253037 = 94889) (by norm_num)
theorem B187525 : Blo 147793 187525 := bbase (se 4 (by rfl) ⟨17580, by rfl⟩ : syracuseStep 187525 = 35161) (by norm_num)
theorem B384173 : Blo 147793 384173 := bbase (se 3 (by rfl) ⟨72032, by rfl⟩ : syracuseStep 384173 = 144065) (by norm_num)
theorem B154829 : Blo 147793 154829 := bbase (se 3 (by rfl) ⟨29030, by rfl⟩ : syracuseStep 154829 = 58061) (by norm_num)
theorem B253165 : Blo 147793 253165 := bbase (se 3 (by rfl) ⟨47468, by rfl⟩ : syracuseStep 253165 = 94937) (by norm_num)
theorem B187697 : Blo 147793 187697 := bbase (se 2 (by rfl) ⟨70386, by rfl⟩ : syracuseStep 187697 = 140773) (by norm_num)
theorem B253253 : Blo 147793 253253 := bbase (se 4 (by rfl) ⟨23742, by rfl⟩ : syracuseStep 253253 = 47485) (by norm_num)
theorem B187753 : Blo 147793 187753 := bbase (se 2 (by rfl) ⟨70407, by rfl⟩ : syracuseStep 187753 = 140815) (by norm_num)
theorem B253381 : Blo 147793 253381 := bbase (se 4 (by rfl) ⟨23754, by rfl⟩ : syracuseStep 253381 = 47509) (by norm_num)
theorem B187849 : Blo 147793 187849 := bbase (se 2 (by rfl) ⟨70443, by rfl⟩ : syracuseStep 187849 = 140887) (by norm_num)
theorem B482773 : Blo 147793 482773 := bbase (se 7 (by rfl) ⟨5657, by rfl⟩ : syracuseStep 482773 = 11315) (by norm_num)
theorem B712165 : Blo 147793 712165 := bbase (se 4 (by rfl) ⟨66765, by rfl⟩ : syracuseStep 712165 = 133531) (by norm_num)
theorem B777701 : Blo 147793 777701 := bbase (se 4 (by rfl) ⟨72909, by rfl⟩ : syracuseStep 777701 = 145819) (by norm_num)
theorem B810485 : Blo 147793 810485 := bbase (se 5 (by rfl) ⟨37991, by rfl⟩ : syracuseStep 810485 = 75983) (by norm_num)
theorem B253469 : Blo 147793 253469 := bbase (se 3 (by rfl) ⟨47525, by rfl⟩ : syracuseStep 253469 = 95051) (by norm_num)
theorem B843317 : Blo 147793 843317 := bbase (se 5 (by rfl) ⟨39530, by rfl⟩ : syracuseStep 843317 = 79061) (by norm_num)
theorem B188021 : Blo 147793 188021 := bbase (se 5 (by rfl) ⟨8813, by rfl⟩ : syracuseStep 188021 = 17627) (by norm_num)
theorem B646805 : Blo 147793 646805 := bbase (se 6 (by rfl) ⟨15159, by rfl⟩ : syracuseStep 646805 = 30319) (by norm_num)
theorem B253597 : Blo 147793 253597 := bbase (se 3 (by rfl) ⟨47549, by rfl⟩ : syracuseStep 253597 = 95099) (by norm_num)
theorem B188077 : Blo 147793 188077 := bbase (se 3 (by rfl) ⟨35264, by rfl⟩ : syracuseStep 188077 = 70529) (by norm_num)
theorem B286429 : Blo 147793 286429 := bbase (se 3 (by rfl) ⟨53705, by rfl⟩ : syracuseStep 286429 = 107411) (by norm_num)
theorem B253685 : Blo 147793 253685 := bbase (se 5 (by rfl) ⟨11891, by rfl⟩ : syracuseStep 253685 = 23783) (by norm_num)
theorem B188173 : Blo 147793 188173 := bbase (se 3 (by rfl) ⟨35282, by rfl⟩ : syracuseStep 188173 = 70565) (by norm_num)
theorem B286573 : Blo 147793 286573 := bbase (se 3 (by rfl) ⟨53732, by rfl⟩ : syracuseStep 286573 = 107465) (by norm_num)
theorem B253813 : Blo 147793 253813 := bbase (se 5 (by rfl) ⟨11897, by rfl⟩ : syracuseStep 253813 = 23795) (by norm_num)
theorem B286621 : Blo 147793 286621 := bbase (se 3 (by rfl) ⟨53741, by rfl⟩ : syracuseStep 286621 = 107483) (by norm_num)
theorem B319405 : Blo 147793 319405 := bbase (se 3 (by rfl) ⟨59888, by rfl⟩ : syracuseStep 319405 = 119777) (by norm_num)
theorem B188345 : Blo 147793 188345 := bbase (se 2 (by rfl) ⟨70629, by rfl⟩ : syracuseStep 188345 = 141259) (by norm_num)
theorem B253901 : Blo 147793 253901 := bbase (se 3 (by rfl) ⟨47606, by rfl⟩ : syracuseStep 253901 = 95213) (by norm_num)
theorem B188401 : Blo 147793 188401 := bbase (se 2 (by rfl) ⟨70650, by rfl⟩ : syracuseStep 188401 = 141301) (by norm_num)
theorem B286733 : Blo 147793 286733 := bbase (se 3 (by rfl) ⟨53762, by rfl⟩ : syracuseStep 286733 = 107525) (by norm_num)
theorem B254029 : Blo 147793 254029 := bbase (se 3 (by rfl) ⟨47630, by rfl⟩ : syracuseStep 254029 = 95261) (by norm_num)
theorem B188497 : Blo 147793 188497 := bbase (se 2 (by rfl) ⟨70686, by rfl⟩ : syracuseStep 188497 = 141373) (by norm_num)
theorem B286805 : Blo 147793 286805 := bbase (se 8 (by rfl) ⟨1680, by rfl⟩ : syracuseStep 286805 = 3361) (by norm_num)
theorem B647317 : Blo 147793 647317 := bbase (se 6 (by rfl) ⟨15171, by rfl⟩ : syracuseStep 647317 = 30343) (by norm_num)
theorem B286877 : Blo 147793 286877 := bbase (se 3 (by rfl) ⟨53789, by rfl⟩ : syracuseStep 286877 = 107579) (by norm_num)
theorem B254117 : Blo 147793 254117 := bbase (se 4 (by rfl) ⟨23823, by rfl⟩ : syracuseStep 254117 = 47647) (by norm_num)
theorem B188669 : Blo 147793 188669 := bbase (se 3 (by rfl) ⟨35375, by rfl⟩ : syracuseStep 188669 = 70751) (by norm_num)
theorem B319781 : Blo 147793 319781 := bbase (se 4 (by rfl) ⟨29979, by rfl⟩ : syracuseStep 319781 = 59959) (by norm_num)
theorem B254245 : Blo 147793 254245 := bbase (se 4 (by rfl) ⟨23835, by rfl⟩ : syracuseStep 254245 = 47671) (by norm_num)
theorem B287021 : Blo 147793 287021 := bbase (se 3 (by rfl) ⟨53816, by rfl⟩ : syracuseStep 287021 = 107633) (by norm_num)
theorem B188725 : Blo 147793 188725 := bbase (se 5 (by rfl) ⟨8846, by rfl⟩ : syracuseStep 188725 = 17693) (by norm_num)
theorem B581957 : Blo 147793 581957 := bbase (se 4 (by rfl) ⟨54558, by rfl⟩ : syracuseStep 581957 = 109117) (by norm_num)
theorem B254333 : Blo 147793 254333 := bbase (se 3 (by rfl) ⟨47687, by rfl⟩ : syracuseStep 254333 = 95375) (by norm_num)
theorem B188821 : Blo 147793 188821 := bbase (se 6 (by rfl) ⟨4425, by rfl⟩ : syracuseStep 188821 = 8851) (by norm_num)
theorem B287165 : Blo 147793 287165 := bbase (se 3 (by rfl) ⟨53843, by rfl⟩ : syracuseStep 287165 = 107687) (by norm_num)
theorem B778693 : Blo 147793 778693 := bbase (se 4 (by rfl) ⟨73002, by rfl⟩ : syracuseStep 778693 = 146005) (by norm_num)
theorem B221693 : Blo 147793 221693 := bbase (se 3 (by rfl) ⟨41567, by rfl⟩ : syracuseStep 221693 = 83135) (by norm_num)
theorem B254461 : Blo 147793 254461 := bbase (se 3 (by rfl) ⟨47711, by rfl⟩ : syracuseStep 254461 = 95423) (by norm_num)
theorem B221717 : Blo 147793 221717 := bbase (se 6 (by rfl) ⟨5196, by rfl⟩ : syracuseStep 221717 = 10393) (by norm_num)
theorem B1925653 : Blo 147793 1925653 := bbase (se 6 (by rfl) ⟨45132, by rfl⟩ : syracuseStep 1925653 = 90265) (by norm_num)
theorem B221741 : Blo 147793 221741 := bbase (se 3 (by rfl) ⟨41576, by rfl⟩ : syracuseStep 221741 = 83153) (by norm_num)
theorem B188993 : Blo 147793 188993 := bbase (se 2 (by rfl) ⟨70872, by rfl⟩ : syracuseStep 188993 = 141745) (by norm_num)
theorem B221765 : Blo 147793 221765 := bbase (se 4 (by rfl) ⟨20790, by rfl⟩ : syracuseStep 221765 = 41581) (by norm_num)
theorem B254549 : Blo 147793 254549 := bbase (se 8 (by rfl) ⟨1491, by rfl⟩ : syracuseStep 254549 = 2983) (by norm_num)
theorem B287317 : Blo 147793 287317 := bbase (se 8 (by rfl) ⟨1683, by rfl⟩ : syracuseStep 287317 = 3367) (by norm_num)
theorem B221789 : Blo 147793 221789 := bbase (se 3 (by rfl) ⟨41585, by rfl⟩ : syracuseStep 221789 = 83171) (by norm_num)
theorem B221813 : Blo 147793 221813 := bbase (se 5 (by rfl) ⟨10397, by rfl⟩ : syracuseStep 221813 = 20795) (by norm_num)
theorem B647797 : Blo 147793 647797 := bbase (se 5 (by rfl) ⟨30365, by rfl⟩ : syracuseStep 647797 = 60731) (by norm_num)
theorem B189049 : Blo 147793 189049 := bbase (se 2 (by rfl) ⟨70893, by rfl⟩ : syracuseStep 189049 = 141787) (by norm_num)
theorem B221837 : Blo 147793 221837 := bbase (se 3 (by rfl) ⟨41594, by rfl⟩ : syracuseStep 221837 = 83189) (by norm_num)
theorem B221861 : Blo 147793 221861 := bbase (se 4 (by rfl) ⟨20799, by rfl⟩ : syracuseStep 221861 = 41599) (by norm_num)
theorem B221869 : Blo 147793 221869 := bbase (se 3 (by rfl) ⟨41600, by rfl⟩ : syracuseStep 221869 = 83201) (by norm_num)
theorem B221885 : Blo 147793 221885 := bbase (se 3 (by rfl) ⟨41603, by rfl⟩ : syracuseStep 221885 = 83207) (by norm_num)
theorem B221909 : Blo 147793 221909 := bbase (se 7 (by rfl) ⟨2600, by rfl⟩ : syracuseStep 221909 = 5201) (by norm_num)
theorem B254677 : Blo 147793 254677 := bbase (se 7 (by rfl) ⟨2984, by rfl⟩ : syracuseStep 254677 = 5969) (by norm_num)
theorem B189145 : Blo 147793 189145 := bbase (se 2 (by rfl) ⟨70929, by rfl⟩ : syracuseStep 189145 = 141859) (by norm_num)
theorem B221933 : Blo 147793 221933 := bbase (se 3 (by rfl) ⟨41612, by rfl⟩ : syracuseStep 221933 = 83225) (by norm_num)
theorem B221957 : Blo 147793 221957 := bbase (se 4 (by rfl) ⟨20808, by rfl⟩ : syracuseStep 221957 = 41617) (by norm_num)
theorem B221981 : Blo 147793 221981 := bbase (se 3 (by rfl) ⟨41621, by rfl⟩ : syracuseStep 221981 = 83243) (by norm_num)
theorem B254765 : Blo 147793 254765 := bbase (se 3 (by rfl) ⟨47768, by rfl⟩ : syracuseStep 254765 = 95537) (by norm_num)
theorem B222005 : Blo 147793 222005 := bbase (se 5 (by rfl) ⟨10406, by rfl⟩ : syracuseStep 222005 = 20813) (by norm_num)
theorem B222029 : Blo 147793 222029 := bbase (se 3 (by rfl) ⟨41630, by rfl⟩ : syracuseStep 222029 = 83261) (by norm_num)
theorem B222053 : Blo 147793 222053 := bbase (se 4 (by rfl) ⟨20817, by rfl⟩ : syracuseStep 222053 = 41635) (by norm_num)
theorem B222077 : Blo 147793 222077 := bbase (se 3 (by rfl) ⟨41639, by rfl⟩ : syracuseStep 222077 = 83279) (by norm_num)
theorem B189317 : Blo 147793 189317 := bbase (se 4 (by rfl) ⟨17748, by rfl⟩ : syracuseStep 189317 = 35497) (by norm_num)
theorem B287621 : Blo 147793 287621 := bbase (se 4 (by rfl) ⟨26964, by rfl⟩ : syracuseStep 287621 = 53929) (by norm_num)
theorem B222101 : Blo 147793 222101 := bbase (se 6 (by rfl) ⟨5205, by rfl⟩ : syracuseStep 222101 = 10411) (by norm_num)
theorem B222125 : Blo 147793 222125 := bbase (se 3 (by rfl) ⟨41648, by rfl⟩ : syracuseStep 222125 = 83297) (by norm_num)
theorem B254893 : Blo 147793 254893 := bbase (se 3 (by rfl) ⟨47792, by rfl⟩ : syracuseStep 254893 = 95585) (by norm_num)
theorem B189373 : Blo 147793 189373 := bbase (se 3 (by rfl) ⟨35507, by rfl⟩ : syracuseStep 189373 = 71015) (by norm_num)
theorem B222149 : Blo 147793 222149 := bbase (se 4 (by rfl) ⟨20826, by rfl⟩ : syracuseStep 222149 = 41653) (by norm_num)
theorem B1139669 : Blo 147793 1139669 := bbase (se 7 (by rfl) ⟨13355, by rfl⟩ : syracuseStep 1139669 = 26711) (by norm_num)
theorem B222173 : Blo 147793 222173 := bbase (se 3 (by rfl) ⟨41657, by rfl⟩ : syracuseStep 222173 = 83315) (by norm_num)
theorem B222197 : Blo 147793 222197 := bbase (se 5 (by rfl) ⟨10415, by rfl⟩ : syracuseStep 222197 = 20831) (by norm_num)
theorem B254981 : Blo 147793 254981 := bbase (se 4 (by rfl) ⟨23904, by rfl⟩ : syracuseStep 254981 = 47809) (by norm_num)
theorem B222221 : Blo 147793 222221 := bbase (se 3 (by rfl) ⟨41666, by rfl⟩ : syracuseStep 222221 = 83333) (by norm_num)
theorem B2057237 : Blo 147793 2057237 := bbase (se 6 (by rfl) ⟨48216, by rfl⟩ : syracuseStep 2057237 = 96433) (by norm_num)
theorem B189469 : Blo 147793 189469 := bbase (se 3 (by rfl) ⟨35525, by rfl⟩ : syracuseStep 189469 = 71051) (by norm_num)
theorem B222245 : Blo 147793 222245 := bbase (se 4 (by rfl) ⟨20835, by rfl⟩ : syracuseStep 222245 = 41671) (by norm_num)
theorem B222269 : Blo 147793 222269 := bbase (se 3 (by rfl) ⟨41675, by rfl⟩ : syracuseStep 222269 = 83351) (by norm_num)
theorem B222293 : Blo 147793 222293 := bbase (se 8 (by rfl) ⟨1302, by rfl⟩ : syracuseStep 222293 = 2605) (by norm_num)
theorem B222317 : Blo 147793 222317 := bbase (se 3 (by rfl) ⟨41684, by rfl⟩ : syracuseStep 222317 = 83369) (by norm_num)
theorem B222341 : Blo 147793 222341 := bbase (se 4 (by rfl) ⟨20844, by rfl⟩ : syracuseStep 222341 = 41689) (by norm_num)
theorem B255109 : Blo 147793 255109 := bbase (se 4 (by rfl) ⟨23916, by rfl⟩ : syracuseStep 255109 = 47833) (by norm_num)
theorem B222365 : Blo 147793 222365 := bbase (se 3 (by rfl) ⟨41693, by rfl⟩ : syracuseStep 222365 = 83387) (by norm_num)
theorem B222389 : Blo 147793 222389 := bbase (se 5 (by rfl) ⟨10424, by rfl⟩ : syracuseStep 222389 = 20849) (by norm_num)
theorem B189641 : Blo 147793 189641 := bbase (se 2 (by rfl) ⟨71115, by rfl⟩ : syracuseStep 189641 = 142231) (by norm_num)
theorem B222413 : Blo 147793 222413 := bbase (se 3 (by rfl) ⟨41702, by rfl⟩ : syracuseStep 222413 = 83405) (by norm_num)
theorem B255197 : Blo 147793 255197 := bbase (se 3 (by rfl) ⟨47849, by rfl⟩ : syracuseStep 255197 = 95699) (by norm_num)
theorem B222437 : Blo 147793 222437 := bbase (se 4 (by rfl) ⟨20853, by rfl⟩ : syracuseStep 222437 = 41707) (by norm_num)
theorem B681205 : Blo 147793 681205 := bbase (se 5 (by rfl) ⟨31931, by rfl⟩ : syracuseStep 681205 = 63863) (by norm_num)
theorem B222461 : Blo 147793 222461 := bbase (se 3 (by rfl) ⟨41711, by rfl⟩ : syracuseStep 222461 = 83423) (by norm_num)
theorem B189697 : Blo 147793 189697 := bbase (se 2 (by rfl) ⟨71136, by rfl⟩ : syracuseStep 189697 = 142273) (by norm_num)
theorem B222485 : Blo 147793 222485 := bbase (se 6 (by rfl) ⟨5214, by rfl⟩ : syracuseStep 222485 = 10429) (by norm_num)
theorem B255253 : Blo 147793 255253 := bbase (se 6 (by rfl) ⟨5982, by rfl⟩ : syracuseStep 255253 = 11965) (by norm_num)
theorem B222509 : Blo 147793 222509 := bbase (se 3 (by rfl) ⟨41720, by rfl⟩ : syracuseStep 222509 = 83441) (by norm_num)
theorem B517429 : Blo 147793 517429 := bbase (se 5 (by rfl) ⟨24254, by rfl⟩ : syracuseStep 517429 = 48509) (by norm_num)
theorem B255293 : Blo 147793 255293 := bbase (se 3 (by rfl) ⟨47867, by rfl⟩ : syracuseStep 255293 = 95735) (by norm_num)
theorem B222533 : Blo 147793 222533 := bbase (se 4 (by rfl) ⟨20862, by rfl⟩ : syracuseStep 222533 = 41725) (by norm_num)
theorem B3106133 : Blo 147793 3106133 := bbase (se 12 (by rfl) ⟨1137, by rfl⟩ : syracuseStep 3106133 = 2275) (by norm_num)
theorem B222557 : Blo 147793 222557 := bbase (se 3 (by rfl) ⟨41729, by rfl⟩ : syracuseStep 222557 = 83459) (by norm_num)
theorem B255325 : Blo 147793 255325 := bbase (se 3 (by rfl) ⟨47873, by rfl⟩ : syracuseStep 255325 = 95747) (by norm_num)
theorem B189793 : Blo 147793 189793 := bbase (se 2 (by rfl) ⟨71172, by rfl⟩ : syracuseStep 189793 = 142345) (by norm_num)
theorem B222581 : Blo 147793 222581 := bbase (se 5 (by rfl) ⟨10433, by rfl⟩ : syracuseStep 222581 = 20867) (by norm_num)
theorem B222605 : Blo 147793 222605 := bbase (se 3 (by rfl) ⟨41738, by rfl⟩ : syracuseStep 222605 = 83477) (by norm_num)
theorem B681365 : Blo 147793 681365 := bbase (se 6 (by rfl) ⟨15969, by rfl⟩ : syracuseStep 681365 = 31939) (by norm_num)
theorem B222629 : Blo 147793 222629 := bbase (se 4 (by rfl) ⟨20871, by rfl⟩ : syracuseStep 222629 = 41743) (by norm_num)
theorem B255413 : Blo 147793 255413 := bbase (se 5 (by rfl) ⟨11972, by rfl⟩ : syracuseStep 255413 = 23945) (by norm_num)
theorem B222653 : Blo 147793 222653 := bbase (se 3 (by rfl) ⟨41747, by rfl⟩ : syracuseStep 222653 = 83495) (by norm_num)
theorem B222677 : Blo 147793 222677 := bbase (se 7 (by rfl) ⟨2609, by rfl⟩ : syracuseStep 222677 = 5219) (by norm_num)
theorem B222701 : Blo 147793 222701 := bbase (se 3 (by rfl) ⟨41756, by rfl⟩ : syracuseStep 222701 = 83513) (by norm_num)
theorem B222725 : Blo 147793 222725 := bbase (se 4 (by rfl) ⟨20880, by rfl⟩ : syracuseStep 222725 = 41761) (by norm_num)
theorem B189965 : Blo 147793 189965 := bbase (se 3 (by rfl) ⟨35618, by rfl⟩ : syracuseStep 189965 = 71237) (by norm_num)
theorem B222749 : Blo 147793 222749 := bbase (se 3 (by rfl) ⟨41765, by rfl⟩ : syracuseStep 222749 = 83531) (by norm_num)
theorem B222773 : Blo 147793 222773 := bbase (se 5 (by rfl) ⟨10442, by rfl⟩ : syracuseStep 222773 = 20885) (by norm_num)
theorem B255541 : Blo 147793 255541 := bbase (se 5 (by rfl) ⟨11978, by rfl⟩ : syracuseStep 255541 = 23957) (by norm_num)
theorem B190021 : Blo 147793 190021 := bbase (se 4 (by rfl) ⟨17814, by rfl⟩ : syracuseStep 190021 = 35629) (by norm_num)
theorem B222797 : Blo 147793 222797 := bbase (se 3 (by rfl) ⟨41774, by rfl⟩ : syracuseStep 222797 = 83549) (by norm_num)
theorem B222821 : Blo 147793 222821 := bbase (se 4 (by rfl) ⟨20889, by rfl⟩ : syracuseStep 222821 = 41779) (by norm_num)
theorem B222845 : Blo 147793 222845 := bbase (se 3 (by rfl) ⟨41783, by rfl⟩ : syracuseStep 222845 = 83567) (by norm_num)
theorem B255629 : Blo 147793 255629 := bbase (se 3 (by rfl) ⟨47930, by rfl⟩ : syracuseStep 255629 = 95861) (by norm_num)
theorem B222869 : Blo 147793 222869 := bbase (se 6 (by rfl) ⟨5223, by rfl⟩ : syracuseStep 222869 = 10447) (by norm_num)
theorem B190117 : Blo 147793 190117 := bbase (se 4 (by rfl) ⟨17823, by rfl⟩ : syracuseStep 190117 = 35647) (by norm_num)
theorem B222893 : Blo 147793 222893 := bbase (se 3 (by rfl) ⟨41792, by rfl⟩ : syracuseStep 222893 = 83585) (by norm_num)
theorem B222917 : Blo 147793 222917 := bbase (se 4 (by rfl) ⟨20898, by rfl⟩ : syracuseStep 222917 = 41797) (by norm_num)
theorem B222941 : Blo 147793 222941 := bbase (se 3 (by rfl) ⟨41801, by rfl⟩ : syracuseStep 222941 = 83603) (by norm_num)
theorem B222965 : Blo 147793 222965 := bbase (se 5 (by rfl) ⟨10451, by rfl⟩ : syracuseStep 222965 = 20903) (by norm_num)
theorem B222989 : Blo 147793 222989 := bbase (se 3 (by rfl) ⟨41810, by rfl⟩ : syracuseStep 222989 = 83621) (by norm_num)
theorem B255757 : Blo 147793 255757 := bbase (se 3 (by rfl) ⟨47954, by rfl⟩ : syracuseStep 255757 = 95909) (by norm_num)
theorem B223013 : Blo 147793 223013 := bbase (se 4 (by rfl) ⟨20907, by rfl⟩ : syracuseStep 223013 = 41815) (by norm_num)
theorem B223037 : Blo 147793 223037 := bbase (se 3 (by rfl) ⟨41819, by rfl⟩ : syracuseStep 223037 = 83639) (by norm_num)
theorem B190289 : Blo 147793 190289 := bbase (se 2 (by rfl) ⟨71358, by rfl⟩ : syracuseStep 190289 = 142717) (by norm_num)
theorem B223061 : Blo 147793 223061 := bbase (se 9 (by rfl) ⟨653, by rfl⟩ : syracuseStep 223061 = 1307) (by norm_num)
theorem B255845 : Blo 147793 255845 := bbase (se 4 (by rfl) ⟨23985, by rfl⟩ : syracuseStep 255845 = 47971) (by norm_num)
theorem B223085 : Blo 147793 223085 := bbase (se 3 (by rfl) ⟨41828, by rfl⟩ : syracuseStep 223085 = 83657) (by norm_num)
theorem B223109 : Blo 147793 223109 := bbase (se 4 (by rfl) ⟨20916, by rfl⟩ : syracuseStep 223109 = 41833) (by norm_num)
theorem B190345 : Blo 147793 190345 := bbase (se 2 (by rfl) ⟨71379, by rfl⟩ : syracuseStep 190345 = 142759) (by norm_num)
theorem B321421 : Blo 147793 321421 := bbase (se 3 (by rfl) ⟨60266, by rfl⟩ : syracuseStep 321421 = 120533) (by norm_num)
theorem B223133 : Blo 147793 223133 := bbase (se 3 (by rfl) ⟨41837, by rfl⟩ : syracuseStep 223133 = 83675) (by norm_num)
theorem B223157 : Blo 147793 223157 := bbase (se 5 (by rfl) ⟨10460, by rfl⟩ : syracuseStep 223157 = 20921) (by norm_num)
theorem B223181 : Blo 147793 223181 := bbase (se 3 (by rfl) ⟨41846, by rfl⟩ : syracuseStep 223181 = 83693) (by norm_num)
theorem B223205 : Blo 147793 223205 := bbase (se 4 (by rfl) ⟨20925, by rfl⟩ : syracuseStep 223205 = 41851) (by norm_num)
theorem B255973 : Blo 147793 255973 := bbase (se 4 (by rfl) ⟨23997, by rfl⟩ : syracuseStep 255973 = 47995) (by norm_num)
theorem B190441 : Blo 147793 190441 := bbase (se 2 (by rfl) ⟨71415, by rfl⟩ : syracuseStep 190441 = 142831) (by norm_num)
theorem B223229 : Blo 147793 223229 := bbase (se 3 (by rfl) ⟨41855, by rfl⟩ : syracuseStep 223229 = 83711) (by norm_num)
theorem B223253 : Blo 147793 223253 := bbase (se 6 (by rfl) ⟨5232, by rfl⟩ : syracuseStep 223253 = 10465) (by norm_num)
theorem B223277 : Blo 147793 223277 := bbase (se 3 (by rfl) ⟨41864, by rfl⟩ : syracuseStep 223277 = 83729) (by norm_num)
theorem B256061 : Blo 147793 256061 := bbase (se 3 (by rfl) ⟨48011, by rfl⟩ : syracuseStep 256061 = 96023) (by norm_num)
theorem B223301 : Blo 147793 223301 := bbase (se 4 (by rfl) ⟨20934, by rfl⟩ : syracuseStep 223301 = 41869) (by norm_num)
theorem B223325 : Blo 147793 223325 := bbase (se 3 (by rfl) ⟨41873, by rfl⟩ : syracuseStep 223325 = 83747) (by norm_num)
theorem B223349 : Blo 147793 223349 := bbase (se 5 (by rfl) ⟨10469, by rfl⟩ : syracuseStep 223349 = 20939) (by norm_num)
theorem B223373 : Blo 147793 223373 := bbase (se 3 (by rfl) ⟨41882, by rfl⟩ : syracuseStep 223373 = 83765) (by norm_num)
theorem B190613 : Blo 147793 190613 := bbase (se 6 (by rfl) ⟨4467, by rfl⟩ : syracuseStep 190613 = 8935) (by norm_num)
theorem B223397 : Blo 147793 223397 := bbase (se 4 (by rfl) ⟨20943, by rfl⟩ : syracuseStep 223397 = 41887) (by norm_num)
theorem B223421 : Blo 147793 223421 := bbase (se 3 (by rfl) ⟨41891, by rfl⟩ : syracuseStep 223421 = 83783) (by norm_num)
theorem B190669 : Blo 147793 190669 := bbase (se 3 (by rfl) ⟨35750, by rfl⟩ : syracuseStep 190669 = 71501) (by norm_num)
theorem B223445 : Blo 147793 223445 := bbase (se 7 (by rfl) ⟨2618, by rfl⟩ : syracuseStep 223445 = 5237) (by norm_num)
theorem B485605 : Blo 147793 485605 := bbase (se 4 (by rfl) ⟨45525, by rfl⟩ : syracuseStep 485605 = 91051) (by norm_num)
theorem B223469 : Blo 147793 223469 := bbase (se 3 (by rfl) ⟨41900, by rfl⟩ : syracuseStep 223469 = 83801) (by norm_num)
theorem B223493 : Blo 147793 223493 := bbase (se 4 (by rfl) ⟨20952, by rfl⟩ : syracuseStep 223493 = 41905) (by norm_num)
theorem B223517 : Blo 147793 223517 := bbase (se 3 (by rfl) ⟨41909, by rfl⟩ : syracuseStep 223517 = 83819) (by norm_num)
theorem B485669 : Blo 147793 485669 := bbase (se 4 (by rfl) ⟨45531, by rfl⟩ : syracuseStep 485669 = 91063) (by norm_num)
theorem B190765 : Blo 147793 190765 := bbase (se 3 (by rfl) ⟨35768, by rfl⟩ : syracuseStep 190765 = 71537) (by norm_num)
theorem B223541 : Blo 147793 223541 := bbase (se 5 (by rfl) ⟨10478, by rfl⟩ : syracuseStep 223541 = 20957) (by norm_num)
theorem B223565 : Blo 147793 223565 := bbase (se 3 (by rfl) ⟨41918, by rfl⟩ : syracuseStep 223565 = 83837) (by norm_num)
theorem B158041 : Blo 147793 158041 := bbase (se 2 (by rfl) ⟨59265, by rfl⟩ : syracuseStep 158041 = 118531) (by norm_num)
theorem B158045 : Blo 147793 158045 := bbase (se 3 (by rfl) ⟨29633, by rfl⟩ : syracuseStep 158045 = 59267) (by norm_num)
theorem B223589 : Blo 147793 223589 := bbase (se 4 (by rfl) ⟨20961, by rfl⟩ : syracuseStep 223589 = 41923) (by norm_num)
theorem B223613 : Blo 147793 223613 := bbase (se 3 (by rfl) ⟨41927, by rfl⟩ : syracuseStep 223613 = 83855) (by norm_num)
theorem B223637 : Blo 147793 223637 := bbase (se 6 (by rfl) ⟨5241, by rfl⟩ : syracuseStep 223637 = 10483) (by norm_num)
theorem B223661 : Blo 147793 223661 := bbase (se 3 (by rfl) ⟨41936, by rfl⟩ : syracuseStep 223661 = 83873) (by norm_num)
theorem B223685 : Blo 147793 223685 := bbase (se 4 (by rfl) ⟨20970, by rfl⟩ : syracuseStep 223685 = 41941) (by norm_num)
theorem B190937 : Blo 147793 190937 := bbase (se 2 (by rfl) ⟨71601, by rfl⟩ : syracuseStep 190937 = 143203) (by norm_num)
theorem B223709 : Blo 147793 223709 := bbase (se 3 (by rfl) ⟨41945, by rfl⟩ : syracuseStep 223709 = 83891) (by norm_num)
theorem B223733 : Blo 147793 223733 := bbase (se 5 (by rfl) ⟨10487, by rfl⟩ : syracuseStep 223733 = 20975) (by norm_num)
theorem B223757 : Blo 147793 223757 := bbase (se 3 (by rfl) ⟨41954, by rfl⟩ : syracuseStep 223757 = 83909) (by norm_num)
theorem B190993 : Blo 147793 190993 := bbase (se 2 (by rfl) ⟨71622, by rfl⟩ : syracuseStep 190993 = 143245) (by norm_num)
theorem B223781 : Blo 147793 223781 := bbase (se 4 (by rfl) ⟨20979, by rfl⟩ : syracuseStep 223781 = 41959) (by norm_num)
theorem B223805 : Blo 147793 223805 := bbase (se 3 (by rfl) ⟨41963, by rfl⟩ : syracuseStep 223805 = 83927) (by norm_num)
theorem B223829 : Blo 147793 223829 := bbase (se 8 (by rfl) ⟨1311, by rfl⟩ : syracuseStep 223829 = 2623) (by norm_num)
theorem B223853 : Blo 147793 223853 := bbase (se 3 (by rfl) ⟨41972, by rfl⟩ : syracuseStep 223853 = 83945) (by norm_num)
theorem B191089 : Blo 147793 191089 := bbase (se 2 (by rfl) ⟨71658, by rfl⟩ : syracuseStep 191089 = 143317) (by norm_num)
theorem B813685 : Blo 147793 813685 := bbase (se 5 (by rfl) ⟨38141, by rfl⟩ : syracuseStep 813685 = 76283) (by norm_num)
theorem B223877 : Blo 147793 223877 := bbase (se 4 (by rfl) ⟨20988, by rfl⟩ : syracuseStep 223877 = 41977) (by norm_num)
theorem B223901 : Blo 147793 223901 := bbase (se 3 (by rfl) ⟨41981, by rfl⟩ : syracuseStep 223901 = 83963) (by norm_num)
theorem B223925 : Blo 147793 223925 := bbase (se 5 (by rfl) ⟨10496, by rfl⟩ : syracuseStep 223925 = 20993) (by norm_num)
theorem B223949 : Blo 147793 223949 := bbase (se 3 (by rfl) ⟨41990, by rfl⟩ : syracuseStep 223949 = 83981) (by norm_num)
theorem B223973 : Blo 147793 223973 := bbase (se 4 (by rfl) ⟨20997, by rfl⟩ : syracuseStep 223973 = 41995) (by norm_num)
theorem B879349 : Blo 147793 879349 := bbase (se 5 (by rfl) ⟨41219, by rfl⟩ : syracuseStep 879349 = 82439) (by norm_num)
theorem B748277 : Blo 147793 748277 := bbase (se 5 (by rfl) ⟨35075, by rfl⟩ : syracuseStep 748277 = 70151) (by norm_num)
theorem B223997 : Blo 147793 223997 := bbase (se 3 (by rfl) ⟨41999, by rfl⟩ : syracuseStep 223997 = 83999) (by norm_num)
theorem B322309 : Blo 147793 322309 := bbase (se 4 (by rfl) ⟨30216, by rfl⟩ : syracuseStep 322309 = 60433) (by norm_num)
theorem B224021 : Blo 147793 224021 := bbase (se 6 (by rfl) ⟨5250, by rfl⟩ : syracuseStep 224021 = 10501) (by norm_num)
theorem B191261 : Blo 147793 191261 := bbase (se 3 (by rfl) ⟨35861, by rfl⟩ : syracuseStep 191261 = 71723) (by norm_num)
theorem B224045 : Blo 147793 224045 := bbase (se 3 (by rfl) ⟨42008, by rfl⟩ : syracuseStep 224045 = 84017) (by norm_num)
theorem B224069 : Blo 147793 224069 := bbase (se 4 (by rfl) ⟨21006, by rfl⟩ : syracuseStep 224069 = 42013) (by norm_num)
theorem B191317 : Blo 147793 191317 := bbase (se 9 (by rfl) ⟨560, by rfl⟩ : syracuseStep 191317 = 1121) (by norm_num)
theorem B224093 : Blo 147793 224093 := bbase (se 3 (by rfl) ⟨42017, by rfl⟩ : syracuseStep 224093 = 84035) (by norm_num)
theorem B224117 : Blo 147793 224117 := bbase (se 5 (by rfl) ⟨10505, by rfl⟩ : syracuseStep 224117 = 21011) (by norm_num)
theorem B224141 : Blo 147793 224141 := bbase (se 3 (by rfl) ⟨42026, by rfl⟩ : syracuseStep 224141 = 84053) (by norm_num)
theorem B158609 : Blo 147793 158609 := bbase (se 2 (by rfl) ⟨59478, by rfl⟩ : syracuseStep 158609 = 118957) (by norm_num)
theorem B224165 : Blo 147793 224165 := bbase (se 4 (by rfl) ⟨21015, by rfl⟩ : syracuseStep 224165 = 42031) (by norm_num)
theorem B191413 : Blo 147793 191413 := bbase (se 5 (by rfl) ⟨8972, by rfl⟩ : syracuseStep 191413 = 17945) (by norm_num)
theorem B224189 : Blo 147793 224189 := bbase (se 3 (by rfl) ⟨42035, by rfl⟩ : syracuseStep 224189 = 84071) (by norm_num)
theorem B224213 : Blo 147793 224213 := bbase (se 7 (by rfl) ⟨2627, by rfl⟩ : syracuseStep 224213 = 5255) (by norm_num)
theorem B224237 : Blo 147793 224237 := bbase (se 3 (by rfl) ⟨42044, by rfl⟩ : syracuseStep 224237 = 84089) (by norm_num)
theorem B224261 : Blo 147793 224261 := bbase (se 4 (by rfl) ⟨21024, by rfl⟩ : syracuseStep 224261 = 42049) (by norm_num)
theorem B257053 : Blo 147793 257053 := bbase (se 3 (by rfl) ⟨48197, by rfl⟩ : syracuseStep 257053 = 96395) (by norm_num)
theorem B224285 : Blo 147793 224285 := bbase (se 3 (by rfl) ⟨42053, by rfl⟩ : syracuseStep 224285 = 84107) (by norm_num)
theorem B224309 : Blo 147793 224309 := bbase (se 5 (by rfl) ⟨10514, by rfl⟩ : syracuseStep 224309 = 21029) (by norm_num)
theorem B158797 : Blo 147793 158797 := bbase (se 3 (by rfl) ⟨29774, by rfl⟩ : syracuseStep 158797 = 59549) (by norm_num)
theorem B224333 : Blo 147793 224333 := bbase (se 3 (by rfl) ⟨42062, by rfl⟩ : syracuseStep 224333 = 84125) (by norm_num)
theorem B191585 : Blo 147793 191585 := bbase (se 2 (by rfl) ⟨71844, by rfl⟩ : syracuseStep 191585 = 143689) (by norm_num)
theorem B224357 : Blo 147793 224357 := bbase (se 4 (by rfl) ⟨21033, by rfl⟩ : syracuseStep 224357 = 42067) (by norm_num)
theorem B224381 : Blo 147793 224381 := bbase (se 3 (by rfl) ⟨42071, by rfl⟩ : syracuseStep 224381 = 84143) (by norm_num)
theorem B224405 : Blo 147793 224405 := bbase (se 6 (by rfl) ⟨5259, by rfl⟩ : syracuseStep 224405 = 10519) (by norm_num)
theorem B191641 : Blo 147793 191641 := bbase (se 2 (by rfl) ⟨71865, by rfl⟩ : syracuseStep 191641 = 143731) (by norm_num)
theorem B224429 : Blo 147793 224429 := bbase (se 3 (by rfl) ⟨42080, by rfl⟩ : syracuseStep 224429 = 84161) (by norm_num)
theorem B224453 : Blo 147793 224453 := bbase (se 4 (by rfl) ⟨21042, by rfl⟩ : syracuseStep 224453 = 42085) (by norm_num)
theorem B224477 : Blo 147793 224477 := bbase (se 3 (by rfl) ⟨42089, by rfl⟩ : syracuseStep 224477 = 84179) (by norm_num)
theorem B224501 : Blo 147793 224501 := bbase (se 5 (by rfl) ⟨10523, by rfl⟩ : syracuseStep 224501 = 21047) (by norm_num)
theorem B322805 : Blo 147793 322805 := bbase (se 5 (by rfl) ⟨15131, by rfl⟩ : syracuseStep 322805 = 30263) (by norm_num)
theorem B191737 : Blo 147793 191737 := bbase (se 2 (by rfl) ⟨71901, by rfl⟩ : syracuseStep 191737 = 143803) (by norm_num)
theorem B224525 : Blo 147793 224525 := bbase (se 3 (by rfl) ⟨42098, by rfl⟩ : syracuseStep 224525 = 84197) (by norm_num)
theorem B224549 : Blo 147793 224549 := bbase (se 4 (by rfl) ⟨21051, by rfl⟩ : syracuseStep 224549 = 42103) (by norm_num)
theorem B290093 : Blo 147793 290093 := bbase (se 3 (by rfl) ⟨54392, by rfl⟩ : syracuseStep 290093 = 108785) (by norm_num)
theorem B224573 : Blo 147793 224573 := bbase (se 3 (by rfl) ⟨42107, by rfl⟩ : syracuseStep 224573 = 84215) (by norm_num)
theorem B224597 : Blo 147793 224597 := bbase (se 11 (by rfl) ⟨164, by rfl⟩ : syracuseStep 224597 = 329) (by norm_num)
theorem B224621 : Blo 147793 224621 := bbase (se 3 (by rfl) ⟨42116, by rfl⟩ : syracuseStep 224621 = 84233) (by norm_num)
theorem B224645 : Blo 147793 224645 := bbase (se 4 (by rfl) ⟨21060, by rfl⟩ : syracuseStep 224645 = 42121) (by norm_num)
theorem B224669 : Blo 147793 224669 := bbase (se 3 (by rfl) ⟨42125, by rfl⟩ : syracuseStep 224669 = 84251) (by norm_num)
theorem B191909 : Blo 147793 191909 := bbase (se 4 (by rfl) ⟨17991, by rfl⟩ : syracuseStep 191909 = 35983) (by norm_num)
theorem B224693 : Blo 147793 224693 := bbase (se 5 (by rfl) ⟨10532, by rfl⟩ : syracuseStep 224693 = 21065) (by norm_num)
theorem B224717 : Blo 147793 224717 := bbase (se 3 (by rfl) ⟨42134, by rfl⟩ : syracuseStep 224717 = 84269) (by norm_num)
theorem B191965 : Blo 147793 191965 := bbase (se 3 (by rfl) ⟨35993, by rfl⟩ : syracuseStep 191965 = 71987) (by norm_num)
theorem B224741 : Blo 147793 224741 := bbase (se 4 (by rfl) ⟨21069, by rfl⟩ : syracuseStep 224741 = 42139) (by norm_num)
theorem B224765 : Blo 147793 224765 := bbase (se 3 (by rfl) ⟨42143, by rfl⟩ : syracuseStep 224765 = 84287) (by norm_num)
theorem B224789 : Blo 147793 224789 := bbase (se 6 (by rfl) ⟨5268, by rfl⟩ : syracuseStep 224789 = 10537) (by norm_num)
theorem B224813 : Blo 147793 224813 := bbase (se 3 (by rfl) ⟨42152, by rfl⟩ : syracuseStep 224813 = 84305) (by norm_num)
theorem B192061 : Blo 147793 192061 := bbase (se 3 (by rfl) ⟨36011, by rfl⟩ : syracuseStep 192061 = 72023) (by norm_num)
theorem B355909 : Blo 147793 355909 := bbase (se 4 (by rfl) ⟨33366, by rfl⟩ : syracuseStep 355909 = 66733) (by norm_num)
theorem B224837 : Blo 147793 224837 := bbase (se 4 (by rfl) ⟨21078, by rfl⟩ : syracuseStep 224837 = 42157) (by norm_num)
theorem B224861 : Blo 147793 224861 := bbase (se 3 (by rfl) ⟨42161, by rfl⟩ : syracuseStep 224861 = 84323) (by norm_num)
theorem B224885 : Blo 147793 224885 := bbase (se 5 (by rfl) ⟨10541, by rfl⟩ : syracuseStep 224885 = 21083) (by norm_num)
theorem B224909 : Blo 147793 224909 := bbase (se 3 (by rfl) ⟨42170, by rfl⟩ : syracuseStep 224909 = 84341) (by norm_num)
theorem B224933 : Blo 147793 224933 := bbase (se 4 (by rfl) ⟨21087, by rfl⟩ : syracuseStep 224933 = 42175) (by norm_num)
theorem B224957 : Blo 147793 224957 := bbase (se 3 (by rfl) ⟨42179, by rfl⟩ : syracuseStep 224957 = 84359) (by norm_num)
theorem B224981 : Blo 147793 224981 := bbase (se 7 (by rfl) ⟨2636, by rfl⟩ : syracuseStep 224981 = 5273) (by norm_num)
theorem B225005 : Blo 147793 225005 := bbase (se 3 (by rfl) ⟨42188, by rfl⟩ : syracuseStep 225005 = 84377) (by norm_num)
theorem B225029 : Blo 147793 225029 := bbase (se 4 (by rfl) ⟨21096, by rfl⟩ : syracuseStep 225029 = 42193) (by norm_num)
theorem B225053 : Blo 147793 225053 := bbase (se 3 (by rfl) ⟨42197, by rfl⟩ : syracuseStep 225053 = 84395) (by norm_num)
theorem B225077 : Blo 147793 225077 := bbase (se 5 (by rfl) ⟨10550, by rfl⟩ : syracuseStep 225077 = 21101) (by norm_num)
theorem B225101 : Blo 147793 225101 := bbase (se 3 (by rfl) ⟨42206, by rfl⟩ : syracuseStep 225101 = 84413) (by norm_num)
theorem B225125 : Blo 147793 225125 := bbase (se 4 (by rfl) ⟨21105, by rfl⟩ : syracuseStep 225125 = 42211) (by norm_num)
theorem B225149 : Blo 147793 225149 := bbase (se 3 (by rfl) ⟨42215, by rfl⟩ : syracuseStep 225149 = 84431) (by norm_num)
theorem B159617 : Blo 147793 159617 := bbase (se 2 (by rfl) ⟨59856, by rfl⟩ : syracuseStep 159617 = 119713) (by norm_num)
theorem B225173 : Blo 147793 225173 := bbase (se 6 (by rfl) ⟨5277, by rfl⟩ : syracuseStep 225173 = 10555) (by norm_num)
theorem B225197 : Blo 147793 225197 := bbase (se 3 (by rfl) ⟨42224, by rfl⟩ : syracuseStep 225197 = 84449) (by norm_num)
theorem B225221 : Blo 147793 225221 := bbase (se 4 (by rfl) ⟨21114, by rfl⟩ : syracuseStep 225221 = 42229) (by norm_num)
theorem B2060245 : Blo 147793 2060245 := bbase (se 7 (by rfl) ⟨24143, by rfl⟩ : syracuseStep 2060245 = 48287) (by norm_num)
theorem B225245 : Blo 147793 225245 := bbase (se 3 (by rfl) ⟨42233, by rfl⟩ : syracuseStep 225245 = 84467) (by norm_num)
theorem B225269 : Blo 147793 225269 := bbase (se 5 (by rfl) ⟨10559, by rfl⟩ : syracuseStep 225269 = 21119) (by norm_num)
theorem B749573 : Blo 147793 749573 := bbase (se 4 (by rfl) ⟨70272, by rfl⟩ : syracuseStep 749573 = 140545) (by norm_num)
theorem B225293 : Blo 147793 225293 := bbase (se 3 (by rfl) ⟨42242, by rfl⟩ : syracuseStep 225293 = 84485) (by norm_num)
theorem B225317 : Blo 147793 225317 := bbase (se 4 (by rfl) ⟨21123, by rfl⟩ : syracuseStep 225317 = 42247) (by norm_num)
theorem B1437749 : Blo 147793 1437749 := bbase (se 5 (by rfl) ⟨67394, by rfl⟩ : syracuseStep 1437749 = 134789) (by norm_num)
theorem B225341 : Blo 147793 225341 := bbase (se 3 (by rfl) ⟨42251, by rfl⟩ : syracuseStep 225341 = 84503) (by norm_num)
theorem B225365 : Blo 147793 225365 := bbase (se 8 (by rfl) ⟨1320, by rfl⟩ : syracuseStep 225365 = 2641) (by norm_num)
theorem B323669 : Blo 147793 323669 := bbase (se 8 (by rfl) ⟨1896, by rfl⟩ : syracuseStep 323669 = 3793) (by norm_num)
theorem B225389 : Blo 147793 225389 := bbase (se 3 (by rfl) ⟨42260, by rfl⟩ : syracuseStep 225389 = 84521) (by norm_num)
theorem B225413 : Blo 147793 225413 := bbase (se 4 (by rfl) ⟨21132, by rfl⟩ : syracuseStep 225413 = 42265) (by norm_num)
theorem B192661 : Blo 147793 192661 := bbase (se 6 (by rfl) ⟨4515, by rfl⟩ : syracuseStep 192661 = 9031) (by norm_num)
theorem B225437 : Blo 147793 225437 := bbase (se 3 (by rfl) ⟨42269, by rfl⟩ : syracuseStep 225437 = 84539) (by norm_num)
theorem B356525 : Blo 147793 356525 := bbase (se 3 (by rfl) ⟨66848, by rfl⟩ : syracuseStep 356525 = 133697) (by norm_num)
theorem B258221 : Blo 147793 258221 := bbase (se 3 (by rfl) ⟨48416, by rfl⟩ : syracuseStep 258221 = 96833) (by norm_num)
theorem B225461 : Blo 147793 225461 := bbase (se 5 (by rfl) ⟨10568, by rfl⟩ : syracuseStep 225461 = 21137) (by norm_num)
theorem B225485 : Blo 147793 225485 := bbase (se 3 (by rfl) ⟨42278, by rfl⟩ : syracuseStep 225485 = 84557) (by norm_num)
theorem B225509 : Blo 147793 225509 := bbase (se 4 (by rfl) ⟨21141, by rfl⟩ : syracuseStep 225509 = 42283) (by norm_num)
theorem B323813 : Blo 147793 323813 := bbase (se 4 (by rfl) ⟨30357, by rfl⟩ : syracuseStep 323813 = 60715) (by norm_num)
theorem B225533 : Blo 147793 225533 := bbase (se 3 (by rfl) ⟨42287, by rfl⟩ : syracuseStep 225533 = 84575) (by norm_num)
theorem B225557 : Blo 147793 225557 := bbase (se 6 (by rfl) ⟨5286, by rfl⟩ : syracuseStep 225557 = 10573) (by norm_num)
theorem B225581 : Blo 147793 225581 := bbase (se 3 (by rfl) ⟨42296, by rfl⟩ : syracuseStep 225581 = 84593) (by norm_num)
theorem B160061 : Blo 147793 160061 := bbase (se 3 (by rfl) ⟨30011, by rfl⟩ : syracuseStep 160061 = 60023) (by norm_num)
theorem B225605 : Blo 147793 225605 := bbase (se 4 (by rfl) ⟨21150, by rfl⟩ : syracuseStep 225605 = 42301) (by norm_num)
theorem B3207509 : Blo 147793 3207509 := bbase (se 10 (by rfl) ⟨4698, by rfl⟩ : syracuseStep 3207509 = 9397) (by norm_num)
theorem B225629 : Blo 147793 225629 := bbase (se 3 (by rfl) ⟨42305, by rfl⟩ : syracuseStep 225629 = 84611) (by norm_num)
theorem B356717 : Blo 147793 356717 := bbase (se 3 (by rfl) ⟨66884, by rfl⟩ : syracuseStep 356717 = 133769) (by norm_num)
theorem B225653 : Blo 147793 225653 := bbase (se 5 (by rfl) ⟨10577, by rfl⟩ : syracuseStep 225653 = 21155) (by norm_num)
theorem B225677 : Blo 147793 225677 := bbase (se 3 (by rfl) ⟨42314, by rfl⟩ : syracuseStep 225677 = 84629) (by norm_num)
theorem B225701 : Blo 147793 225701 := bbase (se 4 (by rfl) ⟨21159, by rfl⟩ : syracuseStep 225701 = 42319) (by norm_num)
theorem B225725 : Blo 147793 225725 := bbase (se 3 (by rfl) ⟨42323, by rfl⟩ : syracuseStep 225725 = 84647) (by norm_num)
theorem B225749 : Blo 147793 225749 := bbase (se 7 (by rfl) ⟨2645, by rfl⟩ : syracuseStep 225749 = 5291) (by norm_num)
theorem B225773 : Blo 147793 225773 := bbase (se 3 (by rfl) ⟨42332, by rfl⟩ : syracuseStep 225773 = 84665) (by norm_num)
theorem B225797 : Blo 147793 225797 := bbase (se 4 (by rfl) ⟨21168, by rfl⟩ : syracuseStep 225797 = 42337) (by norm_num)
theorem B225821 : Blo 147793 225821 := bbase (se 3 (by rfl) ⟨42341, by rfl⟩ : syracuseStep 225821 = 84683) (by norm_num)
theorem B160309 : Blo 147793 160309 := bbase (se 5 (by rfl) ⟨7514, by rfl⟩ : syracuseStep 160309 = 15029) (by norm_num)
theorem B225845 : Blo 147793 225845 := bbase (se 5 (by rfl) ⟨10586, by rfl⟩ : syracuseStep 225845 = 21173) (by norm_num)
theorem B225869 : Blo 147793 225869 := bbase (se 3 (by rfl) ⟨42350, by rfl⟩ : syracuseStep 225869 = 84701) (by norm_num)
theorem B225893 : Blo 147793 225893 := bbase (se 4 (by rfl) ⟨21177, by rfl⟩ : syracuseStep 225893 = 42355) (by norm_num)
theorem B225917 : Blo 147793 225917 := bbase (se 3 (by rfl) ⟨42359, by rfl⟩ : syracuseStep 225917 = 84719) (by norm_num)
theorem B357005 : Blo 147793 357005 := bbase (se 3 (by rfl) ⟨66938, by rfl⟩ : syracuseStep 357005 = 133877) (by norm_num)
theorem B225941 : Blo 147793 225941 := bbase (se 6 (by rfl) ⟨5295, by rfl⟩ : syracuseStep 225941 = 10591) (by norm_num)
theorem B225965 : Blo 147793 225965 := bbase (se 3 (by rfl) ⟨42368, by rfl⟩ : syracuseStep 225965 = 84737) (by norm_num)
theorem B225989 : Blo 147793 225989 := bbase (se 4 (by rfl) ⟨21186, by rfl⟩ : syracuseStep 225989 = 42373) (by norm_num)
theorem B226013 : Blo 147793 226013 := bbase (se 3 (by rfl) ⟨42377, by rfl⟩ : syracuseStep 226013 = 84755) (by norm_num)
theorem B226037 : Blo 147793 226037 := bbase (se 5 (by rfl) ⟨10595, by rfl⟩ : syracuseStep 226037 = 21191) (by norm_num)
theorem B226061 : Blo 147793 226061 := bbase (se 3 (by rfl) ⟨42386, by rfl⟩ : syracuseStep 226061 = 84773) (by norm_num)
theorem B193313 : Blo 147793 193313 := bbase (se 2 (by rfl) ⟨72492, by rfl⟩ : syracuseStep 193313 = 144985) (by norm_num)
theorem B226085 : Blo 147793 226085 := bbase (se 4 (by rfl) ⟨21195, by rfl⟩ : syracuseStep 226085 = 42391) (by norm_num)
theorem B226109 : Blo 147793 226109 := bbase (se 3 (by rfl) ⟨42395, by rfl⟩ : syracuseStep 226109 = 84791) (by norm_num)
theorem B226133 : Blo 147793 226133 := bbase (se 9 (by rfl) ⟨662, by rfl⟩ : syracuseStep 226133 = 1325) (by norm_num)
theorem B226157 : Blo 147793 226157 := bbase (se 3 (by rfl) ⟨42404, by rfl⟩ : syracuseStep 226157 = 84809) (by norm_num)
theorem B226181 : Blo 147793 226181 := bbase (se 4 (by rfl) ⟨21204, by rfl⟩ : syracuseStep 226181 = 42409) (by norm_num)
theorem B226205 : Blo 147793 226205 := bbase (se 3 (by rfl) ⟨42413, by rfl⟩ : syracuseStep 226205 = 84827) (by norm_num)
theorem B226229 : Blo 147793 226229 := bbase (se 5 (by rfl) ⟨10604, by rfl⟩ : syracuseStep 226229 = 21209) (by norm_num)
theorem B226253 : Blo 147793 226253 := bbase (se 3 (by rfl) ⟨42422, by rfl⟩ : syracuseStep 226253 = 84845) (by norm_num)
theorem B160741 : Blo 147793 160741 := bbase (se 4 (by rfl) ⟨15069, by rfl⟩ : syracuseStep 160741 = 30139) (by norm_num)
theorem B226277 : Blo 147793 226277 := bbase (se 4 (by rfl) ⟨21213, by rfl⟩ : syracuseStep 226277 = 42427) (by norm_num)
theorem B226301 : Blo 147793 226301 := bbase (se 3 (by rfl) ⟨42431, by rfl⟩ : syracuseStep 226301 = 84863) (by norm_num)
theorem B226325 : Blo 147793 226325 := bbase (se 6 (by rfl) ⟨5304, by rfl⟩ : syracuseStep 226325 = 10609) (by norm_num)
theorem B160813 : Blo 147793 160813 := bbase (se 3 (by rfl) ⟨30152, by rfl⟩ : syracuseStep 160813 = 60305) (by norm_num)
theorem B226349 : Blo 147793 226349 := bbase (se 3 (by rfl) ⟨42440, by rfl⟩ : syracuseStep 226349 = 84881) (by norm_num)
theorem B1373237 : Blo 147793 1373237 := bbase (se 5 (by rfl) ⟨64370, by rfl⟩ : syracuseStep 1373237 = 128741) (by norm_num)
theorem B226373 : Blo 147793 226373 := bbase (se 4 (by rfl) ⟨21222, by rfl⟩ : syracuseStep 226373 = 42445) (by norm_num)
theorem B226397 : Blo 147793 226397 := bbase (se 3 (by rfl) ⟨42449, by rfl⟩ : syracuseStep 226397 = 84899) (by norm_num)
theorem B226421 : Blo 147793 226421 := bbase (se 5 (by rfl) ⟨10613, by rfl⟩ : syracuseStep 226421 = 21227) (by norm_num)
theorem B226445 : Blo 147793 226445 := bbase (se 3 (by rfl) ⟨42458, by rfl⟩ : syracuseStep 226445 = 84917) (by norm_num)
theorem B226469 : Blo 147793 226469 := bbase (se 4 (by rfl) ⟨21231, by rfl⟩ : syracuseStep 226469 = 42463) (by norm_num)
theorem B226493 : Blo 147793 226493 := bbase (se 3 (by rfl) ⟨42467, by rfl⟩ : syracuseStep 226493 = 84935) (by norm_num)
theorem B226517 : Blo 147793 226517 := bbase (se 7 (by rfl) ⟨2654, by rfl⟩ : syracuseStep 226517 = 5309) (by norm_num)
theorem B226541 : Blo 147793 226541 := bbase (se 3 (by rfl) ⟨42476, by rfl⟩ : syracuseStep 226541 = 84953) (by norm_num)
theorem B226565 : Blo 147793 226565 := bbase (se 4 (by rfl) ⟨21240, by rfl⟩ : syracuseStep 226565 = 42481) (by norm_num)
theorem B750869 : Blo 147793 750869 := bbase (se 6 (by rfl) ⟨17598, by rfl⟩ : syracuseStep 750869 = 35197) (by norm_num)
theorem B226589 : Blo 147793 226589 := bbase (se 3 (by rfl) ⟨42485, by rfl⟩ : syracuseStep 226589 = 84971) (by norm_num)
theorem B226613 : Blo 147793 226613 := bbase (se 5 (by rfl) ⟨10622, by rfl⟩ : syracuseStep 226613 = 21245) (by norm_num)
theorem B685381 : Blo 147793 685381 := bbase (se 4 (by rfl) ⟨64254, by rfl⟩ : syracuseStep 685381 = 128509) (by norm_num)
theorem B226637 : Blo 147793 226637 := bbase (se 3 (by rfl) ⟨42494, by rfl⟩ : syracuseStep 226637 = 84989) (by norm_num)
theorem B226661 : Blo 147793 226661 := bbase (se 4 (by rfl) ⟨21249, by rfl⟩ : syracuseStep 226661 = 42499) (by norm_num)
theorem B226685 : Blo 147793 226685 := bbase (se 3 (by rfl) ⟨42503, by rfl⟩ : syracuseStep 226685 = 85007) (by norm_num)
theorem B226709 : Blo 147793 226709 := bbase (se 6 (by rfl) ⟨5313, by rfl⟩ : syracuseStep 226709 = 10627) (by norm_num)
theorem B161185 : Blo 147793 161185 := bbase (se 2 (by rfl) ⟨60444, by rfl⟩ : syracuseStep 161185 = 120889) (by norm_num)
theorem B226733 : Blo 147793 226733 := bbase (se 3 (by rfl) ⟨42512, by rfl⟩ : syracuseStep 226733 = 85025) (by norm_num)
theorem B226757 : Blo 147793 226757 := bbase (se 4 (by rfl) ⟨21258, by rfl⟩ : syracuseStep 226757 = 42517) (by norm_num)
theorem B226781 : Blo 147793 226781 := bbase (se 3 (by rfl) ⟨42521, by rfl⟩ : syracuseStep 226781 = 85043) (by norm_num)
theorem B423413 : Blo 147793 423413 := bbase (se 5 (by rfl) ⟨19847, by rfl⟩ : syracuseStep 423413 = 39695) (by norm_num)
theorem B226805 : Blo 147793 226805 := bbase (se 5 (by rfl) ⟨10631, by rfl⟩ : syracuseStep 226805 = 21263) (by norm_num)
theorem B226829 : Blo 147793 226829 := bbase (se 3 (by rfl) ⟨42530, by rfl⟩ : syracuseStep 226829 = 85061) (by norm_num)
theorem B226853 : Blo 147793 226853 := bbase (se 4 (by rfl) ⟨21267, by rfl⟩ : syracuseStep 226853 = 42535) (by norm_num)
theorem B226877 : Blo 147793 226877 := bbase (se 3 (by rfl) ⟨42539, by rfl⟩ : syracuseStep 226877 = 85079) (by norm_num)
theorem B226901 : Blo 147793 226901 := bbase (se 8 (by rfl) ⟨1329, by rfl⟩ : syracuseStep 226901 = 2659) (by norm_num)
theorem B161389 : Blo 147793 161389 := bbase (se 3 (by rfl) ⟨30260, by rfl⟩ : syracuseStep 161389 = 60521) (by norm_num)
theorem B226925 : Blo 147793 226925 := bbase (se 3 (by rfl) ⟨42548, by rfl⟩ : syracuseStep 226925 = 85097) (by norm_num)
theorem B226949 : Blo 147793 226949 := bbase (se 4 (by rfl) ⟨21276, by rfl⟩ : syracuseStep 226949 = 42553) (by norm_num)
theorem B947861 : Blo 147793 947861 := bbase (se 6 (by rfl) ⟨22215, by rfl⟩ : syracuseStep 947861 = 44431) (by norm_num)
theorem B226973 : Blo 147793 226973 := bbase (se 3 (by rfl) ⟨42557, by rfl⟩ : syracuseStep 226973 = 85115) (by norm_num)
theorem B226997 : Blo 147793 226997 := bbase (se 5 (by rfl) ⟨10640, by rfl⟩ : syracuseStep 226997 = 21281) (by norm_num)
theorem B227021 : Blo 147793 227021 := bbase (se 3 (by rfl) ⟨42566, by rfl⟩ : syracuseStep 227021 = 85133) (by norm_num)
theorem B227045 : Blo 147793 227045 := bbase (se 4 (by rfl) ⟨21285, by rfl⟩ : syracuseStep 227045 = 42571) (by norm_num)
theorem B227069 : Blo 147793 227069 := bbase (se 3 (by rfl) ⟨42575, by rfl⟩ : syracuseStep 227069 = 85151) (by norm_num)
theorem B227093 : Blo 147793 227093 := bbase (se 6 (by rfl) ⟨5322, by rfl⟩ : syracuseStep 227093 = 10645) (by norm_num)
theorem B161561 : Blo 147793 161561 := bbase (se 2 (by rfl) ⟨60585, by rfl⟩ : syracuseStep 161561 = 121171) (by norm_num)
theorem B227117 : Blo 147793 227117 := bbase (se 3 (by rfl) ⟨42584, by rfl⟩ : syracuseStep 227117 = 85169) (by norm_num)
theorem B227141 : Blo 147793 227141 := bbase (se 4 (by rfl) ⟨21294, by rfl⟩ : syracuseStep 227141 = 42589) (by norm_num)
theorem B227165 : Blo 147793 227165 := bbase (se 3 (by rfl) ⟨42593, by rfl⟩ : syracuseStep 227165 = 85187) (by norm_num)
theorem B161633 : Blo 147793 161633 := bbase (se 2 (by rfl) ⟨60612, by rfl⟩ : syracuseStep 161633 = 121225) (by norm_num)
theorem B227189 : Blo 147793 227189 := bbase (se 5 (by rfl) ⟨10649, by rfl⟩ : syracuseStep 227189 = 21299) (by norm_num)
theorem B227213 : Blo 147793 227213 := bbase (se 3 (by rfl) ⟨42602, by rfl⟩ : syracuseStep 227213 = 85205) (by norm_num)
theorem B227237 : Blo 147793 227237 := bbase (se 4 (by rfl) ⟨21303, by rfl⟩ : syracuseStep 227237 = 42607) (by norm_num)
theorem B227261 : Blo 147793 227261 := bbase (se 3 (by rfl) ⟨42611, by rfl⟩ : syracuseStep 227261 = 85223) (by norm_num)
theorem B227285 : Blo 147793 227285 := bbase (se 7 (by rfl) ⟨2663, by rfl⟩ : syracuseStep 227285 = 5327) (by norm_num)
theorem B227309 : Blo 147793 227309 := bbase (se 3 (by rfl) ⟨42620, by rfl⟩ : syracuseStep 227309 = 85241) (by norm_num)
theorem B227333 : Blo 147793 227333 := bbase (se 4 (by rfl) ⟨21312, by rfl⟩ : syracuseStep 227333 = 42625) (by norm_num)
theorem B161821 : Blo 147793 161821 := bbase (se 3 (by rfl) ⟨30341, by rfl⟩ : syracuseStep 161821 = 60683) (by norm_num)
theorem B227357 : Blo 147793 227357 := bbase (se 3 (by rfl) ⟨42629, by rfl⟩ : syracuseStep 227357 = 85259) (by norm_num)
theorem B227381 : Blo 147793 227381 := bbase (se 5 (by rfl) ⟨10658, by rfl⟩ : syracuseStep 227381 = 21317) (by norm_num)
theorem B227405 : Blo 147793 227405 := bbase (se 3 (by rfl) ⟨42638, by rfl⟩ : syracuseStep 227405 = 85277) (by norm_num)
theorem B227429 : Blo 147793 227429 := bbase (se 4 (by rfl) ⟨21321, by rfl⟩ : syracuseStep 227429 = 42643) (by norm_num)
theorem B227453 : Blo 147793 227453 := bbase (se 3 (by rfl) ⟨42647, by rfl⟩ : syracuseStep 227453 = 85295) (by norm_num)
theorem B227477 : Blo 147793 227477 := bbase (se 6 (by rfl) ⟨5331, by rfl⟩ : syracuseStep 227477 = 10663) (by norm_num)
theorem B227501 : Blo 147793 227501 := bbase (se 3 (by rfl) ⟨42656, by rfl⟩ : syracuseStep 227501 = 85313) (by norm_num)
theorem B719045 : Blo 147793 719045 := bbase (se 4 (by rfl) ⟨67410, by rfl⟩ : syracuseStep 719045 = 134821) (by norm_num)
theorem B227525 : Blo 147793 227525 := bbase (se 4 (by rfl) ⟨21330, by rfl⟩ : syracuseStep 227525 = 42661) (by norm_num)
theorem B162005 : Blo 147793 162005 := bbase (se 7 (by rfl) ⟨1898, by rfl⟩ : syracuseStep 162005 = 3797) (by norm_num)
theorem B227549 : Blo 147793 227549 := bbase (se 3 (by rfl) ⟨42665, by rfl⟩ : syracuseStep 227549 = 85331) (by norm_num)
theorem B227573 : Blo 147793 227573 := bbase (se 5 (by rfl) ⟨10667, by rfl⟩ : syracuseStep 227573 = 21335) (by norm_num)
theorem B227597 : Blo 147793 227597 := bbase (se 3 (by rfl) ⟨42674, by rfl⟩ : syracuseStep 227597 = 85349) (by norm_num)
theorem B227621 : Blo 147793 227621 := bbase (se 4 (by rfl) ⟨21339, by rfl⟩ : syracuseStep 227621 = 42679) (by norm_num)
theorem B227645 : Blo 147793 227645 := bbase (se 3 (by rfl) ⟨42683, by rfl⟩ : syracuseStep 227645 = 85367) (by norm_num)
theorem B227669 : Blo 147793 227669 := bbase (se 10 (by rfl) ⟨333, by rfl⟩ : syracuseStep 227669 = 667) (by norm_num)
theorem B227701 : Blo 147793 227701 := bbase (se 5 (by rfl) ⟨10673, by rfl⟩ : syracuseStep 227701 = 21347) (by norm_num)
theorem B752165 : Blo 147793 752165 := bbase (se 4 (by rfl) ⟨70515, by rfl⟩ : syracuseStep 752165 = 141031) (by norm_num)
theorem B457285 : Blo 147793 457285 := bbase (se 4 (by rfl) ⟨42870, by rfl⟩ : syracuseStep 457285 = 85741) (by norm_num)
theorem B359005 : Blo 147793 359005 := bbase (se 3 (by rfl) ⟨67313, by rfl⟩ : syracuseStep 359005 = 134627) (by norm_num)
theorem B424597 : Blo 147793 424597 := bbase (se 6 (by rfl) ⟨9951, by rfl⟩ : syracuseStep 424597 = 19903) (by norm_num)
theorem B1276661 : Blo 147793 1276661 := bbase (se 5 (by rfl) ⟨59843, by rfl⟩ : syracuseStep 1276661 = 119687) (by norm_num)
theorem B424757 : Blo 147793 424757 := bbase (se 5 (by rfl) ⟨19910, by rfl⟩ : syracuseStep 424757 = 39821) (by norm_num)
theorem B424997 : Blo 147793 424997 := bbase (se 4 (by rfl) ⟨39843, by rfl⟩ : syracuseStep 424997 = 79687) (by norm_num)
theorem B326741 : Blo 147793 326741 := bbase (se 8 (by rfl) ⟨1914, by rfl⟩ : syracuseStep 326741 = 3829) (by norm_num)
theorem B425189 : Blo 147793 425189 := bbase (se 4 (by rfl) ⟨39861, by rfl⟩ : syracuseStep 425189 = 79723) (by norm_num)
theorem B851381 : Blo 147793 851381 := bbase (se 5 (by rfl) ⟨39908, by rfl⟩ : syracuseStep 851381 = 79817) (by norm_num)
theorem B753461 : Blo 147793 753461 := bbase (se 5 (by rfl) ⟨35318, by rfl⟩ : syracuseStep 753461 = 70637) (by norm_num)
theorem B556949 : Blo 147793 556949 := bbase (se 6 (by rfl) ⟨13053, by rfl⟩ : syracuseStep 556949 = 26107) (by norm_num)
theorem B360389 : Blo 147793 360389 := bbase (se 4 (by rfl) ⟨33786, by rfl⟩ : syracuseStep 360389 = 67573) (by norm_num)
theorem B688589 : Blo 147793 688589 := bstep (se 3 (by rfl) ⟨129110, by rfl⟩ : syracuseStep 688589 = 258221) B258221
theorem B295825 : Blo 147793 295825 := bstep (se 2 (by rfl) ⟨110934, by rfl⟩ : syracuseStep 295825 = 221869) B221869
theorem B754595 : Blo 147793 754595 := bstep (se 1 (by rfl) ⟨565946, by rfl⟩ : syracuseStep 754595 = 1131893) B1131893
theorem B853091 : Blo 147793 853091 := bstep (se 1 (by rfl) ⟨639818, by rfl⟩ : syracuseStep 853091 = 1279637) B1279637
theorem B460081 : Blo 147793 460081 := bstep (se 2 (by rfl) ⟨172530, by rfl⟩ : syracuseStep 460081 = 345061) B345061
theorem B427331 : Blo 147793 427331 := bstep (se 1 (by rfl) ⟨320498, by rfl⟩ : syracuseStep 427331 = 640997) B640997
theorem B755021 : Blo 147793 755021 := bstep (se 3 (by rfl) ⟨141566, by rfl⟩ : syracuseStep 755021 = 283133) B283133
theorem B952013 : Blo 147793 952013 := bstep (se 3 (by rfl) ⟨178502, by rfl⟩ : syracuseStep 952013 = 357005) B357005
theorem B755405 : Blo 147793 755405 := bstep (se 3 (by rfl) ⟨141638, by rfl⟩ : syracuseStep 755405 = 283277) B283277
theorem B689905 : Blo 147793 689905 := bstep (se 2 (by rfl) ⟨258714, by rfl⟩ : syracuseStep 689905 = 517429) B517429
theorem B723043 : Blo 147793 723043 := bstep (se 1 (by rfl) ⟨542282, by rfl⟩ : syracuseStep 723043 = 1084565) B1084565
theorem B166387 : Blo 147793 166387 := bstep (se 1 (by rfl) ⟨124790, by rfl⟩ : syracuseStep 166387 = 249581) B249581
theorem B428561 : Blo 147793 428561 := bstep (se 2 (by rfl) ⟨160710, by rfl⟩ : syracuseStep 428561 = 321421) B321421
theorem B723505 : Blo 147793 723505 := bstep (se 2 (by rfl) ⟨271314, by rfl⟩ : syracuseStep 723505 = 542629) B542629
theorem B166531 : Blo 147793 166531 := bstep (se 1 (by rfl) ⟨124898, by rfl⟩ : syracuseStep 166531 = 249797) B249797
theorem B166675 : Blo 147793 166675 := bstep (se 1 (by rfl) ⟨125006, by rfl⟩ : syracuseStep 166675 = 250013) B250013
theorem B166819 : Blo 147793 166819 := bstep (se 1 (by rfl) ⟨125114, by rfl⟩ : syracuseStep 166819 = 250229) B250229
theorem B854981 : Blo 147793 854981 := bstep (se 4 (by rfl) ⟨80154, by rfl⟩ : syracuseStep 854981 = 160309) B160309
theorem B166963 : Blo 147793 166963 := bstep (se 1 (by rfl) ⟨125222, by rfl⟩ : syracuseStep 166963 = 250445) B250445
theorem B167107 : Blo 147793 167107 := bstep (se 1 (by rfl) ⟨125330, by rfl⟩ : syracuseStep 167107 = 250661) B250661
theorem B1707317 : Blo 147793 1707317 := bstep (se 5 (by rfl) ⟨80030, by rfl⟩ : syracuseStep 1707317 = 160061) B160061
theorem B167251 : Blo 147793 167251 := bstep (se 1 (by rfl) ⟨125438, by rfl⟩ : syracuseStep 167251 = 250877) B250877
theorem B167395 : Blo 147793 167395 := bstep (se 1 (by rfl) ⟨125546, by rfl⟩ : syracuseStep 167395 = 251093) B251093
theorem B1084913 : Blo 147793 1084913 := bstep (se 2 (by rfl) ⟨406842, by rfl⟩ : syracuseStep 1084913 = 813685) B813685
theorem B3640945 : Blo 147793 3640945 := bstep (se 2 (by rfl) ⟨1365354, by rfl⟩ : syracuseStep 3640945 = 2730709) B2730709
theorem B167539 : Blo 147793 167539 := bstep (se 1 (by rfl) ⟨125654, by rfl⟩ : syracuseStep 167539 = 251309) B251309
theorem B167683 : Blo 147793 167683 := bstep (se 1 (by rfl) ⟨125762, by rfl⟩ : syracuseStep 167683 = 251525) B251525
theorem B167827 : Blo 147793 167827 := bstep (se 1 (by rfl) ⟨125870, by rfl⟩ : syracuseStep 167827 = 251741) B251741
theorem B430019 : Blo 147793 430019 := bstep (se 1 (by rfl) ⟨322514, by rfl⟩ : syracuseStep 430019 = 645029) B645029
theorem B167971 : Blo 147793 167971 := bstep (se 1 (by rfl) ⟨125978, by rfl⟩ : syracuseStep 167971 = 251957) B251957
theorem B364675 : Blo 147793 364675 := bstep (se 1 (by rfl) ⟨273506, by rfl⟩ : syracuseStep 364675 = 547013) B547013
theorem B2330765 : Blo 147793 2330765 := bstep (se 3 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 2330765 = 874037) B874037
theorem B692387 : Blo 147793 692387 := bstep (se 1 (by rfl) ⟨519290, by rfl⟩ : syracuseStep 692387 = 1038581) B1038581
theorem B168115 : Blo 147793 168115 := bstep (se 1 (by rfl) ⟨126086, by rfl⟩ : syracuseStep 168115 = 252173) B252173
theorem B168259 : Blo 147793 168259 := bstep (se 1 (by rfl) ⟨126194, by rfl⟩ : syracuseStep 168259 = 252389) B252389
theorem B790897 : Blo 147793 790897 := bstep (se 2 (by rfl) ⟨296586, by rfl⟩ : syracuseStep 790897 = 593173) B593173
theorem B168403 : Blo 147793 168403 := bstep (se 1 (by rfl) ⟨126302, by rfl⟩ : syracuseStep 168403 = 252605) B252605
theorem B758321 : Blo 147793 758321 := bstep (se 2 (by rfl) ⟨284370, by rfl⟩ : syracuseStep 758321 = 568741) B568741
theorem B168547 : Blo 147793 168547 := bstep (se 1 (by rfl) ⟨126410, by rfl⟩ : syracuseStep 168547 = 252821) B252821
theorem B430829 : Blo 147793 430829 := bstep (se 3 (by rfl) ⟨80780, by rfl⟩ : syracuseStep 430829 = 161561) B161561
theorem B168691 : Blo 147793 168691 := bstep (se 1 (by rfl) ⟨126518, by rfl⟩ : syracuseStep 168691 = 253037) B253037
theorem B332657 : Blo 147793 332657 := bstep (se 2 (by rfl) ⟨124746, by rfl⟩ : syracuseStep 332657 = 249493) B249493
theorem B332675 : Blo 147793 332675 := bstep (se 1 (by rfl) ⟨249506, by rfl⟩ : syracuseStep 332675 = 499013) B499013
theorem B168835 : Blo 147793 168835 := bstep (se 1 (by rfl) ⟨126626, by rfl⟩ : syracuseStep 168835 = 253253) B253253
theorem B431021 : Blo 147793 431021 := bstep (se 3 (by rfl) ⟨80816, by rfl⟩ : syracuseStep 431021 = 161633) B161633
theorem B168979 : Blo 147793 168979 := bstep (se 1 (by rfl) ⟨126734, by rfl⟩ : syracuseStep 168979 = 253469) B253469
theorem B562211 : Blo 147793 562211 := bstep (se 1 (by rfl) ⟨421658, by rfl⟩ : syracuseStep 562211 = 843317) B843317
theorem B332945 : Blo 147793 332945 := bstep (se 2 (by rfl) ⟨124854, by rfl⟩ : syracuseStep 332945 = 249709) B249709
theorem B332963 : Blo 147793 332963 := bstep (se 1 (by rfl) ⟨249722, by rfl⟩ : syracuseStep 332963 = 499445) B499445
theorem B169123 : Blo 147793 169123 := bstep (se 1 (by rfl) ⟨126842, by rfl⟩ : syracuseStep 169123 = 253685) B253685
theorem B169267 : Blo 147793 169267 := bstep (se 1 (by rfl) ⟨126950, by rfl⟩ : syracuseStep 169267 = 253901) B253901
theorem B333233 : Blo 147793 333233 := bstep (se 2 (by rfl) ⟨124962, by rfl⟩ : syracuseStep 333233 = 249925) B249925
theorem B333251 : Blo 147793 333251 := bstep (se 1 (by rfl) ⟨249938, by rfl⟩ : syracuseStep 333251 = 499877) B499877
theorem B169411 : Blo 147793 169411 := bstep (se 1 (by rfl) ⟨127058, by rfl⟩ : syracuseStep 169411 = 254117) B254117
theorem B726563 : Blo 147793 726563 := bstep (se 1 (by rfl) ⟨544922, by rfl⟩ : syracuseStep 726563 = 1089845) B1089845
theorem B169555 : Blo 147793 169555 := bstep (se 1 (by rfl) ⟨127166, by rfl⟩ : syracuseStep 169555 = 254333) B254333
theorem B333521 : Blo 147793 333521 := bstep (se 2 (by rfl) ⟨125070, by rfl⟩ : syracuseStep 333521 = 250141) B250141
theorem B267985 : Blo 147793 267985 := bstep (se 2 (by rfl) ⟨100494, by rfl⟩ : syracuseStep 267985 = 200989) B200989
theorem B333539 : Blo 147793 333539 := bstep (se 1 (by rfl) ⟨250154, by rfl⟩ : syracuseStep 333539 = 500309) B500309
theorem B169699 : Blo 147793 169699 := bstep (se 1 (by rfl) ⟨127274, by rfl⟩ : syracuseStep 169699 = 254549) B254549
theorem B1709923 : Blo 147793 1709923 := bstep (se 1 (by rfl) ⟨1282442, by rfl⟩ : syracuseStep 1709923 = 2564885) B2564885
theorem B169843 : Blo 147793 169843 := bstep (se 1 (by rfl) ⟨127382, by rfl⟩ : syracuseStep 169843 = 254765) B254765
theorem B432013 : Blo 147793 432013 := bstep (se 3 (by rfl) ⟨81002, by rfl⟩ : syracuseStep 432013 = 162005) B162005
theorem B759779 : Blo 147793 759779 := bstep (se 1 (by rfl) ⟨569834, by rfl⟩ : syracuseStep 759779 = 1139669) B1139669
theorem B333809 : Blo 147793 333809 := bstep (se 2 (by rfl) ⟨125178, by rfl⟩ : syracuseStep 333809 = 250357) B250357
theorem B333827 : Blo 147793 333827 := bstep (se 1 (by rfl) ⟨250370, by rfl⟩ : syracuseStep 333827 = 500741) B500741
theorem B169987 : Blo 147793 169987 := bstep (se 1 (by rfl) ⟨127490, by rfl⟩ : syracuseStep 169987 = 254981) B254981
theorem B563213 : Blo 147793 563213 := bstep (se 3 (by rfl) ⟨105602, by rfl⟩ : syracuseStep 563213 = 211205) B211205
theorem B170131 : Blo 147793 170131 := bstep (se 1 (by rfl) ⟨127598, by rfl⟩ : syracuseStep 170131 = 255197) B255197
theorem B170195 : Blo 147793 170195 := bstep (se 1 (by rfl) ⟨127646, by rfl⟩ : syracuseStep 170195 = 255293) B255293
theorem B2070755 : Blo 147793 2070755 := bstep (se 1 (by rfl) ⟨1553066, by rfl⟩ : syracuseStep 2070755 = 3106133) B3106133
theorem B334097 : Blo 147793 334097 := bstep (se 2 (by rfl) ⟨125286, by rfl⟩ : syracuseStep 334097 = 250573) B250573
theorem B334115 : Blo 147793 334115 := bstep (se 1 (by rfl) ⟨250586, by rfl⟩ : syracuseStep 334115 = 501173) B501173
theorem B170275 : Blo 147793 170275 := bstep (se 1 (by rfl) ⟨127706, by rfl⟩ : syracuseStep 170275 = 255413) B255413
theorem B170419 : Blo 147793 170419 := bstep (se 1 (by rfl) ⟨127814, by rfl⟩ : syracuseStep 170419 = 255629) B255629
theorem B268771 : Blo 147793 268771 := bstep (se 1 (by rfl) ⟨201578, by rfl⟩ : syracuseStep 268771 = 403157) B403157
theorem B203249 : Blo 147793 203249 := bstep (se 2 (by rfl) ⟨76218, by rfl⟩ : syracuseStep 203249 = 152437) B152437
theorem B334385 : Blo 147793 334385 := bstep (se 2 (by rfl) ⟨125394, by rfl⟩ : syracuseStep 334385 = 250789) B250789
theorem B334403 : Blo 147793 334403 := bstep (se 1 (by rfl) ⟨250802, by rfl⟩ : syracuseStep 334403 = 501605) B501605
theorem B170563 : Blo 147793 170563 := bstep (se 1 (by rfl) ⟨127922, by rfl⟩ : syracuseStep 170563 = 255845) B255845
theorem B498317 : Blo 147793 498317 := bstep (se 3 (by rfl) ⟨93434, by rfl⟩ : syracuseStep 498317 = 186869) B186869
theorem B170707 : Blo 147793 170707 := bstep (se 1 (by rfl) ⟨128030, by rfl⟩ : syracuseStep 170707 = 256061) B256061
theorem B760589 : Blo 147793 760589 := bstep (se 3 (by rfl) ⟨142610, by rfl⟩ : syracuseStep 760589 = 285221) B285221
theorem B334673 : Blo 147793 334673 := bstep (se 2 (by rfl) ⟨125502, by rfl⟩ : syracuseStep 334673 = 251005) B251005
theorem B334691 : Blo 147793 334691 := bstep (se 1 (by rfl) ⟨251018, by rfl⟩ : syracuseStep 334691 = 502037) B502037
theorem B203827 : Blo 147793 203827 := bstep (se 1 (by rfl) ⟨152870, by rfl⟩ : syracuseStep 203827 = 305741) B305741
theorem B334961 : Blo 147793 334961 := bstep (se 2 (by rfl) ⟨125610, by rfl⟩ : syracuseStep 334961 = 251221) B251221
theorem B334979 : Blo 147793 334979 := bstep (se 1 (by rfl) ⟨251234, by rfl⟩ : syracuseStep 334979 = 502469) B502469
theorem B498851 : Blo 147793 498851 := bstep (se 1 (by rfl) ⟨374138, by rfl⟩ : syracuseStep 498851 = 748277) B748277
theorem B400657 : Blo 147793 400657 := bstep (se 2 (by rfl) ⟨150246, by rfl⟩ : syracuseStep 400657 = 300493) B300493
theorem B204083 : Blo 147793 204083 := bstep (se 1 (by rfl) ⟨153062, by rfl⟩ : syracuseStep 204083 = 306125) B306125
theorem B335249 : Blo 147793 335249 := bstep (se 2 (by rfl) ⟨125718, by rfl⟩ : syracuseStep 335249 = 251437) B251437
theorem B335267 : Blo 147793 335267 := bstep (se 1 (by rfl) ⟨251450, by rfl⟩ : syracuseStep 335267 = 502901) B502901
theorem B499121 : Blo 147793 499121 := bstep (se 2 (by rfl) ⟨187170, by rfl⟩ : syracuseStep 499121 = 374341) B374341
theorem B400909 : Blo 147793 400909 := bstep (se 3 (by rfl) ⟨75170, by rfl⟩ : syracuseStep 400909 = 150341) B150341
theorem B269873 : Blo 147793 269873 := bstep (se 2 (by rfl) ⟨101202, by rfl⟩ : syracuseStep 269873 = 202405) B202405
theorem B335537 : Blo 147793 335537 := bstep (se 2 (by rfl) ⟨125826, by rfl⟩ : syracuseStep 335537 = 251653) B251653
theorem B335555 : Blo 147793 335555 := bstep (se 1 (by rfl) ⟨251666, by rfl⟩ : syracuseStep 335555 = 503333) B503333
theorem B499661 : Blo 147793 499661 := bstep (se 3 (by rfl) ⟨93686, by rfl⟩ : syracuseStep 499661 = 187373) B187373
theorem B335825 : Blo 147793 335825 := bstep (se 2 (by rfl) ⟨125934, by rfl⟩ : syracuseStep 335825 = 251869) B251869
theorem B335843 : Blo 147793 335843 := bstep (se 1 (by rfl) ⟨251882, by rfl⟩ : syracuseStep 335843 = 503765) B503765
theorem B499715 : Blo 147793 499715 := bstep (se 1 (by rfl) ⟨374786, by rfl⟩ : syracuseStep 499715 = 749573) B749573
theorem B958499 : Blo 147793 958499 := bstep (se 1 (by rfl) ⟨718874, by rfl⟩ : syracuseStep 958499 = 1437749) B1437749
theorem B565325 : Blo 147793 565325 := bstep (se 3 (by rfl) ⟨105998, by rfl⟩ : syracuseStep 565325 = 211997) B211997
theorem B237683 : Blo 147793 237683 := bstep (se 1 (by rfl) ⟨178262, by rfl⟩ : syracuseStep 237683 = 356525) B356525
theorem B2138339 : Blo 147793 2138339 := bstep (se 1 (by rfl) ⟨1603754, by rfl⟩ : syracuseStep 2138339 = 3207509) B3207509
theorem B336113 : Blo 147793 336113 := bstep (se 2 (by rfl) ⟨126042, by rfl⟩ : syracuseStep 336113 = 252085) B252085
theorem B237811 : Blo 147793 237811 := bstep (se 1 (by rfl) ⟨178358, by rfl⟩ : syracuseStep 237811 = 356717) B356717
theorem B336131 : Blo 147793 336131 := bstep (se 1 (by rfl) ⟨252098, by rfl⟩ : syracuseStep 336131 = 504197) B504197
theorem B499985 : Blo 147793 499985 := bstep (se 2 (by rfl) ⟨187494, by rfl⟩ : syracuseStep 499985 = 374989) B374989
theorem B1122659 : Blo 147793 1122659 := bstep (se 1 (by rfl) ⟨841994, by rfl⟩ : syracuseStep 1122659 = 1683989) B1683989
theorem B401773 : Blo 147793 401773 := bstep (se 3 (by rfl) ⟨75332, by rfl⟩ : syracuseStep 401773 = 150665) B150665
theorem B237953 : Blo 147793 237953 := bstep (se 2 (by rfl) ⟨89232, by rfl⟩ : syracuseStep 237953 = 178465) B178465
theorem B303601 : Blo 147793 303601 := bstep (se 2 (by rfl) ⟨113850, by rfl⟩ : syracuseStep 303601 = 227701) B227701
theorem B336401 : Blo 147793 336401 := bstep (se 2 (by rfl) ⟨126150, by rfl⟩ : syracuseStep 336401 = 252301) B252301
theorem B336419 : Blo 147793 336419 := bstep (se 1 (by rfl) ⟨252314, by rfl⟩ : syracuseStep 336419 = 504629) B504629
theorem B860813 : Blo 147793 860813 := bstep (se 3 (by rfl) ⟨161402, by rfl⟩ : syracuseStep 860813 = 322805) B322805
theorem B238241 : Blo 147793 238241 := bstep (se 2 (by rfl) ⟨89340, by rfl⟩ : syracuseStep 238241 = 178681) B178681
theorem B500525 : Blo 147793 500525 := bstep (se 3 (by rfl) ⟨93848, by rfl⟩ : syracuseStep 500525 = 187697) B187697
theorem B336689 : Blo 147793 336689 := bstep (se 2 (by rfl) ⟨126258, by rfl⟩ : syracuseStep 336689 = 252517) B252517
theorem B336707 : Blo 147793 336707 := bstep (se 1 (by rfl) ⟨252530, by rfl⟩ : syracuseStep 336707 = 505061) B505061
theorem B500579 : Blo 147793 500579 := bstep (se 1 (by rfl) ⟨375434, by rfl⟩ : syracuseStep 500579 = 750869) B750869
theorem B566129 : Blo 147793 566129 := bstep (se 2 (by rfl) ⟨212298, by rfl⟩ : syracuseStep 566129 = 424597) B424597
theorem B336977 : Blo 147793 336977 := bstep (se 2 (by rfl) ⟨126366, by rfl⟩ : syracuseStep 336977 = 252733) B252733
theorem B205907 : Blo 147793 205907 := bstep (se 1 (by rfl) ⟨154430, by rfl⟩ : syracuseStep 205907 = 308861) B308861
theorem B631907 : Blo 147793 631907 := bstep (se 1 (by rfl) ⟨473930, by rfl⟩ : syracuseStep 631907 = 947861) B947861
theorem B336995 : Blo 147793 336995 := bstep (se 1 (by rfl) ⟨252746, by rfl⟩ : syracuseStep 336995 = 505493) B505493
theorem B271459 : Blo 147793 271459 := bstep (se 1 (by rfl) ⟨203594, by rfl⟩ : syracuseStep 271459 = 407189) B407189
theorem B500849 : Blo 147793 500849 := bstep (se 2 (by rfl) ⟨187818, by rfl⟩ : syracuseStep 500849 = 375637) B375637
theorem B402691 : Blo 147793 402691 := bstep (se 1 (by rfl) ⟨302018, by rfl⟩ : syracuseStep 402691 = 604037) B604037
theorem B271633 : Blo 147793 271633 := bstep (se 2 (by rfl) ⟨101862, by rfl⟩ : syracuseStep 271633 = 203725) B203725
theorem B402733 : Blo 147793 402733 := bstep (se 3 (by rfl) ⟨75512, by rfl⟩ : syracuseStep 402733 = 151025) B151025
theorem B337265 : Blo 147793 337265 := bstep (se 2 (by rfl) ⟨126474, by rfl⟩ : syracuseStep 337265 = 252949) B252949
theorem B337283 : Blo 147793 337283 := bstep (se 1 (by rfl) ⟨252962, by rfl⟩ : syracuseStep 337283 = 505925) B505925
theorem B239041 : Blo 147793 239041 := bstep (se 2 (by rfl) ⟨89640, by rfl⟩ : syracuseStep 239041 = 179281) B179281
theorem B566797 : Blo 147793 566797 := bstep (se 3 (by rfl) ⟨106274, by rfl⟩ : syracuseStep 566797 = 212549) B212549
theorem B763505 : Blo 147793 763505 := bstep (se 2 (by rfl) ⟨286314, by rfl⟩ : syracuseStep 763505 = 572629) B572629
theorem B501389 : Blo 147793 501389 := bstep (se 3 (by rfl) ⟨94010, by rfl⟩ : syracuseStep 501389 = 188021) B188021
theorem B337553 : Blo 147793 337553 := bstep (se 2 (by rfl) ⟨126582, by rfl⟩ : syracuseStep 337553 = 253165) B253165
theorem B337571 : Blo 147793 337571 := bstep (se 1 (by rfl) ⟨253178, by rfl⟩ : syracuseStep 337571 = 506357) B506357
theorem B501443 : Blo 147793 501443 := bstep (se 1 (by rfl) ⟨376082, by rfl⟩ : syracuseStep 501443 = 752165) B752165
theorem B337841 : Blo 147793 337841 := bstep (se 2 (by rfl) ⟨126690, by rfl⟩ : syracuseStep 337841 = 253381) B253381
theorem B337859 : Blo 147793 337859 := bstep (se 1 (by rfl) ⟨253394, by rfl⟩ : syracuseStep 337859 = 506789) B506789
theorem B501713 : Blo 147793 501713 := bstep (se 2 (by rfl) ⟨188142, by rfl⟩ : syracuseStep 501713 = 376285) B376285
theorem B338129 : Blo 147793 338129 := bstep (se 2 (by rfl) ⟨126798, by rfl⟩ : syracuseStep 338129 = 253597) B253597
theorem B338147 : Blo 147793 338147 := bstep (se 1 (by rfl) ⟨253610, by rfl⟩ : syracuseStep 338147 = 507221) B507221
theorem B567587 : Blo 147793 567587 := bstep (se 1 (by rfl) ⟨425690, by rfl⟩ : syracuseStep 567587 = 851381) B851381
theorem B3909941 : Blo 147793 3909941 := bstep (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) B366557
theorem B502253 : Blo 147793 502253 := bstep (se 3 (by rfl) ⟨94172, by rfl⟩ : syracuseStep 502253 = 188345) B188345
theorem B338417 : Blo 147793 338417 := bstep (se 2 (by rfl) ⟨126906, by rfl⟩ : syracuseStep 338417 = 253813) B253813
theorem B338435 : Blo 147793 338435 := bstep (se 1 (by rfl) ⟨253826, by rfl⟩ : syracuseStep 338435 = 507653) B507653
theorem B502307 : Blo 147793 502307 := bstep (se 1 (by rfl) ⟨376730, by rfl⟩ : syracuseStep 502307 = 753461) B753461
theorem B272945 : Blo 147793 272945 := bstep (se 2 (by rfl) ⟨102354, by rfl⟩ : syracuseStep 272945 = 204709) B204709
theorem B371299 : Blo 147793 371299 := bstep (se 1 (by rfl) ⟨278474, by rfl⟩ : syracuseStep 371299 = 556949) B556949
theorem B240259 : Blo 147793 240259 := bstep (se 1 (by rfl) ⟨180194, by rfl⟩ : syracuseStep 240259 = 360389) B360389
theorem B338705 : Blo 147793 338705 := bstep (se 2 (by rfl) ⟨127014, by rfl⟩ : syracuseStep 338705 = 254029) B254029
theorem B338723 : Blo 147793 338723 := bstep (se 1 (by rfl) ⟨254042, by rfl⟩ : syracuseStep 338723 = 508085) B508085
theorem B502577 : Blo 147793 502577 := bstep (se 2 (by rfl) ⟨188466, by rfl⟩ : syracuseStep 502577 = 376933) B376933
theorem B404291 : Blo 147793 404291 := bstep (se 1 (by rfl) ⟨303218, by rfl⟩ : syracuseStep 404291 = 606437) B606437
theorem B863045 : Blo 147793 863045 := bstep (se 4 (by rfl) ⟨80910, by rfl⟩ : syracuseStep 863045 = 161821) B161821
theorem B273233 : Blo 147793 273233 := bstep (se 2 (by rfl) ⟨102462, by rfl⟩ : syracuseStep 273233 = 204925) B204925
theorem B863075 : Blo 147793 863075 := bstep (se 1 (by rfl) ⟨647306, by rfl⟩ : syracuseStep 863075 = 1294613) B1294613
theorem B568241 : Blo 147793 568241 := bstep (se 2 (by rfl) ⟨213090, by rfl⟩ : syracuseStep 568241 = 426181) B426181
theorem B764963 : Blo 147793 764963 := bstep (se 1 (by rfl) ⟨573722, by rfl⟩ : syracuseStep 764963 = 1147445) B1147445
theorem B338993 : Blo 147793 338993 := bstep (se 2 (by rfl) ⟨127122, by rfl⟩ : syracuseStep 338993 = 254245) B254245
theorem B339011 : Blo 147793 339011 := bstep (se 1 (by rfl) ⟨254258, by rfl⟩ : syracuseStep 339011 = 508517) B508517
theorem B11775203 : Blo 147793 11775203 := bstep (se 1 (by rfl) ⟨8831402, by rfl⟩ : syracuseStep 11775203 = 17662805) B17662805
theorem B503117 : Blo 147793 503117 := bstep (se 3 (by rfl) ⟨94334, by rfl⟩ : syracuseStep 503117 = 188669) B188669
theorem B240977 : Blo 147793 240977 := bstep (se 2 (by rfl) ⟨90366, by rfl⟩ : syracuseStep 240977 = 180733) B180733
theorem B339281 : Blo 147793 339281 := bstep (se 2 (by rfl) ⟨127230, by rfl⟩ : syracuseStep 339281 = 254461) B254461
theorem B339299 : Blo 147793 339299 := bstep (se 1 (by rfl) ⟨254474, by rfl⟩ : syracuseStep 339299 = 508949) B508949
theorem B2567537 : Blo 147793 2567537 := bstep (se 2 (by rfl) ⟨962826, by rfl⟩ : syracuseStep 2567537 = 1925653) B1925653
theorem B503171 : Blo 147793 503171 := bstep (se 1 (by rfl) ⟨377378, by rfl⟩ : syracuseStep 503171 = 754757) B754757
theorem B3452357 : Blo 147793 3452357 := bstep (se 4 (by rfl) ⟨323658, by rfl⟩ : syracuseStep 3452357 = 647317) B647317
theorem B1027525 : Blo 147793 1027525 := bstep (se 4 (by rfl) ⟨96330, by rfl⟩ : syracuseStep 1027525 = 192661) B192661
theorem B765389 : Blo 147793 765389 := bstep (se 3 (by rfl) ⟨143510, by rfl⟩ : syracuseStep 765389 = 287021) B287021
theorem B863729 : Blo 147793 863729 := bstep (se 2 (by rfl) ⟨323898, by rfl⟩ : syracuseStep 863729 = 647797) B647797
theorem B405005 : Blo 147793 405005 := bstep (se 3 (by rfl) ⟨75938, by rfl⟩ : syracuseStep 405005 = 151877) B151877
theorem B405091 : Blo 147793 405091 := bstep (se 1 (by rfl) ⟨303818, by rfl⟩ : syracuseStep 405091 = 607637) B607637
theorem B241265 : Blo 147793 241265 := bstep (se 2 (by rfl) ⟨90474, by rfl⟩ : syracuseStep 241265 = 180949) B180949
theorem B339569 : Blo 147793 339569 := bstep (se 2 (by rfl) ⟨127338, by rfl⟩ : syracuseStep 339569 = 254677) B254677
theorem B339587 : Blo 147793 339587 := bstep (se 1 (by rfl) ⟨254690, by rfl⟩ : syracuseStep 339587 = 509381) B509381
theorem B962189 : Blo 147793 962189 := bstep (se 3 (by rfl) ⟨180410, by rfl⟩ : syracuseStep 962189 = 360821) B360821
theorem B503441 : Blo 147793 503441 := bstep (se 2 (by rfl) ⟨188790, by rfl⟩ : syracuseStep 503441 = 377581) B377581
theorem B405233 : Blo 147793 405233 := bstep (se 2 (by rfl) ⟨151962, by rfl⟩ : syracuseStep 405233 = 303925) B303925
theorem B765773 : Blo 147793 765773 := bstep (se 3 (by rfl) ⟨143582, by rfl⟩ : syracuseStep 765773 = 287165) B287165
theorem B241489 : Blo 147793 241489 := bstep (se 2 (by rfl) ⟨90558, by rfl⟩ : syracuseStep 241489 = 181117) B181117
theorem B962417 : Blo 147793 962417 := bstep (se 2 (by rfl) ⟨360906, by rfl⟩ : syracuseStep 962417 = 721813) B721813
theorem B339857 : Blo 147793 339857 := bstep (se 2 (by rfl) ⟨127446, by rfl⟩ : syracuseStep 339857 = 254893) B254893
theorem B339875 : Blo 147793 339875 := bstep (se 1 (by rfl) ⟨254906, by rfl⟩ : syracuseStep 339875 = 509813) B509813
theorem B405425 : Blo 147793 405425 := bstep (se 2 (by rfl) ⟨152034, by rfl⟩ : syracuseStep 405425 = 304069) B304069
theorem B503981 : Blo 147793 503981 := bstep (se 3 (by rfl) ⟨94496, by rfl⟩ : syracuseStep 503981 = 188993) B188993
theorem B340145 : Blo 147793 340145 := bstep (se 2 (by rfl) ⟨127554, by rfl⟩ : syracuseStep 340145 = 255109) B255109
theorem B340163 : Blo 147793 340163 := bstep (se 1 (by rfl) ⟨255122, by rfl⟩ : syracuseStep 340163 = 510245) B510245
theorem B504035 : Blo 147793 504035 := bstep (se 1 (by rfl) ⟨378026, by rfl⟩ : syracuseStep 504035 = 756053) B756053
theorem B405805 : Blo 147793 405805 := bstep (se 3 (by rfl) ⟨76088, by rfl⟩ : syracuseStep 405805 = 152177) B152177
theorem B569699 : Blo 147793 569699 := bstep (se 1 (by rfl) ⟨427274, by rfl⟩ : syracuseStep 569699 = 854549) B854549
theorem B340337 : Blo 147793 340337 := bstep (se 2 (by rfl) ⟨127626, by rfl⟩ : syracuseStep 340337 = 255253) B255253
theorem B1618289 : Blo 147793 1618289 := bstep (se 2 (by rfl) ⟨606858, by rfl⟩ : syracuseStep 1618289 = 1213717) B1213717
theorem B569713 : Blo 147793 569713 := bstep (se 2 (by rfl) ⟨213642, by rfl⟩ : syracuseStep 569713 = 427285) B427285
theorem B930253 : Blo 147793 930253 := bstep (se 3 (by rfl) ⟨174422, by rfl⟩ : syracuseStep 930253 = 348845) B348845
theorem B340433 : Blo 147793 340433 := bstep (se 2 (by rfl) ⟨127662, by rfl⟩ : syracuseStep 340433 = 255325) B255325
theorem B340451 : Blo 147793 340451 := bstep (se 1 (by rfl) ⟨255338, by rfl⟩ : syracuseStep 340451 = 510677) B510677
theorem B504305 : Blo 147793 504305 := bstep (se 2 (by rfl) ⟨189114, by rfl⟩ : syracuseStep 504305 = 378229) B378229
theorem B406129 : Blo 147793 406129 := bstep (se 2 (by rfl) ⟨152298, by rfl⟩ : syracuseStep 406129 = 304597) B304597
theorem B635597 : Blo 147793 635597 := bstep (se 3 (by rfl) ⟨119174, by rfl⟩ : syracuseStep 635597 = 238349) B238349
theorem B635633 : Blo 147793 635633 := bstep (se 2 (by rfl) ⟨238362, by rfl⟩ : syracuseStep 635633 = 476725) B476725
theorem B340721 : Blo 147793 340721 := bstep (se 2 (by rfl) ⟨127770, by rfl⟩ : syracuseStep 340721 = 255541) B255541
theorem B340739 : Blo 147793 340739 := bstep (se 1 (by rfl) ⟨255554, by rfl⟩ : syracuseStep 340739 = 511109) B511109
theorem B504845 : Blo 147793 504845 := bstep (se 3 (by rfl) ⟨94658, by rfl⟩ : syracuseStep 504845 = 189317) B189317
theorem B341009 : Blo 147793 341009 := bstep (se 2 (by rfl) ⟨127878, by rfl⟩ : syracuseStep 341009 = 255757) B255757
theorem B341027 : Blo 147793 341027 := bstep (se 1 (by rfl) ⟨255770, by rfl⟩ : syracuseStep 341027 = 511541) B511541
theorem B504899 : Blo 147793 504899 := bstep (se 1 (by rfl) ⟨378674, by rfl⟩ : syracuseStep 504899 = 757349) B757349
theorem B373987 : Blo 147793 373987 := bstep (se 1 (by rfl) ⟨280490, by rfl⟩ : syracuseStep 373987 = 560981) B560981
theorem B341297 : Blo 147793 341297 := bstep (se 2 (by rfl) ⟨127986, by rfl⟩ : syracuseStep 341297 = 255973) B255973
theorem B341315 : Blo 147793 341315 := bstep (se 1 (by rfl) ⟨255986, by rfl⟩ : syracuseStep 341315 = 511973) B511973
theorem B505169 : Blo 147793 505169 := bstep (se 2 (by rfl) ⟨189438, by rfl⟩ : syracuseStep 505169 = 378877) B378877
theorem B374129 : Blo 147793 374129 := bstep (se 2 (by rfl) ⟨140298, by rfl⟩ : syracuseStep 374129 = 280597) B280597
theorem B243091 : Blo 147793 243091 := bstep (se 1 (by rfl) ⟨182318, by rfl⟩ : syracuseStep 243091 = 364637) B364637
theorem B374179 : Blo 147793 374179 := bstep (se 1 (by rfl) ⟨280634, by rfl⟩ : syracuseStep 374179 = 561269) B561269
theorem B374321 : Blo 147793 374321 := bstep (se 2 (by rfl) ⟨140370, by rfl⟩ : syracuseStep 374321 = 280741) B280741
theorem B1128005 : Blo 147793 1128005 := bstep (se 4 (by rfl) ⟨105750, by rfl⟩ : syracuseStep 1128005 = 211501) B211501
theorem B571171 : Blo 147793 571171 := bstep (se 1 (by rfl) ⟨428378, by rfl⟩ : syracuseStep 571171 = 856757) B856757
theorem B3094325 : Blo 147793 3094325 := bstep (se 5 (by rfl) ⟨145046, by rfl⟩ : syracuseStep 3094325 = 290093) B290093
theorem B505709 : Blo 147793 505709 := bstep (se 3 (by rfl) ⟨94820, by rfl⟩ : syracuseStep 505709 = 189641) B189641
theorem B407405 : Blo 147793 407405 := bstep (se 3 (by rfl) ⟨76388, by rfl⟩ : syracuseStep 407405 = 152777) B152777
theorem B505763 : Blo 147793 505763 := bstep (se 1 (by rfl) ⟨379322, by rfl⟩ : syracuseStep 505763 = 758645) B758645
theorem B178147 : Blo 147793 178147 := bstep (se 1 (by rfl) ⟨133610, by rfl⟩ : syracuseStep 178147 = 267221) B267221
theorem B211091 : Blo 147793 211091 := bstep (se 1 (by rfl) ⟨158318, by rfl⟩ : syracuseStep 211091 = 316637) B316637
theorem B506033 : Blo 147793 506033 := bstep (se 2 (by rfl) ⟨189762, by rfl⟩ : syracuseStep 506033 = 379525) B379525
theorem B1423601 : Blo 147793 1423601 := bstep (se 2 (by rfl) ⟨533850, by rfl⟩ : syracuseStep 1423601 = 1067701) B1067701
theorem B178531 : Blo 147793 178531 := bstep (se 1 (by rfl) ⟨133898, by rfl⟩ : syracuseStep 178531 = 267797) B267797
theorem B1227149 : Blo 147793 1227149 := bstep (se 3 (by rfl) ⟨230090, by rfl⟩ : syracuseStep 1227149 = 460181) B460181
theorem B375313 : Blo 147793 375313 := bstep (se 2 (by rfl) ⟨140742, by rfl⟩ : syracuseStep 375313 = 281485) B281485
theorem B309955 : Blo 147793 309955 := bstep (se 1 (by rfl) ⟨232466, by rfl⟩ : syracuseStep 309955 = 464933) B464933
theorem B1718981 : Blo 147793 1718981 := bstep (se 4 (by rfl) ⟨161154, by rfl⟩ : syracuseStep 1718981 = 322309) B322309
theorem B506573 : Blo 147793 506573 := bstep (se 3 (by rfl) ⟨94982, by rfl⟩ : syracuseStep 506573 = 189965) B189965
theorem B408269 : Blo 147793 408269 := bstep (se 3 (by rfl) ⟨76550, by rfl⟩ : syracuseStep 408269 = 153101) B153101
theorem B342737 : Blo 147793 342737 := bstep (se 2 (by rfl) ⟨128526, by rfl⟩ : syracuseStep 342737 = 257053) B257053
theorem B506627 : Blo 147793 506627 := bstep (se 1 (by rfl) ⟨379970, by rfl⟩ : syracuseStep 506627 = 759941) B759941
theorem B211729 : Blo 147793 211729 := bstep (se 2 (by rfl) ⟨79398, by rfl⟩ : syracuseStep 211729 = 158797) B158797
theorem B375587 : Blo 147793 375587 := bstep (se 1 (by rfl) ⟨281690, by rfl⟩ : syracuseStep 375587 = 563381) B563381
theorem B244577 : Blo 147793 244577 := bstep (se 2 (by rfl) ⟨91716, by rfl⟩ : syracuseStep 244577 = 183433) B183433
theorem B211843 : Blo 147793 211843 := bstep (se 1 (by rfl) ⟨158882, by rfl⟩ : syracuseStep 211843 = 317765) B317765
theorem B375779 : Blo 147793 375779 := bstep (se 1 (by rfl) ⟨281834, by rfl⟩ : syracuseStep 375779 = 563669) B563669
theorem B506897 : Blo 147793 506897 := bstep (se 2 (by rfl) ⟨190086, by rfl⟩ : syracuseStep 506897 = 380173) B380173
theorem B474545 : Blo 147793 474545 := bstep (se 2 (by rfl) ⟨177954, by rfl⟩ : syracuseStep 474545 = 355909) B355909
theorem B507437 : Blo 147793 507437 := bstep (se 3 (by rfl) ⟨95144, by rfl⟩ : syracuseStep 507437 = 190289) B190289
theorem B507491 : Blo 147793 507491 := bstep (se 1 (by rfl) ⟨380618, by rfl⟩ : syracuseStep 507491 = 761237) B761237
theorem B540323 : Blo 147793 540323 := bstep (se 1 (by rfl) ⟨405242, by rfl⟩ : syracuseStep 540323 = 810485) B810485
theorem B507761 : Blo 147793 507761 := bstep (se 2 (by rfl) ⟨190410, by rfl⟩ : syracuseStep 507761 = 380821) B380821
theorem B376721 : Blo 147793 376721 := bstep (se 2 (by rfl) ⟨141270, by rfl⟩ : syracuseStep 376721 = 282541) B282541
theorem B376771 : Blo 147793 376771 := bstep (se 1 (by rfl) ⟨282578, by rfl⟩ : syracuseStep 376771 = 565157) B565157
theorem B475085 : Blo 147793 475085 := bstep (se 3 (by rfl) ⟨89078, by rfl⟩ : syracuseStep 475085 = 178157) B178157
theorem B573389 : Blo 147793 573389 := bstep (se 3 (by rfl) ⟨107510, by rfl⟩ : syracuseStep 573389 = 215021) B215021
theorem B1458161 : Blo 147793 1458161 := bstep (se 2 (by rfl) ⟨546810, by rfl⟩ : syracuseStep 1458161 = 1093621) B1093621
theorem B376913 : Blo 147793 376913 := bstep (se 2 (by rfl) ⟨141342, by rfl⟩ : syracuseStep 376913 = 282685) B282685
theorem B213187 : Blo 147793 213187 := bstep (se 1 (by rfl) ⟨159890, by rfl⟩ : syracuseStep 213187 = 319781) B319781
theorem B672077 : Blo 147793 672077 := bstep (se 3 (by rfl) ⟨126014, by rfl⟩ : syracuseStep 672077 = 252029) B252029
theorem B147795 : Blo 147793 147795 := bstep (se 1 (by rfl) ⟨110846, by rfl⟩ : syracuseStep 147795 = 221693) B221693
theorem B147811 : Blo 147793 147811 := bstep (se 1 (by rfl) ⟨110858, by rfl⟩ : syracuseStep 147811 = 221717) B221717
theorem B147827 : Blo 147793 147827 := bstep (se 1 (by rfl) ⟨110870, by rfl⟩ : syracuseStep 147827 = 221741) B221741
theorem B147843 : Blo 147793 147843 := bstep (se 1 (by rfl) ⟨110882, by rfl⟩ : syracuseStep 147843 = 221765) B221765
theorem B508301 : Blo 147793 508301 := bstep (se 3 (by rfl) ⟨95306, by rfl⟩ : syracuseStep 508301 = 190613) B190613
theorem B147859 : Blo 147793 147859 := bstep (se 1 (by rfl) ⟨110894, by rfl⟩ : syracuseStep 147859 = 221789) B221789
theorem B147875 : Blo 147793 147875 := bstep (se 1 (by rfl) ⟨110906, by rfl⟩ : syracuseStep 147875 = 221813) B221813
theorem B147891 : Blo 147793 147891 := bstep (se 1 (by rfl) ⟨110918, by rfl⟩ : syracuseStep 147891 = 221837) B221837
theorem B147907 : Blo 147793 147907 := bstep (se 1 (by rfl) ⟨110930, by rfl⟩ : syracuseStep 147907 = 221861) B221861
theorem B508355 : Blo 147793 508355 := bstep (se 1 (by rfl) ⟨381266, by rfl⟩ : syracuseStep 508355 = 762533) B762533
theorem B147923 : Blo 147793 147923 := bstep (se 1 (by rfl) ⟨110942, by rfl⟩ : syracuseStep 147923 = 221885) B221885
theorem B147939 : Blo 147793 147939 := bstep (se 1 (by rfl) ⟨110954, by rfl⟩ : syracuseStep 147939 = 221909) B221909
theorem B147955 : Blo 147793 147955 := bstep (se 1 (by rfl) ⟨110966, by rfl⟩ : syracuseStep 147955 = 221933) B221933
theorem B147971 : Blo 147793 147971 := bstep (se 1 (by rfl) ⟨110978, by rfl⟩ : syracuseStep 147971 = 221957) B221957
theorem B147987 : Blo 147793 147987 := bstep (se 1 (by rfl) ⟨110990, by rfl⟩ : syracuseStep 147987 = 221981) B221981
theorem B148003 : Blo 147793 148003 := bstep (se 1 (by rfl) ⟨111002, by rfl⟩ : syracuseStep 148003 = 222005) B222005
theorem B148019 : Blo 147793 148019 := bstep (se 1 (by rfl) ⟨111014, by rfl⟩ : syracuseStep 148019 = 222029) B222029
theorem B148035 : Blo 147793 148035 := bstep (se 1 (by rfl) ⟨111026, by rfl⟩ : syracuseStep 148035 = 222053) B222053
theorem B148051 : Blo 147793 148051 := bstep (se 1 (by rfl) ⟨111038, by rfl⟩ : syracuseStep 148051 = 222077) B222077
theorem B148067 : Blo 147793 148067 := bstep (se 1 (by rfl) ⟨111050, by rfl⟩ : syracuseStep 148067 = 222101) B222101
theorem B148083 : Blo 147793 148083 := bstep (se 1 (by rfl) ⟨111062, by rfl⟩ : syracuseStep 148083 = 222125) B222125
theorem B148099 : Blo 147793 148099 := bstep (se 1 (by rfl) ⟨111074, by rfl⟩ : syracuseStep 148099 = 222149) B222149
theorem B148115 : Blo 147793 148115 := bstep (se 1 (by rfl) ⟨111086, by rfl⟩ : syracuseStep 148115 = 222173) B222173
theorem B148131 : Blo 147793 148131 := bstep (se 1 (by rfl) ⟨111098, by rfl⟩ : syracuseStep 148131 = 222197) B222197
theorem B148147 : Blo 147793 148147 := bstep (se 1 (by rfl) ⟨111110, by rfl⟩ : syracuseStep 148147 = 222221) B222221
theorem B148163 : Blo 147793 148163 := bstep (se 1 (by rfl) ⟨111122, by rfl⟩ : syracuseStep 148163 = 222245) B222245
theorem B508625 : Blo 147793 508625 := bstep (se 2 (by rfl) ⟨190734, by rfl⟩ : syracuseStep 508625 = 381469) B381469
theorem B148179 : Blo 147793 148179 := bstep (se 1 (by rfl) ⟨111134, by rfl⟩ : syracuseStep 148179 = 222269) B222269
theorem B148195 : Blo 147793 148195 := bstep (se 1 (by rfl) ⟨111146, by rfl⟩ : syracuseStep 148195 = 222293) B222293
theorem B148211 : Blo 147793 148211 := bstep (se 1 (by rfl) ⟨111158, by rfl⟩ : syracuseStep 148211 = 222317) B222317
theorem B148227 : Blo 147793 148227 := bstep (se 1 (by rfl) ⟨111170, by rfl⟩ : syracuseStep 148227 = 222341) B222341
theorem B148243 : Blo 147793 148243 := bstep (se 1 (by rfl) ⟨111182, by rfl⟩ : syracuseStep 148243 = 222365) B222365
theorem B148259 : Blo 147793 148259 := bstep (se 1 (by rfl) ⟨111194, by rfl⟩ : syracuseStep 148259 = 222389) B222389
theorem B148275 : Blo 147793 148275 := bstep (se 1 (by rfl) ⟨111206, by rfl⟩ : syracuseStep 148275 = 222413) B222413
theorem B148291 : Blo 147793 148291 := bstep (se 1 (by rfl) ⟨111218, by rfl⟩ : syracuseStep 148291 = 222437) B222437
theorem B148307 : Blo 147793 148307 := bstep (se 1 (by rfl) ⟨111230, by rfl⟩ : syracuseStep 148307 = 222461) B222461
theorem B148323 : Blo 147793 148323 := bstep (se 1 (by rfl) ⟨111242, by rfl⟩ : syracuseStep 148323 = 222485) B222485
theorem B148339 : Blo 147793 148339 := bstep (se 1 (by rfl) ⟨111254, by rfl⟩ : syracuseStep 148339 = 222509) B222509
theorem B148355 : Blo 147793 148355 := bstep (se 1 (by rfl) ⟨111266, by rfl⟩ : syracuseStep 148355 = 222533) B222533
theorem B148371 : Blo 147793 148371 := bstep (se 1 (by rfl) ⟨111278, by rfl⟩ : syracuseStep 148371 = 222557) B222557
theorem B148387 : Blo 147793 148387 := bstep (se 1 (by rfl) ⟨111290, by rfl⟩ : syracuseStep 148387 = 222581) B222581
theorem B508835 : Blo 147793 508835 := bstep (se 1 (by rfl) ⟨381626, by rfl⟩ : syracuseStep 508835 = 763253) B763253
theorem B148403 : Blo 147793 148403 := bstep (se 1 (by rfl) ⟨111302, by rfl⟩ : syracuseStep 148403 = 222605) B222605
theorem B148419 : Blo 147793 148419 := bstep (se 1 (by rfl) ⟨111314, by rfl⟩ : syracuseStep 148419 = 222629) B222629
theorem B148435 : Blo 147793 148435 := bstep (se 1 (by rfl) ⟨111326, by rfl⟩ : syracuseStep 148435 = 222653) B222653
theorem B1426403 : Blo 147793 1426403 := bstep (se 1 (by rfl) ⟨1069802, by rfl⟩ : syracuseStep 1426403 = 2139605) B2139605
theorem B148451 : Blo 147793 148451 := bstep (se 1 (by rfl) ⟨111338, by rfl⟩ : syracuseStep 148451 = 222677) B222677
theorem B639971 : Blo 147793 639971 := bstep (se 1 (by rfl) ⟨479978, by rfl⟩ : syracuseStep 639971 = 959957) B959957
theorem B148467 : Blo 147793 148467 := bstep (se 1 (by rfl) ⟨111350, by rfl⟩ : syracuseStep 148467 = 222701) B222701
theorem B148483 : Blo 147793 148483 := bstep (se 1 (by rfl) ⟨111362, by rfl⟩ : syracuseStep 148483 = 222725) B222725
theorem B508931 : Blo 147793 508931 := bstep (se 1 (by rfl) ⟨381698, by rfl⟩ : syracuseStep 508931 = 763397) B763397
theorem B148499 : Blo 147793 148499 := bstep (se 1 (by rfl) ⟨111374, by rfl⟩ : syracuseStep 148499 = 222749) B222749
theorem B148515 : Blo 147793 148515 := bstep (se 1 (by rfl) ⟨111386, by rfl⟩ : syracuseStep 148515 = 222773) B222773
theorem B377905 : Blo 147793 377905 := bstep (se 2 (by rfl) ⟨141714, by rfl⟩ : syracuseStep 377905 = 283429) B283429
theorem B148531 : Blo 147793 148531 := bstep (se 1 (by rfl) ⟨111398, by rfl⟩ : syracuseStep 148531 = 222797) B222797
theorem B148547 : Blo 147793 148547 := bstep (se 1 (by rfl) ⟨111410, by rfl⟩ : syracuseStep 148547 = 222821) B222821
theorem B148563 : Blo 147793 148563 := bstep (se 1 (by rfl) ⟨111422, by rfl⟩ : syracuseStep 148563 = 222845) B222845
theorem B148579 : Blo 147793 148579 := bstep (se 1 (by rfl) ⟨111434, by rfl⟩ : syracuseStep 148579 = 222869) B222869
theorem B312419 : Blo 147793 312419 := bstep (se 1 (by rfl) ⟨234314, by rfl⟩ : syracuseStep 312419 = 468629) B468629
theorem B148595 : Blo 147793 148595 := bstep (se 1 (by rfl) ⟨111446, by rfl⟩ : syracuseStep 148595 = 222893) B222893
theorem B148611 : Blo 147793 148611 := bstep (se 1 (by rfl) ⟨111458, by rfl⟩ : syracuseStep 148611 = 222917) B222917
theorem B148627 : Blo 147793 148627 := bstep (se 1 (by rfl) ⟨111470, by rfl⟩ : syracuseStep 148627 = 222941) B222941
theorem B148643 : Blo 147793 148643 := bstep (se 1 (by rfl) ⟨111482, by rfl⟩ : syracuseStep 148643 = 222965) B222965
theorem B148659 : Blo 147793 148659 := bstep (se 1 (by rfl) ⟨111494, by rfl⟩ : syracuseStep 148659 = 222989) B222989
theorem B148675 : Blo 147793 148675 := bstep (se 1 (by rfl) ⟨111506, by rfl⟩ : syracuseStep 148675 = 223013) B223013
theorem B1262789 : Blo 147793 1262789 := bstep (se 4 (by rfl) ⟨118386, by rfl⟩ : syracuseStep 1262789 = 236773) B236773
theorem B148691 : Blo 147793 148691 := bstep (se 1 (by rfl) ⟨111518, by rfl⟩ : syracuseStep 148691 = 223037) B223037
theorem B148707 : Blo 147793 148707 := bstep (se 1 (by rfl) ⟨111530, by rfl⟩ : syracuseStep 148707 = 223061) B223061
theorem B509165 : Blo 147793 509165 := bstep (se 3 (by rfl) ⟨95468, by rfl⟩ : syracuseStep 509165 = 190937) B190937
theorem B148723 : Blo 147793 148723 := bstep (se 1 (by rfl) ⟨111542, by rfl⟩ : syracuseStep 148723 = 223085) B223085
theorem B148739 : Blo 147793 148739 := bstep (se 1 (by rfl) ⟨111554, by rfl⟩ : syracuseStep 148739 = 223109) B223109
theorem B148755 : Blo 147793 148755 := bstep (se 1 (by rfl) ⟨111566, by rfl⟩ : syracuseStep 148755 = 223133) B223133
theorem B148771 : Blo 147793 148771 := bstep (se 1 (by rfl) ⟨111578, by rfl⟩ : syracuseStep 148771 = 223157) B223157
theorem B509219 : Blo 147793 509219 := bstep (se 1 (by rfl) ⟨381914, by rfl⟩ : syracuseStep 509219 = 763829) B763829
theorem B214321 : Blo 147793 214321 := bstep (se 2 (by rfl) ⟨80370, by rfl⟩ : syracuseStep 214321 = 160741) B160741
theorem B148787 : Blo 147793 148787 := bstep (se 1 (by rfl) ⟨111590, by rfl⟩ : syracuseStep 148787 = 223181) B223181
theorem B148803 : Blo 147793 148803 := bstep (se 1 (by rfl) ⟨111602, by rfl⟩ : syracuseStep 148803 = 223205) B223205
theorem B378179 : Blo 147793 378179 := bstep (se 1 (by rfl) ⟨283634, by rfl⟩ : syracuseStep 378179 = 567269) B567269
theorem B148819 : Blo 147793 148819 := bstep (se 1 (by rfl) ⟨111614, by rfl⟩ : syracuseStep 148819 = 223229) B223229
theorem B148835 : Blo 147793 148835 := bstep (se 1 (by rfl) ⟨111626, by rfl⟩ : syracuseStep 148835 = 223253) B223253
theorem B148851 : Blo 147793 148851 := bstep (se 1 (by rfl) ⟨111638, by rfl⟩ : syracuseStep 148851 = 223277) B223277
theorem B148867 : Blo 147793 148867 := bstep (se 1 (by rfl) ⟨111650, by rfl⟩ : syracuseStep 148867 = 223301) B223301
theorem B214417 : Blo 147793 214417 := bstep (se 2 (by rfl) ⟨80406, by rfl⟩ : syracuseStep 214417 = 160813) B160813
theorem B148883 : Blo 147793 148883 := bstep (se 1 (by rfl) ⟨111662, by rfl⟩ : syracuseStep 148883 = 223325) B223325
theorem B148899 : Blo 147793 148899 := bstep (se 1 (by rfl) ⟨111674, by rfl⟩ : syracuseStep 148899 = 223349) B223349
theorem B148915 : Blo 147793 148915 := bstep (se 1 (by rfl) ⟨111686, by rfl⟩ : syracuseStep 148915 = 223373) B223373
theorem B148931 : Blo 147793 148931 := bstep (se 1 (by rfl) ⟨111698, by rfl⟩ : syracuseStep 148931 = 223397) B223397
theorem B148947 : Blo 147793 148947 := bstep (se 1 (by rfl) ⟨111710, by rfl⟩ : syracuseStep 148947 = 223421) B223421
theorem B148963 : Blo 147793 148963 := bstep (se 1 (by rfl) ⟨111722, by rfl⟩ : syracuseStep 148963 = 223445) B223445
theorem B148979 : Blo 147793 148979 := bstep (se 1 (by rfl) ⟨111734, by rfl⟩ : syracuseStep 148979 = 223469) B223469
theorem B148995 : Blo 147793 148995 := bstep (se 1 (by rfl) ⟨111746, by rfl⟩ : syracuseStep 148995 = 223493) B223493
theorem B378371 : Blo 147793 378371 := bstep (se 1 (by rfl) ⟨283778, by rfl⟩ : syracuseStep 378371 = 567557) B567557
theorem B149011 : Blo 147793 149011 := bstep (se 1 (by rfl) ⟨111758, by rfl⟩ : syracuseStep 149011 = 223517) B223517
theorem B149027 : Blo 147793 149027 := bstep (se 1 (by rfl) ⟨111770, by rfl⟩ : syracuseStep 149027 = 223541) B223541
theorem B509489 : Blo 147793 509489 := bstep (se 2 (by rfl) ⟨191058, by rfl⟩ : syracuseStep 509489 = 382117) B382117
theorem B149043 : Blo 147793 149043 := bstep (se 1 (by rfl) ⟨111782, by rfl⟩ : syracuseStep 149043 = 223565) B223565
theorem B149059 : Blo 147793 149059 := bstep (se 1 (by rfl) ⟨111794, by rfl⟩ : syracuseStep 149059 = 223589) B223589
theorem B149075 : Blo 147793 149075 := bstep (se 1 (by rfl) ⟨111806, by rfl⟩ : syracuseStep 149075 = 223613) B223613
theorem B149091 : Blo 147793 149091 := bstep (se 1 (by rfl) ⟨111818, by rfl⟩ : syracuseStep 149091 = 223637) B223637
theorem B149107 : Blo 147793 149107 := bstep (se 1 (by rfl) ⟨111830, by rfl⟩ : syracuseStep 149107 = 223661) B223661
theorem B149123 : Blo 147793 149123 := bstep (se 1 (by rfl) ⟨111842, by rfl⟩ : syracuseStep 149123 = 223685) B223685
theorem B149139 : Blo 147793 149139 := bstep (se 1 (by rfl) ⟨111854, by rfl⟩ : syracuseStep 149139 = 223709) B223709
theorem B149155 : Blo 147793 149155 := bstep (se 1 (by rfl) ⟨111866, by rfl⟩ : syracuseStep 149155 = 223733) B223733
theorem B149171 : Blo 147793 149171 := bstep (se 1 (by rfl) ⟨111878, by rfl⟩ : syracuseStep 149171 = 223757) B223757
theorem B149187 : Blo 147793 149187 := bstep (se 1 (by rfl) ⟨111890, by rfl⟩ : syracuseStep 149187 = 223781) B223781
theorem B149203 : Blo 147793 149203 := bstep (se 1 (by rfl) ⟨111902, by rfl⟩ : syracuseStep 149203 = 223805) B223805
theorem B149219 : Blo 147793 149219 := bstep (se 1 (by rfl) ⟨111914, by rfl⟩ : syracuseStep 149219 = 223829) B223829
theorem B149235 : Blo 147793 149235 := bstep (se 1 (by rfl) ⟨111926, by rfl⟩ : syracuseStep 149235 = 223853) B223853
theorem B149251 : Blo 147793 149251 := bstep (se 1 (by rfl) ⟨111938, by rfl⟩ : syracuseStep 149251 = 223877) B223877
theorem B149267 : Blo 147793 149267 := bstep (se 1 (by rfl) ⟨111950, by rfl⟩ : syracuseStep 149267 = 223901) B223901
theorem B968483 : Blo 147793 968483 := bstep (se 1 (by rfl) ⟨726362, by rfl⟩ : syracuseStep 968483 = 1452725) B1452725
theorem B149283 : Blo 147793 149283 := bstep (se 1 (by rfl) ⟨111962, by rfl⟩ : syracuseStep 149283 = 223925) B223925
theorem B149299 : Blo 147793 149299 := bstep (se 1 (by rfl) ⟨111974, by rfl⟩ : syracuseStep 149299 = 223949) B223949
theorem B149315 : Blo 147793 149315 := bstep (se 1 (by rfl) ⟨111986, by rfl⟩ : syracuseStep 149315 = 223973) B223973
theorem B149331 : Blo 147793 149331 := bstep (se 1 (by rfl) ⟨111998, by rfl⟩ : syracuseStep 149331 = 223997) B223997
theorem B149347 : Blo 147793 149347 := bstep (se 1 (by rfl) ⟨112010, by rfl⟩ : syracuseStep 149347 = 224021) B224021
theorem B149363 : Blo 147793 149363 := bstep (se 1 (by rfl) ⟨112022, by rfl⟩ : syracuseStep 149363 = 224045) B224045
theorem B214913 : Blo 147793 214913 := bstep (se 2 (by rfl) ⟨80592, by rfl⟩ : syracuseStep 214913 = 161185) B161185
theorem B149379 : Blo 147793 149379 := bstep (se 1 (by rfl) ⟨112034, by rfl⟩ : syracuseStep 149379 = 224069) B224069
theorem B149395 : Blo 147793 149395 := bstep (se 1 (by rfl) ⟨112046, by rfl⟩ : syracuseStep 149395 = 224093) B224093
theorem B149411 : Blo 147793 149411 := bstep (se 1 (by rfl) ⟨112058, by rfl⟩ : syracuseStep 149411 = 224117) B224117
theorem B182179 : Blo 147793 182179 := bstep (se 1 (by rfl) ⟨136634, by rfl⟩ : syracuseStep 182179 = 273269) B273269
theorem B149427 : Blo 147793 149427 := bstep (se 1 (by rfl) ⟨112070, by rfl⟩ : syracuseStep 149427 = 224141) B224141
theorem B149443 : Blo 147793 149443 := bstep (se 1 (by rfl) ⟨112082, by rfl⟩ : syracuseStep 149443 = 224165) B224165
theorem B149459 : Blo 147793 149459 := bstep (se 1 (by rfl) ⟨112094, by rfl⟩ : syracuseStep 149459 = 224189) B224189
theorem B149475 : Blo 147793 149475 := bstep (se 1 (by rfl) ⟨112106, by rfl⟩ : syracuseStep 149475 = 224213) B224213
theorem B149491 : Blo 147793 149491 := bstep (se 1 (by rfl) ⟨112118, by rfl⟩ : syracuseStep 149491 = 224237) B224237
theorem B149507 : Blo 147793 149507 := bstep (se 1 (by rfl) ⟨112130, by rfl⟩ : syracuseStep 149507 = 224261) B224261
theorem B149523 : Blo 147793 149523 := bstep (se 1 (by rfl) ⟨112142, by rfl⟩ : syracuseStep 149523 = 224285) B224285
theorem B149539 : Blo 147793 149539 := bstep (se 1 (by rfl) ⟨112154, by rfl⟩ : syracuseStep 149539 = 224309) B224309
theorem B149555 : Blo 147793 149555 := bstep (se 1 (by rfl) ⟨112166, by rfl⟩ : syracuseStep 149555 = 224333) B224333
theorem B149571 : Blo 147793 149571 := bstep (se 1 (by rfl) ⟨112178, by rfl⟩ : syracuseStep 149571 = 224357) B224357
theorem B968773 : Blo 147793 968773 := bstep (se 4 (by rfl) ⟨90822, by rfl⟩ : syracuseStep 968773 = 181645) B181645
theorem B510029 : Blo 147793 510029 := bstep (se 3 (by rfl) ⟨95630, by rfl⟩ : syracuseStep 510029 = 191261) B191261
theorem B149587 : Blo 147793 149587 := bstep (se 1 (by rfl) ⟨112190, by rfl⟩ : syracuseStep 149587 = 224381) B224381
theorem B149603 : Blo 147793 149603 := bstep (se 1 (by rfl) ⟨112202, by rfl⟩ : syracuseStep 149603 = 224405) B224405
theorem B149619 : Blo 147793 149619 := bstep (se 1 (by rfl) ⟨112214, by rfl⟩ : syracuseStep 149619 = 224429) B224429
theorem B149635 : Blo 147793 149635 := bstep (se 1 (by rfl) ⟨112226, by rfl⟩ : syracuseStep 149635 = 224453) B224453
theorem B510083 : Blo 147793 510083 := bstep (se 1 (by rfl) ⟨382562, by rfl⟩ : syracuseStep 510083 = 765125) B765125
theorem B215185 : Blo 147793 215185 := bstep (se 2 (by rfl) ⟨80694, by rfl⟩ : syracuseStep 215185 = 161389) B161389
theorem B149651 : Blo 147793 149651 := bstep (se 1 (by rfl) ⟨112238, by rfl⟩ : syracuseStep 149651 = 224477) B224477
theorem B149667 : Blo 147793 149667 := bstep (se 1 (by rfl) ⟨112250, by rfl⟩ : syracuseStep 149667 = 224501) B224501
theorem B149683 : Blo 147793 149683 := bstep (se 1 (by rfl) ⟨112262, by rfl⟩ : syracuseStep 149683 = 224525) B224525
theorem B149699 : Blo 147793 149699 := bstep (se 1 (by rfl) ⟨112274, by rfl⟩ : syracuseStep 149699 = 224549) B224549
theorem B149715 : Blo 147793 149715 := bstep (se 1 (by rfl) ⟨112286, by rfl⟩ : syracuseStep 149715 = 224573) B224573
theorem B149731 : Blo 147793 149731 := bstep (se 1 (by rfl) ⟨112298, by rfl⟩ : syracuseStep 149731 = 224597) B224597
theorem B280817 : Blo 147793 280817 := bstep (se 2 (by rfl) ⟨105306, by rfl⟩ : syracuseStep 280817 = 210613) B210613
theorem B149747 : Blo 147793 149747 := bstep (se 1 (by rfl) ⟨112310, by rfl⟩ : syracuseStep 149747 = 224621) B224621
theorem B149763 : Blo 147793 149763 := bstep (se 1 (by rfl) ⟨112322, by rfl⟩ : syracuseStep 149763 = 224645) B224645
theorem B149779 : Blo 147793 149779 := bstep (se 1 (by rfl) ⟨112334, by rfl⟩ : syracuseStep 149779 = 224669) B224669
theorem B149795 : Blo 147793 149795 := bstep (se 1 (by rfl) ⟨112346, by rfl⟩ : syracuseStep 149795 = 224693) B224693
theorem B149811 : Blo 147793 149811 := bstep (se 1 (by rfl) ⟨112358, by rfl⟩ : syracuseStep 149811 = 224717) B224717
theorem B149827 : Blo 147793 149827 := bstep (se 1 (by rfl) ⟨112370, by rfl⟩ : syracuseStep 149827 = 224741) B224741
theorem B149843 : Blo 147793 149843 := bstep (se 1 (by rfl) ⟨112382, by rfl⟩ : syracuseStep 149843 = 224765) B224765
theorem B149859 : Blo 147793 149859 := bstep (se 1 (by rfl) ⟨112394, by rfl⟩ : syracuseStep 149859 = 224789) B224789
theorem B149875 : Blo 147793 149875 := bstep (se 1 (by rfl) ⟨112406, by rfl⟩ : syracuseStep 149875 = 224813) B224813
theorem B149891 : Blo 147793 149891 := bstep (se 1 (by rfl) ⟨112418, by rfl⟩ : syracuseStep 149891 = 224837) B224837
theorem B510353 : Blo 147793 510353 := bstep (se 2 (by rfl) ⟨191382, by rfl⟩ : syracuseStep 510353 = 382765) B382765
theorem B149907 : Blo 147793 149907 := bstep (se 1 (by rfl) ⟨112430, by rfl⟩ : syracuseStep 149907 = 224861) B224861
theorem B149923 : Blo 147793 149923 := bstep (se 1 (by rfl) ⟨112442, by rfl⟩ : syracuseStep 149923 = 224885) B224885
theorem B379313 : Blo 147793 379313 := bstep (se 2 (by rfl) ⟨142242, by rfl⟩ : syracuseStep 379313 = 284485) B284485
theorem B149939 : Blo 147793 149939 := bstep (se 1 (by rfl) ⟨112454, by rfl⟩ : syracuseStep 149939 = 224909) B224909
theorem B149955 : Blo 147793 149955 := bstep (se 1 (by rfl) ⟨112466, by rfl⟩ : syracuseStep 149955 = 224933) B224933
theorem B149971 : Blo 147793 149971 := bstep (se 1 (by rfl) ⟨112478, by rfl⟩ : syracuseStep 149971 = 224957) B224957
theorem B379363 : Blo 147793 379363 := bstep (se 1 (by rfl) ⟨284522, by rfl⟩ : syracuseStep 379363 = 569045) B569045
theorem B149987 : Blo 147793 149987 := bstep (se 1 (by rfl) ⟨112490, by rfl⟩ : syracuseStep 149987 = 224981) B224981
theorem B150003 : Blo 147793 150003 := bstep (se 1 (by rfl) ⟨112502, by rfl⟩ : syracuseStep 150003 = 225005) B225005
theorem B150019 : Blo 147793 150019 := bstep (se 1 (by rfl) ⟨112514, by rfl⟩ : syracuseStep 150019 = 225029) B225029
theorem B150035 : Blo 147793 150035 := bstep (se 1 (by rfl) ⟨112526, by rfl⟩ : syracuseStep 150035 = 225053) B225053
theorem B150051 : Blo 147793 150051 := bstep (se 1 (by rfl) ⟨112538, by rfl⟩ : syracuseStep 150051 = 225077) B225077
theorem B150067 : Blo 147793 150067 := bstep (se 1 (by rfl) ⟨112550, by rfl⟩ : syracuseStep 150067 = 225101) B225101
theorem B150083 : Blo 147793 150083 := bstep (se 1 (by rfl) ⟨112562, by rfl⟩ : syracuseStep 150083 = 225125) B225125
theorem B150099 : Blo 147793 150099 := bstep (se 1 (by rfl) ⟨112574, by rfl⟩ : syracuseStep 150099 = 225149) B225149
theorem B150115 : Blo 147793 150115 := bstep (se 1 (by rfl) ⟨112586, by rfl⟩ : syracuseStep 150115 = 225173) B225173
theorem B379505 : Blo 147793 379505 := bstep (se 2 (by rfl) ⟨142314, by rfl⟩ : syracuseStep 379505 = 284629) B284629
theorem B150131 : Blo 147793 150131 := bstep (se 1 (by rfl) ⟨112598, by rfl⟩ : syracuseStep 150131 = 225197) B225197
theorem B150147 : Blo 147793 150147 := bstep (se 1 (by rfl) ⟨112610, by rfl⟩ : syracuseStep 150147 = 225221) B225221
theorem B150163 : Blo 147793 150163 := bstep (se 1 (by rfl) ⟨112622, by rfl⟩ : syracuseStep 150163 = 225245) B225245
theorem B150179 : Blo 147793 150179 := bstep (se 1 (by rfl) ⟨112634, by rfl⟩ : syracuseStep 150179 = 225269) B225269
theorem B150195 : Blo 147793 150195 := bstep (se 1 (by rfl) ⟨112646, by rfl⟩ : syracuseStep 150195 = 225293) B225293
theorem B150211 : Blo 147793 150211 := bstep (se 1 (by rfl) ⟨112658, by rfl⟩ : syracuseStep 150211 = 225317) B225317
theorem B150227 : Blo 147793 150227 := bstep (se 1 (by rfl) ⟨112670, by rfl⟩ : syracuseStep 150227 = 225341) B225341
theorem B150243 : Blo 147793 150243 := bstep (se 1 (by rfl) ⟨112682, by rfl⟩ : syracuseStep 150243 = 225365) B225365
theorem B215779 : Blo 147793 215779 := bstep (se 1 (by rfl) ⟨161834, by rfl⟩ : syracuseStep 215779 = 323669) B323669
theorem B150259 : Blo 147793 150259 := bstep (se 1 (by rfl) ⟨112694, by rfl⟩ : syracuseStep 150259 = 225389) B225389
theorem B150275 : Blo 147793 150275 := bstep (se 1 (by rfl) ⟨112706, by rfl⟩ : syracuseStep 150275 = 225413) B225413
theorem B150291 : Blo 147793 150291 := bstep (se 1 (by rfl) ⟨112718, by rfl⟩ : syracuseStep 150291 = 225437) B225437
theorem B150307 : Blo 147793 150307 := bstep (se 1 (by rfl) ⟨112730, by rfl⟩ : syracuseStep 150307 = 225461) B225461
theorem B576305 : Blo 147793 576305 := bstep (se 2 (by rfl) ⟨216114, by rfl⟩ : syracuseStep 576305 = 432229) B432229
theorem B150323 : Blo 147793 150323 := bstep (se 1 (by rfl) ⟨112742, by rfl⟩ : syracuseStep 150323 = 225485) B225485
theorem B150339 : Blo 147793 150339 := bstep (se 1 (by rfl) ⟨112754, by rfl⟩ : syracuseStep 150339 = 225509) B225509
theorem B215875 : Blo 147793 215875 := bstep (se 1 (by rfl) ⟨161906, by rfl⟩ : syracuseStep 215875 = 323813) B323813
theorem B150355 : Blo 147793 150355 := bstep (se 1 (by rfl) ⟨112766, by rfl⟩ : syracuseStep 150355 = 225533) B225533
theorem B150371 : Blo 147793 150371 := bstep (se 1 (by rfl) ⟨112778, by rfl⟩ : syracuseStep 150371 = 225557) B225557
theorem B150387 : Blo 147793 150387 := bstep (se 1 (by rfl) ⟨112790, by rfl⟩ : syracuseStep 150387 = 225581) B225581
theorem B150403 : Blo 147793 150403 := bstep (se 1 (by rfl) ⟨112802, by rfl⟩ : syracuseStep 150403 = 225605) B225605
theorem B871309 : Blo 147793 871309 := bstep (se 3 (by rfl) ⟨163370, by rfl⟩ : syracuseStep 871309 = 326741) B326741
theorem B150419 : Blo 147793 150419 := bstep (se 1 (by rfl) ⟨112814, by rfl⟩ : syracuseStep 150419 = 225629) B225629
theorem B150435 : Blo 147793 150435 := bstep (se 1 (by rfl) ⟨112826, by rfl⟩ : syracuseStep 150435 = 225653) B225653
theorem B510893 : Blo 147793 510893 := bstep (se 3 (by rfl) ⟨95792, by rfl⟩ : syracuseStep 510893 = 191585) B191585
theorem B150451 : Blo 147793 150451 := bstep (se 1 (by rfl) ⟨112838, by rfl⟩ : syracuseStep 150451 = 225677) B225677
theorem B150467 : Blo 147793 150467 := bstep (se 1 (by rfl) ⟨112850, by rfl⟩ : syracuseStep 150467 = 225701) B225701
theorem B150483 : Blo 147793 150483 := bstep (se 1 (by rfl) ⟨112862, by rfl⟩ : syracuseStep 150483 = 225725) B225725
theorem B150499 : Blo 147793 150499 := bstep (se 1 (by rfl) ⟨112874, by rfl⟩ : syracuseStep 150499 = 225749) B225749
theorem B510947 : Blo 147793 510947 := bstep (se 1 (by rfl) ⟨383210, by rfl⟩ : syracuseStep 510947 = 766421) B766421
theorem B150515 : Blo 147793 150515 := bstep (se 1 (by rfl) ⟨112886, by rfl⟩ : syracuseStep 150515 = 225773) B225773
theorem B150531 : Blo 147793 150531 := bstep (se 1 (by rfl) ⟨112898, by rfl⟩ : syracuseStep 150531 = 225797) B225797
theorem B150547 : Blo 147793 150547 := bstep (se 1 (by rfl) ⟨112910, by rfl⟩ : syracuseStep 150547 = 225821) B225821
theorem B150563 : Blo 147793 150563 := bstep (se 1 (by rfl) ⟨112922, by rfl⟩ : syracuseStep 150563 = 225845) B225845
theorem B150579 : Blo 147793 150579 := bstep (se 1 (by rfl) ⟨112934, by rfl⟩ : syracuseStep 150579 = 225869) B225869
theorem B150595 : Blo 147793 150595 := bstep (se 1 (by rfl) ⟨112946, by rfl⟩ : syracuseStep 150595 = 225893) B225893
theorem B150611 : Blo 147793 150611 := bstep (se 1 (by rfl) ⟨112958, by rfl⟩ : syracuseStep 150611 = 225917) B225917
theorem B150627 : Blo 147793 150627 := bstep (se 1 (by rfl) ⟨112970, by rfl⟩ : syracuseStep 150627 = 225941) B225941
theorem B281713 : Blo 147793 281713 := bstep (se 2 (by rfl) ⟨105642, by rfl⟩ : syracuseStep 281713 = 211285) B211285
theorem B150643 : Blo 147793 150643 := bstep (se 1 (by rfl) ⟨112982, by rfl⟩ : syracuseStep 150643 = 225965) B225965
theorem B150659 : Blo 147793 150659 := bstep (se 1 (by rfl) ⟨112994, by rfl⟩ : syracuseStep 150659 = 225989) B225989
theorem B150675 : Blo 147793 150675 := bstep (se 1 (by rfl) ⟨113006, by rfl⟩ : syracuseStep 150675 = 226013) B226013
theorem B150691 : Blo 147793 150691 := bstep (se 1 (by rfl) ⟨113018, by rfl⟩ : syracuseStep 150691 = 226037) B226037
theorem B150707 : Blo 147793 150707 := bstep (se 1 (by rfl) ⟨113030, by rfl⟩ : syracuseStep 150707 = 226061) B226061
theorem B150723 : Blo 147793 150723 := bstep (se 1 (by rfl) ⟨113042, by rfl⟩ : syracuseStep 150723 = 226085) B226085
theorem B412877 : Blo 147793 412877 := bstep (se 3 (by rfl) ⟨77414, by rfl⟩ : syracuseStep 412877 = 154829) B154829
theorem B150739 : Blo 147793 150739 := bstep (se 1 (by rfl) ⟨113054, by rfl⟩ : syracuseStep 150739 = 226109) B226109
theorem B150755 : Blo 147793 150755 := bstep (se 1 (by rfl) ⟨113066, by rfl⟩ : syracuseStep 150755 = 226133) B226133
theorem B511217 : Blo 147793 511217 := bstep (se 2 (by rfl) ⟨191706, by rfl⟩ : syracuseStep 511217 = 383413) B383413
theorem B150771 : Blo 147793 150771 := bstep (se 1 (by rfl) ⟨113078, by rfl⟩ : syracuseStep 150771 = 226157) B226157
theorem B150787 : Blo 147793 150787 := bstep (se 1 (by rfl) ⟨113090, by rfl⟩ : syracuseStep 150787 = 226181) B226181
theorem B544013 : Blo 147793 544013 := bstep (se 3 (by rfl) ⟨102002, by rfl⟩ : syracuseStep 544013 = 204005) B204005
theorem B1133837 : Blo 147793 1133837 := bstep (se 3 (by rfl) ⟨212594, by rfl⟩ : syracuseStep 1133837 = 425189) B425189
theorem B281873 : Blo 147793 281873 := bstep (se 2 (by rfl) ⟨105702, by rfl⟩ : syracuseStep 281873 = 211405) B211405
theorem B150803 : Blo 147793 150803 := bstep (se 1 (by rfl) ⟨113102, by rfl⟩ : syracuseStep 150803 = 226205) B226205
theorem B150819 : Blo 147793 150819 := bstep (se 1 (by rfl) ⟨113114, by rfl⟩ : syracuseStep 150819 = 226229) B226229
theorem B150835 : Blo 147793 150835 := bstep (se 1 (by rfl) ⟨113126, by rfl⟩ : syracuseStep 150835 = 226253) B226253
theorem B150851 : Blo 147793 150851 := bstep (se 1 (by rfl) ⟨113138, by rfl⟩ : syracuseStep 150851 = 226277) B226277
theorem B150867 : Blo 147793 150867 := bstep (se 1 (by rfl) ⟨113150, by rfl⟩ : syracuseStep 150867 = 226301) B226301
theorem B150883 : Blo 147793 150883 := bstep (se 1 (by rfl) ⟨113162, by rfl⟩ : syracuseStep 150883 = 226325) B226325
theorem B150899 : Blo 147793 150899 := bstep (se 1 (by rfl) ⟨113174, by rfl⟩ : syracuseStep 150899 = 226349) B226349
theorem B150915 : Blo 147793 150915 := bstep (se 1 (by rfl) ⟨113186, by rfl⟩ : syracuseStep 150915 = 226373) B226373
theorem B150931 : Blo 147793 150931 := bstep (se 1 (by rfl) ⟨113198, by rfl⟩ : syracuseStep 150931 = 226397) B226397
theorem B150947 : Blo 147793 150947 := bstep (se 1 (by rfl) ⟨113210, by rfl⟩ : syracuseStep 150947 = 226421) B226421
theorem B609713 : Blo 147793 609713 := bstep (se 2 (by rfl) ⟨228642, by rfl⟩ : syracuseStep 609713 = 457285) B457285
theorem B150963 : Blo 147793 150963 := bstep (se 1 (by rfl) ⟨113222, by rfl⟩ : syracuseStep 150963 = 226445) B226445
theorem B150979 : Blo 147793 150979 := bstep (se 1 (by rfl) ⟨113234, by rfl⟩ : syracuseStep 150979 = 226469) B226469
theorem B478673 : Blo 147793 478673 := bstep (se 2 (by rfl) ⟨179502, by rfl⟩ : syracuseStep 478673 = 359005) B359005
theorem B150995 : Blo 147793 150995 := bstep (se 1 (by rfl) ⟨113246, by rfl⟩ : syracuseStep 150995 = 226493) B226493
theorem B151011 : Blo 147793 151011 := bstep (se 1 (by rfl) ⟨113258, by rfl⟩ : syracuseStep 151011 = 226517) B226517
theorem B151027 : Blo 147793 151027 := bstep (se 1 (by rfl) ⟨113270, by rfl⟩ : syracuseStep 151027 = 226541) B226541
theorem B151043 : Blo 147793 151043 := bstep (se 1 (by rfl) ⟨113282, by rfl⟩ : syracuseStep 151043 = 226565) B226565
theorem B151059 : Blo 147793 151059 := bstep (se 1 (by rfl) ⟨113294, by rfl⟩ : syracuseStep 151059 = 226589) B226589
theorem B151075 : Blo 147793 151075 := bstep (se 1 (by rfl) ⟨113306, by rfl⟩ : syracuseStep 151075 = 226613) B226613
theorem B151091 : Blo 147793 151091 := bstep (se 1 (by rfl) ⟨113318, by rfl⟩ : syracuseStep 151091 = 226637) B226637
theorem B151107 : Blo 147793 151107 := bstep (se 1 (by rfl) ⟨113330, by rfl⟩ : syracuseStep 151107 = 226661) B226661
theorem B380497 : Blo 147793 380497 := bstep (se 2 (by rfl) ⟨142686, by rfl⟩ : syracuseStep 380497 = 285373) B285373
theorem B151123 : Blo 147793 151123 := bstep (se 1 (by rfl) ⟨113342, by rfl⟩ : syracuseStep 151123 = 226685) B226685
theorem B151139 : Blo 147793 151139 := bstep (se 1 (by rfl) ⟨113354, by rfl⟩ : syracuseStep 151139 = 226709) B226709
theorem B151155 : Blo 147793 151155 := bstep (se 1 (by rfl) ⟨113366, by rfl⟩ : syracuseStep 151155 = 226733) B226733
theorem B249473 : Blo 147793 249473 := bstep (se 2 (by rfl) ⟨93552, by rfl⟩ : syracuseStep 249473 = 187105) B187105
theorem B151171 : Blo 147793 151171 := bstep (se 1 (by rfl) ⟨113378, by rfl⟩ : syracuseStep 151171 = 226757) B226757
theorem B151187 : Blo 147793 151187 := bstep (se 1 (by rfl) ⟨113390, by rfl⟩ : syracuseStep 151187 = 226781) B226781
theorem B282275 : Blo 147793 282275 := bstep (se 1 (by rfl) ⟨211706, by rfl⟩ : syracuseStep 282275 = 423413) B423413
theorem B151203 : Blo 147793 151203 := bstep (se 1 (by rfl) ⟨113402, by rfl⟩ : syracuseStep 151203 = 226805) B226805
theorem B151219 : Blo 147793 151219 := bstep (se 1 (by rfl) ⟨113414, by rfl⟩ : syracuseStep 151219 = 226829) B226829
theorem B151235 : Blo 147793 151235 := bstep (se 1 (by rfl) ⟨113426, by rfl⟩ : syracuseStep 151235 = 226853) B226853
theorem B151251 : Blo 147793 151251 := bstep (se 1 (by rfl) ⟨113438, by rfl⟩ : syracuseStep 151251 = 226877) B226877
theorem B151267 : Blo 147793 151267 := bstep (se 1 (by rfl) ⟨113450, by rfl⟩ : syracuseStep 151267 = 226901) B226901
theorem B151283 : Blo 147793 151283 := bstep (se 1 (by rfl) ⟨113462, by rfl⟩ : syracuseStep 151283 = 226925) B226925
theorem B249601 : Blo 147793 249601 := bstep (se 2 (by rfl) ⟨93600, by rfl⟩ : syracuseStep 249601 = 187201) B187201
theorem B151299 : Blo 147793 151299 := bstep (se 1 (by rfl) ⟨113474, by rfl⟩ : syracuseStep 151299 = 226949) B226949
theorem B511757 : Blo 147793 511757 := bstep (se 3 (by rfl) ⟨95954, by rfl⟩ : syracuseStep 511757 = 191909) B191909
theorem B151315 : Blo 147793 151315 := bstep (se 1 (by rfl) ⟨113486, by rfl⟩ : syracuseStep 151315 = 226973) B226973
theorem B249635 : Blo 147793 249635 := bstep (se 1 (by rfl) ⟨187226, by rfl⟩ : syracuseStep 249635 = 374453) B374453
theorem B151331 : Blo 147793 151331 := bstep (se 1 (by rfl) ⟨113498, by rfl⟩ : syracuseStep 151331 = 226997) B226997
theorem B151347 : Blo 147793 151347 := bstep (se 1 (by rfl) ⟨113510, by rfl⟩ : syracuseStep 151347 = 227021) B227021
theorem B151363 : Blo 147793 151363 := bstep (se 1 (by rfl) ⟨113522, by rfl⟩ : syracuseStep 151363 = 227045) B227045
theorem B511811 : Blo 147793 511811 := bstep (se 1 (by rfl) ⟨383858, by rfl⟩ : syracuseStep 511811 = 767717) B767717
theorem B151379 : Blo 147793 151379 := bstep (se 1 (by rfl) ⟨113534, by rfl⟩ : syracuseStep 151379 = 227069) B227069
theorem B380771 : Blo 147793 380771 := bstep (se 1 (by rfl) ⟨285578, by rfl⟩ : syracuseStep 380771 = 571157) B571157
theorem B184163 : Blo 147793 184163 := bstep (se 1 (by rfl) ⟨138122, by rfl⟩ : syracuseStep 184163 = 276245) B276245
theorem B151395 : Blo 147793 151395 := bstep (se 1 (by rfl) ⟨113546, by rfl⟩ : syracuseStep 151395 = 227093) B227093
theorem B151411 : Blo 147793 151411 := bstep (se 1 (by rfl) ⟨113558, by rfl⟩ : syracuseStep 151411 = 227117) B227117
theorem B151427 : Blo 147793 151427 := bstep (se 1 (by rfl) ⟨113570, by rfl⟩ : syracuseStep 151427 = 227141) B227141
theorem B151443 : Blo 147793 151443 := bstep (se 1 (by rfl) ⟨113582, by rfl⟩ : syracuseStep 151443 = 227165) B227165
theorem B249763 : Blo 147793 249763 := bstep (se 1 (by rfl) ⟨187322, by rfl⟩ : syracuseStep 249763 = 374645) B374645
theorem B151459 : Blo 147793 151459 := bstep (se 1 (by rfl) ⟨113594, by rfl⟩ : syracuseStep 151459 = 227189) B227189
theorem B151475 : Blo 147793 151475 := bstep (se 1 (by rfl) ⟨113606, by rfl⟩ : syracuseStep 151475 = 227213) B227213
theorem B151491 : Blo 147793 151491 := bstep (se 1 (by rfl) ⟨113618, by rfl⟩ : syracuseStep 151491 = 227237) B227237
theorem B151507 : Blo 147793 151507 := bstep (se 1 (by rfl) ⟨113630, by rfl⟩ : syracuseStep 151507 = 227261) B227261
theorem B151523 : Blo 147793 151523 := bstep (se 1 (by rfl) ⟨113642, by rfl⟩ : syracuseStep 151523 = 227285) B227285
theorem B151539 : Blo 147793 151539 := bstep (se 1 (by rfl) ⟨113654, by rfl⟩ : syracuseStep 151539 = 227309) B227309
theorem B151555 : Blo 147793 151555 := bstep (se 1 (by rfl) ⟨113666, by rfl⟩ : syracuseStep 151555 = 227333) B227333
theorem B151571 : Blo 147793 151571 := bstep (se 1 (by rfl) ⟨113678, by rfl⟩ : syracuseStep 151571 = 227357) B227357
theorem B380963 : Blo 147793 380963 := bstep (se 1 (by rfl) ⟨285722, by rfl⟩ : syracuseStep 380963 = 571445) B571445
theorem B151587 : Blo 147793 151587 := bstep (se 1 (by rfl) ⟨113690, by rfl⟩ : syracuseStep 151587 = 227381) B227381
theorem B249905 : Blo 147793 249905 := bstep (se 2 (by rfl) ⟨93714, by rfl⟩ : syracuseStep 249905 = 187429) B187429
theorem B151603 : Blo 147793 151603 := bstep (se 1 (by rfl) ⟨113702, by rfl⟩ : syracuseStep 151603 = 227405) B227405
theorem B151619 : Blo 147793 151619 := bstep (se 1 (by rfl) ⟨113714, by rfl⟩ : syracuseStep 151619 = 227429) B227429
theorem B512081 : Blo 147793 512081 := bstep (se 2 (by rfl) ⟨192030, by rfl⟩ : syracuseStep 512081 = 384061) B384061
theorem B151635 : Blo 147793 151635 := bstep (se 1 (by rfl) ⟨113726, by rfl⟩ : syracuseStep 151635 = 227453) B227453
theorem B151651 : Blo 147793 151651 := bstep (se 1 (by rfl) ⟨113738, by rfl⟩ : syracuseStep 151651 = 227477) B227477
theorem B151667 : Blo 147793 151667 := bstep (se 1 (by rfl) ⟨113750, by rfl⟩ : syracuseStep 151667 = 227501) B227501
theorem B479363 : Blo 147793 479363 := bstep (se 1 (by rfl) ⟨359522, by rfl⟩ : syracuseStep 479363 = 719045) B719045
theorem B151683 : Blo 147793 151683 := bstep (se 1 (by rfl) ⟨113762, by rfl⟩ : syracuseStep 151683 = 227525) B227525
theorem B151699 : Blo 147793 151699 := bstep (se 1 (by rfl) ⟨113774, by rfl⟩ : syracuseStep 151699 = 227549) B227549
theorem B151715 : Blo 147793 151715 := bstep (se 1 (by rfl) ⟨113786, by rfl⟩ : syracuseStep 151715 = 227573) B227573
theorem B250033 : Blo 147793 250033 := bstep (se 2 (by rfl) ⟨93762, by rfl⟩ : syracuseStep 250033 = 187525) B187525
theorem B151731 : Blo 147793 151731 := bstep (se 1 (by rfl) ⟨113798, by rfl⟩ : syracuseStep 151731 = 227597) B227597
theorem B151747 : Blo 147793 151747 := bstep (se 1 (by rfl) ⟨113810, by rfl⟩ : syracuseStep 151747 = 227621) B227621
theorem B250067 : Blo 147793 250067 := bstep (se 1 (by rfl) ⟨187550, by rfl⟩ : syracuseStep 250067 = 375101) B375101
theorem B151763 : Blo 147793 151763 := bstep (se 1 (by rfl) ⟨113822, by rfl⟩ : syracuseStep 151763 = 227645) B227645
theorem B151779 : Blo 147793 151779 := bstep (se 1 (by rfl) ⟨113834, by rfl⟩ : syracuseStep 151779 = 227669) B227669
theorem B807245 : Blo 147793 807245 := bstep (se 3 (by rfl) ⟨151358, by rfl⟩ : syracuseStep 807245 = 302717) B302717
theorem B250195 : Blo 147793 250195 := bstep (se 1 (by rfl) ⟨187646, by rfl⟩ : syracuseStep 250195 = 375293) B375293
theorem B1724813 : Blo 147793 1724813 := bstep (se 3 (by rfl) ⟨323402, by rfl⟩ : syracuseStep 1724813 = 646805) B646805
theorem B250337 : Blo 147793 250337 := bstep (se 2 (by rfl) ⟨93876, by rfl⟩ : syracuseStep 250337 = 187753) B187753
theorem B283171 : Blo 147793 283171 := bstep (se 1 (by rfl) ⟨212378, by rfl⟩ : syracuseStep 283171 = 424757) B424757
theorem B315971 : Blo 147793 315971 := bstep (se 1 (by rfl) ⟨236978, by rfl⟩ : syracuseStep 315971 = 473957) B473957
theorem B250465 : Blo 147793 250465 := bstep (se 2 (by rfl) ⟨93924, by rfl⟩ : syracuseStep 250465 = 187849) B187849
theorem B643697 : Blo 147793 643697 := bstep (se 2 (by rfl) ⟨241386, by rfl⟩ : syracuseStep 643697 = 482773) B482773
theorem B250499 : Blo 147793 250499 := bstep (se 1 (by rfl) ⟨187874, by rfl⟩ : syracuseStep 250499 = 375749) B375749
theorem B283331 : Blo 147793 283331 := bstep (se 1 (by rfl) ⟨212498, by rfl⟩ : syracuseStep 283331 = 424997) B424997
theorem B250627 : Blo 147793 250627 := bstep (se 1 (by rfl) ⟨187970, by rfl⟩ : syracuseStep 250627 = 375941) B375941
theorem B1528645 : Blo 147793 1528645 := bstep (se 4 (by rfl) ⟨143310, by rfl⟩ : syracuseStep 1528645 = 286621) B286621
theorem B1364849 : Blo 147793 1364849 := bstep (se 2 (by rfl) ⟨511818, by rfl⟩ : syracuseStep 1364849 = 1023637) B1023637
theorem B250769 : Blo 147793 250769 := bstep (se 2 (by rfl) ⟨94038, by rfl⟩ : syracuseStep 250769 = 188077) B188077
theorem B381905 : Blo 147793 381905 := bstep (se 2 (by rfl) ⟨143214, by rfl⟩ : syracuseStep 381905 = 286429) B286429
theorem B971747 : Blo 147793 971747 := bstep (se 1 (by rfl) ⟨728810, by rfl⟩ : syracuseStep 971747 = 1457621) B1457621
theorem B381955 : Blo 147793 381955 := bstep (se 1 (by rfl) ⟨286466, by rfl⟩ : syracuseStep 381955 = 572933) B572933
theorem B250897 : Blo 147793 250897 := bstep (se 2 (by rfl) ⟨94086, by rfl⟩ : syracuseStep 250897 = 188173) B188173
theorem B250931 : Blo 147793 250931 := bstep (se 1 (by rfl) ⟨188198, by rfl⟩ : syracuseStep 250931 = 376397) B376397
theorem B316561 : Blo 147793 316561 := bstep (se 2 (by rfl) ⟨118710, by rfl⟩ : syracuseStep 316561 = 237421) B237421
theorem B382097 : Blo 147793 382097 := bstep (se 2 (by rfl) ⟨143286, by rfl⟩ : syracuseStep 382097 = 286573) B286573
theorem B251059 : Blo 147793 251059 := bstep (se 1 (by rfl) ⟨188294, by rfl⟩ : syracuseStep 251059 = 376589) B376589
theorem B251201 : Blo 147793 251201 := bstep (se 2 (by rfl) ⟨94200, by rfl⟩ : syracuseStep 251201 = 188401) B188401
theorem B152947 : Blo 147793 152947 := bstep (se 1 (by rfl) ⟨114710, by rfl⟩ : syracuseStep 152947 = 229421) B229421
theorem B251329 : Blo 147793 251329 := bstep (se 2 (by rfl) ⟨94248, by rfl⟩ : syracuseStep 251329 = 188497) B188497
theorem B2807237 : Blo 147793 2807237 := bstep (se 4 (by rfl) ⟨263178, by rfl⟩ : syracuseStep 2807237 = 526357) B526357
theorem B251363 : Blo 147793 251363 := bstep (se 1 (by rfl) ⟨188522, by rfl⟩ : syracuseStep 251363 = 377045) B377045
theorem B251491 : Blo 147793 251491 := bstep (se 1 (by rfl) ⟨188618, by rfl⟩ : syracuseStep 251491 = 377237) B377237
theorem B251633 : Blo 147793 251633 := bstep (se 2 (by rfl) ⟨94362, by rfl⟩ : syracuseStep 251633 = 188725) B188725
theorem B284401 : Blo 147793 284401 := bstep (se 2 (by rfl) ⟨106650, by rfl⟩ : syracuseStep 284401 = 213301) B213301
theorem B481133 : Blo 147793 481133 := bstep (se 3 (by rfl) ⟨90212, by rfl⟩ : syracuseStep 481133 = 180425) B180425
theorem B251761 : Blo 147793 251761 := bstep (se 2 (by rfl) ⟨94410, by rfl⟩ : syracuseStep 251761 = 188821) B188821
theorem B251795 : Blo 147793 251795 := bstep (se 1 (by rfl) ⟨188846, by rfl⟩ : syracuseStep 251795 = 377693) B377693
theorem B1038257 : Blo 147793 1038257 := bstep (se 2 (by rfl) ⟨389346, by rfl⟩ : syracuseStep 1038257 = 778693) B778693
theorem B153523 : Blo 147793 153523 := bstep (se 1 (by rfl) ⟨115142, by rfl⟩ : syracuseStep 153523 = 230285) B230285
theorem B1103813 : Blo 147793 1103813 := bstep (se 4 (by rfl) ⟨103482, by rfl⟩ : syracuseStep 1103813 = 206965) B206965
theorem B481261 : Blo 147793 481261 := bstep (se 3 (by rfl) ⟨90236, by rfl⟩ : syracuseStep 481261 = 180473) B180473
theorem B251923 : Blo 147793 251923 := bstep (se 1 (by rfl) ⟨188942, by rfl⟩ : syracuseStep 251923 = 377885) B377885
theorem B1136753 : Blo 147793 1136753 := bstep (se 2 (by rfl) ⟨426282, by rfl⟩ : syracuseStep 1136753 = 852565) B852565
theorem B383089 : Blo 147793 383089 := bstep (se 2 (by rfl) ⟨143658, by rfl⟩ : syracuseStep 383089 = 287317) B287317
theorem B252065 : Blo 147793 252065 := bstep (se 2 (by rfl) ⟨94524, by rfl⟩ : syracuseStep 252065 = 189049) B189049
theorem B481517 : Blo 147793 481517 := bstep (se 3 (by rfl) ⟨90284, by rfl⟩ : syracuseStep 481517 = 180569) B180569
theorem B252193 : Blo 147793 252193 := bstep (se 2 (by rfl) ⟨94572, by rfl⟩ : syracuseStep 252193 = 189145) B189145
theorem B252227 : Blo 147793 252227 := bstep (se 1 (by rfl) ⟨189170, by rfl⟩ : syracuseStep 252227 = 378341) B378341
theorem B383363 : Blo 147793 383363 := bstep (se 1 (by rfl) ⟨287522, by rfl⟩ : syracuseStep 383363 = 575045) B575045
theorem B252355 : Blo 147793 252355 := bstep (se 1 (by rfl) ⟨189266, by rfl⟩ : syracuseStep 252355 = 378533) B378533
theorem B383555 : Blo 147793 383555 := bstep (se 1 (by rfl) ⟨287666, by rfl⟩ : syracuseStep 383555 = 575333) B575333
theorem B252497 : Blo 147793 252497 := bstep (se 2 (by rfl) ⟨94686, by rfl⟩ : syracuseStep 252497 = 189373) B189373
theorem B711281 : Blo 147793 711281 := bstep (se 2 (by rfl) ⟨266730, by rfl⟩ : syracuseStep 711281 = 533461) B533461
theorem B2153101 : Blo 147793 2153101 := bstep (se 3 (by rfl) ⟨403706, by rfl⟩ : syracuseStep 2153101 = 807413) B807413
theorem B580259 : Blo 147793 580259 := bstep (se 1 (by rfl) ⟨435194, by rfl⟩ : syracuseStep 580259 = 870389) B870389
theorem B252625 : Blo 147793 252625 := bstep (se 2 (by rfl) ⟨94734, by rfl⟩ : syracuseStep 252625 = 189469) B189469
theorem B252659 : Blo 147793 252659 := bstep (se 1 (by rfl) ⟨189494, by rfl⟩ : syracuseStep 252659 = 378989) B378989
theorem B285457 : Blo 147793 285457 := bstep (se 2 (by rfl) ⟨107046, by rfl⟩ : syracuseStep 285457 = 214093) B214093
theorem B252787 : Blo 147793 252787 := bstep (se 1 (by rfl) ⟨189590, by rfl⟩ : syracuseStep 252787 = 379181) B379181
theorem B187267 : Blo 147793 187267 := bstep (se 1 (by rfl) ⟨140450, by rfl⟩ : syracuseStep 187267 = 280901) B280901
theorem B187363 : Blo 147793 187363 := bstep (se 1 (by rfl) ⟨140522, by rfl⟩ : syracuseStep 187363 = 281045) B281045
theorem B908273 : Blo 147793 908273 := bstep (se 2 (by rfl) ⟨340602, by rfl⟩ : syracuseStep 908273 = 681205) B681205
theorem B252929 : Blo 147793 252929 := bstep (se 2 (by rfl) ⟨94848, by rfl⟩ : syracuseStep 252929 = 189697) B189697
theorem B646157 : Blo 147793 646157 := bstep (se 3 (by rfl) ⟨121154, by rfl⟩ : syracuseStep 646157 = 242309) B242309
theorem B1956917 : Blo 147793 1956917 := bstep (se 5 (by rfl) ⟨91730, by rfl⟩ : syracuseStep 1956917 = 183461) B183461
theorem B253057 : Blo 147793 253057 := bstep (se 2 (by rfl) ⟨94896, by rfl⟩ : syracuseStep 253057 = 189793) B189793
theorem B842885 : Blo 147793 842885 := bstep (se 4 (by rfl) ⟨79020, by rfl⟩ : syracuseStep 842885 = 158041) B158041
theorem B253091 : Blo 147793 253091 := bstep (se 1 (by rfl) ⟨189818, by rfl⟩ : syracuseStep 253091 = 379637) B379637
theorem B285859 : Blo 147793 285859 := bstep (se 1 (by rfl) ⟨214394, by rfl⟩ : syracuseStep 285859 = 428789) B428789
theorem B285905 : Blo 147793 285905 := bstep (se 2 (by rfl) ⟨107214, by rfl⟩ : syracuseStep 285905 = 214429) B214429
theorem B1727729 : Blo 147793 1727729 := bstep (se 2 (by rfl) ⟨647898, by rfl⟩ : syracuseStep 1727729 = 1295797) B1295797
theorem B253219 : Blo 147793 253219 := bstep (se 1 (by rfl) ⟨189914, by rfl⟩ : syracuseStep 253219 = 379829) B379829
theorem B515501 : Blo 147793 515501 := bstep (se 3 (by rfl) ⟨96656, by rfl⟩ : syracuseStep 515501 = 193313) B193313
theorem B253361 : Blo 147793 253361 := bstep (se 2 (by rfl) ⟨95010, by rfl⟩ : syracuseStep 253361 = 190021) B190021
theorem B187859 : Blo 147793 187859 := bstep (se 1 (by rfl) ⟨140894, by rfl⟩ : syracuseStep 187859 = 281789) B281789
theorem B286193 : Blo 147793 286193 := bstep (se 2 (by rfl) ⟨107322, by rfl⟩ : syracuseStep 286193 = 214645) B214645
theorem B253489 : Blo 147793 253489 := bstep (se 2 (by rfl) ⟨95058, by rfl⟩ : syracuseStep 253489 = 190117) B190117
theorem B253523 : Blo 147793 253523 := bstep (se 1 (by rfl) ⟨190142, by rfl⟩ : syracuseStep 253523 = 380285) B380285
theorem B253651 : Blo 147793 253651 := bstep (se 1 (by rfl) ⟨190238, by rfl⟩ : syracuseStep 253651 = 380477) B380477
theorem B483043 : Blo 147793 483043 := bstep (se 1 (by rfl) ⟨362282, by rfl⟩ : syracuseStep 483043 = 724565) B724565
theorem B548657 : Blo 147793 548657 := bstep (se 2 (by rfl) ⟨205746, by rfl⟩ : syracuseStep 548657 = 411493) B411493
theorem B253793 : Blo 147793 253793 := bstep (se 2 (by rfl) ⟨95172, by rfl⟩ : syracuseStep 253793 = 190345) B190345
theorem B2187121 : Blo 147793 2187121 := bstep (se 2 (by rfl) ⟨820170, by rfl⟩ : syracuseStep 2187121 = 1640341) B1640341
theorem B253921 : Blo 147793 253921 := bstep (se 2 (by rfl) ⟨95220, by rfl⟩ : syracuseStep 253921 = 190441) B190441
theorem B253955 : Blo 147793 253955 := bstep (se 1 (by rfl) ⟨190466, by rfl⟩ : syracuseStep 253955 = 380933) B380933
theorem B1630307 : Blo 147793 1630307 := bstep (se 1 (by rfl) ⟨1222730, by rfl⟩ : syracuseStep 1630307 = 2445461) B2445461
theorem B254083 : Blo 147793 254083 := bstep (se 1 (by rfl) ⟨190562, by rfl⟩ : syracuseStep 254083 = 381125) B381125
theorem B1532045 : Blo 147793 1532045 := bstep (se 3 (by rfl) ⟨287258, by rfl⟩ : syracuseStep 1532045 = 574517) B574517
theorem B188563 : Blo 147793 188563 := bstep (se 1 (by rfl) ⟨141422, by rfl⟩ : syracuseStep 188563 = 282845) B282845
theorem B286915 : Blo 147793 286915 := bstep (se 1 (by rfl) ⟨215186, by rfl⟩ : syracuseStep 286915 = 430373) B430373
theorem B188659 : Blo 147793 188659 := bstep (se 1 (by rfl) ⟨141494, by rfl⟩ : syracuseStep 188659 = 282989) B282989
theorem B319747 : Blo 147793 319747 := bstep (se 1 (by rfl) ⟨239810, by rfl⟩ : syracuseStep 319747 = 479621) B479621
theorem B254225 : Blo 147793 254225 := bstep (se 2 (by rfl) ⟨95334, by rfl⟩ : syracuseStep 254225 = 190669) B190669
theorem B647473 : Blo 147793 647473 := bstep (se 2 (by rfl) ⟨242802, by rfl⟩ : syracuseStep 647473 = 485605) B485605
theorem B483725 : Blo 147793 483725 := bstep (se 3 (by rfl) ⟨90698, by rfl⟩ : syracuseStep 483725 = 181397) B181397
theorem B254353 : Blo 147793 254353 := bstep (se 2 (by rfl) ⟨95382, by rfl⟩ : syracuseStep 254353 = 190765) B190765
theorem B254387 : Blo 147793 254387 := bstep (se 1 (by rfl) ⟨190790, by rfl⟩ : syracuseStep 254387 = 381581) B381581
theorem B221699 : Blo 147793 221699 := bstep (se 1 (by rfl) ⟨166274, by rfl⟩ : syracuseStep 221699 = 332549) B332549
theorem B221729 : Blo 147793 221729 := bstep (se 2 (by rfl) ⟨83148, by rfl⟩ : syracuseStep 221729 = 166297) B166297
theorem B221747 : Blo 147793 221747 := bstep (se 1 (by rfl) ⟨166310, by rfl⟩ : syracuseStep 221747 = 332621) B332621
theorem B254515 : Blo 147793 254515 := bstep (se 1 (by rfl) ⟨190886, by rfl⟩ : syracuseStep 254515 = 381773) B381773
theorem B221777 : Blo 147793 221777 := bstep (se 2 (by rfl) ⟨83166, by rfl⟩ : syracuseStep 221777 = 166333) B166333
theorem B221795 : Blo 147793 221795 := bstep (se 1 (by rfl) ⟨166346, by rfl⟩ : syracuseStep 221795 = 332693) B332693
theorem B221825 : Blo 147793 221825 := bstep (se 2 (by rfl) ⟨83184, by rfl⟩ : syracuseStep 221825 = 166369) B166369
theorem B287363 : Blo 147793 287363 := bstep (se 1 (by rfl) ⟨215522, by rfl⟩ : syracuseStep 287363 = 431045) B431045
theorem B713357 : Blo 147793 713357 := bstep (se 3 (by rfl) ⟨133754, by rfl⟩ : syracuseStep 713357 = 267509) B267509
theorem B221843 : Blo 147793 221843 := bstep (se 1 (by rfl) ⟨166382, by rfl⟩ : syracuseStep 221843 = 332765) B332765
theorem B221873 : Blo 147793 221873 := bstep (se 2 (by rfl) ⟨83202, by rfl⟩ : syracuseStep 221873 = 166405) B166405
theorem B254657 : Blo 147793 254657 := bstep (se 2 (by rfl) ⟨95496, by rfl⟩ : syracuseStep 254657 = 190993) B190993
theorem B221891 : Blo 147793 221891 := bstep (se 1 (by rfl) ⟨166418, by rfl⟩ : syracuseStep 221891 = 332837) B332837
theorem B221921 : Blo 147793 221921 := bstep (se 2 (by rfl) ⟨83220, by rfl⟩ : syracuseStep 221921 = 166441) B166441
theorem B189155 : Blo 147793 189155 := bstep (se 1 (by rfl) ⟨141866, by rfl⟩ : syracuseStep 189155 = 283733) B283733
theorem B221939 : Blo 147793 221939 := bstep (se 1 (by rfl) ⟨166454, by rfl⟩ : syracuseStep 221939 = 332909) B332909
theorem B221969 : Blo 147793 221969 := bstep (se 2 (by rfl) ⟨83238, by rfl⟩ : syracuseStep 221969 = 166477) B166477
theorem B221987 : Blo 147793 221987 := bstep (se 1 (by rfl) ⟨166490, by rfl⟩ : syracuseStep 221987 = 332981) B332981
theorem B222017 : Blo 147793 222017 := bstep (se 2 (by rfl) ⟨83256, by rfl⟩ : syracuseStep 222017 = 166513) B166513
theorem B254785 : Blo 147793 254785 := bstep (se 2 (by rfl) ⟨95544, by rfl⟩ : syracuseStep 254785 = 191089) B191089
theorem B222035 : Blo 147793 222035 := bstep (se 1 (by rfl) ⟨166526, by rfl⟩ : syracuseStep 222035 = 333053) B333053
theorem B254819 : Blo 147793 254819 := bstep (se 1 (by rfl) ⟨191114, by rfl⟩ : syracuseStep 254819 = 382229) B382229
theorem B222065 : Blo 147793 222065 := bstep (se 2 (by rfl) ⟨83274, by rfl⟩ : syracuseStep 222065 = 166549) B166549
theorem B222083 : Blo 147793 222083 := bstep (se 1 (by rfl) ⟨166562, by rfl⟩ : syracuseStep 222083 = 333125) B333125
theorem B222113 : Blo 147793 222113 := bstep (se 2 (by rfl) ⟨83292, by rfl⟩ : syracuseStep 222113 = 166585) B166585
theorem B287651 : Blo 147793 287651 := bstep (se 1 (by rfl) ⟨215738, by rfl⟩ : syracuseStep 287651 = 431477) B431477
theorem B222131 : Blo 147793 222131 := bstep (se 1 (by rfl) ⟨166598, by rfl⟩ : syracuseStep 222131 = 333197) B333197
theorem B222161 : Blo 147793 222161 := bstep (se 2 (by rfl) ⟨83310, by rfl⟩ : syracuseStep 222161 = 166621) B166621
theorem B222179 : Blo 147793 222179 := bstep (se 1 (by rfl) ⟨166634, by rfl⟩ : syracuseStep 222179 = 333269) B333269
theorem B254947 : Blo 147793 254947 := bstep (se 1 (by rfl) ⟨191210, by rfl⟩ : syracuseStep 254947 = 382421) B382421
theorem B1172465 : Blo 147793 1172465 := bstep (se 2 (by rfl) ⟨439674, by rfl⟩ : syracuseStep 1172465 = 879349) B879349
theorem B222209 : Blo 147793 222209 := bstep (se 2 (by rfl) ⟨83328, by rfl⟩ : syracuseStep 222209 = 166657) B166657
theorem B222227 : Blo 147793 222227 := bstep (se 1 (by rfl) ⟨166670, by rfl⟩ : syracuseStep 222227 = 333341) B333341
theorem B222257 : Blo 147793 222257 := bstep (se 2 (by rfl) ⟨83346, by rfl⟩ : syracuseStep 222257 = 166693) B166693
theorem B222275 : Blo 147793 222275 := bstep (se 1 (by rfl) ⟨166706, by rfl⟩ : syracuseStep 222275 = 333413) B333413
theorem B320593 : Blo 147793 320593 := bstep (se 2 (by rfl) ⟨120222, by rfl⟩ : syracuseStep 320593 = 240445) B240445
theorem B222305 : Blo 147793 222305 := bstep (se 2 (by rfl) ⟨83364, by rfl⟩ : syracuseStep 222305 = 166729) B166729
theorem B255089 : Blo 147793 255089 := bstep (se 2 (by rfl) ⟨95658, by rfl⟩ : syracuseStep 255089 = 191317) B191317
theorem B222323 : Blo 147793 222323 := bstep (se 1 (by rfl) ⟨166742, by rfl⟩ : syracuseStep 222323 = 333485) B333485
theorem B222353 : Blo 147793 222353 := bstep (se 2 (by rfl) ⟨83382, by rfl⟩ : syracuseStep 222353 = 166765) B166765
theorem B222371 : Blo 147793 222371 := bstep (se 1 (by rfl) ⟨166778, by rfl⟩ : syracuseStep 222371 = 333557) B333557
theorem B222401 : Blo 147793 222401 := bstep (se 2 (by rfl) ⟨83400, by rfl⟩ : syracuseStep 222401 = 166801) B166801
theorem B222419 : Blo 147793 222419 := bstep (se 1 (by rfl) ⟨166814, by rfl⟩ : syracuseStep 222419 = 333629) B333629
theorem B222449 : Blo 147793 222449 := bstep (se 2 (by rfl) ⟨83418, by rfl⟩ : syracuseStep 222449 = 166837) B166837
theorem B255217 : Blo 147793 255217 := bstep (se 2 (by rfl) ⟨95706, by rfl⟩ : syracuseStep 255217 = 191413) B191413
theorem B222467 : Blo 147793 222467 := bstep (se 1 (by rfl) ⟨166850, by rfl⟩ : syracuseStep 222467 = 333701) B333701
theorem B255251 : Blo 147793 255251 := bstep (se 1 (by rfl) ⟨191438, by rfl⟩ : syracuseStep 255251 = 382877) B382877
theorem B222497 : Blo 147793 222497 := bstep (se 2 (by rfl) ⟨83436, by rfl⟩ : syracuseStep 222497 = 166873) B166873
theorem B484643 : Blo 147793 484643 := bstep (se 1 (by rfl) ⟨363482, by rfl⟩ : syracuseStep 484643 = 726965) B726965
theorem B222515 : Blo 147793 222515 := bstep (se 1 (by rfl) ⟨166886, by rfl⟩ : syracuseStep 222515 = 333773) B333773
theorem B222545 : Blo 147793 222545 := bstep (se 2 (by rfl) ⟨83454, by rfl⟩ : syracuseStep 222545 = 166909) B166909
theorem B222563 : Blo 147793 222563 := bstep (se 1 (by rfl) ⟨166922, by rfl⟩ : syracuseStep 222563 = 333845) B333845
theorem B222593 : Blo 147793 222593 := bstep (se 2 (by rfl) ⟨83472, by rfl⟩ : syracuseStep 222593 = 166945) B166945
theorem B222611 : Blo 147793 222611 := bstep (se 1 (by rfl) ⟨166958, by rfl⟩ : syracuseStep 222611 = 333917) B333917
theorem B255379 : Blo 147793 255379 := bstep (se 1 (by rfl) ⟨191534, by rfl⟩ : syracuseStep 255379 = 383069) B383069
theorem B189859 : Blo 147793 189859 := bstep (se 1 (by rfl) ⟨142394, by rfl⟩ : syracuseStep 189859 = 284789) B284789
theorem B222641 : Blo 147793 222641 := bstep (se 2 (by rfl) ⟨83490, by rfl⟩ : syracuseStep 222641 = 166981) B166981
theorem B222659 : Blo 147793 222659 := bstep (se 1 (by rfl) ⟨166994, by rfl⟩ : syracuseStep 222659 = 333989) B333989
theorem B222689 : Blo 147793 222689 := bstep (se 2 (by rfl) ⟨83508, by rfl⟩ : syracuseStep 222689 = 167017) B167017
theorem B222707 : Blo 147793 222707 := bstep (se 1 (by rfl) ⟨167030, by rfl⟩ : syracuseStep 222707 = 334061) B334061
theorem B189955 : Blo 147793 189955 := bstep (se 1 (by rfl) ⟨142466, by rfl⟩ : syracuseStep 189955 = 284933) B284933
theorem B222737 : Blo 147793 222737 := bstep (se 2 (by rfl) ⟨83526, by rfl⟩ : syracuseStep 222737 = 167053) B167053
theorem B255521 : Blo 147793 255521 := bstep (se 2 (by rfl) ⟨95820, by rfl⟩ : syracuseStep 255521 = 191641) B191641
theorem B222755 : Blo 147793 222755 := bstep (se 1 (by rfl) ⟨167066, by rfl⟩ : syracuseStep 222755 = 334133) B334133
theorem B222785 : Blo 147793 222785 := bstep (se 2 (by rfl) ⟨83544, by rfl⟩ : syracuseStep 222785 = 167089) B167089
theorem B222803 : Blo 147793 222803 := bstep (se 1 (by rfl) ⟨167102, by rfl⟩ : syracuseStep 222803 = 334205) B334205
theorem B222833 : Blo 147793 222833 := bstep (se 2 (by rfl) ⟨83562, by rfl⟩ : syracuseStep 222833 = 167125) B167125
theorem B222851 : Blo 147793 222851 := bstep (se 1 (by rfl) ⟨167138, by rfl⟩ : syracuseStep 222851 = 334277) B334277
theorem B222881 : Blo 147793 222881 := bstep (se 2 (by rfl) ⟨83580, by rfl⟩ : syracuseStep 222881 = 167161) B167161
theorem B255649 : Blo 147793 255649 := bstep (se 2 (by rfl) ⟨95868, by rfl⟩ : syracuseStep 255649 = 191737) B191737
theorem B222899 : Blo 147793 222899 := bstep (se 1 (by rfl) ⟨167174, by rfl⟩ : syracuseStep 222899 = 334349) B334349
theorem B255683 : Blo 147793 255683 := bstep (se 1 (by rfl) ⟨191762, by rfl⟩ : syracuseStep 255683 = 383525) B383525
theorem B222929 : Blo 147793 222929 := bstep (se 2 (by rfl) ⟨83598, by rfl⟩ : syracuseStep 222929 = 167197) B167197
theorem B222947 : Blo 147793 222947 := bstep (se 1 (by rfl) ⟨167210, by rfl⟩ : syracuseStep 222947 = 334421) B334421
theorem B1271537 : Blo 147793 1271537 := bstep (se 2 (by rfl) ⟨476826, by rfl⟩ : syracuseStep 1271537 = 953653) B953653
theorem B222977 : Blo 147793 222977 := bstep (se 2 (by rfl) ⟨83616, by rfl⟩ : syracuseStep 222977 = 167233) B167233
theorem B222995 : Blo 147793 222995 := bstep (se 1 (by rfl) ⟨167246, by rfl⟩ : syracuseStep 222995 = 334493) B334493
theorem B223025 : Blo 147793 223025 := bstep (se 2 (by rfl) ⟨83634, by rfl⟩ : syracuseStep 223025 = 167269) B167269
theorem B223043 : Blo 147793 223043 := bstep (se 1 (by rfl) ⟨167282, by rfl⟩ : syracuseStep 223043 = 334565) B334565
theorem B255811 : Blo 147793 255811 := bstep (se 1 (by rfl) ⟨191858, by rfl⟩ : syracuseStep 255811 = 383717) B383717
theorem B223073 : Blo 147793 223073 := bstep (se 2 (by rfl) ⟨83652, by rfl⟩ : syracuseStep 223073 = 167305) B167305
theorem B583537 : Blo 147793 583537 := bstep (se 2 (by rfl) ⟨218826, by rfl⟩ : syracuseStep 583537 = 437653) B437653
theorem B223091 : Blo 147793 223091 := bstep (se 1 (by rfl) ⟨167318, by rfl⟩ : syracuseStep 223091 = 334637) B334637
theorem B223121 : Blo 147793 223121 := bstep (se 2 (by rfl) ⟨83670, by rfl⟩ : syracuseStep 223121 = 167341) B167341
theorem B223139 : Blo 147793 223139 := bstep (se 1 (by rfl) ⟨167354, by rfl⟩ : syracuseStep 223139 = 334709) B334709
theorem B223169 : Blo 147793 223169 := bstep (se 2 (by rfl) ⟨83688, by rfl⟩ : syracuseStep 223169 = 167377) B167377
theorem B255953 : Blo 147793 255953 := bstep (se 2 (by rfl) ⟨95982, by rfl⟩ : syracuseStep 255953 = 191965) B191965
theorem B223187 : Blo 147793 223187 := bstep (se 1 (by rfl) ⟨167390, by rfl⟩ : syracuseStep 223187 = 334781) B334781
theorem B223217 : Blo 147793 223217 := bstep (se 2 (by rfl) ⟨83706, by rfl⟩ : syracuseStep 223217 = 167413) B167413
theorem B190451 : Blo 147793 190451 := bstep (se 1 (by rfl) ⟨142838, by rfl⟩ : syracuseStep 190451 = 285677) B285677
theorem B223235 : Blo 147793 223235 := bstep (se 1 (by rfl) ⟨167426, by rfl⟩ : syracuseStep 223235 = 334853) B334853
theorem B419843 : Blo 147793 419843 := bstep (se 1 (by rfl) ⟨314882, by rfl⟩ : syracuseStep 419843 = 629765) B629765
theorem B223265 : Blo 147793 223265 := bstep (se 2 (by rfl) ⟨83724, by rfl⟩ : syracuseStep 223265 = 167449) B167449
theorem B223283 : Blo 147793 223283 := bstep (se 1 (by rfl) ⟨167462, by rfl⟩ : syracuseStep 223283 = 334925) B334925
theorem B223313 : Blo 147793 223313 := bstep (se 2 (by rfl) ⟨83742, by rfl⟩ : syracuseStep 223313 = 167485) B167485
theorem B256081 : Blo 147793 256081 := bstep (se 2 (by rfl) ⟨96030, by rfl⟩ : syracuseStep 256081 = 192061) B192061
theorem B223331 : Blo 147793 223331 := bstep (se 1 (by rfl) ⟨167498, by rfl⟩ : syracuseStep 223331 = 334997) B334997
theorem B256115 : Blo 147793 256115 := bstep (se 1 (by rfl) ⟨192086, by rfl⟩ : syracuseStep 256115 = 384173) B384173
theorem B223361 : Blo 147793 223361 := bstep (se 2 (by rfl) ⟨83760, by rfl⟩ : syracuseStep 223361 = 167521) B167521
theorem B223379 : Blo 147793 223379 := bstep (se 1 (by rfl) ⟨167534, by rfl⟩ : syracuseStep 223379 = 335069) B335069
theorem B223409 : Blo 147793 223409 := bstep (se 2 (by rfl) ⟨83778, by rfl⟩ : syracuseStep 223409 = 167557) B167557
theorem B223427 : Blo 147793 223427 := bstep (se 1 (by rfl) ⟨167570, by rfl⟩ : syracuseStep 223427 = 335141) B335141
theorem B223457 : Blo 147793 223457 := bstep (se 2 (by rfl) ⟨83796, by rfl⟩ : syracuseStep 223457 = 167593) B167593
theorem B485617 : Blo 147793 485617 := bstep (se 2 (by rfl) ⟨182106, by rfl⟩ : syracuseStep 485617 = 364213) B364213
theorem B223475 : Blo 147793 223475 := bstep (se 1 (by rfl) ⟨167606, by rfl⟩ : syracuseStep 223475 = 335213) B335213
theorem B223505 : Blo 147793 223505 := bstep (se 2 (by rfl) ⟨83814, by rfl⟩ : syracuseStep 223505 = 167629) B167629
theorem B223523 : Blo 147793 223523 := bstep (se 1 (by rfl) ⟨167642, by rfl⟩ : syracuseStep 223523 = 335285) B335285
theorem B223553 : Blo 147793 223553 := bstep (se 2 (by rfl) ⟨83832, by rfl⟩ : syracuseStep 223553 = 167665) B167665
theorem B518467 : Blo 147793 518467 := bstep (se 1 (by rfl) ⟨388850, by rfl⟩ : syracuseStep 518467 = 777701) B777701
theorem B223571 : Blo 147793 223571 := bstep (se 1 (by rfl) ⟨167678, by rfl⟩ : syracuseStep 223571 = 335357) B335357
theorem B223601 : Blo 147793 223601 := bstep (se 2 (by rfl) ⟨83850, by rfl⟩ : syracuseStep 223601 = 167701) B167701
theorem B223619 : Blo 147793 223619 := bstep (se 1 (by rfl) ⟨167714, by rfl⟩ : syracuseStep 223619 = 335429) B335429
theorem B223649 : Blo 147793 223649 := bstep (se 2 (by rfl) ⟨83868, by rfl⟩ : syracuseStep 223649 = 167737) B167737
theorem B223667 : Blo 147793 223667 := bstep (se 1 (by rfl) ⟨167750, by rfl⟩ : syracuseStep 223667 = 335501) B335501
theorem B223697 : Blo 147793 223697 := bstep (se 2 (by rfl) ⟨83886, by rfl⟩ : syracuseStep 223697 = 167773) B167773
theorem B223715 : Blo 147793 223715 := bstep (se 1 (by rfl) ⟨167786, by rfl⟩ : syracuseStep 223715 = 335573) B335573
theorem B223745 : Blo 147793 223745 := bstep (se 2 (by rfl) ⟨83904, by rfl⟩ : syracuseStep 223745 = 167809) B167809
theorem B223763 : Blo 147793 223763 := bstep (se 1 (by rfl) ⟨167822, by rfl⟩ : syracuseStep 223763 = 335645) B335645
theorem B223793 : Blo 147793 223793 := bstep (se 2 (by rfl) ⟨83922, by rfl⟩ : syracuseStep 223793 = 167845) B167845
theorem B223811 : Blo 147793 223811 := bstep (se 1 (by rfl) ⟨167858, by rfl⟩ : syracuseStep 223811 = 335717) B335717
theorem B223841 : Blo 147793 223841 := bstep (se 2 (by rfl) ⟨83940, by rfl⟩ : syracuseStep 223841 = 167881) B167881
theorem B289379 : Blo 147793 289379 := bstep (se 1 (by rfl) ⟨217034, by rfl⟩ : syracuseStep 289379 = 434069) B434069
theorem B2746993 : Blo 147793 2746993 := bstep (se 2 (by rfl) ⟨1030122, by rfl⟩ : syracuseStep 2746993 = 2060245) B2060245
theorem B223859 : Blo 147793 223859 := bstep (se 1 (by rfl) ⟨167894, by rfl⟩ : syracuseStep 223859 = 335789) B335789
theorem B223889 : Blo 147793 223889 := bstep (se 2 (by rfl) ⟨83958, by rfl⟩ : syracuseStep 223889 = 167917) B167917
theorem B223907 : Blo 147793 223907 := bstep (se 1 (by rfl) ⟨167930, by rfl⟩ : syracuseStep 223907 = 335861) B335861
theorem B191155 : Blo 147793 191155 := bstep (se 1 (by rfl) ⟨143366, by rfl⟩ : syracuseStep 191155 = 286733) B286733
theorem B223937 : Blo 147793 223937 := bstep (se 2 (by rfl) ⟨83976, by rfl⟩ : syracuseStep 223937 = 167953) B167953
theorem B223955 : Blo 147793 223955 := bstep (se 1 (by rfl) ⟨167966, by rfl⟩ : syracuseStep 223955 = 335933) B335933
theorem B191203 : Blo 147793 191203 := bstep (se 1 (by rfl) ⟨143402, by rfl⟩ : syracuseStep 191203 = 286805) B286805
theorem B223985 : Blo 147793 223985 := bstep (se 2 (by rfl) ⟨83994, by rfl⟩ : syracuseStep 223985 = 167989) B167989
theorem B224003 : Blo 147793 224003 := bstep (se 1 (by rfl) ⟨168002, by rfl⟩ : syracuseStep 224003 = 336005) B336005
theorem B191251 : Blo 147793 191251 := bstep (se 1 (by rfl) ⟨143438, by rfl⟩ : syracuseStep 191251 = 286877) B286877
theorem B224033 : Blo 147793 224033 := bstep (se 2 (by rfl) ⟨84012, by rfl⟩ : syracuseStep 224033 = 168025) B168025
theorem B551729 : Blo 147793 551729 := bstep (se 2 (by rfl) ⟨206898, by rfl⟩ : syracuseStep 551729 = 413797) B413797
theorem B224051 : Blo 147793 224051 := bstep (se 1 (by rfl) ⟨168038, by rfl⟩ : syracuseStep 224051 = 336077) B336077
theorem B224081 : Blo 147793 224081 := bstep (se 2 (by rfl) ⟨84030, by rfl⟩ : syracuseStep 224081 = 168061) B168061
theorem B224099 : Blo 147793 224099 := bstep (se 1 (by rfl) ⟨168074, by rfl⟩ : syracuseStep 224099 = 336149) B336149
theorem B224129 : Blo 147793 224129 := bstep (se 2 (by rfl) ⟨84048, by rfl⟩ : syracuseStep 224129 = 168097) B168097
theorem B387971 : Blo 147793 387971 := bstep (se 1 (by rfl) ⟨290978, by rfl⟩ : syracuseStep 387971 = 581957) B581957
theorem B1895309 : Blo 147793 1895309 := bstep (se 3 (by rfl) ⟨355370, by rfl⟩ : syracuseStep 1895309 = 710741) B710741
theorem B846733 : Blo 147793 846733 := bstep (se 3 (by rfl) ⟨158762, by rfl⟩ : syracuseStep 846733 = 317525) B317525
theorem B224147 : Blo 147793 224147 := bstep (se 1 (by rfl) ⟨168110, by rfl⟩ : syracuseStep 224147 = 336221) B336221
theorem B322481 : Blo 147793 322481 := bstep (se 2 (by rfl) ⟨120930, by rfl⟩ : syracuseStep 322481 = 241861) B241861
theorem B224177 : Blo 147793 224177 := bstep (se 2 (by rfl) ⟨84066, by rfl⟩ : syracuseStep 224177 = 168133) B168133
theorem B224195 : Blo 147793 224195 := bstep (se 1 (by rfl) ⟨168146, by rfl⟩ : syracuseStep 224195 = 336293) B336293
theorem B224225 : Blo 147793 224225 := bstep (se 2 (by rfl) ⟨84084, by rfl⟩ : syracuseStep 224225 = 168169) B168169
theorem B224243 : Blo 147793 224243 := bstep (se 1 (by rfl) ⟨168182, by rfl⟩ : syracuseStep 224243 = 336365) B336365
theorem B224273 : Blo 147793 224273 := bstep (se 2 (by rfl) ⟨84102, by rfl⟩ : syracuseStep 224273 = 168205) B168205
theorem B224291 : Blo 147793 224291 := bstep (se 1 (by rfl) ⟨168218, by rfl⟩ : syracuseStep 224291 = 336437) B336437
theorem B224321 : Blo 147793 224321 := bstep (se 2 (by rfl) ⟨84120, by rfl⟩ : syracuseStep 224321 = 168241) B168241
theorem B453709 : Blo 147793 453709 := bstep (se 3 (by rfl) ⟨85070, by rfl⟩ : syracuseStep 453709 = 170141) B170141
theorem B224339 : Blo 147793 224339 := bstep (se 1 (by rfl) ⟨168254, by rfl⟩ : syracuseStep 224339 = 336509) B336509
theorem B224369 : Blo 147793 224369 := bstep (se 2 (by rfl) ⟨84138, by rfl⟩ : syracuseStep 224369 = 168277) B168277
theorem B224387 : Blo 147793 224387 := bstep (se 1 (by rfl) ⟨168290, by rfl⟩ : syracuseStep 224387 = 336581) B336581
theorem B224417 : Blo 147793 224417 := bstep (se 2 (by rfl) ⟨84156, by rfl⟩ : syracuseStep 224417 = 168313) B168313
theorem B224435 : Blo 147793 224435 := bstep (se 1 (by rfl) ⟨168326, by rfl⟩ : syracuseStep 224435 = 336653) B336653
theorem B224465 : Blo 147793 224465 := bstep (se 2 (by rfl) ⟨84174, by rfl⟩ : syracuseStep 224465 = 168349) B168349
theorem B224483 : Blo 147793 224483 := bstep (se 1 (by rfl) ⟨168362, by rfl⟩ : syracuseStep 224483 = 336725) B336725
theorem B224513 : Blo 147793 224513 := bstep (se 2 (by rfl) ⟨84192, by rfl⟩ : syracuseStep 224513 = 168385) B168385
theorem B191747 : Blo 147793 191747 := bstep (se 1 (by rfl) ⟨143810, by rfl⟩ : syracuseStep 191747 = 287621) B287621
theorem B224531 : Blo 147793 224531 := bstep (se 1 (by rfl) ⟨168398, by rfl⟩ : syracuseStep 224531 = 336797) B336797
theorem B224561 : Blo 147793 224561 := bstep (se 2 (by rfl) ⟨84210, by rfl⟩ : syracuseStep 224561 = 168421) B168421
theorem B224579 : Blo 147793 224579 := bstep (se 1 (by rfl) ⟨168434, by rfl⟩ : syracuseStep 224579 = 336869) B336869
theorem B224609 : Blo 147793 224609 := bstep (se 2 (by rfl) ⟨84228, by rfl⟩ : syracuseStep 224609 = 168457) B168457
theorem B1371491 : Blo 147793 1371491 := bstep (se 1 (by rfl) ⟨1028618, by rfl⟩ : syracuseStep 1371491 = 2057237) B2057237
theorem B224627 : Blo 147793 224627 := bstep (se 1 (by rfl) ⟨168470, by rfl⟩ : syracuseStep 224627 = 336941) B336941
theorem B224657 : Blo 147793 224657 := bstep (se 2 (by rfl) ⟨84246, by rfl⟩ : syracuseStep 224657 = 168493) B168493
theorem B355747 : Blo 147793 355747 := bstep (se 1 (by rfl) ⟨266810, by rfl⟩ : syracuseStep 355747 = 533621) B533621
theorem B224675 : Blo 147793 224675 := bstep (se 1 (by rfl) ⟨168506, by rfl⟩ : syracuseStep 224675 = 337013) B337013
theorem B224705 : Blo 147793 224705 := bstep (se 2 (by rfl) ⟨84264, by rfl⟩ : syracuseStep 224705 = 168529) B168529
theorem B224723 : Blo 147793 224723 := bstep (se 1 (by rfl) ⟨168542, by rfl⟩ : syracuseStep 224723 = 337085) B337085
theorem B159203 : Blo 147793 159203 := bstep (se 1 (by rfl) ⟨119402, by rfl⟩ : syracuseStep 159203 = 238805) B238805
theorem B224753 : Blo 147793 224753 := bstep (se 2 (by rfl) ⟨84282, by rfl⟩ : syracuseStep 224753 = 168565) B168565
theorem B224771 : Blo 147793 224771 := bstep (se 1 (by rfl) ⟨168578, by rfl⟩ : syracuseStep 224771 = 337157) B337157
theorem B224801 : Blo 147793 224801 := bstep (se 2 (by rfl) ⟨84300, by rfl⟩ : syracuseStep 224801 = 168601) B168601
theorem B224819 : Blo 147793 224819 := bstep (se 1 (by rfl) ⟨168614, by rfl⟩ : syracuseStep 224819 = 337229) B337229
theorem B421453 : Blo 147793 421453 := bstep (se 3 (by rfl) ⟨79022, by rfl⟩ : syracuseStep 421453 = 158045) B158045
theorem B224849 : Blo 147793 224849 := bstep (se 2 (by rfl) ⟨84318, by rfl⟩ : syracuseStep 224849 = 168637) B168637
theorem B454243 : Blo 147793 454243 := bstep (se 1 (by rfl) ⟨340682, by rfl⟩ : syracuseStep 454243 = 681365) B681365
theorem B224867 : Blo 147793 224867 := bstep (se 1 (by rfl) ⟨168650, by rfl⟩ : syracuseStep 224867 = 337301) B337301
theorem B224897 : Blo 147793 224897 := bstep (se 2 (by rfl) ⟨84336, by rfl⟩ : syracuseStep 224897 = 168673) B168673
theorem B224915 : Blo 147793 224915 := bstep (se 1 (by rfl) ⟨168686, by rfl⟩ : syracuseStep 224915 = 337373) B337373
theorem B224945 : Blo 147793 224945 := bstep (se 2 (by rfl) ⟨84354, by rfl⟩ : syracuseStep 224945 = 168709) B168709
theorem B224963 : Blo 147793 224963 := bstep (se 1 (by rfl) ⟨168722, by rfl⟩ : syracuseStep 224963 = 337445) B337445
theorem B224993 : Blo 147793 224993 := bstep (se 2 (by rfl) ⟨84372, by rfl⟩ : syracuseStep 224993 = 168745) B168745
theorem B225011 : Blo 147793 225011 := bstep (se 1 (by rfl) ⟨168758, by rfl⟩ : syracuseStep 225011 = 337517) B337517
theorem B913157 : Blo 147793 913157 := bstep (se 4 (by rfl) ⟨85608, by rfl⟩ : syracuseStep 913157 = 171217) B171217
theorem B225041 : Blo 147793 225041 := bstep (se 2 (by rfl) ⟨84390, by rfl⟩ : syracuseStep 225041 = 168781) B168781
theorem B225059 : Blo 147793 225059 := bstep (se 1 (by rfl) ⟨168794, by rfl⟩ : syracuseStep 225059 = 337589) B337589
theorem B421681 : Blo 147793 421681 := bstep (se 2 (by rfl) ⟨158130, by rfl⟩ : syracuseStep 421681 = 316261) B316261
theorem B225089 : Blo 147793 225089 := bstep (se 2 (by rfl) ⟨84408, by rfl⟩ : syracuseStep 225089 = 168817) B168817
theorem B225107 : Blo 147793 225107 := bstep (se 1 (by rfl) ⟨168830, by rfl⟩ : syracuseStep 225107 = 337661) B337661
theorem B749411 : Blo 147793 749411 := bstep (se 1 (by rfl) ⟨562058, by rfl⟩ : syracuseStep 749411 = 1124117) B1124117
theorem B225137 : Blo 147793 225137 := bstep (se 2 (by rfl) ⟨84426, by rfl⟩ : syracuseStep 225137 = 168853) B168853
theorem B225155 : Blo 147793 225155 := bstep (se 1 (by rfl) ⟨168866, by rfl⟩ : syracuseStep 225155 = 337733) B337733
theorem B225185 : Blo 147793 225185 := bstep (se 2 (by rfl) ⟨84444, by rfl⟩ : syracuseStep 225185 = 168889) B168889
theorem B225203 : Blo 147793 225203 := bstep (se 1 (by rfl) ⟨168902, by rfl⟩ : syracuseStep 225203 = 337805) B337805
theorem B421841 : Blo 147793 421841 := bstep (se 2 (by rfl) ⟨158190, by rfl⟩ : syracuseStep 421841 = 316381) B316381
theorem B225233 : Blo 147793 225233 := bstep (se 2 (by rfl) ⟨84462, by rfl⟩ : syracuseStep 225233 = 168925) B168925
theorem B225251 : Blo 147793 225251 := bstep (se 1 (by rfl) ⟨168938, by rfl⟩ : syracuseStep 225251 = 337877) B337877
theorem B225281 : Blo 147793 225281 := bstep (se 2 (by rfl) ⟨84480, by rfl⟩ : syracuseStep 225281 = 168961) B168961
theorem B225299 : Blo 147793 225299 := bstep (se 1 (by rfl) ⟨168974, by rfl⟩ : syracuseStep 225299 = 337949) B337949
theorem B1011761 : Blo 147793 1011761 := bstep (se 2 (by rfl) ⟨379410, by rfl⟩ : syracuseStep 1011761 = 758821) B758821
theorem B225329 : Blo 147793 225329 := bstep (se 2 (by rfl) ⟨84498, by rfl⟩ : syracuseStep 225329 = 168997) B168997
theorem B421955 : Blo 147793 421955 := bstep (se 1 (by rfl) ⟨316466, by rfl⟩ : syracuseStep 421955 = 632933) B632933
theorem B225347 : Blo 147793 225347 := bstep (se 1 (by rfl) ⟨169010, by rfl⟩ : syracuseStep 225347 = 338021) B338021
theorem B225377 : Blo 147793 225377 := bstep (se 2 (by rfl) ⟨84516, by rfl⟩ : syracuseStep 225377 = 169033) B169033
theorem B225395 : Blo 147793 225395 := bstep (se 1 (by rfl) ⟨169046, by rfl⟩ : syracuseStep 225395 = 338093) B338093
theorem B225425 : Blo 147793 225425 := bstep (se 2 (by rfl) ⟨84534, by rfl⟩ : syracuseStep 225425 = 169069) B169069
theorem B225443 : Blo 147793 225443 := bstep (se 1 (by rfl) ⟨169082, by rfl⟩ : syracuseStep 225443 = 338165) B338165
theorem B225473 : Blo 147793 225473 := bstep (se 2 (by rfl) ⟨84552, by rfl⟩ : syracuseStep 225473 = 169105) B169105
theorem B323779 : Blo 147793 323779 := bstep (se 1 (by rfl) ⟨242834, by rfl⟩ : syracuseStep 323779 = 485669) B485669
theorem B225491 : Blo 147793 225491 := bstep (se 1 (by rfl) ⟨169118, by rfl⟩ : syracuseStep 225491 = 338237) B338237
theorem B225521 : Blo 147793 225521 := bstep (se 2 (by rfl) ⟨84570, by rfl⟩ : syracuseStep 225521 = 169141) B169141
theorem B225539 : Blo 147793 225539 := bstep (se 1 (by rfl) ⟨169154, by rfl⟩ : syracuseStep 225539 = 338309) B338309
theorem B225569 : Blo 147793 225569 := bstep (se 2 (by rfl) ⟨84588, by rfl⟩ : syracuseStep 225569 = 169177) B169177
theorem B225587 : Blo 147793 225587 := bstep (se 1 (by rfl) ⟨169190, by rfl⟩ : syracuseStep 225587 = 338381) B338381
theorem B225617 : Blo 147793 225617 := bstep (se 2 (by rfl) ⟨84606, by rfl⟩ : syracuseStep 225617 = 169213) B169213
theorem B225635 : Blo 147793 225635 := bstep (se 1 (by rfl) ⟨169226, by rfl⟩ : syracuseStep 225635 = 338453) B338453
theorem B225665 : Blo 147793 225665 := bstep (se 2 (by rfl) ⟨84624, by rfl⟩ : syracuseStep 225665 = 169249) B169249
theorem B815501 : Blo 147793 815501 := bstep (se 3 (by rfl) ⟨152906, by rfl⟩ : syracuseStep 815501 = 305813) B305813
theorem B160147 : Blo 147793 160147 := bstep (se 1 (by rfl) ⟨120110, by rfl⟩ : syracuseStep 160147 = 240221) B240221
theorem B225683 : Blo 147793 225683 := bstep (se 1 (by rfl) ⟨169262, by rfl⟩ : syracuseStep 225683 = 338525) B338525
theorem B913841 : Blo 147793 913841 := bstep (se 2 (by rfl) ⟨342690, by rfl⟩ : syracuseStep 913841 = 685381) B685381
theorem B225713 : Blo 147793 225713 := bstep (se 2 (by rfl) ⟨84642, by rfl⟩ : syracuseStep 225713 = 169285) B169285
theorem B225731 : Blo 147793 225731 := bstep (se 1 (by rfl) ⟨169298, by rfl⟩ : syracuseStep 225731 = 338597) B338597
theorem B225761 : Blo 147793 225761 := bstep (se 2 (by rfl) ⟨84660, by rfl⟩ : syracuseStep 225761 = 169321) B169321
theorem B225779 : Blo 147793 225779 := bstep (se 1 (by rfl) ⟨169334, by rfl⟩ : syracuseStep 225779 = 338669) B338669
theorem B225809 : Blo 147793 225809 := bstep (se 2 (by rfl) ⟨84678, by rfl⟩ : syracuseStep 225809 = 169357) B169357
theorem B225827 : Blo 147793 225827 := bstep (se 1 (by rfl) ⟨169370, by rfl⟩ : syracuseStep 225827 = 338741) B338741
theorem B225857 : Blo 147793 225857 := bstep (se 2 (by rfl) ⟨84696, by rfl⟩ : syracuseStep 225857 = 169393) B169393
theorem B225875 : Blo 147793 225875 := bstep (se 1 (by rfl) ⟨169406, by rfl⟩ : syracuseStep 225875 = 338813) B338813
theorem B356977 : Blo 147793 356977 := bstep (se 2 (by rfl) ⟨133866, by rfl⟩ : syracuseStep 356977 = 267733) B267733
theorem B225905 : Blo 147793 225905 := bstep (se 2 (by rfl) ⟨84714, by rfl⟩ : syracuseStep 225905 = 169429) B169429
theorem B225923 : Blo 147793 225923 := bstep (se 1 (by rfl) ⟨169442, by rfl⟩ : syracuseStep 225923 = 338885) B338885
theorem B750221 : Blo 147793 750221 := bstep (se 3 (by rfl) ⟨140666, by rfl⟩ : syracuseStep 750221 = 281333) B281333
theorem B225953 : Blo 147793 225953 := bstep (se 2 (by rfl) ⟨84732, by rfl⟩ : syracuseStep 225953 = 169465) B169465
theorem B455341 : Blo 147793 455341 := bstep (se 3 (by rfl) ⟨85376, by rfl⟩ : syracuseStep 455341 = 170753) B170753
theorem B225971 : Blo 147793 225971 := bstep (se 1 (by rfl) ⟨169478, by rfl⟩ : syracuseStep 225971 = 338957) B338957
theorem B226001 : Blo 147793 226001 := bstep (se 2 (by rfl) ⟨84750, by rfl⟩ : syracuseStep 226001 = 169501) B169501
theorem B226003 : Blo 147793 226003 := bstep (se 1 (by rfl) ⟨169502, by rfl⟩ : syracuseStep 226003 = 339005) B339005
theorem B226019 : Blo 147793 226019 := bstep (se 1 (by rfl) ⟨169514, by rfl⟩ : syracuseStep 226019 = 339029) B339029
theorem B226049 : Blo 147793 226049 := bstep (se 2 (by rfl) ⟨84768, by rfl⟩ : syracuseStep 226049 = 169537) B169537
theorem B226067 : Blo 147793 226067 := bstep (se 1 (by rfl) ⟨169550, by rfl⟩ : syracuseStep 226067 = 339101) B339101
theorem B226097 : Blo 147793 226097 := bstep (se 2 (by rfl) ⟨84786, by rfl⟩ : syracuseStep 226097 = 169573) B169573
theorem B226115 : Blo 147793 226115 := bstep (se 1 (by rfl) ⟨169586, by rfl⟩ : syracuseStep 226115 = 339173) B339173
theorem B848717 : Blo 147793 848717 := bstep (se 3 (by rfl) ⟨159134, by rfl⟩ : syracuseStep 848717 = 318269) B318269
theorem B226145 : Blo 147793 226145 := bstep (se 2 (by rfl) ⟨84804, by rfl⟩ : syracuseStep 226145 = 169609) B169609
theorem B226163 : Blo 147793 226163 := bstep (se 1 (by rfl) ⟨169622, by rfl⟩ : syracuseStep 226163 = 339245) B339245
theorem B226193 : Blo 147793 226193 := bstep (se 2 (by rfl) ⟨84822, by rfl⟩ : syracuseStep 226193 = 169645) B169645
theorem B226211 : Blo 147793 226211 := bstep (se 1 (by rfl) ⟨169658, by rfl⟩ : syracuseStep 226211 = 339317) B339317
theorem B226241 : Blo 147793 226241 := bstep (se 2 (by rfl) ⟨84840, by rfl⟩ : syracuseStep 226241 = 169681) B169681
theorem B226259 : Blo 147793 226259 := bstep (se 1 (by rfl) ⟨169694, by rfl⟩ : syracuseStep 226259 = 339389) B339389
theorem B226289 : Blo 147793 226289 := bstep (se 2 (by rfl) ⟨84858, by rfl⟩ : syracuseStep 226289 = 169717) B169717
theorem B226307 : Blo 147793 226307 := bstep (se 1 (by rfl) ⟨169730, by rfl⟩ : syracuseStep 226307 = 339461) B339461
theorem B226337 : Blo 147793 226337 := bstep (se 2 (by rfl) ⟨84876, by rfl⟩ : syracuseStep 226337 = 169753) B169753
theorem B422957 : Blo 147793 422957 := bstep (se 3 (by rfl) ⟨79304, by rfl⟩ : syracuseStep 422957 = 158609) B158609
theorem B226355 : Blo 147793 226355 := bstep (se 1 (by rfl) ⟨169766, by rfl⟩ : syracuseStep 226355 = 339533) B339533
theorem B226385 : Blo 147793 226385 := bstep (se 2 (by rfl) ⟨84894, by rfl⟩ : syracuseStep 226385 = 169789) B169789
theorem B226403 : Blo 147793 226403 := bstep (se 1 (by rfl) ⟨169802, by rfl⟩ : syracuseStep 226403 = 339605) B339605
theorem B226433 : Blo 147793 226433 := bstep (se 2 (by rfl) ⟨84912, by rfl⟩ : syracuseStep 226433 = 169825) B169825
theorem B226451 : Blo 147793 226451 := bstep (se 1 (by rfl) ⟨169838, by rfl⟩ : syracuseStep 226451 = 339677) B339677
theorem B226481 : Blo 147793 226481 := bstep (se 2 (by rfl) ⟨84930, by rfl⟩ : syracuseStep 226481 = 169861) B169861
theorem B226499 : Blo 147793 226499 := bstep (se 1 (by rfl) ⟨169874, by rfl⟩ : syracuseStep 226499 = 339749) B339749
theorem B226529 : Blo 147793 226529 := bstep (se 2 (by rfl) ⟨84948, by rfl⟩ : syracuseStep 226529 = 169897) B169897
theorem B423139 : Blo 147793 423139 := bstep (se 1 (by rfl) ⟨317354, by rfl⟩ : syracuseStep 423139 = 634709) B634709
theorem B226547 : Blo 147793 226547 := bstep (se 1 (by rfl) ⟨169910, by rfl⟩ : syracuseStep 226547 = 339821) B339821
theorem B226577 : Blo 147793 226577 := bstep (se 2 (by rfl) ⟨84966, by rfl⟩ : syracuseStep 226577 = 169933) B169933
theorem B226595 : Blo 147793 226595 := bstep (se 1 (by rfl) ⟨169946, by rfl⟩ : syracuseStep 226595 = 339893) B339893
theorem B226625 : Blo 147793 226625 := bstep (se 2 (by rfl) ⟨84984, by rfl⟩ : syracuseStep 226625 = 169969) B169969
theorem B226643 : Blo 147793 226643 := bstep (se 1 (by rfl) ⟨169982, by rfl⟩ : syracuseStep 226643 = 339965) B339965
theorem B226673 : Blo 147793 226673 := bstep (se 2 (by rfl) ⟨85002, by rfl⟩ : syracuseStep 226673 = 170005) B170005
theorem B423299 : Blo 147793 423299 := bstep (se 1 (by rfl) ⟨317474, by rfl⟩ : syracuseStep 423299 = 634949) B634949
theorem B226691 : Blo 147793 226691 := bstep (se 1 (by rfl) ⟨170018, by rfl⟩ : syracuseStep 226691 = 340037) B340037
theorem B226721 : Blo 147793 226721 := bstep (se 2 (by rfl) ⟨85020, by rfl⟩ : syracuseStep 226721 = 170041) B170041
theorem B226739 : Blo 147793 226739 := bstep (se 1 (by rfl) ⟨170054, by rfl⟩ : syracuseStep 226739 = 340109) B340109
theorem B226769 : Blo 147793 226769 := bstep (se 2 (by rfl) ⟨85038, by rfl⟩ : syracuseStep 226769 = 170077) B170077
theorem B1799651 : Blo 147793 1799651 := bstep (se 1 (by rfl) ⟨1349738, by rfl⟩ : syracuseStep 1799651 = 2699477) B2699477
theorem B226787 : Blo 147793 226787 := bstep (se 1 (by rfl) ⟨170090, by rfl⟩ : syracuseStep 226787 = 340181) B340181
theorem B226817 : Blo 147793 226817 := bstep (se 2 (by rfl) ⟨85056, by rfl⟩ : syracuseStep 226817 = 170113) B170113
theorem B226835 : Blo 147793 226835 := bstep (se 1 (by rfl) ⟨170126, by rfl⟩ : syracuseStep 226835 = 340253) B340253
theorem B226865 : Blo 147793 226865 := bstep (se 2 (by rfl) ⟨85074, by rfl⟩ : syracuseStep 226865 = 170149) B170149
theorem B226883 : Blo 147793 226883 := bstep (se 1 (by rfl) ⟨170162, by rfl⟩ : syracuseStep 226883 = 340325) B340325
theorem B226913 : Blo 147793 226913 := bstep (se 2 (by rfl) ⟨85092, by rfl⟩ : syracuseStep 226913 = 170185) B170185
theorem B226931 : Blo 147793 226931 := bstep (se 1 (by rfl) ⟨170198, by rfl⟩ : syracuseStep 226931 = 340397) B340397
theorem B161411 : Blo 147793 161411 := bstep (se 1 (by rfl) ⟨121058, by rfl⟩ : syracuseStep 161411 = 242117) B242117
theorem B226961 : Blo 147793 226961 := bstep (se 2 (by rfl) ⟨85110, by rfl⟩ : syracuseStep 226961 = 170221) B170221
theorem B226979 : Blo 147793 226979 := bstep (se 1 (by rfl) ⟨170234, by rfl⟩ : syracuseStep 226979 = 340469) B340469
theorem B227009 : Blo 147793 227009 := bstep (se 2 (by rfl) ⟨85128, by rfl⟩ : syracuseStep 227009 = 170257) B170257
theorem B227027 : Blo 147793 227027 := bstep (se 1 (by rfl) ⟨170270, by rfl⟩ : syracuseStep 227027 = 340541) B340541
theorem B849649 : Blo 147793 849649 := bstep (se 2 (by rfl) ⟨318618, by rfl⟩ : syracuseStep 849649 = 637237) B637237
theorem B227057 : Blo 147793 227057 := bstep (se 2 (by rfl) ⟨85146, by rfl⟩ : syracuseStep 227057 = 170293) B170293
theorem B227075 : Blo 147793 227075 := bstep (se 1 (by rfl) ⟨170306, by rfl⟩ : syracuseStep 227075 = 340613) B340613
theorem B227105 : Blo 147793 227105 := bstep (se 2 (by rfl) ⟨85164, by rfl⟩ : syracuseStep 227105 = 170329) B170329
theorem B227123 : Blo 147793 227123 := bstep (se 1 (by rfl) ⟨170342, by rfl⟩ : syracuseStep 227123 = 340685) B340685
theorem B227153 : Blo 147793 227153 := bstep (se 2 (by rfl) ⟨85182, by rfl⟩ : syracuseStep 227153 = 170365) B170365
theorem B227171 : Blo 147793 227171 := bstep (se 1 (by rfl) ⟨170378, by rfl⟩ : syracuseStep 227171 = 340757) B340757
theorem B227201 : Blo 147793 227201 := bstep (se 2 (by rfl) ⟨85200, by rfl⟩ : syracuseStep 227201 = 170401) B170401
theorem B227219 : Blo 147793 227219 := bstep (se 1 (by rfl) ⟨170414, by rfl⟩ : syracuseStep 227219 = 340829) B340829
theorem B227249 : Blo 147793 227249 := bstep (se 2 (by rfl) ⟨85218, by rfl⟩ : syracuseStep 227249 = 170437) B170437
theorem B227267 : Blo 147793 227267 := bstep (se 1 (by rfl) ⟨170450, by rfl⟩ : syracuseStep 227267 = 340901) B340901
theorem B227297 : Blo 147793 227297 := bstep (se 2 (by rfl) ⟨85236, by rfl⟩ : syracuseStep 227297 = 170473) B170473
theorem B227315 : Blo 147793 227315 := bstep (se 1 (by rfl) ⟨170486, by rfl⟩ : syracuseStep 227315 = 340973) B340973
theorem B227345 : Blo 147793 227345 := bstep (se 2 (by rfl) ⟨85254, by rfl⟩ : syracuseStep 227345 = 170509) B170509
theorem B915491 : Blo 147793 915491 := bstep (se 1 (by rfl) ⟨686618, by rfl⟩ : syracuseStep 915491 = 1373237) B1373237
theorem B227363 : Blo 147793 227363 := bstep (se 1 (by rfl) ⟨170522, by rfl⟩ : syracuseStep 227363 = 341045) B341045
theorem B227393 : Blo 147793 227393 := bstep (se 2 (by rfl) ⟨85272, by rfl⟩ : syracuseStep 227393 = 170545) B170545
theorem B227411 : Blo 147793 227411 := bstep (se 1 (by rfl) ⟨170558, by rfl⟩ : syracuseStep 227411 = 341117) B341117
theorem B227441 : Blo 147793 227441 := bstep (se 2 (by rfl) ⟨85290, by rfl⟩ : syracuseStep 227441 = 170581) B170581
theorem B227459 : Blo 147793 227459 := bstep (se 1 (by rfl) ⟨170594, by rfl⟩ : syracuseStep 227459 = 341189) B341189
theorem B227489 : Blo 147793 227489 := bstep (se 2 (by rfl) ⟨85308, by rfl⟩ : syracuseStep 227489 = 170617) B170617
theorem B227507 : Blo 147793 227507 := bstep (se 1 (by rfl) ⟨170630, by rfl⟩ : syracuseStep 227507 = 341261) B341261
theorem B227537 : Blo 147793 227537 := bstep (se 2 (by rfl) ⟨85326, by rfl⟩ : syracuseStep 227537 = 170653) B170653
theorem B227555 : Blo 147793 227555 := bstep (se 1 (by rfl) ⟨170666, by rfl⟩ : syracuseStep 227555 = 341333) B341333
theorem B227585 : Blo 147793 227585 := bstep (se 2 (by rfl) ⟨85344, by rfl⟩ : syracuseStep 227585 = 170689) B170689
theorem B227603 : Blo 147793 227603 := bstep (se 1 (by rfl) ⟨170702, by rfl⟩ : syracuseStep 227603 = 341405) B341405
theorem B227633 : Blo 147793 227633 := bstep (se 2 (by rfl) ⟨85362, by rfl⟩ : syracuseStep 227633 = 170725) B170725
theorem B227651 : Blo 147793 227651 := bstep (se 1 (by rfl) ⟨170738, by rfl⟩ : syracuseStep 227651 = 341477) B341477
theorem B227681 : Blo 147793 227681 := bstep (se 2 (by rfl) ⟨85380, by rfl⟩ : syracuseStep 227681 = 170761) B170761
theorem B424369 : Blo 147793 424369 := bstep (se 2 (by rfl) ⟨159138, by rfl⟩ : syracuseStep 424369 = 318277) B318277
theorem B3013685 : Blo 147793 3013685 := bstep (se 5 (by rfl) ⟨141266, by rfl⟩ : syracuseStep 3013685 = 282533) B282533
theorem B851107 : Blo 147793 851107 := bstep (se 1 (by rfl) ⟨638330, by rfl⟩ : syracuseStep 851107 = 1276661) B1276661
theorem B228595 : Blo 147793 228595 := bstep (se 1 (by rfl) ⟨171446, by rfl⟩ : syracuseStep 228595 = 342893) B342893
theorem B949553 : Blo 147793 949553 := bstep (se 2 (by rfl) ⟨356082, by rfl⟩ : syracuseStep 949553 = 712165) B712165
theorem B949603 : Blo 147793 949603 := bstep (se 1 (by rfl) ⟨712202, by rfl⟩ : syracuseStep 949603 = 1424405) B1424405
theorem B818531 : Blo 147793 818531 := bstep (se 1 (by rfl) ⟨613898, by rfl⟩ : syracuseStep 818531 = 1227797) B1227797
theorem B1441165 : Blo 147793 1441165 := bstep (se 3 (by rfl) ⟨270218, by rfl⟩ : syracuseStep 1441165 = 540437) B540437
theorem B753137 : Blo 147793 753137 := bstep (se 2 (by rfl) ⟨282426, by rfl⟩ : syracuseStep 753137 = 564853) B564853
theorem B228883 : Blo 147793 228883 := bstep (se 1 (by rfl) ⟨171662, by rfl⟩ : syracuseStep 228883 = 343325) B343325
theorem B425645 : Blo 147793 425645 := bstep (se 3 (by rfl) ⟨79808, by rfl⟩ : syracuseStep 425645 = 159617) B159617
theorem B851633 : Blo 147793 851633 := bstep (se 2 (by rfl) ⟨319362, by rfl⟩ : syracuseStep 851633 = 638725) B638725
theorem B425827 : Blo 147793 425827 := bstep (se 1 (by rfl) ⟨319370, by rfl⟩ : syracuseStep 425827 = 638741) B638741
theorem B425873 : Blo 147793 425873 := bstep (se 2 (by rfl) ⟨159702, by rfl⟩ : syracuseStep 425873 = 319405) B319405
theorem B459059 : Blo 147793 459059 := bstep (se 1 (by rfl) ⟨344294, by rfl⟩ : syracuseStep 459059 = 688589) B688589
theorem B426329 : Blo 147793 426329 := bstep (se 2 (by rfl) ⟨159873, by rfl⟩ : syracuseStep 426329 = 319747) B319747
theorem B1278301 : Blo 147793 1278301 := bstep (se 3 (by rfl) ⟨239681, by rfl⟩ : syracuseStep 1278301 = 479363) B479363
theorem B4882837 : Blo 147793 4882837 := bstep (se 6 (by rfl) ⟨114441, by rfl⟩ : syracuseStep 4882837 = 228883) B228883
theorem B950935 : Blo 147793 950935 := bstep (se 1 (by rfl) ⟨713201, by rfl⟩ : syracuseStep 950935 = 1426403) B1426403
theorem B426647 : Blo 147793 426647 := bstep (se 1 (by rfl) ⟨319985, by rfl⟩ : syracuseStep 426647 = 639971) B639971
theorem B2196341 : Blo 147793 2196341 := bstep (se 5 (by rfl) ⟨102953, by rfl⟩ : syracuseStep 2196341 = 205907) B205907
theorem B394433 : Blo 147793 394433 := bstep (se 2 (by rfl) ⟨147912, by rfl⟩ : syracuseStep 394433 = 295825) B295825
theorem B427457 : Blo 147793 427457 := bstep (se 2 (by rfl) ⟨160296, by rfl⟩ : syracuseStep 427457 = 320593) B320593
theorem B361945 : Blo 147793 361945 := bstep (se 2 (by rfl) ⟨135729, by rfl⟩ : syracuseStep 361945 = 271459) B271459
theorem B362177 : Blo 147793 362177 := bstep (se 2 (by rfl) ⟨135816, by rfl⟩ : syracuseStep 362177 = 271633) B271633
theorem B952165 : Blo 147793 952165 := bstep (se 4 (by rfl) ⟨89265, by rfl⟩ : syracuseStep 952165 = 178531) B178531
theorem B755729 : Blo 147793 755729 := bstep (se 2 (by rfl) ⟨283398, by rfl⟩ : syracuseStep 755729 = 566797) B566797
theorem B755891 : Blo 147793 755891 := bstep (se 1 (by rfl) ⟨566918, by rfl⟩ : syracuseStep 755891 = 1133837) B1133837
theorem B362675 : Blo 147793 362675 := bstep (se 1 (by rfl) ⟨272006, by rfl⟩ : syracuseStep 362675 = 544013) B544013
theorem B919873 : Blo 147793 919873 := bstep (se 2 (by rfl) ⟨344952, by rfl⟩ : syracuseStep 919873 = 689905) B689905
theorem B723275 : Blo 147793 723275 := bstep (se 1 (by rfl) ⟨542456, by rfl⟩ : syracuseStep 723275 = 1084913) B1084913
theorem B166315 : Blo 147793 166315 := bstep (se 1 (by rfl) ⟨124736, by rfl⟩ : syracuseStep 166315 = 249473) B249473
theorem B1149389 : Blo 147793 1149389 := bstep (se 3 (by rfl) ⟨215510, by rfl⟩ : syracuseStep 1149389 = 431021) B431021
theorem B166423 : Blo 147793 166423 := bstep (se 1 (by rfl) ⟨124817, by rfl⟩ : syracuseStep 166423 = 249635) B249635
theorem B166603 : Blo 147793 166603 := bstep (se 1 (by rfl) ⟨124952, by rfl⟩ : syracuseStep 166603 = 249905) B249905
theorem B461591 : Blo 147793 461591 := bstep (se 1 (by rfl) ⟨346193, by rfl⟩ : syracuseStep 461591 = 692387) B692387
theorem B166711 : Blo 147793 166711 := bstep (se 1 (by rfl) ⟨125033, by rfl⟩ : syracuseStep 166711 = 250067) B250067
theorem B1149875 : Blo 147793 1149875 := bstep (se 1 (by rfl) ⟨862406, by rfl⟩ : syracuseStep 1149875 = 1724813) B1724813
theorem B166891 : Blo 147793 166891 := bstep (se 1 (by rfl) ⟨125168, by rfl⟩ : syracuseStep 166891 = 250337) B250337
theorem B429131 : Blo 147793 429131 := bstep (se 1 (by rfl) ⟨321848, by rfl⟩ : syracuseStep 429131 = 643697) B643697
theorem B166999 : Blo 147793 166999 := bstep (se 1 (by rfl) ⟨125249, by rfl⟩ : syracuseStep 166999 = 250499) B250499
theorem B691289 : Blo 147793 691289 := bstep (se 2 (by rfl) ⟨259233, by rfl⟩ : syracuseStep 691289 = 518467) B518467
theorem B167179 : Blo 147793 167179 := bstep (se 1 (by rfl) ⟨125384, by rfl⟩ : syracuseStep 167179 = 250769) B250769
theorem B167287 : Blo 147793 167287 := bstep (se 1 (by rfl) ⟨125465, by rfl⟩ : syracuseStep 167287 = 250931) B250931
theorem B495065 : Blo 147793 495065 := bstep (se 2 (by rfl) ⟨185649, by rfl⟩ : syracuseStep 495065 = 371299) B371299
theorem B167467 : Blo 147793 167467 := bstep (se 1 (by rfl) ⟨125600, by rfl⟩ : syracuseStep 167467 = 251201) B251201
theorem B167575 : Blo 147793 167575 := bstep (se 1 (by rfl) ⟨125681, by rfl⟩ : syracuseStep 167575 = 251363) B251363
theorem B167755 : Blo 147793 167755 := bstep (se 1 (by rfl) ⟨125816, by rfl⟩ : syracuseStep 167755 = 251633) B251633
theorem B167863 : Blo 147793 167863 := bstep (se 1 (by rfl) ⟨125897, by rfl⟩ : syracuseStep 167863 = 251795) B251795
theorem B692171 : Blo 147793 692171 := bstep (se 1 (by rfl) ⟨519128, by rfl⟩ : syracuseStep 692171 = 1038257) B1038257
theorem B757835 : Blo 147793 757835 := bstep (se 1 (by rfl) ⟨568376, by rfl⟩ : syracuseStep 757835 = 1136753) B1136753
theorem B168043 : Blo 147793 168043 := bstep (se 1 (by rfl) ⟨126032, by rfl⟩ : syracuseStep 168043 = 252065) B252065
theorem B1380503 : Blo 147793 1380503 := bstep (se 1 (by rfl) ⟨1035377, by rfl⟩ : syracuseStep 1380503 = 2070755) B2070755
theorem B168151 : Blo 147793 168151 := bstep (se 1 (by rfl) ⟨126113, by rfl⟩ : syracuseStep 168151 = 252227) B252227
theorem B430429 : Blo 147793 430429 := bstep (se 3 (by rfl) ⟨80705, by rfl⟩ : syracuseStep 430429 = 161411) B161411
theorem B1151333 : Blo 147793 1151333 := bstep (se 4 (by rfl) ⟨107937, by rfl⟩ : syracuseStep 1151333 = 215875) B215875
theorem B168331 : Blo 147793 168331 := bstep (se 1 (by rfl) ⟨126248, by rfl⟩ : syracuseStep 168331 = 252497) B252497
theorem B168439 : Blo 147793 168439 := bstep (se 1 (by rfl) ⟨126329, by rfl⟩ : syracuseStep 168439 = 252659) B252659
theorem B168619 : Blo 147793 168619 := bstep (se 1 (by rfl) ⟨126464, by rfl⟩ : syracuseStep 168619 = 252929) B252929
theorem B430771 : Blo 147793 430771 := bstep (se 1 (by rfl) ⟨323078, by rfl⟩ : syracuseStep 430771 = 646157) B646157
theorem B561923 : Blo 147793 561923 := bstep (se 1 (by rfl) ⟨421442, by rfl⟩ : syracuseStep 561923 = 842885) B842885
theorem B561937 : Blo 147793 561937 := bstep (se 2 (by rfl) ⟨210726, by rfl⟩ : syracuseStep 561937 = 421453) B421453
theorem B332567 : Blo 147793 332567 := bstep (se 1 (by rfl) ⟨249425, by rfl⟩ : syracuseStep 332567 = 498851) B498851
theorem B168727 : Blo 147793 168727 := bstep (se 1 (by rfl) ⟨126545, by rfl⟩ : syracuseStep 168727 = 253091) B253091
theorem B4854593 : Blo 147793 4854593 := bstep (se 2 (by rfl) ⟨1820472, by rfl⟩ : syracuseStep 4854593 = 3640945) B3640945
theorem B1151819 : Blo 147793 1151819 := bstep (se 1 (by rfl) ⟨863864, by rfl⟩ : syracuseStep 1151819 = 1727729) B1727729
theorem B332747 : Blo 147793 332747 := bstep (se 1 (by rfl) ⟨249560, by rfl⟩ : syracuseStep 332747 = 499121) B499121
theorem B168907 : Blo 147793 168907 := bstep (se 1 (by rfl) ⟨126680, by rfl⟩ : syracuseStep 168907 = 253361) B253361
theorem B332801 : Blo 147793 332801 := bstep (se 2 (by rfl) ⟨124800, by rfl⟩ : syracuseStep 332801 = 249601) B249601
theorem B169015 : Blo 147793 169015 := bstep (se 1 (by rfl) ⟨126761, by rfl⟩ : syracuseStep 169015 = 253523) B253523
theorem B562241 : Blo 147793 562241 := bstep (se 2 (by rfl) ⟨210840, by rfl⟩ : syracuseStep 562241 = 421681) B421681
theorem B365771 : Blo 147793 365771 := bstep (se 1 (by rfl) ⟨274328, by rfl⟩ : syracuseStep 365771 = 548657) B548657
theorem B333017 : Blo 147793 333017 := bstep (se 2 (by rfl) ⟨124881, by rfl⟩ : syracuseStep 333017 = 249763) B249763
theorem B169195 : Blo 147793 169195 := bstep (se 1 (by rfl) ⟨126896, by rfl⟩ : syracuseStep 169195 = 253793) B253793
theorem B333107 : Blo 147793 333107 := bstep (se 1 (by rfl) ⟨249830, by rfl⟩ : syracuseStep 333107 = 499661) B499661
theorem B333143 : Blo 147793 333143 := bstep (se 1 (by rfl) ⟨249857, by rfl⟩ : syracuseStep 333143 = 499715) B499715
theorem B169303 : Blo 147793 169303 := bstep (se 1 (by rfl) ⟨126977, by rfl⟩ : syracuseStep 169303 = 253955) B253955
theorem B1086871 : Blo 147793 1086871 := bstep (se 1 (by rfl) ⟨815153, by rfl⟩ : syracuseStep 1086871 = 1630307) B1630307
theorem B333323 : Blo 147793 333323 := bstep (se 1 (by rfl) ⟨249992, by rfl⟩ : syracuseStep 333323 = 499985) B499985
theorem B169483 : Blo 147793 169483 := bstep (se 1 (by rfl) ⟨127112, by rfl⟩ : syracuseStep 169483 = 254225) B254225
theorem B333377 : Blo 147793 333377 := bstep (se 2 (by rfl) ⟨125016, by rfl⟩ : syracuseStep 333377 = 250033) B250033
theorem B431705 : Blo 147793 431705 := bstep (se 2 (by rfl) ⟨161889, by rfl⟩ : syracuseStep 431705 = 323779) B323779
theorem B169591 : Blo 147793 169591 := bstep (se 1 (by rfl) ⟨127193, by rfl⟩ : syracuseStep 169591 = 254387) B254387
theorem B562909 : Blo 147793 562909 := bstep (se 3 (by rfl) ⟨105545, by rfl⟩ : syracuseStep 562909 = 211091) B211091
theorem B333593 : Blo 147793 333593 := bstep (se 2 (by rfl) ⟨125097, by rfl⟩ : syracuseStep 333593 = 250195) B250195
theorem B169771 : Blo 147793 169771 := bstep (se 1 (by rfl) ⟨127328, by rfl⟩ : syracuseStep 169771 = 254657) B254657
theorem B1054529 : Blo 147793 1054529 := bstep (se 2 (by rfl) ⟨395448, by rfl⟩ : syracuseStep 1054529 = 790897) B790897
theorem B759617 : Blo 147793 759617 := bstep (se 2 (by rfl) ⟨284856, by rfl⟩ : syracuseStep 759617 = 569713) B569713
theorem B333683 : Blo 147793 333683 := bstep (se 1 (by rfl) ⟨250262, by rfl⟩ : syracuseStep 333683 = 500525) B500525
theorem B333719 : Blo 147793 333719 := bstep (se 1 (by rfl) ⟨250289, by rfl⟩ : syracuseStep 333719 = 500579) B500579
theorem B169879 : Blo 147793 169879 := bstep (se 1 (by rfl) ⟨127409, by rfl⟩ : syracuseStep 169879 = 254819) B254819
theorem B333899 : Blo 147793 333899 := bstep (se 1 (by rfl) ⟨250424, by rfl⟩ : syracuseStep 333899 = 500849) B500849
theorem B170059 : Blo 147793 170059 := bstep (se 1 (by rfl) ⟨127544, by rfl⟩ : syracuseStep 170059 = 255089) B255089
theorem B333953 : Blo 147793 333953 := bstep (se 2 (by rfl) ⟨125232, by rfl⟩ : syracuseStep 333953 = 250465) B250465
theorem B170167 : Blo 147793 170167 := bstep (se 1 (by rfl) ⟨127625, by rfl⟩ : syracuseStep 170167 = 255251) B255251
theorem B301337 : Blo 147793 301337 := bstep (se 2 (by rfl) ⟨113001, by rfl⟩ : syracuseStep 301337 = 226003) B226003
theorem B334169 : Blo 147793 334169 := bstep (se 2 (by rfl) ⟨125313, by rfl⟩ : syracuseStep 334169 = 250627) B250627
theorem B170347 : Blo 147793 170347 := bstep (se 1 (by rfl) ⟨127760, by rfl⟩ : syracuseStep 170347 = 255521) B255521
theorem B2038193 : Blo 147793 2038193 := bstep (se 2 (by rfl) ⟨764322, by rfl⟩ : syracuseStep 2038193 = 1528645) B1528645
theorem B334259 : Blo 147793 334259 := bstep (se 1 (by rfl) ⟨250694, by rfl⟩ : syracuseStep 334259 = 501389) B501389
theorem B334295 : Blo 147793 334295 := bstep (se 1 (by rfl) ⟨250721, by rfl⟩ : syracuseStep 334295 = 501443) B501443
theorem B170455 : Blo 147793 170455 := bstep (se 1 (by rfl) ⟨127841, by rfl⟩ : syracuseStep 170455 = 255683) B255683
theorem B334475 : Blo 147793 334475 := bstep (se 1 (by rfl) ⟨250856, by rfl⟩ : syracuseStep 334475 = 501713) B501713
theorem B170635 : Blo 147793 170635 := bstep (se 1 (by rfl) ⟨127976, by rfl⟩ : syracuseStep 170635 = 255953) B255953
theorem B334529 : Blo 147793 334529 := bstep (se 2 (by rfl) ⟨125448, by rfl⟩ : syracuseStep 334529 = 250897) B250897
theorem B170743 : Blo 147793 170743 := bstep (se 1 (by rfl) ⟨128057, by rfl⟩ : syracuseStep 170743 = 256115) B256115
theorem B5315381 : Blo 147793 5315381 := bstep (se 5 (by rfl) ⟨249158, by rfl⟩ : syracuseStep 5315381 = 498317) B498317
theorem B334745 : Blo 147793 334745 := bstep (se 2 (by rfl) ⟨125529, by rfl⟩ : syracuseStep 334745 = 251059) B251059
theorem B564185 : Blo 147793 564185 := bstep (se 2 (by rfl) ⟨211569, by rfl⟩ : syracuseStep 564185 = 423139) B423139
theorem B498649 : Blo 147793 498649 := bstep (se 2 (by rfl) ⟨186993, by rfl⟩ : syracuseStep 498649 = 373987) B373987
theorem B334835 : Blo 147793 334835 := bstep (se 1 (by rfl) ⟨251126, by rfl⟩ : syracuseStep 334835 = 502253) B502253
theorem B334871 : Blo 147793 334871 := bstep (se 1 (by rfl) ⟨251153, by rfl⟩ : syracuseStep 334871 = 502307) B502307
theorem B335051 : Blo 147793 335051 := bstep (se 1 (by rfl) ⟨251288, by rfl⟩ : syracuseStep 335051 = 502577) B502577
theorem B498905 : Blo 147793 498905 := bstep (se 2 (by rfl) ⟨187089, by rfl⟩ : syracuseStep 498905 = 374179) B374179
theorem B335105 : Blo 147793 335105 := bstep (se 2 (by rfl) ⟨125664, by rfl⟩ : syracuseStep 335105 = 251329) B251329
theorem B335321 : Blo 147793 335321 := bstep (se 2 (by rfl) ⟨125745, by rfl⟩ : syracuseStep 335321 = 251491) B251491
theorem B728621 : Blo 147793 728621 := bstep (se 3 (by rfl) ⟨136616, by rfl⟩ : syracuseStep 728621 = 273233) B273233
theorem B335411 : Blo 147793 335411 := bstep (se 1 (by rfl) ⟨251558, by rfl⟩ : syracuseStep 335411 = 503117) B503117
theorem B1711691 : Blo 147793 1711691 := bstep (se 1 (by rfl) ⟨1283768, by rfl⟩ : syracuseStep 1711691 = 2567537) B2567537
theorem B335447 : Blo 147793 335447 := bstep (se 1 (by rfl) ⟨251585, by rfl⟩ : syracuseStep 335447 = 503171) B503171
theorem B2301571 : Blo 147793 2301571 := bstep (se 1 (by rfl) ⟨1726178, by rfl⟩ : syracuseStep 2301571 = 3452357) B3452357
theorem B761561 : Blo 147793 761561 := bstep (se 2 (by rfl) ⟨285585, by rfl⟩ : syracuseStep 761561 = 571171) B571171
theorem B335627 : Blo 147793 335627 := bstep (se 1 (by rfl) ⟨251720, by rfl⟩ : syracuseStep 335627 = 503441) B503441
theorem B335681 : Blo 147793 335681 := bstep (se 2 (by rfl) ⟨125880, by rfl⟩ : syracuseStep 335681 = 251761) B251761
theorem B270155 : Blo 147793 270155 := bstep (se 1 (by rfl) ⟨202616, by rfl⟩ : syracuseStep 270155 = 405233) B405233
theorem B499607 : Blo 147793 499607 := bstep (se 1 (by rfl) ⟨374705, by rfl⟩ : syracuseStep 499607 = 749411) B749411
theorem B204697 : Blo 147793 204697 := bstep (se 2 (by rfl) ⟨76761, by rfl⟩ : syracuseStep 204697 = 153523) B153523
theorem B270283 : Blo 147793 270283 := bstep (se 1 (by rfl) ⟨202712, by rfl⟩ : syracuseStep 270283 = 405425) B405425
theorem B237529 : Blo 147793 237529 := bstep (se 2 (by rfl) ⟨89073, by rfl⟩ : syracuseStep 237529 = 178147) B178147
theorem B335897 : Blo 147793 335897 := bstep (se 2 (by rfl) ⟨125961, by rfl⟩ : syracuseStep 335897 = 251923) B251923
theorem B335987 : Blo 147793 335987 := bstep (se 1 (by rfl) ⟨251990, by rfl⟩ : syracuseStep 335987 = 503981) B503981
theorem B5218445 : Blo 147793 5218445 := bstep (se 3 (by rfl) ⟨978458, by rfl⟩ : syracuseStep 5218445 = 1956917) B1956917
theorem B336023 : Blo 147793 336023 := bstep (se 1 (by rfl) ⟨252017, by rfl⟩ : syracuseStep 336023 = 504035) B504035
theorem B336203 : Blo 147793 336203 := bstep (se 1 (by rfl) ⟨252152, by rfl⟩ : syracuseStep 336203 = 504305) B504305
theorem B336257 : Blo 147793 336257 := bstep (se 2 (by rfl) ⟨126096, by rfl⟩ : syracuseStep 336257 = 252193) B252193
theorem B500147 : Blo 147793 500147 := bstep (se 1 (by rfl) ⟨375110, by rfl⟩ : syracuseStep 500147 = 750221) B750221
theorem B565811 : Blo 147793 565811 := bstep (se 1 (by rfl) ⟨424358, by rfl⟩ : syracuseStep 565811 = 848717) B848717
theorem B565825 : Blo 147793 565825 := bstep (se 2 (by rfl) ⟨212184, by rfl⟩ : syracuseStep 565825 = 424369) B424369
theorem B336473 : Blo 147793 336473 := bstep (se 2 (by rfl) ⟨126177, by rfl⟩ : syracuseStep 336473 = 252355) B252355
theorem B336563 : Blo 147793 336563 := bstep (se 1 (by rfl) ⟨252422, by rfl⟩ : syracuseStep 336563 = 504845) B504845
theorem B500417 : Blo 147793 500417 := bstep (se 2 (by rfl) ⟨187656, by rfl⟩ : syracuseStep 500417 = 375313) B375313
theorem B336599 : Blo 147793 336599 := bstep (se 1 (by rfl) ⟨252449, by rfl⟩ : syracuseStep 336599 = 504899) B504899
theorem B336779 : Blo 147793 336779 := bstep (se 1 (by rfl) ⟨252584, by rfl⟩ : syracuseStep 336779 = 505169) B505169
theorem B336833 : Blo 147793 336833 := bstep (se 2 (by rfl) ⟨126312, by rfl⟩ : syracuseStep 336833 = 252625) B252625
theorem B337049 : Blo 147793 337049 := bstep (se 2 (by rfl) ⟨126393, by rfl⟩ : syracuseStep 337049 = 252787) B252787
theorem B500957 : Blo 147793 500957 := bstep (se 3 (by rfl) ⟨93929, by rfl⟩ : syracuseStep 500957 = 187859) B187859
theorem B337139 : Blo 147793 337139 := bstep (se 1 (by rfl) ⟨252854, by rfl⟩ : syracuseStep 337139 = 505709) B505709
theorem B271603 : Blo 147793 271603 := bstep (se 1 (by rfl) ⟨203702, by rfl⟩ : syracuseStep 271603 = 407405) B407405
theorem B337175 : Blo 147793 337175 := bstep (se 1 (by rfl) ⟨252881, by rfl⟩ : syracuseStep 337175 = 505763) B505763
theorem B763181 : Blo 147793 763181 := bstep (se 3 (by rfl) ⟨143096, by rfl⟩ : syracuseStep 763181 = 286193) B286193
theorem B271769 : Blo 147793 271769 := bstep (se 2 (by rfl) ⟨101913, by rfl⟩ : syracuseStep 271769 = 203827) B203827
theorem B337355 : Blo 147793 337355 := bstep (se 1 (by rfl) ⟨253016, by rfl⟩ : syracuseStep 337355 = 506033) B506033
theorem B337409 : Blo 147793 337409 := bstep (se 2 (by rfl) ⟨126528, by rfl⟩ : syracuseStep 337409 = 253057) B253057
theorem B304793 : Blo 147793 304793 := bstep (se 2 (by rfl) ⟨114297, by rfl⟩ : syracuseStep 304793 = 228595) B228595
theorem B534209 : Blo 147793 534209 := bstep (se 2 (by rfl) ⟨200328, by rfl⟩ : syracuseStep 534209 = 400657) B400657
theorem B337625 : Blo 147793 337625 := bstep (se 2 (by rfl) ⟨126609, by rfl⟩ : syracuseStep 337625 = 253219) B253219
theorem B337715 : Blo 147793 337715 := bstep (se 1 (by rfl) ⟨253286, by rfl⟩ : syracuseStep 337715 = 506573) B506573
theorem B272179 : Blo 147793 272179 := bstep (se 1 (by rfl) ⟨204134, by rfl⟩ : syracuseStep 272179 = 408269) B408269
theorem B337751 : Blo 147793 337751 := bstep (se 1 (by rfl) ⟨253313, by rfl⟩ : syracuseStep 337751 = 506627) B506627
theorem B337931 : Blo 147793 337931 := bstep (se 1 (by rfl) ⟨253448, by rfl⟩ : syracuseStep 337931 = 506897) B506897
theorem B534545 : Blo 147793 534545 := bstep (se 2 (by rfl) ⟨200454, by rfl⟩ : syracuseStep 534545 = 400909) B400909
theorem B2009123 : Blo 147793 2009123 := bstep (se 1 (by rfl) ⟨1506842, by rfl⟩ : syracuseStep 2009123 = 3013685) B3013685
theorem B337985 : Blo 147793 337985 := bstep (se 2 (by rfl) ⟨126744, by rfl⟩ : syracuseStep 337985 = 253489) B253489
theorem B3582133 : Blo 147793 3582133 := bstep (se 5 (by rfl) ⟨167912, by rfl⟩ : syracuseStep 3582133 = 335825) B335825
theorem B633035 : Blo 147793 633035 := bstep (se 1 (by rfl) ⟨474776, by rfl⟩ : syracuseStep 633035 = 949553) B949553
theorem B338201 : Blo 147793 338201 := bstep (se 2 (by rfl) ⟨126825, by rfl⟩ : syracuseStep 338201 = 253651) B253651
theorem B502091 : Blo 147793 502091 := bstep (se 1 (by rfl) ⟨376568, by rfl⟩ : syracuseStep 502091 = 753137) B753137
theorem B338291 : Blo 147793 338291 := bstep (se 1 (by rfl) ⟨253718, by rfl⟩ : syracuseStep 338291 = 507437) B507437
theorem B338327 : Blo 147793 338327 := bstep (se 1 (by rfl) ⟨253745, by rfl⟩ : syracuseStep 338327 = 507491) B507491
theorem B567755 : Blo 147793 567755 := bstep (se 1 (by rfl) ⟨425816, by rfl⟩ : syracuseStep 567755 = 851633) B851633
theorem B567769 : Blo 147793 567769 := bstep (se 2 (by rfl) ⟨212913, by rfl⟩ : syracuseStep 567769 = 425827) B425827
theorem B338507 : Blo 147793 338507 := bstep (se 1 (by rfl) ⟨253880, by rfl⟩ : syracuseStep 338507 = 507761) B507761
theorem B502361 : Blo 147793 502361 := bstep (se 2 (by rfl) ⟨188385, by rfl⟩ : syracuseStep 502361 = 376771) B376771
theorem B338561 : Blo 147793 338561 := bstep (se 2 (by rfl) ⟨126960, by rfl⟩ : syracuseStep 338561 = 253921) B253921
theorem B338777 : Blo 147793 338777 := bstep (se 2 (by rfl) ⟨127041, by rfl⟩ : syracuseStep 338777 = 254083) B254083
theorem B338867 : Blo 147793 338867 := bstep (se 1 (by rfl) ⟨254150, by rfl⟩ : syracuseStep 338867 = 508301) B508301
theorem B338903 : Blo 147793 338903 := bstep (se 1 (by rfl) ⟨254177, by rfl⟩ : syracuseStep 338903 = 508355) B508355
theorem B863297 : Blo 147793 863297 := bstep (se 2 (by rfl) ⟨323736, by rfl⟩ : syracuseStep 863297 = 647473) B647473
theorem B339083 : Blo 147793 339083 := bstep (se 1 (by rfl) ⟨254312, by rfl⟩ : syracuseStep 339083 = 508625) B508625
theorem B535697 : Blo 147793 535697 := bstep (se 2 (by rfl) ⟨200886, by rfl⟩ : syracuseStep 535697 = 401773) B401773
theorem B339137 : Blo 147793 339137 := bstep (se 2 (by rfl) ⟨127176, by rfl⟩ : syracuseStep 339137 = 254353) B254353
theorem B339223 : Blo 147793 339223 := bstep (se 1 (by rfl) ⟨254417, by rfl⟩ : syracuseStep 339223 = 508835) B508835
theorem B503063 : Blo 147793 503063 := bstep (se 1 (by rfl) ⟨377297, by rfl⟩ : syracuseStep 503063 = 754595) B754595
theorem B404801 : Blo 147793 404801 := bstep (se 2 (by rfl) ⟨151800, by rfl⟩ : syracuseStep 404801 = 303601) B303601
theorem B339287 : Blo 147793 339287 := bstep (se 1 (by rfl) ⟨254465, by rfl⟩ : syracuseStep 339287 = 508931) B508931
theorem B568727 : Blo 147793 568727 := bstep (se 1 (by rfl) ⟨426545, by rfl⟩ : syracuseStep 568727 = 853091) B853091
theorem B208279 : Blo 147793 208279 := bstep (se 1 (by rfl) ⟨156209, by rfl⟩ : syracuseStep 208279 = 312419) B312419
theorem B339353 : Blo 147793 339353 := bstep (se 2 (by rfl) ⟨127257, by rfl⟩ : syracuseStep 339353 = 254515) B254515
theorem B339443 : Blo 147793 339443 := bstep (se 1 (by rfl) ⟨254582, by rfl⟩ : syracuseStep 339443 = 509165) B509165
theorem B339479 : Blo 147793 339479 := bstep (se 1 (by rfl) ⟨254609, by rfl⟩ : syracuseStep 339479 = 509219) B509219
theorem B503347 : Blo 147793 503347 := bstep (se 1 (by rfl) ⟨377510, by rfl⟩ : syracuseStep 503347 = 755021) B755021
theorem B339659 : Blo 147793 339659 := bstep (se 1 (by rfl) ⟨254744, by rfl⟩ : syracuseStep 339659 = 509489) B509489
theorem B339713 : Blo 147793 339713 := bstep (se 2 (by rfl) ⟨127392, by rfl⟩ : syracuseStep 339713 = 254785) B254785
theorem B634675 : Blo 147793 634675 := bstep (se 1 (by rfl) ⟨476006, by rfl⟩ : syracuseStep 634675 = 952013) B952013
theorem B503603 : Blo 147793 503603 := bstep (se 1 (by rfl) ⟨377702, by rfl⟩ : syracuseStep 503603 = 755405) B755405
theorem B339929 : Blo 147793 339929 := bstep (se 2 (by rfl) ⟨127473, by rfl⟩ : syracuseStep 339929 = 254947) B254947
theorem B340019 : Blo 147793 340019 := bstep (se 1 (by rfl) ⟨255014, by rfl⟩ : syracuseStep 340019 = 510029) B510029
theorem B503873 : Blo 147793 503873 := bstep (se 2 (by rfl) ⟨188952, by rfl⟩ : syracuseStep 503873 = 377905) B377905
theorem B340055 : Blo 147793 340055 := bstep (se 1 (by rfl) ⟨255041, by rfl⟩ : syracuseStep 340055 = 510083) B510083
theorem B340235 : Blo 147793 340235 := bstep (se 1 (by rfl) ⟨255176, by rfl⟩ : syracuseStep 340235 = 510353) B510353
theorem B340289 : Blo 147793 340289 := bstep (se 2 (by rfl) ⟨127608, by rfl⟩ : syracuseStep 340289 = 255217) B255217
theorem B536921 : Blo 147793 536921 := bstep (se 2 (by rfl) ⟨201345, by rfl⟩ : syracuseStep 536921 = 402691) B402691
theorem B536977 : Blo 147793 536977 := bstep (se 2 (by rfl) ⟨201366, by rfl⟩ : syracuseStep 536977 = 402733) B402733
theorem B635309 : Blo 147793 635309 := bstep (se 3 (by rfl) ⟨119120, by rfl⟩ : syracuseStep 635309 = 238241) B238241
theorem B340505 : Blo 147793 340505 := bstep (se 2 (by rfl) ⟨127689, by rfl⟩ : syracuseStep 340505 = 255379) B255379
theorem B504413 : Blo 147793 504413 := bstep (se 3 (by rfl) ⟨94577, by rfl⟩ : syracuseStep 504413 = 189155) B189155
theorem B340595 : Blo 147793 340595 := bstep (se 1 (by rfl) ⟨255446, by rfl⟩ : syracuseStep 340595 = 510893) B510893
theorem B569987 : Blo 147793 569987 := bstep (se 1 (by rfl) ⟨427490, by rfl⟩ : syracuseStep 569987 = 854981) B854981
theorem B340631 : Blo 147793 340631 := bstep (se 1 (by rfl) ⟨255473, by rfl⟩ : syracuseStep 340631 = 510947) B510947
theorem B275251 : Blo 147793 275251 := bstep (se 1 (by rfl) ⟨206438, by rfl⟩ : syracuseStep 275251 = 412877) B412877
theorem B340811 : Blo 147793 340811 := bstep (se 1 (by rfl) ⟨255608, by rfl⟩ : syracuseStep 340811 = 511217) B511217
theorem B340865 : Blo 147793 340865 := bstep (se 2 (by rfl) ⟨127824, by rfl⟩ : syracuseStep 340865 = 255649) B255649
theorem B406475 : Blo 147793 406475 := bstep (se 1 (by rfl) ⟨304856, by rfl⟩ : syracuseStep 406475 = 609713) B609713
theorem B341081 : Blo 147793 341081 := bstep (se 2 (by rfl) ⟨127905, by rfl⟩ : syracuseStep 341081 = 255811) B255811
theorem B767069 : Blo 147793 767069 := bstep (se 3 (by rfl) ⟨143825, by rfl⟩ : syracuseStep 767069 = 287651) B287651
theorem B341171 : Blo 147793 341171 := bstep (se 1 (by rfl) ⟨255878, by rfl⟩ : syracuseStep 341171 = 511757) B511757
theorem B341207 : Blo 147793 341207 := bstep (se 1 (by rfl) ⟨255905, by rfl⟩ : syracuseStep 341207 = 511811) B511811
theorem B341387 : Blo 147793 341387 := bstep (se 1 (by rfl) ⟨256040, by rfl⟩ : syracuseStep 341387 = 512081) B512081
theorem B1291697 : Blo 147793 1291697 := bstep (se 2 (by rfl) ⟨484386, by rfl⟩ : syracuseStep 1291697 = 968773) B968773
theorem B1553843 : Blo 147793 1553843 := bstep (se 1 (by rfl) ⟨1165382, by rfl⟩ : syracuseStep 1553843 = 2330765) B2330765
theorem B341441 : Blo 147793 341441 := bstep (se 2 (by rfl) ⟨128040, by rfl⟩ : syracuseStep 341441 = 256081) B256081
theorem B964057 : Blo 147793 964057 := bstep (se 2 (by rfl) ⟨361521, by rfl⟩ : syracuseStep 964057 = 723043) B723043
theorem B538163 : Blo 147793 538163 := bstep (se 1 (by rfl) ⟨403622, by rfl⟩ : syracuseStep 538163 = 807245) B807245
theorem B505547 : Blo 147793 505547 := bstep (se 1 (by rfl) ⟨379160, by rfl⟩ : syracuseStep 505547 = 758321) B758321
theorem B210647 : Blo 147793 210647 := bstep (se 1 (by rfl) ⟨157985, by rfl⟩ : syracuseStep 210647 = 315971) B315971
theorem B2176885 : Blo 147793 2176885 := bstep (se 5 (by rfl) ⟨102041, by rfl⟩ : syracuseStep 2176885 = 204083) B204083
theorem B505817 : Blo 147793 505817 := bstep (se 2 (by rfl) ⟨189681, by rfl⟩ : syracuseStep 505817 = 379363) B379363
theorem B374807 : Blo 147793 374807 := bstep (se 1 (by rfl) ⟨281105, by rfl⟩ : syracuseStep 374807 = 562211) B562211
theorem B964673 : Blo 147793 964673 := bstep (se 2 (by rfl) ⟨361752, by rfl⟩ : syracuseStep 964673 = 723505) B723505
theorem B1292381 : Blo 147793 1292381 := bstep (se 3 (by rfl) ⟨242321, by rfl⟩ : syracuseStep 1292381 = 484643) B484643
theorem B7485965 : Blo 147793 7485965 := bstep (se 3 (by rfl) ⟨1403618, by rfl⟩ : syracuseStep 7485965 = 2807237) B2807237
theorem B1128977 : Blo 147793 1128977 := bstep (se 2 (by rfl) ⟨423366, by rfl⟩ : syracuseStep 1128977 = 846733) B846733
theorem B1161745 : Blo 147793 1161745 := bstep (se 2 (by rfl) ⟨435654, by rfl⟩ : syracuseStep 1161745 = 871309) B871309
theorem B735875 : Blo 147793 735875 := bstep (se 1 (by rfl) ⟨551906, by rfl⟩ : syracuseStep 735875 = 1103813) B1103813
theorem B506519 : Blo 147793 506519 := bstep (se 1 (by rfl) ⟨379889, by rfl⟩ : syracuseStep 506519 = 759779) B759779
theorem B375475 : Blo 147793 375475 := bstep (se 1 (by rfl) ⟨281606, by rfl⟩ : syracuseStep 375475 = 563213) B563213
theorem B604945 : Blo 147793 604945 := bstep (se 2 (by rfl) ⟨226854, by rfl⟩ : syracuseStep 604945 = 453709) B453709
theorem B375617 : Blo 147793 375617 := bstep (se 2 (by rfl) ⟨140856, by rfl⟩ : syracuseStep 375617 = 281713) B281713
theorem B474187 : Blo 147793 474187 := bstep (se 1 (by rfl) ⟨355640, by rfl⟩ : syracuseStep 474187 = 711281) B711281
theorem B507059 : Blo 147793 507059 := bstep (se 1 (by rfl) ⟨380294, by rfl⟩ : syracuseStep 507059 = 760589) B760589
theorem B474329 : Blo 147793 474329 := bstep (se 2 (by rfl) ⟨177873, by rfl⟩ : syracuseStep 474329 = 355747) B355747
theorem B605515 : Blo 147793 605515 := bstep (se 1 (by rfl) ⟨454136, by rfl⟩ : syracuseStep 605515 = 908273) B908273
theorem B4078997 : Blo 147793 4078997 := bstep (se 6 (by rfl) ⟨95601, by rfl⟩ : syracuseStep 4078997 = 191203) B191203
theorem B507329 : Blo 147793 507329 := bstep (se 2 (by rfl) ⟨190248, by rfl⟩ : syracuseStep 507329 = 380497) B380497
theorem B605657 : Blo 147793 605657 := bstep (se 2 (by rfl) ⟨227121, by rfl⟩ : syracuseStep 605657 = 454243) B454243
theorem B540121 : Blo 147793 540121 := bstep (se 2 (by rfl) ⟨202545, by rfl⟩ : syracuseStep 540121 = 405091) B405091
theorem B605789 : Blo 147793 605789 := bstep (se 3 (by rfl) ⟨113585, by rfl⟩ : syracuseStep 605789 = 227171) B227171
theorem B343667 : Blo 147793 343667 := bstep (se 1 (by rfl) ⟨257750, by rfl⟩ : syracuseStep 343667 = 515501) B515501
theorem B573101 : Blo 147793 573101 := bstep (se 3 (by rfl) ⟨107456, by rfl⟩ : syracuseStep 573101 = 214913) B214913
theorem B179915 : Blo 147793 179915 := bstep (se 1 (by rfl) ⟨134936, by rfl⟩ : syracuseStep 179915 = 269873) B269873
theorem B507869 : Blo 147793 507869 := bstep (se 3 (by rfl) ⟨95225, by rfl⟩ : syracuseStep 507869 = 190451) B190451
theorem B638999 : Blo 147793 638999 := bstep (se 1 (by rfl) ⟨479249, by rfl⟩ : syracuseStep 638999 = 958499) B958499
theorem B376883 : Blo 147793 376883 := bstep (se 1 (by rfl) ⟨282662, by rfl⟩ : syracuseStep 376883 = 565325) B565325
theorem B1425559 : Blo 147793 1425559 := bstep (se 1 (by rfl) ⟨1069169, by rfl⟩ : syracuseStep 1425559 = 2138339) B2138339
theorem B147799 : Blo 147793 147799 := bstep (se 1 (by rfl) ⟨110849, by rfl⟩ : syracuseStep 147799 = 221699) B221699
theorem B147819 : Blo 147793 147819 := bstep (se 1 (by rfl) ⟨110864, by rfl⟩ : syracuseStep 147819 = 221729) B221729
theorem B147831 : Blo 147793 147831 := bstep (se 1 (by rfl) ⟨110873, by rfl⟩ : syracuseStep 147831 = 221747) B221747
theorem B147851 : Blo 147793 147851 := bstep (se 1 (by rfl) ⟨110888, by rfl⟩ : syracuseStep 147851 = 221777) B221777
theorem B541073 : Blo 147793 541073 := bstep (se 2 (by rfl) ⟨202902, by rfl⟩ : syracuseStep 541073 = 405805) B405805
theorem B147863 : Blo 147793 147863 := bstep (se 1 (by rfl) ⟨110897, by rfl⟩ : syracuseStep 147863 = 221795) B221795
theorem B147883 : Blo 147793 147883 := bstep (se 1 (by rfl) ⟨110912, by rfl⟩ : syracuseStep 147883 = 221825) B221825
theorem B475571 : Blo 147793 475571 := bstep (se 1 (by rfl) ⟨356678, by rfl⟩ : syracuseStep 475571 = 713357) B713357
theorem B573875 : Blo 147793 573875 := bstep (se 1 (by rfl) ⟨430406, by rfl⟩ : syracuseStep 573875 = 860813) B860813
theorem B147895 : Blo 147793 147895 := bstep (se 1 (by rfl) ⟨110921, by rfl⟩ : syracuseStep 147895 = 221843) B221843
theorem B147915 : Blo 147793 147915 := bstep (se 1 (by rfl) ⟨110936, by rfl⟩ : syracuseStep 147915 = 221873) B221873
theorem B147927 : Blo 147793 147927 := bstep (se 1 (by rfl) ⟨110945, by rfl⟩ : syracuseStep 147927 = 221891) B221891
theorem B147947 : Blo 147793 147947 := bstep (se 1 (by rfl) ⟨110960, by rfl⟩ : syracuseStep 147947 = 221921) B221921
theorem B147959 : Blo 147793 147959 := bstep (se 1 (by rfl) ⟨110969, by rfl⟩ : syracuseStep 147959 = 221939) B221939
theorem B147979 : Blo 147793 147979 := bstep (se 1 (by rfl) ⟨110984, by rfl⟩ : syracuseStep 147979 = 221969) B221969
theorem B147991 : Blo 147793 147991 := bstep (se 1 (by rfl) ⟨110993, by rfl⟩ : syracuseStep 147991 = 221987) B221987
theorem B213529 : Blo 147793 213529 := bstep (se 2 (by rfl) ⟨80073, by rfl⟩ : syracuseStep 213529 = 160147) B160147
theorem B148011 : Blo 147793 148011 := bstep (se 1 (by rfl) ⟨111008, by rfl⟩ : syracuseStep 148011 = 222017) B222017
theorem B148023 : Blo 147793 148023 := bstep (se 1 (by rfl) ⟨111017, by rfl⟩ : syracuseStep 148023 = 222035) B222035
theorem B148043 : Blo 147793 148043 := bstep (se 1 (by rfl) ⟨111032, by rfl⟩ : syracuseStep 148043 = 222065) B222065
theorem B377419 : Blo 147793 377419 := bstep (se 1 (by rfl) ⟨283064, by rfl⟩ : syracuseStep 377419 = 566129) B566129
theorem B148055 : Blo 147793 148055 := bstep (se 1 (by rfl) ⟨111041, by rfl⟩ : syracuseStep 148055 = 222083) B222083
theorem B148075 : Blo 147793 148075 := bstep (se 1 (by rfl) ⟨111056, by rfl⟩ : syracuseStep 148075 = 222113) B222113
theorem B148087 : Blo 147793 148087 := bstep (se 1 (by rfl) ⟨111065, by rfl⟩ : syracuseStep 148087 = 222131) B222131
theorem B148107 : Blo 147793 148107 := bstep (se 1 (by rfl) ⟨111080, by rfl⟩ : syracuseStep 148107 = 222161) B222161
theorem B148119 : Blo 147793 148119 := bstep (se 1 (by rfl) ⟨111089, by rfl⟩ : syracuseStep 148119 = 222179) B222179
theorem B148139 : Blo 147793 148139 := bstep (se 1 (by rfl) ⟨111104, by rfl⟩ : syracuseStep 148139 = 222209) B222209
theorem B148151 : Blo 147793 148151 := bstep (se 1 (by rfl) ⟨111113, by rfl⟩ : syracuseStep 148151 = 222227) B222227
theorem B148171 : Blo 147793 148171 := bstep (se 1 (by rfl) ⟨111128, by rfl⟩ : syracuseStep 148171 = 222257) B222257
theorem B148183 : Blo 147793 148183 := bstep (se 1 (by rfl) ⟨111137, by rfl⟩ : syracuseStep 148183 = 222275) B222275
theorem B377561 : Blo 147793 377561 := bstep (se 2 (by rfl) ⟨141585, by rfl⟩ : syracuseStep 377561 = 283171) B283171
theorem B148203 : Blo 147793 148203 := bstep (se 1 (by rfl) ⟨111152, by rfl⟩ : syracuseStep 148203 = 222305) B222305
theorem B148215 : Blo 147793 148215 := bstep (se 1 (by rfl) ⟨111161, by rfl⟩ : syracuseStep 148215 = 222323) B222323
theorem B148235 : Blo 147793 148235 := bstep (se 1 (by rfl) ⟨111176, by rfl⟩ : syracuseStep 148235 = 222353) B222353
theorem B148247 : Blo 147793 148247 := bstep (se 1 (by rfl) ⟨111185, by rfl⟩ : syracuseStep 148247 = 222371) B222371
theorem B148267 : Blo 147793 148267 := bstep (se 1 (by rfl) ⟨111200, by rfl⟩ : syracuseStep 148267 = 222401) B222401
theorem B148279 : Blo 147793 148279 := bstep (se 1 (by rfl) ⟨111209, by rfl⟩ : syracuseStep 148279 = 222419) B222419
theorem B475969 : Blo 147793 475969 := bstep (se 2 (by rfl) ⟨178488, by rfl⟩ : syracuseStep 475969 = 356977) B356977
theorem B541505 : Blo 147793 541505 := bstep (se 2 (by rfl) ⟨203064, by rfl⟩ : syracuseStep 541505 = 406129) B406129
theorem B148299 : Blo 147793 148299 := bstep (se 1 (by rfl) ⟨111224, by rfl⟩ : syracuseStep 148299 = 222449) B222449
theorem B148311 : Blo 147793 148311 := bstep (se 1 (by rfl) ⟨111233, by rfl⟩ : syracuseStep 148311 = 222467) B222467
theorem B148331 : Blo 147793 148331 := bstep (se 1 (by rfl) ⟨111248, by rfl⟩ : syracuseStep 148331 = 222497) B222497
theorem B148343 : Blo 147793 148343 := bstep (se 1 (by rfl) ⟨111257, by rfl⟩ : syracuseStep 148343 = 222515) B222515
theorem B148363 : Blo 147793 148363 := bstep (se 1 (by rfl) ⟨111272, by rfl⟩ : syracuseStep 148363 = 222545) B222545
theorem B607121 : Blo 147793 607121 := bstep (se 2 (by rfl) ⟨227670, by rfl⟩ : syracuseStep 607121 = 455341) B455341
theorem B148375 : Blo 147793 148375 := bstep (se 1 (by rfl) ⟨111281, by rfl⟩ : syracuseStep 148375 = 222563) B222563
theorem B148395 : Blo 147793 148395 := bstep (se 1 (by rfl) ⟨111296, by rfl⟩ : syracuseStep 148395 = 222593) B222593
theorem B148407 : Blo 147793 148407 := bstep (se 1 (by rfl) ⟨111305, by rfl⟩ : syracuseStep 148407 = 222611) B222611
theorem B148427 : Blo 147793 148427 := bstep (se 1 (by rfl) ⟨111320, by rfl⟩ : syracuseStep 148427 = 222641) B222641
theorem B148439 : Blo 147793 148439 := bstep (se 1 (by rfl) ⟨111329, by rfl⟩ : syracuseStep 148439 = 222659) B222659
theorem B148459 : Blo 147793 148459 := bstep (se 1 (by rfl) ⟨111344, by rfl⟩ : syracuseStep 148459 = 222689) B222689
theorem B148471 : Blo 147793 148471 := bstep (se 1 (by rfl) ⟨111353, by rfl⟩ : syracuseStep 148471 = 222707) B222707
theorem B148491 : Blo 147793 148491 := bstep (se 1 (by rfl) ⟨111368, by rfl⟩ : syracuseStep 148491 = 222737) B222737
theorem B148503 : Blo 147793 148503 := bstep (se 1 (by rfl) ⟨111377, by rfl⟩ : syracuseStep 148503 = 222755) B222755
theorem B148523 : Blo 147793 148523 := bstep (se 1 (by rfl) ⟨111392, by rfl⟩ : syracuseStep 148523 = 222785) B222785
theorem B148535 : Blo 147793 148535 := bstep (se 1 (by rfl) ⟨111401, by rfl⟩ : syracuseStep 148535 = 222803) B222803
theorem B148555 : Blo 147793 148555 := bstep (se 1 (by rfl) ⟨111416, by rfl⟩ : syracuseStep 148555 = 222833) B222833
theorem B509003 : Blo 147793 509003 := bstep (se 1 (by rfl) ⟨381752, by rfl⟩ : syracuseStep 509003 = 763505) B763505
theorem B148567 : Blo 147793 148567 := bstep (se 1 (by rfl) ⟨111425, by rfl⟩ : syracuseStep 148567 = 222851) B222851
theorem B148587 : Blo 147793 148587 := bstep (se 1 (by rfl) ⟨111440, by rfl⟩ : syracuseStep 148587 = 222881) B222881
theorem B148599 : Blo 147793 148599 := bstep (se 1 (by rfl) ⟨111449, by rfl⟩ : syracuseStep 148599 = 222899) B222899
theorem B148619 : Blo 147793 148619 := bstep (se 1 (by rfl) ⟨111464, by rfl⟩ : syracuseStep 148619 = 222929) B222929
theorem B148631 : Blo 147793 148631 := bstep (se 1 (by rfl) ⟨111473, by rfl⟩ : syracuseStep 148631 = 222947) B222947
theorem B148651 : Blo 147793 148651 := bstep (se 1 (by rfl) ⟨111488, by rfl⟩ : syracuseStep 148651 = 222977) B222977
theorem B148663 : Blo 147793 148663 := bstep (se 1 (by rfl) ⟨111497, by rfl⟩ : syracuseStep 148663 = 222995) B222995
theorem B148683 : Blo 147793 148683 := bstep (se 1 (by rfl) ⟨111512, by rfl⟩ : syracuseStep 148683 = 223025) B223025
theorem B148695 : Blo 147793 148695 := bstep (se 1 (by rfl) ⟨111521, by rfl⟩ : syracuseStep 148695 = 223043) B223043
theorem B148715 : Blo 147793 148715 := bstep (se 1 (by rfl) ⟨111536, by rfl⟩ : syracuseStep 148715 = 223073) B223073
theorem B148727 : Blo 147793 148727 := bstep (se 1 (by rfl) ⟨111545, by rfl⟩ : syracuseStep 148727 = 223091) B223091
theorem B148747 : Blo 147793 148747 := bstep (se 1 (by rfl) ⟨111560, by rfl⟩ : syracuseStep 148747 = 223121) B223121
theorem B148759 : Blo 147793 148759 := bstep (se 1 (by rfl) ⟨111569, by rfl⟩ : syracuseStep 148759 = 223139) B223139
theorem B148779 : Blo 147793 148779 := bstep (se 1 (by rfl) ⟨111584, by rfl⟩ : syracuseStep 148779 = 223169) B223169
theorem B541997 : Blo 147793 541997 := bstep (se 3 (by rfl) ⟨101624, by rfl⟩ : syracuseStep 541997 = 203249) B203249
theorem B148791 : Blo 147793 148791 := bstep (se 1 (by rfl) ⟨111593, by rfl⟩ : syracuseStep 148791 = 223187) B223187
theorem B148811 : Blo 147793 148811 := bstep (se 1 (by rfl) ⟨111608, by rfl⟩ : syracuseStep 148811 = 223217) B223217
theorem B148823 : Blo 147793 148823 := bstep (se 1 (by rfl) ⟨111617, by rfl⟩ : syracuseStep 148823 = 223235) B223235
theorem B279895 : Blo 147793 279895 := bstep (se 1 (by rfl) ⟨209921, by rfl⟩ : syracuseStep 279895 = 419843) B419843
theorem B509273 : Blo 147793 509273 := bstep (se 2 (by rfl) ⟨190977, by rfl⟩ : syracuseStep 509273 = 381955) B381955
theorem B148843 : Blo 147793 148843 := bstep (se 1 (by rfl) ⟨111632, by rfl⟩ : syracuseStep 148843 = 223265) B223265
theorem B148855 : Blo 147793 148855 := bstep (se 1 (by rfl) ⟨111641, by rfl⟩ : syracuseStep 148855 = 223283) B223283
theorem B148875 : Blo 147793 148875 := bstep (se 1 (by rfl) ⟨111656, by rfl⟩ : syracuseStep 148875 = 223313) B223313
theorem B148887 : Blo 147793 148887 := bstep (se 1 (by rfl) ⟨111665, by rfl⟩ : syracuseStep 148887 = 223331) B223331
theorem B148907 : Blo 147793 148907 := bstep (se 1 (by rfl) ⟨111680, by rfl⟩ : syracuseStep 148907 = 223361) B223361
theorem B148919 : Blo 147793 148919 := bstep (se 1 (by rfl) ⟨111689, by rfl⟩ : syracuseStep 148919 = 223379) B223379
theorem B148939 : Blo 147793 148939 := bstep (se 1 (by rfl) ⟨111704, by rfl⟩ : syracuseStep 148939 = 223409) B223409
theorem B148951 : Blo 147793 148951 := bstep (se 1 (by rfl) ⟨111713, by rfl⟩ : syracuseStep 148951 = 223427) B223427
theorem B148971 : Blo 147793 148971 := bstep (se 1 (by rfl) ⟨111728, by rfl⟩ : syracuseStep 148971 = 223457) B223457
theorem B148983 : Blo 147793 148983 := bstep (se 1 (by rfl) ⟨111737, by rfl⟩ : syracuseStep 148983 = 223475) B223475
theorem B149003 : Blo 147793 149003 := bstep (se 1 (by rfl) ⟨111752, by rfl⟩ : syracuseStep 149003 = 223505) B223505
theorem B149015 : Blo 147793 149015 := bstep (se 1 (by rfl) ⟨111761, by rfl⟩ : syracuseStep 149015 = 223523) B223523
theorem B378391 : Blo 147793 378391 := bstep (se 1 (by rfl) ⟨283793, by rfl⟩ : syracuseStep 378391 = 567587) B567587
theorem B2606627 : Blo 147793 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B149035 : Blo 147793 149035 := bstep (se 1 (by rfl) ⟨111776, by rfl⟩ : syracuseStep 149035 = 223553) B223553
theorem B149047 : Blo 147793 149047 := bstep (se 1 (by rfl) ⟨111785, by rfl⟩ : syracuseStep 149047 = 223571) B223571
theorem B149067 : Blo 147793 149067 := bstep (se 1 (by rfl) ⟨111800, by rfl⟩ : syracuseStep 149067 = 223601) B223601
theorem B149079 : Blo 147793 149079 := bstep (se 1 (by rfl) ⟨111809, by rfl⟩ : syracuseStep 149079 = 223619) B223619
theorem B771677 : Blo 147793 771677 := bstep (se 3 (by rfl) ⟨144689, by rfl⟩ : syracuseStep 771677 = 289379) B289379
theorem B149099 : Blo 147793 149099 := bstep (se 1 (by rfl) ⟨111824, by rfl⟩ : syracuseStep 149099 = 223649) B223649
theorem B149111 : Blo 147793 149111 := bstep (se 1 (by rfl) ⟨111833, by rfl⟩ : syracuseStep 149111 = 223667) B223667
theorem B149131 : Blo 147793 149131 := bstep (se 1 (by rfl) ⟨111848, by rfl⟩ : syracuseStep 149131 = 223697) B223697
theorem B149143 : Blo 147793 149143 := bstep (se 1 (by rfl) ⟨111857, by rfl⟩ : syracuseStep 149143 = 223715) B223715
theorem B149163 : Blo 147793 149163 := bstep (se 1 (by rfl) ⟨111872, by rfl⟩ : syracuseStep 149163 = 223745) B223745
theorem B149175 : Blo 147793 149175 := bstep (se 1 (by rfl) ⟨111881, by rfl⟩ : syracuseStep 149175 = 223763) B223763
theorem B149195 : Blo 147793 149195 := bstep (se 1 (by rfl) ⟨111896, by rfl⟩ : syracuseStep 149195 = 223793) B223793
theorem B181963 : Blo 147793 181963 := bstep (se 1 (by rfl) ⟨136472, by rfl⟩ : syracuseStep 181963 = 272945) B272945
theorem B149207 : Blo 147793 149207 := bstep (se 1 (by rfl) ⟨111905, by rfl⟩ : syracuseStep 149207 = 223811) B223811
theorem B149227 : Blo 147793 149227 := bstep (se 1 (by rfl) ⟨111920, by rfl⟩ : syracuseStep 149227 = 223841) B223841
theorem B149239 : Blo 147793 149239 := bstep (se 1 (by rfl) ⟨111929, by rfl⟩ : syracuseStep 149239 = 223859) B223859
theorem B149259 : Blo 147793 149259 := bstep (se 1 (by rfl) ⟨111944, by rfl⟩ : syracuseStep 149259 = 223889) B223889
theorem B149271 : Blo 147793 149271 := bstep (se 1 (by rfl) ⟨111953, by rfl⟩ : syracuseStep 149271 = 223907) B223907
theorem B149291 : Blo 147793 149291 := bstep (se 1 (by rfl) ⟨111968, by rfl⟩ : syracuseStep 149291 = 223937) B223937
theorem B149303 : Blo 147793 149303 := bstep (se 1 (by rfl) ⟨111977, by rfl⟩ : syracuseStep 149303 = 223955) B223955
theorem B149323 : Blo 147793 149323 := bstep (se 1 (by rfl) ⟨111992, by rfl⟩ : syracuseStep 149323 = 223985) B223985
theorem B149335 : Blo 147793 149335 := bstep (se 1 (by rfl) ⟨112001, by rfl⟩ : syracuseStep 149335 = 224003) B224003
theorem B149355 : Blo 147793 149355 := bstep (se 1 (by rfl) ⟨112016, by rfl⟩ : syracuseStep 149355 = 224033) B224033
theorem B149367 : Blo 147793 149367 := bstep (se 1 (by rfl) ⟨112025, by rfl⟩ : syracuseStep 149367 = 224051) B224051
theorem B575363 : Blo 147793 575363 := bstep (se 1 (by rfl) ⟨431522, by rfl⟩ : syracuseStep 575363 = 863045) B863045
theorem B149387 : Blo 147793 149387 := bstep (se 1 (by rfl) ⟨112040, by rfl⟩ : syracuseStep 149387 = 224081) B224081
theorem B149399 : Blo 147793 149399 := bstep (se 1 (by rfl) ⟨112049, by rfl⟩ : syracuseStep 149399 = 224099) B224099
theorem B575383 : Blo 147793 575383 := bstep (se 1 (by rfl) ⟨431537, by rfl⟩ : syracuseStep 575383 = 863075) B863075
theorem B149419 : Blo 147793 149419 := bstep (se 1 (by rfl) ⟨112064, by rfl⟩ : syracuseStep 149419 = 224129) B224129
theorem B1263539 : Blo 147793 1263539 := bstep (se 1 (by rfl) ⟨947654, by rfl⟩ : syracuseStep 1263539 = 1895309) B1895309
theorem B149431 : Blo 147793 149431 := bstep (se 1 (by rfl) ⟨112073, by rfl⟩ : syracuseStep 149431 = 224147) B224147
theorem B149451 : Blo 147793 149451 := bstep (se 1 (by rfl) ⟨112088, by rfl⟩ : syracuseStep 149451 = 224177) B224177
theorem B378827 : Blo 147793 378827 := bstep (se 1 (by rfl) ⟨284120, by rfl⟩ : syracuseStep 378827 = 568241) B568241
theorem B214987 : Blo 147793 214987 := bstep (se 1 (by rfl) ⟨161240, by rfl⟩ : syracuseStep 214987 = 322481) B322481
theorem B149463 : Blo 147793 149463 := bstep (se 1 (by rfl) ⟨112097, by rfl⟩ : syracuseStep 149463 = 224195) B224195
theorem B149483 : Blo 147793 149483 := bstep (se 1 (by rfl) ⟨112112, by rfl⟩ : syracuseStep 149483 = 224225) B224225
theorem B149495 : Blo 147793 149495 := bstep (se 1 (by rfl) ⟨112121, by rfl⟩ : syracuseStep 149495 = 224243) B224243
theorem B149515 : Blo 147793 149515 := bstep (se 1 (by rfl) ⟨112136, by rfl⟩ : syracuseStep 149515 = 224273) B224273
theorem B149527 : Blo 147793 149527 := bstep (se 1 (by rfl) ⟨112145, by rfl⟩ : syracuseStep 149527 = 224291) B224291
theorem B509975 : Blo 147793 509975 := bstep (se 1 (by rfl) ⟨382481, by rfl⟩ : syracuseStep 509975 = 764963) B764963
theorem B149547 : Blo 147793 149547 := bstep (se 1 (by rfl) ⟨112160, by rfl⟩ : syracuseStep 149547 = 224321) B224321
theorem B149559 : Blo 147793 149559 := bstep (se 1 (by rfl) ⟨112169, by rfl⟩ : syracuseStep 149559 = 224339) B224339
theorem B149579 : Blo 147793 149579 := bstep (se 1 (by rfl) ⟨112184, by rfl⟩ : syracuseStep 149579 = 224369) B224369
theorem B149591 : Blo 147793 149591 := bstep (se 1 (by rfl) ⟨112193, by rfl⟩ : syracuseStep 149591 = 224387) B224387
theorem B149611 : Blo 147793 149611 := bstep (se 1 (by rfl) ⟨112208, by rfl⟩ : syracuseStep 149611 = 224417) B224417
theorem B149623 : Blo 147793 149623 := bstep (se 1 (by rfl) ⟨112217, by rfl⟩ : syracuseStep 149623 = 224435) B224435
theorem B149643 : Blo 147793 149643 := bstep (se 1 (by rfl) ⟨112232, by rfl⟩ : syracuseStep 149643 = 224465) B224465
theorem B149655 : Blo 147793 149655 := bstep (se 1 (by rfl) ⟨112241, by rfl⟩ : syracuseStep 149655 = 224483) B224483
theorem B7850135 : Blo 147793 7850135 := bstep (se 1 (by rfl) ⟨5887601, by rfl⟩ : syracuseStep 7850135 = 11775203) B11775203
theorem B149675 : Blo 147793 149675 := bstep (se 1 (by rfl) ⟨112256, by rfl⟩ : syracuseStep 149675 = 224513) B224513
theorem B149687 : Blo 147793 149687 := bstep (se 1 (by rfl) ⟨112265, by rfl⟩ : syracuseStep 149687 = 224531) B224531
theorem B149707 : Blo 147793 149707 := bstep (se 1 (by rfl) ⟨112280, by rfl⟩ : syracuseStep 149707 = 224561) B224561
theorem B149719 : Blo 147793 149719 := bstep (se 1 (by rfl) ⟨112289, by rfl⟩ : syracuseStep 149719 = 224579) B224579
theorem B149739 : Blo 147793 149739 := bstep (se 1 (by rfl) ⟨112304, by rfl⟩ : syracuseStep 149739 = 224609) B224609
theorem B149751 : Blo 147793 149751 := bstep (se 1 (by rfl) ⟨112313, by rfl⟩ : syracuseStep 149751 = 224627) B224627
theorem B149771 : Blo 147793 149771 := bstep (se 1 (by rfl) ⟨112328, by rfl⟩ : syracuseStep 149771 = 224657) B224657
theorem B149783 : Blo 147793 149783 := bstep (se 1 (by rfl) ⟨112337, by rfl⟩ : syracuseStep 149783 = 224675) B224675
theorem B149803 : Blo 147793 149803 := bstep (se 1 (by rfl) ⟨112352, by rfl⟩ : syracuseStep 149803 = 224705) B224705
theorem B510259 : Blo 147793 510259 := bstep (se 1 (by rfl) ⟨382694, by rfl⟩ : syracuseStep 510259 = 765389) B765389
theorem B149815 : Blo 147793 149815 := bstep (se 1 (by rfl) ⟨112361, by rfl⟩ : syracuseStep 149815 = 224723) B224723
theorem B1132865 : Blo 147793 1132865 := bstep (se 2 (by rfl) ⟨424824, by rfl⟩ : syracuseStep 1132865 = 849649) B849649
theorem B379201 : Blo 147793 379201 := bstep (se 2 (by rfl) ⟨142200, by rfl⟩ : syracuseStep 379201 = 284401) B284401
theorem B149835 : Blo 147793 149835 := bstep (se 1 (by rfl) ⟨112376, by rfl⟩ : syracuseStep 149835 = 224753) B224753
theorem B575819 : Blo 147793 575819 := bstep (se 1 (by rfl) ⟨431864, by rfl⟩ : syracuseStep 575819 = 863729) B863729
theorem B149847 : Blo 147793 149847 := bstep (se 1 (by rfl) ⟨112385, by rfl⟩ : syracuseStep 149847 = 224771) B224771
theorem B149867 : Blo 147793 149867 := bstep (se 1 (by rfl) ⟨112400, by rfl⟩ : syracuseStep 149867 = 224801) B224801
theorem B149879 : Blo 147793 149879 := bstep (se 1 (by rfl) ⟨112409, by rfl⟩ : syracuseStep 149879 = 224819) B224819
theorem B149899 : Blo 147793 149899 := bstep (se 1 (by rfl) ⟨112424, by rfl⟩ : syracuseStep 149899 = 224849) B224849
theorem B149911 : Blo 147793 149911 := bstep (se 1 (by rfl) ⟨112433, by rfl⟩ : syracuseStep 149911 = 224867) B224867
theorem B149931 : Blo 147793 149931 := bstep (se 1 (by rfl) ⟨112448, by rfl⟩ : syracuseStep 149931 = 224897) B224897
theorem B641459 : Blo 147793 641459 := bstep (se 1 (by rfl) ⟨481094, by rfl⟩ : syracuseStep 641459 = 962189) B962189
theorem B149943 : Blo 147793 149943 := bstep (se 1 (by rfl) ⟨112457, by rfl⟩ : syracuseStep 149943 = 224915) B224915
theorem B149963 : Blo 147793 149963 := bstep (se 1 (by rfl) ⟨112472, by rfl⟩ : syracuseStep 149963 = 224945) B224945
theorem B149975 : Blo 147793 149975 := bstep (se 1 (by rfl) ⟨112481, by rfl⟩ : syracuseStep 149975 = 224963) B224963
theorem B2279897 : Blo 147793 2279897 := bstep (se 2 (by rfl) ⟨854961, by rfl⟩ : syracuseStep 2279897 = 1709923) B1709923
theorem B149995 : Blo 147793 149995 := bstep (se 1 (by rfl) ⟨112496, by rfl⟩ : syracuseStep 149995 = 224993) B224993
theorem B150007 : Blo 147793 150007 := bstep (se 1 (by rfl) ⟨112505, by rfl⟩ : syracuseStep 150007 = 225011) B225011
theorem B608771 : Blo 147793 608771 := bstep (se 1 (by rfl) ⟨456578, by rfl⟩ : syracuseStep 608771 = 913157) B913157
theorem B150027 : Blo 147793 150027 := bstep (se 1 (by rfl) ⟨112520, by rfl⟩ : syracuseStep 150027 = 225041) B225041
theorem B576017 : Blo 147793 576017 := bstep (se 2 (by rfl) ⟨216006, by rfl⟩ : syracuseStep 576017 = 432013) B432013
theorem B150039 : Blo 147793 150039 := bstep (se 1 (by rfl) ⟨112529, by rfl⟩ : syracuseStep 150039 = 225059) B225059
theorem B150059 : Blo 147793 150059 := bstep (se 1 (by rfl) ⟨112544, by rfl⟩ : syracuseStep 150059 = 225089) B225089
theorem B510515 : Blo 147793 510515 := bstep (se 1 (by rfl) ⟨382886, by rfl⟩ : syracuseStep 510515 = 765773) B765773
theorem B150071 : Blo 147793 150071 := bstep (se 1 (by rfl) ⟨112553, by rfl⟩ : syracuseStep 150071 = 225107) B225107
theorem B150091 : Blo 147793 150091 := bstep (se 1 (by rfl) ⟨112568, by rfl⟩ : syracuseStep 150091 = 225137) B225137
theorem B641611 : Blo 147793 641611 := bstep (se 1 (by rfl) ⟨481208, by rfl⟩ : syracuseStep 641611 = 962417) B962417
theorem B150103 : Blo 147793 150103 := bstep (se 1 (by rfl) ⟨112577, by rfl⟩ : syracuseStep 150103 = 225155) B225155
theorem B150123 : Blo 147793 150123 := bstep (se 1 (by rfl) ⟨112592, by rfl⟩ : syracuseStep 150123 = 225185) B225185
theorem B150135 : Blo 147793 150135 := bstep (se 1 (by rfl) ⟨112601, by rfl⟩ : syracuseStep 150135 = 225203) B225203
theorem B281227 : Blo 147793 281227 := bstep (se 1 (by rfl) ⟨210920, by rfl⟩ : syracuseStep 281227 = 421841) B421841
theorem B150155 : Blo 147793 150155 := bstep (se 1 (by rfl) ⟨112616, by rfl⟩ : syracuseStep 150155 = 225233) B225233
theorem B641681 : Blo 147793 641681 := bstep (se 2 (by rfl) ⟨240630, by rfl⟩ : syracuseStep 641681 = 481261) B481261
theorem B150167 : Blo 147793 150167 := bstep (se 1 (by rfl) ⟨112625, by rfl⟩ : syracuseStep 150167 = 225251) B225251
theorem B150187 : Blo 147793 150187 := bstep (se 1 (by rfl) ⟨112640, by rfl⟩ : syracuseStep 150187 = 225281) B225281
theorem B150199 : Blo 147793 150199 := bstep (se 1 (by rfl) ⟨112649, by rfl⟩ : syracuseStep 150199 = 225299) B225299
theorem B674507 : Blo 147793 674507 := bstep (se 1 (by rfl) ⟨505880, by rfl⟩ : syracuseStep 674507 = 1011761) B1011761
theorem B150219 : Blo 147793 150219 := bstep (se 1 (by rfl) ⟨112664, by rfl⟩ : syracuseStep 150219 = 225329) B225329
theorem B281303 : Blo 147793 281303 := bstep (se 1 (by rfl) ⟨210977, by rfl⟩ : syracuseStep 281303 = 421955) B421955
theorem B150231 : Blo 147793 150231 := bstep (se 1 (by rfl) ⟨112673, by rfl⟩ : syracuseStep 150231 = 225347) B225347
theorem B150251 : Blo 147793 150251 := bstep (se 1 (by rfl) ⟨112688, by rfl⟩ : syracuseStep 150251 = 225377) B225377
theorem B150263 : Blo 147793 150263 := bstep (se 1 (by rfl) ⟨112697, by rfl⟩ : syracuseStep 150263 = 225395) B225395
theorem B150283 : Blo 147793 150283 := bstep (se 1 (by rfl) ⟨112712, by rfl⟩ : syracuseStep 150283 = 225425) B225425
theorem B150295 : Blo 147793 150295 := bstep (se 1 (by rfl) ⟨112721, by rfl⟩ : syracuseStep 150295 = 225443) B225443
theorem B150315 : Blo 147793 150315 := bstep (se 1 (by rfl) ⟨112736, by rfl⟩ : syracuseStep 150315 = 225473) B225473
theorem B150327 : Blo 147793 150327 := bstep (se 1 (by rfl) ⟨112745, by rfl⟩ : syracuseStep 150327 = 225491) B225491
theorem B510785 : Blo 147793 510785 := bstep (se 2 (by rfl) ⟨191544, by rfl⟩ : syracuseStep 510785 = 383089) B383089
theorem B150347 : Blo 147793 150347 := bstep (se 1 (by rfl) ⟨112760, by rfl⟩ : syracuseStep 150347 = 225521) B225521
theorem B150359 : Blo 147793 150359 := bstep (se 1 (by rfl) ⟨112769, by rfl⟩ : syracuseStep 150359 = 225539) B225539
theorem B150379 : Blo 147793 150379 := bstep (se 1 (by rfl) ⟨112784, by rfl⟩ : syracuseStep 150379 = 225569) B225569
theorem B150391 : Blo 147793 150391 := bstep (se 1 (by rfl) ⟨112793, by rfl⟩ : syracuseStep 150391 = 225587) B225587
theorem B150411 : Blo 147793 150411 := bstep (se 1 (by rfl) ⟨112808, by rfl⟩ : syracuseStep 150411 = 225617) B225617
theorem B379799 : Blo 147793 379799 := bstep (se 1 (by rfl) ⟨284849, by rfl⟩ : syracuseStep 379799 = 569699) B569699
theorem B150423 : Blo 147793 150423 := bstep (se 1 (by rfl) ⟨112817, by rfl⟩ : syracuseStep 150423 = 225635) B225635
theorem B150443 : Blo 147793 150443 := bstep (se 1 (by rfl) ⟨112832, by rfl⟩ : syracuseStep 150443 = 225665) B225665
theorem B543667 : Blo 147793 543667 := bstep (se 1 (by rfl) ⟨407750, by rfl⟩ : syracuseStep 543667 = 815501) B815501
theorem B150455 : Blo 147793 150455 := bstep (se 1 (by rfl) ⟨112841, by rfl⟩ : syracuseStep 150455 = 225683) B225683
theorem B609227 : Blo 147793 609227 := bstep (se 1 (by rfl) ⟨456920, by rfl⟩ : syracuseStep 609227 = 913841) B913841
theorem B150475 : Blo 147793 150475 := bstep (se 1 (by rfl) ⟨112856, by rfl⟩ : syracuseStep 150475 = 225713) B225713
theorem B150487 : Blo 147793 150487 := bstep (se 1 (by rfl) ⟨112865, by rfl⟩ : syracuseStep 150487 = 225731) B225731
theorem B150507 : Blo 147793 150507 := bstep (se 1 (by rfl) ⟨112880, by rfl⟩ : syracuseStep 150507 = 225761) B225761
theorem B150519 : Blo 147793 150519 := bstep (se 1 (by rfl) ⟨112889, by rfl⟩ : syracuseStep 150519 = 225779) B225779
theorem B150539 : Blo 147793 150539 := bstep (se 1 (by rfl) ⟨112904, by rfl⟩ : syracuseStep 150539 = 225809) B225809
theorem B150551 : Blo 147793 150551 := bstep (se 1 (by rfl) ⟨112913, by rfl⟩ : syracuseStep 150551 = 225827) B225827
theorem B150571 : Blo 147793 150571 := bstep (se 1 (by rfl) ⟨112928, by rfl⟩ : syracuseStep 150571 = 225857) B225857
theorem B150583 : Blo 147793 150583 := bstep (se 1 (by rfl) ⟨112937, by rfl⟩ : syracuseStep 150583 = 225875) B225875
theorem B150603 : Blo 147793 150603 := bstep (se 1 (by rfl) ⟨112952, by rfl⟩ : syracuseStep 150603 = 225905) B225905
theorem B150615 : Blo 147793 150615 := bstep (se 1 (by rfl) ⟨112961, by rfl⟩ : syracuseStep 150615 = 225923) B225923
theorem B150635 : Blo 147793 150635 := bstep (se 1 (by rfl) ⟨112976, by rfl⟩ : syracuseStep 150635 = 225953) B225953
theorem B150647 : Blo 147793 150647 := bstep (se 1 (by rfl) ⟨112985, by rfl⟩ : syracuseStep 150647 = 225971) B225971
theorem B150667 : Blo 147793 150667 := bstep (se 1 (by rfl) ⟨113000, by rfl⟩ : syracuseStep 150667 = 226001) B226001
theorem B150679 : Blo 147793 150679 := bstep (se 1 (by rfl) ⟨113009, by rfl⟩ : syracuseStep 150679 = 226019) B226019
theorem B150699 : Blo 147793 150699 := bstep (se 1 (by rfl) ⟨113024, by rfl⟩ : syracuseStep 150699 = 226049) B226049
theorem B150711 : Blo 147793 150711 := bstep (se 1 (by rfl) ⟨113033, by rfl⟩ : syracuseStep 150711 = 226067) B226067
theorem B150731 : Blo 147793 150731 := bstep (se 1 (by rfl) ⟨113048, by rfl⟩ : syracuseStep 150731 = 226097) B226097
theorem B150743 : Blo 147793 150743 := bstep (se 1 (by rfl) ⟨113057, by rfl⟩ : syracuseStep 150743 = 226115) B226115
theorem B150763 : Blo 147793 150763 := bstep (se 1 (by rfl) ⟨113072, by rfl⟩ : syracuseStep 150763 = 226145) B226145
theorem B150775 : Blo 147793 150775 := bstep (se 1 (by rfl) ⟨113081, by rfl⟩ : syracuseStep 150775 = 226163) B226163
theorem B150795 : Blo 147793 150795 := bstep (se 1 (by rfl) ⟨113096, by rfl⟩ : syracuseStep 150795 = 226193) B226193
theorem B150807 : Blo 147793 150807 := bstep (se 1 (by rfl) ⟨113105, by rfl⟩ : syracuseStep 150807 = 226211) B226211
theorem B150827 : Blo 147793 150827 := bstep (se 1 (by rfl) ⟨113120, by rfl⟩ : syracuseStep 150827 = 226241) B226241
theorem B150839 : Blo 147793 150839 := bstep (se 1 (by rfl) ⟨113129, by rfl⟩ : syracuseStep 150839 = 226259) B226259
theorem B150859 : Blo 147793 150859 := bstep (se 1 (by rfl) ⟨113144, by rfl⟩ : syracuseStep 150859 = 226289) B226289
theorem B150871 : Blo 147793 150871 := bstep (se 1 (by rfl) ⟨113153, by rfl⟩ : syracuseStep 150871 = 226307) B226307
theorem B511325 : Blo 147793 511325 := bstep (se 3 (by rfl) ⟨95873, by rfl⟩ : syracuseStep 511325 = 191747) B191747
theorem B150891 : Blo 147793 150891 := bstep (se 1 (by rfl) ⟨113168, by rfl⟩ : syracuseStep 150891 = 226337) B226337
theorem B281971 : Blo 147793 281971 := bstep (se 1 (by rfl) ⟨211478, by rfl⟩ : syracuseStep 281971 = 422957) B422957
theorem B150903 : Blo 147793 150903 := bstep (se 1 (by rfl) ⟨113177, by rfl⟩ : syracuseStep 150903 = 226355) B226355
theorem B150923 : Blo 147793 150923 := bstep (se 1 (by rfl) ⟨113192, by rfl⟩ : syracuseStep 150923 = 226385) B226385
theorem B150935 : Blo 147793 150935 := bstep (se 1 (by rfl) ⟨113201, by rfl⟩ : syracuseStep 150935 = 226403) B226403
theorem B150955 : Blo 147793 150955 := bstep (se 1 (by rfl) ⟨113216, by rfl⟩ : syracuseStep 150955 = 226433) B226433
theorem B150967 : Blo 147793 150967 := bstep (se 1 (by rfl) ⟨113225, by rfl⟩ : syracuseStep 150967 = 226451) B226451
theorem B150987 : Blo 147793 150987 := bstep (se 1 (by rfl) ⟨113240, by rfl⟩ : syracuseStep 150987 = 226481) B226481
theorem B150999 : Blo 147793 150999 := bstep (se 1 (by rfl) ⟨113249, by rfl⟩ : syracuseStep 150999 = 226499) B226499
theorem B151019 : Blo 147793 151019 := bstep (se 1 (by rfl) ⟨113264, by rfl⟩ : syracuseStep 151019 = 226529) B226529
theorem B151031 : Blo 147793 151031 := bstep (se 1 (by rfl) ⟨113273, by rfl⟩ : syracuseStep 151031 = 226547) B226547
theorem B151051 : Blo 147793 151051 := bstep (se 1 (by rfl) ⟨113288, by rfl⟩ : syracuseStep 151051 = 226577) B226577
theorem B2870801 : Blo 147793 2870801 := bstep (se 2 (by rfl) ⟨1076550, by rfl⟩ : syracuseStep 2870801 = 2153101) B2153101
theorem B151063 : Blo 147793 151063 := bstep (se 1 (by rfl) ⟨113297, by rfl⟩ : syracuseStep 151063 = 226595) B226595
theorem B151083 : Blo 147793 151083 := bstep (se 1 (by rfl) ⟨113312, by rfl⟩ : syracuseStep 151083 = 226625) B226625
theorem B151095 : Blo 147793 151095 := bstep (se 1 (by rfl) ⟨113321, by rfl⟩ : syracuseStep 151095 = 226643) B226643
theorem B249419 : Blo 147793 249419 := bstep (se 1 (by rfl) ⟨187064, by rfl⟩ : syracuseStep 249419 = 374129) B374129
theorem B151115 : Blo 147793 151115 := bstep (se 1 (by rfl) ⟨113336, by rfl⟩ : syracuseStep 151115 = 226673) B226673
theorem B282199 : Blo 147793 282199 := bstep (se 1 (by rfl) ⟨211649, by rfl⟩ : syracuseStep 282199 = 423299) B423299
theorem B151127 : Blo 147793 151127 := bstep (se 1 (by rfl) ⟨113345, by rfl⟩ : syracuseStep 151127 = 226691) B226691
theorem B413273 : Blo 147793 413273 := bstep (se 2 (by rfl) ⟨154977, by rfl⟩ : syracuseStep 413273 = 309955) B309955
theorem B151147 : Blo 147793 151147 := bstep (se 1 (by rfl) ⟨113360, by rfl⟩ : syracuseStep 151147 = 226721) B226721
theorem B151159 : Blo 147793 151159 := bstep (se 1 (by rfl) ⟨113369, by rfl⟩ : syracuseStep 151159 = 226739) B226739
theorem B151179 : Blo 147793 151179 := bstep (se 1 (by rfl) ⟨113384, by rfl⟩ : syracuseStep 151179 = 226769) B226769
theorem B1199767 : Blo 147793 1199767 := bstep (se 1 (by rfl) ⟨899825, by rfl⟩ : syracuseStep 1199767 = 1799651) B1799651
theorem B151191 : Blo 147793 151191 := bstep (se 1 (by rfl) ⟨113393, by rfl⟩ : syracuseStep 151191 = 226787) B226787
theorem B151211 : Blo 147793 151211 := bstep (se 1 (by rfl) ⟨113408, by rfl⟩ : syracuseStep 151211 = 226817) B226817
theorem B151223 : Blo 147793 151223 := bstep (se 1 (by rfl) ⟨113417, by rfl⟩ : syracuseStep 151223 = 226835) B226835
theorem B282305 : Blo 147793 282305 := bstep (se 2 (by rfl) ⟨105864, by rfl⟩ : syracuseStep 282305 = 211729) B211729
theorem B380609 : Blo 147793 380609 := bstep (se 2 (by rfl) ⟨142728, by rfl⟩ : syracuseStep 380609 = 285457) B285457
theorem B249547 : Blo 147793 249547 := bstep (se 1 (by rfl) ⟨187160, by rfl⟩ : syracuseStep 249547 = 374321) B374321
theorem B151243 : Blo 147793 151243 := bstep (se 1 (by rfl) ⟨113432, by rfl⟩ : syracuseStep 151243 = 226865) B226865
theorem B151255 : Blo 147793 151255 := bstep (se 1 (by rfl) ⟨113441, by rfl⟩ : syracuseStep 151255 = 226883) B226883
theorem B151275 : Blo 147793 151275 := bstep (se 1 (by rfl) ⟨113456, by rfl⟩ : syracuseStep 151275 = 226913) B226913
theorem B151287 : Blo 147793 151287 := bstep (se 1 (by rfl) ⟨113465, by rfl⟩ : syracuseStep 151287 = 226931) B226931
theorem B151307 : Blo 147793 151307 := bstep (se 1 (by rfl) ⟨113480, by rfl⟩ : syracuseStep 151307 = 226961) B226961
theorem B151319 : Blo 147793 151319 := bstep (se 1 (by rfl) ⟨113489, by rfl⟩ : syracuseStep 151319 = 226979) B226979
theorem B151339 : Blo 147793 151339 := bstep (se 1 (by rfl) ⟨113504, by rfl⟩ : syracuseStep 151339 = 227009) B227009
theorem B1265453 : Blo 147793 1265453 := bstep (se 3 (by rfl) ⟨237272, by rfl⟩ : syracuseStep 1265453 = 474545) B474545
theorem B151351 : Blo 147793 151351 := bstep (se 1 (by rfl) ⟨113513, by rfl⟩ : syracuseStep 151351 = 227027) B227027
theorem B151371 : Blo 147793 151371 := bstep (se 1 (by rfl) ⟨113528, by rfl⟩ : syracuseStep 151371 = 227057) B227057
theorem B151383 : Blo 147793 151383 := bstep (se 1 (by rfl) ⟨113537, by rfl⟩ : syracuseStep 151383 = 227075) B227075
theorem B249689 : Blo 147793 249689 := bstep (se 2 (by rfl) ⟨93633, by rfl⟩ : syracuseStep 249689 = 187267) B187267
theorem B282457 : Blo 147793 282457 := bstep (se 2 (by rfl) ⟨105921, by rfl⟩ : syracuseStep 282457 = 211843) B211843
theorem B151403 : Blo 147793 151403 := bstep (se 1 (by rfl) ⟨113552, by rfl⟩ : syracuseStep 151403 = 227105) B227105
theorem B151415 : Blo 147793 151415 := bstep (se 1 (by rfl) ⟨113561, by rfl⟩ : syracuseStep 151415 = 227123) B227123
theorem B151435 : Blo 147793 151435 := bstep (se 1 (by rfl) ⟨113576, by rfl⟩ : syracuseStep 151435 = 227153) B227153
theorem B151447 : Blo 147793 151447 := bstep (se 1 (by rfl) ⟨113585, by rfl⟩ : syracuseStep 151447 = 227171) B227171
theorem B151467 : Blo 147793 151467 := bstep (se 1 (by rfl) ⟨113600, by rfl⟩ : syracuseStep 151467 = 227201) B227201
theorem B151479 : Blo 147793 151479 := bstep (se 1 (by rfl) ⟨113609, by rfl⟩ : syracuseStep 151479 = 227219) B227219
theorem B151499 : Blo 147793 151499 := bstep (se 1 (by rfl) ⟨113624, by rfl⟩ : syracuseStep 151499 = 227249) B227249
theorem B151511 : Blo 147793 151511 := bstep (se 1 (by rfl) ⟨113633, by rfl⟩ : syracuseStep 151511 = 227267) B227267
theorem B249817 : Blo 147793 249817 := bstep (se 2 (by rfl) ⟨93681, by rfl⟩ : syracuseStep 249817 = 187363) B187363
theorem B151531 : Blo 147793 151531 := bstep (se 1 (by rfl) ⟨113648, by rfl⟩ : syracuseStep 151531 = 227297) B227297
theorem B151543 : Blo 147793 151543 := bstep (se 1 (by rfl) ⟨113657, by rfl⟩ : syracuseStep 151543 = 227315) B227315
theorem B151563 : Blo 147793 151563 := bstep (se 1 (by rfl) ⟨113672, by rfl⟩ : syracuseStep 151563 = 227345) B227345
theorem B610327 : Blo 147793 610327 := bstep (se 1 (by rfl) ⟨457745, by rfl⟩ : syracuseStep 610327 = 915491) B915491
theorem B151575 : Blo 147793 151575 := bstep (se 1 (by rfl) ⟨113681, by rfl⟩ : syracuseStep 151575 = 227363) B227363
theorem B151595 : Blo 147793 151595 := bstep (se 1 (by rfl) ⟨113696, by rfl⟩ : syracuseStep 151595 = 227393) B227393
theorem B151607 : Blo 147793 151607 := bstep (se 1 (by rfl) ⟨113705, by rfl⟩ : syracuseStep 151607 = 227411) B227411
theorem B151627 : Blo 147793 151627 := bstep (se 1 (by rfl) ⟨113720, by rfl⟩ : syracuseStep 151627 = 227441) B227441
theorem B151639 : Blo 147793 151639 := bstep (se 1 (by rfl) ⟨113729, by rfl⟩ : syracuseStep 151639 = 227459) B227459
theorem B151659 : Blo 147793 151659 := bstep (se 1 (by rfl) ⟨113744, by rfl⟩ : syracuseStep 151659 = 227489) B227489
theorem B151671 : Blo 147793 151671 := bstep (se 1 (by rfl) ⟨113753, by rfl⟩ : syracuseStep 151671 = 227507) B227507
theorem B151691 : Blo 147793 151691 := bstep (se 1 (by rfl) ⟨113768, by rfl⟩ : syracuseStep 151691 = 227537) B227537
theorem B151703 : Blo 147793 151703 := bstep (se 1 (by rfl) ⟨113777, by rfl⟩ : syracuseStep 151703 = 227555) B227555
theorem B151723 : Blo 147793 151723 := bstep (se 1 (by rfl) ⟨113792, by rfl⟩ : syracuseStep 151723 = 227585) B227585
theorem B151735 : Blo 147793 151735 := bstep (se 1 (by rfl) ⟨113801, by rfl⟩ : syracuseStep 151735 = 227603) B227603
theorem B151755 : Blo 147793 151755 := bstep (se 1 (by rfl) ⟨113816, by rfl⟩ : syracuseStep 151755 = 227633) B227633
theorem B151767 : Blo 147793 151767 := bstep (se 1 (by rfl) ⟨113825, by rfl⟩ : syracuseStep 151767 = 227651) B227651
theorem B1134809 : Blo 147793 1134809 := bstep (se 2 (by rfl) ⟨425553, by rfl⟩ : syracuseStep 1134809 = 851107) B851107
theorem B381145 : Blo 147793 381145 := bstep (se 2 (by rfl) ⟨142929, by rfl⟩ : syracuseStep 381145 = 285859) B285859
theorem B151787 : Blo 147793 151787 := bstep (se 1 (by rfl) ⟨113840, by rfl⟩ : syracuseStep 151787 = 227681) B227681
theorem B643373 : Blo 147793 643373 := bstep (se 3 (by rfl) ⟨120632, by rfl⟩ : syracuseStep 643373 = 241265) B241265
theorem B1266137 : Blo 147793 1266137 := bstep (se 2 (by rfl) ⟨474801, by rfl⟩ : syracuseStep 1266137 = 949603) B949603
theorem B1921553 : Blo 147793 1921553 := bstep (se 2 (by rfl) ⟨720582, by rfl⟩ : syracuseStep 1921553 = 1441165) B1441165
theorem B250391 : Blo 147793 250391 := bstep (se 1 (by rfl) ⟨187793, by rfl⟩ : syracuseStep 250391 = 375587) B375587
theorem B250519 : Blo 147793 250519 := bstep (se 1 (by rfl) ⟨187889, by rfl⟩ : syracuseStep 250519 = 375779) B375779
theorem B971621 : Blo 147793 971621 := bstep (se 4 (by rfl) ⟨91089, by rfl⟩ : syracuseStep 971621 = 182179) B182179
theorem B545687 : Blo 147793 545687 := bstep (se 1 (by rfl) ⟨409265, by rfl⟩ : syracuseStep 545687 = 818531) B818531
theorem B644057 : Blo 147793 644057 := bstep (se 2 (by rfl) ⟨241521, by rfl⟩ : syracuseStep 644057 = 483043) B483043
theorem B283763 : Blo 147793 283763 := bstep (se 1 (by rfl) ⟨212822, by rfl⟩ : syracuseStep 283763 = 425645) B425645
theorem B251147 : Blo 147793 251147 := bstep (se 1 (by rfl) ⟨188360, by rfl⟩ : syracuseStep 251147 = 376721) B376721
theorem B283915 : Blo 147793 283915 := bstep (se 1 (by rfl) ⟨212936, by rfl⟩ : syracuseStep 283915 = 425873) B425873
theorem B316723 : Blo 147793 316723 := bstep (se 1 (by rfl) ⟨237542, by rfl⟩ : syracuseStep 316723 = 475085) B475085
theorem B382259 : Blo 147793 382259 := bstep (se 1 (by rfl) ⟨286694, by rfl⟩ : syracuseStep 382259 = 573389) B573389
theorem B972107 : Blo 147793 972107 := bstep (se 1 (by rfl) ⟨729080, by rfl⟩ : syracuseStep 972107 = 1458161) B1458161
theorem B251275 : Blo 147793 251275 := bstep (se 1 (by rfl) ⟨188456, by rfl⟩ : syracuseStep 251275 = 376913) B376913
theorem B251417 : Blo 147793 251417 := bstep (se 2 (by rfl) ⟨94281, by rfl⟩ : syracuseStep 251417 = 188563) B188563
theorem B448051 : Blo 147793 448051 := bstep (se 1 (by rfl) ⟨336038, by rfl⟩ : syracuseStep 448051 = 672077) B672077
theorem B284249 : Blo 147793 284249 := bstep (se 2 (by rfl) ⟨106593, by rfl⟩ : syracuseStep 284249 = 213187) B213187
theorem B382553 : Blo 147793 382553 := bstep (se 2 (by rfl) ⟨143457, by rfl⟩ : syracuseStep 382553 = 286915) B286915
theorem B317081 : Blo 147793 317081 := bstep (se 2 (by rfl) ⟨118905, by rfl⟩ : syracuseStep 317081 = 237811) B237811
theorem B251545 : Blo 147793 251545 := bstep (se 2 (by rfl) ⟨94329, by rfl⟩ : syracuseStep 251545 = 188659) B188659
theorem B4085453 : Blo 147793 4085453 := bstep (se 3 (by rfl) ⟨766022, by rfl⟩ : syracuseStep 4085453 = 1532045) B1532045
theorem B841859 : Blo 147793 841859 := bstep (se 1 (by rfl) ⟨631394, by rfl⟩ : syracuseStep 841859 = 1262789) B1262789
theorem B252119 : Blo 147793 252119 := bstep (se 1 (by rfl) ⟨189089, by rfl⟩ : syracuseStep 252119 = 378179) B378179
theorem B284887 : Blo 147793 284887 := bstep (se 1 (by rfl) ⟨213665, by rfl⟩ : syracuseStep 284887 = 427331) B427331
theorem B252247 : Blo 147793 252247 := bstep (se 1 (by rfl) ⟨189185, by rfl⟩ : syracuseStep 252247 = 378371) B378371
theorem B645655 : Blo 147793 645655 := bstep (se 1 (by rfl) ⟨484241, by rfl⟩ : syracuseStep 645655 = 968483) B968483
theorem B187211 : Blo 147793 187211 := bstep (se 1 (by rfl) ⟨140408, by rfl⟩ : syracuseStep 187211 = 280817) B280817
theorem B252875 : Blo 147793 252875 := bstep (se 1 (by rfl) ⟨189656, by rfl⟩ : syracuseStep 252875 = 379313) B379313
theorem B285707 : Blo 147793 285707 := bstep (se 1 (by rfl) ⟨214280, by rfl⟩ : syracuseStep 285707 = 428561) B428561
theorem B285761 : Blo 147793 285761 := bstep (se 2 (by rfl) ⟨107160, by rfl⟩ : syracuseStep 285761 = 214321) B214321
theorem B613441 : Blo 147793 613441 := bstep (se 2 (by rfl) ⟨230040, by rfl⟩ : syracuseStep 613441 = 460081) B460081
theorem B253003 : Blo 147793 253003 := bstep (se 1 (by rfl) ⟨189752, by rfl⟩ : syracuseStep 253003 = 379505) B379505
theorem B384203 : Blo 147793 384203 := bstep (se 1 (by rfl) ⟨288152, by rfl⟩ : syracuseStep 384203 = 576305) B576305
theorem B253145 : Blo 147793 253145 := bstep (se 2 (by rfl) ⟨94929, by rfl⟩ : syracuseStep 253145 = 189859) B189859
theorem B253273 : Blo 147793 253273 := bstep (se 2 (by rfl) ⟨94977, by rfl⟩ : syracuseStep 253273 = 189955) B189955
theorem B187915 : Blo 147793 187915 := bstep (se 1 (by rfl) ⟨140936, by rfl⟩ : syracuseStep 187915 = 281873) B281873
theorem B1138211 : Blo 147793 1138211 := bstep (se 1 (by rfl) ⟨853658, by rfl⟩ : syracuseStep 1138211 = 1707317) B1707317
theorem B319115 : Blo 147793 319115 := bstep (se 1 (by rfl) ⟨239336, by rfl⟩ : syracuseStep 319115 = 478673) B478673
theorem B188183 : Blo 147793 188183 := bstep (se 1 (by rfl) ⟨141137, by rfl⟩ : syracuseStep 188183 = 282275) B282275
theorem B778049 : Blo 147793 778049 := bstep (se 2 (by rfl) ⟨291768, by rfl⟩ : syracuseStep 778049 = 583537) B583537
theorem B253847 : Blo 147793 253847 := bstep (se 1 (by rfl) ⟨190385, by rfl⟩ : syracuseStep 253847 = 380771) B380771
theorem B286679 : Blo 147793 286679 := bstep (se 1 (by rfl) ⟨215009, by rfl⟩ : syracuseStep 286679 = 430019) B430019
theorem B253975 : Blo 147793 253975 := bstep (se 1 (by rfl) ⟨190481, by rfl⟩ : syracuseStep 253975 = 380963) B380963
theorem B286913 : Blo 147793 286913 := bstep (se 2 (by rfl) ⟨107592, by rfl⟩ : syracuseStep 286913 = 215185) B215185
theorem B647489 : Blo 147793 647489 := bstep (se 2 (by rfl) ⟨242808, by rfl⟩ : syracuseStep 647489 = 485617) B485617
theorem B188887 : Blo 147793 188887 := bstep (se 1 (by rfl) ⟨141665, by rfl⟩ : syracuseStep 188887 = 283331) B283331
theorem B287219 : Blo 147793 287219 := bstep (se 1 (by rfl) ⟨215414, by rfl⟩ : syracuseStep 287219 = 430829) B430829
theorem B221771 : Blo 147793 221771 := bstep (se 1 (by rfl) ⟨166328, by rfl⟩ : syracuseStep 221771 = 332657) B332657
theorem B909899 : Blo 147793 909899 := bstep (se 1 (by rfl) ⟨682424, by rfl⟩ : syracuseStep 909899 = 1364849) B1364849
theorem B221783 : Blo 147793 221783 := bstep (se 1 (by rfl) ⟨166337, by rfl⟩ : syracuseStep 221783 = 332675) B332675
theorem B254603 : Blo 147793 254603 := bstep (se 1 (by rfl) ⟨190952, by rfl⟩ : syracuseStep 254603 = 381905) B381905
theorem B647831 : Blo 147793 647831 := bstep (se 1 (by rfl) ⟨485873, by rfl⟩ : syracuseStep 647831 = 971747) B971747
theorem B221849 : Blo 147793 221849 := bstep (se 2 (by rfl) ⟨83193, by rfl⟩ : syracuseStep 221849 = 166387) B166387
theorem B221963 : Blo 147793 221963 := bstep (se 1 (by rfl) ⟨166472, by rfl⟩ : syracuseStep 221963 = 332945) B332945
theorem B254731 : Blo 147793 254731 := bstep (se 1 (by rfl) ⟨191048, by rfl⟩ : syracuseStep 254731 = 382097) B382097
theorem B221975 : Blo 147793 221975 := bstep (se 1 (by rfl) ⟨166481, by rfl⟩ : syracuseStep 221975 = 332963) B332963
theorem B3662657 : Blo 147793 3662657 := bstep (se 2 (by rfl) ⟨1373496, by rfl⟩ : syracuseStep 3662657 = 2746993) B2746993
theorem B222041 : Blo 147793 222041 := bstep (se 2 (by rfl) ⟨83265, by rfl⟩ : syracuseStep 222041 = 166531) B166531
theorem B320345 : Blo 147793 320345 := bstep (se 2 (by rfl) ⟨120129, by rfl⟩ : syracuseStep 320345 = 240259) B240259
theorem B254873 : Blo 147793 254873 := bstep (se 2 (by rfl) ⟨95577, by rfl⟩ : syracuseStep 254873 = 191155) B191155
theorem B222155 : Blo 147793 222155 := bstep (se 1 (by rfl) ⟨166616, by rfl⟩ : syracuseStep 222155 = 333233) B333233
theorem B222167 : Blo 147793 222167 := bstep (se 1 (by rfl) ⟨166625, by rfl⟩ : syracuseStep 222167 = 333251) B333251
theorem B287705 : Blo 147793 287705 := bstep (se 2 (by rfl) ⟨107889, by rfl⟩ : syracuseStep 287705 = 215779) B215779
theorem B484375 : Blo 147793 484375 := bstep (se 1 (by rfl) ⟨363281, by rfl⟩ : syracuseStep 484375 = 726563) B726563
theorem B222233 : Blo 147793 222233 := bstep (se 2 (by rfl) ⟨83337, by rfl⟩ : syracuseStep 222233 = 166675) B166675
theorem B255001 : Blo 147793 255001 := bstep (se 2 (by rfl) ⟨95625, by rfl⟩ : syracuseStep 255001 = 191251) B191251
theorem B222347 : Blo 147793 222347 := bstep (se 1 (by rfl) ⟨166760, by rfl⟩ : syracuseStep 222347 = 333521) B333521
theorem B222359 : Blo 147793 222359 := bstep (se 1 (by rfl) ⟨166769, by rfl⟩ : syracuseStep 222359 = 333539) B333539
theorem B222425 : Blo 147793 222425 := bstep (se 2 (by rfl) ⟨83409, by rfl⟩ : syracuseStep 222425 = 166819) B166819
theorem B320755 : Blo 147793 320755 := bstep (se 1 (by rfl) ⟨240566, by rfl⟩ : syracuseStep 320755 = 481133) B481133
theorem B222539 : Blo 147793 222539 := bstep (se 1 (by rfl) ⟨166904, by rfl⟩ : syracuseStep 222539 = 333809) B333809
theorem B222551 : Blo 147793 222551 := bstep (se 1 (by rfl) ⟨166913, by rfl⟩ : syracuseStep 222551 = 333827) B333827
theorem B222617 : Blo 147793 222617 := bstep (se 2 (by rfl) ⟨83481, by rfl⟩ : syracuseStep 222617 = 166963) B166963
theorem B321011 : Blo 147793 321011 := bstep (se 1 (by rfl) ⟨240758, by rfl⟩ : syracuseStep 321011 = 481517) B481517
theorem B222731 : Blo 147793 222731 := bstep (se 1 (by rfl) ⟨167048, by rfl⟩ : syracuseStep 222731 = 334097) B334097
theorem B222743 : Blo 147793 222743 := bstep (se 1 (by rfl) ⟨167057, by rfl⟩ : syracuseStep 222743 = 334115) B334115
theorem B255575 : Blo 147793 255575 := bstep (se 1 (by rfl) ⟨191681, by rfl⟩ : syracuseStep 255575 = 383363) B383363
theorem B222809 : Blo 147793 222809 := bstep (se 2 (by rfl) ⟨83553, by rfl⟩ : syracuseStep 222809 = 167107) B167107
theorem B222923 : Blo 147793 222923 := bstep (se 1 (by rfl) ⟨167192, by rfl⟩ : syracuseStep 222923 = 334385) B334385
theorem B222935 : Blo 147793 222935 := bstep (se 1 (by rfl) ⟨167201, by rfl⟩ : syracuseStep 222935 = 334403) B334403
theorem B255703 : Blo 147793 255703 := bstep (se 1 (by rfl) ⟨191777, by rfl⟩ : syracuseStep 255703 = 383555) B383555
theorem B386839 : Blo 147793 386839 := bstep (se 1 (by rfl) ⟨290129, by rfl⟩ : syracuseStep 386839 = 580259) B580259
theorem B223001 : Blo 147793 223001 := bstep (se 2 (by rfl) ⟨83625, by rfl⟩ : syracuseStep 223001 = 167251) B167251
theorem B223115 : Blo 147793 223115 := bstep (se 1 (by rfl) ⟨167336, by rfl⟩ : syracuseStep 223115 = 334673) B334673
theorem B223127 : Blo 147793 223127 := bstep (se 1 (by rfl) ⟨167345, by rfl⟩ : syracuseStep 223127 = 334691) B334691
theorem B1370033 : Blo 147793 1370033 := bstep (se 2 (by rfl) ⟨513762, by rfl⟩ : syracuseStep 1370033 = 1027525) B1027525
theorem B223193 : Blo 147793 223193 := bstep (se 2 (by rfl) ⟨83697, by rfl⟩ : syracuseStep 223193 = 167395) B167395
theorem B223307 : Blo 147793 223307 := bstep (se 1 (by rfl) ⟨167480, by rfl⟩ : syracuseStep 223307 = 334961) B334961
theorem B223319 : Blo 147793 223319 := bstep (se 1 (by rfl) ⟨167489, by rfl⟩ : syracuseStep 223319 = 334979) B334979
theorem B190603 : Blo 147793 190603 := bstep (se 1 (by rfl) ⟨142952, by rfl⟩ : syracuseStep 190603 = 285905) B285905
theorem B223385 : Blo 147793 223385 := bstep (se 2 (by rfl) ⟨83769, by rfl⟩ : syracuseStep 223385 = 167539) B167539
theorem B223499 : Blo 147793 223499 := bstep (se 1 (by rfl) ⟨167624, by rfl⟩ : syracuseStep 223499 = 335249) B335249
theorem B223511 : Blo 147793 223511 := bstep (se 1 (by rfl) ⟨167633, by rfl⟩ : syracuseStep 223511 = 335267) B335267
theorem B223577 : Blo 147793 223577 := bstep (se 2 (by rfl) ⟨83841, by rfl⟩ : syracuseStep 223577 = 167683) B167683
theorem B321985 : Blo 147793 321985 := bstep (se 2 (by rfl) ⟨120744, by rfl⟩ : syracuseStep 321985 = 241489) B241489
theorem B223691 : Blo 147793 223691 := bstep (se 1 (by rfl) ⟨167768, by rfl⟩ : syracuseStep 223691 = 335537) B335537
theorem B223703 : Blo 147793 223703 := bstep (se 1 (by rfl) ⟨167777, by rfl⟩ : syracuseStep 223703 = 335555) B335555
theorem B223769 : Blo 147793 223769 := bstep (se 2 (by rfl) ⟨83913, by rfl⟩ : syracuseStep 223769 = 167827) B167827
theorem B223883 : Blo 147793 223883 := bstep (se 1 (by rfl) ⟨167912, by rfl⟩ : syracuseStep 223883 = 335825) B335825
theorem B223895 : Blo 147793 223895 := bstep (se 1 (by rfl) ⟨167921, by rfl⟩ : syracuseStep 223895 = 335843) B335843
theorem B223961 : Blo 147793 223961 := bstep (se 2 (by rfl) ⟨83985, by rfl⟩ : syracuseStep 223961 = 167971) B167971
theorem B158455 : Blo 147793 158455 := bstep (se 1 (by rfl) ⟨118841, by rfl⟩ : syracuseStep 158455 = 237683) B237683
theorem B224075 : Blo 147793 224075 := bstep (se 1 (by rfl) ⟨168056, by rfl⟩ : syracuseStep 224075 = 336113) B336113
theorem B224087 : Blo 147793 224087 := bstep (se 1 (by rfl) ⟨168065, by rfl⟩ : syracuseStep 224087 = 336131) B336131
theorem B486233 : Blo 147793 486233 := bstep (se 2 (by rfl) ⟨182337, by rfl⟩ : syracuseStep 486233 = 364675) B364675
theorem B748439 : Blo 147793 748439 := bstep (se 1 (by rfl) ⟨561329, by rfl⟩ : syracuseStep 748439 = 1122659) B1122659
theorem B224153 : Blo 147793 224153 := bstep (se 2 (by rfl) ⟨84057, by rfl⟩ : syracuseStep 224153 = 168115) B168115
theorem B158635 : Blo 147793 158635 := bstep (se 1 (by rfl) ⟨118976, by rfl⟩ : syracuseStep 158635 = 237953) B237953
theorem B322483 : Blo 147793 322483 := bstep (se 1 (by rfl) ⟨241862, by rfl⟩ : syracuseStep 322483 = 483725) B483725
theorem B224267 : Blo 147793 224267 := bstep (se 1 (by rfl) ⟨168200, by rfl⟩ : syracuseStep 224267 = 336401) B336401
theorem B224279 : Blo 147793 224279 := bstep (se 1 (by rfl) ⟨168209, by rfl⟩ : syracuseStep 224279 = 336419) B336419
theorem B191575 : Blo 147793 191575 := bstep (se 1 (by rfl) ⟨143681, by rfl⟩ : syracuseStep 191575 = 287363) B287363
theorem B224345 : Blo 147793 224345 := bstep (se 2 (by rfl) ⟨84129, by rfl⟩ : syracuseStep 224345 = 168259) B168259
theorem B224459 : Blo 147793 224459 := bstep (se 1 (by rfl) ⟨168344, by rfl⟩ : syracuseStep 224459 = 336689) B336689
theorem B224471 : Blo 147793 224471 := bstep (se 1 (by rfl) ⟨168353, by rfl⟩ : syracuseStep 224471 = 336707) B336707
theorem B453853 : Blo 147793 453853 := bstep (se 3 (by rfl) ⟨85097, by rfl⟩ : syracuseStep 453853 = 170195) B170195
theorem B1240337 : Blo 147793 1240337 := bstep (se 2 (by rfl) ⟨465126, by rfl⟩ : syracuseStep 1240337 = 930253) B930253
theorem B224537 : Blo 147793 224537 := bstep (se 2 (by rfl) ⟨84201, by rfl⟩ : syracuseStep 224537 = 168403) B168403
theorem B781643 : Blo 147793 781643 := bstep (se 1 (by rfl) ⟨586232, by rfl⟩ : syracuseStep 781643 = 1172465) B1172465
theorem B224651 : Blo 147793 224651 := bstep (se 1 (by rfl) ⟨168488, by rfl⟩ : syracuseStep 224651 = 336977) B336977
theorem B421271 : Blo 147793 421271 := bstep (se 1 (by rfl) ⟨315953, by rfl⟩ : syracuseStep 421271 = 631907) B631907
theorem B224663 : Blo 147793 224663 := bstep (se 1 (by rfl) ⟨168497, by rfl⟩ : syracuseStep 224663 = 336995) B336995
theorem B224729 : Blo 147793 224729 := bstep (se 2 (by rfl) ⟨84273, by rfl⟩ : syracuseStep 224729 = 168547) B168547
theorem B224843 : Blo 147793 224843 := bstep (se 1 (by rfl) ⟨168632, by rfl⟩ : syracuseStep 224843 = 337265) B337265
theorem B224855 : Blo 147793 224855 := bstep (se 1 (by rfl) ⟨168641, by rfl⟩ : syracuseStep 224855 = 337283) B337283
theorem B224921 : Blo 147793 224921 := bstep (se 2 (by rfl) ⟨84345, by rfl⟩ : syracuseStep 224921 = 168691) B168691
theorem B225035 : Blo 147793 225035 := bstep (se 1 (by rfl) ⟨168776, by rfl⟩ : syracuseStep 225035 = 337553) B337553
theorem B225047 : Blo 147793 225047 := bstep (se 1 (by rfl) ⟨168785, by rfl⟩ : syracuseStep 225047 = 337571) B337571
theorem B847691 : Blo 147793 847691 := bstep (se 1 (by rfl) ⟨635768, by rfl⟩ : syracuseStep 847691 = 1271537) B1271537
theorem B225113 : Blo 147793 225113 := bstep (se 2 (by rfl) ⟨84417, by rfl⟩ : syracuseStep 225113 = 168835) B168835
theorem B225227 : Blo 147793 225227 := bstep (se 1 (by rfl) ⟨168920, by rfl⟩ : syracuseStep 225227 = 337841) B337841
theorem B225239 : Blo 147793 225239 := bstep (se 1 (by rfl) ⟨168929, by rfl⟩ : syracuseStep 225239 = 337859) B337859
theorem B225305 : Blo 147793 225305 := bstep (se 2 (by rfl) ⟨84489, by rfl⟩ : syracuseStep 225305 = 168979) B168979
theorem B225419 : Blo 147793 225419 := bstep (se 1 (by rfl) ⟨169064, by rfl⟩ : syracuseStep 225419 = 338129) B338129
theorem B225431 : Blo 147793 225431 := bstep (se 1 (by rfl) ⟨169073, by rfl⟩ : syracuseStep 225431 = 338147) B338147
theorem B422081 : Blo 147793 422081 := bstep (se 2 (by rfl) ⟨158280, by rfl⟩ : syracuseStep 422081 = 316561) B316561
theorem B225497 : Blo 147793 225497 := bstep (se 2 (by rfl) ⟨84561, by rfl⟩ : syracuseStep 225497 = 169123) B169123
theorem B225611 : Blo 147793 225611 := bstep (se 1 (by rfl) ⟨169208, by rfl⟩ : syracuseStep 225611 = 338417) B338417
theorem B225623 : Blo 147793 225623 := bstep (se 1 (by rfl) ⟨169217, by rfl⟩ : syracuseStep 225623 = 338435) B338435
theorem B225689 : Blo 147793 225689 := bstep (se 2 (by rfl) ⟨84633, by rfl⟩ : syracuseStep 225689 = 169267) B169267
theorem B225803 : Blo 147793 225803 := bstep (se 1 (by rfl) ⟨169352, by rfl⟩ : syracuseStep 225803 = 338705) B338705
theorem B225815 : Blo 147793 225815 := bstep (se 1 (by rfl) ⟨169361, by rfl⟩ : syracuseStep 225815 = 338723) B338723
theorem B324121 : Blo 147793 324121 := bstep (se 2 (by rfl) ⟨121545, by rfl⟩ : syracuseStep 324121 = 243091) B243091
theorem B258647 : Blo 147793 258647 := bstep (se 1 (by rfl) ⟨193985, by rfl⟩ : syracuseStep 258647 = 387971) B387971
theorem B225881 : Blo 147793 225881 := bstep (se 2 (by rfl) ⟨84705, by rfl⟩ : syracuseStep 225881 = 169411) B169411
theorem B815717 : Blo 147793 815717 := bstep (se 4 (by rfl) ⟨76473, by rfl⟩ : syracuseStep 815717 = 152947) B152947
theorem B225995 : Blo 147793 225995 := bstep (se 1 (by rfl) ⟨169496, by rfl⟩ : syracuseStep 225995 = 338993) B338993
theorem B226007 : Blo 147793 226007 := bstep (se 1 (by rfl) ⟨169505, by rfl⟩ : syracuseStep 226007 = 339011) B339011
theorem B1143557 : Blo 147793 1143557 := bstep (se 4 (by rfl) ⟨107208, by rfl⟩ : syracuseStep 1143557 = 214417) B214417
theorem B226073 : Blo 147793 226073 := bstep (se 2 (by rfl) ⟨84777, by rfl⟩ : syracuseStep 226073 = 169555) B169555
theorem B1471277 : Blo 147793 1471277 := bstep (se 3 (by rfl) ⟨275864, by rfl⟩ : syracuseStep 1471277 = 551729) B551729
theorem B1078109 : Blo 147793 1078109 := bstep (se 3 (by rfl) ⟨202145, by rfl⟩ : syracuseStep 1078109 = 404291) B404291
theorem B160651 : Blo 147793 160651 := bstep (se 1 (by rfl) ⟨120488, by rfl⟩ : syracuseStep 160651 = 240977) B240977
theorem B226187 : Blo 147793 226187 := bstep (se 1 (by rfl) ⟨169640, by rfl⟩ : syracuseStep 226187 = 339281) B339281
theorem B914327 : Blo 147793 914327 := bstep (se 1 (by rfl) ⟨685745, by rfl⟩ : syracuseStep 914327 = 1371491) B1371491
theorem B226199 : Blo 147793 226199 := bstep (se 1 (by rfl) ⟨169649, by rfl⟩ : syracuseStep 226199 = 339299) B339299
theorem B652205 : Blo 147793 652205 := bstep (se 3 (by rfl) ⟨122288, by rfl⟩ : syracuseStep 652205 = 244577) B244577
theorem B357313 : Blo 147793 357313 := bstep (se 2 (by rfl) ⟨133992, by rfl⟩ : syracuseStep 357313 = 267985) B267985
theorem B226265 : Blo 147793 226265 := bstep (se 2 (by rfl) ⟨84849, by rfl⟩ : syracuseStep 226265 = 169699) B169699
theorem B1274885 : Blo 147793 1274885 := bstep (se 4 (by rfl) ⟨119520, by rfl⟩ : syracuseStep 1274885 = 239041) B239041
theorem B226379 : Blo 147793 226379 := bstep (se 1 (by rfl) ⟨169784, by rfl⟩ : syracuseStep 226379 = 339569) B339569
theorem B226391 : Blo 147793 226391 := bstep (se 1 (by rfl) ⟨169793, by rfl⟩ : syracuseStep 226391 = 339587) B339587
theorem B226457 : Blo 147793 226457 := bstep (se 2 (by rfl) ⟨84921, by rfl⟩ : syracuseStep 226457 = 169843) B169843
theorem B226571 : Blo 147793 226571 := bstep (se 1 (by rfl) ⟨169928, by rfl⟩ : syracuseStep 226571 = 339857) B339857
theorem B226583 : Blo 147793 226583 := bstep (se 1 (by rfl) ⟨169937, by rfl⟩ : syracuseStep 226583 = 339875) B339875
theorem B226649 : Blo 147793 226649 := bstep (se 2 (by rfl) ⟨84993, by rfl⟩ : syracuseStep 226649 = 169987) B169987
theorem B226763 : Blo 147793 226763 := bstep (se 1 (by rfl) ⟨170072, by rfl⟩ : syracuseStep 226763 = 340145) B340145
theorem B226775 : Blo 147793 226775 := bstep (se 1 (by rfl) ⟨170081, by rfl⟩ : syracuseStep 226775 = 340163) B340163
theorem B226841 : Blo 147793 226841 := bstep (se 2 (by rfl) ⟨85065, by rfl⟩ : syracuseStep 226841 = 170131) B170131
theorem B226891 : Blo 147793 226891 := bstep (se 1 (by rfl) ⟨170168, by rfl⟩ : syracuseStep 226891 = 340337) B340337
theorem B1078859 : Blo 147793 1078859 := bstep (se 1 (by rfl) ⟨809144, by rfl⟩ : syracuseStep 1078859 = 1618289) B1618289
theorem B226955 : Blo 147793 226955 := bstep (se 1 (by rfl) ⟨170216, by rfl⟩ : syracuseStep 226955 = 340433) B340433
theorem B226967 : Blo 147793 226967 := bstep (se 1 (by rfl) ⟨170225, by rfl⟩ : syracuseStep 226967 = 340451) B340451
theorem B227033 : Blo 147793 227033 := bstep (se 2 (by rfl) ⟨85137, by rfl⟩ : syracuseStep 227033 = 170275) B170275
theorem B423731 : Blo 147793 423731 := bstep (se 1 (by rfl) ⟨317798, by rfl⟩ : syracuseStep 423731 = 635597) B635597
theorem B423755 : Blo 147793 423755 := bstep (se 1 (by rfl) ⟨317816, by rfl⟩ : syracuseStep 423755 = 635633) B635633
theorem B227147 : Blo 147793 227147 := bstep (se 1 (by rfl) ⟨170360, by rfl⟩ : syracuseStep 227147 = 340721) B340721
theorem B227159 : Blo 147793 227159 := bstep (se 1 (by rfl) ⟨170369, by rfl⟩ : syracuseStep 227159 = 340739) B340739
theorem B227225 : Blo 147793 227225 := bstep (se 2 (by rfl) ⟨85209, by rfl⟩ : syracuseStep 227225 = 170419) B170419
theorem B358361 : Blo 147793 358361 := bstep (se 2 (by rfl) ⟨134385, by rfl⟩ : syracuseStep 358361 = 268771) B268771
theorem B227339 : Blo 147793 227339 := bstep (se 1 (by rfl) ⟨170504, by rfl⟩ : syracuseStep 227339 = 341009) B341009
theorem B227351 : Blo 147793 227351 := bstep (se 1 (by rfl) ⟨170513, by rfl⟩ : syracuseStep 227351 = 341027) B341027
theorem B227417 : Blo 147793 227417 := bstep (se 2 (by rfl) ⟨85281, by rfl⟩ : syracuseStep 227417 = 170563) B170563
theorem B227531 : Blo 147793 227531 := bstep (se 1 (by rfl) ⟨170648, by rfl⟩ : syracuseStep 227531 = 341297) B341297
theorem B227543 : Blo 147793 227543 := bstep (se 1 (by rfl) ⟨170657, by rfl⟩ : syracuseStep 227543 = 341315) B341315
theorem B227609 : Blo 147793 227609 := bstep (se 2 (by rfl) ⟨85353, by rfl⟩ : syracuseStep 227609 = 170707) B170707
theorem B1964405 : Blo 147793 1964405 := bstep (se 5 (by rfl) ⟨92081, by rfl⟩ : syracuseStep 1964405 = 184163) B184163
theorem B752003 : Blo 147793 752003 := bstep (se 1 (by rfl) ⟨564002, by rfl⟩ : syracuseStep 752003 = 1128005) B1128005
theorem B2062883 : Blo 147793 2062883 := bstep (se 1 (by rfl) ⟨1547162, by rfl⟩ : syracuseStep 2062883 = 3094325) B3094325
theorem B424541 : Blo 147793 424541 := bstep (se 3 (by rfl) ⟨79601, by rfl⟩ : syracuseStep 424541 = 159203) B159203
theorem B1080013 : Blo 147793 1080013 := bstep (se 3 (by rfl) ⟨202502, by rfl⟩ : syracuseStep 1080013 = 405005) B405005
theorem B949067 : Blo 147793 949067 := bstep (se 1 (by rfl) ⟨711800, by rfl⟩ : syracuseStep 949067 = 1423601) B1423601
theorem B818099 : Blo 147793 818099 := bstep (se 1 (by rfl) ⟨613574, by rfl⟩ : syracuseStep 818099 = 1227149) B1227149
theorem B1145987 : Blo 147793 1145987 := bstep (se 1 (by rfl) ⟨859490, by rfl⟩ : syracuseStep 1145987 = 1718981) B1718981
theorem B228491 : Blo 147793 228491 := bstep (se 1 (by rfl) ⟨171368, by rfl⟩ : syracuseStep 228491 = 342737) B342737
theorem B360215 : Blo 147793 360215 := bstep (se 1 (by rfl) ⟨270161, by rfl⟩ : syracuseStep 360215 = 540323) B540323
theorem B2916161 : Blo 147793 2916161 := bstep (se 2 (by rfl) ⟨1093560, by rfl⟩ : syracuseStep 2916161 = 2187121) B2187121
theorem B425999 : Blo 147793 425999 := bstep (se 1 (by rfl) ⟨319499, by rfl⟩ : syracuseStep 425999 = 638999) B638999
theorem B1900745 : Blo 147793 1900745 := bstep (se 2 (by rfl) ⟨712779, by rfl⟩ : syracuseStep 1900745 = 1425559) B1425559
theorem B360715 : Blo 147793 360715 := bstep (se 1 (by rfl) ⟨270536, by rfl⟩ : syracuseStep 360715 = 541073) B541073
theorem B1704401 : Blo 147793 1704401 := bstep (se 2 (by rfl) ⟨639150, by rfl⟩ : syracuseStep 1704401 = 1278301) B1278301
theorem B754433 : Blo 147793 754433 := bstep (se 2 (by rfl) ⟨282912, by rfl⟩ : syracuseStep 754433 = 565825) B565825
theorem B361331 : Blo 147793 361331 := bstep (se 1 (by rfl) ⟨270998, by rfl⟩ : syracuseStep 361331 = 541997) B541997
theorem B19104709 : Blo 147793 19104709 := bstep (se 4 (by rfl) ⟨1791066, by rfl⟩ : syracuseStep 19104709 = 3582133) B3582133
theorem B755243 : Blo 147793 755243 := bstep (se 1 (by rfl) ⟨566432, by rfl⟩ : syracuseStep 755243 = 1132865) B1132865
theorem B689725 : Blo 147793 689725 := bstep (se 3 (by rfl) ⟨129323, by rfl⟩ : syracuseStep 689725 = 258647) B258647
theorem B427639 : Blo 147793 427639 := bstep (se 1 (by rfl) ⟨320729, by rfl⟩ : syracuseStep 427639 = 641459) B641459
theorem B427673 : Blo 147793 427673 := bstep (se 2 (by rfl) ⟨160377, by rfl⟩ : syracuseStep 427673 = 320755) B320755
theorem B362137 : Blo 147793 362137 := bstep (se 2 (by rfl) ⟨135801, by rfl⟩ : syracuseStep 362137 = 271603) B271603
theorem B427787 : Blo 147793 427787 := bstep (se 1 (by rfl) ⟨320840, by rfl⟩ : syracuseStep 427787 = 641681) B641681
theorem B460859 : Blo 147793 460859 := bstep (se 1 (by rfl) ⟨345644, by rfl⟩ : syracuseStep 460859 = 691289) B691289
theorem B1444013 : Blo 147793 1444013 := bstep (se 3 (by rfl) ⟨270752, by rfl⟩ : syracuseStep 1444013 = 541505) B541505
theorem B330043 : Blo 147793 330043 := bstep (se 1 (by rfl) ⟨247532, by rfl⟩ : syracuseStep 330043 = 495065) B495065
theorem B166279 : Blo 147793 166279 := bstep (se 1 (by rfl) ⟨124709, by rfl⟩ : syracuseStep 166279 = 249419) B249419
theorem B166459 : Blo 147793 166459 := bstep (se 1 (by rfl) ⟨124844, by rfl⟩ : syracuseStep 166459 = 249689) B249689
theorem B461447 : Blo 147793 461447 := bstep (se 1 (by rfl) ⟨346085, by rfl⟩ : syracuseStep 461447 = 692171) B692171
theorem B6195973 : Blo 147793 6195973 := bstep (se 4 (by rfl) ⟨580872, by rfl⟩ : syracuseStep 6195973 = 1161745) B1161745
theorem B920335 : Blo 147793 920335 := bstep (se 1 (by rfl) ⟨690251, by rfl⟩ : syracuseStep 920335 = 1380503) B1380503
theorem B756539 : Blo 147793 756539 := bstep (se 1 (by rfl) ⟨567404, by rfl⟩ : syracuseStep 756539 = 1134809) B1134809
theorem B428915 : Blo 147793 428915 := bstep (se 1 (by rfl) ⟨321686, by rfl⟩ : syracuseStep 428915 = 643373) B643373
theorem B756701 : Blo 147793 756701 := bstep (se 3 (by rfl) ⟨141881, by rfl⟩ : syracuseStep 756701 = 283763) B283763
theorem B1281035 : Blo 147793 1281035 := bstep (se 1 (by rfl) ⟨960776, by rfl⟩ : syracuseStep 1281035 = 1921553) B1921553
theorem B166927 : Blo 147793 166927 := bstep (se 1 (by rfl) ⟨125195, by rfl⟩ : syracuseStep 166927 = 250391) B250391
theorem B429313 : Blo 147793 429313 := bstep (se 2 (by rfl) ⟨160992, by rfl⟩ : syracuseStep 429313 = 321985) B321985
theorem B363791 : Blo 147793 363791 := bstep (se 1 (by rfl) ⟨272843, by rfl⟩ : syracuseStep 363791 = 545687) B545687
theorem B757025 : Blo 147793 757025 := bstep (se 2 (by rfl) ⟨283884, by rfl⟩ : syracuseStep 757025 = 567769) B567769
theorem B429371 : Blo 147793 429371 := bstep (se 1 (by rfl) ⟨322028, by rfl⟩ : syracuseStep 429371 = 644057) B644057
theorem B855481 : Blo 147793 855481 := bstep (se 2 (by rfl) ⟨320805, by rfl⟩ : syracuseStep 855481 = 641611) B641611
theorem B167431 : Blo 147793 167431 := bstep (se 1 (by rfl) ⟨125573, by rfl⟩ : syracuseStep 167431 = 251147) B251147
theorem B167611 : Blo 147793 167611 := bstep (se 1 (by rfl) ⟨125708, by rfl⟩ : syracuseStep 167611 = 251417) B251417
theorem B724717 : Blo 147793 724717 := bstep (se 3 (by rfl) ⟨135884, by rfl⟩ : syracuseStep 724717 = 271769) B271769
theorem B2723635 : Blo 147793 2723635 := bstep (se 1 (by rfl) ⟨2042726, by rfl⟩ : syracuseStep 2723635 = 4085453) B4085453
theorem B429977 : Blo 147793 429977 := bstep (se 2 (by rfl) ⟨161241, by rfl⟩ : syracuseStep 429977 = 322483) B322483
theorem B724889 : Blo 147793 724889 := bstep (se 2 (by rfl) ⟨271833, by rfl⟩ : syracuseStep 724889 = 543667) B543667
theorem B561239 : Blo 147793 561239 := bstep (se 1 (by rfl) ⟨420929, by rfl⟩ : syracuseStep 561239 = 841859) B841859
theorem B6951005 : Blo 147793 6951005 := bstep (se 3 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 6951005 = 2606627) B2606627
theorem B168079 : Blo 147793 168079 := bstep (se 1 (by rfl) ⟨126059, by rfl⟩ : syracuseStep 168079 = 252119) B252119
theorem B200891 : Blo 147793 200891 := bstep (se 1 (by rfl) ⟨150668, by rfl⟩ : syracuseStep 200891 = 301337) B301337
theorem B757997 : Blo 147793 757997 := bstep (se 3 (by rfl) ⟨142124, by rfl⟩ : syracuseStep 757997 = 284249) B284249
theorem B3543587 : Blo 147793 3543587 := bstep (se 1 (by rfl) ⟨2657690, by rfl⟩ : syracuseStep 3543587 = 5315381) B5315381
theorem B561725 : Blo 147793 561725 := bstep (se 3 (by rfl) ⟨105323, by rfl⟩ : syracuseStep 561725 = 210647) B210647
theorem B168583 : Blo 147793 168583 := bstep (se 1 (by rfl) ⟨126437, by rfl⟩ : syracuseStep 168583 = 252875) B252875
theorem B332603 : Blo 147793 332603 := bstep (se 1 (by rfl) ⟨249452, by rfl⟩ : syracuseStep 332603 = 498905) B498905
theorem B168763 : Blo 147793 168763 := bstep (se 1 (by rfl) ⟨126572, by rfl⟩ : syracuseStep 168763 = 253145) B253145
theorem B332729 : Blo 147793 332729 := bstep (se 2 (by rfl) ⟨124773, by rfl⟩ : syracuseStep 332729 = 249547) B249547
theorem B758807 : Blo 147793 758807 := bstep (se 1 (by rfl) ⟨569105, by rfl⟩ : syracuseStep 758807 = 1138211) B1138211
theorem B333071 : Blo 147793 333071 := bstep (se 1 (by rfl) ⟨249803, by rfl⟩ : syracuseStep 333071 = 499607) B499607
theorem B169231 : Blo 147793 169231 := bstep (se 1 (by rfl) ⟨126923, by rfl⟩ : syracuseStep 169231 = 253847) B253847
theorem B333089 : Blo 147793 333089 := bstep (se 2 (by rfl) ⟨124908, by rfl⟩ : syracuseStep 333089 = 249817) B249817
theorem B3478963 : Blo 147793 3478963 := bstep (se 1 (by rfl) ⟨2609222, by rfl⟩ : syracuseStep 3478963 = 5218445) B5218445
theorem B431659 : Blo 147793 431659 := bstep (se 1 (by rfl) ⟨323744, by rfl⟩ : syracuseStep 431659 = 647489) B647489
theorem B333431 : Blo 147793 333431 := bstep (se 1 (by rfl) ⟨250073, by rfl⟩ : syracuseStep 333431 = 500147) B500147
theorem B169735 : Blo 147793 169735 := bstep (se 1 (by rfl) ⟨127301, by rfl⟩ : syracuseStep 169735 = 254603) B254603
theorem B431887 : Blo 147793 431887 := bstep (se 1 (by rfl) ⟨323915, by rfl⟩ : syracuseStep 431887 = 647831) B647831
theorem B333611 : Blo 147793 333611 := bstep (se 1 (by rfl) ⟨250208, by rfl⟩ : syracuseStep 333611 = 500417) B500417
theorem B169915 : Blo 147793 169915 := bstep (se 1 (by rfl) ⟨127436, by rfl⟩ : syracuseStep 169915 = 254873) B254873
theorem B432161 : Blo 147793 432161 := bstep (se 2 (by rfl) ⟨162060, by rfl⟩ : syracuseStep 432161 = 324121) B324121
theorem B333971 : Blo 147793 333971 := bstep (se 1 (by rfl) ⟨250478, by rfl⟩ : syracuseStep 333971 = 500957) B500957
theorem B334025 : Blo 147793 334025 := bstep (se 2 (by rfl) ⟨125259, by rfl⟩ : syracuseStep 334025 = 250519) B250519
theorem B170383 : Blo 147793 170383 := bstep (se 1 (by rfl) ⟨127787, by rfl⟩ : syracuseStep 170383 = 255575) B255575
theorem B367001 : Blo 147793 367001 := bstep (se 2 (by rfl) ⟨137625, by rfl⟩ : syracuseStep 367001 = 275251) B275251
theorem B203195 : Blo 147793 203195 := bstep (se 1 (by rfl) ⟨152396, by rfl⟩ : syracuseStep 203195 = 304793) B304793
theorem B334727 : Blo 147793 334727 := bstep (se 1 (by rfl) ⟨251045, by rfl⟩ : syracuseStep 334727 = 502091) B502091
theorem B334907 : Blo 147793 334907 := bstep (se 1 (by rfl) ⟨251180, by rfl⟩ : syracuseStep 334907 = 502361) B502361
theorem B335033 : Blo 147793 335033 := bstep (se 2 (by rfl) ⟨125637, by rfl⟩ : syracuseStep 335033 = 251275) B251275
theorem B1449161 : Blo 147793 1449161 := bstep (se 2 (by rfl) ⟨543435, by rfl⟩ : syracuseStep 1449161 = 1086871) B1086871
theorem B498959 : Blo 147793 498959 := bstep (se 1 (by rfl) ⟨374219, by rfl⟩ : syracuseStep 498959 = 748439) B748439
theorem B1285409 : Blo 147793 1285409 := bstep (se 2 (by rfl) ⟨482028, by rfl⟩ : syracuseStep 1285409 = 964057) B964057
theorem B597401 : Blo 147793 597401 := bstep (se 2 (by rfl) ⟨224025, by rfl⟩ : syracuseStep 597401 = 448051) B448051
theorem B826891 : Blo 147793 826891 := bstep (se 1 (by rfl) ⟨620168, by rfl⟩ : syracuseStep 826891 = 1240337) B1240337
theorem B335375 : Blo 147793 335375 := bstep (se 1 (by rfl) ⟨251531, by rfl⟩ : syracuseStep 335375 = 503063) B503063
theorem B499229 : Blo 147793 499229 := bstep (se 3 (by rfl) ⟨93605, by rfl⟩ : syracuseStep 499229 = 187211) B187211
theorem B335393 : Blo 147793 335393 := bstep (se 2 (by rfl) ⟨125772, by rfl⟩ : syracuseStep 335393 = 251545) B251545
theorem B269867 : Blo 147793 269867 := bstep (se 1 (by rfl) ⟨202400, by rfl⟩ : syracuseStep 269867 = 404801) B404801
theorem B335735 : Blo 147793 335735 := bstep (se 1 (by rfl) ⟨251801, by rfl⟩ : syracuseStep 335735 = 503603) B503603
theorem B565127 : Blo 147793 565127 := bstep (se 1 (by rfl) ⟨423845, by rfl⟩ : syracuseStep 565127 = 847691) B847691
theorem B761885 : Blo 147793 761885 := bstep (se 3 (by rfl) ⟨142853, by rfl⟩ : syracuseStep 761885 = 285707) B285707
theorem B335915 : Blo 147793 335915 := bstep (se 1 (by rfl) ⟨251936, by rfl⟩ : syracuseStep 335915 = 503873) B503873
theorem B336275 : Blo 147793 336275 := bstep (se 1 (by rfl) ⟨252206, by rfl⟩ : syracuseStep 336275 = 504413) B504413
theorem B336329 : Blo 147793 336329 := bstep (se 2 (by rfl) ⟨126123, by rfl⟩ : syracuseStep 336329 = 252247) B252247
theorem B762371 : Blo 147793 762371 := bstep (se 1 (by rfl) ⟨571778, by rfl⟩ : syracuseStep 762371 = 1143557) B1143557
theorem B434803 : Blo 147793 434803 := bstep (se 1 (by rfl) ⟨326102, by rfl⟩ : syracuseStep 434803 = 652205) B652205
theorem B270983 : Blo 147793 270983 := bstep (se 1 (by rfl) ⟨203237, by rfl⟩ : syracuseStep 270983 = 406475) B406475
theorem B860873 : Blo 147793 860873 := bstep (se 2 (by rfl) ⟨322827, by rfl⟩ : syracuseStep 860873 = 645655) B645655
theorem B500633 : Blo 147793 500633 := bstep (se 2 (by rfl) ⟨187737, by rfl⟩ : syracuseStep 500633 = 375475) B375475
theorem B861131 : Blo 147793 861131 := bstep (se 1 (by rfl) ⟨645848, by rfl⟩ : syracuseStep 861131 = 1291697) B1291697
theorem B337031 : Blo 147793 337031 := bstep (se 1 (by rfl) ⟨252773, by rfl⟩ : syracuseStep 337031 = 505547) B505547
theorem B1615085 : Blo 147793 1615085 := bstep (se 3 (by rfl) ⟨302828, by rfl⟩ : syracuseStep 1615085 = 605657) B605657
theorem B664865 : Blo 147793 664865 := bstep (se 2 (by rfl) ⟨249324, by rfl⟩ : syracuseStep 664865 = 498649) B498649
theorem B238907 : Blo 147793 238907 := bstep (se 1 (by rfl) ⟨179180, by rfl⟩ : syracuseStep 238907 = 358361) B358361
theorem B337211 : Blo 147793 337211 := bstep (se 1 (by rfl) ⟨252908, by rfl⟩ : syracuseStep 337211 = 505817) B505817
theorem B861587 : Blo 147793 861587 := bstep (se 1 (by rfl) ⟨646190, by rfl⟩ : syracuseStep 861587 = 1292381) B1292381
theorem B632249 : Blo 147793 632249 := bstep (se 2 (by rfl) ⟨237093, by rfl⟩ : syracuseStep 632249 = 474187) B474187
theorem B337337 : Blo 147793 337337 := bstep (se 2 (by rfl) ⟨126501, by rfl⟩ : syracuseStep 337337 = 253003) B253003
theorem B501335 : Blo 147793 501335 := bstep (se 1 (by rfl) ⟨376001, by rfl⟩ : syracuseStep 501335 = 752003) B752003
theorem B1451621 : Blo 147793 1451621 := bstep (se 4 (by rfl) ⟨136089, by rfl⟩ : syracuseStep 1451621 = 272179) B272179
theorem B4990643 : Blo 147793 4990643 := bstep (se 1 (by rfl) ⟨3742982, by rfl⟩ : syracuseStep 4990643 = 7485965) B7485965
theorem B337679 : Blo 147793 337679 := bstep (se 1 (by rfl) ⟨253259, by rfl⟩ : syracuseStep 337679 = 506519) B506519
theorem B337697 : Blo 147793 337697 := bstep (se 2 (by rfl) ⟨126636, by rfl⟩ : syracuseStep 337697 = 253273) B253273
theorem B632711 : Blo 147793 632711 := bstep (se 1 (by rfl) ⟨474533, by rfl⟩ : syracuseStep 632711 = 949067) B949067
theorem B11610053 : Blo 147793 11610053 := bstep (se 4 (by rfl) ⟨1088442, by rfl⟩ : syracuseStep 11610053 = 2176885) B2176885
theorem B501821 : Blo 147793 501821 := bstep (se 3 (by rfl) ⟨94091, by rfl⟩ : syracuseStep 501821 = 188183) B188183
theorem B763991 : Blo 147793 763991 := bstep (se 1 (by rfl) ⟨572993, by rfl⟩ : syracuseStep 763991 = 1145987) B1145987
theorem B338039 : Blo 147793 338039 := bstep (se 1 (by rfl) ⟨253529, by rfl⟩ : syracuseStep 338039 = 507059) B507059
theorem B1091717 : Blo 147793 1091717 := bstep (se 4 (by rfl) ⟨102348, by rfl⟩ : syracuseStep 1091717 = 204697) B204697
theorem B338219 : Blo 147793 338219 := bstep (se 1 (by rfl) ⟨253664, by rfl⟩ : syracuseStep 338219 = 507329) B507329
theorem B403859 : Blo 147793 403859 := bstep (se 1 (by rfl) ⟨302894, by rfl⟩ : syracuseStep 403859 = 605789) B605789
theorem B240143 : Blo 147793 240143 := bstep (se 1 (by rfl) ⟨180107, by rfl⟩ : syracuseStep 240143 = 360215) B360215
theorem B1944107 : Blo 147793 1944107 := bstep (se 1 (by rfl) ⟨1458080, by rfl⟩ : syracuseStep 1944107 = 2916161) B2916161
theorem B764477 : Blo 147793 764477 := bstep (se 3 (by rfl) ⟨143339, by rfl⟩ : syracuseStep 764477 = 286679) B286679
theorem B338579 : Blo 147793 338579 := bstep (se 1 (by rfl) ⟨253934, by rfl⟩ : syracuseStep 338579 = 507869) B507869
theorem B338633 : Blo 147793 338633 := bstep (se 2 (by rfl) ⟨126987, by rfl⟩ : syracuseStep 338633 = 253975) B253975
theorem B765101 : Blo 147793 765101 := bstep (se 3 (by rfl) ⟨143456, by rfl⟩ : syracuseStep 765101 = 286913) B286913
theorem B404747 : Blo 147793 404747 := bstep (se 1 (by rfl) ⟨303560, by rfl⟩ : syracuseStep 404747 = 607121) B607121
theorem B339335 : Blo 147793 339335 := bstep (se 1 (by rfl) ⟨254501, by rfl⟩ : syracuseStep 339335 = 509003) B509003
theorem B503225 : Blo 147793 503225 := bstep (se 2 (by rfl) ⟨188709, by rfl⟩ : syracuseStep 503225 = 377419) B377419
theorem B1224157 : Blo 147793 1224157 := bstep (se 3 (by rfl) ⟨229529, by rfl⟩ : syracuseStep 1224157 = 459059) B459059
theorem B339515 : Blo 147793 339515 := bstep (se 1 (by rfl) ⟨254636, by rfl⟩ : syracuseStep 339515 = 509273) B509273
theorem B339641 : Blo 147793 339641 := bstep (se 2 (by rfl) ⟨127365, by rfl⟩ : syracuseStep 339641 = 254731) B254731
theorem B634625 : Blo 147793 634625 := bstep (se 2 (by rfl) ⟨237984, by rfl⟩ : syracuseStep 634625 = 475969) B475969
theorem B241451 : Blo 147793 241451 := bstep (se 1 (by rfl) ⟨181088, by rfl⟩ : syracuseStep 241451 = 362177) B362177
theorem B503819 : Blo 147793 503819 := bstep (se 1 (by rfl) ⟨377864, by rfl⟩ : syracuseStep 503819 = 755729) B755729
theorem B339983 : Blo 147793 339983 := bstep (se 1 (by rfl) ⟨254987, by rfl⟩ : syracuseStep 339983 = 509975) B509975
theorem B340001 : Blo 147793 340001 := bstep (se 2 (by rfl) ⟨127500, by rfl⟩ : syracuseStep 340001 = 255001) B255001
theorem B503927 : Blo 147793 503927 := bstep (se 1 (by rfl) ⟨377945, by rfl⟩ : syracuseStep 503927 = 755891) B755891
theorem B2175245 : Blo 147793 2175245 := bstep (se 3 (by rfl) ⟨407858, by rfl⟩ : syracuseStep 2175245 = 815717) B815717
theorem B766259 : Blo 147793 766259 := bstep (se 1 (by rfl) ⟨574694, by rfl⟩ : syracuseStep 766259 = 1149389) B1149389
theorem B1519931 : Blo 147793 1519931 := bstep (se 1 (by rfl) ⟨1139948, by rfl⟩ : syracuseStep 1519931 = 2279897) B2279897
theorem B405847 : Blo 147793 405847 := bstep (se 1 (by rfl) ⟨304385, by rfl⟩ : syracuseStep 405847 = 608771) B608771
theorem B340343 : Blo 147793 340343 := bstep (se 1 (by rfl) ⟨255257, by rfl⟩ : syracuseStep 340343 = 510515) B510515
theorem B373193 : Blo 147793 373193 := bstep (se 2 (by rfl) ⟨139947, by rfl⟩ : syracuseStep 373193 = 279895) B279895
theorem B307727 : Blo 147793 307727 := bstep (se 1 (by rfl) ⟨230795, by rfl⟩ : syracuseStep 307727 = 461591) B461591
theorem B340523 : Blo 147793 340523 := bstep (se 1 (by rfl) ⟨255392, by rfl⟩ : syracuseStep 340523 = 510785) B510785
theorem B766583 : Blo 147793 766583 := bstep (se 1 (by rfl) ⟨574937, by rfl⟩ : syracuseStep 766583 = 1149875) B1149875
theorem B406151 : Blo 147793 406151 := bstep (se 1 (by rfl) ⟨304613, by rfl⟩ : syracuseStep 406151 = 609227) B609227
theorem B4207285 : Blo 147793 4207285 := bstep (se 5 (by rfl) ⟨197216, by rfl⟩ : syracuseStep 4207285 = 394433) B394433
theorem B504521 : Blo 147793 504521 := bstep (se 2 (by rfl) ⟨189195, by rfl⟩ : syracuseStep 504521 = 378391) B378391
theorem B340883 : Blo 147793 340883 := bstep (se 1 (by rfl) ⟨255662, by rfl⟩ : syracuseStep 340883 = 511325) B511325
theorem B242617 : Blo 147793 242617 := bstep (se 2 (by rfl) ⟨90981, by rfl⟩ : syracuseStep 242617 = 181963) B181963
theorem B340937 : Blo 147793 340937 := bstep (se 2 (by rfl) ⟨127851, by rfl⟩ : syracuseStep 340937 = 255703) B255703
theorem B1913867 : Blo 147793 1913867 := bstep (se 1 (by rfl) ⟨1435400, by rfl⟩ : syracuseStep 1913867 = 2870801) B2870801
theorem B767177 : Blo 147793 767177 := bstep (se 2 (by rfl) ⟨287691, by rfl⟩ : syracuseStep 767177 = 575383) B575383
theorem B505223 : Blo 147793 505223 := bstep (se 1 (by rfl) ⟨378917, by rfl⟩ : syracuseStep 505223 = 757835) B757835
theorem B767555 : Blo 147793 767555 := bstep (se 1 (by rfl) ⟨575666, by rfl⟩ : syracuseStep 767555 = 1151333) B1151333
theorem B505601 : Blo 147793 505601 := bstep (se 2 (by rfl) ⟨189600, by rfl⟩ : syracuseStep 505601 = 379201) B379201
theorem B1226497 : Blo 147793 1226497 := bstep (se 2 (by rfl) ⟨459936, by rfl⟩ : syracuseStep 1226497 = 919873) B919873
theorem B374615 : Blo 147793 374615 := bstep (se 1 (by rfl) ⟨280961, by rfl⟩ : syracuseStep 374615 = 561923) B561923
theorem B767879 : Blo 147793 767879 := bstep (se 1 (by rfl) ⟨575909, by rfl⟩ : syracuseStep 767879 = 1151819) B1151819
theorem B374827 : Blo 147793 374827 := bstep (se 1 (by rfl) ⟨281120, by rfl⟩ : syracuseStep 374827 = 562241) B562241
theorem B243847 : Blo 147793 243847 := bstep (se 1 (by rfl) ⟨182885, by rfl⟩ : syracuseStep 243847 = 365771) B365771
theorem B374969 : Blo 147793 374969 := bstep (se 2 (by rfl) ⟨140613, by rfl⟩ : syracuseStep 374969 = 281227) B281227
theorem B4143581 : Blo 147793 4143581 := bstep (se 3 (by rfl) ⟨776921, by rfl⟩ : syracuseStep 4143581 = 1553843) B1553843
theorem B703019 : Blo 147793 703019 := bstep (se 1 (by rfl) ⟨527264, by rfl⟩ : syracuseStep 703019 = 1054529) B1054529
theorem B506411 : Blo 147793 506411 := bstep (se 1 (by rfl) ⟨379808, by rfl⟩ : syracuseStep 506411 = 759617) B759617
theorem B211513 : Blo 147793 211513 := bstep (se 2 (by rfl) ⟨79317, by rfl⟩ : syracuseStep 211513 = 158635) B158635
theorem B1358795 : Blo 147793 1358795 := bstep (se 1 (by rfl) ⟨1019096, by rfl⟩ : syracuseStep 1358795 = 2038193) B2038193
theorem B375961 : Blo 147793 375961 := bstep (se 2 (by rfl) ⟨140985, by rfl⟩ : syracuseStep 375961 = 281971) B281971
theorem B1424557 : Blo 147793 1424557 := bstep (se 3 (by rfl) ⟨267104, by rfl⟩ : syracuseStep 1424557 = 534209) B534209
theorem B277705 : Blo 147793 277705 := bstep (se 2 (by rfl) ⟨104139, by rfl⟩ : syracuseStep 277705 = 208279) B208279
theorem B376123 : Blo 147793 376123 := bstep (se 1 (by rfl) ⟨282092, by rfl⟩ : syracuseStep 376123 = 564185) B564185
theorem B671129 : Blo 147793 671129 := bstep (se 2 (by rfl) ⟨251673, by rfl⟩ : syracuseStep 671129 = 503347) B503347
theorem B376265 : Blo 147793 376265 := bstep (se 2 (by rfl) ⟨141099, by rfl⟩ : syracuseStep 376265 = 282199) B282199
theorem B1129949 : Blo 147793 1129949 := bstep (se 3 (by rfl) ⟨211865, by rfl⟩ : syracuseStep 1129949 = 423731) B423731
theorem B212743 : Blo 147793 212743 := bstep (se 1 (by rfl) ⟨159557, by rfl⟩ : syracuseStep 212743 = 319115) B319115
theorem B376609 : Blo 147793 376609 := bstep (se 2 (by rfl) ⟨141228, by rfl⟩ : syracuseStep 376609 = 282457) B282457
theorem B507707 : Blo 147793 507707 := bstep (se 1 (by rfl) ⟨380780, by rfl⟩ : syracuseStep 507707 = 761561) B761561
theorem B508193 : Blo 147793 508193 := bstep (se 2 (by rfl) ⟨190572, by rfl⟩ : syracuseStep 508193 = 381145) B381145
theorem B377207 : Blo 147793 377207 := bstep (se 1 (by rfl) ⟨282905, by rfl⟩ : syracuseStep 377207 = 565811) B565811
theorem B147847 : Blo 147793 147847 := bstep (se 1 (by rfl) ⟨110885, by rfl⟩ : syracuseStep 147847 = 221771) B221771
theorem B606599 : Blo 147793 606599 := bstep (se 1 (by rfl) ⟨454949, by rfl⟩ : syracuseStep 606599 = 909899) B909899
theorem B147855 : Blo 147793 147855 := bstep (se 1 (by rfl) ⟨110891, by rfl⟩ : syracuseStep 147855 = 221783) B221783
theorem B147899 : Blo 147793 147899 := bstep (se 1 (by rfl) ⟨110924, by rfl⟩ : syracuseStep 147899 = 221849) B221849
theorem B573905 : Blo 147793 573905 := bstep (se 2 (by rfl) ⟨215214, by rfl⟩ : syracuseStep 573905 = 430429) B430429
theorem B967133 : Blo 147793 967133 := bstep (se 3 (by rfl) ⟨181337, by rfl⟩ : syracuseStep 967133 = 362675) B362675
theorem B147975 : Blo 147793 147975 := bstep (se 1 (by rfl) ⟨110981, by rfl⟩ : syracuseStep 147975 = 221963) B221963
theorem B147983 : Blo 147793 147983 := bstep (se 1 (by rfl) ⟨110987, by rfl⟩ : syracuseStep 147983 = 221975) B221975
theorem B2441771 : Blo 147793 2441771 := bstep (se 1 (by rfl) ⟨1831328, by rfl⟩ : syracuseStep 2441771 = 3662657) B3662657
theorem B148027 : Blo 147793 148027 := bstep (se 1 (by rfl) ⟨111020, by rfl⟩ : syracuseStep 148027 = 222041) B222041
theorem B213563 : Blo 147793 213563 := bstep (se 1 (by rfl) ⟨160172, by rfl⟩ : syracuseStep 213563 = 320345) B320345
theorem B148103 : Blo 147793 148103 := bstep (se 1 (by rfl) ⟨111077, by rfl⟩ : syracuseStep 148103 = 222155) B222155
theorem B148111 : Blo 147793 148111 := bstep (se 1 (by rfl) ⟨111083, by rfl⟩ : syracuseStep 148111 = 222167) B222167
theorem B148155 : Blo 147793 148155 := bstep (se 1 (by rfl) ⟨111116, by rfl⟩ : syracuseStep 148155 = 222233) B222233
theorem B148231 : Blo 147793 148231 := bstep (se 1 (by rfl) ⟨111173, by rfl⟩ : syracuseStep 148231 = 222347) B222347
theorem B148239 : Blo 147793 148239 := bstep (se 1 (by rfl) ⟨111179, by rfl⟩ : syracuseStep 148239 = 222359) B222359
theorem B148283 : Blo 147793 148283 := bstep (se 1 (by rfl) ⟨111212, by rfl⟩ : syracuseStep 148283 = 222425) B222425
theorem B508787 : Blo 147793 508787 := bstep (se 1 (by rfl) ⟨381590, by rfl⟩ : syracuseStep 508787 = 763181) B763181
theorem B148359 : Blo 147793 148359 := bstep (se 1 (by rfl) ⟨111269, by rfl⟩ : syracuseStep 148359 = 222539) B222539
theorem B148367 : Blo 147793 148367 := bstep (se 1 (by rfl) ⟨111275, by rfl⟩ : syracuseStep 148367 = 222551) B222551
theorem B574361 : Blo 147793 574361 := bstep (se 2 (by rfl) ⟨215385, by rfl⟩ : syracuseStep 574361 = 430771) B430771
theorem B148411 : Blo 147793 148411 := bstep (se 1 (by rfl) ⟨111308, by rfl⟩ : syracuseStep 148411 = 222617) B222617
theorem B214007 : Blo 147793 214007 := bstep (se 1 (by rfl) ⟨160505, by rfl⟩ : syracuseStep 214007 = 321011) B321011
theorem B148487 : Blo 147793 148487 := bstep (se 1 (by rfl) ⟨111365, by rfl⟩ : syracuseStep 148487 = 222731) B222731
theorem B148495 : Blo 147793 148495 := bstep (se 1 (by rfl) ⟨111371, by rfl⟩ : syracuseStep 148495 = 222743) B222743
theorem B148539 : Blo 147793 148539 := bstep (se 1 (by rfl) ⟨111404, by rfl⟩ : syracuseStep 148539 = 222809) B222809
theorem B148615 : Blo 147793 148615 := bstep (se 1 (by rfl) ⟨111461, by rfl⟩ : syracuseStep 148615 = 222923) B222923
theorem B148623 : Blo 147793 148623 := bstep (se 1 (by rfl) ⟨111467, by rfl⟩ : syracuseStep 148623 = 222935) B222935
theorem B214201 : Blo 147793 214201 := bstep (se 2 (by rfl) ⟨80325, by rfl⟩ : syracuseStep 214201 = 160651) B160651
theorem B148667 : Blo 147793 148667 := bstep (se 1 (by rfl) ⟨111500, by rfl⟩ : syracuseStep 148667 = 223001) B223001
theorem B476417 : Blo 147793 476417 := bstep (se 2 (by rfl) ⟨178656, by rfl⟩ : syracuseStep 476417 = 357313) B357313
theorem B148743 : Blo 147793 148743 := bstep (se 1 (by rfl) ⟨111557, by rfl⟩ : syracuseStep 148743 = 223115) B223115
theorem B148751 : Blo 147793 148751 := bstep (se 1 (by rfl) ⟨111563, by rfl⟩ : syracuseStep 148751 = 223127) B223127
theorem B148795 : Blo 147793 148795 := bstep (se 1 (by rfl) ⟨111596, by rfl⟩ : syracuseStep 148795 = 223193) B223193
theorem B148871 : Blo 147793 148871 := bstep (se 1 (by rfl) ⟨111653, by rfl⟩ : syracuseStep 148871 = 223307) B223307
theorem B148879 : Blo 147793 148879 := bstep (se 1 (by rfl) ⟨111659, by rfl⟩ : syracuseStep 148879 = 223319) B223319
theorem B148923 : Blo 147793 148923 := bstep (se 1 (by rfl) ⟨111692, by rfl⟩ : syracuseStep 148923 = 223385) B223385
theorem B148999 : Blo 147793 148999 := bstep (se 1 (by rfl) ⟨111749, by rfl⟩ : syracuseStep 148999 = 223499) B223499
theorem B149007 : Blo 147793 149007 := bstep (se 1 (by rfl) ⟨111755, by rfl⟩ : syracuseStep 149007 = 223511) B223511
theorem B149051 : Blo 147793 149051 := bstep (se 1 (by rfl) ⟨111788, by rfl⟩ : syracuseStep 149051 = 223577) B223577
theorem B149127 : Blo 147793 149127 := bstep (se 1 (by rfl) ⟨111845, by rfl⟩ : syracuseStep 149127 = 223691) B223691
theorem B378503 : Blo 147793 378503 := bstep (se 1 (by rfl) ⟨283877, by rfl⟩ : syracuseStep 378503 = 567755) B567755
theorem B149135 : Blo 147793 149135 := bstep (se 1 (by rfl) ⟨111851, by rfl⟩ : syracuseStep 149135 = 223703) B223703
theorem B378553 : Blo 147793 378553 := bstep (se 2 (by rfl) ⟨141957, by rfl⟩ : syracuseStep 378553 = 283915) B283915
theorem B149179 : Blo 147793 149179 := bstep (se 1 (by rfl) ⟨111884, by rfl⟩ : syracuseStep 149179 = 223769) B223769
theorem B149255 : Blo 147793 149255 := bstep (se 1 (by rfl) ⟨111941, by rfl⟩ : syracuseStep 149255 = 223883) B223883
theorem B149263 : Blo 147793 149263 := bstep (se 1 (by rfl) ⟨111947, by rfl⟩ : syracuseStep 149263 = 223895) B223895
theorem B149307 : Blo 147793 149307 := bstep (se 1 (by rfl) ⟨111980, by rfl⟩ : syracuseStep 149307 = 223961) B223961
theorem B149383 : Blo 147793 149383 := bstep (se 1 (by rfl) ⟨112037, by rfl⟩ : syracuseStep 149383 = 224075) B224075
theorem B149391 : Blo 147793 149391 := bstep (se 1 (by rfl) ⟨112043, by rfl⟩ : syracuseStep 149391 = 224087) B224087
theorem B149435 : Blo 147793 149435 := bstep (se 1 (by rfl) ⟨112076, by rfl⟩ : syracuseStep 149435 = 224153) B224153
theorem B149511 : Blo 147793 149511 := bstep (se 1 (by rfl) ⟨112133, by rfl⟩ : syracuseStep 149511 = 224267) B224267
theorem B149519 : Blo 147793 149519 := bstep (se 1 (by rfl) ⟨112139, by rfl⟩ : syracuseStep 149519 = 224279) B224279
theorem B575531 : Blo 147793 575531 := bstep (se 1 (by rfl) ⟨431648, by rfl⟩ : syracuseStep 575531 = 863297) B863297
theorem B149563 : Blo 147793 149563 := bstep (se 1 (by rfl) ⟨112172, by rfl⟩ : syracuseStep 149563 = 224345) B224345
theorem B149639 : Blo 147793 149639 := bstep (se 1 (by rfl) ⟨112229, by rfl⟩ : syracuseStep 149639 = 224459) B224459
theorem B149647 : Blo 147793 149647 := bstep (se 1 (by rfl) ⟨112235, by rfl⟩ : syracuseStep 149647 = 224471) B224471
theorem B149691 : Blo 147793 149691 := bstep (se 1 (by rfl) ⟨112268, by rfl⟩ : syracuseStep 149691 = 224537) B224537
theorem B149767 : Blo 147793 149767 := bstep (se 1 (by rfl) ⟨112325, by rfl⟩ : syracuseStep 149767 = 224651) B224651
theorem B280847 : Blo 147793 280847 := bstep (se 1 (by rfl) ⟨210635, by rfl⟩ : syracuseStep 280847 = 421271) B421271
theorem B149775 : Blo 147793 149775 := bstep (se 1 (by rfl) ⟨112331, by rfl⟩ : syracuseStep 149775 = 224663) B224663
theorem B379151 : Blo 147793 379151 := bstep (se 1 (by rfl) ⟨284363, by rfl⟩ : syracuseStep 379151 = 568727) B568727
theorem B149819 : Blo 147793 149819 := bstep (se 1 (by rfl) ⟨112364, by rfl⟩ : syracuseStep 149819 = 224729) B224729
theorem B149895 : Blo 147793 149895 := bstep (se 1 (by rfl) ⟨112421, by rfl⟩ : syracuseStep 149895 = 224843) B224843
theorem B149903 : Blo 147793 149903 := bstep (se 1 (by rfl) ⟨112427, by rfl⟩ : syracuseStep 149903 = 224855) B224855
theorem B149947 : Blo 147793 149947 := bstep (se 1 (by rfl) ⟨112460, by rfl⟩ : syracuseStep 149947 = 224921) B224921
theorem B150023 : Blo 147793 150023 := bstep (se 1 (by rfl) ⟨112517, by rfl⟩ : syracuseStep 150023 = 225035) B225035
theorem B150031 : Blo 147793 150031 := bstep (se 1 (by rfl) ⟨112523, by rfl⟩ : syracuseStep 150031 = 225047) B225047
theorem B150075 : Blo 147793 150075 := bstep (se 1 (by rfl) ⟨112556, by rfl⟩ : syracuseStep 150075 = 225113) B225113
theorem B150151 : Blo 147793 150151 := bstep (se 1 (by rfl) ⟨112613, by rfl⟩ : syracuseStep 150151 = 225227) B225227
theorem B150159 : Blo 147793 150159 := bstep (se 1 (by rfl) ⟨112619, by rfl⟩ : syracuseStep 150159 = 225239) B225239
theorem B150203 : Blo 147793 150203 := bstep (se 1 (by rfl) ⟨112652, by rfl⟩ : syracuseStep 150203 = 225305) B225305
theorem B150279 : Blo 147793 150279 := bstep (se 1 (by rfl) ⟨112709, by rfl⟩ : syracuseStep 150279 = 225419) B225419
theorem B150287 : Blo 147793 150287 := bstep (se 1 (by rfl) ⟨112715, by rfl⟩ : syracuseStep 150287 = 225431) B225431
theorem B281387 : Blo 147793 281387 := bstep (se 1 (by rfl) ⟨211040, by rfl⟩ : syracuseStep 281387 = 422081) B422081
theorem B150331 : Blo 147793 150331 := bstep (se 1 (by rfl) ⟨112748, by rfl⟩ : syracuseStep 150331 = 225497) B225497
theorem B150407 : Blo 147793 150407 := bstep (se 1 (by rfl) ⟨112805, by rfl⟩ : syracuseStep 150407 = 225611) B225611
theorem B150415 : Blo 147793 150415 := bstep (se 1 (by rfl) ⟨112811, by rfl⟩ : syracuseStep 150415 = 225623) B225623
theorem B150459 : Blo 147793 150459 := bstep (se 1 (by rfl) ⟨112844, by rfl⟩ : syracuseStep 150459 = 225689) B225689
theorem B379849 : Blo 147793 379849 := bstep (se 2 (by rfl) ⟨142443, by rfl⟩ : syracuseStep 379849 = 284887) B284887
theorem B150535 : Blo 147793 150535 := bstep (se 1 (by rfl) ⟨112901, by rfl⟩ : syracuseStep 150535 = 225803) B225803
theorem B150543 : Blo 147793 150543 := bstep (se 1 (by rfl) ⟨112907, by rfl⟩ : syracuseStep 150543 = 225815) B225815
theorem B150587 : Blo 147793 150587 := bstep (se 1 (by rfl) ⟨112940, by rfl⟩ : syracuseStep 150587 = 225881) B225881
theorem B379991 : Blo 147793 379991 := bstep (se 1 (by rfl) ⟨284993, by rfl⟩ : syracuseStep 379991 = 569987) B569987
theorem B150663 : Blo 147793 150663 := bstep (se 1 (by rfl) ⟨112997, by rfl⟩ : syracuseStep 150663 = 225995) B225995
theorem B150671 : Blo 147793 150671 := bstep (se 1 (by rfl) ⟨113003, by rfl⟩ : syracuseStep 150671 = 226007) B226007
theorem B150715 : Blo 147793 150715 := bstep (se 1 (by rfl) ⟨113036, by rfl⟩ : syracuseStep 150715 = 226073) B226073
theorem B150791 : Blo 147793 150791 := bstep (se 1 (by rfl) ⟨113093, by rfl⟩ : syracuseStep 150791 = 226187) B226187
theorem B609551 : Blo 147793 609551 := bstep (se 1 (by rfl) ⟨457163, by rfl⟩ : syracuseStep 609551 = 914327) B914327
theorem B150799 : Blo 147793 150799 := bstep (se 1 (by rfl) ⟨113099, by rfl⟩ : syracuseStep 150799 = 226199) B226199
theorem B150843 : Blo 147793 150843 := bstep (se 1 (by rfl) ⟨113132, by rfl⟩ : syracuseStep 150843 = 226265) B226265
theorem B150919 : Blo 147793 150919 := bstep (se 1 (by rfl) ⟨113189, by rfl⟩ : syracuseStep 150919 = 226379) B226379
theorem B150927 : Blo 147793 150927 := bstep (se 1 (by rfl) ⟨113195, by rfl⟩ : syracuseStep 150927 = 226391) B226391
theorem B511379 : Blo 147793 511379 := bstep (se 1 (by rfl) ⟨383534, by rfl⟩ : syracuseStep 511379 = 767069) B767069
theorem B150971 : Blo 147793 150971 := bstep (se 1 (by rfl) ⟨113228, by rfl⟩ : syracuseStep 150971 = 226457) B226457
theorem B151047 : Blo 147793 151047 := bstep (se 1 (by rfl) ⟨113285, by rfl⟩ : syracuseStep 151047 = 226571) B226571
theorem B151055 : Blo 147793 151055 := bstep (se 1 (by rfl) ⟨113291, by rfl⟩ : syracuseStep 151055 = 226583) B226583
theorem B151099 : Blo 147793 151099 := bstep (se 1 (by rfl) ⟨113324, by rfl⟩ : syracuseStep 151099 = 226649) B226649
theorem B904765 : Blo 147793 904765 := bstep (se 3 (by rfl) ⟨169643, by rfl⟩ : syracuseStep 904765 = 339287) B339287
theorem B151175 : Blo 147793 151175 := bstep (se 1 (by rfl) ⟨113381, by rfl⟩ : syracuseStep 151175 = 226763) B226763
theorem B151183 : Blo 147793 151183 := bstep (se 1 (by rfl) ⟨113387, by rfl⟩ : syracuseStep 151183 = 226775) B226775
theorem B151227 : Blo 147793 151227 := bstep (se 1 (by rfl) ⟨113420, by rfl⟩ : syracuseStep 151227 = 226841) B226841
theorem B806593 : Blo 147793 806593 := bstep (se 2 (by rfl) ⟨302472, by rfl⟩ : syracuseStep 806593 = 604945) B604945
theorem B151303 : Blo 147793 151303 := bstep (se 1 (by rfl) ⟨113477, by rfl⟩ : syracuseStep 151303 = 226955) B226955
theorem B151311 : Blo 147793 151311 := bstep (se 1 (by rfl) ⟨113483, by rfl⟩ : syracuseStep 151311 = 226967) B226967
theorem B151355 : Blo 147793 151355 := bstep (se 1 (by rfl) ⟨113516, by rfl⟩ : syracuseStep 151355 = 227033) B227033
theorem B282503 : Blo 147793 282503 := bstep (se 1 (by rfl) ⟨211877, by rfl⟩ : syracuseStep 282503 = 423755) B423755
theorem B151431 : Blo 147793 151431 := bstep (se 1 (by rfl) ⟨113573, by rfl⟩ : syracuseStep 151431 = 227147) B227147
theorem B151439 : Blo 147793 151439 := bstep (se 1 (by rfl) ⟨113579, by rfl⟩ : syracuseStep 151439 = 227159) B227159
theorem B151483 : Blo 147793 151483 := bstep (se 1 (by rfl) ⟨113612, by rfl⟩ : syracuseStep 151483 = 227225) B227225
theorem B151559 : Blo 147793 151559 := bstep (se 1 (by rfl) ⟨113669, by rfl⟩ : syracuseStep 151559 = 227339) B227339
theorem B249871 : Blo 147793 249871 := bstep (se 1 (by rfl) ⟨187403, by rfl⟩ : syracuseStep 249871 = 374807) B374807
theorem B151567 : Blo 147793 151567 := bstep (se 1 (by rfl) ⟨113675, by rfl⟩ : syracuseStep 151567 = 227351) B227351
theorem B643115 : Blo 147793 643115 := bstep (se 1 (by rfl) ⟨482336, by rfl⟩ : syracuseStep 643115 = 964673) B964673
theorem B151611 : Blo 147793 151611 := bstep (se 1 (by rfl) ⟨113708, by rfl⟩ : syracuseStep 151611 = 227417) B227417
theorem B151687 : Blo 147793 151687 := bstep (se 1 (by rfl) ⟨113765, by rfl⟩ : syracuseStep 151687 = 227531) B227531
theorem B151695 : Blo 147793 151695 := bstep (se 1 (by rfl) ⟨113771, by rfl⟩ : syracuseStep 151695 = 227543) B227543
theorem B151739 : Blo 147793 151739 := bstep (se 1 (by rfl) ⟨113804, by rfl⟩ : syracuseStep 151739 = 227609) B227609
theorem B1102061 : Blo 147793 1102061 := bstep (se 3 (by rfl) ⟨206636, by rfl⟩ : syracuseStep 1102061 = 413273) B413273
theorem B283027 : Blo 147793 283027 := bstep (se 1 (by rfl) ⟨212270, by rfl⟩ : syracuseStep 283027 = 424541) B424541
theorem B807353 : Blo 147793 807353 := bstep (se 2 (by rfl) ⟨302757, by rfl⟩ : syracuseStep 807353 = 605515) B605515
theorem B479773 : Blo 147793 479773 := bstep (se 3 (by rfl) ⟨89957, by rfl⟩ : syracuseStep 479773 = 179915) B179915
theorem B250411 : Blo 147793 250411 := bstep (se 1 (by rfl) ⟨187808, by rfl⟩ : syracuseStep 250411 = 375617) B375617
theorem B545399 : Blo 147793 545399 := bstep (se 1 (by rfl) ⟨409049, by rfl⟩ : syracuseStep 545399 = 818099) B818099
theorem B250553 : Blo 147793 250553 := bstep (se 2 (by rfl) ⟨93957, by rfl⟩ : syracuseStep 250553 = 187915) B187915
theorem B152327 : Blo 147793 152327 := bstep (se 1 (by rfl) ⟨114245, by rfl⟩ : syracuseStep 152327 = 228491) B228491
theorem B316219 : Blo 147793 316219 := bstep (se 1 (by rfl) ⟨237164, by rfl⟩ : syracuseStep 316219 = 474329) B474329
theorem B3068761 : Blo 147793 3068761 := bstep (se 2 (by rfl) ⟨1150785, by rfl⟩ : syracuseStep 3068761 = 2301571) B2301571
theorem B382067 : Blo 147793 382067 := bstep (se 1 (by rfl) ⟨286550, by rfl⟩ : syracuseStep 382067 = 573101) B573101
theorem B316705 : Blo 147793 316705 := bstep (se 2 (by rfl) ⟨118764, by rfl⟩ : syracuseStep 316705 = 237529) B237529
theorem B251255 : Blo 147793 251255 := bstep (se 1 (by rfl) ⟨188441, by rfl⟩ : syracuseStep 251255 = 376883) B376883
theorem B284219 : Blo 147793 284219 := bstep (se 1 (by rfl) ⟨213164, by rfl⟩ : syracuseStep 284219 = 426329) B426329
theorem B317047 : Blo 147793 317047 := bstep (se 1 (by rfl) ⟨237785, by rfl⟩ : syracuseStep 317047 = 475571) B475571
theorem B382583 : Blo 147793 382583 := bstep (se 1 (by rfl) ⟨286937, by rfl⟩ : syracuseStep 382583 = 573875) B573875
theorem B251707 : Blo 147793 251707 := bstep (se 1 (by rfl) ⟨188780, by rfl⟩ : syracuseStep 251707 = 377561) B377561
theorem B6510449 : Blo 147793 6510449 := bstep (se 2 (by rfl) ⟨2441418, by rfl⟩ : syracuseStep 6510449 = 4882837) B4882837
theorem B1464227 : Blo 147793 1464227 := bstep (se 1 (by rfl) ⟨1098170, by rfl⟩ : syracuseStep 1464227 = 2196341) B2196341
theorem B251849 : Blo 147793 251849 := bstep (se 2 (by rfl) ⟨94443, by rfl⟩ : syracuseStep 251849 = 188887) B188887
theorem B284705 : Blo 147793 284705 := bstep (se 2 (by rfl) ⟨106764, by rfl⟩ : syracuseStep 284705 = 213529) B213529
theorem B1267913 : Blo 147793 1267913 := bstep (se 2 (by rfl) ⟨475467, by rfl⟩ : syracuseStep 1267913 = 950935) B950935
theorem B284971 : Blo 147793 284971 := bstep (se 1 (by rfl) ⟨213728, by rfl⟩ : syracuseStep 284971 = 427457) B427457
theorem B514451 : Blo 147793 514451 := bstep (se 1 (by rfl) ⟨385838, by rfl⟩ : syracuseStep 514451 = 771677) B771677
theorem B383575 : Blo 147793 383575 := bstep (se 1 (by rfl) ⟨287681, by rfl⟩ : syracuseStep 383575 = 575363) B575363
theorem B842359 : Blo 147793 842359 := bstep (se 1 (by rfl) ⟨631769, by rfl⟩ : syracuseStep 842359 = 1263539) B1263539
theorem B252551 : Blo 147793 252551 := bstep (se 1 (by rfl) ⟨189413, by rfl⟩ : syracuseStep 252551 = 378827) B378827
theorem B645833 : Blo 147793 645833 := bstep (se 2 (by rfl) ⟨242187, by rfl⟩ : syracuseStep 645833 = 484375) B484375
theorem B5233423 : Blo 147793 5233423 := bstep (se 1 (by rfl) ⟨3925067, by rfl⟩ : syracuseStep 5233423 = 7850135) B7850135
theorem B482183 : Blo 147793 482183 := bstep (se 1 (by rfl) ⟨361637, by rfl⟩ : syracuseStep 482183 = 723275) B723275
theorem B383879 : Blo 147793 383879 := bstep (se 1 (by rfl) ⟨287909, by rfl⟩ : syracuseStep 383879 = 575819) B575819
theorem B384011 : Blo 147793 384011 := bstep (se 1 (by rfl) ⟨288008, by rfl⟩ : syracuseStep 384011 = 576017) B576017
theorem B1137725 : Blo 147793 1137725 := bstep (se 3 (by rfl) ⟨213323, by rfl⟩ : syracuseStep 1137725 = 426647) B426647
theorem B449671 : Blo 147793 449671 := bstep (se 1 (by rfl) ⟨337253, by rfl⟩ : syracuseStep 449671 = 674507) B674507
theorem B187535 : Blo 147793 187535 := bstep (se 1 (by rfl) ⟨140651, by rfl⟩ : syracuseStep 187535 = 281303) B281303
theorem B253199 : Blo 147793 253199 := bstep (se 1 (by rfl) ⟨189899, by rfl⟩ : syracuseStep 253199 = 379799) B379799
theorem B482593 : Blo 147793 482593 := bstep (se 2 (by rfl) ⟨180972, by rfl⟩ : syracuseStep 482593 = 361945) B361945
theorem B286087 : Blo 147793 286087 := bstep (se 1 (by rfl) ⟨214565, by rfl⟩ : syracuseStep 286087 = 429131) B429131
theorem B253739 : Blo 147793 253739 := bstep (se 1 (by rfl) ⟨190304, by rfl⟩ : syracuseStep 253739 = 380609) B380609
theorem B1269553 : Blo 147793 1269553 := bstep (se 2 (by rfl) ⟨476082, by rfl⟩ : syracuseStep 1269553 = 952165) B952165
theorem B843635 : Blo 147793 843635 := bstep (se 1 (by rfl) ⟨632726, by rfl⟩ : syracuseStep 843635 = 1265453) B1265453
theorem B286649 : Blo 147793 286649 := bstep (se 2 (by rfl) ⟨107493, by rfl⟩ : syracuseStep 286649 = 214987) B214987
theorem B254137 : Blo 147793 254137 := bstep (se 2 (by rfl) ⟨95301, by rfl⟩ : syracuseStep 254137 = 190603) B190603
theorem B844091 : Blo 147793 844091 := bstep (se 1 (by rfl) ⟨633068, by rfl⟩ : syracuseStep 844091 = 1266137) B1266137
theorem B680345 : Blo 147793 680345 := bstep (se 2 (by rfl) ⟨255129, by rfl⟩ : syracuseStep 680345 = 510259) B510259
theorem B221711 : Blo 147793 221711 := bstep (se 1 (by rfl) ⟨166283, by rfl⟩ : syracuseStep 221711 = 332567) B332567
theorem B3236395 : Blo 147793 3236395 := bstep (se 1 (by rfl) ⟨2427296, by rfl⟩ : syracuseStep 3236395 = 4854593) B4854593
theorem B221753 : Blo 147793 221753 := bstep (se 2 (by rfl) ⟨83157, by rfl⟩ : syracuseStep 221753 = 166315) B166315
theorem B647747 : Blo 147793 647747 := bstep (se 1 (by rfl) ⟨485810, by rfl⟩ : syracuseStep 647747 = 971621) B971621
theorem B221831 : Blo 147793 221831 := bstep (se 1 (by rfl) ⟨166373, by rfl⟩ : syracuseStep 221831 = 332747) B332747
theorem B221867 : Blo 147793 221867 := bstep (se 1 (by rfl) ⟨166400, by rfl⟩ : syracuseStep 221867 = 332801) B332801
theorem B221897 : Blo 147793 221897 := bstep (se 2 (by rfl) ⟨83211, by rfl⟩ : syracuseStep 221897 = 166423) B166423
theorem B222011 : Blo 147793 222011 := bstep (se 1 (by rfl) ⟨166508, by rfl⟩ : syracuseStep 222011 = 333017) B333017
theorem B222071 : Blo 147793 222071 := bstep (se 1 (by rfl) ⟨166553, by rfl⟩ : syracuseStep 222071 = 333107) B333107
theorem B254839 : Blo 147793 254839 := bstep (se 1 (by rfl) ⟨191129, by rfl⟩ : syracuseStep 254839 = 382259) B382259
theorem B648071 : Blo 147793 648071 := bstep (se 1 (by rfl) ⟨486053, by rfl⟩ : syracuseStep 648071 = 972107) B972107
theorem B222095 : Blo 147793 222095 := bstep (se 1 (by rfl) ⟨166571, by rfl⟩ : syracuseStep 222095 = 333143) B333143
theorem B222137 : Blo 147793 222137 := bstep (se 2 (by rfl) ⟨83301, by rfl⟩ : syracuseStep 222137 = 166603) B166603
theorem B222215 : Blo 147793 222215 := bstep (se 1 (by rfl) ⟨166661, by rfl⟩ : syracuseStep 222215 = 333323) B333323
theorem B222251 : Blo 147793 222251 := bstep (se 1 (by rfl) ⟨166688, by rfl⟩ : syracuseStep 222251 = 333377) B333377
theorem B255035 : Blo 147793 255035 := bstep (se 1 (by rfl) ⟨191276, by rfl⟩ : syracuseStep 255035 = 382553) B382553
theorem B287803 : Blo 147793 287803 := bstep (se 1 (by rfl) ⟨215852, by rfl⟩ : syracuseStep 287803 = 431705) B431705
theorem B222281 : Blo 147793 222281 := bstep (se 2 (by rfl) ⟨83355, by rfl⟩ : syracuseStep 222281 = 166711) B166711
theorem B222395 : Blo 147793 222395 := bstep (se 1 (by rfl) ⟨166796, by rfl⟩ : syracuseStep 222395 = 333593) B333593
theorem B222455 : Blo 147793 222455 := bstep (se 1 (by rfl) ⟨166841, by rfl⟩ : syracuseStep 222455 = 333683) B333683
theorem B222479 : Blo 147793 222479 := bstep (se 1 (by rfl) ⟨166859, by rfl⟩ : syracuseStep 222479 = 333719) B333719
theorem B845093 : Blo 147793 845093 := bstep (se 4 (by rfl) ⟨79227, by rfl⟩ : syracuseStep 845093 = 158455) B158455
theorem B222521 : Blo 147793 222521 := bstep (se 2 (by rfl) ⟨83445, by rfl⟩ : syracuseStep 222521 = 166891) B166891
theorem B222599 : Blo 147793 222599 := bstep (se 1 (by rfl) ⟨166949, by rfl⟩ : syracuseStep 222599 = 333899) B333899
theorem B222635 : Blo 147793 222635 := bstep (se 1 (by rfl) ⟨166976, by rfl⟩ : syracuseStep 222635 = 333953) B333953
theorem B222665 : Blo 147793 222665 := bstep (se 2 (by rfl) ⟨83499, by rfl⟩ : syracuseStep 222665 = 166999) B166999
theorem B255433 : Blo 147793 255433 := bstep (se 2 (by rfl) ⟨95787, by rfl⟩ : syracuseStep 255433 = 191575) B191575
theorem B222779 : Blo 147793 222779 := bstep (se 1 (by rfl) ⟨167084, by rfl⟩ : syracuseStep 222779 = 334169) B334169
theorem B222839 : Blo 147793 222839 := bstep (se 1 (by rfl) ⟨167129, by rfl⟩ : syracuseStep 222839 = 334259) B334259
theorem B222863 : Blo 147793 222863 := bstep (se 1 (by rfl) ⟨167147, by rfl⟩ : syracuseStep 222863 = 334295) B334295
theorem B222905 : Blo 147793 222905 := bstep (se 2 (by rfl) ⟨83589, by rfl⟩ : syracuseStep 222905 = 167179) B167179
theorem B452297 : Blo 147793 452297 := bstep (se 2 (by rfl) ⟨169611, by rfl⟩ : syracuseStep 452297 = 339223) B339223
theorem B845549 : Blo 147793 845549 := bstep (se 3 (by rfl) ⟨158540, by rfl⟩ : syracuseStep 845549 = 317081) B317081
theorem B222983 : Blo 147793 222983 := bstep (se 1 (by rfl) ⟨167237, by rfl⟩ : syracuseStep 222983 = 334475) B334475
theorem B223019 : Blo 147793 223019 := bstep (se 1 (by rfl) ⟨167264, by rfl⟩ : syracuseStep 223019 = 334529) B334529
theorem B223049 : Blo 147793 223049 := bstep (se 2 (by rfl) ⟨83643, by rfl⟩ : syracuseStep 223049 = 167287) B167287
theorem B223163 : Blo 147793 223163 := bstep (se 1 (by rfl) ⟨167372, by rfl⟩ : syracuseStep 223163 = 334745) B334745
theorem B223223 : Blo 147793 223223 := bstep (se 1 (by rfl) ⟨167417, by rfl⟩ : syracuseStep 223223 = 334835) B334835
theorem B223247 : Blo 147793 223247 := bstep (se 1 (by rfl) ⟨167435, by rfl⟩ : syracuseStep 223247 = 334871) B334871
theorem B190507 : Blo 147793 190507 := bstep (se 1 (by rfl) ⟨142880, by rfl⟩ : syracuseStep 190507 = 285761) B285761
theorem B223289 : Blo 147793 223289 := bstep (se 2 (by rfl) ⟨83733, by rfl⟩ : syracuseStep 223289 = 167467) B167467
theorem B223367 : Blo 147793 223367 := bstep (se 1 (by rfl) ⟨167525, by rfl⟩ : syracuseStep 223367 = 335051) B335051
theorem B256135 : Blo 147793 256135 := bstep (se 1 (by rfl) ⟨192101, by rfl⟩ : syracuseStep 256135 = 384203) B384203
theorem B223403 : Blo 147793 223403 := bstep (se 1 (by rfl) ⟨167552, by rfl⟩ : syracuseStep 223403 = 335105) B335105
theorem B1599689 : Blo 147793 1599689 := bstep (se 2 (by rfl) ⟨599883, by rfl⟩ : syracuseStep 1599689 = 1199767) B1199767
theorem B223433 : Blo 147793 223433 := bstep (se 2 (by rfl) ⟨83787, by rfl⟩ : syracuseStep 223433 = 167575) B167575
theorem B223547 : Blo 147793 223547 := bstep (se 1 (by rfl) ⟨167660, by rfl⟩ : syracuseStep 223547 = 335321) B335321
theorem B485747 : Blo 147793 485747 := bstep (se 1 (by rfl) ⟨364310, by rfl⟩ : syracuseStep 485747 = 728621) B728621
theorem B223607 : Blo 147793 223607 := bstep (se 1 (by rfl) ⟨167705, by rfl⟩ : syracuseStep 223607 = 335411) B335411
theorem B1141127 : Blo 147793 1141127 := bstep (se 1 (by rfl) ⟨855845, by rfl⟩ : syracuseStep 1141127 = 1711691) B1711691
theorem B223631 : Blo 147793 223631 := bstep (se 1 (by rfl) ⟨167723, by rfl⟩ : syracuseStep 223631 = 335447) B335447
theorem B846233 : Blo 147793 846233 := bstep (se 2 (by rfl) ⟨317337, by rfl⟩ : syracuseStep 846233 = 634675) B634675
theorem B223673 : Blo 147793 223673 := bstep (se 2 (by rfl) ⟨83877, by rfl⟩ : syracuseStep 223673 = 167755) B167755
theorem B223751 : Blo 147793 223751 := bstep (se 1 (by rfl) ⟨167813, by rfl⟩ : syracuseStep 223751 = 335627) B335627
theorem B223787 : Blo 147793 223787 := bstep (se 1 (by rfl) ⟨167840, by rfl⟩ : syracuseStep 223787 = 335681) B335681
theorem B518699 : Blo 147793 518699 := bstep (se 1 (by rfl) ⟨389024, by rfl⟩ : syracuseStep 518699 = 778049) B778049
theorem B223817 : Blo 147793 223817 := bstep (se 2 (by rfl) ⟨83931, by rfl⟩ : syracuseStep 223817 = 167863) B167863
theorem B223931 : Blo 147793 223931 := bstep (se 1 (by rfl) ⟨167948, by rfl⟩ : syracuseStep 223931 = 335897) B335897
theorem B813769 : Blo 147793 813769 := bstep (se 2 (by rfl) ⟨305163, by rfl⟩ : syracuseStep 813769 = 610327) B610327
theorem B223991 : Blo 147793 223991 := bstep (se 1 (by rfl) ⟨167993, by rfl⟩ : syracuseStep 223991 = 335987) B335987
theorem B224015 : Blo 147793 224015 := bstep (se 1 (by rfl) ⟨168011, by rfl⟩ : syracuseStep 224015 = 336023) B336023
theorem B224057 : Blo 147793 224057 := bstep (se 2 (by rfl) ⟨84021, by rfl⟩ : syracuseStep 224057 = 168043) B168043
theorem B224135 : Blo 147793 224135 := bstep (se 1 (by rfl) ⟨168101, by rfl⟩ : syracuseStep 224135 = 336203) B336203
theorem B224171 : Blo 147793 224171 := bstep (se 1 (by rfl) ⟨168128, by rfl⟩ : syracuseStep 224171 = 336257) B336257
theorem B224201 : Blo 147793 224201 := bstep (se 2 (by rfl) ⟨84075, by rfl⟩ : syracuseStep 224201 = 168151) B168151
theorem B191479 : Blo 147793 191479 := bstep (se 1 (by rfl) ⟨143609, by rfl⟩ : syracuseStep 191479 = 287219) B287219
theorem B224315 : Blo 147793 224315 := bstep (se 1 (by rfl) ⟨168236, by rfl⟩ : syracuseStep 224315 = 336473) B336473
theorem B224375 : Blo 147793 224375 := bstep (se 1 (by rfl) ⟨168281, by rfl⟩ : syracuseStep 224375 = 336563) B336563
theorem B224399 : Blo 147793 224399 := bstep (se 1 (by rfl) ⟨168299, by rfl⟩ : syracuseStep 224399 = 336599) B336599
theorem B224441 : Blo 147793 224441 := bstep (se 2 (by rfl) ⟨84165, by rfl⟩ : syracuseStep 224441 = 168331) B168331
theorem B715969 : Blo 147793 715969 := bstep (se 2 (by rfl) ⟨268488, by rfl⟩ : syracuseStep 715969 = 536977) B536977
theorem B224519 : Blo 147793 224519 := bstep (se 1 (by rfl) ⟨168389, by rfl⟩ : syracuseStep 224519 = 336779) B336779
theorem B224555 : Blo 147793 224555 := bstep (se 1 (by rfl) ⟨168416, by rfl⟩ : syracuseStep 224555 = 336833) B336833
theorem B191803 : Blo 147793 191803 := bstep (se 1 (by rfl) ⟨143852, by rfl⟩ : syracuseStep 191803 = 287705) B287705
theorem B224585 : Blo 147793 224585 := bstep (se 2 (by rfl) ⟨84219, by rfl⟩ : syracuseStep 224585 = 168439) B168439
theorem B224699 : Blo 147793 224699 := bstep (se 1 (by rfl) ⟨168524, by rfl⟩ : syracuseStep 224699 = 337049) B337049
theorem B224759 : Blo 147793 224759 := bstep (se 1 (by rfl) ⟨168569, by rfl⟩ : syracuseStep 224759 = 337139) B337139
theorem B224783 : Blo 147793 224783 := bstep (se 1 (by rfl) ⟨168587, by rfl⟩ : syracuseStep 224783 = 337175) B337175
theorem B224825 : Blo 147793 224825 := bstep (se 2 (by rfl) ⟨84309, by rfl⟩ : syracuseStep 224825 = 168619) B168619
theorem B224903 : Blo 147793 224903 := bstep (se 1 (by rfl) ⟨168677, by rfl⟩ : syracuseStep 224903 = 337355) B337355
theorem B224939 : Blo 147793 224939 := bstep (se 1 (by rfl) ⟨168704, by rfl⟩ : syracuseStep 224939 = 337409) B337409
theorem B749249 : Blo 147793 749249 := bstep (se 2 (by rfl) ⟨280968, by rfl⟩ : syracuseStep 749249 = 561937) B561937
theorem B224969 : Blo 147793 224969 := bstep (se 2 (by rfl) ⟨84363, by rfl⟩ : syracuseStep 224969 = 168727) B168727
theorem B225083 : Blo 147793 225083 := bstep (se 1 (by rfl) ⟨168812, by rfl⟩ : syracuseStep 225083 = 337625) B337625
theorem B2420549 : Blo 147793 2420549 := bstep (se 4 (by rfl) ⟨226926, by rfl⟩ : syracuseStep 2420549 = 453853) B453853
theorem B225143 : Blo 147793 225143 := bstep (se 1 (by rfl) ⟨168857, by rfl⟩ : syracuseStep 225143 = 337715) B337715
theorem B225167 : Blo 147793 225167 := bstep (se 1 (by rfl) ⟨168875, by rfl⟩ : syracuseStep 225167 = 337751) B337751
theorem B225209 : Blo 147793 225209 := bstep (se 2 (by rfl) ⟨84453, by rfl⟩ : syracuseStep 225209 = 168907) B168907
theorem B913355 : Blo 147793 913355 := bstep (se 1 (by rfl) ⟨685016, by rfl⟩ : syracuseStep 913355 = 1370033) B1370033
theorem B225287 : Blo 147793 225287 := bstep (se 1 (by rfl) ⟨168965, by rfl⟩ : syracuseStep 225287 = 337931) B337931
theorem B356363 : Blo 147793 356363 := bstep (se 1 (by rfl) ⟨267272, by rfl⟩ : syracuseStep 356363 = 534545) B534545
theorem B1339415 : Blo 147793 1339415 := bstep (se 1 (by rfl) ⟨1004561, by rfl⟩ : syracuseStep 1339415 = 2009123) B2009123
theorem B225323 : Blo 147793 225323 := bstep (se 1 (by rfl) ⟨168992, by rfl⟩ : syracuseStep 225323 = 337985) B337985
theorem B225353 : Blo 147793 225353 := bstep (se 2 (by rfl) ⟨84507, by rfl⟩ : syracuseStep 225353 = 169015) B169015
theorem B422023 : Blo 147793 422023 := bstep (se 1 (by rfl) ⟨316517, by rfl⟩ : syracuseStep 422023 = 633035) B633035
theorem B225467 : Blo 147793 225467 := bstep (se 1 (by rfl) ⟨169100, by rfl⟩ : syracuseStep 225467 = 338201) B338201
theorem B225527 : Blo 147793 225527 := bstep (se 1 (by rfl) ⟨169145, by rfl⟩ : syracuseStep 225527 = 338291) B338291
theorem B225551 : Blo 147793 225551 := bstep (se 1 (by rfl) ⟨169163, by rfl⟩ : syracuseStep 225551 = 338327) B338327
theorem B225593 : Blo 147793 225593 := bstep (se 2 (by rfl) ⟨84597, by rfl⟩ : syracuseStep 225593 = 169195) B169195
theorem B225671 : Blo 147793 225671 := bstep (se 1 (by rfl) ⟨169253, by rfl⟩ : syracuseStep 225671 = 338507) B338507
theorem B422297 : Blo 147793 422297 := bstep (se 2 (by rfl) ⟨158361, by rfl⟩ : syracuseStep 422297 = 316723) B316723
theorem B225707 : Blo 147793 225707 := bstep (se 1 (by rfl) ⟨169280, by rfl⟩ : syracuseStep 225707 = 338561) B338561
theorem B225737 : Blo 147793 225737 := bstep (se 2 (by rfl) ⟨84651, by rfl⟩ : syracuseStep 225737 = 169303) B169303
theorem B225851 : Blo 147793 225851 := bstep (se 1 (by rfl) ⟨169388, by rfl⟩ : syracuseStep 225851 = 338777) B338777
theorem B324155 : Blo 147793 324155 := bstep (se 1 (by rfl) ⟨243116, by rfl⟩ : syracuseStep 324155 = 486233) B486233
theorem B225911 : Blo 147793 225911 := bstep (se 1 (by rfl) ⟨169433, by rfl⟩ : syracuseStep 225911 = 338867) B338867
theorem B225935 : Blo 147793 225935 := bstep (se 1 (by rfl) ⟨169451, by rfl⟩ : syracuseStep 225935 = 338903) B338903
theorem B225977 : Blo 147793 225977 := bstep (se 2 (by rfl) ⟨84741, by rfl⟩ : syracuseStep 225977 = 169483) B169483
theorem B226055 : Blo 147793 226055 := bstep (se 1 (by rfl) ⟨169541, by rfl⟩ : syracuseStep 226055 = 339083) B339083
theorem B357131 : Blo 147793 357131 := bstep (se 1 (by rfl) ⟨267848, by rfl⟩ : syracuseStep 357131 = 535697) B535697
theorem B226091 : Blo 147793 226091 := bstep (se 1 (by rfl) ⟨169568, by rfl⟩ : syracuseStep 226091 = 339137) B339137
theorem B226121 : Blo 147793 226121 := bstep (se 2 (by rfl) ⟨84795, by rfl⟩ : syracuseStep 226121 = 169591) B169591
theorem B521095 : Blo 147793 521095 := bstep (se 1 (by rfl) ⟨390821, by rfl⟩ : syracuseStep 521095 = 781643) B781643
theorem B226235 : Blo 147793 226235 := bstep (se 1 (by rfl) ⟨169676, by rfl⟩ : syracuseStep 226235 = 339353) B339353
theorem B750545 : Blo 147793 750545 := bstep (se 2 (by rfl) ⟨281454, by rfl⟩ : syracuseStep 750545 = 562909) B562909
theorem B226295 : Blo 147793 226295 := bstep (se 1 (by rfl) ⟨169721, by rfl⟩ : syracuseStep 226295 = 339443) B339443
theorem B226319 : Blo 147793 226319 := bstep (se 1 (by rfl) ⟨169739, by rfl⟩ : syracuseStep 226319 = 339479) B339479
theorem B226361 : Blo 147793 226361 := bstep (se 2 (by rfl) ⟨84885, by rfl⟩ : syracuseStep 226361 = 169771) B169771
theorem B226439 : Blo 147793 226439 := bstep (se 1 (by rfl) ⟨169829, by rfl⟩ : syracuseStep 226439 = 339659) B339659
theorem B226475 : Blo 147793 226475 := bstep (se 1 (by rfl) ⟨169856, by rfl⟩ : syracuseStep 226475 = 339713) B339713
theorem B226505 : Blo 147793 226505 := bstep (se 2 (by rfl) ⟨84939, by rfl⟩ : syracuseStep 226505 = 169879) B169879
theorem B226619 : Blo 147793 226619 := bstep (se 1 (by rfl) ⟨169964, by rfl⟩ : syracuseStep 226619 = 339929) B339929
theorem B226679 : Blo 147793 226679 := bstep (se 1 (by rfl) ⟨170009, by rfl⟩ : syracuseStep 226679 = 340019) B340019
theorem B226703 : Blo 147793 226703 := bstep (se 1 (by rfl) ⟨170027, by rfl⟩ : syracuseStep 226703 = 340055) B340055
theorem B226745 : Blo 147793 226745 := bstep (se 2 (by rfl) ⟨85029, by rfl⟩ : syracuseStep 226745 = 170059) B170059
theorem B226823 : Blo 147793 226823 := bstep (se 1 (by rfl) ⟨170117, by rfl⟩ : syracuseStep 226823 = 340235) B340235
theorem B226859 : Blo 147793 226859 := bstep (se 1 (by rfl) ⟨170144, by rfl⟩ : syracuseStep 226859 = 340289) B340289
theorem B357947 : Blo 147793 357947 := bstep (se 1 (by rfl) ⟨268460, by rfl⟩ : syracuseStep 357947 = 536921) B536921
theorem B226889 : Blo 147793 226889 := bstep (se 2 (by rfl) ⟨85083, by rfl⟩ : syracuseStep 226889 = 170167) B170167
theorem B423539 : Blo 147793 423539 := bstep (se 1 (by rfl) ⟨317654, by rfl⟩ : syracuseStep 423539 = 635309) B635309
theorem B227003 : Blo 147793 227003 := bstep (se 1 (by rfl) ⟨170252, by rfl⟩ : syracuseStep 227003 = 340505) B340505
theorem B1210085 : Blo 147793 1210085 := bstep (se 4 (by rfl) ⟨113445, by rfl⟩ : syracuseStep 1210085 = 226891) B226891
theorem B227063 : Blo 147793 227063 := bstep (se 1 (by rfl) ⟨170297, by rfl⟩ : syracuseStep 227063 = 340595) B340595
theorem B227087 : Blo 147793 227087 := bstep (se 1 (by rfl) ⟨170315, by rfl⟩ : syracuseStep 227087 = 340631) B340631
theorem B227129 : Blo 147793 227129 := bstep (se 2 (by rfl) ⟨85173, by rfl⟩ : syracuseStep 227129 = 170347) B170347
theorem B980851 : Blo 147793 980851 := bstep (se 1 (by rfl) ⟨735638, by rfl⟩ : syracuseStep 980851 = 1471277) B1471277
theorem B227207 : Blo 147793 227207 := bstep (se 1 (by rfl) ⟨170405, by rfl⟩ : syracuseStep 227207 = 340811) B340811
theorem B718739 : Blo 147793 718739 := bstep (se 1 (by rfl) ⟨539054, by rfl⟩ : syracuseStep 718739 = 1078109) B1078109
theorem B227243 : Blo 147793 227243 := bstep (se 1 (by rfl) ⟨170432, by rfl⟩ : syracuseStep 227243 = 340865) B340865
theorem B227273 : Blo 147793 227273 := bstep (se 2 (by rfl) ⟨85227, by rfl⟩ : syracuseStep 227273 = 170455) B170455
theorem B849923 : Blo 147793 849923 := bstep (se 1 (by rfl) ⟨637442, by rfl⟩ : syracuseStep 849923 = 1274885) B1274885
theorem B227387 : Blo 147793 227387 := bstep (se 1 (by rfl) ⟨170540, by rfl⟩ : syracuseStep 227387 = 341081) B341081
theorem B227447 : Blo 147793 227447 := bstep (se 1 (by rfl) ⟨170585, by rfl⟩ : syracuseStep 227447 = 341171) B341171
theorem B227471 : Blo 147793 227471 := bstep (se 1 (by rfl) ⟨170603, by rfl⟩ : syracuseStep 227471 = 341207) B341207
theorem B227513 : Blo 147793 227513 := bstep (se 2 (by rfl) ⟨85317, by rfl⟩ : syracuseStep 227513 = 170635) B170635
theorem B227591 : Blo 147793 227591 := bstep (se 1 (by rfl) ⟨170693, by rfl⟩ : syracuseStep 227591 = 341387) B341387
theorem B1440017 : Blo 147793 1440017 := bstep (se 2 (by rfl) ⟨540006, by rfl⟩ : syracuseStep 1440017 = 1080013) B1080013
theorem B227627 : Blo 147793 227627 := bstep (se 1 (by rfl) ⟨170720, by rfl⟩ : syracuseStep 227627 = 341441) B341441
theorem B227657 : Blo 147793 227657 := bstep (se 2 (by rfl) ⟨85371, by rfl⟩ : syracuseStep 227657 = 170743) B170743
theorem B358775 : Blo 147793 358775 := bstep (se 1 (by rfl) ⟨269081, by rfl⟩ : syracuseStep 358775 = 538163) B538163
theorem B719239 : Blo 147793 719239 := bstep (se 1 (by rfl) ⟨539429, by rfl⟩ : syracuseStep 719239 = 1078859) B1078859
theorem B817921 : Blo 147793 817921 := bstep (se 2 (by rfl) ⟨306720, by rfl⟩ : syracuseStep 817921 = 613441) B613441
theorem B2063141 : Blo 147793 2063141 := bstep (se 4 (by rfl) ⟨193419, by rfl⟩ : syracuseStep 2063141 = 386839) B386839
theorem B1309603 : Blo 147793 1309603 := bstep (se 1 (by rfl) ⟨982202, by rfl⟩ : syracuseStep 1309603 = 1964405) B1964405
theorem B752651 : Blo 147793 752651 := bstep (se 1 (by rfl) ⟨564488, by rfl⟩ : syracuseStep 752651 = 1128977) B1128977
theorem B1375255 : Blo 147793 1375255 := bstep (se 1 (by rfl) ⟨1031441, by rfl⟩ : syracuseStep 1375255 = 2062883) B2062883
theorem B490583 : Blo 147793 490583 := bstep (se 1 (by rfl) ⟨367937, by rfl⟩ : syracuseStep 490583 = 735875) B735875
theorem B752813 : Blo 147793 752813 := bstep (se 3 (by rfl) ⟨141152, by rfl⟩ : syracuseStep 752813 = 282305) B282305
theorem B720161 : Blo 147793 720161 := bstep (se 2 (by rfl) ⟨270060, by rfl⟩ : syracuseStep 720161 = 540121) B540121
theorem B720413 : Blo 147793 720413 := bstep (se 3 (by rfl) ⟨135077, by rfl⟩ : syracuseStep 720413 = 270155) B270155
theorem B2719331 : Blo 147793 2719331 := bstep (se 1 (by rfl) ⟨2039498, by rfl⟩ : syracuseStep 2719331 = 4078997) B4078997
theorem B229111 : Blo 147793 229111 := bstep (se 1 (by rfl) ⟨171833, by rfl⟩ : syracuseStep 229111 = 343667) B343667
theorem B360377 : Blo 147793 360377 := bstep (se 2 (by rfl) ⟨135141, by rfl⟩ : syracuseStep 360377 = 270283) B270283
theorem B4915829 : Blo 147793 4915829 := bstep (se 5 (by rfl) ⟨230429, by rfl⟩ : syracuseStep 4915829 = 460859) B460859
theorem B722621 : Blo 147793 722621 := bstep (se 3 (by rfl) ⟨135491, by rfl⟩ : syracuseStep 722621 = 270983) B270983
theorem B854023 : Blo 147793 854023 := bstep (se 1 (by rfl) ⟨640517, by rfl⟩ : syracuseStep 854023 = 1281035) B1281035
theorem B919633 : Blo 147793 919633 := bstep (se 2 (by rfl) ⟨344862, by rfl⟩ : syracuseStep 919633 = 689725) B689725
theorem B428743 : Blo 147793 428743 := bstep (se 1 (by rfl) ⟨321557, by rfl⟩ : syracuseStep 428743 = 643115) B643115
theorem B2558789 : Blo 147793 2558789 := bstep (se 4 (by rfl) ⟨239886, by rfl⟩ : syracuseStep 2558789 = 479773) B479773
theorem B2362391 : Blo 147793 2362391 := bstep (se 1 (by rfl) ⟨1771793, by rfl⟩ : syracuseStep 2362391 = 3543587) B3543587
theorem B363599 : Blo 147793 363599 := bstep (se 1 (by rfl) ⟨272699, by rfl⟩ : syracuseStep 363599 = 545399) B545399
theorem B167035 : Blo 147793 167035 := bstep (se 1 (by rfl) ⟨125276, by rfl⟩ : syracuseStep 167035 = 250553) B250553
theorem B167503 : Blo 147793 167503 := bstep (se 1 (by rfl) ⟨125627, by rfl⟩ : syracuseStep 167503 = 251255) B251255
theorem B8261297 : Blo 147793 8261297 := bstep (se 2 (by rfl) ⟨3097986, by rfl⟩ : syracuseStep 8261297 = 6195973) B6195973
theorem B200441 : Blo 147793 200441 := bstep (se 2 (by rfl) ⟨75165, by rfl⟩ : syracuseStep 200441 = 150331) B150331
theorem B167899 : Blo 147793 167899 := bstep (se 1 (by rfl) ⟨125924, by rfl⟩ : syracuseStep 167899 = 251849) B251849
theorem B4362245 : Blo 147793 4362245 := bstep (se 4 (by rfl) ⟨408960, by rfl⟩ : syracuseStep 4362245 = 817921) B817921
theorem B3870989 : Blo 147793 3870989 := bstep (se 3 (by rfl) ⟨725810, by rfl⟩ : syracuseStep 3870989 = 1451621) B1451621
theorem B168367 : Blo 147793 168367 := bstep (se 1 (by rfl) ⟨126275, by rfl⟩ : syracuseStep 168367 = 252551) B252551
theorem B430555 : Blo 147793 430555 := bstep (se 1 (by rfl) ⟨322916, by rfl⟩ : syracuseStep 430555 = 645833) B645833
theorem B758483 : Blo 147793 758483 := bstep (se 1 (by rfl) ⟨568862, by rfl⟩ : syracuseStep 758483 = 1137725) B1137725
theorem B332639 : Blo 147793 332639 := bstep (se 1 (by rfl) ⟨249479, by rfl⟩ : syracuseStep 332639 = 498959) B498959
theorem B168799 : Blo 147793 168799 := bstep (se 1 (by rfl) ⟨126599, by rfl⟩ : syracuseStep 168799 = 253199) B253199
theorem B856939 : Blo 147793 856939 := bstep (se 1 (by rfl) ⟨642704, by rfl⟩ : syracuseStep 856939 = 1285409) B1285409
theorem B398267 : Blo 147793 398267 := bstep (se 1 (by rfl) ⟨298700, by rfl⟩ : syracuseStep 398267 = 597401) B597401
theorem B332819 : Blo 147793 332819 := bstep (se 1 (by rfl) ⟨249614, by rfl⟩ : syracuseStep 332819 = 499229) B499229
theorem B169159 : Blo 147793 169159 := bstep (se 1 (by rfl) ⟨126869, by rfl⟩ : syracuseStep 169159 = 253739) B253739
theorem B562423 : Blo 147793 562423 := bstep (se 1 (by rfl) ⟨421817, by rfl⟩ : syracuseStep 562423 = 843635) B843635
theorem B333161 : Blo 147793 333161 := bstep (se 2 (by rfl) ⟨124935, by rfl⟩ : syracuseStep 333161 = 249871) B249871
theorem B562697 : Blo 147793 562697 := bstep (se 2 (by rfl) ⟨211011, by rfl⟩ : syracuseStep 562697 = 422023) B422023
theorem B562727 : Blo 147793 562727 := bstep (se 1 (by rfl) ⟨422045, by rfl⟩ : syracuseStep 562727 = 844091) B844091
theorem B431831 : Blo 147793 431831 := bstep (se 1 (by rfl) ⟨323873, by rfl⟩ : syracuseStep 431831 = 647747) B647747
theorem B432047 : Blo 147793 432047 := bstep (se 1 (by rfl) ⟨324035, by rfl⟩ : syracuseStep 432047 = 648071) B648071
theorem B333755 : Blo 147793 333755 := bstep (se 1 (by rfl) ⟨250316, by rfl⟩ : syracuseStep 333755 = 500633) B500633
theorem B170023 : Blo 147793 170023 := bstep (se 1 (by rfl) ⟨127517, by rfl⟩ : syracuseStep 170023 = 255035) B255035
theorem B333881 : Blo 147793 333881 := bstep (se 2 (by rfl) ⟨125205, by rfl⟩ : syracuseStep 333881 = 250411) B250411
theorem B563395 : Blo 147793 563395 := bstep (se 1 (by rfl) ⟨422546, by rfl⟩ : syracuseStep 563395 = 845093) B845093
theorem B334223 : Blo 147793 334223 := bstep (se 1 (by rfl) ⟨250667, by rfl⟩ : syracuseStep 334223 = 501335) B501335
theorem B301531 : Blo 147793 301531 := bstep (se 1 (by rfl) ⟨226148, by rfl⟩ : syracuseStep 301531 = 452297) B452297
theorem B563699 : Blo 147793 563699 := bstep (se 1 (by rfl) ⟨422774, by rfl⟩ : syracuseStep 563699 = 845549) B845549
theorem B694793 : Blo 147793 694793 := bstep (se 2 (by rfl) ⟨260547, by rfl⟩ : syracuseStep 694793 = 521095) B521095
theorem B7740035 : Blo 147793 7740035 := bstep (se 1 (by rfl) ⟨5805026, by rfl⟩ : syracuseStep 7740035 = 11610053) B11610053
theorem B334547 : Blo 147793 334547 := bstep (se 1 (by rfl) ⟨250910, by rfl⟩ : syracuseStep 334547 = 501821) B501821
theorem B727811 : Blo 147793 727811 := bstep (se 1 (by rfl) ⟨545858, by rfl⟩ : syracuseStep 727811 = 1091717) B1091717
theorem B760751 : Blo 147793 760751 := bstep (se 1 (by rfl) ⟨570563, by rfl⟩ : syracuseStep 760751 = 1141127) B1141127
theorem B269239 : Blo 147793 269239 := bstep (se 1 (by rfl) ⟨201929, by rfl⟩ : syracuseStep 269239 = 403859) B403859
theorem B564155 : Blo 147793 564155 := bstep (se 1 (by rfl) ⟨423116, by rfl⟩ : syracuseStep 564155 = 846233) B846233
theorem B9182645 : Blo 147793 9182645 := bstep (se 5 (by rfl) ⟨430436, by rfl⟩ : syracuseStep 9182645 = 860873) B860873
theorem B269831 : Blo 147793 269831 := bstep (se 1 (by rfl) ⟨202373, by rfl⟩ : syracuseStep 269831 = 404747) B404747
theorem B335483 : Blo 147793 335483 := bstep (se 1 (by rfl) ⟨251612, by rfl⟩ : syracuseStep 335483 = 503225) B503225
theorem B335609 : Blo 147793 335609 := bstep (se 2 (by rfl) ⟨125853, by rfl⟩ : syracuseStep 335609 = 251707) B251707
theorem B499499 : Blo 147793 499499 := bstep (se 1 (by rfl) ⟨374624, by rfl⟩ : syracuseStep 499499 = 749249) B749249
theorem B1613699 : Blo 147793 1613699 := bstep (se 1 (by rfl) ⟨1210274, by rfl⟩ : syracuseStep 1613699 = 2420549) B2420549
theorem B237575 : Blo 147793 237575 := bstep (se 1 (by rfl) ⟨178181, by rfl⟩ : syracuseStep 237575 = 356363) B356363
theorem B335879 : Blo 147793 335879 := bstep (se 1 (by rfl) ⟨251909, by rfl⟩ : syracuseStep 335879 = 503819) B503819
theorem B892943 : Blo 147793 892943 := bstep (se 1 (by rfl) ⟨669707, by rfl⟩ : syracuseStep 892943 = 1339415) B1339415
theorem B499769 : Blo 147793 499769 := bstep (se 2 (by rfl) ⟨187413, by rfl⟩ : syracuseStep 499769 = 374827) B374827
theorem B335951 : Blo 147793 335951 := bstep (se 1 (by rfl) ⟨251963, by rfl⟩ : syracuseStep 335951 = 503927) B503927
theorem B1450163 : Blo 147793 1450163 := bstep (se 1 (by rfl) ⟨1087622, by rfl⟩ : syracuseStep 1450163 = 2175245) B2175245
theorem B205151 : Blo 147793 205151 := bstep (se 1 (by rfl) ⟨153863, by rfl⟩ : syracuseStep 205151 = 307727) B307727
theorem B500093 : Blo 147793 500093 := bstep (se 3 (by rfl) ⟨93767, by rfl⟩ : syracuseStep 500093 = 187535) B187535
theorem B270767 : Blo 147793 270767 := bstep (se 1 (by rfl) ⟨203075, by rfl⟩ : syracuseStep 270767 = 406151) B406151
theorem B336347 : Blo 147793 336347 := bstep (se 1 (by rfl) ⟨252260, by rfl⟩ : syracuseStep 336347 = 504521) B504521
theorem B238087 : Blo 147793 238087 := bstep (se 1 (by rfl) ⟨178565, by rfl⟩ : syracuseStep 238087 = 357131) B357131
theorem B958985 : Blo 147793 958985 := bstep (se 2 (by rfl) ⟨359619, by rfl⟩ : syracuseStep 958985 = 719239) B719239
theorem B500363 : Blo 147793 500363 := bstep (se 1 (by rfl) ⟨375272, by rfl⟩ : syracuseStep 500363 = 750545) B750545
theorem B1123145 : Blo 147793 1123145 := bstep (se 2 (by rfl) ⟨421179, by rfl⟩ : syracuseStep 1123145 = 842359) B842359
theorem B336815 : Blo 147793 336815 := bstep (se 1 (by rfl) ⟨252611, by rfl⟩ : syracuseStep 336815 = 505223) B505223
theorem B238631 : Blo 147793 238631 := bstep (se 1 (by rfl) ⟨178973, by rfl⟩ : syracuseStep 238631 = 357947) B357947
theorem B337067 : Blo 147793 337067 := bstep (se 1 (by rfl) ⟨252800, by rfl⟩ : syracuseStep 337067 = 505601) B505601
theorem B1746137 : Blo 147793 1746137 := bstep (se 2 (by rfl) ⟨654801, by rfl⟩ : syracuseStep 1746137 = 1309603) B1309603
theorem B1221925 : Blo 147793 1221925 := bstep (se 4 (by rfl) ⟨114555, by rfl⟩ : syracuseStep 1221925 = 229111) B229111
theorem B566615 : Blo 147793 566615 := bstep (se 1 (by rfl) ⟨424961, by rfl⟩ : syracuseStep 566615 = 849923) B849923
theorem B599561 : Blo 147793 599561 := bstep (se 2 (by rfl) ⟨224835, by rfl⟩ : syracuseStep 599561 = 449671) B449671
theorem B960011 : Blo 147793 960011 := bstep (se 1 (by rfl) ⟨720008, by rfl⟩ : syracuseStep 960011 = 1440017) B1440017
theorem B501281 : Blo 147793 501281 := bstep (se 2 (by rfl) ⟨187980, by rfl⟩ : syracuseStep 501281 = 375961) B375961
theorem B239183 : Blo 147793 239183 := bstep (se 1 (by rfl) ⟨179387, by rfl⟩ : syracuseStep 239183 = 358775) B358775
theorem B370273 : Blo 147793 370273 := bstep (se 2 (by rfl) ⟨138852, by rfl⟩ : syracuseStep 370273 = 277705) B277705
theorem B14526053 : Blo 147793 14526053 := bstep (se 4 (by rfl) ⟨1361817, by rfl⟩ : syracuseStep 14526053 = 2723635) B2723635
theorem B2762387 : Blo 147793 2762387 := bstep (se 1 (by rfl) ⟨2071790, by rfl⟩ : syracuseStep 2762387 = 4143581) B4143581
theorem B468679 : Blo 147793 468679 := bstep (se 1 (by rfl) ⟨351509, by rfl⟩ : syracuseStep 468679 = 703019) B703019
theorem B337607 : Blo 147793 337607 := bstep (se 1 (by rfl) ⟨253205, by rfl⟩ : syracuseStep 337607 = 506411) B506411
theorem B501497 : Blo 147793 501497 := bstep (se 2 (by rfl) ⟨188061, by rfl⟩ : syracuseStep 501497 = 376123) B376123
theorem B501767 : Blo 147793 501767 := bstep (se 1 (by rfl) ⟨376325, by rfl⟩ : syracuseStep 501767 = 752651) B752651
theorem B501875 : Blo 147793 501875 := bstep (se 1 (by rfl) ⟨376406, by rfl⟩ : syracuseStep 501875 = 752813) B752813
theorem B502145 : Blo 147793 502145 := bstep (se 2 (by rfl) ⟨188304, by rfl⟩ : syracuseStep 502145 = 376609) B376609
theorem B1812887 : Blo 147793 1812887 := bstep (se 1 (by rfl) ⟨1359665, by rfl⟩ : syracuseStep 1812887 = 2719331) B2719331
theorem B338471 : Blo 147793 338471 := bstep (se 1 (by rfl) ⟨253853, by rfl⟩ : syracuseStep 338471 = 507707) B507707
theorem B240251 : Blo 147793 240251 := bstep (se 1 (by rfl) ⟨180188, by rfl⟩ : syracuseStep 240251 = 360377) B360377
theorem B338795 : Blo 147793 338795 := bstep (se 1 (by rfl) ⟨254096, by rfl⟩ : syracuseStep 338795 = 508193) B508193
theorem B338849 : Blo 147793 338849 := bstep (se 2 (by rfl) ⟨127068, by rfl⟩ : syracuseStep 338849 = 254137) B254137
theorem B404399 : Blo 147793 404399 := bstep (se 1 (by rfl) ⟨303299, by rfl⟩ : syracuseStep 404399 = 606599) B606599
theorem B535709 : Blo 147793 535709 := bstep (se 3 (by rfl) ⟨100445, by rfl⟩ : syracuseStep 535709 = 200891) B200891
theorem B502955 : Blo 147793 502955 := bstep (se 1 (by rfl) ⟨377216, by rfl⟩ : syracuseStep 502955 = 754433) B754433
theorem B240887 : Blo 147793 240887 := bstep (se 1 (by rfl) ⟨180665, by rfl⟩ : syracuseStep 240887 = 361331) B361331
theorem B339191 : Blo 147793 339191 := bstep (se 1 (by rfl) ⟨254393, by rfl⟩ : syracuseStep 339191 = 508787) B508787
theorem B503495 : Blo 147793 503495 := bstep (se 1 (by rfl) ⟨377621, by rfl⟩ : syracuseStep 503495 = 755243) B755243
theorem B339785 : Blo 147793 339785 := bstep (se 2 (by rfl) ⟨127419, by rfl⟩ : syracuseStep 339785 = 254839) B254839
theorem B25472945 : Blo 147793 25472945 := bstep (se 2 (by rfl) ⟨9552354, by rfl⟩ : syracuseStep 25472945 = 19104709) B19104709
theorem B962675 : Blo 147793 962675 := bstep (se 1 (by rfl) ⟨722006, by rfl⟩ : syracuseStep 962675 = 1444013) B1444013
theorem B569501 : Blo 147793 569501 := bstep (se 3 (by rfl) ⟨106781, by rfl⟩ : syracuseStep 569501 = 213563) B213563
theorem B307631 : Blo 147793 307631 := bstep (se 1 (by rfl) ⟨230723, by rfl⟩ : syracuseStep 307631 = 461447) B461447
theorem B504359 : Blo 147793 504359 := bstep (se 1 (by rfl) ⟨378269, by rfl⟩ : syracuseStep 504359 = 756539) B756539
theorem B340577 : Blo 147793 340577 := bstep (se 2 (by rfl) ⟨127716, by rfl⟩ : syracuseStep 340577 = 255433) B255433
theorem B504467 : Blo 147793 504467 := bstep (se 1 (by rfl) ⟨378350, by rfl⟩ : syracuseStep 504467 = 756701) B756701
theorem B406205 : Blo 147793 406205 := bstep (se 3 (by rfl) ⟨76163, by rfl⟩ : syracuseStep 406205 = 152327) B152327
theorem B570185 : Blo 147793 570185 := bstep (se 2 (by rfl) ⟨213819, by rfl⟩ : syracuseStep 570185 = 427639) B427639
theorem B406367 : Blo 147793 406367 := bstep (se 1 (by rfl) ⟨304775, by rfl⟩ : syracuseStep 406367 = 609551) B609551
theorem B242527 : Blo 147793 242527 := bstep (se 1 (by rfl) ⟨181895, by rfl⟩ : syracuseStep 242527 = 363791) B363791
theorem B504683 : Blo 147793 504683 := bstep (se 1 (by rfl) ⟨378512, by rfl⟩ : syracuseStep 504683 = 757025) B757025
theorem B504737 : Blo 147793 504737 := bstep (se 2 (by rfl) ⟨189276, by rfl⟩ : syracuseStep 504737 = 378553) B378553
theorem B340919 : Blo 147793 340919 := bstep (se 1 (by rfl) ⟨255689, by rfl⟩ : syracuseStep 340919 = 511379) B511379
theorem B570685 : Blo 147793 570685 := bstep (se 3 (by rfl) ⟨107003, by rfl⟩ : syracuseStep 570685 = 214007) B214007
theorem B374159 : Blo 147793 374159 := bstep (se 1 (by rfl) ⟨280619, by rfl⟩ : syracuseStep 374159 = 561239) B561239
theorem B4634003 : Blo 147793 4634003 := bstep (se 1 (by rfl) ⟨3475502, by rfl⟩ : syracuseStep 4634003 = 6951005) B6951005
theorem B505331 : Blo 147793 505331 := bstep (se 1 (by rfl) ⟨378998, by rfl⟩ : syracuseStep 505331 = 757997) B757997
theorem B734707 : Blo 147793 734707 := bstep (se 1 (by rfl) ⟨551030, by rfl⟩ : syracuseStep 734707 = 1102061) B1102061
theorem B341513 : Blo 147793 341513 := bstep (se 2 (by rfl) ⟨128067, by rfl⟩ : syracuseStep 341513 = 256135) B256135
theorem B538235 : Blo 147793 538235 := bstep (se 1 (by rfl) ⟨403676, by rfl⟩ : syracuseStep 538235 = 807353) B807353
theorem B374483 : Blo 147793 374483 := bstep (se 1 (by rfl) ⟨280862, by rfl⟩ : syracuseStep 374483 = 561725) B561725
theorem B440057 : Blo 147793 440057 := bstep (se 2 (by rfl) ⟨165021, by rfl⟩ : syracuseStep 440057 = 330043) B330043
theorem B505871 : Blo 147793 505871 := bstep (se 1 (by rfl) ⟨379403, by rfl⟩ : syracuseStep 505871 = 758807) B758807
theorem B637085 : Blo 147793 637085 := bstep (se 3 (by rfl) ⟨119453, by rfl⟩ : syracuseStep 637085 = 238907) B238907
theorem B1227113 : Blo 147793 1227113 := bstep (se 2 (by rfl) ⟨460167, by rfl⟩ : syracuseStep 1227113 = 920335) B920335
theorem B4340101 : Blo 147793 4340101 := bstep (se 4 (by rfl) ⟨406884, by rfl⟩ : syracuseStep 4340101 = 813769) B813769
theorem B4340299 : Blo 147793 4340299 := bstep (se 1 (by rfl) ⟨3255224, by rfl⟩ : syracuseStep 4340299 = 6510449) B6510449
theorem B506465 : Blo 147793 506465 := bstep (se 2 (by rfl) ⟨189924, by rfl⟩ : syracuseStep 506465 = 379849) B379849
theorem B342967 : Blo 147793 342967 := bstep (se 1 (by rfl) ⟨257225, by rfl⟩ : syracuseStep 342967 = 514451) B514451
theorem B244667 : Blo 147793 244667 := bstep (se 1 (by rfl) ⟨183500, by rfl⟩ : syracuseStep 244667 = 367001) B367001
theorem B572417 : Blo 147793 572417 := bstep (se 2 (by rfl) ⟨214656, by rfl⟩ : syracuseStep 572417 = 429313) B429313
theorem B966107 : Blo 147793 966107 := bstep (se 1 (by rfl) ⟨724580, by rfl⟩ : syracuseStep 966107 = 1449161) B1449161
theorem B966289 : Blo 147793 966289 := bstep (se 2 (by rfl) ⟨362358, by rfl⟩ : syracuseStep 966289 = 724717) B724717
theorem B179911 : Blo 147793 179911 := bstep (se 1 (by rfl) ⟨134933, by rfl⟩ : syracuseStep 179911 = 269867) B269867
theorem B376751 : Blo 147793 376751 := bstep (se 1 (by rfl) ⟨282563, by rfl⟩ : syracuseStep 376751 = 565127) B565127
theorem B507923 : Blo 147793 507923 := bstep (se 1 (by rfl) ⟨380942, by rfl⟩ : syracuseStep 507923 = 761885) B761885
theorem B508247 : Blo 147793 508247 := bstep (se 1 (by rfl) ⟨381185, by rfl⟩ : syracuseStep 508247 = 762371) B762371
theorem B147807 : Blo 147793 147807 := bstep (se 1 (by rfl) ⟨110855, by rfl⟩ : syracuseStep 147807 = 221711) B221711
theorem B147835 : Blo 147793 147835 := bstep (se 1 (by rfl) ⟨110876, by rfl⟩ : syracuseStep 147835 = 221753) B221753
theorem B147887 : Blo 147793 147887 := bstep (se 1 (by rfl) ⟨110915, by rfl⟩ : syracuseStep 147887 = 221831) B221831
theorem B147911 : Blo 147793 147911 := bstep (se 1 (by rfl) ⟨110933, by rfl⟩ : syracuseStep 147911 = 221867) B221867
theorem B541129 : Blo 147793 541129 := bstep (se 2 (by rfl) ⟨202923, by rfl⟩ : syracuseStep 541129 = 405847) B405847
theorem B147931 : Blo 147793 147931 := bstep (se 1 (by rfl) ⟨110948, by rfl⟩ : syracuseStep 147931 = 221897) B221897
theorem B377369 : Blo 147793 377369 := bstep (se 2 (by rfl) ⟨141513, by rfl⟩ : syracuseStep 377369 = 283027) B283027
theorem B148007 : Blo 147793 148007 := bstep (se 1 (by rfl) ⟨111005, by rfl⟩ : syracuseStep 148007 = 222011) B222011
theorem B148047 : Blo 147793 148047 := bstep (se 1 (by rfl) ⟨111035, by rfl⟩ : syracuseStep 148047 = 222071) B222071
theorem B148063 : Blo 147793 148063 := bstep (se 1 (by rfl) ⟨111047, by rfl⟩ : syracuseStep 148063 = 222095) B222095
theorem B148091 : Blo 147793 148091 := bstep (se 1 (by rfl) ⟨111068, by rfl⟩ : syracuseStep 148091 = 222137) B222137
theorem B574087 : Blo 147793 574087 := bstep (se 1 (by rfl) ⟨430565, by rfl⟩ : syracuseStep 574087 = 861131) B861131
theorem B148143 : Blo 147793 148143 := bstep (se 1 (by rfl) ⟨111107, by rfl⟩ : syracuseStep 148143 = 222215) B222215
theorem B148167 : Blo 147793 148167 := bstep (se 1 (by rfl) ⟨111125, by rfl⟩ : syracuseStep 148167 = 222251) B222251
theorem B148187 : Blo 147793 148187 := bstep (se 1 (by rfl) ⟨111140, by rfl⟩ : syracuseStep 148187 = 222281) B222281
theorem B148263 : Blo 147793 148263 := bstep (se 1 (by rfl) ⟨111197, by rfl⟩ : syracuseStep 148263 = 222395) B222395
theorem B148303 : Blo 147793 148303 := bstep (se 1 (by rfl) ⟨111227, by rfl⟩ : syracuseStep 148303 = 222455) B222455
theorem B148319 : Blo 147793 148319 := bstep (se 1 (by rfl) ⟨111239, by rfl⟩ : syracuseStep 148319 = 222479) B222479
theorem B443243 : Blo 147793 443243 := bstep (se 1 (by rfl) ⟨332432, by rfl⟩ : syracuseStep 443243 = 664865) B664865
theorem B148347 : Blo 147793 148347 := bstep (se 1 (by rfl) ⟨111260, by rfl⟩ : syracuseStep 148347 = 222521) B222521
theorem B148399 : Blo 147793 148399 := bstep (se 1 (by rfl) ⟨111299, by rfl⟩ : syracuseStep 148399 = 222599) B222599
theorem B574391 : Blo 147793 574391 := bstep (se 1 (by rfl) ⟨430793, by rfl⟩ : syracuseStep 574391 = 861587) B861587
theorem B148423 : Blo 147793 148423 := bstep (se 1 (by rfl) ⟨111317, by rfl⟩ : syracuseStep 148423 = 222635) B222635
theorem B148443 : Blo 147793 148443 := bstep (se 1 (by rfl) ⟨111332, by rfl⟩ : syracuseStep 148443 = 222665) B222665
theorem B3818501 : Blo 147793 3818501 := bstep (se 4 (by rfl) ⟨357984, by rfl⟩ : syracuseStep 3818501 = 715969) B715969
theorem B148519 : Blo 147793 148519 := bstep (se 1 (by rfl) ⟨111389, by rfl⟩ : syracuseStep 148519 = 222779) B222779
theorem B148559 : Blo 147793 148559 := bstep (se 1 (by rfl) ⟨111419, by rfl⟩ : syracuseStep 148559 = 222839) B222839
theorem B148575 : Blo 147793 148575 := bstep (se 1 (by rfl) ⟨111431, by rfl⟩ : syracuseStep 148575 = 222863) B222863
theorem B3327095 : Blo 147793 3327095 := bstep (se 1 (by rfl) ⟨2495321, by rfl⟩ : syracuseStep 3327095 = 4990643) B4990643
theorem B148603 : Blo 147793 148603 := bstep (se 1 (by rfl) ⟨111452, by rfl⟩ : syracuseStep 148603 = 222905) B222905
theorem B541853 : Blo 147793 541853 := bstep (se 3 (by rfl) ⟨101597, by rfl⟩ : syracuseStep 541853 = 203195) B203195
theorem B148655 : Blo 147793 148655 := bstep (se 1 (by rfl) ⟨111491, by rfl⟩ : syracuseStep 148655 = 222983) B222983
theorem B148679 : Blo 147793 148679 := bstep (se 1 (by rfl) ⟨111509, by rfl⟩ : syracuseStep 148679 = 223019) B223019
theorem B148699 : Blo 147793 148699 := bstep (se 1 (by rfl) ⟨111524, by rfl⟩ : syracuseStep 148699 = 223049) B223049
theorem B148775 : Blo 147793 148775 := bstep (se 1 (by rfl) ⟨111581, by rfl⟩ : syracuseStep 148775 = 223163) B223163
theorem B148815 : Blo 147793 148815 := bstep (se 1 (by rfl) ⟨111611, by rfl⟩ : syracuseStep 148815 = 223223) B223223
theorem B148831 : Blo 147793 148831 := bstep (se 1 (by rfl) ⟨111623, by rfl⟩ : syracuseStep 148831 = 223247) B223247
theorem B148859 : Blo 147793 148859 := bstep (se 1 (by rfl) ⟨111644, by rfl⟩ : syracuseStep 148859 = 223289) B223289
theorem B640381 : Blo 147793 640381 := bstep (se 3 (by rfl) ⟨120071, by rfl⟩ : syracuseStep 640381 = 240143) B240143
theorem B509327 : Blo 147793 509327 := bstep (se 1 (by rfl) ⟨381995, by rfl⟩ : syracuseStep 509327 = 763991) B763991
theorem B148911 : Blo 147793 148911 := bstep (se 1 (by rfl) ⟨111683, by rfl⟩ : syracuseStep 148911 = 223367) B223367
theorem B148935 : Blo 147793 148935 := bstep (se 1 (by rfl) ⟨111701, by rfl⟩ : syracuseStep 148935 = 223403) B223403
theorem B1066459 : Blo 147793 1066459 := bstep (se 1 (by rfl) ⟨799844, by rfl⟩ : syracuseStep 1066459 = 1599689) B1599689
theorem B148955 : Blo 147793 148955 := bstep (se 1 (by rfl) ⟨111716, by rfl⟩ : syracuseStep 148955 = 223433) B223433
theorem B149031 : Blo 147793 149031 := bstep (se 1 (by rfl) ⟨111773, by rfl⟩ : syracuseStep 149031 = 223547) B223547
theorem B149071 : Blo 147793 149071 := bstep (se 1 (by rfl) ⟨111803, by rfl⟩ : syracuseStep 149071 = 223607) B223607
theorem B149087 : Blo 147793 149087 := bstep (se 1 (by rfl) ⟨111815, by rfl⟩ : syracuseStep 149087 = 223631) B223631
theorem B149115 : Blo 147793 149115 := bstep (se 1 (by rfl) ⟨111836, by rfl⟩ : syracuseStep 149115 = 223673) B223673
theorem B149167 : Blo 147793 149167 := bstep (se 1 (by rfl) ⟨111875, by rfl⟩ : syracuseStep 149167 = 223751) B223751
theorem B149191 : Blo 147793 149191 := bstep (se 1 (by rfl) ⟨111893, by rfl⟩ : syracuseStep 149191 = 223787) B223787
theorem B345799 : Blo 147793 345799 := bstep (se 1 (by rfl) ⟨259349, by rfl⟩ : syracuseStep 345799 = 518699) B518699
theorem B1296071 : Blo 147793 1296071 := bstep (se 1 (by rfl) ⟨972053, by rfl⟩ : syracuseStep 1296071 = 1944107) B1944107
theorem B509651 : Blo 147793 509651 := bstep (se 1 (by rfl) ⟨382238, by rfl⟩ : syracuseStep 509651 = 764477) B764477
theorem B149211 : Blo 147793 149211 := bstep (se 1 (by rfl) ⟨111908, by rfl⟩ : syracuseStep 149211 = 223817) B223817
theorem B149287 : Blo 147793 149287 := bstep (se 1 (by rfl) ⟨111965, by rfl⟩ : syracuseStep 149287 = 223931) B223931
theorem B149327 : Blo 147793 149327 := bstep (se 1 (by rfl) ⟨111995, by rfl⟩ : syracuseStep 149327 = 223991) B223991
theorem B149343 : Blo 147793 149343 := bstep (se 1 (by rfl) ⟨112007, by rfl⟩ : syracuseStep 149343 = 224015) B224015
theorem B149371 : Blo 147793 149371 := bstep (se 1 (by rfl) ⟨112028, by rfl⟩ : syracuseStep 149371 = 224057) B224057
theorem B4638617 : Blo 147793 4638617 := bstep (se 2 (by rfl) ⟨1739481, by rfl⟩ : syracuseStep 4638617 = 3478963) B3478963
theorem B149423 : Blo 147793 149423 := bstep (se 1 (by rfl) ⟨112067, by rfl⟩ : syracuseStep 149423 = 224135) B224135
theorem B149447 : Blo 147793 149447 := bstep (se 1 (by rfl) ⟨112085, by rfl⟩ : syracuseStep 149447 = 224171) B224171
theorem B149467 : Blo 147793 149467 := bstep (se 1 (by rfl) ⟨112100, by rfl⟩ : syracuseStep 149467 = 224201) B224201
theorem B149543 : Blo 147793 149543 := bstep (se 1 (by rfl) ⟨112157, by rfl⟩ : syracuseStep 149543 = 224315) B224315
theorem B575545 : Blo 147793 575545 := bstep (se 2 (by rfl) ⟨215829, by rfl⟩ : syracuseStep 575545 = 431659) B431659
theorem B149583 : Blo 147793 149583 := bstep (se 1 (by rfl) ⟨112187, by rfl⟩ : syracuseStep 149583 = 224375) B224375
theorem B149599 : Blo 147793 149599 := bstep (se 1 (by rfl) ⟨112199, by rfl⟩ : syracuseStep 149599 = 224399) B224399
theorem B510067 : Blo 147793 510067 := bstep (se 1 (by rfl) ⟨382550, by rfl⟩ : syracuseStep 510067 = 765101) B765101
theorem B149627 : Blo 147793 149627 := bstep (se 1 (by rfl) ⟨112220, by rfl⟩ : syracuseStep 149627 = 224441) B224441
theorem B149679 : Blo 147793 149679 := bstep (se 1 (by rfl) ⟨112259, by rfl⟩ : syracuseStep 149679 = 224519) B224519
theorem B149703 : Blo 147793 149703 := bstep (se 1 (by rfl) ⟨112277, by rfl⟩ : syracuseStep 149703 = 224555) B224555
theorem B149723 : Blo 147793 149723 := bstep (se 1 (by rfl) ⟨112292, by rfl⟩ : syracuseStep 149723 = 224585) B224585
theorem B149799 : Blo 147793 149799 := bstep (se 1 (by rfl) ⟨112349, by rfl⟩ : syracuseStep 149799 = 224699) B224699
theorem B149839 : Blo 147793 149839 := bstep (se 1 (by rfl) ⟨112379, by rfl⟩ : syracuseStep 149839 = 224759) B224759
theorem B149855 : Blo 147793 149855 := bstep (se 1 (by rfl) ⟨112391, by rfl⟩ : syracuseStep 149855 = 224783) B224783
theorem B575849 : Blo 147793 575849 := bstep (se 2 (by rfl) ⟨215943, by rfl⟩ : syracuseStep 575849 = 431887) B431887
theorem B149883 : Blo 147793 149883 := bstep (se 1 (by rfl) ⟨112412, by rfl⟩ : syracuseStep 149883 = 224825) B224825
theorem B149935 : Blo 147793 149935 := bstep (se 1 (by rfl) ⟨112451, by rfl⟩ : syracuseStep 149935 = 224903) B224903
theorem B149959 : Blo 147793 149959 := bstep (se 1 (by rfl) ⟨112469, by rfl⟩ : syracuseStep 149959 = 224939) B224939
theorem B149979 : Blo 147793 149979 := bstep (se 1 (by rfl) ⟨112484, by rfl⟩ : syracuseStep 149979 = 224969) B224969
theorem B150055 : Blo 147793 150055 := bstep (se 1 (by rfl) ⟨112541, by rfl⟩ : syracuseStep 150055 = 225083) B225083
theorem B150095 : Blo 147793 150095 := bstep (se 1 (by rfl) ⟨112571, by rfl⟩ : syracuseStep 150095 = 225143) B225143
theorem B150111 : Blo 147793 150111 := bstep (se 1 (by rfl) ⟨112583, by rfl⟩ : syracuseStep 150111 = 225167) B225167
theorem B150139 : Blo 147793 150139 := bstep (se 1 (by rfl) ⟨112604, by rfl⟩ : syracuseStep 150139 = 225209) B225209
theorem B608903 : Blo 147793 608903 := bstep (se 1 (by rfl) ⟨456677, by rfl⟩ : syracuseStep 608903 = 913355) B913355
theorem B150191 : Blo 147793 150191 := bstep (se 1 (by rfl) ⟨112643, by rfl⟩ : syracuseStep 150191 = 225287) B225287
theorem B150215 : Blo 147793 150215 := bstep (se 1 (by rfl) ⟨112661, by rfl⟩ : syracuseStep 150215 = 225323) B225323
theorem B150235 : Blo 147793 150235 := bstep (se 1 (by rfl) ⟨112676, by rfl⟩ : syracuseStep 150235 = 225353) B225353
theorem B4410085 : Blo 147793 4410085 := bstep (se 4 (by rfl) ⟨413445, by rfl⟩ : syracuseStep 4410085 = 826891) B826891
theorem B150311 : Blo 147793 150311 := bstep (se 1 (by rfl) ⟨112733, by rfl⟩ : syracuseStep 150311 = 225467) B225467
theorem B150351 : Blo 147793 150351 := bstep (se 1 (by rfl) ⟨112763, by rfl⟩ : syracuseStep 150351 = 225527) B225527
theorem B150367 : Blo 147793 150367 := bstep (se 1 (by rfl) ⟨112775, by rfl⟩ : syracuseStep 150367 = 225551) B225551
theorem B510839 : Blo 147793 510839 := bstep (se 1 (by rfl) ⟨383129, by rfl⟩ : syracuseStep 510839 = 766259) B766259
theorem B150395 : Blo 147793 150395 := bstep (se 1 (by rfl) ⟨112796, by rfl⟩ : syracuseStep 150395 = 225593) B225593
theorem B150447 : Blo 147793 150447 := bstep (se 1 (by rfl) ⟨112835, by rfl⟩ : syracuseStep 150447 = 225671) B225671
theorem B281531 : Blo 147793 281531 := bstep (se 1 (by rfl) ⟨211148, by rfl⟩ : syracuseStep 281531 = 422297) B422297
theorem B150471 : Blo 147793 150471 := bstep (se 1 (by rfl) ⟨112853, by rfl⟩ : syracuseStep 150471 = 225707) B225707
theorem B150491 : Blo 147793 150491 := bstep (se 1 (by rfl) ⟨112868, by rfl⟩ : syracuseStep 150491 = 225737) B225737
theorem B248795 : Blo 147793 248795 := bstep (se 1 (by rfl) ⟨186596, by rfl⟩ : syracuseStep 248795 = 373193) B373193
theorem B150567 : Blo 147793 150567 := bstep (se 1 (by rfl) ⟨112925, by rfl⟩ : syracuseStep 150567 = 225851) B225851
theorem B216103 : Blo 147793 216103 := bstep (se 1 (by rfl) ⟨162077, by rfl⟩ : syracuseStep 216103 = 324155) B324155
theorem B379961 : Blo 147793 379961 := bstep (se 2 (by rfl) ⟨142485, by rfl⟩ : syracuseStep 379961 = 284971) B284971
theorem B150607 : Blo 147793 150607 := bstep (se 1 (by rfl) ⟨112955, by rfl⟩ : syracuseStep 150607 = 225911) B225911
theorem B511055 : Blo 147793 511055 := bstep (se 1 (by rfl) ⟨383291, by rfl⟩ : syracuseStep 511055 = 766583) B766583
theorem B150623 : Blo 147793 150623 := bstep (se 1 (by rfl) ⟨112967, by rfl⟩ : syracuseStep 150623 = 225935) B225935
theorem B150651 : Blo 147793 150651 := bstep (se 1 (by rfl) ⟨112988, by rfl⟩ : syracuseStep 150651 = 225977) B225977
theorem B150703 : Blo 147793 150703 := bstep (se 1 (by rfl) ⟨113027, by rfl⟩ : syracuseStep 150703 = 226055) B226055
theorem B150727 : Blo 147793 150727 := bstep (se 1 (by rfl) ⟨113045, by rfl⟩ : syracuseStep 150727 = 226091) B226091
theorem B150747 : Blo 147793 150747 := bstep (se 1 (by rfl) ⟨113060, by rfl⟩ : syracuseStep 150747 = 226121) B226121
theorem B150823 : Blo 147793 150823 := bstep (se 1 (by rfl) ⟨113117, by rfl⟩ : syracuseStep 150823 = 226235) B226235
theorem B150863 : Blo 147793 150863 := bstep (se 1 (by rfl) ⟨113147, by rfl⟩ : syracuseStep 150863 = 226295) B226295
theorem B150879 : Blo 147793 150879 := bstep (se 1 (by rfl) ⟨113159, by rfl⟩ : syracuseStep 150879 = 226319) B226319
theorem B150907 : Blo 147793 150907 := bstep (se 1 (by rfl) ⟨113180, by rfl⟩ : syracuseStep 150907 = 226361) B226361
theorem B282017 : Blo 147793 282017 := bstep (se 2 (by rfl) ⟨105756, by rfl⟩ : syracuseStep 282017 = 211513) B211513
theorem B150959 : Blo 147793 150959 := bstep (se 1 (by rfl) ⟨113219, by rfl⟩ : syracuseStep 150959 = 226439) B226439
theorem B150983 : Blo 147793 150983 := bstep (se 1 (by rfl) ⟨113237, by rfl⟩ : syracuseStep 150983 = 226475) B226475
theorem B511433 : Blo 147793 511433 := bstep (se 2 (by rfl) ⟨191787, by rfl⟩ : syracuseStep 511433 = 383575) B383575
theorem B511451 : Blo 147793 511451 := bstep (se 1 (by rfl) ⟨383588, by rfl⟩ : syracuseStep 511451 = 767177) B767177
theorem B151003 : Blo 147793 151003 := bstep (se 1 (by rfl) ⟨113252, by rfl⟩ : syracuseStep 151003 = 226505) B226505
theorem B151079 : Blo 147793 151079 := bstep (se 1 (by rfl) ⟨113309, by rfl⟩ : syracuseStep 151079 = 226619) B226619
theorem B151119 : Blo 147793 151119 := bstep (se 1 (by rfl) ⟨113339, by rfl⟩ : syracuseStep 151119 = 226679) B226679
theorem B151135 : Blo 147793 151135 := bstep (se 1 (by rfl) ⟨113351, by rfl⟩ : syracuseStep 151135 = 226703) B226703
theorem B151163 : Blo 147793 151163 := bstep (se 1 (by rfl) ⟨113372, by rfl⟩ : syracuseStep 151163 = 226745) B226745
theorem B151215 : Blo 147793 151215 := bstep (se 1 (by rfl) ⟨113411, by rfl⟩ : syracuseStep 151215 = 226823) B226823
theorem B151239 : Blo 147793 151239 := bstep (se 1 (by rfl) ⟨113429, by rfl⟩ : syracuseStep 151239 = 226859) B226859
theorem B511703 : Blo 147793 511703 := bstep (se 1 (by rfl) ⟨383777, by rfl⟩ : syracuseStep 511703 = 767555) B767555
theorem B151259 : Blo 147793 151259 := bstep (se 1 (by rfl) ⟨113444, by rfl⟩ : syracuseStep 151259 = 226889) B226889
theorem B282359 : Blo 147793 282359 := bstep (se 1 (by rfl) ⟨211769, by rfl⟩ : syracuseStep 282359 = 423539) B423539
theorem B151335 : Blo 147793 151335 := bstep (se 1 (by rfl) ⟨113501, by rfl⟩ : syracuseStep 151335 = 227003) B227003
theorem B806723 : Blo 147793 806723 := bstep (se 1 (by rfl) ⟨605042, by rfl⟩ : syracuseStep 806723 = 1210085) B1210085
theorem B151375 : Blo 147793 151375 := bstep (se 1 (by rfl) ⟨113531, by rfl⟩ : syracuseStep 151375 = 227063) B227063
theorem B151391 : Blo 147793 151391 := bstep (se 1 (by rfl) ⟨113543, by rfl⟩ : syracuseStep 151391 = 227087) B227087
theorem B151419 : Blo 147793 151419 := bstep (se 1 (by rfl) ⟨113564, by rfl⟩ : syracuseStep 151419 = 227129) B227129
theorem B249743 : Blo 147793 249743 := bstep (se 1 (by rfl) ⟨187307, by rfl⟩ : syracuseStep 249743 = 374615) B374615
theorem B151471 : Blo 147793 151471 := bstep (se 1 (by rfl) ⟨113603, by rfl⟩ : syracuseStep 151471 = 227207) B227207
theorem B511919 : Blo 147793 511919 := bstep (se 1 (by rfl) ⟨383939, by rfl⟩ : syracuseStep 511919 = 767879) B767879
theorem B479159 : Blo 147793 479159 := bstep (se 1 (by rfl) ⟨359369, by rfl⟩ : syracuseStep 479159 = 718739) B718739
theorem B151495 : Blo 147793 151495 := bstep (se 1 (by rfl) ⟨113621, by rfl⟩ : syracuseStep 151495 = 227243) B227243
theorem B151515 : Blo 147793 151515 := bstep (se 1 (by rfl) ⟨113636, by rfl⟩ : syracuseStep 151515 = 227273) B227273
theorem B151591 : Blo 147793 151591 := bstep (se 1 (by rfl) ⟨113693, by rfl⟩ : syracuseStep 151591 = 227387) B227387
theorem B151631 : Blo 147793 151631 := bstep (se 1 (by rfl) ⟨113723, by rfl⟩ : syracuseStep 151631 = 227447) B227447
theorem B151647 : Blo 147793 151647 := bstep (se 1 (by rfl) ⟨113735, by rfl⟩ : syracuseStep 151647 = 227471) B227471
theorem B249979 : Blo 147793 249979 := bstep (se 1 (by rfl) ⟨187484, by rfl⟩ : syracuseStep 249979 = 374969) B374969
theorem B151675 : Blo 147793 151675 := bstep (se 1 (by rfl) ⟨113756, by rfl⟩ : syracuseStep 151675 = 227513) B227513
theorem B151727 : Blo 147793 151727 := bstep (se 1 (by rfl) ⟨113795, by rfl⟩ : syracuseStep 151727 = 227591) B227591
theorem B151751 : Blo 147793 151751 := bstep (se 1 (by rfl) ⟨113813, by rfl⟩ : syracuseStep 151751 = 227627) B227627
theorem B151771 : Blo 147793 151771 := bstep (se 1 (by rfl) ⟨113828, by rfl⟩ : syracuseStep 151771 = 227657) B227657
theorem B643457 : Blo 147793 643457 := bstep (se 2 (by rfl) ⟨241296, by rfl⟩ : syracuseStep 643457 = 482593) B482593
theorem B381449 : Blo 147793 381449 := bstep (se 2 (by rfl) ⟨143043, by rfl⟩ : syracuseStep 381449 = 286087) B286087
theorem B905863 : Blo 147793 905863 := bstep (se 1 (by rfl) ⟨679397, by rfl⟩ : syracuseStep 905863 = 1358795) B1358795
theorem B480107 : Blo 147793 480107 := bstep (se 1 (by rfl) ⟨360080, by rfl⟩ : syracuseStep 480107 = 720161) B720161
theorem B447419 : Blo 147793 447419 := bstep (se 1 (by rfl) ⟨335564, by rfl⟩ : syracuseStep 447419 = 671129) B671129
theorem B250843 : Blo 147793 250843 := bstep (se 1 (by rfl) ⟨188132, by rfl⟩ : syracuseStep 250843 = 376265) B376265
theorem B283657 : Blo 147793 283657 := bstep (se 2 (by rfl) ⟨106371, by rfl⟩ : syracuseStep 283657 = 212743) B212743
theorem B480275 : Blo 147793 480275 := bstep (se 1 (by rfl) ⟨360206, by rfl⟩ : syracuseStep 480275 = 720413) B720413
theorem B1692737 : Blo 147793 1692737 := bstep (se 2 (by rfl) ⟨634776, by rfl⟩ : syracuseStep 1692737 = 1269553) B1269553
theorem B283999 : Blo 147793 283999 := bstep (se 1 (by rfl) ⟨212999, by rfl⟩ : syracuseStep 283999 = 425999) B425999
theorem B1267163 : Blo 147793 1267163 := bstep (se 1 (by rfl) ⟨950372, by rfl⟩ : syracuseStep 1267163 = 1900745) B1900745
theorem B251471 : Blo 147793 251471 := bstep (se 1 (by rfl) ⟨188603, by rfl⟩ : syracuseStep 251471 = 377207) B377207
theorem B1136267 : Blo 147793 1136267 := bstep (se 1 (by rfl) ⟨852200, by rfl⟩ : syracuseStep 1136267 = 1704401) B1704401
theorem B382603 : Blo 147793 382603 := bstep (se 1 (by rfl) ⟨286952, by rfl⟩ : syracuseStep 382603 = 573905) B573905
theorem B644755 : Blo 147793 644755 := bstep (se 1 (by rfl) ⟨483566, by rfl⟩ : syracuseStep 644755 = 967133) B967133
theorem B480953 : Blo 147793 480953 := bstep (se 2 (by rfl) ⟨180357, by rfl⟩ : syracuseStep 480953 = 360715) B360715
theorem B1627847 : Blo 147793 1627847 := bstep (se 1 (by rfl) ⟨1220885, by rfl⟩ : syracuseStep 1627847 = 2441771) B2441771
theorem B382907 : Blo 147793 382907 := bstep (se 1 (by rfl) ⟨287180, by rfl⟩ : syracuseStep 382907 = 574361) B574361
theorem B4315193 : Blo 147793 4315193 := bstep (se 2 (by rfl) ⟨1618197, by rfl⟩ : syracuseStep 4315193 = 3236395) B3236395
theorem B579737 : Blo 147793 579737 := bstep (se 2 (by rfl) ⟨217401, by rfl⟩ : syracuseStep 579737 = 434803) B434803
theorem B4053149 : Blo 147793 4053149 := bstep (se 3 (by rfl) ⟨759965, by rfl⟩ : syracuseStep 4053149 = 1519931) B1519931
theorem B317611 : Blo 147793 317611 := bstep (se 1 (by rfl) ⟨238208, by rfl⟩ : syracuseStep 317611 = 476417) B476417
theorem B252335 : Blo 147793 252335 := bstep (se 1 (by rfl) ⟨189251, by rfl⟩ : syracuseStep 252335 = 378503) B378503
theorem B285115 : Blo 147793 285115 := bstep (se 1 (by rfl) ⟨213836, by rfl⟩ : syracuseStep 285115 = 427673) B427673
theorem B285191 : Blo 147793 285191 := bstep (se 1 (by rfl) ⟨213893, by rfl⟩ : syracuseStep 285191 = 427787) B427787
theorem B383687 : Blo 147793 383687 := bstep (se 1 (by rfl) ⟨287765, by rfl⟩ : syracuseStep 383687 = 575531) B575531
theorem B383737 : Blo 147793 383737 := bstep (se 2 (by rfl) ⟨143901, by rfl⟩ : syracuseStep 383737 = 287803) B287803
theorem B252767 : Blo 147793 252767 := bstep (se 1 (by rfl) ⟨189575, by rfl⟩ : syracuseStep 252767 = 379151) B379151
theorem B285601 : Blo 147793 285601 := bstep (se 2 (by rfl) ⟨107100, by rfl⟩ : syracuseStep 285601 = 214201) B214201
theorem B187591 : Blo 147793 187591 := bstep (se 1 (by rfl) ⟨140693, by rfl⟩ : syracuseStep 187591 = 281387) B281387
theorem B285943 : Blo 147793 285943 := bstep (se 1 (by rfl) ⟨214457, by rfl⟩ : syracuseStep 285943 = 428915) B428915
theorem B253327 : Blo 147793 253327 := bstep (se 1 (by rfl) ⟨189995, by rfl⟩ : syracuseStep 253327 = 379991) B379991
theorem B482849 : Blo 147793 482849 := bstep (se 2 (by rfl) ⟨181068, by rfl⟩ : syracuseStep 482849 = 362137) B362137
theorem B286247 : Blo 147793 286247 := bstep (se 1 (by rfl) ⟨214685, by rfl⟩ : syracuseStep 286247 = 429371) B429371
theorem B188335 : Blo 147793 188335 := bstep (se 1 (by rfl) ⟨141251, by rfl⟩ : syracuseStep 188335 = 282503) B282503
theorem B286651 : Blo 147793 286651 := bstep (se 1 (by rfl) ⟨214988, by rfl⟩ : syracuseStep 286651 = 429977) B429977
theorem B483259 : Blo 147793 483259 := bstep (se 1 (by rfl) ⟨362444, by rfl⟩ : syracuseStep 483259 = 724889) B724889
theorem B254009 : Blo 147793 254009 := bstep (se 2 (by rfl) ⟨95253, by rfl⟩ : syracuseStep 254009 = 190507) B190507
theorem B221705 : Blo 147793 221705 := bstep (se 2 (by rfl) ⟨83139, by rfl⟩ : syracuseStep 221705 = 166279) B166279
theorem B221735 : Blo 147793 221735 := bstep (se 1 (by rfl) ⟨166301, by rfl⟩ : syracuseStep 221735 = 332603) B332603
theorem B221819 : Blo 147793 221819 := bstep (se 1 (by rfl) ⟨166364, by rfl⟩ : syracuseStep 221819 = 332729) B332729
theorem B254711 : Blo 147793 254711 := bstep (se 1 (by rfl) ⟨191033, by rfl⟩ : syracuseStep 254711 = 382067) B382067
theorem B221945 : Blo 147793 221945 := bstep (se 2 (by rfl) ⟨83229, by rfl⟩ : syracuseStep 221945 = 166459) B166459
theorem B222047 : Blo 147793 222047 := bstep (se 1 (by rfl) ⟨166535, by rfl⟩ : syracuseStep 222047 = 333071) B333071
theorem B222059 : Blo 147793 222059 := bstep (se 1 (by rfl) ⟨166544, by rfl⟩ : syracuseStep 222059 = 333089) B333089
theorem B22438853 : Blo 147793 22438853 := bstep (se 4 (by rfl) ⟨2103642, by rfl⟩ : syracuseStep 22438853 = 4207285) B4207285
theorem B189479 : Blo 147793 189479 := bstep (se 1 (by rfl) ⟨142109, by rfl⟩ : syracuseStep 189479 = 284219) B284219
theorem B222287 : Blo 147793 222287 := bstep (se 1 (by rfl) ⟨166715, by rfl⟩ : syracuseStep 222287 = 333431) B333431
theorem B255055 : Blo 147793 255055 := bstep (se 1 (by rfl) ⟨191291, by rfl⟩ : syracuseStep 255055 = 382583) B382583
theorem B222407 : Blo 147793 222407 := bstep (se 1 (by rfl) ⟨166805, by rfl⟩ : syracuseStep 222407 = 333611) B333611
theorem B976151 : Blo 147793 976151 := bstep (se 1 (by rfl) ⟨732113, by rfl⟩ : syracuseStep 976151 = 1464227) B1464227
theorem B255305 : Blo 147793 255305 := bstep (se 2 (by rfl) ⟨95739, by rfl⟩ : syracuseStep 255305 = 191479) B191479
theorem B222569 : Blo 147793 222569 := bstep (se 2 (by rfl) ⟨83463, by rfl⟩ : syracuseStep 222569 = 166927) B166927
theorem B189803 : Blo 147793 189803 := bstep (se 1 (by rfl) ⟨142352, by rfl⟩ : syracuseStep 189803 = 284705) B284705
theorem B288107 : Blo 147793 288107 := bstep (se 1 (by rfl) ⟨216080, by rfl⟩ : syracuseStep 288107 = 432161) B432161
theorem B222647 : Blo 147793 222647 := bstep (se 1 (by rfl) ⟨166985, by rfl⟩ : syracuseStep 222647 = 333971) B333971
theorem B845275 : Blo 147793 845275 := bstep (se 1 (by rfl) ⟨633956, by rfl⟩ : syracuseStep 845275 = 1267913) B1267913
theorem B222683 : Blo 147793 222683 := bstep (se 1 (by rfl) ⟨167012, by rfl⟩ : syracuseStep 222683 = 334025) B334025
theorem B255737 : Blo 147793 255737 := bstep (se 2 (by rfl) ⟨95901, by rfl⟩ : syracuseStep 255737 = 191803) B191803
theorem B1140641 : Blo 147793 1140641 := bstep (se 2 (by rfl) ⟨427740, by rfl⟩ : syracuseStep 1140641 = 855481) B855481
theorem B223151 : Blo 147793 223151 := bstep (se 1 (by rfl) ⟨167363, by rfl⟩ : syracuseStep 223151 = 334727) B334727
theorem B321455 : Blo 147793 321455 := bstep (se 1 (by rfl) ⟨241091, by rfl⟩ : syracuseStep 321455 = 482183) B482183
theorem B255919 : Blo 147793 255919 := bstep (se 1 (by rfl) ⟨191939, by rfl⟩ : syracuseStep 255919 = 383879) B383879
theorem B1632209 : Blo 147793 1632209 := bstep (se 2 (by rfl) ⟨612078, by rfl⟩ : syracuseStep 1632209 = 1224157) B1224157
theorem B256007 : Blo 147793 256007 := bstep (se 1 (by rfl) ⟨192005, by rfl⟩ : syracuseStep 256007 = 384011) B384011
theorem B223241 : Blo 147793 223241 := bstep (se 2 (by rfl) ⟨83715, by rfl⟩ : syracuseStep 223241 = 167431) B167431
theorem B223271 : Blo 147793 223271 := bstep (se 1 (by rfl) ⟨167453, by rfl⟩ : syracuseStep 223271 = 334907) B334907
theorem B1206353 : Blo 147793 1206353 := bstep (se 2 (by rfl) ⟨452382, by rfl⟩ : syracuseStep 1206353 = 904765) B904765
theorem B223355 : Blo 147793 223355 := bstep (se 1 (by rfl) ⟨167516, by rfl⟩ : syracuseStep 223355 = 335033) B335033
theorem B223481 : Blo 147793 223481 := bstep (se 2 (by rfl) ⟨83805, by rfl⟩ : syracuseStep 223481 = 167611) B167611
theorem B1075457 : Blo 147793 1075457 := bstep (se 2 (by rfl) ⟨403296, by rfl⟩ : syracuseStep 1075457 = 806593) B806593
theorem B223583 : Blo 147793 223583 := bstep (se 1 (by rfl) ⟨167687, by rfl⟩ : syracuseStep 223583 = 335375) B335375
theorem B223595 : Blo 147793 223595 := bstep (se 1 (by rfl) ⟨167696, by rfl⟩ : syracuseStep 223595 = 335393) B335393
theorem B223823 : Blo 147793 223823 := bstep (se 1 (by rfl) ⟨167867, by rfl⟩ : syracuseStep 223823 = 335735) B335735
theorem B191099 : Blo 147793 191099 := bstep (se 1 (by rfl) ⟨143324, by rfl⟩ : syracuseStep 191099 = 286649) B286649
theorem B223943 : Blo 147793 223943 := bstep (se 1 (by rfl) ⟨167957, by rfl⟩ : syracuseStep 223943 = 335915) B335915
theorem B224105 : Blo 147793 224105 := bstep (se 2 (by rfl) ⟨84039, by rfl⟩ : syracuseStep 224105 = 168079) B168079
theorem B224183 : Blo 147793 224183 := bstep (se 1 (by rfl) ⟨168137, by rfl⟩ : syracuseStep 224183 = 336275) B336275
theorem B453563 : Blo 147793 453563 := bstep (se 1 (by rfl) ⟨340172, by rfl⟩ : syracuseStep 453563 = 680345) B680345
theorem B224219 : Blo 147793 224219 := bstep (se 1 (by rfl) ⟨168164, by rfl⟩ : syracuseStep 224219 = 336329) B336329
theorem B748925 : Blo 147793 748925 := bstep (se 3 (by rfl) ⟨140423, by rfl⟩ : syracuseStep 748925 = 280847) B280847
theorem B224687 : Blo 147793 224687 := bstep (se 1 (by rfl) ⟨168515, by rfl⟩ : syracuseStep 224687 = 337031) B337031
theorem B1076723 : Blo 147793 1076723 := bstep (se 1 (by rfl) ⟨807542, by rfl⟩ : syracuseStep 1076723 = 1615085) B1615085
theorem B224777 : Blo 147793 224777 := bstep (se 2 (by rfl) ⟨84291, by rfl⟩ : syracuseStep 224777 = 168583) B168583
theorem B224807 : Blo 147793 224807 := bstep (se 1 (by rfl) ⟨168605, by rfl⟩ : syracuseStep 224807 = 337211) B337211
theorem B421499 : Blo 147793 421499 := bstep (se 1 (by rfl) ⟨316124, by rfl⟩ : syracuseStep 421499 = 632249) B632249
theorem B224891 : Blo 147793 224891 := bstep (se 1 (by rfl) ⟨168668, by rfl⟩ : syracuseStep 224891 = 337337) B337337
theorem B421625 : Blo 147793 421625 := bstep (se 2 (by rfl) ⟨158109, by rfl⟩ : syracuseStep 421625 = 316219) B316219
theorem B225017 : Blo 147793 225017 := bstep (se 2 (by rfl) ⟨84381, by rfl⟩ : syracuseStep 225017 = 168763) B168763
theorem B4091681 : Blo 147793 4091681 := bstep (se 2 (by rfl) ⟨1534380, by rfl⟩ : syracuseStep 4091681 = 3068761) B3068761
theorem B225119 : Blo 147793 225119 := bstep (se 1 (by rfl) ⟨168839, by rfl⟩ : syracuseStep 225119 = 337679) B337679
theorem B225131 : Blo 147793 225131 := bstep (se 1 (by rfl) ⟨168848, by rfl⟩ : syracuseStep 225131 = 337697) B337697
theorem B323489 : Blo 147793 323489 := bstep (se 2 (by rfl) ⟨121308, by rfl⟩ : syracuseStep 323489 = 242617) B242617
theorem B421807 : Blo 147793 421807 := bstep (se 1 (by rfl) ⟨316355, by rfl⟩ : syracuseStep 421807 = 632711) B632711
theorem B225359 : Blo 147793 225359 := bstep (se 1 (by rfl) ⟨169019, by rfl⟩ : syracuseStep 225359 = 338039) B338039
theorem B225479 : Blo 147793 225479 := bstep (se 1 (by rfl) ⟨169109, by rfl⟩ : syracuseStep 225479 = 338219) B338219
theorem B323831 : Blo 147793 323831 := bstep (se 1 (by rfl) ⟨242873, by rfl⟩ : syracuseStep 323831 = 485747) B485747
theorem B225641 : Blo 147793 225641 := bstep (se 2 (by rfl) ⟨84615, by rfl⟩ : syracuseStep 225641 = 169231) B169231
theorem B422273 : Blo 147793 422273 := bstep (se 2 (by rfl) ⟨158352, by rfl⟩ : syracuseStep 422273 = 316705) B316705
theorem B225719 : Blo 147793 225719 := bstep (se 1 (by rfl) ⟨169289, by rfl⟩ : syracuseStep 225719 = 338579) B338579
theorem B225755 : Blo 147793 225755 := bstep (se 1 (by rfl) ⟨169316, by rfl⟩ : syracuseStep 225755 = 338633) B338633
theorem B422729 : Blo 147793 422729 := bstep (se 2 (by rfl) ⟨158523, by rfl⟩ : syracuseStep 422729 = 317047) B317047
theorem B226223 : Blo 147793 226223 := bstep (se 1 (by rfl) ⟨169667, by rfl⟩ : syracuseStep 226223 = 339335) B339335
theorem B1635329 : Blo 147793 1635329 := bstep (se 2 (by rfl) ⟨613248, by rfl⟩ : syracuseStep 1635329 = 1226497) B1226497
theorem B226313 : Blo 147793 226313 := bstep (se 2 (by rfl) ⟨84867, by rfl⟩ : syracuseStep 226313 = 169735) B169735
theorem B226343 : Blo 147793 226343 := bstep (se 1 (by rfl) ⟨169757, by rfl⟩ : syracuseStep 226343 = 339515) B339515
theorem B226427 : Blo 147793 226427 := bstep (se 1 (by rfl) ⟨169820, by rfl⟩ : syracuseStep 226427 = 339641) B339641
theorem B1307801 : Blo 147793 1307801 := bstep (se 2 (by rfl) ⟨490425, by rfl⟩ : syracuseStep 1307801 = 980851) B980851
theorem B423083 : Blo 147793 423083 := bstep (se 1 (by rfl) ⟨317312, by rfl⟩ : syracuseStep 423083 = 634625) B634625
theorem B160967 : Blo 147793 160967 := bstep (se 1 (by rfl) ⟨120725, by rfl⟩ : syracuseStep 160967 = 241451) B241451
theorem B226553 : Blo 147793 226553 := bstep (se 2 (by rfl) ⟨84957, by rfl⟩ : syracuseStep 226553 = 169915) B169915
theorem B226655 : Blo 147793 226655 := bstep (se 1 (by rfl) ⟨169991, by rfl⟩ : syracuseStep 226655 = 339983) B339983
theorem B226667 : Blo 147793 226667 := bstep (se 1 (by rfl) ⟨170000, by rfl⟩ : syracuseStep 226667 = 340001) B340001
theorem B325129 : Blo 147793 325129 := bstep (se 2 (by rfl) ⟨121923, by rfl⟩ : syracuseStep 325129 = 243847) B243847
theorem B1308221 : Blo 147793 1308221 := bstep (se 3 (by rfl) ⟨245291, by rfl⟩ : syracuseStep 1308221 = 490583) B490583
theorem B226895 : Blo 147793 226895 := bstep (se 1 (by rfl) ⟨170171, by rfl⟩ : syracuseStep 226895 = 340343) B340343
theorem B227015 : Blo 147793 227015 := bstep (se 1 (by rfl) ⟨170261, by rfl⟩ : syracuseStep 227015 = 340523) B340523
theorem B227177 : Blo 147793 227177 := bstep (se 2 (by rfl) ⟨85191, by rfl⟩ : syracuseStep 227177 = 170383) B170383
theorem B227255 : Blo 147793 227255 := bstep (se 1 (by rfl) ⟨170441, by rfl⟩ : syracuseStep 227255 = 340883) B340883
theorem B227291 : Blo 147793 227291 := bstep (se 1 (by rfl) ⟨170468, by rfl⟩ : syracuseStep 227291 = 340937) B340937
theorem B1275911 : Blo 147793 1275911 := bstep (se 1 (by rfl) ⟨956933, by rfl⟩ : syracuseStep 1275911 = 1913867) B1913867
theorem B6977897 : Blo 147793 6977897 := bstep (se 2 (by rfl) ⟨2616711, by rfl⟩ : syracuseStep 6977897 = 5233423) B5233423
theorem B1833673 : Blo 147793 1833673 := bstep (se 2 (by rfl) ⟨687627, by rfl⟩ : syracuseStep 1833673 = 1375255) B1375255
theorem B1899409 : Blo 147793 1899409 := bstep (se 2 (by rfl) ⟨712278, by rfl⟩ : syracuseStep 1899409 = 1424557) B1424557
theorem B1375427 : Blo 147793 1375427 := bstep (se 1 (by rfl) ⟨1031570, by rfl⟩ : syracuseStep 1375427 = 2063141) B2063141
theorem B753299 : Blo 147793 753299 := bstep (se 1 (by rfl) ⟨564974, by rfl⟩ : syracuseStep 753299 = 1129949) B1129949
theorem B295495 : Blo 147793 295495 := bstep (se 1 (by rfl) ⟨221621, by rfl⟩ : syracuseStep 295495 = 443243) B443243
theorem B721505 : Blo 147793 721505 := bstep (se 2 (by rfl) ⟨270564, by rfl⟩ : syracuseStep 721505 = 541129) B541129
theorem B361235 : Blo 147793 361235 := bstep (se 1 (by rfl) ⟨270926, by rfl⟩ : syracuseStep 361235 = 541853) B541853
theorem B13108877 : Blo 147793 13108877 := bstep (se 3 (by rfl) ⟨2457914, by rfl⟩ : syracuseStep 13108877 = 4915829) B4915829
theorem B853841 : Blo 147793 853841 := bstep (se 2 (by rfl) ⟨320190, by rfl⟩ : syracuseStep 853841 = 640381) B640381
theorem B1705859 : Blo 147793 1705859 := bstep (se 1 (by rfl) ⟨1279394, by rfl⟩ : syracuseStep 1705859 = 2558789) B2558789
theorem B165863 : Blo 147793 165863 := bstep (se 1 (by rfl) ⟨124397, by rfl⟩ : syracuseStep 165863 = 248795) B248795
theorem B1574927 : Blo 147793 1574927 := bstep (se 1 (by rfl) ⟨1181195, by rfl⟩ : syracuseStep 1574927 = 2362391) B2362391
theorem B493697 : Blo 147793 493697 := bstep (se 2 (by rfl) ⟨185136, by rfl⟩ : syracuseStep 493697 = 370273) B370273
theorem B461065 : Blo 147793 461065 := bstep (se 2 (by rfl) ⟨172899, by rfl⟩ : syracuseStep 461065 = 345799) B345799
theorem B624905 : Blo 147793 624905 := bstep (se 2 (by rfl) ⟨234339, by rfl⟩ : syracuseStep 624905 = 468679) B468679
theorem B1280285 : Blo 147793 1280285 := bstep (se 3 (by rfl) ⟨240053, by rfl⟩ : syracuseStep 1280285 = 480107) B480107
theorem B5507531 : Blo 147793 5507531 := bstep (se 1 (by rfl) ⟨4130648, by rfl⟩ : syracuseStep 5507531 = 8261297) B8261297
theorem B166495 : Blo 147793 166495 := bstep (se 1 (by rfl) ⟨124871, by rfl⟩ : syracuseStep 166495 = 249743) B249743
theorem B428971 : Blo 147793 428971 := bstep (se 1 (by rfl) ⟨321728, by rfl⟩ : syracuseStep 428971 = 643457) B643457
theorem B429245 : Blo 147793 429245 := bstep (se 3 (by rfl) ⟨80483, by rfl⟩ : syracuseStep 429245 = 160967) B160967
theorem B4656365 : Blo 147793 4656365 := bstep (se 3 (by rfl) ⟨873068, by rfl⟩ : syracuseStep 4656365 = 1746137) B1746137
theorem B298279 : Blo 147793 298279 := bstep (se 1 (by rfl) ⟨223709, by rfl⟩ : syracuseStep 298279 = 447419) B447419
theorem B265511 : Blo 147793 265511 := bstep (se 1 (by rfl) ⟨199133, by rfl⟩ : syracuseStep 265511 = 398267) B398267
theorem B167647 : Blo 147793 167647 := bstep (se 1 (by rfl) ⟨125735, by rfl⟩ : syracuseStep 167647 = 251471) B251471
theorem B757511 : Blo 147793 757511 := bstep (se 1 (by rfl) ⟨568133, by rfl⟩ : syracuseStep 757511 = 1136267) B1136267
theorem B1085231 : Blo 147793 1085231 := bstep (se 1 (by rfl) ⟨813923, by rfl⟩ : syracuseStep 1085231 = 1627847) B1627847
theorem B168223 : Blo 147793 168223 := bstep (se 1 (by rfl) ⟨126167, by rfl⟩ : syracuseStep 168223 = 252335) B252335
theorem B463195 : Blo 147793 463195 := bstep (se 1 (by rfl) ⟨347396, by rfl⟩ : syracuseStep 463195 = 694793) B694793
theorem B168511 : Blo 147793 168511 := bstep (se 1 (by rfl) ⟨126383, by rfl⟩ : syracuseStep 168511 = 252767) B252767
theorem B857213 : Blo 147793 857213 := bstep (se 3 (by rfl) ⟨160727, by rfl⟩ : syracuseStep 857213 = 321455) B321455
theorem B332999 : Blo 147793 332999 := bstep (se 1 (by rfl) ⟨249749, by rfl⟩ : syracuseStep 332999 = 499499) B499499
theorem B562409 : Blo 147793 562409 := bstep (se 2 (by rfl) ⟨210903, by rfl⟩ : syracuseStep 562409 = 421807) B421807
theorem B595295 : Blo 147793 595295 := bstep (se 1 (by rfl) ⟨446471, by rfl⟩ : syracuseStep 595295 = 892943) B892943
theorem B333179 : Blo 147793 333179 := bstep (se 1 (by rfl) ⟨249884, by rfl⟩ : syracuseStep 333179 = 499769) B499769
theorem B169339 : Blo 147793 169339 := bstep (se 1 (by rfl) ⟨127004, by rfl⟩ : syracuseStep 169339 = 254009) B254009
theorem B333305 : Blo 147793 333305 := bstep (se 2 (by rfl) ⟨124989, by rfl⟩ : syracuseStep 333305 = 249979) B249979
theorem B3216941 : Blo 147793 3216941 := bstep (se 3 (by rfl) ⟨603176, by rfl⟩ : syracuseStep 3216941 = 1206353) B1206353
theorem B333395 : Blo 147793 333395 := bstep (se 1 (by rfl) ⟨250046, by rfl⟩ : syracuseStep 333395 = 500093) B500093
theorem B1545965 : Blo 147793 1545965 := bstep (se 3 (by rfl) ⟨289868, by rfl⟩ : syracuseStep 1545965 = 579737) B579737
theorem B333575 : Blo 147793 333575 := bstep (se 1 (by rfl) ⟨250181, by rfl⟩ : syracuseStep 333575 = 500363) B500363
theorem B169807 : Blo 147793 169807 := bstep (se 1 (by rfl) ⟨127355, by rfl⟩ : syracuseStep 169807 = 254711) B254711
theorem B170203 : Blo 147793 170203 := bstep (se 1 (by rfl) ⟨127652, by rfl⟩ : syracuseStep 170203 = 255305) B255305
theorem B399707 : Blo 147793 399707 := bstep (se 1 (by rfl) ⟨299780, by rfl⟩ : syracuseStep 399707 = 599561) B599561
theorem B334187 : Blo 147793 334187 := bstep (se 1 (by rfl) ⟨250640, by rfl⟩ : syracuseStep 334187 = 501281) B501281
theorem B1841591 : Blo 147793 1841591 := bstep (se 1 (by rfl) ⟨1381193, by rfl⟩ : syracuseStep 1841591 = 2762387) B2762387
theorem B334331 : Blo 147793 334331 := bstep (se 1 (by rfl) ⟨250748, by rfl⟩ : syracuseStep 334331 = 501497) B501497
theorem B170491 : Blo 147793 170491 := bstep (se 1 (by rfl) ⟨127868, by rfl⟩ : syracuseStep 170491 = 255737) B255737
theorem B760427 : Blo 147793 760427 := bstep (se 1 (by rfl) ⟨570320, by rfl⟩ : syracuseStep 760427 = 1140641) B1140641
theorem B334457 : Blo 147793 334457 := bstep (se 2 (by rfl) ⟨125421, by rfl⟩ : syracuseStep 334457 = 250843) B250843
theorem B334511 : Blo 147793 334511 := bstep (se 1 (by rfl) ⟨250883, by rfl⟩ : syracuseStep 334511 = 501767) B501767
theorem B170671 : Blo 147793 170671 := bstep (se 1 (by rfl) ⟨128003, by rfl⟩ : syracuseStep 170671 = 256007) B256007
theorem B334583 : Blo 147793 334583 := bstep (se 1 (by rfl) ⟨250937, by rfl⟩ : syracuseStep 334583 = 501875) B501875
theorem B334763 : Blo 147793 334763 := bstep (se 1 (by rfl) ⟨251072, by rfl⟩ : syracuseStep 334763 = 502145) B502145
theorem B760913 : Blo 147793 760913 := bstep (se 2 (by rfl) ⟨285342, by rfl⟩ : syracuseStep 760913 = 570685) B570685
theorem B302375 : Blo 147793 302375 := bstep (se 1 (by rfl) ⟨226781, by rfl⟩ : syracuseStep 302375 = 453563) B453563
theorem B433505 : Blo 147793 433505 := bstep (se 2 (by rfl) ⟨162564, by rfl⟩ : syracuseStep 433505 = 325129) B325129
theorem B335303 : Blo 147793 335303 := bstep (se 1 (by rfl) ⟨251477, by rfl⟩ : syracuseStep 335303 = 502955) B502955
theorem B859673 : Blo 147793 859673 := bstep (se 2 (by rfl) ⟨322377, by rfl⟩ : syracuseStep 859673 = 644755) B644755
theorem B499283 : Blo 147793 499283 := bstep (se 1 (by rfl) ⟨374462, by rfl⟩ : syracuseStep 499283 = 748925) B748925
theorem B335663 : Blo 147793 335663 := bstep (se 1 (by rfl) ⟨251747, by rfl⟩ : syracuseStep 335663 = 503495) B503495
theorem B205087 : Blo 147793 205087 := bstep (se 1 (by rfl) ⟨153815, by rfl⟩ : syracuseStep 205087 = 307631) B307631
theorem B336239 : Blo 147793 336239 := bstep (se 1 (by rfl) ⟨252179, by rfl⟩ : syracuseStep 336239 = 504359) B504359
theorem B336311 : Blo 147793 336311 := bstep (se 1 (by rfl) ⟨252233, by rfl⟩ : syracuseStep 336311 = 504467) B504467
theorem B270803 : Blo 147793 270803 := bstep (se 1 (by rfl) ⟨203102, by rfl⟩ : syracuseStep 270803 = 406205) B406205
theorem B270911 : Blo 147793 270911 := bstep (se 1 (by rfl) ⟨203183, by rfl⟩ : syracuseStep 270911 = 406367) B406367
theorem B336455 : Blo 147793 336455 := bstep (se 1 (by rfl) ⟨252341, by rfl⟩ : syracuseStep 336455 = 504683) B504683
theorem B336491 : Blo 147793 336491 := bstep (se 1 (by rfl) ⟨252368, by rfl⟩ : syracuseStep 336491 = 504737) B504737
theorem B402041 : Blo 147793 402041 := bstep (se 2 (by rfl) ⟨150765, by rfl⟩ : syracuseStep 402041 = 301531) B301531
theorem B1090219 : Blo 147793 1090219 := bstep (se 1 (by rfl) ⟨817664, by rfl⟩ : syracuseStep 1090219 = 1635329) B1635329
theorem B3089335 : Blo 147793 3089335 := bstep (se 1 (by rfl) ⟨2317001, by rfl⟩ : syracuseStep 3089335 = 4634003) B4634003
theorem B336887 : Blo 147793 336887 := bstep (se 1 (by rfl) ⟨252665, by rfl⟩ : syracuseStep 336887 = 505331) B505331
theorem B959525 : Blo 147793 959525 := bstep (se 4 (by rfl) ⟨89955, by rfl⟩ : syracuseStep 959525 = 179911) B179911
theorem B2532545 : Blo 147793 2532545 := bstep (se 2 (by rfl) ⟨949704, by rfl⟩ : syracuseStep 2532545 = 1899409) B1899409
theorem B337247 : Blo 147793 337247 := bstep (se 1 (by rfl) ⟨252935, by rfl⟩ : syracuseStep 337247 = 505871) B505871
theorem B337643 : Blo 147793 337643 := bstep (se 1 (by rfl) ⟨253232, by rfl⟩ : syracuseStep 337643 = 506465) B506465
theorem B337769 : Blo 147793 337769 := bstep (se 2 (by rfl) ⟨126663, by rfl⟩ : syracuseStep 337769 = 253327) B253327
theorem B534509 : Blo 147793 534509 := bstep (se 3 (by rfl) ⟨100220, by rfl⟩ : syracuseStep 534509 = 200441) B200441
theorem B17410229 : Blo 147793 17410229 := bstep (se 5 (by rfl) ⟨816104, by rfl⟩ : syracuseStep 17410229 = 1632209) B1632209
theorem B1288385 : Blo 147793 1288385 := bstep (se 2 (by rfl) ⟨483144, by rfl⟩ : syracuseStep 1288385 = 966289) B966289
theorem B502199 : Blo 147793 502199 := bstep (se 1 (by rfl) ⟨376649, by rfl⟩ : syracuseStep 502199 = 753299) B753299
theorem B338615 : Blo 147793 338615 := bstep (se 1 (by rfl) ⟨253961, by rfl⟩ : syracuseStep 338615 = 507923) B507923
theorem B338831 : Blo 147793 338831 := bstep (se 1 (by rfl) ⟨254123, by rfl⟩ : syracuseStep 338831 = 508247) B508247
theorem B765449 : Blo 147793 765449 := bstep (se 2 (by rfl) ⟨287043, by rfl⟩ : syracuseStep 765449 = 574087) B574087
theorem B339551 : Blo 147793 339551 := bstep (se 1 (by rfl) ⟨254663, by rfl⟩ : syracuseStep 339551 = 509327) B509327
theorem B1126061 : Blo 147793 1126061 := bstep (se 3 (by rfl) ⟨211136, by rfl⟩ : syracuseStep 1126061 = 422273) B422273
theorem B864047 : Blo 147793 864047 := bstep (se 1 (by rfl) ⟨648035, by rfl⟩ : syracuseStep 864047 = 1296071) B1296071
theorem B339767 : Blo 147793 339767 := bstep (se 1 (by rfl) ⟨254825, by rfl⟩ : syracuseStep 339767 = 509651) B509651
theorem B3092411 : Blo 147793 3092411 := bstep (se 1 (by rfl) ⟨2319308, by rfl⟩ : syracuseStep 3092411 = 4638617) B4638617
theorem B340073 : Blo 147793 340073 := bstep (se 2 (by rfl) ⟨127527, by rfl⟩ : syracuseStep 340073 = 255055) B255055
theorem B405935 : Blo 147793 405935 := bstep (se 1 (by rfl) ⟨304451, by rfl⟩ : syracuseStep 405935 = 608903) B608903
theorem B340559 : Blo 147793 340559 := bstep (se 1 (by rfl) ⟨255419, by rfl⟩ : syracuseStep 340559 = 510839) B510839
theorem B1421945 : Blo 147793 1421945 := bstep (se 2 (by rfl) ⟨533229, by rfl⟩ : syracuseStep 1421945 = 1066459) B1066459
theorem B1127033 : Blo 147793 1127033 := bstep (se 2 (by rfl) ⟨422637, by rfl⟩ : syracuseStep 1127033 = 845275) B845275
theorem B242399 : Blo 147793 242399 := bstep (se 1 (by rfl) ⟨181799, by rfl⟩ : syracuseStep 242399 = 363599) B363599
theorem B340703 : Blo 147793 340703 := bstep (se 1 (by rfl) ⟨255527, by rfl⟩ : syracuseStep 340703 = 511055) B511055
theorem B340955 : Blo 147793 340955 := bstep (se 1 (by rfl) ⟨255716, by rfl⟩ : syracuseStep 340955 = 511433) B511433
theorem B340967 : Blo 147793 340967 := bstep (se 1 (by rfl) ⟨255725, by rfl⟩ : syracuseStep 340967 = 511451) B511451
theorem B341135 : Blo 147793 341135 := bstep (se 1 (by rfl) ⟨255851, by rfl⟩ : syracuseStep 341135 = 511703) B511703
theorem B537815 : Blo 147793 537815 := bstep (se 1 (by rfl) ⟨403361, by rfl⟩ : syracuseStep 537815 = 806723) B806723
theorem B341225 : Blo 147793 341225 := bstep (se 2 (by rfl) ⟨127959, by rfl⟩ : syracuseStep 341225 = 255919) B255919
theorem B341279 : Blo 147793 341279 := bstep (se 1 (by rfl) ⟨255959, by rfl⟩ : syracuseStep 341279 = 511919) B511919
theorem B767393 : Blo 147793 767393 := bstep (se 2 (by rfl) ⟨287772, by rfl⟩ : syracuseStep 767393 = 575545) B575545
theorem B636349 : Blo 147793 636349 := bstep (se 3 (by rfl) ⟨119315, by rfl⟩ : syracuseStep 636349 = 238631) B238631
theorem B505277 : Blo 147793 505277 := bstep (se 3 (by rfl) ⟨94739, by rfl⟩ : syracuseStep 505277 = 189479) B189479
theorem B1226177 : Blo 147793 1226177 := bstep (se 2 (by rfl) ⟨459816, by rfl⟩ : syracuseStep 1226177 = 919633) B919633
theorem B505655 : Blo 147793 505655 := bstep (se 1 (by rfl) ⟨379241, by rfl⟩ : syracuseStep 505655 = 758483) B758483
theorem B1128491 : Blo 147793 1128491 := bstep (se 1 (by rfl) ⟨846368, by rfl⟩ : syracuseStep 1128491 = 1692737) B1692737
theorem B571657 : Blo 147793 571657 := bstep (se 2 (by rfl) ⟨214371, by rfl⟩ : syracuseStep 571657 = 428743) B428743
theorem B506141 : Blo 147793 506141 := bstep (se 3 (by rfl) ⟨94901, by rfl⟩ : syracuseStep 506141 = 189803) B189803
theorem B5880113 : Blo 147793 5880113 := bstep (se 2 (by rfl) ⟨2205042, by rfl⟩ : syracuseStep 5880113 = 4410085) B4410085
theorem B375131 : Blo 147793 375131 := bstep (se 1 (by rfl) ⟨281348, by rfl⟩ : syracuseStep 375131 = 562697) B562697
theorem B375151 : Blo 147793 375151 := bstep (se 1 (by rfl) ⟨281363, by rfl⟩ : syracuseStep 375151 = 562727) B562727
theorem B2702099 : Blo 147793 2702099 := bstep (se 1 (by rfl) ⟨2026574, by rfl⟩ : syracuseStep 2702099 = 4053149) B4053149
theorem B375799 : Blo 147793 375799 := bstep (se 1 (by rfl) ⟨281849, by rfl⟩ : syracuseStep 375799 = 563699) B563699
theorem B5160023 : Blo 147793 5160023 := bstep (se 1 (by rfl) ⟨3870017, by rfl⟩ : syracuseStep 5160023 = 7740035) B7740035
theorem B507167 : Blo 147793 507167 := bstep (se 1 (by rfl) ⟨380375, by rfl⟩ : syracuseStep 507167 = 760751) B760751
theorem B376103 : Blo 147793 376103 := bstep (se 1 (by rfl) ⟨282077, by rfl⟩ : syracuseStep 376103 = 564155) B564155
theorem B179887 : Blo 147793 179887 := bstep (se 1 (by rfl) ⟨134915, by rfl⟩ : syracuseStep 179887 = 269831) B269831
theorem B966775 : Blo 147793 966775 := bstep (se 1 (by rfl) ⟨725081, by rfl⟩ : syracuseStep 966775 = 1450163) B1450163
theorem B180511 : Blo 147793 180511 := bstep (se 1 (by rfl) ⟨135383, by rfl⟩ : syracuseStep 180511 = 270767) B270767
theorem B147803 : Blo 147793 147803 := bstep (se 1 (by rfl) ⟨110852, by rfl⟩ : syracuseStep 147803 = 221705) B221705
theorem B639323 : Blo 147793 639323 := bstep (se 1 (by rfl) ⟨479492, by rfl⟩ : syracuseStep 639323 = 958985) B958985
theorem B147823 : Blo 147793 147823 := bstep (se 1 (by rfl) ⟨110867, by rfl⟩ : syracuseStep 147823 = 221735) B221735
theorem B147879 : Blo 147793 147879 := bstep (se 1 (by rfl) ⟨110909, by rfl⟩ : syracuseStep 147879 = 221819) B221819
theorem B147963 : Blo 147793 147963 := bstep (se 1 (by rfl) ⟨110972, by rfl⟩ : syracuseStep 147963 = 221945) B221945
theorem B148031 : Blo 147793 148031 := bstep (se 1 (by rfl) ⟨111023, by rfl⟩ : syracuseStep 148031 = 222047) B222047
theorem B148039 : Blo 147793 148039 := bstep (se 1 (by rfl) ⟨111029, by rfl⟩ : syracuseStep 148039 = 222059) B222059
theorem B574073 : Blo 147793 574073 := bstep (se 2 (by rfl) ⟨215277, by rfl⟩ : syracuseStep 574073 = 430555) B430555
theorem B14959235 : Blo 147793 14959235 := bstep (se 1 (by rfl) ⟨11219426, by rfl⟩ : syracuseStep 14959235 = 22438853) B22438853
theorem B148191 : Blo 147793 148191 := bstep (se 1 (by rfl) ⟨111143, by rfl⟩ : syracuseStep 148191 = 222287) B222287
theorem B148271 : Blo 147793 148271 := bstep (se 1 (by rfl) ⟨111203, by rfl⟩ : syracuseStep 148271 = 222407) B222407
theorem B377743 : Blo 147793 377743 := bstep (se 1 (by rfl) ⟨283307, by rfl⟩ : syracuseStep 377743 = 566615) B566615
theorem B148379 : Blo 147793 148379 := bstep (se 1 (by rfl) ⟨111284, by rfl⟩ : syracuseStep 148379 = 222569) B222569
theorem B148431 : Blo 147793 148431 := bstep (se 1 (by rfl) ⟨111323, by rfl⟩ : syracuseStep 148431 = 222647) B222647
theorem B148455 : Blo 147793 148455 := bstep (se 1 (by rfl) ⟨111341, by rfl⟩ : syracuseStep 148455 = 222683) B222683
theorem B640007 : Blo 147793 640007 := bstep (se 1 (by rfl) ⟨480005, by rfl⟩ : syracuseStep 640007 = 960011) B960011
theorem B9684035 : Blo 147793 9684035 := bstep (se 1 (by rfl) ⟨7263026, by rfl⟩ : syracuseStep 9684035 = 14526053) B14526053
theorem B148767 : Blo 147793 148767 := bstep (se 1 (by rfl) ⟨111575, by rfl⟩ : syracuseStep 148767 = 223151) B223151
theorem B148827 : Blo 147793 148827 := bstep (se 1 (by rfl) ⟨111620, by rfl⟩ : syracuseStep 148827 = 223241) B223241
theorem B378209 : Blo 147793 378209 := bstep (se 2 (by rfl) ⟨141828, by rfl⟩ : syracuseStep 378209 = 283657) B283657
theorem B148847 : Blo 147793 148847 := bstep (se 1 (by rfl) ⟨111635, by rfl⟩ : syracuseStep 148847 = 223271) B223271
theorem B148903 : Blo 147793 148903 := bstep (se 1 (by rfl) ⟨111677, by rfl⟩ : syracuseStep 148903 = 223355) B223355
theorem B148987 : Blo 147793 148987 := bstep (se 1 (by rfl) ⟨111740, by rfl⟩ : syracuseStep 148987 = 223481) B223481
theorem B149055 : Blo 147793 149055 := bstep (se 1 (by rfl) ⟨111791, by rfl⟩ : syracuseStep 149055 = 223583) B223583
theorem B149063 : Blo 147793 149063 := bstep (se 1 (by rfl) ⟨111797, by rfl⟩ : syracuseStep 149063 = 223595) B223595
theorem B640669 : Blo 147793 640669 := bstep (se 3 (by rfl) ⟨120125, by rfl⟩ : syracuseStep 640669 = 240251) B240251
theorem B509597 : Blo 147793 509597 := bstep (se 3 (by rfl) ⟨95549, by rfl⟩ : syracuseStep 509597 = 191099) B191099
theorem B149215 : Blo 147793 149215 := bstep (se 1 (by rfl) ⟨111911, by rfl⟩ : syracuseStep 149215 = 223823) B223823
theorem B378665 : Blo 147793 378665 := bstep (se 2 (by rfl) ⟨141999, by rfl⟩ : syracuseStep 378665 = 283999) B283999
theorem B149295 : Blo 147793 149295 := bstep (se 1 (by rfl) ⟨111971, by rfl⟩ : syracuseStep 149295 = 223943) B223943
theorem B149403 : Blo 147793 149403 := bstep (se 1 (by rfl) ⟨112052, by rfl⟩ : syracuseStep 149403 = 224105) B224105
theorem B149455 : Blo 147793 149455 := bstep (se 1 (by rfl) ⟨112091, by rfl⟩ : syracuseStep 149455 = 224183) B224183
theorem B149479 : Blo 147793 149479 := bstep (se 1 (by rfl) ⟨112109, by rfl⟩ : syracuseStep 149479 = 224219) B224219
theorem B510137 : Blo 147793 510137 := bstep (se 2 (by rfl) ⟨191301, by rfl⟩ : syracuseStep 510137 = 382603) B382603
theorem B149791 : Blo 147793 149791 := bstep (se 1 (by rfl) ⟨112343, by rfl⟩ : syracuseStep 149791 = 224687) B224687
theorem B149851 : Blo 147793 149851 := bstep (se 1 (by rfl) ⟨112388, by rfl⟩ : syracuseStep 149851 = 224777) B224777
theorem B149871 : Blo 147793 149871 := bstep (se 1 (by rfl) ⟨112403, by rfl⟩ : syracuseStep 149871 = 224807) B224807
theorem B280999 : Blo 147793 280999 := bstep (se 1 (by rfl) ⟨210749, by rfl⟩ : syracuseStep 280999 = 421499) B421499
theorem B149927 : Blo 147793 149927 := bstep (se 1 (by rfl) ⟨112445, by rfl⟩ : syracuseStep 149927 = 224891) B224891
theorem B281083 : Blo 147793 281083 := bstep (se 1 (by rfl) ⟨210812, by rfl⟩ : syracuseStep 281083 = 421625) B421625
theorem B150011 : Blo 147793 150011 := bstep (se 1 (by rfl) ⟨112508, by rfl⟩ : syracuseStep 150011 = 225017) B225017
theorem B150079 : Blo 147793 150079 := bstep (se 1 (by rfl) ⟨112559, by rfl⟩ : syracuseStep 150079 = 225119) B225119
theorem B150087 : Blo 147793 150087 := bstep (se 1 (by rfl) ⟨112565, by rfl⟩ : syracuseStep 150087 = 225131) B225131
theorem B215659 : Blo 147793 215659 := bstep (se 1 (by rfl) ⟨161744, by rfl⟩ : syracuseStep 215659 = 323489) B323489
theorem B150239 : Blo 147793 150239 := bstep (se 1 (by rfl) ⟨112679, by rfl⟩ : syracuseStep 150239 = 225359) B225359
theorem B641783 : Blo 147793 641783 := bstep (se 1 (by rfl) ⟨481337, by rfl⟩ : syracuseStep 641783 = 962675) B962675
theorem B379667 : Blo 147793 379667 := bstep (se 1 (by rfl) ⟨284750, by rfl⟩ : syracuseStep 379667 = 569501) B569501
theorem B150319 : Blo 147793 150319 := bstep (se 1 (by rfl) ⟨112739, by rfl⟩ : syracuseStep 150319 = 225479) B225479
theorem B215887 : Blo 147793 215887 := bstep (se 1 (by rfl) ⟨161915, by rfl⟩ : syracuseStep 215887 = 323831) B323831
theorem B150427 : Blo 147793 150427 := bstep (se 1 (by rfl) ⟨112820, by rfl⟩ : syracuseStep 150427 = 225641) B225641
theorem B150479 : Blo 147793 150479 := bstep (se 1 (by rfl) ⟨112859, by rfl⟩ : syracuseStep 150479 = 225719) B225719
theorem B150503 : Blo 147793 150503 := bstep (se 1 (by rfl) ⟨112877, by rfl⟩ : syracuseStep 150503 = 225755) B225755
theorem B5786801 : Blo 147793 5786801 := bstep (se 2 (by rfl) ⟨2170050, by rfl⟩ : syracuseStep 5786801 = 4340101) B4340101
theorem B281819 : Blo 147793 281819 := bstep (se 1 (by rfl) ⟨211364, by rfl⟩ : syracuseStep 281819 = 422729) B422729
theorem B380123 : Blo 147793 380123 := bstep (se 1 (by rfl) ⟨285092, by rfl⟩ : syracuseStep 380123 = 570185) B570185
theorem B380153 : Blo 147793 380153 := bstep (se 2 (by rfl) ⟨142557, by rfl⟩ : syracuseStep 380153 = 285115) B285115
theorem B150815 : Blo 147793 150815 := bstep (se 1 (by rfl) ⟨113111, by rfl⟩ : syracuseStep 150815 = 226223) B226223
theorem B150875 : Blo 147793 150875 := bstep (se 1 (by rfl) ⟨113156, by rfl⟩ : syracuseStep 150875 = 226313) B226313
theorem B150895 : Blo 147793 150895 := bstep (se 1 (by rfl) ⟨113171, by rfl⟩ : syracuseStep 150895 = 226343) B226343
theorem B150951 : Blo 147793 150951 := bstep (se 1 (by rfl) ⟨113213, by rfl⟩ : syracuseStep 150951 = 226427) B226427
theorem B5787065 : Blo 147793 5787065 := bstep (se 2 (by rfl) ⟨2170149, by rfl⟩ : syracuseStep 5787065 = 4340299) B4340299
theorem B871867 : Blo 147793 871867 := bstep (se 1 (by rfl) ⟨653900, by rfl⟩ : syracuseStep 871867 = 1307801) B1307801
theorem B282055 : Blo 147793 282055 := bstep (se 1 (by rfl) ⟨211541, by rfl⟩ : syracuseStep 282055 = 423083) B423083
theorem B151035 : Blo 147793 151035 := bstep (se 1 (by rfl) ⟨113276, by rfl⟩ : syracuseStep 151035 = 226553) B226553
theorem B151103 : Blo 147793 151103 := bstep (se 1 (by rfl) ⟨113327, by rfl⟩ : syracuseStep 151103 = 226655) B226655
theorem B151111 : Blo 147793 151111 := bstep (se 1 (by rfl) ⟨113333, by rfl⟩ : syracuseStep 151111 = 226667) B226667
theorem B249439 : Blo 147793 249439 := bstep (se 1 (by rfl) ⟨187079, by rfl⟩ : syracuseStep 249439 = 374159) B374159
theorem B2444897 : Blo 147793 2444897 := bstep (se 2 (by rfl) ⟨916836, by rfl⟩ : syracuseStep 2444897 = 1833673) B1833673
theorem B511649 : Blo 147793 511649 := bstep (se 2 (by rfl) ⟨191868, by rfl⟩ : syracuseStep 511649 = 383737) B383737
theorem B872147 : Blo 147793 872147 := bstep (se 1 (by rfl) ⟨654110, by rfl⟩ : syracuseStep 872147 = 1308221) B1308221
theorem B151263 : Blo 147793 151263 := bstep (se 1 (by rfl) ⟨113447, by rfl⟩ : syracuseStep 151263 = 226895) B226895
theorem B151343 : Blo 147793 151343 := bstep (se 1 (by rfl) ⟨113507, by rfl⟩ : syracuseStep 151343 = 227015) B227015
theorem B249655 : Blo 147793 249655 := bstep (se 1 (by rfl) ⟨187241, by rfl⟩ : syracuseStep 249655 = 374483) B374483
theorem B380801 : Blo 147793 380801 := bstep (se 2 (by rfl) ⟨142800, by rfl⟩ : syracuseStep 380801 = 285601) B285601
theorem B151451 : Blo 147793 151451 := bstep (se 1 (by rfl) ⟨113588, by rfl⟩ : syracuseStep 151451 = 227177) B227177
theorem B2576285 : Blo 147793 2576285 := bstep (se 3 (by rfl) ⟨483053, by rfl⟩ : syracuseStep 2576285 = 966107) B966107
theorem B151503 : Blo 147793 151503 := bstep (se 1 (by rfl) ⟨113627, by rfl⟩ : syracuseStep 151503 = 227255) B227255
theorem B151527 : Blo 147793 151527 := bstep (se 1 (by rfl) ⟨113645, by rfl⟩ : syracuseStep 151527 = 227291) B227291
theorem B250121 : Blo 147793 250121 := bstep (se 2 (by rfl) ⟨93795, by rfl⟩ : syracuseStep 250121 = 187591) B187591
theorem B381257 : Blo 147793 381257 := bstep (se 2 (by rfl) ⟨142971, by rfl⟩ : syracuseStep 381257 = 285943) B285943
theorem B381611 : Blo 147793 381611 := bstep (se 1 (by rfl) ⟨286208, by rfl⟩ : syracuseStep 381611 = 572417) B572417
theorem B251113 : Blo 147793 251113 := bstep (se 2 (by rfl) ⟨94167, by rfl⟩ : syracuseStep 251113 = 188335) B188335
theorem B382201 : Blo 147793 382201 := bstep (se 2 (by rfl) ⟨143325, by rfl⟩ : syracuseStep 382201 = 286651) B286651
theorem B644345 : Blo 147793 644345 := bstep (se 2 (by rfl) ⟨241629, by rfl⟩ : syracuseStep 644345 = 483259) B483259
theorem B251167 : Blo 147793 251167 := bstep (se 1 (by rfl) ⟨188375, by rfl⟩ : syracuseStep 251167 = 376751) B376751
theorem B251579 : Blo 147793 251579 := bstep (se 1 (by rfl) ⟨188684, by rfl⟩ : syracuseStep 251579 = 377369) B377369
theorem B382927 : Blo 147793 382927 := bstep (se 1 (by rfl) ⟨287195, by rfl⟩ : syracuseStep 382927 = 574391) B574391
theorem B2545667 : Blo 147793 2545667 := bstep (se 1 (by rfl) ⟨1909250, by rfl⟩ : syracuseStep 2545667 = 3818501) B3818501
theorem B317449 : Blo 147793 317449 := bstep (se 2 (by rfl) ⟨119043, by rfl⟩ : syracuseStep 317449 = 238087) B238087
theorem B2218063 : Blo 147793 2218063 := bstep (se 1 (by rfl) ⟨1663547, by rfl⟩ : syracuseStep 2218063 = 3327095) B3327095
theorem B547069 : Blo 147793 547069 := bstep (se 3 (by rfl) ⟨102575, by rfl⟩ : syracuseStep 547069 = 205151) B205151
theorem B383899 : Blo 147793 383899 := bstep (se 1 (by rfl) ⟨287924, by rfl⟩ : syracuseStep 383899 = 575849) B575849
theorem B1629233 : Blo 147793 1629233 := bstep (se 2 (by rfl) ⟨610962, by rfl⟩ : syracuseStep 1629233 = 1221925) B1221925
theorem B187687 : Blo 147793 187687 := bstep (se 1 (by rfl) ⟨140765, by rfl⟩ : syracuseStep 187687 = 281531) B281531
theorem B253307 : Blo 147793 253307 := bstep (se 1 (by rfl) ⟨189980, by rfl⟩ : syracuseStep 253307 = 379961) B379961
theorem B188011 : Blo 147793 188011 := bstep (se 1 (by rfl) ⟨141008, by rfl⟩ : syracuseStep 188011 = 282017) B282017
theorem B188239 : Blo 147793 188239 := bstep (se 1 (by rfl) ⟨141179, by rfl⟩ : syracuseStep 188239 = 282359) B282359
theorem B319439 : Blo 147793 319439 := bstep (se 1 (by rfl) ⟨239579, by rfl⟩ : syracuseStep 319439 = 479159) B479159
theorem B2908163 : Blo 147793 2908163 := bstep (se 1 (by rfl) ⟨2181122, by rfl⟩ : syracuseStep 2908163 = 4362245) B4362245
theorem B1138697 : Blo 147793 1138697 := bstep (se 2 (by rfl) ⟨427011, by rfl⟩ : syracuseStep 1138697 = 854023) B854023
theorem B680089 : Blo 147793 680089 := bstep (se 2 (by rfl) ⟨255033, by rfl⟩ : syracuseStep 680089 = 510067) B510067
theorem B2580659 : Blo 147793 2580659 := bstep (se 1 (by rfl) ⟨1935494, by rfl⟩ : syracuseStep 2580659 = 3870989) B3870989
theorem B254299 : Blo 147793 254299 := bstep (se 1 (by rfl) ⟨190724, by rfl⟩ : syracuseStep 254299 = 381449) B381449
theorem B221759 : Blo 147793 221759 := bstep (se 1 (by rfl) ⟨166319, by rfl⟩ : syracuseStep 221759 = 332639) B332639
theorem B221879 : Blo 147793 221879 := bstep (se 1 (by rfl) ⟨166409, by rfl⟩ : syracuseStep 221879 = 332819) B332819
theorem B320183 : Blo 147793 320183 := bstep (se 1 (by rfl) ⟨240137, by rfl⟩ : syracuseStep 320183 = 480275) B480275
theorem B222107 : Blo 147793 222107 := bstep (se 1 (by rfl) ⟨166580, by rfl⟩ : syracuseStep 222107 = 333161) B333161
theorem B844775 : Blo 147793 844775 := bstep (se 1 (by rfl) ⟨633581, by rfl⟩ : syracuseStep 844775 = 1267163) B1267163
theorem B320635 : Blo 147793 320635 := bstep (se 1 (by rfl) ⟨240476, by rfl⟩ : syracuseStep 320635 = 480953) B480953
theorem B287887 : Blo 147793 287887 := bstep (se 1 (by rfl) ⟨215915, by rfl⟩ : syracuseStep 287887 = 431831) B431831
theorem B288031 : Blo 147793 288031 := bstep (se 1 (by rfl) ⟨216023, by rfl⟩ : syracuseStep 288031 = 432047) B432047
theorem B222503 : Blo 147793 222503 := bstep (se 1 (by rfl) ⟨166877, by rfl⟩ : syracuseStep 222503 = 333755) B333755
theorem B255271 : Blo 147793 255271 := bstep (se 1 (by rfl) ⟨191453, by rfl⟩ : syracuseStep 255271 = 382907) B382907
theorem B222587 : Blo 147793 222587 := bstep (se 1 (by rfl) ⟨166940, by rfl⟩ : syracuseStep 222587 = 333881) B333881
theorem B2876795 : Blo 147793 2876795 := bstep (se 1 (by rfl) ⟨2157596, by rfl⟩ : syracuseStep 2876795 = 4315193) B4315193
theorem B288137 : Blo 147793 288137 := bstep (se 2 (by rfl) ⟨108051, by rfl⟩ : syracuseStep 288137 = 216103) B216103
theorem B222713 : Blo 147793 222713 := bstep (se 2 (by rfl) ⟨83517, by rfl⟩ : syracuseStep 222713 = 167035) B167035
theorem B222815 : Blo 147793 222815 := bstep (se 1 (by rfl) ⟨167111, by rfl⟩ : syracuseStep 222815 = 334223) B334223
theorem B190127 : Blo 147793 190127 := bstep (se 1 (by rfl) ⟨142595, by rfl⟩ : syracuseStep 190127 = 285191) B285191
theorem B255791 : Blo 147793 255791 := bstep (se 1 (by rfl) ⟨191843, by rfl⟩ : syracuseStep 255791 = 383687) B383687
theorem B223031 : Blo 147793 223031 := bstep (se 1 (by rfl) ⟨167273, by rfl⟩ : syracuseStep 223031 = 334547) B334547
theorem B1926989 : Blo 147793 1926989 := bstep (se 3 (by rfl) ⟨361310, by rfl⟩ : syracuseStep 1926989 = 722621) B722621
theorem B485207 : Blo 147793 485207 := bstep (se 1 (by rfl) ⟨363905, by rfl⟩ : syracuseStep 485207 = 727811) B727811
theorem B223337 : Blo 147793 223337 := bstep (se 2 (by rfl) ⟨83751, by rfl⟩ : syracuseStep 223337 = 167503) B167503
theorem B6121763 : Blo 147793 6121763 := bstep (se 1 (by rfl) ⟨4591322, by rfl⟩ : syracuseStep 6121763 = 9182645) B9182645
theorem B321899 : Blo 147793 321899 := bstep (se 1 (by rfl) ⟨241424, by rfl⟩ : syracuseStep 321899 = 482849) B482849
theorem B190831 : Blo 147793 190831 := bstep (se 1 (by rfl) ⟨143123, by rfl⟩ : syracuseStep 190831 = 286247) B286247
theorem B223655 : Blo 147793 223655 := bstep (se 1 (by rfl) ⟨167741, by rfl⟩ : syracuseStep 223655 = 335483) B335483
theorem B223739 : Blo 147793 223739 := bstep (se 1 (by rfl) ⟨167804, by rfl⟩ : syracuseStep 223739 = 335609) B335609
theorem B1075799 : Blo 147793 1075799 := bstep (se 1 (by rfl) ⟨806849, by rfl⟩ : syracuseStep 1075799 = 1613699) B1613699
theorem B223865 : Blo 147793 223865 := bstep (se 2 (by rfl) ⟨83949, by rfl⟩ : syracuseStep 223865 = 167899) B167899
theorem B158383 : Blo 147793 158383 := bstep (se 1 (by rfl) ⟨118787, by rfl⟩ : syracuseStep 158383 = 237575) B237575
theorem B223919 : Blo 147793 223919 := bstep (se 1 (by rfl) ⟨167939, by rfl⟩ : syracuseStep 223919 = 335879) B335879
theorem B223967 : Blo 147793 223967 := bstep (se 1 (by rfl) ⟨167975, by rfl⟩ : syracuseStep 223967 = 335951) B335951
theorem B224231 : Blo 147793 224231 := bstep (se 1 (by rfl) ⟨168173, by rfl⟩ : syracuseStep 224231 = 336347) B336347
theorem B748763 : Blo 147793 748763 := bstep (se 1 (by rfl) ⟨561572, by rfl⟩ : syracuseStep 748763 = 1123145) B1123145
theorem B224489 : Blo 147793 224489 := bstep (se 2 (by rfl) ⟨84183, by rfl⟩ : syracuseStep 224489 = 168367) B168367
theorem B224543 : Blo 147793 224543 := bstep (se 1 (by rfl) ⟨168407, by rfl⟩ : syracuseStep 224543 = 336815) B336815
theorem B224711 : Blo 147793 224711 := bstep (se 1 (by rfl) ⟨168533, by rfl⟩ : syracuseStep 224711 = 337067) B337067
theorem B1207817 : Blo 147793 1207817 := bstep (se 2 (by rfl) ⟨452931, by rfl⟩ : syracuseStep 1207817 = 905863) B905863
theorem B650767 : Blo 147793 650767 := bstep (se 1 (by rfl) ⟨488075, by rfl⟩ : syracuseStep 650767 = 976151) B976151
theorem B192071 : Blo 147793 192071 := bstep (se 1 (by rfl) ⟨144053, by rfl⟩ : syracuseStep 192071 = 288107) B288107
theorem B159455 : Blo 147793 159455 := bstep (se 1 (by rfl) ⟨119591, by rfl⟩ : syracuseStep 159455 = 239183) B239183
theorem B225065 : Blo 147793 225065 := bstep (se 2 (by rfl) ⟨84399, by rfl⟩ : syracuseStep 225065 = 168799) B168799
theorem B323369 : Blo 147793 323369 := bstep (se 2 (by rfl) ⟨121263, by rfl⟩ : syracuseStep 323369 = 242527) B242527
theorem B225071 : Blo 147793 225071 := bstep (se 1 (by rfl) ⟨168803, by rfl⟩ : syracuseStep 225071 = 337607) B337607
theorem B1142585 : Blo 147793 1142585 := bstep (se 2 (by rfl) ⟨428469, by rfl⟩ : syracuseStep 1142585 = 856939) B856939
theorem B716971 : Blo 147793 716971 := bstep (se 1 (by rfl) ⟨537728, by rfl⟩ : syracuseStep 716971 = 1075457) B1075457
theorem B225545 : Blo 147793 225545 := bstep (se 2 (by rfl) ⟨84579, by rfl⟩ : syracuseStep 225545 = 169159) B169159
theorem B1208591 : Blo 147793 1208591 := bstep (se 1 (by rfl) ⟨906443, by rfl⟩ : syracuseStep 1208591 = 1812887) B1812887
theorem B749897 : Blo 147793 749897 := bstep (se 2 (by rfl) ⟨281211, by rfl⟩ : syracuseStep 749897 = 562423) B562423
theorem B225647 : Blo 147793 225647 := bstep (se 1 (by rfl) ⟨169235, by rfl⟩ : syracuseStep 225647 = 338471) B338471
theorem B225863 : Blo 147793 225863 := bstep (se 1 (by rfl) ⟨169397, by rfl⟩ : syracuseStep 225863 = 338795) B338795
theorem B225899 : Blo 147793 225899 := bstep (se 1 (by rfl) ⟨169424, by rfl⟩ : syracuseStep 225899 = 338849) B338849
theorem B979609 : Blo 147793 979609 := bstep (se 2 (by rfl) ⟨367353, by rfl⟩ : syracuseStep 979609 = 734707) B734707
theorem B357139 : Blo 147793 357139 := bstep (se 1 (by rfl) ⟨267854, by rfl⟩ : syracuseStep 357139 = 535709) B535709
theorem B160591 : Blo 147793 160591 := bstep (se 1 (by rfl) ⟨120443, by rfl⟩ : syracuseStep 160591 = 240887) B240887
theorem B226127 : Blo 147793 226127 := bstep (se 1 (by rfl) ⟨169595, by rfl⟩ : syracuseStep 226127 = 339191) B339191
theorem B717815 : Blo 147793 717815 := bstep (se 1 (by rfl) ⟨538361, by rfl⟩ : syracuseStep 717815 = 1076723) B1076723
theorem B1078397 : Blo 147793 1078397 := bstep (se 3 (by rfl) ⟨202199, by rfl⟩ : syracuseStep 1078397 = 404399) B404399
theorem B652445 : Blo 147793 652445 := bstep (se 3 (by rfl) ⟨122333, by rfl⟩ : syracuseStep 652445 = 244667) B244667
theorem B226523 : Blo 147793 226523 := bstep (se 1 (by rfl) ⟨169892, by rfl⟩ : syracuseStep 226523 = 339785) B339785
theorem B226697 : Blo 147793 226697 := bstep (se 2 (by rfl) ⟨85011, by rfl⟩ : syracuseStep 226697 = 170023) B170023
theorem B423481 : Blo 147793 423481 := bstep (se 2 (by rfl) ⟨158805, by rfl⟩ : syracuseStep 423481 = 317611) B317611
theorem B751193 : Blo 147793 751193 := bstep (se 2 (by rfl) ⟨281697, by rfl⟩ : syracuseStep 751193 = 563395) B563395
theorem B227051 : Blo 147793 227051 := bstep (se 1 (by rfl) ⟨170288, by rfl⟩ : syracuseStep 227051 = 340577) B340577
theorem B3667805 : Blo 147793 3667805 := bstep (se 3 (by rfl) ⟨687713, by rfl⟩ : syracuseStep 3667805 = 1375427) B1375427
theorem B227279 : Blo 147793 227279 := bstep (se 1 (by rfl) ⟨170459, by rfl⟩ : syracuseStep 227279 = 340919) B340919
theorem B227675 : Blo 147793 227675 := bstep (se 1 (by rfl) ⟨170756, by rfl⟩ : syracuseStep 227675 = 341513) B341513
theorem B358823 : Blo 147793 358823 := bstep (se 1 (by rfl) ⟨269117, by rfl⟩ : syracuseStep 358823 = 538235) B538235
theorem B293371 : Blo 147793 293371 := bstep (se 1 (by rfl) ⟨220028, by rfl⟩ : syracuseStep 293371 = 440057) B440057
theorem B457289 : Blo 147793 457289 := bstep (se 2 (by rfl) ⟨171483, by rfl⟩ : syracuseStep 457289 = 342967) B342967
theorem B358985 : Blo 147793 358985 := bstep (se 2 (by rfl) ⟨134619, by rfl⟩ : syracuseStep 358985 = 269239) B269239
theorem B850607 : Blo 147793 850607 := bstep (se 1 (by rfl) ⟨637955, by rfl⟩ : syracuseStep 850607 = 1275911) B1275911
theorem B424723 : Blo 147793 424723 := bstep (se 1 (by rfl) ⟨318542, by rfl⟩ : syracuseStep 424723 = 637085) B637085
theorem B4651931 : Blo 147793 4651931 := bstep (se 1 (by rfl) ⟨3488948, by rfl⟩ : syracuseStep 4651931 = 6977897) B6977897
theorem B818075 : Blo 147793 818075 := bstep (se 1 (by rfl) ⟨613556, by rfl⟩ : syracuseStep 818075 = 1227113) B1227113
theorem B10911149 : Blo 147793 10911149 := bstep (se 3 (by rfl) ⟨2045840, by rfl⟩ : syracuseStep 10911149 = 4091681) B4091681
theorem B67927853 : Blo 147793 67927853 := bstep (se 3 (by rfl) ⟨12736472, by rfl⟩ : syracuseStep 67927853 = 25472945) B25472945
theorem B426215 : Blo 147793 426215 := bstep (se 1 (by rfl) ⟨319661, by rfl⟩ : syracuseStep 426215 = 639323) B639323
theorem B426671 : Blo 147793 426671 := bstep (se 1 (by rfl) ⟨320003, by rfl⟩ : syracuseStep 426671 = 640007) B640007
theorem B6456023 : Blo 147793 6456023 := bstep (se 1 (by rfl) ⟨4842017, by rfl⟩ : syracuseStep 6456023 = 9684035) B9684035
theorem B1049951 : Blo 147793 1049951 := bstep (se 1 (by rfl) ⟨787463, by rfl⟩ : syracuseStep 1049951 = 1574927) B1574927
theorem B329131 : Blo 147793 329131 := bstep (se 1 (by rfl) ⟨246848, by rfl⟩ : syracuseStep 329131 = 493697) B493697
theorem B427513 : Blo 147793 427513 := bstep (se 2 (by rfl) ⟨160317, by rfl⟩ : syracuseStep 427513 = 320635) B320635
theorem B722429 : Blo 147793 722429 := bstep (se 3 (by rfl) ⟨135455, by rfl⟩ : syracuseStep 722429 = 270911) B270911
theorem B853523 : Blo 147793 853523 := bstep (se 1 (by rfl) ⟨640142, by rfl⟩ : syracuseStep 853523 = 1280285) B1280285
theorem B3671687 : Blo 147793 3671687 := bstep (se 1 (by rfl) ⟨2753765, by rfl⟩ : syracuseStep 3671687 = 5507531) B5507531
theorem B427855 : Blo 147793 427855 := bstep (se 1 (by rfl) ⟨320891, by rfl⟩ : syracuseStep 427855 = 641783) B641783
theorem B854225 : Blo 147793 854225 := bstep (se 2 (by rfl) ⟨320334, by rfl⟩ : syracuseStep 854225 = 640669) B640669
theorem B723487 : Blo 147793 723487 := bstep (se 1 (by rfl) ⟨542615, by rfl⟩ : syracuseStep 723487 = 1085231) B1085231
theorem B166747 : Blo 147793 166747 := bstep (se 1 (by rfl) ⟨125060, by rfl⟩ : syracuseStep 166747 = 250121) B250121
theorem B1575973 : Blo 147793 1575973 := bstep (se 4 (by rfl) ⟨147747, by rfl⟩ : syracuseStep 1575973 = 295495) B295495
theorem B429563 : Blo 147793 429563 := bstep (se 1 (by rfl) ⟨322172, by rfl⟩ : syracuseStep 429563 = 644345) B644345
theorem B396863 : Blo 147793 396863 := bstep (se 1 (by rfl) ⟨297647, by rfl⟩ : syracuseStep 396863 = 595295) B595295
theorem B167719 : Blo 147793 167719 := bstep (se 1 (by rfl) ⟨125789, by rfl⟩ : syracuseStep 167719 = 251579) B251579
theorem B1904741 : Blo 147793 1904741 := bstep (se 4 (by rfl) ⟨178569, by rfl⟩ : syracuseStep 1904741 = 357139) B357139
theorem B266471 : Blo 147793 266471 := bstep (se 1 (by rfl) ⟨199853, by rfl⟩ : syracuseStep 266471 = 399707) B399707
theorem B1086155 : Blo 147793 1086155 := bstep (se 1 (by rfl) ⟨814616, by rfl⟩ : syracuseStep 1086155 = 1629233) B1629233
theorem B332585 : Blo 147793 332585 := bstep (se 2 (by rfl) ⟨124719, by rfl⟩ : syracuseStep 332585 = 249439) B249439
theorem B201583 : Blo 147793 201583 := bstep (se 1 (by rfl) ⟨151187, by rfl⟩ : syracuseStep 201583 = 302375) B302375
theorem B168871 : Blo 147793 168871 := bstep (se 1 (by rfl) ⟨126653, by rfl⟩ : syracuseStep 168871 = 253307) B253307
theorem B332855 : Blo 147793 332855 := bstep (se 1 (by rfl) ⟨249641, by rfl⟩ : syracuseStep 332855 = 499283) B499283
theorem B332873 : Blo 147793 332873 := bstep (se 2 (by rfl) ⟨124827, by rfl⟩ : syracuseStep 332873 = 249655) B249655
theorem B1938775 : Blo 147793 1938775 := bstep (se 1 (by rfl) ⟨1454081, by rfl⟩ : syracuseStep 1938775 = 2908163) B2908163
theorem B759131 : Blo 147793 759131 := bstep (se 1 (by rfl) ⟨569348, by rfl⟩ : syracuseStep 759131 = 1138697) B1138697
theorem B955961 : Blo 147793 955961 := bstep (se 2 (by rfl) ⟨358485, by rfl⟩ : syracuseStep 955961 = 716971) B716971
theorem B563183 : Blo 147793 563183 := bstep (se 1 (by rfl) ⟨422387, by rfl⟩ : syracuseStep 563183 = 844775) B844775
theorem B858397 : Blo 147793 858397 := bstep (se 3 (by rfl) ⟨160949, by rfl⟩ : syracuseStep 858397 = 321899) B321899
theorem B170527 : Blo 147793 170527 := bstep (se 1 (by rfl) ⟨127895, by rfl⟩ : syracuseStep 170527 = 255791) B255791
theorem B1284659 : Blo 147793 1284659 := bstep (se 1 (by rfl) ⟨963494, by rfl⟩ : syracuseStep 1284659 = 1926989) B1926989
theorem B2038405 : Blo 147793 2038405 := bstep (se 4 (by rfl) ⟨191100, by rfl⟩ : syracuseStep 2038405 = 382201) B382201
theorem B11606819 : Blo 147793 11606819 := bstep (se 1 (by rfl) ⟨8705114, by rfl⟩ : syracuseStep 11606819 = 17410229) B17410229
theorem B858923 : Blo 147793 858923 := bstep (se 1 (by rfl) ⟨644192, by rfl⟩ : syracuseStep 858923 = 1288385) B1288385
theorem B334799 : Blo 147793 334799 := bstep (se 1 (by rfl) ⟨251099, by rfl⟩ : syracuseStep 334799 = 502199) B502199
theorem B334817 : Blo 147793 334817 := bstep (se 2 (by rfl) ⟨125556, by rfl⟩ : syracuseStep 334817 = 251113) B251113
theorem B334889 : Blo 147793 334889 := bstep (se 2 (by rfl) ⟨125583, by rfl⟩ : syracuseStep 334889 = 251167) B251167
theorem B564641 : Blo 147793 564641 := bstep (se 2 (by rfl) ⟨211740, by rfl⟩ : syracuseStep 564641 = 423481) B423481
theorem B499175 : Blo 147793 499175 := bstep (se 1 (by rfl) ⟨374381, by rfl⟩ : syracuseStep 499175 = 748763) B748763
theorem B761723 : Blo 147793 761723 := bstep (se 1 (by rfl) ⟨571292, by rfl⟩ : syracuseStep 761723 = 1142585) B1142585
theorem B2957417 : Blo 147793 2957417 := bstep (se 2 (by rfl) ⟨1109031, by rfl⟩ : syracuseStep 2957417 = 2218063) B2218063
theorem B499931 : Blo 147793 499931 := bstep (se 1 (by rfl) ⟨374948, by rfl⟩ : syracuseStep 499931 = 749897) B749897
theorem B270623 : Blo 147793 270623 := bstep (se 1 (by rfl) ⟨202967, by rfl⟩ : syracuseStep 270623 = 405935) B405935
theorem B729425 : Blo 147793 729425 := bstep (se 2 (by rfl) ⟨273534, by rfl⟩ : syracuseStep 729425 = 547069) B547069
theorem B762209 : Blo 147793 762209 := bstep (se 2 (by rfl) ⟨285828, by rfl⟩ : syracuseStep 762209 = 571657) B571657
theorem B500201 : Blo 147793 500201 := bstep (se 2 (by rfl) ⟨187575, by rfl⟩ : syracuseStep 500201 = 375151) B375151
theorem B434963 : Blo 147793 434963 := bstep (se 1 (by rfl) ⟨326222, by rfl⟩ : syracuseStep 434963 = 652445) B652445
theorem B336851 : Blo 147793 336851 := bstep (se 1 (by rfl) ⟨252638, by rfl⟩ : syracuseStep 336851 = 505277) B505277
theorem B566297 : Blo 147793 566297 := bstep (se 2 (by rfl) ⟨212361, by rfl⟩ : syracuseStep 566297 = 424723) B424723
theorem B500795 : Blo 147793 500795 := bstep (se 1 (by rfl) ⟨375596, by rfl⟩ : syracuseStep 500795 = 751193) B751193
theorem B337103 : Blo 147793 337103 := bstep (se 1 (by rfl) ⟨252827, by rfl⟩ : syracuseStep 337103 = 505655) B505655
theorem B501065 : Blo 147793 501065 := bstep (se 2 (by rfl) ⟨187899, by rfl⟩ : syracuseStep 501065 = 375799) B375799
theorem B337427 : Blo 147793 337427 := bstep (se 1 (by rfl) ⟨253070, by rfl⟩ : syracuseStep 337427 = 506141) B506141
theorem B239215 : Blo 147793 239215 := bstep (se 1 (by rfl) ⟨179411, by rfl⟩ : syracuseStep 239215 = 358823) B358823
theorem B304859 : Blo 147793 304859 := bstep (se 1 (by rfl) ⟨228644, by rfl⟩ : syracuseStep 304859 = 457289) B457289
theorem B239323 : Blo 147793 239323 := bstep (se 1 (by rfl) ⟨179492, by rfl⟩ : syracuseStep 239323 = 358985) B358985
theorem B567071 : Blo 147793 567071 := bstep (se 1 (by rfl) ⟨425303, by rfl⟩ : syracuseStep 567071 = 850607) B850607
theorem B338111 : Blo 147793 338111 := bstep (se 1 (by rfl) ⟨253583, by rfl⟩ : syracuseStep 338111 = 507167) B507167
theorem B239849 : Blo 147793 239849 := bstep (se 2 (by rfl) ⟨89943, by rfl⟩ : syracuseStep 239849 = 179887) B179887
theorem B1289033 : Blo 147793 1289033 := bstep (se 2 (by rfl) ⟨483387, by rfl⟩ : syracuseStep 1289033 = 966775) B966775
theorem B273449 : Blo 147793 273449 := bstep (se 2 (by rfl) ⟨102543, by rfl⟩ : syracuseStep 273449 = 205087) B205087
theorem B9972823 : Blo 147793 9972823 := bstep (se 1 (by rfl) ⟨7479617, by rfl⟩ : syracuseStep 9972823 = 14959235) B14959235
theorem B339065 : Blo 147793 339065 := bstep (se 2 (by rfl) ⟨127149, by rfl⟩ : syracuseStep 339065 = 254299) B254299
theorem B240823 : Blo 147793 240823 := bstep (se 1 (by rfl) ⟨180617, by rfl⟩ : syracuseStep 240823 = 361235) B361235
theorem B1453625 : Blo 147793 1453625 := bstep (se 2 (by rfl) ⟨545109, by rfl⟩ : syracuseStep 1453625 = 1090219) B1090219
theorem B339731 : Blo 147793 339731 := bstep (se 1 (by rfl) ⟨254798, by rfl⟩ : syracuseStep 339731 = 509597) B509597
theorem B503657 : Blo 147793 503657 := bstep (se 2 (by rfl) ⟨188871, by rfl⟩ : syracuseStep 503657 = 377743) B377743
theorem B569227 : Blo 147793 569227 := bstep (se 1 (by rfl) ⟨426920, by rfl⟩ : syracuseStep 569227 = 853841) B853841
theorem B340091 : Blo 147793 340091 := bstep (se 1 (by rfl) ⟨255068, by rfl⟩ : syracuseStep 340091 = 510137) B510137
theorem B962725 : Blo 147793 962725 := bstep (se 4 (by rfl) ⟨90255, by rfl⟩ : syracuseStep 962725 = 180511) B180511
theorem B340361 : Blo 147793 340361 := bstep (se 2 (by rfl) ⟨127635, by rfl⟩ : syracuseStep 340361 = 255271) B255271
theorem B177007 : Blo 147793 177007 := bstep (se 1 (by rfl) ⟨132755, by rfl⟩ : syracuseStep 177007 = 265511) B265511
theorem B341099 : Blo 147793 341099 := bstep (se 1 (by rfl) ⟨255824, by rfl⟩ : syracuseStep 341099 = 511649) B511649
theorem B505007 : Blo 147793 505007 := bstep (se 1 (by rfl) ⟨378755, by rfl⟩ : syracuseStep 505007 = 757511) B757511
theorem B1717523 : Blo 147793 1717523 := bstep (se 1 (by rfl) ⟨1288142, by rfl⟩ : syracuseStep 1717523 = 2576285) B2576285
theorem B374665 : Blo 147793 374665 := bstep (se 2 (by rfl) ⟨140499, by rfl⟩ : syracuseStep 374665 = 280999) B280999
theorem B374777 : Blo 147793 374777 := bstep (se 2 (by rfl) ⟨140541, by rfl⟩ : syracuseStep 374777 = 281083) B281083
theorem B571475 : Blo 147793 571475 := bstep (se 1 (by rfl) ⟨428606, by rfl⟩ : syracuseStep 571475 = 857213) B857213
theorem B374939 : Blo 147793 374939 := bstep (se 1 (by rfl) ⟨281204, by rfl⟩ : syracuseStep 374939 = 562409) B562409
theorem B211177 : Blo 147793 211177 := bstep (se 2 (by rfl) ⟨79191, by rfl⟩ : syracuseStep 211177 = 158383) B158383
theorem B768365 : Blo 147793 768365 := bstep (se 3 (by rfl) ⟨144068, by rfl⟩ : syracuseStep 768365 = 288137) B288137
theorem B2144627 : Blo 147793 2144627 := bstep (se 1 (by rfl) ⟨1608470, by rfl⟩ : syracuseStep 2144627 = 3216941) B3216941
theorem B1030643 : Blo 147793 1030643 := bstep (se 1 (by rfl) ⟨772982, by rfl⟩ : syracuseStep 1030643 = 1545965) B1545965
theorem B571961 : Blo 147793 571961 := bstep (se 2 (by rfl) ⟨214485, by rfl⟩ : syracuseStep 571961 = 428971) B428971
theorem B1227727 : Blo 147793 1227727 := bstep (se 1 (by rfl) ⟨920795, by rfl⟩ : syracuseStep 1227727 = 1841591) B1841591
theorem B506951 : Blo 147793 506951 := bstep (se 1 (by rfl) ⟨380213, by rfl⟩ : syracuseStep 506951 = 760427) B760427
theorem B507005 : Blo 147793 507005 := bstep (se 3 (by rfl) ⟨95063, by rfl⟩ : syracuseStep 507005 = 190127) B190127
theorem B376073 : Blo 147793 376073 := bstep (se 2 (by rfl) ⟨141027, by rfl⟩ : syracuseStep 376073 = 282055) B282055
theorem B867689 : Blo 147793 867689 := bstep (se 2 (by rfl) ⟨325383, by rfl⟩ : syracuseStep 867689 = 650767) B650767
theorem B507275 : Blo 147793 507275 := bstep (se 1 (by rfl) ⟨380456, by rfl⟩ : syracuseStep 507275 = 760913) B760913
theorem B573115 : Blo 147793 573115 := bstep (se 1 (by rfl) ⟨429836, by rfl⟩ : syracuseStep 573115 = 859673) B859673
theorem B212959 : Blo 147793 212959 := bstep (se 1 (by rfl) ⟨159719, by rfl⟩ : syracuseStep 212959 = 319439) B319439
theorem B1720439 : Blo 147793 1720439 := bstep (se 1 (by rfl) ⟨1290329, by rfl⟩ : syracuseStep 1720439 = 2580659) B2580659
theorem B180535 : Blo 147793 180535 := bstep (se 1 (by rfl) ⟨135401, by rfl⟩ : syracuseStep 180535 = 270803) B270803
theorem B147839 : Blo 147793 147839 := bstep (se 1 (by rfl) ⟨110879, by rfl⟩ : syracuseStep 147839 = 221759) B221759
theorem B147919 : Blo 147793 147919 := bstep (se 1 (by rfl) ⟨110939, by rfl⟩ : syracuseStep 147919 = 221879) B221879
theorem B213455 : Blo 147793 213455 := bstep (se 1 (by rfl) ⟨160091, by rfl⟩ : syracuseStep 213455 = 320183) B320183
theorem B148071 : Blo 147793 148071 := bstep (se 1 (by rfl) ⟨111053, by rfl⟩ : syracuseStep 148071 = 222107) B222107
theorem B639683 : Blo 147793 639683 := bstep (se 1 (by rfl) ⟨479762, by rfl⟩ : syracuseStep 639683 = 959525) B959525
theorem B1688363 : Blo 147793 1688363 := bstep (se 1 (by rfl) ⟨1266272, by rfl⟩ : syracuseStep 1688363 = 2532545) B2532545
theorem B148335 : Blo 147793 148335 := bstep (se 1 (by rfl) ⟨111251, by rfl⟩ : syracuseStep 148335 = 222503) B222503
theorem B148391 : Blo 147793 148391 := bstep (se 1 (by rfl) ⟨111293, by rfl⟩ : syracuseStep 148391 = 222587) B222587
theorem B1917863 : Blo 147793 1917863 := bstep (se 1 (by rfl) ⟨1438397, by rfl⟩ : syracuseStep 1917863 = 2876795) B2876795
theorem B148475 : Blo 147793 148475 := bstep (se 1 (by rfl) ⟨111356, by rfl⟩ : syracuseStep 148475 = 222713) B222713
theorem B148543 : Blo 147793 148543 := bstep (se 1 (by rfl) ⟨111407, by rfl⟩ : syracuseStep 148543 = 222815) B222815
theorem B214121 : Blo 147793 214121 := bstep (se 2 (by rfl) ⟨80295, by rfl⟩ : syracuseStep 214121 = 160591) B160591
theorem B148687 : Blo 147793 148687 := bstep (se 1 (by rfl) ⟨111515, by rfl⟩ : syracuseStep 148687 = 223031) B223031
theorem B148891 : Blo 147793 148891 := bstep (se 1 (by rfl) ⟨111668, by rfl⟩ : syracuseStep 148891 = 223337) B223337
theorem B4081175 : Blo 147793 4081175 := bstep (se 1 (by rfl) ⟨3060881, by rfl⟩ : syracuseStep 4081175 = 6121763) B6121763
theorem B1590821 : Blo 147793 1590821 := bstep (se 4 (by rfl) ⟨149139, by rfl⟩ : syracuseStep 1590821 = 298279) B298279
theorem B2868797 : Blo 147793 2868797 := bstep (se 3 (by rfl) ⟨537899, by rfl⟩ : syracuseStep 2868797 = 1075799) B1075799
theorem B149103 : Blo 147793 149103 := bstep (se 1 (by rfl) ⟨111827, by rfl⟩ : syracuseStep 149103 = 223655) B223655
theorem B149159 : Blo 147793 149159 := bstep (se 1 (by rfl) ⟨111869, by rfl⟩ : syracuseStep 149159 = 223739) B223739
theorem B149243 : Blo 147793 149243 := bstep (se 1 (by rfl) ⟨111932, by rfl⟩ : syracuseStep 149243 = 223865) B223865
theorem B149279 : Blo 147793 149279 := bstep (se 1 (by rfl) ⟨111959, by rfl⟩ : syracuseStep 149279 = 223919) B223919
theorem B149311 : Blo 147793 149311 := bstep (se 1 (by rfl) ⟨111983, by rfl⟩ : syracuseStep 149311 = 223967) B223967
theorem B149487 : Blo 147793 149487 := bstep (se 1 (by rfl) ⟨112115, by rfl⟩ : syracuseStep 149487 = 224231) B224231
theorem B149659 : Blo 147793 149659 := bstep (se 1 (by rfl) ⟨112244, by rfl⟩ : syracuseStep 149659 = 224489) B224489
theorem B149695 : Blo 147793 149695 := bstep (se 1 (by rfl) ⟨112271, by rfl⟩ : syracuseStep 149695 = 224543) B224543
theorem B149807 : Blo 147793 149807 := bstep (se 1 (by rfl) ⟨112355, by rfl⟩ : syracuseStep 149807 = 224711) B224711
theorem B805211 : Blo 147793 805211 := bstep (se 1 (by rfl) ⟨603908, by rfl⟩ : syracuseStep 805211 = 1207817) B1207817
theorem B510299 : Blo 147793 510299 := bstep (se 1 (by rfl) ⟨382724, by rfl⟩ : syracuseStep 510299 = 765449) B765449
theorem B150043 : Blo 147793 150043 := bstep (se 1 (by rfl) ⟨112532, by rfl⟩ : syracuseStep 150043 = 225065) B225065
theorem B215579 : Blo 147793 215579 := bstep (se 1 (by rfl) ⟨161684, by rfl⟩ : syracuseStep 215579 = 323369) B323369
theorem B150047 : Blo 147793 150047 := bstep (se 1 (by rfl) ⟨112535, by rfl⟩ : syracuseStep 150047 = 225071) B225071
theorem B576031 : Blo 147793 576031 := bstep (se 1 (by rfl) ⟨432023, by rfl⟩ : syracuseStep 576031 = 864047) B864047
theorem B510569 : Blo 147793 510569 := bstep (se 2 (by rfl) ⟨191463, by rfl⟩ : syracuseStep 510569 = 382927) B382927
theorem B150363 : Blo 147793 150363 := bstep (se 1 (by rfl) ⟨112772, by rfl⟩ : syracuseStep 150363 = 225545) B225545
theorem B805727 : Blo 147793 805727 := bstep (se 1 (by rfl) ⟨604295, by rfl⟩ : syracuseStep 805727 = 1208591) B1208591
theorem B150431 : Blo 147793 150431 := bstep (se 1 (by rfl) ⟨112823, by rfl⟩ : syracuseStep 150431 = 225647) B225647
theorem B150575 : Blo 147793 150575 := bstep (se 1 (by rfl) ⟨112931, by rfl⟩ : syracuseStep 150575 = 225863) B225863
theorem B150599 : Blo 147793 150599 := bstep (se 1 (by rfl) ⟨112949, by rfl⟩ : syracuseStep 150599 = 225899) B225899
theorem B150751 : Blo 147793 150751 := bstep (se 1 (by rfl) ⟨113063, by rfl⟩ : syracuseStep 150751 = 226127) B226127
theorem B478543 : Blo 147793 478543 := bstep (se 1 (by rfl) ⟨358907, by rfl⟩ : syracuseStep 478543 = 717815) B717815
theorem B151015 : Blo 147793 151015 := bstep (se 1 (by rfl) ⟨113261, by rfl⟩ : syracuseStep 151015 = 226523) B226523
theorem B151131 : Blo 147793 151131 := bstep (se 1 (by rfl) ⟨113348, by rfl⟩ : syracuseStep 151131 = 226697) B226697
theorem B511595 : Blo 147793 511595 := bstep (se 1 (by rfl) ⟨383696, by rfl⟩ : syracuseStep 511595 = 767393) B767393
theorem B151367 : Blo 147793 151367 := bstep (se 1 (by rfl) ⟨113525, by rfl⟩ : syracuseStep 151367 = 227051) B227051
theorem B511865 : Blo 147793 511865 := bstep (se 2 (by rfl) ⟨191949, by rfl⟩ : syracuseStep 511865 = 383899) B383899
theorem B2445203 : Blo 147793 2445203 := bstep (se 1 (by rfl) ⟨1833902, by rfl⟩ : syracuseStep 2445203 = 3667805) B3667805
theorem B151519 : Blo 147793 151519 := bstep (se 1 (by rfl) ⟨113639, by rfl⟩ : syracuseStep 151519 = 227279) B227279
theorem B512189 : Blo 147793 512189 := bstep (se 3 (by rfl) ⟨96035, by rfl⟩ : syracuseStep 512189 = 192071) B192071
theorem B3920075 : Blo 147793 3920075 := bstep (se 1 (by rfl) ⟨2940056, by rfl⟩ : syracuseStep 3920075 = 5880113) B5880113
theorem B250087 : Blo 147793 250087 := bstep (se 1 (by rfl) ⟨187565, by rfl⟩ : syracuseStep 250087 = 375131) B375131
theorem B151783 : Blo 147793 151783 := bstep (se 1 (by rfl) ⟨113837, by rfl⟩ : syracuseStep 151783 = 227675) B227675
theorem B250249 : Blo 147793 250249 := bstep (se 2 (by rfl) ⟨93843, by rfl⟩ : syracuseStep 250249 = 187687) B187687
theorem B3101287 : Blo 147793 3101287 := bstep (se 1 (by rfl) ⟨2325965, by rfl⟩ : syracuseStep 3101287 = 4651931) B4651931
theorem B545383 : Blo 147793 545383 := bstep (se 1 (by rfl) ⟨409037, by rfl⟩ : syracuseStep 545383 = 818075) B818075
theorem B250681 : Blo 147793 250681 := bstep (se 2 (by rfl) ⟨94005, by rfl⟩ : syracuseStep 250681 = 188011) B188011
theorem B250735 : Blo 147793 250735 := bstep (se 1 (by rfl) ⟨188051, by rfl⟩ : syracuseStep 250735 = 376103) B376103
theorem B250985 : Blo 147793 250985 := bstep (se 2 (by rfl) ⟨94119, by rfl⟩ : syracuseStep 250985 = 188239) B188239
theorem B906785 : Blo 147793 906785 := bstep (se 2 (by rfl) ⟨340044, by rfl⟩ : syracuseStep 906785 = 680089) B680089
theorem B382715 : Blo 147793 382715 := bstep (se 1 (by rfl) ⟨287036, by rfl⟩ : syracuseStep 382715 = 574073) B574073
theorem B252139 : Blo 147793 252139 := bstep (se 1 (by rfl) ⟨189104, by rfl⟩ : syracuseStep 252139 = 378209) B378209
theorem B8739251 : Blo 147793 8739251 := bstep (se 1 (by rfl) ⟨6554438, by rfl⟩ : syracuseStep 8739251 = 13108877) B13108877
theorem B252443 : Blo 147793 252443 := bstep (se 1 (by rfl) ⟨189332, by rfl⟩ : syracuseStep 252443 = 378665) B378665
theorem B4119113 : Blo 147793 4119113 := bstep (se 2 (by rfl) ⟨1544667, by rfl⟩ : syracuseStep 4119113 = 3089335) B3089335
theorem B1137239 : Blo 147793 1137239 := bstep (se 1 (by rfl) ⟨852929, by rfl⟩ : syracuseStep 1137239 = 1705859) B1705859
theorem B416603 : Blo 147793 416603 := bstep (se 1 (by rfl) ⟨312452, by rfl⟩ : syracuseStep 416603 = 624905) B624905
theorem B383849 : Blo 147793 383849 := bstep (se 2 (by rfl) ⟨143943, by rfl⟩ : syracuseStep 383849 = 287887) B287887
theorem B1924013 : Blo 147793 1924013 := bstep (se 3 (by rfl) ⟨360752, by rfl⟩ : syracuseStep 1924013 = 721505) B721505
theorem B1072109 : Blo 147793 1072109 := bstep (se 3 (by rfl) ⟨201020, by rfl⟩ : syracuseStep 1072109 = 402041) B402041
theorem B384041 : Blo 147793 384041 := bstep (se 2 (by rfl) ⟨144015, by rfl⟩ : syracuseStep 384041 = 288031) B288031
theorem B253111 : Blo 147793 253111 := bstep (se 1 (by rfl) ⟨189833, by rfl⟩ : syracuseStep 253111 = 379667) B379667
theorem B3857867 : Blo 147793 3857867 := bstep (se 1 (by rfl) ⟨2893400, by rfl⟩ : syracuseStep 3857867 = 5786801) B5786801
theorem B286163 : Blo 147793 286163 := bstep (se 1 (by rfl) ⟨214622, by rfl⟩ : syracuseStep 286163 = 429245) B429245
theorem B253415 : Blo 147793 253415 := bstep (se 1 (by rfl) ⟨190061, by rfl⟩ : syracuseStep 253415 = 380123) B380123
theorem B3104243 : Blo 147793 3104243 := bstep (se 1 (by rfl) ⟨2328182, by rfl⟩ : syracuseStep 3104243 = 4656365) B4656365
theorem B253435 : Blo 147793 253435 := bstep (se 1 (by rfl) ⟨190076, by rfl⟩ : syracuseStep 253435 = 380153) B380153
theorem B3858043 : Blo 147793 3858043 := bstep (se 1 (by rfl) ⟨2893532, by rfl⟩ : syracuseStep 3858043 = 5787065) B5787065
theorem B1629931 : Blo 147793 1629931 := bstep (se 1 (by rfl) ⟨1222448, by rfl⟩ : syracuseStep 1629931 = 2444897) B2444897
theorem B581431 : Blo 147793 581431 := bstep (se 1 (by rfl) ⟨436073, by rfl⟩ : syracuseStep 581431 = 872147) B872147
theorem B253867 : Blo 147793 253867 := bstep (se 1 (by rfl) ⟨190400, by rfl⟩ : syracuseStep 253867 = 380801) B380801
theorem B909245 : Blo 147793 909245 := bstep (se 3 (by rfl) ⟨170483, by rfl⟩ : syracuseStep 909245 = 340967) B340967
theorem B1564645 : Blo 147793 1564645 := bstep (se 4 (by rfl) ⟨146685, by rfl⟩ : syracuseStep 1564645 = 293371) B293371
theorem B254171 : Blo 147793 254171 := bstep (se 1 (by rfl) ⟨190628, by rfl⟩ : syracuseStep 254171 = 381257) B381257
theorem B614753 : Blo 147793 614753 := bstep (se 2 (by rfl) ⟨230532, by rfl⟩ : syracuseStep 614753 = 461065) B461065
theorem B254407 : Blo 147793 254407 := bstep (se 1 (by rfl) ⟨190805, by rfl⟩ : syracuseStep 254407 = 381611) B381611
theorem B254441 : Blo 147793 254441 := bstep (se 2 (by rfl) ⟨95415, by rfl⟩ : syracuseStep 254441 = 190831) B190831
theorem B221993 : Blo 147793 221993 := bstep (se 2 (by rfl) ⟨83247, by rfl⟩ : syracuseStep 221993 = 166495) B166495
theorem B221999 : Blo 147793 221999 := bstep (se 1 (by rfl) ⟨166499, by rfl⟩ : syracuseStep 221999 = 332999) B332999
theorem B287545 : Blo 147793 287545 := bstep (se 2 (by rfl) ⟨107829, by rfl⟩ : syracuseStep 287545 = 215659) B215659
theorem B222119 : Blo 147793 222119 := bstep (se 1 (by rfl) ⟨166589, by rfl⟩ : syracuseStep 222119 = 333179) B333179
theorem B222203 : Blo 147793 222203 := bstep (se 1 (by rfl) ⟨166652, by rfl⟩ : syracuseStep 222203 = 333305) B333305
theorem B222263 : Blo 147793 222263 := bstep (se 1 (by rfl) ⟨166697, by rfl⟩ : syracuseStep 222263 = 333395) B333395
theorem B287849 : Blo 147793 287849 := bstep (se 2 (by rfl) ⟨107943, by rfl⟩ : syracuseStep 287849 = 215887) B215887
theorem B222383 : Blo 147793 222383 := bstep (se 1 (by rfl) ⟨166787, by rfl⟩ : syracuseStep 222383 = 333575) B333575
theorem B1697111 : Blo 147793 1697111 := bstep (se 1 (by rfl) ⟨1272833, by rfl⟩ : syracuseStep 1697111 = 2545667) B2545667
theorem B222791 : Blo 147793 222791 := bstep (se 1 (by rfl) ⟨167093, by rfl⟩ : syracuseStep 222791 = 334187) B334187
theorem B222887 : Blo 147793 222887 := bstep (se 1 (by rfl) ⟨167165, by rfl⟩ : syracuseStep 222887 = 334331) B334331
theorem B222971 : Blo 147793 222971 := bstep (se 1 (by rfl) ⟨167228, by rfl⟩ : syracuseStep 222971 = 334457) B334457
theorem B223007 : Blo 147793 223007 := bstep (se 1 (by rfl) ⟨167255, by rfl⟩ : syracuseStep 223007 = 334511) B334511
theorem B223055 : Blo 147793 223055 := bstep (se 1 (by rfl) ⟨167291, by rfl⟩ : syracuseStep 223055 = 334583) B334583
theorem B223175 : Blo 147793 223175 := bstep (se 1 (by rfl) ⟨167381, by rfl⟩ : syracuseStep 223175 = 334763) B334763
theorem B289003 : Blo 147793 289003 := bstep (se 1 (by rfl) ⟨216752, by rfl⟩ : syracuseStep 289003 = 433505) B433505
theorem B223529 : Blo 147793 223529 := bstep (se 2 (by rfl) ⟨83823, by rfl⟩ : syracuseStep 223529 = 167647) B167647
theorem B223535 : Blo 147793 223535 := bstep (se 1 (by rfl) ⟨167651, by rfl⟩ : syracuseStep 223535 = 335303) B335303
theorem B223775 : Blo 147793 223775 := bstep (se 1 (by rfl) ⟨167831, by rfl⟩ : syracuseStep 223775 = 335663) B335663
theorem B224159 : Blo 147793 224159 := bstep (se 1 (by rfl) ⟨168119, by rfl⟩ : syracuseStep 224159 = 336239) B336239
theorem B224207 : Blo 147793 224207 := bstep (se 1 (by rfl) ⟨168155, by rfl⟩ : syracuseStep 224207 = 336311) B336311
theorem B224297 : Blo 147793 224297 := bstep (se 2 (by rfl) ⟨84111, by rfl⟩ : syracuseStep 224297 = 168223) B168223
theorem B224303 : Blo 147793 224303 := bstep (se 1 (by rfl) ⟨168227, by rfl⟩ : syracuseStep 224303 = 336455) B336455
theorem B224327 : Blo 147793 224327 := bstep (se 1 (by rfl) ⟨168245, by rfl⟩ : syracuseStep 224327 = 336491) B336491
theorem B617593 : Blo 147793 617593 := bstep (se 2 (by rfl) ⟨231597, by rfl⟩ : syracuseStep 617593 = 463195) B463195
theorem B224591 : Blo 147793 224591 := bstep (se 1 (by rfl) ⟨168443, by rfl⟩ : syracuseStep 224591 = 336887) B336887
theorem B224681 : Blo 147793 224681 := bstep (se 2 (by rfl) ⟨84255, by rfl⟩ : syracuseStep 224681 = 168511) B168511
theorem B1306145 : Blo 147793 1306145 := bstep (se 2 (by rfl) ⟨489804, by rfl⟩ : syracuseStep 1306145 = 979609) B979609
theorem B224831 : Blo 147793 224831 := bstep (se 1 (by rfl) ⟨168623, by rfl⟩ : syracuseStep 224831 = 337247) B337247
theorem B225095 : Blo 147793 225095 := bstep (se 1 (by rfl) ⟨168821, by rfl⟩ : syracuseStep 225095 = 337643) B337643
theorem B323471 : Blo 147793 323471 := bstep (se 1 (by rfl) ⟨242603, by rfl⟩ : syracuseStep 323471 = 485207) B485207
theorem B225179 : Blo 147793 225179 := bstep (se 1 (by rfl) ⟨168884, by rfl⟩ : syracuseStep 225179 = 337769) B337769
theorem B356339 : Blo 147793 356339 := bstep (se 1 (by rfl) ⟨267254, by rfl⟩ : syracuseStep 356339 = 534509) B534509
theorem B225743 : Blo 147793 225743 := bstep (se 1 (by rfl) ⟨169307, by rfl⟩ : syracuseStep 225743 = 338615) B338615
theorem B225785 : Blo 147793 225785 := bstep (se 2 (by rfl) ⟨84669, by rfl⟩ : syracuseStep 225785 = 169339) B169339
theorem B848465 : Blo 147793 848465 := bstep (se 2 (by rfl) ⟨318174, by rfl⟩ : syracuseStep 848465 = 636349) B636349
theorem B225887 : Blo 147793 225887 := bstep (se 1 (by rfl) ⟨169415, by rfl⟩ : syracuseStep 225887 = 338831) B338831
theorem B7205597 : Blo 147793 7205597 := bstep (se 3 (by rfl) ⟨1351049, by rfl⟩ : syracuseStep 7205597 = 2702099) B2702099
theorem B4649957 : Blo 147793 4649957 := bstep (se 4 (by rfl) ⟨435933, by rfl⟩ : syracuseStep 4649957 = 871867) B871867
theorem B226367 : Blo 147793 226367 := bstep (se 1 (by rfl) ⟨169775, by rfl⟩ : syracuseStep 226367 = 339551) B339551
theorem B226409 : Blo 147793 226409 := bstep (se 2 (by rfl) ⟨84903, by rfl⟩ : syracuseStep 226409 = 169807) B169807
theorem B750707 : Blo 147793 750707 := bstep (se 1 (by rfl) ⟨563030, by rfl⟩ : syracuseStep 750707 = 1126061) B1126061
theorem B226511 : Blo 147793 226511 := bstep (se 1 (by rfl) ⟨169883, by rfl⟩ : syracuseStep 226511 = 339767) B339767
theorem B2061607 : Blo 147793 2061607 := bstep (se 1 (by rfl) ⟨1546205, by rfl⟩ : syracuseStep 2061607 = 3092411) B3092411
theorem B423265 : Blo 147793 423265 := bstep (se 2 (by rfl) ⟨158724, by rfl⟩ : syracuseStep 423265 = 317449) B317449
theorem B226715 : Blo 147793 226715 := bstep (se 1 (by rfl) ⟨170036, by rfl⟩ : syracuseStep 226715 = 340073) B340073
theorem B226937 : Blo 147793 226937 := bstep (se 2 (by rfl) ⟨85101, by rfl⟩ : syracuseStep 226937 = 170203) B170203
theorem B227039 : Blo 147793 227039 := bstep (se 1 (by rfl) ⟨170279, by rfl⟩ : syracuseStep 227039 = 340559) B340559
theorem B947963 : Blo 147793 947963 := bstep (se 1 (by rfl) ⟨710972, by rfl⟩ : syracuseStep 947963 = 1421945) B1421945
theorem B751355 : Blo 147793 751355 := bstep (se 1 (by rfl) ⟨563516, by rfl⟩ : syracuseStep 751355 = 1127033) B1127033
theorem B161599 : Blo 147793 161599 := bstep (se 1 (by rfl) ⟨121199, by rfl⟩ : syracuseStep 161599 = 242399) B242399
theorem B227135 : Blo 147793 227135 := bstep (se 1 (by rfl) ⟨170351, by rfl⟩ : syracuseStep 227135 = 340703) B340703
theorem B751517 : Blo 147793 751517 := bstep (se 3 (by rfl) ⟨140909, by rfl⟩ : syracuseStep 751517 = 281819) B281819
theorem B227303 : Blo 147793 227303 := bstep (se 1 (by rfl) ⟨170477, by rfl⟩ : syracuseStep 227303 = 340955) B340955
theorem B227321 : Blo 147793 227321 := bstep (se 2 (by rfl) ⟨85245, by rfl⟩ : syracuseStep 227321 = 170491) B170491
theorem B718931 : Blo 147793 718931 := bstep (se 1 (by rfl) ⟨539198, by rfl⟩ : syracuseStep 718931 = 1078397) B1078397
theorem B227423 : Blo 147793 227423 := bstep (se 1 (by rfl) ⟨170567, by rfl⟩ : syracuseStep 227423 = 341135) B341135
theorem B358543 : Blo 147793 358543 := bstep (se 1 (by rfl) ⟨268907, by rfl⟩ : syracuseStep 358543 = 537815) B537815
theorem B227483 : Blo 147793 227483 := bstep (se 1 (by rfl) ⟨170612, by rfl⟩ : syracuseStep 227483 = 341225) B341225
theorem B227519 : Blo 147793 227519 := bstep (se 1 (by rfl) ⟨170639, by rfl⟩ : syracuseStep 227519 = 341279) B341279
theorem B227561 : Blo 147793 227561 := bstep (se 2 (by rfl) ⟨85335, by rfl⟩ : syracuseStep 227561 = 170671) B170671
theorem B817451 : Blo 147793 817451 := bstep (se 1 (by rfl) ⟨613088, by rfl⟩ : syracuseStep 817451 = 1226177) B1226177
theorem B752327 : Blo 147793 752327 := bstep (se 1 (by rfl) ⟨564245, by rfl⟩ : syracuseStep 752327 = 1128491) B1128491
theorem B7076821 : Blo 147793 7076821 := bstep (se 7 (by rfl) ⟨82931, by rfl⟩ : syracuseStep 7076821 = 165863) B165863
theorem B425213 : Blo 147793 425213 := bstep (se 3 (by rfl) ⟨79727, by rfl⟩ : syracuseStep 425213 = 159455) B159455
theorem B3440015 : Blo 147793 3440015 := bstep (se 1 (by rfl) ⟨2580011, by rfl⟩ : syracuseStep 3440015 = 5160023) B5160023
theorem B181140941 : Blo 147793 181140941 := bstep (se 3 (by rfl) ⟨33963926, by rfl⟩ : syracuseStep 181140941 = 67927853) B67927853
theorem B7274099 : Blo 147793 7274099 := bstep (se 1 (by rfl) ⟨5455574, by rfl⟩ : syracuseStep 7274099 = 10911149) B10911149
theorem B1146959 : Blo 147793 1146959 := bstep (se 1 (by rfl) ⟨860219, by rfl⟩ : syracuseStep 1146959 = 1720439) B1720439
theorem B426455 : Blo 147793 426455 := bstep (se 1 (by rfl) ⟨319841, by rfl⟩ : syracuseStep 426455 = 639683) B639683
theorem B1278575 : Blo 147793 1278575 := bstep (se 1 (by rfl) ⟨958931, by rfl⟩ : syracuseStep 1278575 = 1917863) B1917863
theorem B2720783 : Blo 147793 2720783 := bstep (se 1 (by rfl) ⟨2040587, by rfl⟩ : syracuseStep 2720783 = 4081175) B4081175
theorem B264575 : Blo 147793 264575 := bstep (se 1 (by rfl) ⟨198431, by rfl⟩ : syracuseStep 264575 = 396863) B396863
theorem B724103 : Blo 147793 724103 := bstep (se 1 (by rfl) ⟨543077, by rfl⟩ : syracuseStep 724103 = 1086155) B1086155
theorem B167323 : Blo 147793 167323 := bstep (se 1 (by rfl) ⟨125492, by rfl⟩ : syracuseStep 167323 = 250985) B250985
theorem B2101297 : Blo 147793 2101297 := bstep (se 2 (by rfl) ⟨787986, by rfl⟩ : syracuseStep 2101297 = 1575973) B1575973
theorem B823457 : Blo 147793 823457 := bstep (se 2 (by rfl) ⟨308796, by rfl⟩ : syracuseStep 823457 = 617593) B617593
theorem B168295 : Blo 147793 168295 := bstep (se 1 (by rfl) ⟨126221, by rfl⟩ : syracuseStep 168295 = 252443) B252443
theorem B856439 : Blo 147793 856439 := bstep (se 1 (by rfl) ⟨642329, by rfl⟩ : syracuseStep 856439 = 1284659) B1284659
theorem B758159 : Blo 147793 758159 := bstep (se 1 (by rfl) ⟨568619, by rfl⟩ : syracuseStep 758159 = 1137239) B1137239
theorem B1282675 : Blo 147793 1282675 := bstep (se 1 (by rfl) ⟨962006, by rfl⟩ : syracuseStep 1282675 = 1924013) B1924013
theorem B332783 : Blo 147793 332783 := bstep (se 1 (by rfl) ⟨249587, by rfl⟩ : syracuseStep 332783 = 499175) B499175
theorem B168943 : Blo 147793 168943 := bstep (se 1 (by rfl) ⟨126707, by rfl⟩ : syracuseStep 168943 = 253415) B253415
theorem B2069495 : Blo 147793 2069495 := bstep (se 1 (by rfl) ⟨1552121, by rfl⟩ : syracuseStep 2069495 = 3104243) B3104243
theorem B758969 : Blo 147793 758969 := bstep (se 2 (by rfl) ⟨284613, by rfl⟩ : syracuseStep 758969 = 569227) B569227
theorem B1971611 : Blo 147793 1971611 := bstep (se 1 (by rfl) ⟨1478708, by rfl⟩ : syracuseStep 1971611 = 2957417) B2957417
theorem B333287 : Blo 147793 333287 := bstep (se 1 (by rfl) ⟨249965, by rfl⟩ : syracuseStep 333287 = 499931) B499931
theorem B169447 : Blo 147793 169447 := bstep (se 1 (by rfl) ⟨127085, by rfl⟩ : syracuseStep 169447 = 254171) B254171
theorem B1283633 : Blo 147793 1283633 := bstep (se 2 (by rfl) ⟨481362, by rfl⟩ : syracuseStep 1283633 = 962725) B962725
theorem B333449 : Blo 147793 333449 := bstep (se 2 (by rfl) ⟨125043, by rfl⟩ : syracuseStep 333449 = 250087) B250087
theorem B333467 : Blo 147793 333467 := bstep (se 1 (by rfl) ⟨250100, by rfl⟩ : syracuseStep 333467 = 500201) B500201
theorem B169627 : Blo 147793 169627 := bstep (se 1 (by rfl) ⟨127220, by rfl⟩ : syracuseStep 169627 = 254441) B254441
theorem B333665 : Blo 147793 333665 := bstep (se 2 (by rfl) ⟨125124, by rfl⟩ : syracuseStep 333665 = 250249) B250249
theorem B333863 : Blo 147793 333863 := bstep (se 1 (by rfl) ⟨250397, by rfl⟩ : syracuseStep 333863 = 500795) B500795
theorem B4135049 : Blo 147793 4135049 := bstep (se 2 (by rfl) ⟨1550643, by rfl⟩ : syracuseStep 4135049 = 3101287) B3101287
theorem B334043 : Blo 147793 334043 := bstep (se 1 (by rfl) ⟨250532, by rfl⟩ : syracuseStep 334043 = 501065) B501065
theorem B334241 : Blo 147793 334241 := bstep (se 2 (by rfl) ⟨125340, by rfl⟩ : syracuseStep 334241 = 250681) B250681
theorem B203239 : Blo 147793 203239 := bstep (se 1 (by rfl) ⟨152429, by rfl⟩ : syracuseStep 203239 = 304859) B304859
theorem B334313 : Blo 147793 334313 := bstep (se 2 (by rfl) ⟨125367, by rfl⟩ : syracuseStep 334313 = 250735) B250735
theorem B268777 : Blo 147793 268777 := bstep (se 2 (by rfl) ⟨100791, by rfl⟩ : syracuseStep 268777 = 201583) B201583
theorem B236009 : Blo 147793 236009 := bstep (se 2 (by rfl) ⟨88503, by rfl⟩ : syracuseStep 236009 = 177007) B177007
theorem B564353 : Blo 147793 564353 := bstep (se 2 (by rfl) ⟨211632, by rfl⟩ : syracuseStep 564353 = 423265) B423265
theorem B859355 : Blo 147793 859355 := bstep (se 1 (by rfl) ⟨644516, by rfl⟩ : syracuseStep 859355 = 1289033) B1289033
theorem B499553 : Blo 147793 499553 := bstep (se 2 (by rfl) ⟨187332, by rfl⟩ : syracuseStep 499553 = 374665) B374665
theorem B335771 : Blo 147793 335771 := bstep (se 1 (by rfl) ⟨251828, by rfl⟩ : syracuseStep 335771 = 503657) B503657
theorem B237559 : Blo 147793 237559 := bstep (se 1 (by rfl) ⟨178169, by rfl⟩ : syracuseStep 237559 = 356339) B356339
theorem B336185 : Blo 147793 336185 := bstep (se 2 (by rfl) ⟨126069, by rfl⟩ : syracuseStep 336185 = 252139) B252139
theorem B565643 : Blo 147793 565643 := bstep (se 1 (by rfl) ⟨424232, by rfl⟩ : syracuseStep 565643 = 848465) B848465
theorem B500471 : Blo 147793 500471 := bstep (se 1 (by rfl) ⟨375353, by rfl⟩ : syracuseStep 500471 = 750707) B750707
theorem B336671 : Blo 147793 336671 := bstep (se 1 (by rfl) ⟨252503, by rfl⟩ : syracuseStep 336671 = 505007) B505007
theorem B631975 : Blo 147793 631975 := bstep (se 1 (by rfl) ⟨473981, by rfl⟩ : syracuseStep 631975 = 947963) B947963
theorem B500903 : Blo 147793 500903 := bstep (se 1 (by rfl) ⟨375677, by rfl⟩ : syracuseStep 500903 = 751355) B751355
theorem B501011 : Blo 147793 501011 := bstep (se 1 (by rfl) ⟨375758, by rfl⟩ : syracuseStep 501011 = 751517) B751517
theorem B337481 : Blo 147793 337481 := bstep (se 2 (by rfl) ⟨126555, by rfl⟩ : syracuseStep 337481 = 253111) B253111
theorem B501551 : Blo 147793 501551 := bstep (se 1 (by rfl) ⟨376163, by rfl⟩ : syracuseStep 501551 = 752327) B752327
theorem B337913 : Blo 147793 337913 := bstep (se 2 (by rfl) ⟨126717, by rfl⟩ : syracuseStep 337913 = 253435) B253435
theorem B337967 : Blo 147793 337967 := bstep (se 1 (by rfl) ⟨253475, by rfl⟩ : syracuseStep 337967 = 506951) B506951
theorem B338003 : Blo 147793 338003 := bstep (se 1 (by rfl) ⟨253502, by rfl⟩ : syracuseStep 338003 = 507005) B507005
theorem B764153 : Blo 147793 764153 := bstep (se 2 (by rfl) ⟨286557, by rfl⟩ : syracuseStep 764153 = 573115) B573115
theorem B338183 : Blo 147793 338183 := bstep (se 1 (by rfl) ⟨253637, by rfl⟩ : syracuseStep 338183 = 507275) B507275
theorem B120760627 : Blo 147793 120760627 := bstep (se 1 (by rfl) ⟨90570470, by rfl⟩ : syracuseStep 120760627 = 181140941) B181140941
theorem B2173241 : Blo 147793 2173241 := bstep (se 2 (by rfl) ⟨814965, by rfl⟩ : syracuseStep 2173241 = 1629931) B1629931
theorem B862589 : Blo 147793 862589 := bstep (se 3 (by rfl) ⟨161735, by rfl⟩ : syracuseStep 862589 = 323471) B323471
theorem B338489 : Blo 147793 338489 := bstep (se 2 (by rfl) ⟨126933, by rfl⟩ : syracuseStep 338489 = 253867) B253867
theorem B240713 : Blo 147793 240713 := bstep (se 2 (by rfl) ⟨90267, by rfl⟩ : syracuseStep 240713 = 180535) B180535
theorem B4304015 : Blo 147793 4304015 := bstep (se 1 (by rfl) ⟨3228011, by rfl⟩ : syracuseStep 4304015 = 6456023) B6456023
theorem B1125575 : Blo 147793 1125575 := bstep (se 1 (by rfl) ⟨844181, by rfl⟩ : syracuseStep 1125575 = 1688363) B1688363
theorem B339209 : Blo 147793 339209 := bstep (se 2 (by rfl) ⟨127203, by rfl⟩ : syracuseStep 339209 = 254407) B254407
theorem B1945133 : Blo 147793 1945133 := bstep (se 3 (by rfl) ⟨364712, by rfl⟩ : syracuseStep 1945133 = 729425) B729425
theorem B699967 : Blo 147793 699967 := bstep (se 1 (by rfl) ⟨524975, by rfl⟩ : syracuseStep 699967 = 1049951) B1049951
theorem B569015 : Blo 147793 569015 := bstep (se 1 (by rfl) ⟨426761, by rfl⟩ : syracuseStep 569015 = 853523) B853523
theorem B1060547 : Blo 147793 1060547 := bstep (se 1 (by rfl) ⟨795410, by rfl⟩ : syracuseStep 1060547 = 1590821) B1590821
theorem B1912531 : Blo 147793 1912531 := bstep (se 1 (by rfl) ⟨1434398, by rfl⟩ : syracuseStep 1912531 = 2868797) B2868797
theorem B569213 : Blo 147793 569213 := bstep (se 3 (by rfl) ⟨106727, by rfl⟩ : syracuseStep 569213 = 213455) B213455
theorem B569483 : Blo 147793 569483 := bstep (se 1 (by rfl) ⟨427112, by rfl⟩ : syracuseStep 569483 = 854225) B854225
theorem B536807 : Blo 147793 536807 := bstep (se 1 (by rfl) ⟨402605, by rfl⟩ : syracuseStep 536807 = 805211) B805211
theorem B340199 : Blo 147793 340199 := bstep (se 1 (by rfl) ⟨255149, by rfl⟩ : syracuseStep 340199 = 510299) B510299
theorem B340379 : Blo 147793 340379 := bstep (se 1 (by rfl) ⟨255284, by rfl⟩ : syracuseStep 340379 = 510569) B510569
theorem B438841 : Blo 147793 438841 := bstep (se 2 (by rfl) ⟨164565, by rfl⟩ : syracuseStep 438841 = 329131) B329131
theorem B570017 : Blo 147793 570017 := bstep (se 2 (by rfl) ⟨213756, by rfl⟩ : syracuseStep 570017 = 427513) B427513
theorem B1159901 : Blo 147793 1159901 := bstep (se 3 (by rfl) ⟨217481, by rfl⟩ : syracuseStep 1159901 = 434963) B434963
theorem B341063 : Blo 147793 341063 := bstep (se 1 (by rfl) ⟨255797, by rfl⟩ : syracuseStep 341063 = 511595) B511595
theorem B570473 : Blo 147793 570473 := bstep (se 2 (by rfl) ⟨213927, by rfl⟩ : syracuseStep 570473 = 427855) B427855
theorem B341243 : Blo 147793 341243 := bstep (se 1 (by rfl) ⟨255932, by rfl⟩ : syracuseStep 341243 = 511865) B511865
theorem B341459 : Blo 147793 341459 := bstep (se 1 (by rfl) ⟨256094, by rfl⟩ : syracuseStep 341459 = 512189) B512189
theorem B177647 : Blo 147793 177647 := bstep (se 1 (by rfl) ⟨133235, by rfl⟩ : syracuseStep 177647 = 266471) B266471
theorem B570989 : Blo 147793 570989 := bstep (se 3 (by rfl) ⟨107060, by rfl⟩ : syracuseStep 570989 = 214121) B214121
theorem B964649 : Blo 147793 964649 := bstep (se 2 (by rfl) ⟨361743, by rfl⟩ : syracuseStep 964649 = 723487) B723487
theorem B768041 : Blo 147793 768041 := bstep (se 2 (by rfl) ⟨288015, by rfl⟩ : syracuseStep 768041 = 576031) B576031
theorem B506087 : Blo 147793 506087 := bstep (se 1 (by rfl) ⟨379565, by rfl⟩ : syracuseStep 506087 = 759131) B759131
theorem B604523 : Blo 147793 604523 := bstep (se 1 (by rfl) ⟨453392, by rfl⟩ : syracuseStep 604523 = 906785) B906785
theorem B637307 : Blo 147793 637307 := bstep (se 1 (by rfl) ⟨477980, by rfl⟩ : syracuseStep 637307 = 955961) B955961
theorem B375455 : Blo 147793 375455 := bstep (se 1 (by rfl) ⟨281591, by rfl⟩ : syracuseStep 375455 = 563183) B563183
theorem B638057 : Blo 147793 638057 := bstep (se 2 (by rfl) ⟨239271, by rfl⟩ : syracuseStep 638057 = 478543) B478543
theorem B572615 : Blo 147793 572615 := bstep (se 1 (by rfl) ⟨429461, by rfl⟩ : syracuseStep 572615 = 858923) B858923
theorem B376427 : Blo 147793 376427 := bstep (se 1 (by rfl) ⟨282320, by rfl⟩ : syracuseStep 376427 = 564641) B564641
theorem B2571911 : Blo 147793 2571911 := bstep (se 1 (by rfl) ⟨1928933, by rfl⟩ : syracuseStep 2571911 = 3857867) B3857867
theorem B507815 : Blo 147793 507815 := bstep (se 1 (by rfl) ⟨380861, by rfl⟩ : syracuseStep 507815 = 761723) B761723
theorem B180415 : Blo 147793 180415 := bstep (se 1 (by rfl) ⟨135311, by rfl⟩ : syracuseStep 180415 = 270623) B270623
theorem B409835 : Blo 147793 409835 := bstep (se 1 (by rfl) ⟨307376, by rfl⟩ : syracuseStep 409835 = 614753) B614753
theorem B508139 : Blo 147793 508139 := bstep (se 1 (by rfl) ⟨381104, by rfl⟩ : syracuseStep 508139 = 762209) B762209
theorem B147995 : Blo 147793 147995 := bstep (se 1 (by rfl) ⟨110996, by rfl⟩ : syracuseStep 147995 = 221993) B221993
theorem B147999 : Blo 147793 147999 := bstep (se 1 (by rfl) ⟨110999, by rfl⟩ : syracuseStep 147999 = 221999) B221999
theorem B148079 : Blo 147793 148079 := bstep (se 1 (by rfl) ⟨111059, by rfl⟩ : syracuseStep 148079 = 222119) B222119
theorem B148135 : Blo 147793 148135 := bstep (se 1 (by rfl) ⟨111101, by rfl⟩ : syracuseStep 148135 = 222203) B222203
theorem B377531 : Blo 147793 377531 := bstep (se 1 (by rfl) ⟨283148, by rfl⟩ : syracuseStep 377531 = 566297) B566297
theorem B148175 : Blo 147793 148175 := bstep (se 1 (by rfl) ⟨111131, by rfl⟩ : syracuseStep 148175 = 222263) B222263
theorem B148255 : Blo 147793 148255 := bstep (se 1 (by rfl) ⟨111191, by rfl⟩ : syracuseStep 148255 = 222383) B222383
theorem B1131407 : Blo 147793 1131407 := bstep (se 1 (by rfl) ⟨848555, by rfl⟩ : syracuseStep 1131407 = 1697111) B1697111
theorem B148527 : Blo 147793 148527 := bstep (se 1 (by rfl) ⟨111395, by rfl⟩ : syracuseStep 148527 = 222791) B222791
theorem B148591 : Blo 147793 148591 := bstep (se 1 (by rfl) ⟨111443, by rfl⟩ : syracuseStep 148591 = 222887) B222887
theorem B148647 : Blo 147793 148647 := bstep (se 1 (by rfl) ⟨111485, by rfl⟩ : syracuseStep 148647 = 222971) B222971
theorem B148671 : Blo 147793 148671 := bstep (se 1 (by rfl) ⟨111503, by rfl⟩ : syracuseStep 148671 = 223007) B223007
theorem B378047 : Blo 147793 378047 := bstep (se 1 (by rfl) ⟨283535, by rfl⟩ : syracuseStep 378047 = 567071) B567071
theorem B148703 : Blo 147793 148703 := bstep (se 1 (by rfl) ⟨111527, by rfl⟩ : syracuseStep 148703 = 223055) B223055
theorem B148783 : Blo 147793 148783 := bstep (se 1 (by rfl) ⟨111587, by rfl⟩ : syracuseStep 148783 = 223175) B223175
theorem B574877 : Blo 147793 574877 := bstep (se 3 (by rfl) ⟨107789, by rfl⟩ : syracuseStep 574877 = 215579) B215579
theorem B149019 : Blo 147793 149019 := bstep (se 1 (by rfl) ⟨111764, by rfl⟩ : syracuseStep 149019 = 223529) B223529
theorem B149023 : Blo 147793 149023 := bstep (se 1 (by rfl) ⟨111767, by rfl⟩ : syracuseStep 149023 = 223535) B223535
theorem B149183 : Blo 147793 149183 := bstep (se 1 (by rfl) ⟨111887, by rfl⟩ : syracuseStep 149183 = 223775) B223775
theorem B149439 : Blo 147793 149439 := bstep (se 1 (by rfl) ⟨112079, by rfl⟩ : syracuseStep 149439 = 224159) B224159
theorem B149471 : Blo 147793 149471 := bstep (se 1 (by rfl) ⟨112103, by rfl⟩ : syracuseStep 149471 = 224207) B224207
theorem B149531 : Blo 147793 149531 := bstep (se 1 (by rfl) ⟨112148, by rfl⟩ : syracuseStep 149531 = 224297) B224297
theorem B182299 : Blo 147793 182299 := bstep (se 1 (by rfl) ⟨136724, by rfl⟩ : syracuseStep 182299 = 273449) B273449
theorem B149535 : Blo 147793 149535 := bstep (se 1 (by rfl) ⟨112151, by rfl⟩ : syracuseStep 149535 = 224303) B224303
theorem B149551 : Blo 147793 149551 := bstep (se 1 (by rfl) ⟨112163, by rfl⟩ : syracuseStep 149551 = 224327) B224327
theorem B30951517 : Blo 147793 30951517 := bstep (se 3 (by rfl) ⟨5803409, by rfl⟩ : syracuseStep 30951517 = 11606819) B11606819
theorem B149727 : Blo 147793 149727 := bstep (se 1 (by rfl) ⟨112295, by rfl⟩ : syracuseStep 149727 = 224591) B224591
theorem B2148605 : Blo 147793 2148605 := bstep (se 3 (by rfl) ⟨402863, by rfl⟩ : syracuseStep 2148605 = 805727) B805727
theorem B149787 : Blo 147793 149787 := bstep (se 1 (by rfl) ⟨112340, by rfl⟩ : syracuseStep 149787 = 224681) B224681
theorem B870763 : Blo 147793 870763 := bstep (se 1 (by rfl) ⟨653072, by rfl⟩ : syracuseStep 870763 = 1306145) B1306145
theorem B969083 : Blo 147793 969083 := bstep (se 1 (by rfl) ⟨726812, by rfl⟩ : syracuseStep 969083 = 1453625) B1453625
theorem B149887 : Blo 147793 149887 := bstep (se 1 (by rfl) ⟨112415, by rfl⟩ : syracuseStep 149887 = 224831) B224831
theorem B215465 : Blo 147793 215465 := bstep (se 2 (by rfl) ⟨80799, by rfl⟩ : syracuseStep 215465 = 161599) B161599
theorem B150063 : Blo 147793 150063 := bstep (se 1 (by rfl) ⟨112547, by rfl⟩ : syracuseStep 150063 = 225095) B225095
theorem B150119 : Blo 147793 150119 := bstep (se 1 (by rfl) ⟨112589, by rfl⟩ : syracuseStep 150119 = 225179) B225179
theorem B478057 : Blo 147793 478057 := bstep (se 2 (by rfl) ⟨179271, by rfl⟩ : syracuseStep 478057 = 358543) B358543
theorem B150495 : Blo 147793 150495 := bstep (se 1 (by rfl) ⟨112871, by rfl⟩ : syracuseStep 150495 = 225743) B225743
theorem B281569 : Blo 147793 281569 := bstep (se 2 (by rfl) ⟨105588, by rfl⟩ : syracuseStep 281569 = 211177) B211177
theorem B150523 : Blo 147793 150523 := bstep (se 1 (by rfl) ⟨112892, by rfl⟩ : syracuseStep 150523 = 225785) B225785
theorem B150591 : Blo 147793 150591 := bstep (se 1 (by rfl) ⟨112943, by rfl⟩ : syracuseStep 150591 = 225887) B225887
theorem B4803731 : Blo 147793 4803731 := bstep (se 1 (by rfl) ⟨3602798, by rfl⟩ : syracuseStep 4803731 = 7205597) B7205597
theorem B3099971 : Blo 147793 3099971 := bstep (se 1 (by rfl) ⟨2324978, by rfl⟩ : syracuseStep 3099971 = 4649957) B4649957
theorem B150911 : Blo 147793 150911 := bstep (se 1 (by rfl) ⟨113183, by rfl⟩ : syracuseStep 150911 = 226367) B226367
theorem B150939 : Blo 147793 150939 := bstep (se 1 (by rfl) ⟨113204, by rfl⟩ : syracuseStep 150939 = 226409) B226409
theorem B151007 : Blo 147793 151007 := bstep (se 1 (by rfl) ⟨113255, by rfl⟩ : syracuseStep 151007 = 226511) B226511
theorem B151143 : Blo 147793 151143 := bstep (se 1 (by rfl) ⟨113357, by rfl⟩ : syracuseStep 151143 = 226715) B226715
theorem B151291 : Blo 147793 151291 := bstep (se 1 (by rfl) ⟨113468, by rfl⟩ : syracuseStep 151291 = 226937) B226937
theorem B151359 : Blo 147793 151359 := bstep (se 1 (by rfl) ⟨113519, by rfl⟩ : syracuseStep 151359 = 227039) B227039
theorem B151423 : Blo 147793 151423 := bstep (se 1 (by rfl) ⟨113567, by rfl⟩ : syracuseStep 151423 = 227135) B227135
theorem B151535 : Blo 147793 151535 := bstep (se 1 (by rfl) ⟨113651, by rfl⟩ : syracuseStep 151535 = 227303) B227303
theorem B249851 : Blo 147793 249851 := bstep (se 1 (by rfl) ⟨187388, by rfl⟩ : syracuseStep 249851 = 374777) B374777
theorem B151547 : Blo 147793 151547 := bstep (se 1 (by rfl) ⟨113660, by rfl⟩ : syracuseStep 151547 = 227321) B227321
theorem B479287 : Blo 147793 479287 := bstep (se 1 (by rfl) ⟨359465, by rfl⟩ : syracuseStep 479287 = 718931) B718931
theorem B380983 : Blo 147793 380983 := bstep (se 1 (by rfl) ⟨285737, by rfl⟩ : syracuseStep 380983 = 571475) B571475
theorem B151615 : Blo 147793 151615 := bstep (se 1 (by rfl) ⟨113711, by rfl⟩ : syracuseStep 151615 = 227423) B227423
theorem B249959 : Blo 147793 249959 := bstep (se 1 (by rfl) ⟨187469, by rfl⟩ : syracuseStep 249959 = 374939) B374939
theorem B151655 : Blo 147793 151655 := bstep (se 1 (by rfl) ⟨113741, by rfl⟩ : syracuseStep 151655 = 227483) B227483
theorem B151679 : Blo 147793 151679 := bstep (se 1 (by rfl) ⟨113759, by rfl⟩ : syracuseStep 151679 = 227519) B227519
theorem B151707 : Blo 147793 151707 := bstep (se 1 (by rfl) ⟨113780, by rfl⟩ : syracuseStep 151707 = 227561) B227561
theorem B544967 : Blo 147793 544967 := bstep (se 1 (by rfl) ⟨408725, by rfl⟩ : syracuseStep 544967 = 817451) B817451
theorem B512243 : Blo 147793 512243 := bstep (se 1 (by rfl) ⟨384182, by rfl⟩ : syracuseStep 512243 = 768365) B768365
theorem B1429751 : Blo 147793 1429751 := bstep (se 1 (by rfl) ⟨1072313, by rfl⟩ : syracuseStep 1429751 = 2144627) B2144627
theorem B381307 : Blo 147793 381307 := bstep (se 1 (by rfl) ⟨285980, by rfl⟩ : syracuseStep 381307 = 571961) B571961
theorem B283475 : Blo 147793 283475 := bstep (se 1 (by rfl) ⟨212606, by rfl⟩ : syracuseStep 283475 = 425213) B425213
theorem B250715 : Blo 147793 250715 := bstep (se 1 (by rfl) ⟨188036, by rfl⟩ : syracuseStep 250715 = 376073) B376073
theorem B578459 : Blo 147793 578459 := bstep (se 1 (by rfl) ⟨433844, by rfl⟩ : syracuseStep 578459 = 867689) B867689
theorem B775241 : Blo 147793 775241 := bstep (se 2 (by rfl) ⟨290715, by rfl⟩ : syracuseStep 775241 = 581431) B581431
theorem B1135781 : Blo 147793 1135781 := bstep (se 4 (by rfl) ⟨106479, by rfl⟩ : syracuseStep 1135781 = 212959) B212959
theorem B2086193 : Blo 147793 2086193 := bstep (se 2 (by rfl) ⟨782322, by rfl⟩ : syracuseStep 2086193 = 1564645) B1564645
theorem B284143 : Blo 147793 284143 := bstep (se 1 (by rfl) ⟨213107, by rfl⟩ : syracuseStep 284143 = 426215) B426215
theorem B284447 : Blo 147793 284447 := bstep (se 1 (by rfl) ⟨213335, by rfl⟩ : syracuseStep 284447 = 426671) B426671
theorem B481619 : Blo 147793 481619 := bstep (se 1 (by rfl) ⟨361214, by rfl⟩ : syracuseStep 481619 = 722429) B722429
theorem B383393 : Blo 147793 383393 := bstep (se 2 (by rfl) ⟨143772, by rfl⟩ : syracuseStep 383393 = 287545) B287545
theorem B318953 : Blo 147793 318953 := bstep (se 2 (by rfl) ⟨119607, by rfl⟩ : syracuseStep 318953 = 239215) B239215
theorem B319097 : Blo 147793 319097 := bstep (se 2 (by rfl) ⟨119661, by rfl⟩ : syracuseStep 319097 = 239323) B239323
theorem B1630135 : Blo 147793 1630135 := bstep (se 1 (by rfl) ⟨1222601, by rfl⟩ : syracuseStep 1630135 = 2445203) B2445203
theorem B1269827 : Blo 147793 1269827 := bstep (se 1 (by rfl) ⟨952370, by rfl⟩ : syracuseStep 1269827 = 1904741) B1904741
theorem B2613383 : Blo 147793 2613383 := bstep (se 1 (by rfl) ⟨1960037, by rfl⟩ : syracuseStep 2613383 = 3920075) B3920075
theorem B385337 : Blo 147793 385337 := bstep (se 2 (by rfl) ⟨144501, by rfl⟩ : syracuseStep 385337 = 289003) B289003
theorem B221723 : Blo 147793 221723 := bstep (se 1 (by rfl) ⟨166292, by rfl⟩ : syracuseStep 221723 = 332585) B332585
theorem B2908709 : Blo 147793 2908709 := bstep (se 4 (by rfl) ⟨272691, by rfl⟩ : syracuseStep 2908709 = 545383) B545383
theorem B221903 : Blo 147793 221903 := bstep (se 1 (by rfl) ⟨166427, by rfl⟩ : syracuseStep 221903 = 332855) B332855
theorem B221915 : Blo 147793 221915 := bstep (se 1 (by rfl) ⟨166436, by rfl⟩ : syracuseStep 221915 = 332873) B332873
theorem B222329 : Blo 147793 222329 := bstep (se 2 (by rfl) ⟨83373, by rfl⟩ : syracuseStep 222329 = 166747) B166747
theorem B255143 : Blo 147793 255143 := bstep (se 1 (by rfl) ⟨191357, by rfl⟩ : syracuseStep 255143 = 382715) B382715
theorem B13297097 : Blo 147793 13297097 := bstep (se 2 (by rfl) ⟨4986411, by rfl⟩ : syracuseStep 13297097 = 9972823) B9972823
theorem B321097 : Blo 147793 321097 := bstep (se 2 (by rfl) ⟨120411, by rfl⟩ : syracuseStep 321097 = 240823) B240823
theorem B5826167 : Blo 147793 5826167 := bstep (se 1 (by rfl) ⟨4369625, by rfl⟩ : syracuseStep 5826167 = 8739251) B8739251
theorem B9791165 : Blo 147793 9791165 := bstep (se 3 (by rfl) ⟨1835843, by rfl⟩ : syracuseStep 9791165 = 3671687) B3671687
theorem B2746075 : Blo 147793 2746075 := bstep (se 1 (by rfl) ⟨2059556, by rfl⟩ : syracuseStep 2746075 = 4119113) B4119113
theorem B255899 : Blo 147793 255899 := bstep (se 1 (by rfl) ⟨191924, by rfl⟩ : syracuseStep 255899 = 383849) B383849
theorem B223199 : Blo 147793 223199 := bstep (se 1 (by rfl) ⟨167399, by rfl⟩ : syracuseStep 223199 = 334799) B334799
theorem B223211 : Blo 147793 223211 := bstep (se 1 (by rfl) ⟨167408, by rfl⟩ : syracuseStep 223211 = 334817) B334817
theorem B714739 : Blo 147793 714739 := bstep (se 1 (by rfl) ⟨536054, by rfl⟩ : syracuseStep 714739 = 1072109) B1072109
theorem B223259 : Blo 147793 223259 := bstep (se 1 (by rfl) ⟨167444, by rfl⟩ : syracuseStep 223259 = 334889) B334889
theorem B256027 : Blo 147793 256027 := bstep (se 1 (by rfl) ⟨192020, by rfl⟩ : syracuseStep 256027 = 384041) B384041
theorem B190775 : Blo 147793 190775 := bstep (se 1 (by rfl) ⟨143081, by rfl⟩ : syracuseStep 190775 = 286163) B286163
theorem B223625 : Blo 147793 223625 := bstep (se 2 (by rfl) ⟨83859, by rfl⟩ : syracuseStep 223625 = 167719) B167719
theorem B6547877 : Blo 147793 6547877 := bstep (se 4 (by rfl) ⟨613863, by rfl⟩ : syracuseStep 6547877 = 1227727) B1227727
theorem B224567 : Blo 147793 224567 := bstep (se 1 (by rfl) ⟨168425, by rfl⟩ : syracuseStep 224567 = 336851) B336851
theorem B191899 : Blo 147793 191899 := bstep (se 1 (by rfl) ⟨143924, by rfl⟩ : syracuseStep 191899 = 287849) B287849
theorem B224735 : Blo 147793 224735 := bstep (se 1 (by rfl) ⟨168551, by rfl⟩ : syracuseStep 224735 = 337103) B337103
theorem B224951 : Blo 147793 224951 := bstep (se 1 (by rfl) ⟨168713, by rfl⟩ : syracuseStep 224951 = 337427) B337427
theorem B225161 : Blo 147793 225161 := bstep (se 2 (by rfl) ⟨84435, by rfl⟩ : syracuseStep 225161 = 168871) B168871
theorem B225407 : Blo 147793 225407 := bstep (se 1 (by rfl) ⟨169055, by rfl⟩ : syracuseStep 225407 = 338111) B338111
theorem B159899 : Blo 147793 159899 := bstep (se 1 (by rfl) ⟨119924, by rfl⟩ : syracuseStep 159899 = 239849) B239849
theorem B2748809 : Blo 147793 2748809 := bstep (se 2 (by rfl) ⟨1030803, by rfl⟩ : syracuseStep 2748809 = 2061607) B2061607
theorem B2585033 : Blo 147793 2585033 := bstep (se 2 (by rfl) ⟨969387, by rfl⟩ : syracuseStep 2585033 = 1938775) B1938775
theorem B226043 : Blo 147793 226043 := bstep (se 1 (by rfl) ⟨169532, by rfl⟩ : syracuseStep 226043 = 339065) B339065
theorem B1110941 : Blo 147793 1110941 := bstep (se 3 (by rfl) ⟨208301, by rfl⟩ : syracuseStep 1110941 = 416603) B416603
theorem B226487 : Blo 147793 226487 := bstep (se 1 (by rfl) ⟨169865, by rfl⟩ : syracuseStep 226487 = 339731) B339731
theorem B226727 : Blo 147793 226727 := bstep (se 1 (by rfl) ⟨170045, by rfl⟩ : syracuseStep 226727 = 340091) B340091
theorem B226907 : Blo 147793 226907 := bstep (se 1 (by rfl) ⟨170180, by rfl⟩ : syracuseStep 226907 = 340361) B340361
theorem B1144529 : Blo 147793 1144529 := bstep (se 2 (by rfl) ⟨429198, by rfl⟩ : syracuseStep 1144529 = 858397) B858397
theorem B227369 : Blo 147793 227369 := bstep (se 2 (by rfl) ⟨85263, by rfl⟩ : syracuseStep 227369 = 170527) B170527
theorem B227399 : Blo 147793 227399 := bstep (se 1 (by rfl) ⟨170549, by rfl⟩ : syracuseStep 227399 = 341099) B341099
theorem B2717873 : Blo 147793 2717873 := bstep (se 2 (by rfl) ⟨1019202, by rfl⟩ : syracuseStep 2717873 = 2038405) B2038405
theorem B1145015 : Blo 147793 1145015 := bstep (se 1 (by rfl) ⟨858761, by rfl⟩ : syracuseStep 1145015 = 1717523) B1717523
theorem B9435761 : Blo 147793 9435761 := bstep (se 2 (by rfl) ⟨3538410, by rfl⟩ : syracuseStep 9435761 = 7076821) B7076821
theorem B1145501 : Blo 147793 1145501 := bstep (se 3 (by rfl) ⟨214781, by rfl⟩ : syracuseStep 1145501 = 429563) B429563
theorem B687095 : Blo 147793 687095 := bstep (se 1 (by rfl) ⟨515321, by rfl⟩ : syracuseStep 687095 = 1030643) B1030643
theorem B5144057 : Blo 147793 5144057 := bstep (se 2 (by rfl) ⟨1929021, by rfl⟩ : syracuseStep 5144057 = 3858043) B3858043
theorem B2293343 : Blo 147793 2293343 := bstep (se 1 (by rfl) ⟨1720007, by rfl⟩ : syracuseStep 2293343 = 3440015) B3440015
theorem B4849399 : Blo 147793 4849399 := bstep (se 1 (by rfl) ⟨3637049, by rfl⟩ : syracuseStep 4849399 = 7274099) B7274099
theorem B2424653 : Blo 147793 2424653 := bstep (se 3 (by rfl) ⟨454622, by rfl⟩ : syracuseStep 2424653 = 909245) B909245
theorem B426397 : Blo 147793 426397 := bstep (se 3 (by rfl) ⟨79949, by rfl⟩ : syracuseStep 426397 = 159899) B159899
theorem B852383 : Blo 147793 852383 := bstep (se 1 (by rfl) ⟨639287, by rfl⟩ : syracuseStep 852383 = 1278575) B1278575
theorem B2195885 : Blo 147793 2195885 := bstep (se 3 (by rfl) ⟨411728, by rfl⟩ : syracuseStep 2195885 = 823457) B823457
theorem B754271 : Blo 147793 754271 := bstep (se 1 (by rfl) ⟨565703, by rfl⟩ : syracuseStep 754271 = 1131407) B1131407
theorem B428129 : Blo 147793 428129 := bstep (se 2 (by rfl) ⟨160548, by rfl⟩ : syracuseStep 428129 = 321097) B321097
theorem B2066647 : Blo 147793 2066647 := bstep (se 1 (by rfl) ⟨1549985, by rfl⟩ : syracuseStep 2066647 = 3099971) B3099971
theorem B1542557 : Blo 147793 1542557 := bstep (se 3 (by rfl) ⟨289229, by rfl⟩ : syracuseStep 1542557 = 578459) B578459
theorem B1083941 : Blo 147793 1083941 := bstep (se 4 (by rfl) ⟨101619, by rfl⟩ : syracuseStep 1083941 = 203239) B203239
theorem B952985 : Blo 147793 952985 := bstep (se 2 (by rfl) ⟨357369, by rfl⟩ : syracuseStep 952985 = 714739) B714739
theorem B166567 : Blo 147793 166567 := bstep (se 1 (by rfl) ⟨124925, by rfl⟩ : syracuseStep 166567 = 249851) B249851
theorem B166639 : Blo 147793 166639 := bstep (se 1 (by rfl) ⟨124979, by rfl⟩ : syracuseStep 166639 = 249959) B249959
theorem B363311 : Blo 147793 363311 := bstep (se 1 (by rfl) ⟨272483, by rfl⟩ : syracuseStep 363311 = 544967) B544967
theorem B953167 : Blo 147793 953167 := bstep (se 1 (by rfl) ⟨714875, by rfl⟩ : syracuseStep 953167 = 1429751) B1429751
theorem B199849 : Blo 147793 199849 := bstep (se 2 (by rfl) ⟨74943, by rfl⟩ : syracuseStep 199849 = 149887) B149887
theorem B167143 : Blo 147793 167143 := bstep (se 1 (by rfl) ⟨125357, by rfl⟩ : syracuseStep 167143 = 250715) B250715
theorem B1379663 : Blo 147793 1379663 := bstep (se 1 (by rfl) ⟨1034747, by rfl⟩ : syracuseStep 1379663 = 2069495) B2069495
theorem B757187 : Blo 147793 757187 := bstep (se 1 (by rfl) ⟨567890, by rfl⟩ : syracuseStep 757187 = 1135781) B1135781
theorem B1314407 : Blo 147793 1314407 := bstep (se 1 (by rfl) ⟨985805, by rfl⟩ : syracuseStep 1314407 = 1971611) B1971611
theorem B855755 : Blo 147793 855755 := bstep (se 1 (by rfl) ⟨641816, by rfl⟩ : syracuseStep 855755 = 1283633) B1283633
theorem B2756699 : Blo 147793 2756699 := bstep (se 1 (by rfl) ⟨2067524, by rfl⟩ : syracuseStep 2756699 = 4135049) B4135049
theorem B333035 : Blo 147793 333035 := bstep (se 1 (by rfl) ⟨249776, by rfl⟩ : syracuseStep 333035 = 499553) B499553
theorem B1742255 : Blo 147793 1742255 := bstep (se 1 (by rfl) ⟨1306691, by rfl⟩ : syracuseStep 1742255 = 2613383) B2613383
theorem B1939139 : Blo 147793 1939139 := bstep (se 1 (by rfl) ⟨1454354, by rfl⟩ : syracuseStep 1939139 = 2908709) B2908709
theorem B333647 : Blo 147793 333647 := bstep (se 1 (by rfl) ⟨250235, by rfl⟩ : syracuseStep 333647 = 500471) B500471
theorem B333935 : Blo 147793 333935 := bstep (se 1 (by rfl) ⟨250451, by rfl⟩ : syracuseStep 333935 = 500903) B500903
theorem B170095 : Blo 147793 170095 := bstep (se 1 (by rfl) ⟨127571, by rfl⟩ : syracuseStep 170095 = 255143) B255143
theorem B1710233 : Blo 147793 1710233 := bstep (se 2 (by rfl) ⟨641337, by rfl⟩ : syracuseStep 1710233 = 1282675) B1282675
theorem B334007 : Blo 147793 334007 := bstep (se 1 (by rfl) ⟨250505, by rfl⟩ : syracuseStep 334007 = 501011) B501011
theorem B1612061 : Blo 147793 1612061 := bstep (se 3 (by rfl) ⟨302261, by rfl⟩ : syracuseStep 1612061 = 604523) B604523
theorem B334367 : Blo 147793 334367 := bstep (se 1 (by rfl) ⟨250775, by rfl⟩ : syracuseStep 334367 = 501551) B501551
theorem B170599 : Blo 147793 170599 := bstep (se 1 (by rfl) ⟨127949, by rfl⟩ : syracuseStep 170599 = 255899) B255899
theorem B4365251 : Blo 147793 4365251 := bstep (se 1 (by rfl) ⟨3273938, by rfl⟩ : syracuseStep 4365251 = 6547877) B6547877
theorem B763019 : Blo 147793 763019 := bstep (se 1 (by rfl) ⟨572264, by rfl⟩ : syracuseStep 763019 = 1144529) B1144529
theorem B1811915 : Blo 147793 1811915 := bstep (se 1 (by rfl) ⟨1358936, by rfl⟩ : syracuseStep 1811915 = 2717873) B2717873
theorem B763343 : Blo 147793 763343 := bstep (se 1 (by rfl) ⟨572507, by rfl⟩ : syracuseStep 763343 = 1145015) B1145015
theorem B337391 : Blo 147793 337391 := bstep (se 1 (by rfl) ⟨253043, by rfl⟩ : syracuseStep 337391 = 506087) B506087
theorem B763667 : Blo 147793 763667 := bstep (se 1 (by rfl) ⟨572750, by rfl⟩ : syracuseStep 763667 = 1145501) B1145501
theorem B2828125 : Blo 147793 2828125 := bstep (se 3 (by rfl) ⟨530273, by rfl⟩ : syracuseStep 2828125 = 1060547) B1060547
theorem B6465865 : Blo 147793 6465865 := bstep (se 2 (by rfl) ⟨2424699, by rfl⟩ : syracuseStep 6465865 = 4849399) B4849399
theorem B1714607 : Blo 147793 1714607 := bstep (se 1 (by rfl) ⟨1285955, by rfl⟩ : syracuseStep 1714607 = 2571911) B2571911
theorem B1616435 : Blo 147793 1616435 := bstep (se 1 (by rfl) ⟨1212326, by rfl⟩ : syracuseStep 1616435 = 2424653) B2424653
theorem B2173513 : Blo 147793 2173513 := bstep (se 2 (by rfl) ⟨815067, by rfl⟩ : syracuseStep 2173513 = 1630135) B1630135
theorem B338543 : Blo 147793 338543 := bstep (se 1 (by rfl) ⟨253907, by rfl⟩ : syracuseStep 338543 = 507815) B507815
theorem B764639 : Blo 147793 764639 := bstep (se 1 (by rfl) ⟨573479, by rfl⟩ : syracuseStep 764639 = 1146959) B1146959
theorem B273223 : Blo 147793 273223 := bstep (se 1 (by rfl) ⟨204917, by rfl⟩ : syracuseStep 273223 = 409835) B409835
theorem B338759 : Blo 147793 338759 := bstep (se 1 (by rfl) ⟨254069, by rfl⟩ : syracuseStep 338759 = 508139) B508139
theorem B240553 : Blo 147793 240553 := bstep (se 2 (by rfl) ⟨90207, by rfl⟩ : syracuseStep 240553 = 180415) B180415
theorem B1813855 : Blo 147793 1813855 := bstep (se 1 (by rfl) ⟨1360391, by rfl⟩ : syracuseStep 1813855 = 2720783) B2720783
theorem B176383 : Blo 147793 176383 := bstep (se 1 (by rfl) ⟨132287, by rfl⟩ : syracuseStep 176383 = 264575) B264575
theorem B341369 : Blo 147793 341369 := bstep (se 2 (by rfl) ⟨128013, by rfl⟩ : syracuseStep 341369 = 256027) B256027
theorem B243065 : Blo 147793 243065 := bstep (se 2 (by rfl) ⟨91149, by rfl⟩ : syracuseStep 243065 = 182299) B182299
theorem B41268689 : Blo 147793 41268689 := bstep (se 2 (by rfl) ⟨15475758, by rfl⟩ : syracuseStep 41268689 = 30951517) B30951517
theorem B341495 : Blo 147793 341495 := bstep (se 1 (by rfl) ⟨256121, by rfl⟩ : syracuseStep 341495 = 512243) B512243
theorem B570959 : Blo 147793 570959 := bstep (se 1 (by rfl) ⟨428219, by rfl⟩ : syracuseStep 570959 = 856439) B856439
theorem B505439 : Blo 147793 505439 := bstep (se 1 (by rfl) ⟨379079, by rfl⟩ : syracuseStep 505439 = 758159) B758159
theorem B2340485 : Blo 147793 2340485 := bstep (se 4 (by rfl) ⟨219420, by rfl⟩ : syracuseStep 2340485 = 438841) B438841
theorem B1161017 : Blo 147793 1161017 := bstep (se 2 (by rfl) ⟨435381, by rfl⟩ : syracuseStep 1161017 = 870763) B870763
theorem B505979 : Blo 147793 505979 := bstep (se 1 (by rfl) ⟨379484, by rfl⟩ : syracuseStep 505979 = 758969) B758969
theorem B637409 : Blo 147793 637409 := bstep (se 2 (by rfl) ⟨239028, by rfl⟩ : syracuseStep 637409 = 478057) B478057
theorem B473725 : Blo 147793 473725 := bstep (se 3 (by rfl) ⟨88823, by rfl⟩ : syracuseStep 473725 = 177647) B177647
theorem B375425 : Blo 147793 375425 := bstep (se 2 (by rfl) ⟨140784, by rfl⟩ : syracuseStep 375425 = 281569) B281569
theorem B933289 : Blo 147793 933289 := bstep (se 2 (by rfl) ⟨349983, by rfl⟩ : syracuseStep 933289 = 699967) B699967
theorem B376235 : Blo 147793 376235 := bstep (se 1 (by rfl) ⟨282176, by rfl⟩ : syracuseStep 376235 = 564353) B564353
theorem B572903 : Blo 147793 572903 := bstep (se 1 (by rfl) ⟨429677, by rfl⟩ : syracuseStep 572903 = 859355) B859355
theorem B212635 : Blo 147793 212635 := bstep (se 1 (by rfl) ⟨159476, by rfl⟩ : syracuseStep 212635 = 318953) B318953
theorem B2801729 : Blo 147793 2801729 := bstep (se 2 (by rfl) ⟨1050648, by rfl⟩ : syracuseStep 2801729 = 2101297) B2101297
theorem B639049 : Blo 147793 639049 := bstep (se 2 (by rfl) ⟨239643, by rfl⟩ : syracuseStep 639049 = 479287) B479287
theorem B507977 : Blo 147793 507977 := bstep (se 2 (by rfl) ⟨190491, by rfl⟩ : syracuseStep 507977 = 380983) B380983
theorem B377095 : Blo 147793 377095 := bstep (se 1 (by rfl) ⟨282821, by rfl⟩ : syracuseStep 377095 = 565643) B565643
theorem B147815 : Blo 147793 147815 := bstep (se 1 (by rfl) ⟨110861, by rfl⟩ : syracuseStep 147815 = 221723) B221723
theorem B147935 : Blo 147793 147935 := bstep (se 1 (by rfl) ⟨110951, by rfl⟩ : syracuseStep 147935 = 221903) B221903
theorem B147943 : Blo 147793 147943 := bstep (se 1 (by rfl) ⟨110957, by rfl⟩ : syracuseStep 147943 = 221915) B221915
theorem B508409 : Blo 147793 508409 := bstep (se 2 (by rfl) ⟨190653, by rfl⟩ : syracuseStep 508409 = 381307) B381307
theorem B148219 : Blo 147793 148219 := bstep (se 1 (by rfl) ⟨111164, by rfl⟩ : syracuseStep 148219 = 222329) B222329
theorem B508733 : Blo 147793 508733 := bstep (se 3 (by rfl) ⟨95387, by rfl⟩ : syracuseStep 508733 = 190775) B190775
theorem B8864731 : Blo 147793 8864731 := bstep (se 1 (by rfl) ⟨6648548, by rfl⟩ : syracuseStep 8864731 = 13297097) B13297097
theorem B3884111 : Blo 147793 3884111 := bstep (se 1 (by rfl) ⟨2913083, by rfl⟩ : syracuseStep 3884111 = 5826167) B5826167
theorem B574573 : Blo 147793 574573 := bstep (se 3 (by rfl) ⟨107732, by rfl⟩ : syracuseStep 574573 = 215465) B215465
theorem B148799 : Blo 147793 148799 := bstep (se 1 (by rfl) ⟨111599, by rfl⟩ : syracuseStep 148799 = 223199) B223199
theorem B148807 : Blo 147793 148807 := bstep (se 1 (by rfl) ⟨111605, by rfl⟩ : syracuseStep 148807 = 223211) B223211
theorem B148839 : Blo 147793 148839 := bstep (se 1 (by rfl) ⟨111629, by rfl⟩ : syracuseStep 148839 = 223259) B223259
theorem B509435 : Blo 147793 509435 := bstep (se 1 (by rfl) ⟨382076, by rfl⟩ : syracuseStep 509435 = 764153) B764153
theorem B575059 : Blo 147793 575059 := bstep (se 1 (by rfl) ⟨431294, by rfl⟩ : syracuseStep 575059 = 862589) B862589
theorem B149083 : Blo 147793 149083 := bstep (se 1 (by rfl) ⟨111812, by rfl⟩ : syracuseStep 149083 = 223625) B223625
theorem B378857 : Blo 147793 378857 := bstep (se 2 (by rfl) ⟨142071, by rfl⟩ : syracuseStep 378857 = 284143) B284143
theorem B2869343 : Blo 147793 2869343 := bstep (se 1 (by rfl) ⟨2152007, by rfl⟩ : syracuseStep 2869343 = 4304015) B4304015
theorem B149711 : Blo 147793 149711 := bstep (se 1 (by rfl) ⟨112283, by rfl⟩ : syracuseStep 149711 = 224567) B224567
theorem B149823 : Blo 147793 149823 := bstep (se 1 (by rfl) ⟨112367, by rfl⟩ : syracuseStep 149823 = 224735) B224735
theorem B1296755 : Blo 147793 1296755 := bstep (se 1 (by rfl) ⟨972566, by rfl⟩ : syracuseStep 1296755 = 1945133) B1945133
theorem B379343 : Blo 147793 379343 := bstep (se 1 (by rfl) ⟨284507, by rfl⟩ : syracuseStep 379343 = 569015) B569015
theorem B149967 : Blo 147793 149967 := bstep (se 1 (by rfl) ⟨112475, by rfl⟩ : syracuseStep 149967 = 224951) B224951
theorem B379475 : Blo 147793 379475 := bstep (se 1 (by rfl) ⟨284606, by rfl⟩ : syracuseStep 379475 = 569213) B569213
theorem B150107 : Blo 147793 150107 := bstep (se 1 (by rfl) ⟨112580, by rfl⟩ : syracuseStep 150107 = 225161) B225161
theorem B150271 : Blo 147793 150271 := bstep (se 1 (by rfl) ⟨112703, by rfl⟩ : syracuseStep 150271 = 225407) B225407
theorem B379655 : Blo 147793 379655 := bstep (se 1 (by rfl) ⟨284741, by rfl⟩ : syracuseStep 379655 = 569483) B569483
theorem B1723355 : Blo 147793 1723355 := bstep (se 1 (by rfl) ⟨1292516, by rfl⟩ : syracuseStep 1723355 = 2585033) B2585033
theorem B380011 : Blo 147793 380011 := bstep (se 1 (by rfl) ⟨285008, by rfl⟩ : syracuseStep 380011 = 570017) B570017
theorem B773267 : Blo 147793 773267 := bstep (se 1 (by rfl) ⟨579950, by rfl⟩ : syracuseStep 773267 = 1159901) B1159901
theorem B150695 : Blo 147793 150695 := bstep (se 1 (by rfl) ⟨113021, by rfl⟩ : syracuseStep 150695 = 226043) B226043
theorem B740627 : Blo 147793 740627 := bstep (se 1 (by rfl) ⟨555470, by rfl⟩ : syracuseStep 740627 = 1110941) B1110941
theorem B380315 : Blo 147793 380315 := bstep (se 1 (by rfl) ⟨285236, by rfl⟩ : syracuseStep 380315 = 570473) B570473
theorem B150991 : Blo 147793 150991 := bstep (se 1 (by rfl) ⟨113243, by rfl⟩ : syracuseStep 150991 = 226487) B226487
theorem B151151 : Blo 147793 151151 := bstep (se 1 (by rfl) ⟨113363, by rfl⟩ : syracuseStep 151151 = 226727) B226727
theorem B151271 : Blo 147793 151271 := bstep (se 1 (by rfl) ⟨113453, by rfl⟩ : syracuseStep 151271 = 226907) B226907
theorem B380659 : Blo 147793 380659 := bstep (se 1 (by rfl) ⟨285494, by rfl⟩ : syracuseStep 380659 = 570989) B570989
theorem B643099 : Blo 147793 643099 := bstep (se 1 (by rfl) ⟨482324, by rfl⟩ : syracuseStep 643099 = 964649) B964649
theorem B151579 : Blo 147793 151579 := bstep (se 1 (by rfl) ⟨113684, by rfl⟩ : syracuseStep 151579 = 227369) B227369
theorem B512027 : Blo 147793 512027 := bstep (se 1 (by rfl) ⟨384020, by rfl⟩ : syracuseStep 512027 = 768041) B768041
theorem B151599 : Blo 147793 151599 := bstep (se 1 (by rfl) ⟨113699, by rfl⟩ : syracuseStep 151599 = 227399) B227399
theorem B250303 : Blo 147793 250303 := bstep (se 1 (by rfl) ⟨187727, by rfl⟩ : syracuseStep 250303 = 375455) B375455
theorem B381743 : Blo 147793 381743 := bstep (se 1 (by rfl) ⟨286307, by rfl⟩ : syracuseStep 381743 = 572615) B572615
theorem B3429371 : Blo 147793 3429371 := bstep (se 1 (by rfl) ⟨2572028, by rfl⟩ : syracuseStep 3429371 = 5144057) B5144057
theorem B1528895 : Blo 147793 1528895 := bstep (se 1 (by rfl) ⟨1146671, by rfl⟩ : syracuseStep 1528895 = 2293343) B2293343
theorem B250951 : Blo 147793 250951 := bstep (se 1 (by rfl) ⟨188213, by rfl⟩ : syracuseStep 250951 = 376427) B376427
theorem B316745 : Blo 147793 316745 := bstep (se 2 (by rfl) ⟨118779, by rfl⟩ : syracuseStep 316745 = 237559) B237559
theorem B284303 : Blo 147793 284303 := bstep (se 1 (by rfl) ⟨213227, by rfl⟩ : syracuseStep 284303 = 426455) B426455
theorem B251687 : Blo 147793 251687 := bstep (se 1 (by rfl) ⟨188765, by rfl⟩ : syracuseStep 251687 = 377531) B377531
theorem B252031 : Blo 147793 252031 := bstep (se 1 (by rfl) ⟨189023, by rfl⟩ : syracuseStep 252031 = 378047) B378047
theorem B383251 : Blo 147793 383251 := bstep (se 1 (by rfl) ⟨287438, by rfl⟩ : syracuseStep 383251 = 574877) B574877
theorem B1432403 : Blo 147793 1432403 := bstep (se 1 (by rfl) ⟨1074302, by rfl⟩ : syracuseStep 1432403 = 2148605) B2148605
theorem B842633 : Blo 147793 842633 := bstep (se 2 (by rfl) ⟨315987, by rfl⟩ : syracuseStep 842633 = 631975) B631975
theorem B646055 : Blo 147793 646055 := bstep (se 1 (by rfl) ⟨484541, by rfl⟩ : syracuseStep 646055 = 969083) B969083
theorem B482735 : Blo 147793 482735 := bstep (se 1 (by rfl) ⟨362051, by rfl⟩ : syracuseStep 482735 = 724103) B724103
theorem B3202487 : Blo 147793 3202487 := bstep (se 1 (by rfl) ⟨2401865, by rfl⟩ : syracuseStep 3202487 = 4803731) B4803731
theorem B3661433 : Blo 147793 3661433 := bstep (se 2 (by rfl) ⟨1373037, by rfl⟩ : syracuseStep 3661433 = 2746075) B2746075
theorem B1433477 : Blo 147793 1433477 := bstep (se 4 (by rfl) ⟨134388, by rfl⟩ : syracuseStep 1433477 = 268777) B268777
theorem B161014169 : Blo 147793 161014169 := bstep (se 2 (by rfl) ⟨60380313, by rfl⟩ : syracuseStep 161014169 = 120760627) B120760627
theorem B188983 : Blo 147793 188983 := bstep (se 1 (by rfl) ⟨141737, by rfl⟩ : syracuseStep 188983 = 283475) B283475
theorem B221855 : Blo 147793 221855 := bstep (se 1 (by rfl) ⟨166391, by rfl⟩ : syracuseStep 221855 = 332783) B332783
theorem B516827 : Blo 147793 516827 := bstep (se 1 (by rfl) ⟨387620, by rfl⟩ : syracuseStep 516827 = 775241) B775241
theorem B5563181 : Blo 147793 5563181 := bstep (se 3 (by rfl) ⟨1043096, by rfl⟩ : syracuseStep 5563181 = 2086193) B2086193
theorem B222191 : Blo 147793 222191 := bstep (se 1 (by rfl) ⟨166643, by rfl⟩ : syracuseStep 222191 = 333287) B333287
theorem B222299 : Blo 147793 222299 := bstep (se 1 (by rfl) ⟨166724, by rfl⟩ : syracuseStep 222299 = 333449) B333449
theorem B222311 : Blo 147793 222311 := bstep (se 1 (by rfl) ⟨166733, by rfl⟩ : syracuseStep 222311 = 333467) B333467
theorem B189631 : Blo 147793 189631 := bstep (se 1 (by rfl) ⟨142223, by rfl⟩ : syracuseStep 189631 = 284447) B284447
theorem B222443 : Blo 147793 222443 := bstep (se 1 (by rfl) ⟨166832, by rfl⟩ : syracuseStep 222443 = 333665) B333665
theorem B222575 : Blo 147793 222575 := bstep (se 1 (by rfl) ⟨166931, by rfl⟩ : syracuseStep 222575 = 333863) B333863
theorem B222695 : Blo 147793 222695 := bstep (se 1 (by rfl) ⟨167021, by rfl⟩ : syracuseStep 222695 = 334043) B334043
theorem B321079 : Blo 147793 321079 := bstep (se 1 (by rfl) ⟨240809, by rfl⟩ : syracuseStep 321079 = 481619) B481619
theorem B222827 : Blo 147793 222827 := bstep (se 1 (by rfl) ⟨167120, by rfl⟩ : syracuseStep 222827 = 334241) B334241
theorem B255595 : Blo 147793 255595 := bstep (se 1 (by rfl) ⟨191696, by rfl⟩ : syracuseStep 255595 = 383393) B383393
theorem B222875 : Blo 147793 222875 := bstep (se 1 (by rfl) ⟨167156, by rfl⟩ : syracuseStep 222875 = 334313) B334313
theorem B157339 : Blo 147793 157339 := bstep (se 1 (by rfl) ⟨118004, by rfl⟩ : syracuseStep 157339 = 236009) B236009
theorem B26109773 : Blo 147793 26109773 := bstep (se 3 (by rfl) ⟨4895582, by rfl⟩ : syracuseStep 26109773 = 9791165) B9791165
theorem B223097 : Blo 147793 223097 := bstep (se 2 (by rfl) ⟨83661, by rfl⟩ : syracuseStep 223097 = 167323) B167323
theorem B255865 : Blo 147793 255865 := bstep (se 2 (by rfl) ⟨95949, by rfl⟩ : syracuseStep 255865 = 191899) B191899
theorem B2550041 : Blo 147793 2550041 := bstep (se 2 (by rfl) ⟨956265, by rfl⟩ : syracuseStep 2550041 = 1912531) B1912531
theorem B223847 : Blo 147793 223847 := bstep (se 1 (by rfl) ⟨167885, by rfl⟩ : syracuseStep 223847 = 335771) B335771
theorem B846551 : Blo 147793 846551 := bstep (se 1 (by rfl) ⟨634913, by rfl⟩ : syracuseStep 846551 = 1269827) B1269827
theorem B256891 : Blo 147793 256891 := bstep (se 1 (by rfl) ⟨192668, by rfl⟩ : syracuseStep 256891 = 385337) B385337
theorem B224123 : Blo 147793 224123 := bstep (se 1 (by rfl) ⟨168092, by rfl⟩ : syracuseStep 224123 = 336185) B336185
theorem B224393 : Blo 147793 224393 := bstep (se 2 (by rfl) ⟨84147, by rfl⟩ : syracuseStep 224393 = 168295) B168295
theorem B224447 : Blo 147793 224447 := bstep (se 1 (by rfl) ⟨168335, by rfl⟩ : syracuseStep 224447 = 336671) B336671
theorem B5795309 : Blo 147793 5795309 := bstep (se 3 (by rfl) ⟨1086620, by rfl⟩ : syracuseStep 5795309 = 2173241) B2173241
theorem B224987 : Blo 147793 224987 := bstep (se 1 (by rfl) ⟨168740, by rfl⟩ : syracuseStep 224987 = 337481) B337481
theorem B225257 : Blo 147793 225257 := bstep (se 2 (by rfl) ⟨84471, by rfl⟩ : syracuseStep 225257 = 168943) B168943
theorem B225275 : Blo 147793 225275 := bstep (se 1 (by rfl) ⟨168956, by rfl⟩ : syracuseStep 225275 = 337913) B337913
theorem B225311 : Blo 147793 225311 := bstep (se 1 (by rfl) ⟨168983, by rfl⟩ : syracuseStep 225311 = 337967) B337967
theorem B225335 : Blo 147793 225335 := bstep (se 1 (by rfl) ⟨169001, by rfl⟩ : syracuseStep 225335 = 338003) B338003
theorem B225455 : Blo 147793 225455 := bstep (se 1 (by rfl) ⟨169091, by rfl⟩ : syracuseStep 225455 = 338183) B338183
theorem B225659 : Blo 147793 225659 := bstep (se 1 (by rfl) ⟨169244, by rfl⟩ : syracuseStep 225659 = 338489) B338489
theorem B225929 : Blo 147793 225929 := bstep (se 2 (by rfl) ⟨84723, by rfl⟩ : syracuseStep 225929 = 169447) B169447
theorem B160475 : Blo 147793 160475 := bstep (se 1 (by rfl) ⟨120356, by rfl⟩ : syracuseStep 160475 = 240713) B240713
theorem B750383 : Blo 147793 750383 := bstep (se 1 (by rfl) ⟨562787, by rfl⟩ : syracuseStep 750383 = 1125575) B1125575
theorem B226139 : Blo 147793 226139 := bstep (se 1 (by rfl) ⟨169604, by rfl⟩ : syracuseStep 226139 = 339209) B339209
theorem B226169 : Blo 147793 226169 := bstep (se 2 (by rfl) ⟨84813, by rfl⟩ : syracuseStep 226169 = 169627) B169627
theorem B357871 : Blo 147793 357871 := bstep (se 1 (by rfl) ⟨268403, by rfl⟩ : syracuseStep 357871 = 536807) B536807
theorem B226799 : Blo 147793 226799 := bstep (se 1 (by rfl) ⟨170099, by rfl⟩ : syracuseStep 226799 = 340199) B340199
theorem B1832539 : Blo 147793 1832539 := bstep (se 1 (by rfl) ⟨1374404, by rfl⟩ : syracuseStep 1832539 = 2748809) B2748809
theorem B226919 : Blo 147793 226919 := bstep (se 1 (by rfl) ⟨170189, by rfl⟩ : syracuseStep 226919 = 340379) B340379
theorem B1701485 : Blo 147793 1701485 := bstep (se 3 (by rfl) ⟨319028, by rfl⟩ : syracuseStep 1701485 = 638057) B638057
theorem B227375 : Blo 147793 227375 := bstep (se 1 (by rfl) ⟨170531, by rfl⟩ : syracuseStep 227375 = 341063) B341063
theorem B227495 : Blo 147793 227495 := bstep (se 1 (by rfl) ⟨170621, by rfl⟩ : syracuseStep 227495 = 341243) B341243
theorem B227639 : Blo 147793 227639 := bstep (se 1 (by rfl) ⟨170729, by rfl⟩ : syracuseStep 227639 = 341459) B341459
theorem B424871 : Blo 147793 424871 := bstep (se 1 (by rfl) ⟨318653, by rfl⟩ : syracuseStep 424871 = 637307) B637307
theorem B850925 : Blo 147793 850925 := bstep (se 3 (by rfl) ⟨159548, by rfl⟩ : syracuseStep 850925 = 319097) B319097
theorem B6290507 : Blo 147793 6290507 := bstep (se 1 (by rfl) ⟨4717880, by rfl⟩ : syracuseStep 6290507 = 9435761) B9435761
theorem B458063 : Blo 147793 458063 := bstep (se 1 (by rfl) ⟨343547, by rfl⟩ : syracuseStep 458063 = 687095) B687095
theorem B1867819 : Blo 147793 1867819 := bstep (se 1 (by rfl) ⟨1400864, by rfl⟩ : syracuseStep 1867819 = 2801729) B2801729
theorem B852065 : Blo 147793 852065 := bstep (se 2 (by rfl) ⟨319524, by rfl⟩ : syracuseStep 852065 = 639049) B639049
theorem B2589407 : Blo 147793 2589407 := bstep (se 1 (by rfl) ⟨1942055, by rfl⟩ : syracuseStep 2589407 = 3884111) B3884111
theorem B722627 : Blo 147793 722627 := bstep (se 1 (by rfl) ⟨541970, by rfl⟩ : syracuseStep 722627 = 1083941) B1083941
theorem B427933 : Blo 147793 427933 := bstep (se 3 (by rfl) ⟨80237, by rfl⟩ : syracuseStep 427933 = 160475) B160475
theorem B1378205 : Blo 147793 1378205 := bstep (se 3 (by rfl) ⟨258413, by rfl⟩ : syracuseStep 1378205 = 516827) B516827
theorem B1148903 : Blo 147793 1148903 := bstep (se 1 (by rfl) ⟨861677, by rfl⟩ : syracuseStep 1148903 = 1723355) B1723355
theorem B428105 : Blo 147793 428105 := bstep (se 2 (by rfl) ⟨160539, by rfl⟩ : syracuseStep 428105 = 321079) B321079
theorem B493751 : Blo 147793 493751 := bstep (se 1 (by rfl) ⟨370313, by rfl⟩ : syracuseStep 493751 = 740627) B740627
theorem B919775 : Blo 147793 919775 := bstep (se 1 (by rfl) ⟨689831, by rfl⟩ : syracuseStep 919775 = 1379663) B1379663
theorem B3770833 : Blo 147793 3770833 := bstep (se 2 (by rfl) ⟨1414062, by rfl⟩ : syracuseStep 3770833 = 2828125) B2828125
theorem B1837799 : Blo 147793 1837799 := bstep (se 1 (by rfl) ⟨1378349, by rfl⟩ : syracuseStep 1837799 = 2756699) B2756699
theorem B2755529 : Blo 147793 2755529 := bstep (se 2 (by rfl) ⟨1033323, by rfl⟩ : syracuseStep 2755529 = 2066647) B2066647
theorem B8621153 : Blo 147793 8621153 := bstep (se 2 (by rfl) ⟨3232932, by rfl⟩ : syracuseStep 8621153 = 6465865) B6465865
theorem B1019263 : Blo 147793 1019263 := bstep (se 1 (by rfl) ⟨764447, by rfl⟩ : syracuseStep 1019263 = 1528895) B1528895
theorem B364297 : Blo 147793 364297 := bstep (se 2 (by rfl) ⟨136611, by rfl⟩ : syracuseStep 364297 = 273223) B273223
theorem B167791 : Blo 147793 167791 := bstep (se 1 (by rfl) ⟨125843, by rfl⟩ : syracuseStep 167791 = 251687) B251687
theorem B266465 : Blo 147793 266465 := bstep (se 2 (by rfl) ⟨99924, by rfl⟩ : syracuseStep 266465 = 199849) B199849
theorem B954935 : Blo 147793 954935 := bstep (se 1 (by rfl) ⟨716201, by rfl⟩ : syracuseStep 954935 = 1432403) B1432403
theorem B561755 : Blo 147793 561755 := bstep (se 1 (by rfl) ⟨421316, by rfl⟩ : syracuseStep 561755 = 842633) B842633
theorem B430703 : Blo 147793 430703 := bstep (se 1 (by rfl) ⟨323027, by rfl⟩ : syracuseStep 430703 = 646055) B646055
theorem B1282949 : Blo 147793 1282949 := bstep (se 4 (by rfl) ⟨120276, by rfl⟩ : syracuseStep 1282949 = 240553) B240553
theorem B2134991 : Blo 147793 2134991 := bstep (se 1 (by rfl) ⟨1601243, by rfl⟩ : syracuseStep 2134991 = 3202487) B3202487
theorem B955651 : Blo 147793 955651 := bstep (se 1 (by rfl) ⟨716738, by rfl⟩ : syracuseStep 955651 = 1433477) B1433477
theorem B857465 : Blo 147793 857465 := bstep (se 2 (by rfl) ⟨321549, by rfl⟩ : syracuseStep 857465 = 643099) B643099
theorem B3708787 : Blo 147793 3708787 := bstep (se 1 (by rfl) ⟨2781590, by rfl⟩ : syracuseStep 3708787 = 5563181) B5563181
theorem B333737 : Blo 147793 333737 := bstep (se 2 (by rfl) ⟨125151, by rfl⟩ : syracuseStep 333737 = 250303) B250303
theorem B17406515 : Blo 147793 17406515 := bstep (se 1 (by rfl) ⟨13054886, by rfl⟩ : syracuseStep 17406515 = 26109773) B26109773
theorem B334601 : Blo 147793 334601 := bstep (se 2 (by rfl) ⟨125475, by rfl⟩ : syracuseStep 334601 = 250951) B250951
theorem B564367 : Blo 147793 564367 := bstep (se 1 (by rfl) ⟨423275, by rfl⟩ : syracuseStep 564367 = 846551) B846551
theorem B336041 : Blo 147793 336041 := bstep (se 2 (by rfl) ⟨126015, by rfl⟩ : syracuseStep 336041 = 252031) B252031
theorem B500255 : Blo 147793 500255 := bstep (se 1 (by rfl) ⟨375191, by rfl⟩ : syracuseStep 500255 = 750383) B750383
theorem B631633 : Blo 147793 631633 := bstep (se 2 (by rfl) ⟨236862, by rfl⟩ : syracuseStep 631633 = 473725) B473725
theorem B336959 : Blo 147793 336959 := bstep (se 1 (by rfl) ⟨252719, by rfl⟩ : syracuseStep 336959 = 505439) B505439
theorem B337319 : Blo 147793 337319 := bstep (se 1 (by rfl) ⟨252989, by rfl⟩ : syracuseStep 337319 = 505979) B505979
theorem B567283 : Blo 147793 567283 := bstep (se 1 (by rfl) ⟨425462, by rfl⟩ : syracuseStep 567283 = 850925) B850925
theorem B305375 : Blo 147793 305375 := bstep (se 1 (by rfl) ⟨229031, by rfl⟩ : syracuseStep 305375 = 458063) B458063
theorem B338651 : Blo 147793 338651 := bstep (se 1 (by rfl) ⟨253988, by rfl⟩ : syracuseStep 338651 = 507977) B507977
theorem B568255 : Blo 147793 568255 := bstep (se 1 (by rfl) ⟨426191, by rfl⟩ : syracuseStep 568255 = 852383) B852383
theorem B338939 : Blo 147793 338939 := bstep (se 1 (by rfl) ⟨254204, by rfl⟩ : syracuseStep 338939 = 508409) B508409
theorem B502793 : Blo 147793 502793 := bstep (se 2 (by rfl) ⟨188547, by rfl⟩ : syracuseStep 502793 = 377095) B377095
theorem B502847 : Blo 147793 502847 := bstep (se 1 (by rfl) ⟨377135, by rfl⟩ : syracuseStep 502847 = 754271) B754271
theorem B568529 : Blo 147793 568529 := bstep (se 2 (by rfl) ⟨213198, by rfl⟩ : syracuseStep 568529 = 426397) B426397
theorem B339155 : Blo 147793 339155 := bstep (se 1 (by rfl) ⟨254366, by rfl⟩ : syracuseStep 339155 = 508733) B508733
theorem B339623 : Blo 147793 339623 := bstep (se 1 (by rfl) ⟨254717, by rfl⟩ : syracuseStep 339623 = 509435) B509435
theorem B1912895 : Blo 147793 1912895 := bstep (se 1 (by rfl) ⟨1434671, by rfl⟩ : syracuseStep 1912895 = 2869343) B2869343
theorem B766097 : Blo 147793 766097 := bstep (se 2 (by rfl) ⟨287286, by rfl⟩ : syracuseStep 766097 = 574573) B574573
theorem B864503 : Blo 147793 864503 := bstep (se 1 (by rfl) ⟨648377, by rfl⟩ : syracuseStep 864503 = 1296755) B1296755
theorem B1028371 : Blo 147793 1028371 := bstep (se 1 (by rfl) ⟨771278, by rfl⟩ : syracuseStep 1028371 = 1542557) B1542557
theorem B242207 : Blo 147793 242207 := bstep (se 1 (by rfl) ⟨181655, by rfl⟩ : syracuseStep 242207 = 363311) B363311
theorem B766745 : Blo 147793 766745 := bstep (se 2 (by rfl) ⟨287529, by rfl⟩ : syracuseStep 766745 = 575059) B575059
theorem B340793 : Blo 147793 340793 := bstep (se 2 (by rfl) ⟨127797, by rfl⟩ : syracuseStep 340793 = 255595) B255595
theorem B209785 : Blo 147793 209785 := bstep (se 2 (by rfl) ⟨78669, by rfl⟩ : syracuseStep 209785 = 157339) B157339
theorem B504791 : Blo 147793 504791 := bstep (se 1 (by rfl) ⟨378593, by rfl⟩ : syracuseStep 504791 = 757187) B757187
theorem B570503 : Blo 147793 570503 := bstep (se 1 (by rfl) ⟨427877, by rfl⟩ : syracuseStep 570503 = 855755) B855755
theorem B341153 : Blo 147793 341153 := bstep (se 2 (by rfl) ⟨127932, by rfl⟩ : syracuseStep 341153 = 255865) B255865
theorem B341351 : Blo 147793 341351 := bstep (se 1 (by rfl) ⟨256013, by rfl⟩ : syracuseStep 341351 = 512027) B512027
theorem B2898017 : Blo 147793 2898017 := bstep (se 2 (by rfl) ⟨1086756, by rfl⟩ : syracuseStep 2898017 = 2173513) B2173513
theorem B211163 : Blo 147793 211163 := bstep (se 1 (by rfl) ⟨158372, by rfl⟩ : syracuseStep 211163 = 316745) B316745
theorem B1161503 : Blo 147793 1161503 := bstep (se 1 (by rfl) ⟨871127, by rfl⟩ : syracuseStep 1161503 = 1742255) B1742255
theorem B1292759 : Blo 147793 1292759 := bstep (se 1 (by rfl) ⟨969569, by rfl⟩ : syracuseStep 1292759 = 1939139) B1939139
theorem B342521 : Blo 147793 342521 := bstep (se 2 (by rfl) ⟨128445, by rfl⟩ : syracuseStep 342521 = 256891) B256891
theorem B506681 : Blo 147793 506681 := bstep (se 2 (by rfl) ⟨190005, by rfl⟩ : syracuseStep 506681 = 380011) B380011
theorem B507545 : Blo 147793 507545 := bstep (se 2 (by rfl) ⟨190329, by rfl⟩ : syracuseStep 507545 = 380659) B380659
theorem B2440955 : Blo 147793 2440955 := bstep (se 1 (by rfl) ⟨1830716, by rfl⟩ : syracuseStep 2440955 = 3661433) B3661433
theorem B147903 : Blo 147793 147903 := bstep (se 1 (by rfl) ⟨110927, by rfl⟩ : syracuseStep 147903 = 221855) B221855
theorem B148127 : Blo 147793 148127 := bstep (se 1 (by rfl) ⟨111095, by rfl⟩ : syracuseStep 148127 = 222191) B222191
theorem B148199 : Blo 147793 148199 := bstep (se 1 (by rfl) ⟨111149, by rfl⟩ : syracuseStep 148199 = 222299) B222299
theorem B148207 : Blo 147793 148207 := bstep (se 1 (by rfl) ⟨111155, by rfl⟩ : syracuseStep 148207 = 222311) B222311
theorem B508679 : Blo 147793 508679 := bstep (se 1 (by rfl) ⟨381509, by rfl⟩ : syracuseStep 508679 = 763019) B763019
theorem B148295 : Blo 147793 148295 := bstep (se 1 (by rfl) ⟨111221, by rfl⟩ : syracuseStep 148295 = 222443) B222443
theorem B148383 : Blo 147793 148383 := bstep (se 1 (by rfl) ⟨111287, by rfl⟩ : syracuseStep 148383 = 222575) B222575
theorem B508895 : Blo 147793 508895 := bstep (se 1 (by rfl) ⟨381671, by rfl⟩ : syracuseStep 508895 = 763343) B763343
theorem B148463 : Blo 147793 148463 := bstep (se 1 (by rfl) ⟨111347, by rfl⟩ : syracuseStep 148463 = 222695) B222695
theorem B148551 : Blo 147793 148551 := bstep (se 1 (by rfl) ⟨111413, by rfl⟩ : syracuseStep 148551 = 222827) B222827
theorem B148583 : Blo 147793 148583 := bstep (se 1 (by rfl) ⟨111437, by rfl⟩ : syracuseStep 148583 = 222875) B222875
theorem B509111 : Blo 147793 509111 := bstep (se 1 (by rfl) ⟨381833, by rfl⟩ : syracuseStep 509111 = 763667) B763667
theorem B148731 : Blo 147793 148731 := bstep (se 1 (by rfl) ⟨111548, by rfl⟩ : syracuseStep 148731 = 223097) B223097
theorem B2541293 : Blo 147793 2541293 := bstep (se 3 (by rfl) ⟨476492, by rfl⟩ : syracuseStep 2541293 = 952985) B952985
theorem B149231 : Blo 147793 149231 := bstep (se 1 (by rfl) ⟨111923, by rfl⟩ : syracuseStep 149231 = 223847) B223847
theorem B509759 : Blo 147793 509759 := bstep (se 1 (by rfl) ⟨382319, by rfl⟩ : syracuseStep 509759 = 764639) B764639
theorem B149415 : Blo 147793 149415 := bstep (se 1 (by rfl) ⟨112061, by rfl⟩ : syracuseStep 149415 = 224123) B224123
theorem B477161 : Blo 147793 477161 := bstep (se 2 (by rfl) ⟨178935, by rfl⟩ : syracuseStep 477161 = 357871) B357871
theorem B149595 : Blo 147793 149595 := bstep (se 1 (by rfl) ⟨112196, by rfl⟩ : syracuseStep 149595 = 224393) B224393
theorem B2443385 : Blo 147793 2443385 := bstep (se 2 (by rfl) ⟨916269, by rfl⟩ : syracuseStep 2443385 = 1832539) B1832539
theorem B149631 : Blo 147793 149631 := bstep (se 1 (by rfl) ⟨112223, by rfl⟩ : syracuseStep 149631 = 224447) B224447
theorem B149991 : Blo 147793 149991 := bstep (se 1 (by rfl) ⟨112493, by rfl⟩ : syracuseStep 149991 = 224987) B224987
theorem B150171 : Blo 147793 150171 := bstep (se 1 (by rfl) ⟨112628, by rfl⟩ : syracuseStep 150171 = 225257) B225257
theorem B150183 : Blo 147793 150183 := bstep (se 1 (by rfl) ⟨112637, by rfl⟩ : syracuseStep 150183 = 225275) B225275
theorem B150207 : Blo 147793 150207 := bstep (se 1 (by rfl) ⟨112655, by rfl⟩ : syracuseStep 150207 = 225311) B225311
theorem B150223 : Blo 147793 150223 := bstep (se 1 (by rfl) ⟨112667, by rfl⟩ : syracuseStep 150223 = 225335) B225335
theorem B150303 : Blo 147793 150303 := bstep (se 1 (by rfl) ⟨112727, by rfl⟩ : syracuseStep 150303 = 225455) B225455
theorem B150439 : Blo 147793 150439 := bstep (se 1 (by rfl) ⟨112829, by rfl⟩ : syracuseStep 150439 = 225659) B225659
theorem B511001 : Blo 147793 511001 := bstep (se 2 (by rfl) ⟨191625, by rfl⟩ : syracuseStep 511001 = 383251) B383251
theorem B150619 : Blo 147793 150619 := bstep (se 1 (by rfl) ⟨112964, by rfl⟩ : syracuseStep 150619 = 225929) B225929
theorem B150759 : Blo 147793 150759 := bstep (se 1 (by rfl) ⟨113069, by rfl⟩ : syracuseStep 150759 = 226139) B226139
theorem B150779 : Blo 147793 150779 := bstep (se 1 (by rfl) ⟨113084, by rfl⟩ : syracuseStep 150779 = 226169) B226169
theorem B27512459 : Blo 147793 27512459 := bstep (se 1 (by rfl) ⟨20634344, by rfl⟩ : syracuseStep 27512459 = 41268689) B41268689
theorem B151199 : Blo 147793 151199 := bstep (se 1 (by rfl) ⟨113399, by rfl⟩ : syracuseStep 151199 = 226799) B226799
theorem B380639 : Blo 147793 380639 := bstep (se 1 (by rfl) ⟨285479, by rfl⟩ : syracuseStep 380639 = 570959) B570959
theorem B151279 : Blo 147793 151279 := bstep (se 1 (by rfl) ⟨113459, by rfl⟩ : syracuseStep 151279 = 226919) B226919
theorem B1134323 : Blo 147793 1134323 := bstep (se 1 (by rfl) ⟨850742, by rfl⟩ : syracuseStep 1134323 = 1701485) B1701485
theorem B1560323 : Blo 147793 1560323 := bstep (se 1 (by rfl) ⟨1170242, by rfl⟩ : syracuseStep 1560323 = 2340485) B2340485
theorem B774011 : Blo 147793 774011 := bstep (se 1 (by rfl) ⟨580508, by rfl⟩ : syracuseStep 774011 = 1161017) B1161017
theorem B151583 : Blo 147793 151583 := bstep (se 1 (by rfl) ⟨113687, by rfl⟩ : syracuseStep 151583 = 227375) B227375
theorem B151663 : Blo 147793 151663 := bstep (se 1 (by rfl) ⟨113747, by rfl⟩ : syracuseStep 151663 = 227495) B227495
theorem B151759 : Blo 147793 151759 := bstep (se 1 (by rfl) ⟨113819, by rfl⟩ : syracuseStep 151759 = 227639) B227639
theorem B250283 : Blo 147793 250283 := bstep (se 1 (by rfl) ⟨187712, by rfl⟩ : syracuseStep 250283 = 375425) B375425
theorem B283247 : Blo 147793 283247 := bstep (se 1 (by rfl) ⟨212435, by rfl⟩ : syracuseStep 283247 = 424871) B424871
theorem B283513 : Blo 147793 283513 := bstep (se 2 (by rfl) ⟨106317, by rfl⟩ : syracuseStep 283513 = 212635) B212635
theorem B250823 : Blo 147793 250823 := bstep (se 1 (by rfl) ⟨188117, by rfl⟩ : syracuseStep 250823 = 376235) B376235
theorem B381935 : Blo 147793 381935 := bstep (se 1 (by rfl) ⟨286451, by rfl⟩ : syracuseStep 381935 = 572903) B572903
theorem B1463923 : Blo 147793 1463923 := bstep (se 1 (by rfl) ⟨1097942, by rfl⟩ : syracuseStep 1463923 = 2195885) B2195885
theorem B251977 : Blo 147793 251977 := bstep (se 2 (by rfl) ⟨94491, by rfl⟩ : syracuseStep 251977 = 188983) B188983
theorem B11819641 : Blo 147793 11819641 := bstep (se 2 (by rfl) ⟨4432365, by rfl⟩ : syracuseStep 11819641 = 8864731) B8864731
theorem B252571 : Blo 147793 252571 := bstep (se 1 (by rfl) ⟨189428, by rfl⟩ : syracuseStep 252571 = 378857) B378857
theorem B940709 : Blo 147793 940709 := bstep (se 4 (by rfl) ⟨88191, by rfl⟩ : syracuseStep 940709 = 176383) B176383
theorem B285419 : Blo 147793 285419 := bstep (se 1 (by rfl) ⟨214064, by rfl⟩ : syracuseStep 285419 = 428129) B428129
theorem B252841 : Blo 147793 252841 := bstep (se 2 (by rfl) ⟨94815, by rfl⟩ : syracuseStep 252841 = 189631) B189631
theorem B252895 : Blo 147793 252895 := bstep (se 1 (by rfl) ⟨189671, by rfl⟩ : syracuseStep 252895 = 379343) B379343
theorem B252983 : Blo 147793 252983 := bstep (se 1 (by rfl) ⟨189737, by rfl⟩ : syracuseStep 252983 = 379475) B379475
theorem B253103 : Blo 147793 253103 := bstep (se 1 (by rfl) ⟨189827, by rfl⟩ : syracuseStep 253103 = 379655) B379655
theorem B253543 : Blo 147793 253543 := bstep (se 1 (by rfl) ⟨190157, by rfl⟩ : syracuseStep 253543 = 380315) B380315
theorem B876271 : Blo 147793 876271 := bstep (se 1 (by rfl) ⟨657203, by rfl⟩ : syracuseStep 876271 = 1314407) B1314407
theorem B254495 : Blo 147793 254495 := bstep (se 1 (by rfl) ⟨190871, by rfl⟩ : syracuseStep 254495 = 381743) B381743
theorem B2286247 : Blo 147793 2286247 := bstep (se 1 (by rfl) ⟨1714685, by rfl⟩ : syracuseStep 2286247 = 3429371) B3429371
theorem B222023 : Blo 147793 222023 := bstep (se 1 (by rfl) ⟨166517, by rfl⟩ : syracuseStep 222023 = 333035) B333035
theorem B222089 : Blo 147793 222089 := bstep (se 2 (by rfl) ⟨83283, by rfl⟩ : syracuseStep 222089 = 166567) B166567
theorem B222185 : Blo 147793 222185 := bstep (se 2 (by rfl) ⟨83319, by rfl⟩ : syracuseStep 222185 = 166639) B166639
theorem B189535 : Blo 147793 189535 := bstep (se 1 (by rfl) ⟨142151, by rfl⟩ : syracuseStep 189535 = 284303) B284303
theorem B1270889 : Blo 147793 1270889 := bstep (se 2 (by rfl) ⟨476583, by rfl⟩ : syracuseStep 1270889 = 953167) B953167
theorem B222431 : Blo 147793 222431 := bstep (se 1 (by rfl) ⟨166823, by rfl⟩ : syracuseStep 222431 = 333647) B333647
theorem B222623 : Blo 147793 222623 := bstep (se 1 (by rfl) ⟨166967, by rfl⟩ : syracuseStep 222623 = 333935) B333935
theorem B1140155 : Blo 147793 1140155 := bstep (se 1 (by rfl) ⟨855116, by rfl⟩ : syracuseStep 1140155 = 1710233) B1710233
theorem B222671 : Blo 147793 222671 := bstep (se 1 (by rfl) ⟨167003, by rfl⟩ : syracuseStep 222671 = 334007) B334007
theorem B1074707 : Blo 147793 1074707 := bstep (se 1 (by rfl) ⟨806030, by rfl⟩ : syracuseStep 1074707 = 1612061) B1612061
theorem B222857 : Blo 147793 222857 := bstep (se 2 (by rfl) ⟨83571, by rfl⟩ : syracuseStep 222857 = 167143) B167143
theorem B222911 : Blo 147793 222911 := bstep (se 1 (by rfl) ⟨167183, by rfl⟩ : syracuseStep 222911 = 334367) B334367
theorem B2418473 : Blo 147793 2418473 := bstep (se 2 (by rfl) ⟨906927, by rfl⟩ : syracuseStep 2418473 = 1813855) B1813855
theorem B2910167 : Blo 147793 2910167 := bstep (se 1 (by rfl) ⟨2182625, by rfl⟩ : syracuseStep 2910167 = 4365251) B4365251
theorem B321823 : Blo 147793 321823 := bstep (se 1 (by rfl) ⟨241367, by rfl⟩ : syracuseStep 321823 = 482735) B482735
theorem B107342779 : Blo 147793 107342779 := bstep (se 1 (by rfl) ⟨80507084, by rfl⟩ : syracuseStep 107342779 = 161014169) B161014169
theorem B1207943 : Blo 147793 1207943 := bstep (se 1 (by rfl) ⟨905957, by rfl⟩ : syracuseStep 1207943 = 1811915) B1811915
theorem B224927 : Blo 147793 224927 := bstep (se 1 (by rfl) ⟨168695, by rfl⟩ : syracuseStep 224927 = 337391) B337391
theorem B1700027 : Blo 147793 1700027 := bstep (se 1 (by rfl) ⟨1275020, by rfl⟩ : syracuseStep 1700027 = 2550041) B2550041
theorem B1143071 : Blo 147793 1143071 := bstep (se 1 (by rfl) ⟨857303, by rfl⟩ : syracuseStep 1143071 = 1714607) B1714607
theorem B1077623 : Blo 147793 1077623 := bstep (se 1 (by rfl) ⟨808217, by rfl⟩ : syracuseStep 1077623 = 1616435) B1616435
theorem B225695 : Blo 147793 225695 := bstep (se 1 (by rfl) ⟨169271, by rfl⟩ : syracuseStep 225695 = 338543) B338543
theorem B225839 : Blo 147793 225839 := bstep (se 1 (by rfl) ⟨169379, by rfl⟩ : syracuseStep 225839 = 338759) B338759
theorem B4977541 : Blo 147793 4977541 := bstep (se 4 (by rfl) ⟨466644, by rfl⟩ : syracuseStep 4977541 = 933289) B933289
theorem B3863539 : Blo 147793 3863539 := bstep (se 1 (by rfl) ⟨2897654, by rfl⟩ : syracuseStep 3863539 = 5795309) B5795309
theorem B226793 : Blo 147793 226793 := bstep (se 2 (by rfl) ⟨85047, by rfl⟩ : syracuseStep 226793 = 170095) B170095
theorem B16774685 : Blo 147793 16774685 := bstep (se 3 (by rfl) ⟨3145253, by rfl⟩ : syracuseStep 16774685 = 6290507) B6290507
theorem B2062045 : Blo 147793 2062045 := bstep (se 3 (by rfl) ⟨386633, by rfl⟩ : syracuseStep 2062045 = 773267) B773267
theorem B227465 : Blo 147793 227465 := bstep (se 2 (by rfl) ⟨85299, by rfl⟩ : syracuseStep 227465 = 170599) B170599
theorem B227579 : Blo 147793 227579 := bstep (se 1 (by rfl) ⟨170684, by rfl⟩ : syracuseStep 227579 = 341369) B341369
theorem B162043 : Blo 147793 162043 := bstep (se 1 (by rfl) ⟨121532, by rfl⟩ : syracuseStep 162043 = 243065) B243065
theorem B227663 : Blo 147793 227663 := bstep (se 1 (by rfl) ⟨170747, by rfl⟩ : syracuseStep 227663 = 341495) B341495
theorem B424939 : Blo 147793 424939 := bstep (se 1 (by rfl) ⟨318704, by rfl⟩ : syracuseStep 424939 = 637409) B637409
theorem B2490425 : Blo 147793 2490425 := bstep (se 2 (by rfl) ⟨933909, by rfl⟩ : syracuseStep 2490425 = 1867819) B1867819
theorem B3048329 : Blo 147793 3048329 := bstep (se 2 (by rfl) ⟨1143123, by rfl⟩ : syracuseStep 3048329 = 2286247) B2286247
theorem B918803 : Blo 147793 918803 := bstep (se 1 (by rfl) ⟨689102, by rfl⟩ : syracuseStep 918803 = 1378205) B1378205
theorem B329167 : Blo 147793 329167 := bstep (se 1 (by rfl) ⟨246875, by rfl⟩ : syracuseStep 329167 = 493751) B493751
theorem B1837019 : Blo 147793 1837019 := bstep (se 1 (by rfl) ⟨1377764, by rfl⟩ : syracuseStep 1837019 = 2755529) B2755529
theorem B756215 : Blo 147793 756215 := bstep (se 1 (by rfl) ⟨567161, by rfl⟩ : syracuseStep 756215 = 1134323) B1134323
theorem B756377 : Blo 147793 756377 := bstep (se 2 (by rfl) ⟨283641, by rfl⟩ : syracuseStep 756377 = 567283) B567283
theorem B166855 : Blo 147793 166855 := bstep (se 1 (by rfl) ⟨125141, by rfl⟩ : syracuseStep 166855 = 250283) B250283
theorem B429097 : Blo 147793 429097 := bstep (se 2 (by rfl) ⟨160911, by rfl⟩ : syracuseStep 429097 = 321823) B321823
theorem B855299 : Blo 147793 855299 := bstep (se 1 (by rfl) ⟨641474, by rfl⟩ : syracuseStep 855299 = 1282949) B1282949
theorem B167215 : Blo 147793 167215 := bstep (se 1 (by rfl) ⟨125411, by rfl⟩ : syracuseStep 167215 = 250823) B250823
theorem B757673 : Blo 147793 757673 := bstep (se 2 (by rfl) ⟨284127, by rfl⟩ : syracuseStep 757673 = 568255) B568255
theorem B11604343 : Blo 147793 11604343 := bstep (se 1 (by rfl) ⟨8703257, by rfl⟩ : syracuseStep 11604343 = 17406515) B17406515
theorem B627139 : Blo 147793 627139 := bstep (se 1 (by rfl) ⟨470354, by rfl⟩ : syracuseStep 627139 = 940709) B940709
theorem B26546885 : Blo 147793 26546885 := bstep (se 4 (by rfl) ⟨2488770, by rfl⟩ : syracuseStep 26546885 = 4977541) B4977541
theorem B168655 : Blo 147793 168655 := bstep (se 1 (by rfl) ⟨126491, by rfl⟩ : syracuseStep 168655 = 252983) B252983
theorem B333503 : Blo 147793 333503 := bstep (se 1 (by rfl) ⟨250127, by rfl⟩ : syracuseStep 333503 = 500255) B500255
theorem B169663 : Blo 147793 169663 := bstep (se 1 (by rfl) ⟨127247, by rfl⟩ : syracuseStep 169663 = 254495) B254495
theorem B760103 : Blo 147793 760103 := bstep (se 1 (by rfl) ⟨570077, by rfl⟩ : syracuseStep 760103 = 1140155) B1140155
theorem B1612315 : Blo 147793 1612315 := bstep (se 1 (by rfl) ⟨1209236, by rfl⟩ : syracuseStep 1612315 = 2418473) B2418473
theorem B1940111 : Blo 147793 1940111 := bstep (se 1 (by rfl) ⟨1455083, by rfl⟩ : syracuseStep 1940111 = 2910167) B2910167
theorem B5151385 : Blo 147793 5151385 := bstep (se 2 (by rfl) ⟨1931769, by rfl⟩ : syracuseStep 5151385 = 3863539) B3863539
theorem B335195 : Blo 147793 335195 := bstep (se 1 (by rfl) ⟨251396, by rfl⟩ : syracuseStep 335195 = 502793) B502793
theorem B335231 : Blo 147793 335231 := bstep (se 1 (by rfl) ⟨251423, by rfl⟩ : syracuseStep 335231 = 502847) B502847
theorem B335969 : Blo 147793 335969 := bstep (se 2 (by rfl) ⟨125988, by rfl⟩ : syracuseStep 335969 = 251977) B251977
theorem B762047 : Blo 147793 762047 := bstep (se 1 (by rfl) ⟨571535, by rfl⟩ : syracuseStep 762047 = 1143071) B1143071
theorem B336527 : Blo 147793 336527 := bstep (se 1 (by rfl) ⟨252395, by rfl⟩ : syracuseStep 336527 = 504791) B504791
theorem B336761 : Blo 147793 336761 := bstep (se 2 (by rfl) ⟨126285, by rfl⟩ : syracuseStep 336761 = 252571) B252571
theorem B11183123 : Blo 147793 11183123 := bstep (se 1 (by rfl) ⟨8387342, by rfl⟩ : syracuseStep 11183123 = 16774685) B16774685
theorem B337121 : Blo 147793 337121 := bstep (se 2 (by rfl) ⟨126420, by rfl⟩ : syracuseStep 337121 = 252841) B252841
theorem B337193 : Blo 147793 337193 := bstep (se 2 (by rfl) ⟨126447, by rfl⟩ : syracuseStep 337193 = 252895) B252895
theorem B566585 : Blo 147793 566585 := bstep (se 2 (by rfl) ⟨212469, by rfl⟩ : syracuseStep 566585 = 424939) B424939
theorem B861839 : Blo 147793 861839 := bstep (se 1 (by rfl) ⟨646379, by rfl⟩ : syracuseStep 861839 = 1292759) B1292759
theorem B337787 : Blo 147793 337787 := bstep (se 1 (by rfl) ⟨253340, by rfl⟩ : syracuseStep 337787 = 506681) B506681
theorem B338057 : Blo 147793 338057 := bstep (se 2 (by rfl) ⟨126771, by rfl⟩ : syracuseStep 338057 = 253543) B253543
theorem B338363 : Blo 147793 338363 := bstep (se 1 (by rfl) ⟨253772, by rfl⟩ : syracuseStep 338363 = 507545) B507545
theorem B568043 : Blo 147793 568043 := bstep (se 1 (by rfl) ⟨426032, by rfl⟩ : syracuseStep 568043 = 852065) B852065
theorem B339119 : Blo 147793 339119 := bstep (se 1 (by rfl) ⟨254339, by rfl⟩ : syracuseStep 339119 = 508679) B508679
theorem B339263 : Blo 147793 339263 := bstep (se 1 (by rfl) ⟨254447, by rfl⟩ : syracuseStep 339263 = 508895) B508895
theorem B339407 : Blo 147793 339407 := bstep (se 1 (by rfl) ⟨254555, by rfl⟩ : syracuseStep 339407 = 509111) B509111
theorem B339839 : Blo 147793 339839 := bstep (se 1 (by rfl) ⟨254879, by rfl⟩ : syracuseStep 339839 = 509759) B509759
theorem B864229 : Blo 147793 864229 := bstep (se 4 (by rfl) ⟨81021, by rfl⟩ : syracuseStep 864229 = 162043) B162043
theorem B765935 : Blo 147793 765935 := bstep (se 1 (by rfl) ⟨574451, by rfl⟩ : syracuseStep 765935 = 1148903) B1148903
theorem B1225199 : Blo 147793 1225199 := bstep (se 1 (by rfl) ⟨918899, by rfl⟩ : syracuseStep 1225199 = 1837799) B1837799
theorem B340667 : Blo 147793 340667 := bstep (se 1 (by rfl) ⟨255500, by rfl⟩ : syracuseStep 340667 = 511001) B511001
theorem B5747435 : Blo 147793 5747435 := bstep (se 1 (by rfl) ⟨4310576, by rfl⟩ : syracuseStep 5747435 = 8621153) B8621153
theorem B3257333 : Blo 147793 3257333 := bstep (se 5 (by rfl) ⟨152687, by rfl⟩ : syracuseStep 3257333 = 305375) B305375
theorem B570577 : Blo 147793 570577 := bstep (se 2 (by rfl) ⟨213966, by rfl⟩ : syracuseStep 570577 = 427933) B427933
theorem B177643 : Blo 147793 177643 := bstep (se 1 (by rfl) ⟨133232, by rfl⟩ : syracuseStep 177643 = 266465) B266465
theorem B636623 : Blo 147793 636623 := bstep (se 1 (by rfl) ⟨477467, by rfl⟩ : syracuseStep 636623 = 954935) B954935
theorem B374503 : Blo 147793 374503 := bstep (se 1 (by rfl) ⟨280877, by rfl⟩ : syracuseStep 374503 = 561755) B561755
theorem B5027777 : Blo 147793 5027777 := bstep (se 2 (by rfl) ⟨1885416, by rfl⟩ : syracuseStep 5027777 = 3770833) B3770833
theorem B1423327 : Blo 147793 1423327 := bstep (se 1 (by rfl) ⟨1067495, by rfl⟩ : syracuseStep 1423327 = 2134991) B2134991
theorem B571643 : Blo 147793 571643 := bstep (se 1 (by rfl) ⟨428732, by rfl⟩ : syracuseStep 571643 = 857465) B857465
theorem B1359017 : Blo 147793 1359017 := bstep (se 2 (by rfl) ⟨509631, by rfl⟩ : syracuseStep 1359017 = 1019263) B1019263
theorem B148015 : Blo 147793 148015 := bstep (se 1 (by rfl) ⟨111011, by rfl⟩ : syracuseStep 148015 = 222023) B222023
theorem B148059 : Blo 147793 148059 := bstep (se 1 (by rfl) ⟨111044, by rfl⟩ : syracuseStep 148059 = 222089) B222089
theorem B148123 : Blo 147793 148123 := bstep (se 1 (by rfl) ⟨111092, by rfl⟩ : syracuseStep 148123 = 222185) B222185
theorem B148287 : Blo 147793 148287 := bstep (se 1 (by rfl) ⟨111215, by rfl⟩ : syracuseStep 148287 = 222431) B222431
theorem B148415 : Blo 147793 148415 := bstep (se 1 (by rfl) ⟨111311, by rfl⟩ : syracuseStep 148415 = 222623) B222623
theorem B148447 : Blo 147793 148447 := bstep (se 1 (by rfl) ⟨111335, by rfl⟩ : syracuseStep 148447 = 222671) B222671
theorem B148571 : Blo 147793 148571 := bstep (se 1 (by rfl) ⟨111428, by rfl⟩ : syracuseStep 148571 = 222857) B222857
theorem B148607 : Blo 147793 148607 := bstep (se 1 (by rfl) ⟨111455, by rfl⟩ : syracuseStep 148607 = 222911) B222911
theorem B378017 : Blo 147793 378017 := bstep (se 2 (by rfl) ⟨141756, by rfl⟩ : syracuseStep 378017 = 283513) B283513
theorem B279713 : Blo 147793 279713 := bstep (se 2 (by rfl) ⟨104892, by rfl⟩ : syracuseStep 279713 = 209785) B209785
theorem B379019 : Blo 147793 379019 := bstep (se 1 (by rfl) ⟨284264, by rfl⟩ : syracuseStep 379019 = 568529) B568529
theorem B1951897 : Blo 147793 1951897 := bstep (se 2 (by rfl) ⟨731961, by rfl⟩ : syracuseStep 1951897 = 1463923) B1463923
theorem B805295 : Blo 147793 805295 := bstep (se 1 (by rfl) ⟨603971, by rfl⟩ : syracuseStep 805295 = 1207943) B1207943
theorem B149951 : Blo 147793 149951 := bstep (se 1 (by rfl) ⟨112463, by rfl⟩ : syracuseStep 149951 = 224927) B224927
theorem B510731 : Blo 147793 510731 := bstep (se 1 (by rfl) ⟨383048, by rfl⟩ : syracuseStep 510731 = 766097) B766097
theorem B1133351 : Blo 147793 1133351 := bstep (se 1 (by rfl) ⟨850013, by rfl⟩ : syracuseStep 1133351 = 1700027) B1700027
theorem B576335 : Blo 147793 576335 := bstep (se 1 (by rfl) ⟨432251, by rfl⟩ : syracuseStep 576335 = 864503) B864503
theorem B150463 : Blo 147793 150463 := bstep (se 1 (by rfl) ⟨112847, by rfl⟩ : syracuseStep 150463 = 225695) B225695
theorem B150559 : Blo 147793 150559 := bstep (se 1 (by rfl) ⟨112919, by rfl⟩ : syracuseStep 150559 = 225839) B225839
theorem B674941 : Blo 147793 674941 := bstep (se 3 (by rfl) ⟨126551, by rfl⟩ : syracuseStep 674941 = 253103) B253103
theorem B511163 : Blo 147793 511163 := bstep (se 1 (by rfl) ⟨383372, by rfl⟩ : syracuseStep 511163 = 766745) B766745
theorem B380335 : Blo 147793 380335 := bstep (se 1 (by rfl) ⟨285251, by rfl⟩ : syracuseStep 380335 = 570503) B570503
theorem B151195 : Blo 147793 151195 := bstep (se 1 (by rfl) ⟨113396, by rfl⟩ : syracuseStep 151195 = 226793) B226793
theorem B151643 : Blo 147793 151643 := bstep (se 1 (by rfl) ⟨113732, by rfl⟩ : syracuseStep 151643 = 227465) B227465
theorem B151719 : Blo 147793 151719 := bstep (se 1 (by rfl) ⟨113789, by rfl⟩ : syracuseStep 151719 = 227579) B227579
theorem B774335 : Blo 147793 774335 := bstep (se 1 (by rfl) ⟨580751, by rfl⟩ : syracuseStep 774335 = 1161503) B1161503
theorem B151775 : Blo 147793 151775 := bstep (se 1 (by rfl) ⟨113831, by rfl⟩ : syracuseStep 151775 = 227663) B227663
theorem B1168361 : Blo 147793 1168361 := bstep (se 2 (by rfl) ⟨438135, by rfl⟩ : syracuseStep 1168361 = 876271) B876271
theorem B1627303 : Blo 147793 1627303 := bstep (se 1 (by rfl) ⟨1220477, by rfl⟩ : syracuseStep 1627303 = 2440955) B2440955
theorem B1726271 : Blo 147793 1726271 := bstep (se 1 (by rfl) ⟨1294703, by rfl⟩ : syracuseStep 1726271 = 2589407) B2589407
theorem B842177 : Blo 147793 842177 := bstep (se 2 (by rfl) ⟨315816, by rfl⟩ : syracuseStep 842177 = 631633) B631633
theorem B481751 : Blo 147793 481751 := bstep (se 1 (by rfl) ⟨361313, by rfl⟩ : syracuseStep 481751 = 722627) B722627
theorem B1694195 : Blo 147793 1694195 := bstep (se 1 (by rfl) ⟨1270646, by rfl⟩ : syracuseStep 1694195 = 2541293) B2541293
theorem B318107 : Blo 147793 318107 := bstep (se 1 (by rfl) ⟨238580, by rfl⟩ : syracuseStep 318107 = 477161) B477161
theorem B1628923 : Blo 147793 1628923 := bstep (se 1 (by rfl) ⟨1221692, by rfl⟩ : syracuseStep 1628923 = 2443385) B2443385
theorem B252713 : Blo 147793 252713 := bstep (se 2 (by rfl) ⟨94767, by rfl⟩ : syracuseStep 252713 = 189535) B189535
theorem B613183 : Blo 147793 613183 := bstep (se 1 (by rfl) ⟨459887, by rfl⟩ : syracuseStep 613183 = 919775) B919775
theorem B2252405 : Blo 147793 2252405 := bstep (se 5 (by rfl) ⟨105581, by rfl⟩ : syracuseStep 2252405 = 211163) B211163
theorem B18341639 : Blo 147793 18341639 := bstep (se 1 (by rfl) ⟨13756229, by rfl⟩ : syracuseStep 18341639 = 27512459) B27512459
theorem B253759 : Blo 147793 253759 := bstep (se 1 (by rfl) ⟨190319, by rfl⟩ : syracuseStep 253759 = 380639) B380639
theorem B1040215 : Blo 147793 1040215 := bstep (se 1 (by rfl) ⟨780161, by rfl⟩ : syracuseStep 1040215 = 1560323) B1560323
theorem B516007 : Blo 147793 516007 := bstep (se 1 (by rfl) ⟨387005, by rfl⟩ : syracuseStep 516007 = 774011) B774011
theorem B188831 : Blo 147793 188831 := bstep (se 1 (by rfl) ⟨141623, by rfl⟩ : syracuseStep 188831 = 283247) B283247
theorem B287135 : Blo 147793 287135 := bstep (se 1 (by rfl) ⟨215351, by rfl⟩ : syracuseStep 287135 = 430703) B430703
theorem B254623 : Blo 147793 254623 := bstep (se 1 (by rfl) ⟨190967, by rfl⟩ : syracuseStep 254623 = 381935) B381935
theorem B143123705 : Blo 147793 143123705 := bstep (se 2 (by rfl) ⟨53671389, by rfl⟩ : syracuseStep 143123705 = 107342779) B107342779
theorem B222491 : Blo 147793 222491 := bstep (se 1 (by rfl) ⟨166868, by rfl⟩ : syracuseStep 222491 = 333737) B333737
theorem B190279 : Blo 147793 190279 := bstep (se 1 (by rfl) ⟨142709, by rfl⟩ : syracuseStep 190279 = 285419) B285419
theorem B223067 : Blo 147793 223067 := bstep (se 1 (by rfl) ⟨167300, by rfl⟩ : syracuseStep 223067 = 334601) B334601
theorem B485729 : Blo 147793 485729 := bstep (se 2 (by rfl) ⟨182148, by rfl⟩ : syracuseStep 485729 = 364297) B364297
theorem B223721 : Blo 147793 223721 := bstep (se 2 (by rfl) ⟨83895, by rfl⟩ : syracuseStep 223721 = 167791) B167791
theorem B224027 : Blo 147793 224027 := bstep (se 1 (by rfl) ⟨168020, by rfl⟩ : syracuseStep 224027 = 336041) B336041
theorem B1141613 : Blo 147793 1141613 := bstep (se 3 (by rfl) ⟨214052, by rfl⟩ : syracuseStep 1141613 = 428105) B428105
theorem B1371161 : Blo 147793 1371161 := bstep (se 2 (by rfl) ⟨514185, by rfl⟩ : syracuseStep 1371161 = 1028371) B1028371
theorem B224639 : Blo 147793 224639 := bstep (se 1 (by rfl) ⟨168479, by rfl⟩ : syracuseStep 224639 = 336959) B336959
theorem B847259 : Blo 147793 847259 := bstep (se 1 (by rfl) ⟨635444, by rfl⟩ : syracuseStep 847259 = 1270889) B1270889
theorem B224879 : Blo 147793 224879 := bstep (se 1 (by rfl) ⟨168659, by rfl⟩ : syracuseStep 224879 = 337319) B337319
theorem B716471 : Blo 147793 716471 := bstep (se 1 (by rfl) ⟨537353, by rfl⟩ : syracuseStep 716471 = 1074707) B1074707
theorem B1274201 : Blo 147793 1274201 := bstep (se 2 (by rfl) ⟨477825, by rfl⟩ : syracuseStep 1274201 = 955651) B955651
theorem B225767 : Blo 147793 225767 := bstep (se 1 (by rfl) ⟨169325, by rfl⟩ : syracuseStep 225767 = 338651) B338651
theorem B225959 : Blo 147793 225959 := bstep (se 1 (by rfl) ⟨169469, by rfl⟩ : syracuseStep 225959 = 338939) B338939
theorem B226103 : Blo 147793 226103 := bstep (se 1 (by rfl) ⟨169577, by rfl⟩ : syracuseStep 226103 = 339155) B339155
theorem B2749393 : Blo 147793 2749393 := bstep (se 2 (by rfl) ⟨1031022, by rfl⟩ : syracuseStep 2749393 = 2062045) B2062045
theorem B226415 : Blo 147793 226415 := bstep (se 1 (by rfl) ⟨169811, by rfl⟩ : syracuseStep 226415 = 339623) B339623
theorem B4945049 : Blo 147793 4945049 := bstep (se 2 (by rfl) ⟨1854393, by rfl⟩ : syracuseStep 4945049 = 3708787) B3708787
theorem B1275263 : Blo 147793 1275263 := bstep (se 1 (by rfl) ⟨956447, by rfl⟩ : syracuseStep 1275263 = 1912895) B1912895
theorem B718415 : Blo 147793 718415 := bstep (se 1 (by rfl) ⟨538811, by rfl⟩ : syracuseStep 718415 = 1077623) B1077623
theorem B161471 : Blo 147793 161471 := bstep (se 1 (by rfl) ⟨121103, by rfl⟩ : syracuseStep 161471 = 242207) B242207
theorem B227195 : Blo 147793 227195 := bstep (se 1 (by rfl) ⟨170396, by rfl⟩ : syracuseStep 227195 = 340793) B340793
theorem B227435 : Blo 147793 227435 := bstep (se 1 (by rfl) ⟨170576, by rfl⟩ : syracuseStep 227435 = 341153) B341153
theorem B15759521 : Blo 147793 15759521 := bstep (se 2 (by rfl) ⟨5909820, by rfl⟩ : syracuseStep 15759521 = 11819641) B11819641
theorem B227567 : Blo 147793 227567 := bstep (se 1 (by rfl) ⟨170675, by rfl⟩ : syracuseStep 227567 = 341351) B341351
theorem B1932011 : Blo 147793 1932011 := bstep (se 1 (by rfl) ⟨1449008, by rfl⟩ : syracuseStep 1932011 = 2898017) B2898017
theorem B752489 : Blo 147793 752489 := bstep (se 2 (by rfl) ⟨282183, by rfl⟩ : syracuseStep 752489 = 564367) B564367
theorem B228347 : Blo 147793 228347 := bstep (se 1 (by rfl) ⟨171260, by rfl⟩ : syracuseStep 228347 = 342521) B342521
theorem B2032219 : Blo 147793 2032219 := bstep (se 1 (by rfl) ⟨1524164, by rfl⟩ : syracuseStep 2032219 = 3048329) B3048329
theorem B755567 : Blo 147793 755567 := bstep (se 1 (by rfl) ⟨566675, by rfl⟩ : syracuseStep 755567 = 1133351) B1133351
theorem B17697923 : Blo 147793 17697923 := bstep (se 1 (by rfl) ⟨13273442, by rfl⟩ : syracuseStep 17697923 = 26546885) B26546885
theorem B1150847 : Blo 147793 1150847 := bstep (se 1 (by rfl) ⟨863135, by rfl⟩ : syracuseStep 1150847 = 1726271) B1726271
theorem B561451 : Blo 147793 561451 := bstep (se 1 (by rfl) ⟨421088, by rfl⟩ : syracuseStep 561451 = 842177) B842177
theorem B430589 : Blo 147793 430589 := bstep (se 3 (by rfl) ⟨80735, by rfl⟩ : syracuseStep 430589 = 161471) B161471
theorem B168475 : Blo 147793 168475 := bstep (se 1 (by rfl) ⟨126356, by rfl⟩ : syracuseStep 168475 = 252713) B252713
theorem B12227759 : Blo 147793 12227759 := bstep (se 1 (by rfl) ⟨9170819, by rfl⟩ : syracuseStep 12227759 = 18341639) B18341639
theorem B1152305 : Blo 147793 1152305 := bstep (se 2 (by rfl) ⟨432114, by rfl⟩ : syracuseStep 1152305 = 864229) B864229
theorem B15472457 : Blo 147793 15472457 := bstep (se 2 (by rfl) ⟨5802171, by rfl⟩ : syracuseStep 15472457 = 11604343) B11604343
theorem B2169737 : Blo 147793 2169737 := bstep (se 2 (by rfl) ⟨813651, by rfl⟩ : syracuseStep 2169737 = 1627303) B1627303
theorem B760769 : Blo 147793 760769 := bstep (se 2 (by rfl) ⟨285288, by rfl⟩ : syracuseStep 760769 = 570577) B570577
theorem B761075 : Blo 147793 761075 := bstep (se 1 (by rfl) ⟨570806, by rfl⟩ : syracuseStep 761075 = 1141613) B1141613
theorem B236857 : Blo 147793 236857 := bstep (se 2 (by rfl) ⟨88821, by rfl⟩ : syracuseStep 236857 = 177643) B177643
theorem B564839 : Blo 147793 564839 := bstep (se 1 (by rfl) ⟨423629, by rfl⟩ : syracuseStep 564839 = 847259) B847259
theorem B499337 : Blo 147793 499337 := bstep (se 2 (by rfl) ⟨187251, by rfl⟩ : syracuseStep 499337 = 374503) B374503
theorem B2171555 : Blo 147793 2171555 := bstep (se 1 (by rfl) ⟨1628666, by rfl⟩ : syracuseStep 2171555 = 3257333) B3257333
theorem B2171897 : Blo 147793 2171897 := bstep (se 2 (by rfl) ⟨814461, by rfl⟩ : syracuseStep 2171897 = 1628923) B1628923
theorem B3351851 : Blo 147793 3351851 := bstep (se 1 (by rfl) ⟨2513888, by rfl⟩ : syracuseStep 3351851 = 5027777) B5027777
theorem B6006413 : Blo 147793 6006413 := bstep (se 3 (by rfl) ⟨1126202, by rfl⟩ : syracuseStep 6006413 = 2252405) B2252405
theorem B1288007 : Blo 147793 1288007 := bstep (se 1 (by rfl) ⟨966005, by rfl⟩ : syracuseStep 1288007 = 1932011) B1932011
theorem B501659 : Blo 147793 501659 := bstep (se 1 (by rfl) ⟨376244, by rfl⟩ : syracuseStep 501659 = 752489) B752489
theorem B338345 : Blo 147793 338345 := bstep (se 2 (by rfl) ⟨126879, by rfl⟩ : syracuseStep 338345 = 253759) B253759
theorem B1386953 : Blo 147793 1386953 := bstep (se 2 (by rfl) ⟨520107, by rfl⟩ : syracuseStep 1386953 = 1040215) B1040215
theorem B339497 : Blo 147793 339497 := bstep (se 2 (by rfl) ⟨127311, by rfl⟩ : syracuseStep 339497 = 254623) B254623
theorem B503549 : Blo 147793 503549 := bstep (se 3 (by rfl) ⟨94415, by rfl⟩ : syracuseStep 503549 = 188831) B188831
theorem B1224679 : Blo 147793 1224679 := bstep (se 1 (by rfl) ⟨918509, by rfl⟩ : syracuseStep 1224679 = 1837019) B1837019
theorem B536863 : Blo 147793 536863 := bstep (se 1 (by rfl) ⟨402647, by rfl⟩ : syracuseStep 536863 = 805295) B805295
theorem B504143 : Blo 147793 504143 := bstep (se 1 (by rfl) ⟨378107, by rfl⟩ : syracuseStep 504143 = 756215) B756215
theorem B504251 : Blo 147793 504251 := bstep (se 1 (by rfl) ⟨378188, by rfl⟩ : syracuseStep 504251 = 756377) B756377
theorem B340487 : Blo 147793 340487 := bstep (se 1 (by rfl) ⟨255365, by rfl⟩ : syracuseStep 340487 = 510731) B510731
theorem B438889 : Blo 147793 438889 := bstep (se 2 (by rfl) ⟨164583, by rfl⟩ : syracuseStep 438889 = 329167) B329167
theorem B340775 : Blo 147793 340775 := bstep (se 1 (by rfl) ⟨255581, by rfl⟩ : syracuseStep 340775 = 511163) B511163
theorem B570199 : Blo 147793 570199 := bstep (se 1 (by rfl) ⟨427649, by rfl⟩ : syracuseStep 570199 = 855299) B855299
theorem B505115 : Blo 147793 505115 := bstep (se 1 (by rfl) ⟨378836, by rfl⟩ : syracuseStep 505115 = 757673) B757673
theorem B2602529 : Blo 147793 2602529 := bstep (se 2 (by rfl) ⟨975948, by rfl⟩ : syracuseStep 2602529 = 1951897) B1951897
theorem B572129 : Blo 147793 572129 := bstep (se 2 (by rfl) ⟨214548, by rfl⟩ : syracuseStep 572129 = 429097) B429097
theorem B899921 : Blo 147793 899921 := bstep (se 2 (by rfl) ⟨337470, by rfl⟩ : syracuseStep 899921 = 674941) B674941
theorem B506735 : Blo 147793 506735 := bstep (se 1 (by rfl) ⟨380051, by rfl⟩ : syracuseStep 506735 = 760103) B760103
theorem B1129463 : Blo 147793 1129463 := bstep (se 1 (by rfl) ⟨847097, by rfl⟩ : syracuseStep 1129463 = 1694195) B1694195
theorem B1293407 : Blo 147793 1293407 := bstep (se 1 (by rfl) ⟨970055, by rfl⟩ : syracuseStep 1293407 = 1940111) B1940111
theorem B212071 : Blo 147793 212071 := bstep (se 1 (by rfl) ⟨159053, by rfl⟩ : syracuseStep 212071 = 318107) B318107
theorem B507113 : Blo 147793 507113 := bstep (se 2 (by rfl) ⟨190167, by rfl⟩ : syracuseStep 507113 = 380335) B380335
theorem B508031 : Blo 147793 508031 := bstep (se 1 (by rfl) ⟨381023, by rfl⟩ : syracuseStep 508031 = 762047) B762047
theorem B836185 : Blo 147793 836185 := bstep (se 2 (by rfl) ⟨313569, by rfl⟩ : syracuseStep 836185 = 627139) B627139
theorem B7455415 : Blo 147793 7455415 := bstep (se 1 (by rfl) ⟨5591561, by rfl⟩ : syracuseStep 7455415 = 11183123) B11183123
theorem B148327 : Blo 147793 148327 := bstep (se 1 (by rfl) ⟨111245, by rfl⟩ : syracuseStep 148327 = 222491) B222491
theorem B377723 : Blo 147793 377723 := bstep (se 1 (by rfl) ⟨283292, by rfl⟩ : syracuseStep 377723 = 566585) B566585
theorem B574559 : Blo 147793 574559 := bstep (se 1 (by rfl) ⟨430919, by rfl⟩ : syracuseStep 574559 = 861839) B861839
theorem B148711 : Blo 147793 148711 := bstep (se 1 (by rfl) ⟨111533, by rfl⟩ : syracuseStep 148711 = 223067) B223067
theorem B149147 : Blo 147793 149147 := bstep (se 1 (by rfl) ⟨111860, by rfl⟩ : syracuseStep 149147 = 223721) B223721
theorem B378695 : Blo 147793 378695 := bstep (se 1 (by rfl) ⟨284021, by rfl⟩ : syracuseStep 378695 = 568043) B568043
theorem B149351 : Blo 147793 149351 := bstep (se 1 (by rfl) ⟨112013, by rfl⟩ : syracuseStep 149351 = 224027) B224027
theorem B149759 : Blo 147793 149759 := bstep (se 1 (by rfl) ⟨112319, by rfl⟩ : syracuseStep 149759 = 224639) B224639
theorem B149919 : Blo 147793 149919 := bstep (se 1 (by rfl) ⟨112439, by rfl⟩ : syracuseStep 149919 = 224879) B224879
theorem B477647 : Blo 147793 477647 := bstep (se 1 (by rfl) ⟨358235, by rfl⟩ : syracuseStep 477647 = 716471) B716471
theorem B510623 : Blo 147793 510623 := bstep (se 1 (by rfl) ⟨382967, by rfl⟩ : syracuseStep 510623 = 765935) B765935
theorem B150511 : Blo 147793 150511 := bstep (se 1 (by rfl) ⟨112883, by rfl⟩ : syracuseStep 150511 = 225767) B225767
theorem B150639 : Blo 147793 150639 := bstep (se 1 (by rfl) ⟨112979, by rfl⟩ : syracuseStep 150639 = 225959) B225959
theorem B150735 : Blo 147793 150735 := bstep (se 1 (by rfl) ⟨113051, by rfl⟩ : syracuseStep 150735 = 226103) B226103
theorem B2149753 : Blo 147793 2149753 := bstep (se 2 (by rfl) ⟨806157, by rfl⟩ : syracuseStep 2149753 = 1612315) B1612315
theorem B150943 : Blo 147793 150943 := bstep (se 1 (by rfl) ⟨113207, by rfl⟩ : syracuseStep 150943 = 226415) B226415
theorem B3296699 : Blo 147793 3296699 := bstep (se 1 (by rfl) ⟨2472524, by rfl⟩ : syracuseStep 3296699 = 4945049) B4945049
theorem B6868513 : Blo 147793 6868513 := bstep (se 2 (by rfl) ⟨2575692, by rfl⟩ : syracuseStep 6868513 = 5151385) B5151385
theorem B478943 : Blo 147793 478943 := bstep (se 1 (by rfl) ⟨359207, by rfl⟩ : syracuseStep 478943 = 718415) B718415
theorem B151463 : Blo 147793 151463 := bstep (se 1 (by rfl) ⟨113597, by rfl⟩ : syracuseStep 151463 = 227195) B227195
theorem B151623 : Blo 147793 151623 := bstep (se 1 (by rfl) ⟨113717, by rfl⟩ : syracuseStep 151623 = 227435) B227435
theorem B10506347 : Blo 147793 10506347 := bstep (se 1 (by rfl) ⟨7879760, by rfl⟩ : syracuseStep 10506347 = 15759521) B15759521
theorem B151711 : Blo 147793 151711 := bstep (se 1 (by rfl) ⟨113783, by rfl⟩ : syracuseStep 151711 = 227567) B227567
theorem B381095 : Blo 147793 381095 := bstep (se 1 (by rfl) ⟨285821, by rfl⟩ : syracuseStep 381095 = 571643) B571643
theorem B152231 : Blo 147793 152231 := bstep (se 1 (by rfl) ⟨114173, by rfl⟩ : syracuseStep 152231 = 228347) B228347
theorem B906011 : Blo 147793 906011 := bstep (se 1 (by rfl) ⟨679508, by rfl⟩ : syracuseStep 906011 = 1359017) B1359017
theorem B1660283 : Blo 147793 1660283 := bstep (se 1 (by rfl) ⟨1245212, by rfl⟩ : syracuseStep 1660283 = 2490425) B2490425
theorem B252011 : Blo 147793 252011 := bstep (se 1 (by rfl) ⟨189008, by rfl⟩ : syracuseStep 252011 = 378017) B378017
theorem B186475 : Blo 147793 186475 := bstep (se 1 (by rfl) ⟨139856, by rfl⟩ : syracuseStep 186475 = 279713) B279713
theorem B612535 : Blo 147793 612535 := bstep (se 1 (by rfl) ⟨459401, by rfl⟩ : syracuseStep 612535 = 918803) B918803
theorem B252679 : Blo 147793 252679 := bstep (se 1 (by rfl) ⟨189509, by rfl⟩ : syracuseStep 252679 = 379019) B379019
theorem B384223 : Blo 147793 384223 := bstep (se 1 (by rfl) ⟨288167, by rfl⟩ : syracuseStep 384223 = 576335) B576335
theorem B253705 : Blo 147793 253705 := bstep (se 2 (by rfl) ⟨95139, by rfl⟩ : syracuseStep 253705 = 190279) B190279
theorem B516223 : Blo 147793 516223 := bstep (se 1 (by rfl) ⟨387167, by rfl⟩ : syracuseStep 516223 = 774335) B774335
theorem B778907 : Blo 147793 778907 := bstep (se 1 (by rfl) ⟨584180, by rfl⟩ : syracuseStep 778907 = 1168361) B1168361
theorem B222335 : Blo 147793 222335 := bstep (se 1 (by rfl) ⟨166751, by rfl⟩ : syracuseStep 222335 = 333503) B333503
theorem B222473 : Blo 147793 222473 := bstep (se 2 (by rfl) ⟨83427, by rfl⟩ : syracuseStep 222473 = 166855) B166855
theorem B321167 : Blo 147793 321167 := bstep (se 1 (by rfl) ⟨240875, by rfl⟩ : syracuseStep 321167 = 481751) B481751
theorem B222953 : Blo 147793 222953 := bstep (se 2 (by rfl) ⟨83607, by rfl⟩ : syracuseStep 222953 = 167215) B167215
theorem B223463 : Blo 147793 223463 := bstep (se 1 (by rfl) ⟨167597, by rfl⟩ : syracuseStep 223463 = 335195) B335195
theorem B223487 : Blo 147793 223487 := bstep (se 1 (by rfl) ⟨167615, by rfl⟩ : syracuseStep 223487 = 335231) B335231
theorem B223979 : Blo 147793 223979 := bstep (se 1 (by rfl) ⟨167984, by rfl⟩ : syracuseStep 223979 = 335969) B335969
theorem B191423 : Blo 147793 191423 := bstep (se 1 (by rfl) ⟨143567, by rfl⟩ : syracuseStep 191423 = 287135) B287135
theorem B224351 : Blo 147793 224351 := bstep (se 1 (by rfl) ⟨168263, by rfl⟩ : syracuseStep 224351 = 336527) B336527
theorem B224507 : Blo 147793 224507 := bstep (se 1 (by rfl) ⟨168380, by rfl⟩ : syracuseStep 224507 = 336761) B336761
theorem B224747 : Blo 147793 224747 := bstep (se 1 (by rfl) ⟨168560, by rfl⟩ : syracuseStep 224747 = 337121) B337121
theorem B95415803 : Blo 147793 95415803 := bstep (se 1 (by rfl) ⟨71561852, by rfl⟩ : syracuseStep 95415803 = 143123705) B143123705
theorem B224795 : Blo 147793 224795 := bstep (se 1 (by rfl) ⟨168596, by rfl⟩ : syracuseStep 224795 = 337193) B337193
theorem B224873 : Blo 147793 224873 := bstep (se 2 (by rfl) ⟨84327, by rfl⟩ : syracuseStep 224873 = 168655) B168655
theorem B225191 : Blo 147793 225191 := bstep (se 1 (by rfl) ⟨168893, by rfl⟩ : syracuseStep 225191 = 337787) B337787
theorem B3665857 : Blo 147793 3665857 := bstep (se 2 (by rfl) ⟨1374696, by rfl⟩ : syracuseStep 3665857 = 2749393) B2749393
theorem B225371 : Blo 147793 225371 := bstep (se 1 (by rfl) ⟨169028, by rfl⟩ : syracuseStep 225371 = 338057) B338057
theorem B323819 : Blo 147793 323819 := bstep (se 1 (by rfl) ⟨242864, by rfl⟩ : syracuseStep 323819 = 485729) B485729
theorem B225575 : Blo 147793 225575 := bstep (se 1 (by rfl) ⟨169181, by rfl⟩ : syracuseStep 225575 = 338363) B338363
theorem B914107 : Blo 147793 914107 := bstep (se 1 (by rfl) ⟨685580, by rfl⟩ : syracuseStep 914107 = 1371161) B1371161
theorem B226079 : Blo 147793 226079 := bstep (se 1 (by rfl) ⟨169559, by rfl⟩ : syracuseStep 226079 = 339119) B339119
theorem B226175 : Blo 147793 226175 := bstep (se 1 (by rfl) ⟨169631, by rfl⟩ : syracuseStep 226175 = 339263) B339263
theorem B226217 : Blo 147793 226217 := bstep (se 2 (by rfl) ⟨84831, by rfl⟩ : syracuseStep 226217 = 169663) B169663
theorem B226271 : Blo 147793 226271 := bstep (se 1 (by rfl) ⟨169703, by rfl⟩ : syracuseStep 226271 = 339407) B339407
theorem B226559 : Blo 147793 226559 := bstep (se 1 (by rfl) ⟨169919, by rfl⟩ : syracuseStep 226559 = 339839) B339839
theorem B1897769 : Blo 147793 1897769 := bstep (se 2 (by rfl) ⟨711663, by rfl⟩ : syracuseStep 1897769 = 1423327) B1423327
theorem B849467 : Blo 147793 849467 := bstep (se 1 (by rfl) ⟨637100, by rfl⟩ : syracuseStep 849467 = 1274201) B1274201
theorem B816799 : Blo 147793 816799 := bstep (se 1 (by rfl) ⟨612599, by rfl⟩ : syracuseStep 816799 = 1225199) B1225199
theorem B227111 : Blo 147793 227111 := bstep (se 1 (by rfl) ⟨170333, by rfl⟩ : syracuseStep 227111 = 340667) B340667
theorem B3831623 : Blo 147793 3831623 := bstep (se 1 (by rfl) ⟨2873717, by rfl⟩ : syracuseStep 3831623 = 5747435) B5747435
theorem B850175 : Blo 147793 850175 := bstep (se 1 (by rfl) ⟨637631, by rfl⟩ : syracuseStep 850175 = 1275263) B1275263
theorem B817577 : Blo 147793 817577 := bstep (se 2 (by rfl) ⟨306591, by rfl⟩ : syracuseStep 817577 = 613183) B613183
theorem B424415 : Blo 147793 424415 := bstep (se 1 (by rfl) ⟨318311, by rfl⟩ : syracuseStep 424415 = 636623) B636623
theorem B688009 : Blo 147793 688009 := bstep (se 2 (by rfl) ⟨258003, by rfl⟩ : syracuseStep 688009 = 516007) B516007
theorem B688297 : Blo 147793 688297 := bstep (se 2 (by rfl) ⟨258111, by rfl⟩ : syracuseStep 688297 = 516223) B516223
theorem B1114913 : Blo 147793 1114913 := bstep (se 2 (by rfl) ⟨418092, by rfl⟩ : syracuseStep 1114913 = 836185) B836185
theorem B11798615 : Blo 147793 11798615 := bstep (se 1 (by rfl) ⟨8848961, by rfl⟩ : syracuseStep 11798615 = 17697923) B17697923
theorem B2197799 : Blo 147793 2197799 := bstep (se 1 (by rfl) ⟨1648349, by rfl⟩ : syracuseStep 2197799 = 3296699) B3296699
theorem B168007 : Blo 147793 168007 := bstep (se 1 (by rfl) ⟨126005, by rfl⟩ : syracuseStep 168007 = 252011) B252011
theorem B1446491 : Blo 147793 1446491 := bstep (se 1 (by rfl) ⟨1084868, by rfl⟩ : syracuseStep 1446491 = 2169737) B2169737
theorem B332891 : Blo 147793 332891 := bstep (se 1 (by rfl) ⟨249668, by rfl⟩ : syracuseStep 332891 = 499337) B499337
theorem B4887809 : Blo 147793 4887809 := bstep (se 2 (by rfl) ⟨1832928, by rfl⟩ : syracuseStep 4887809 = 3665857) B3665857
theorem B1447703 : Blo 147793 1447703 := bstep (se 1 (by rfl) ⟨1085777, by rfl⟩ : syracuseStep 1447703 = 2171555) B2171555
theorem B1447931 : Blo 147793 1447931 := bstep (se 1 (by rfl) ⟨1085948, by rfl⟩ : syracuseStep 1447931 = 2171897) B2171897
theorem B2234567 : Blo 147793 2234567 := bstep (se 1 (by rfl) ⟨1675925, by rfl⟩ : syracuseStep 2234567 = 3351851) B3351851
theorem B1218809 : Blo 147793 1218809 := bstep (se 2 (by rfl) ⟨457053, by rfl⟩ : syracuseStep 1218809 = 914107) B914107
theorem B4004275 : Blo 147793 4004275 := bstep (se 1 (by rfl) ⟨3003206, by rfl⟩ : syracuseStep 4004275 = 6006413) B6006413
theorem B760265 : Blo 147793 760265 := bstep (se 2 (by rfl) ⟨285099, by rfl⟩ : syracuseStep 760265 = 570199) B570199
theorem B858671 : Blo 147793 858671 := bstep (se 1 (by rfl) ⟨644003, by rfl⟩ : syracuseStep 858671 = 1288007) B1288007
theorem B334439 : Blo 147793 334439 := bstep (se 1 (by rfl) ⟨250829, by rfl⟩ : syracuseStep 334439 = 501659) B501659
theorem B924635 : Blo 147793 924635 := bstep (se 1 (by rfl) ⟨693476, by rfl⟩ : syracuseStep 924635 = 1386953) B1386953
theorem B1089065 : Blo 147793 1089065 := bstep (se 2 (by rfl) ⟨408399, by rfl⟩ : syracuseStep 1089065 = 816799) B816799
theorem B2399789 : Blo 147793 2399789 := bstep (se 3 (by rfl) ⟨449960, by rfl⟩ : syracuseStep 2399789 = 899921) B899921
theorem B63610535 : Blo 147793 63610535 := bstep (se 1 (by rfl) ⟨47707901, by rfl⟩ : syracuseStep 63610535 = 95415803) B95415803
theorem B335699 : Blo 147793 335699 := bstep (se 1 (by rfl) ⟨251774, by rfl⟩ : syracuseStep 335699 = 503549) B503549
theorem B336095 : Blo 147793 336095 := bstep (se 1 (by rfl) ⟨252071, by rfl⟩ : syracuseStep 336095 = 504143) B504143
theorem B336167 : Blo 147793 336167 := bstep (se 1 (by rfl) ⟨252125, by rfl⟩ : syracuseStep 336167 = 504251) B504251
theorem B336743 : Blo 147793 336743 := bstep (se 1 (by rfl) ⟨252557, by rfl⟩ : syracuseStep 336743 = 505115) B505115
theorem B336905 : Blo 147793 336905 := bstep (se 2 (by rfl) ⟨126339, by rfl⟩ : syracuseStep 336905 = 252679) B252679
theorem B566311 : Blo 147793 566311 := bstep (se 1 (by rfl) ⟨424733, by rfl⟩ : syracuseStep 566311 = 849467) B849467
theorem B566783 : Blo 147793 566783 := bstep (se 1 (by rfl) ⟨425087, by rfl⟩ : syracuseStep 566783 = 850175) B850175
theorem B337823 : Blo 147793 337823 := bstep (se 1 (by rfl) ⟨253367, by rfl⟩ : syracuseStep 337823 = 506735) B506735
theorem B862271 : Blo 147793 862271 := bstep (se 1 (by rfl) ⟨646703, by rfl⟩ : syracuseStep 862271 = 1293407) B1293407
theorem B338075 : Blo 147793 338075 := bstep (se 1 (by rfl) ⟨253556, by rfl⟩ : syracuseStep 338075 = 507113) B507113
theorem B338273 : Blo 147793 338273 := bstep (se 2 (by rfl) ⟨126852, by rfl⟩ : syracuseStep 338273 = 253705) B253705
theorem B338687 : Blo 147793 338687 := bstep (se 1 (by rfl) ⟨254015, by rfl⟩ : syracuseStep 338687 = 508031) B508031
theorem B9940553 : Blo 147793 9940553 := bstep (se 2 (by rfl) ⟨3727707, by rfl⟩ : syracuseStep 9940553 = 7455415) B7455415
theorem B503711 : Blo 147793 503711 := bstep (se 1 (by rfl) ⟨377783, by rfl⟩ : syracuseStep 503711 = 755567) B755567
theorem B2077085 : Blo 147793 2077085 := bstep (se 3 (by rfl) ⟨389453, by rfl⟩ : syracuseStep 2077085 = 778907) B778907
theorem B340415 : Blo 147793 340415 := bstep (se 1 (by rfl) ⟨255311, by rfl⟩ : syracuseStep 340415 = 510623) B510623
theorem B767231 : Blo 147793 767231 := bstep (se 1 (by rfl) ⟨575423, by rfl⟩ : syracuseStep 767231 = 1150847) B1150847
theorem B604007 : Blo 147793 604007 := bstep (se 1 (by rfl) ⟨453005, by rfl⟩ : syracuseStep 604007 = 906011) B906011
theorem B768203 : Blo 147793 768203 := bstep (se 1 (by rfl) ⟨576152, by rfl⟩ : syracuseStep 768203 = 1152305) B1152305
theorem B2866337 : Blo 147793 2866337 := bstep (se 2 (by rfl) ⟨1074876, by rfl⟩ : syracuseStep 2866337 = 2149753) B2149753
theorem B507179 : Blo 147793 507179 := bstep (se 1 (by rfl) ⟨380384, by rfl⟩ : syracuseStep 507179 = 760769) B760769
theorem B9158017 : Blo 147793 9158017 := bstep (se 2 (by rfl) ⟨3434256, by rfl⟩ : syracuseStep 9158017 = 6868513) B6868513
theorem B507383 : Blo 147793 507383 := bstep (se 1 (by rfl) ⟨380537, by rfl⟩ : syracuseStep 507383 = 761075) B761075
theorem B376559 : Blo 147793 376559 := bstep (se 1 (by rfl) ⟨282419, by rfl⟩ : syracuseStep 376559 = 564839) B564839
theorem B148223 : Blo 147793 148223 := bstep (se 1 (by rfl) ⟨111167, by rfl⟩ : syracuseStep 148223 = 222335) B222335
theorem B148315 : Blo 147793 148315 := bstep (se 1 (by rfl) ⟨111236, by rfl⟩ : syracuseStep 148315 = 222473) B222473
theorem B214111 : Blo 147793 214111 := bstep (se 1 (by rfl) ⟨160583, by rfl⟩ : syracuseStep 214111 = 321167) B321167
theorem B148635 : Blo 147793 148635 := bstep (se 1 (by rfl) ⟨111476, by rfl⟩ : syracuseStep 148635 = 222953) B222953
theorem B148975 : Blo 147793 148975 := bstep (se 1 (by rfl) ⟨111731, by rfl⟩ : syracuseStep 148975 = 223463) B223463
theorem B148991 : Blo 147793 148991 := bstep (se 1 (by rfl) ⟨111743, by rfl⟩ : syracuseStep 148991 = 223487) B223487
theorem B1623797 : Blo 147793 1623797 := bstep (se 5 (by rfl) ⟨76115, by rfl⟩ : syracuseStep 1623797 = 152231) B152231
theorem B149319 : Blo 147793 149319 := bstep (se 1 (by rfl) ⟨111989, by rfl⟩ : syracuseStep 149319 = 223979) B223979
theorem B149567 : Blo 147793 149567 := bstep (se 1 (by rfl) ⟨112175, by rfl⟩ : syracuseStep 149567 = 224351) B224351
theorem B149671 : Blo 147793 149671 := bstep (se 1 (by rfl) ⟨112253, by rfl⟩ : syracuseStep 149671 = 224507) B224507
theorem B149831 : Blo 147793 149831 := bstep (se 1 (by rfl) ⟨112373, by rfl⟩ : syracuseStep 149831 = 224747) B224747
theorem B149863 : Blo 147793 149863 := bstep (se 1 (by rfl) ⟨112397, by rfl⟩ : syracuseStep 149863 = 224795) B224795
theorem B149915 : Blo 147793 149915 := bstep (se 1 (by rfl) ⟨112436, by rfl⟩ : syracuseStep 149915 = 224873) B224873
theorem B510461 : Blo 147793 510461 := bstep (se 3 (by rfl) ⟨95711, by rfl⟩ : syracuseStep 510461 = 191423) B191423
theorem B150127 : Blo 147793 150127 := bstep (se 1 (by rfl) ⟨112595, by rfl⟩ : syracuseStep 150127 = 225191) B225191
theorem B150247 : Blo 147793 150247 := bstep (se 1 (by rfl) ⟨112685, by rfl⟩ : syracuseStep 150247 = 225371) B225371
theorem B248633 : Blo 147793 248633 := bstep (se 2 (by rfl) ⟨93237, by rfl⟩ : syracuseStep 248633 = 186475) B186475
theorem B215879 : Blo 147793 215879 := bstep (se 1 (by rfl) ⟨161909, by rfl⟩ : syracuseStep 215879 = 323819) B323819
theorem B150383 : Blo 147793 150383 := bstep (se 1 (by rfl) ⟨112787, by rfl⟩ : syracuseStep 150383 = 225575) B225575
theorem B150719 : Blo 147793 150719 := bstep (se 1 (by rfl) ⟨113039, by rfl⟩ : syracuseStep 150719 = 226079) B226079
theorem B150783 : Blo 147793 150783 := bstep (se 1 (by rfl) ⟨113087, by rfl⟩ : syracuseStep 150783 = 226175) B226175
theorem B150811 : Blo 147793 150811 := bstep (se 1 (by rfl) ⟨113108, by rfl⟩ : syracuseStep 150811 = 226217) B226217
theorem B150847 : Blo 147793 150847 := bstep (se 1 (by rfl) ⟨113135, by rfl⟩ : syracuseStep 150847 = 226271) B226271
theorem B151039 : Blo 147793 151039 := bstep (se 1 (by rfl) ⟨113279, by rfl⟩ : syracuseStep 151039 = 226559) B226559
theorem B1265179 : Blo 147793 1265179 := bstep (se 1 (by rfl) ⟨948884, by rfl⟩ : syracuseStep 1265179 = 1897769) B1897769
theorem B151407 : Blo 147793 151407 := bstep (se 1 (by rfl) ⟨113555, by rfl⟩ : syracuseStep 151407 = 227111) B227111
theorem B282761 : Blo 147793 282761 := bstep (se 2 (by rfl) ⟨106035, by rfl⟩ : syracuseStep 282761 = 212071) B212071
theorem B545051 : Blo 147793 545051 := bstep (se 1 (by rfl) ⟨408788, by rfl⟩ : syracuseStep 545051 = 817577) B817577
theorem B512297 : Blo 147793 512297 := bstep (se 2 (by rfl) ⟨192111, by rfl⟩ : syracuseStep 512297 = 384223) B384223
theorem B282943 : Blo 147793 282943 := bstep (se 1 (by rfl) ⟨212207, by rfl⟩ : syracuseStep 282943 = 424415) B424415
theorem B315809 : Blo 147793 315809 := bstep (se 2 (by rfl) ⟨118428, by rfl⟩ : syracuseStep 315809 = 236857) B236857
theorem B381419 : Blo 147793 381419 := bstep (se 1 (by rfl) ⟨286064, by rfl⟩ : syracuseStep 381419 = 572129) B572129
theorem B251815 : Blo 147793 251815 := bstep (se 1 (by rfl) ⟨188861, by rfl⟩ : syracuseStep 251815 = 377723) B377723
theorem B383039 : Blo 147793 383039 := bstep (se 1 (by rfl) ⟨287279, by rfl⟩ : syracuseStep 383039 = 574559) B574559
theorem B2709625 : Blo 147793 2709625 := bstep (se 2 (by rfl) ⟨1016109, by rfl⟩ : syracuseStep 2709625 = 2032219) B2032219
theorem B252463 : Blo 147793 252463 := bstep (se 1 (by rfl) ⟨189347, by rfl⟩ : syracuseStep 252463 = 378695) B378695
theorem B318431 : Blo 147793 318431 := bstep (se 1 (by rfl) ⟨238823, by rfl⟩ : syracuseStep 318431 = 477647) B477647
theorem B319295 : Blo 147793 319295 := bstep (se 1 (by rfl) ⟨239471, by rfl⟩ : syracuseStep 319295 = 478943) B478943
theorem B7004231 : Blo 147793 7004231 := bstep (se 1 (by rfl) ⟨5253173, by rfl⟩ : syracuseStep 7004231 = 10506347) B10506347
theorem B254063 : Blo 147793 254063 := bstep (se 1 (by rfl) ⟨190547, by rfl⟩ : syracuseStep 254063 = 381095) B381095
theorem B287059 : Blo 147793 287059 := bstep (se 1 (by rfl) ⟨215294, by rfl⟩ : syracuseStep 287059 = 430589) B430589
theorem B8151839 : Blo 147793 8151839 := bstep (se 1 (by rfl) ⟨6113879, by rfl⟩ : syracuseStep 8151839 = 12227759) B12227759
theorem B1106855 : Blo 147793 1106855 := bstep (se 1 (by rfl) ⟨830141, by rfl⟩ : syracuseStep 1106855 = 1660283) B1660283
theorem B10314971 : Blo 147793 10314971 := bstep (se 1 (by rfl) ⟨7736228, by rfl⟩ : syracuseStep 10314971 = 15472457) B15472457
theorem B1632905 : Blo 147793 1632905 := bstep (se 2 (by rfl) ⟨612339, by rfl⟩ : syracuseStep 1632905 = 1224679) B1224679
theorem B715817 : Blo 147793 715817 := bstep (se 2 (by rfl) ⟨268431, by rfl⟩ : syracuseStep 715817 = 536863) B536863
theorem B748601 : Blo 147793 748601 := bstep (se 2 (by rfl) ⟨280725, by rfl⟩ : syracuseStep 748601 = 561451) B561451
theorem B224633 : Blo 147793 224633 := bstep (se 2 (by rfl) ⟨84237, by rfl⟩ : syracuseStep 224633 = 168475) B168475
theorem B585185 : Blo 147793 585185 := bstep (se 2 (by rfl) ⟨219444, by rfl⟩ : syracuseStep 585185 = 438889) B438889
theorem B225563 : Blo 147793 225563 := bstep (se 1 (by rfl) ⟨169172, by rfl⟩ : syracuseStep 225563 = 338345) B338345
theorem B226331 : Blo 147793 226331 := bstep (se 1 (by rfl) ⟨169748, by rfl⟩ : syracuseStep 226331 = 339497) B339497
theorem B816713 : Blo 147793 816713 := bstep (se 2 (by rfl) ⟨306267, by rfl⟩ : syracuseStep 816713 = 612535) B612535
theorem B226991 : Blo 147793 226991 := bstep (se 1 (by rfl) ⟨170243, by rfl⟩ : syracuseStep 226991 = 340487) B340487
theorem B227183 : Blo 147793 227183 := bstep (se 1 (by rfl) ⟨170387, by rfl⟩ : syracuseStep 227183 = 340775) B340775
theorem B1735019 : Blo 147793 1735019 := bstep (se 1 (by rfl) ⟨1301264, by rfl⟩ : syracuseStep 1735019 = 2602529) B2602529
theorem B2554415 : Blo 147793 2554415 := bstep (se 1 (by rfl) ⟨1915811, by rfl⟩ : syracuseStep 2554415 = 3831623) B3831623
theorem B752975 : Blo 147793 752975 := bstep (se 1 (by rfl) ⟨564731, by rfl⟩ : syracuseStep 752975 = 1129463) B1129463
theorem B917345 : Blo 147793 917345 := bstep (se 2 (by rfl) ⟨344004, by rfl⟩ : syracuseStep 917345 = 688009) B688009
theorem B917729 : Blo 147793 917729 := bstep (se 2 (by rfl) ⟨344148, by rfl⟩ : syracuseStep 917729 = 688297) B688297
theorem B5538893 : Blo 147793 5538893 := bstep (se 3 (by rfl) ⟨1038542, by rfl⟩ : syracuseStep 5538893 = 2077085) B2077085
theorem B1082531 : Blo 147793 1082531 := bstep (se 1 (by rfl) ⟨811898, by rfl⟩ : syracuseStep 1082531 = 1623797) B1623797
theorem B755081 : Blo 147793 755081 := bstep (se 2 (by rfl) ⟨283155, by rfl⟩ : syracuseStep 755081 = 566311) B566311
theorem B7865743 : Blo 147793 7865743 := bstep (se 1 (by rfl) ⟨5899307, by rfl⟩ : syracuseStep 7865743 = 11798615) B11798615
theorem B165755 : Blo 147793 165755 := bstep (se 1 (by rfl) ⟨124316, by rfl⟩ : syracuseStep 165755 = 248633) B248633
theorem B363367 : Blo 147793 363367 := bstep (se 1 (by rfl) ⟨272525, by rfl⟩ : syracuseStep 363367 = 545051) B545051
theorem B726043 : Blo 147793 726043 := bstep (se 1 (by rfl) ⟨544532, by rfl⟩ : syracuseStep 726043 = 1089065) B1089065
theorem B42407023 : Blo 147793 42407023 := bstep (se 1 (by rfl) ⟨31805267, by rfl⟩ : syracuseStep 42407023 = 63610535) B63610535
theorem B169375 : Blo 147793 169375 := bstep (se 1 (by rfl) ⟨127031, by rfl⟩ : syracuseStep 169375 = 254063) B254063
theorem B1088603 : Blo 147793 1088603 := bstep (se 1 (by rfl) ⟨816452, by rfl⟩ : syracuseStep 1088603 = 1632905) B1632905
theorem B499067 : Blo 147793 499067 := bstep (se 1 (by rfl) ⟨374300, by rfl⟩ : syracuseStep 499067 = 748601) B748601
theorem B6627035 : Blo 147793 6627035 := bstep (se 1 (by rfl) ⟨4970276, by rfl⟩ : syracuseStep 6627035 = 9940553) B9940553
theorem B335753 : Blo 147793 335753 := bstep (se 2 (by rfl) ⟨125907, by rfl⟩ : syracuseStep 335753 = 251815) B251815
theorem B335807 : Blo 147793 335807 := bstep (se 1 (by rfl) ⟨251855, by rfl⟩ : syracuseStep 335807 = 503711) B503711
theorem B3612833 : Blo 147793 3612833 := bstep (se 2 (by rfl) ⟨1354812, by rfl⟩ : syracuseStep 3612833 = 2709625) B2709625
theorem B336617 : Blo 147793 336617 := bstep (se 2 (by rfl) ⟨126231, by rfl⟩ : syracuseStep 336617 = 252463) B252463
theorem B1352477 : Blo 147793 1352477 := bstep (se 3 (by rfl) ⟨253589, by rfl⟩ : syracuseStep 1352477 = 507179) B507179
theorem B402671 : Blo 147793 402671 := bstep (se 1 (by rfl) ⟨302003, by rfl⟩ : syracuseStep 402671 = 604007) B604007
theorem B1156679 : Blo 147793 1156679 := bstep (se 1 (by rfl) ⟨867509, by rfl⟩ : syracuseStep 1156679 = 1735019) B1735019
theorem B1910891 : Blo 147793 1910891 := bstep (se 1 (by rfl) ⟨1433168, by rfl⟩ : syracuseStep 1910891 = 2866337) B2866337
theorem B501983 : Blo 147793 501983 := bstep (se 1 (by rfl) ⟨376487, by rfl⟩ : syracuseStep 501983 = 752975) B752975
theorem B338255 : Blo 147793 338255 := bstep (se 1 (by rfl) ⟨253691, by rfl⟩ : syracuseStep 338255 = 507383) B507383
theorem B340307 : Blo 147793 340307 := bstep (se 1 (by rfl) ⟨255230, by rfl⟩ : syracuseStep 340307 = 510461) B510461
theorem B341531 : Blo 147793 341531 := bstep (se 1 (by rfl) ⟨256148, by rfl⟩ : syracuseStep 341531 = 512297) B512297
theorem B210539 : Blo 147793 210539 := bstep (se 1 (by rfl) ⟨157904, by rfl⟩ : syracuseStep 210539 = 315809) B315809
theorem B964327 : Blo 147793 964327 := bstep (se 1 (by rfl) ⟨723245, by rfl⟩ : syracuseStep 964327 = 1446491) B1446491
theorem B3258539 : Blo 147793 3258539 := bstep (se 1 (by rfl) ⟨2443904, by rfl⟩ : syracuseStep 3258539 = 4887809) B4887809
theorem B965135 : Blo 147793 965135 := bstep (se 1 (by rfl) ⟨723851, by rfl⟩ : syracuseStep 965135 = 1447703) B1447703
theorem B965287 : Blo 147793 965287 := bstep (se 1 (by rfl) ⟨723965, by rfl⟩ : syracuseStep 965287 = 1447931) B1447931
theorem B506843 : Blo 147793 506843 := bstep (se 1 (by rfl) ⟨380132, by rfl⟩ : syracuseStep 506843 = 760265) B760265
theorem B572447 : Blo 147793 572447 := bstep (se 1 (by rfl) ⟨429335, by rfl⟩ : syracuseStep 572447 = 858671) B858671
theorem B1686905 : Blo 147793 1686905 := bstep (se 2 (by rfl) ⟨632589, by rfl⟩ : syracuseStep 1686905 = 1265179) B1265179
theorem B212863 : Blo 147793 212863 := bstep (se 1 (by rfl) ⟨159647, by rfl⟩ : syracuseStep 212863 = 319295) B319295
theorem B4669487 : Blo 147793 4669487 := bstep (se 1 (by rfl) ⟨3502115, by rfl⟩ : syracuseStep 4669487 = 7004231) B7004231
theorem B377257 : Blo 147793 377257 := bstep (se 2 (by rfl) ⟨141471, by rfl⟩ : syracuseStep 377257 = 282943) B282943
theorem B737903 : Blo 147793 737903 := bstep (se 1 (by rfl) ⟨553427, by rfl⟩ : syracuseStep 737903 = 1106855) B1106855
theorem B377855 : Blo 147793 377855 := bstep (se 1 (by rfl) ⟨283391, by rfl⟩ : syracuseStep 377855 = 566783) B566783
theorem B574847 : Blo 147793 574847 := bstep (se 1 (by rfl) ⟨431135, by rfl⟩ : syracuseStep 574847 = 862271) B862271
theorem B477211 : Blo 147793 477211 := bstep (se 1 (by rfl) ⟨357908, by rfl⟩ : syracuseStep 477211 = 715817) B715817
theorem B575677 : Blo 147793 575677 := bstep (se 3 (by rfl) ⟨107939, by rfl⟩ : syracuseStep 575677 = 215879) B215879
theorem B149755 : Blo 147793 149755 := bstep (se 1 (by rfl) ⟨112316, by rfl⟩ : syracuseStep 149755 = 224633) B224633
theorem B150375 : Blo 147793 150375 := bstep (se 1 (by rfl) ⟨112781, by rfl⟩ : syracuseStep 150375 = 225563) B225563
theorem B150887 : Blo 147793 150887 := bstep (se 1 (by rfl) ⟨113165, by rfl⟩ : syracuseStep 150887 = 226331) B226331
theorem B511487 : Blo 147793 511487 := bstep (se 1 (by rfl) ⟨383615, by rfl⟩ : syracuseStep 511487 = 767231) B767231
theorem B544475 : Blo 147793 544475 := bstep (se 1 (by rfl) ⟨408356, by rfl⟩ : syracuseStep 544475 = 816713) B816713
theorem B151327 : Blo 147793 151327 := bstep (se 1 (by rfl) ⟨113495, by rfl⟩ : syracuseStep 151327 = 226991) B226991
theorem B151455 : Blo 147793 151455 := bstep (se 1 (by rfl) ⟨113591, by rfl⟩ : syracuseStep 151455 = 227183) B227183
theorem B1560493 : Blo 147793 1560493 := bstep (se 3 (by rfl) ⟨292592, by rfl⟩ : syracuseStep 1560493 = 585185) B585185
theorem B512135 : Blo 147793 512135 := bstep (se 1 (by rfl) ⟨384101, by rfl⟩ : syracuseStep 512135 = 768203) B768203
theorem B12210689 : Blo 147793 12210689 := bstep (se 2 (by rfl) ⟨4579008, by rfl⟩ : syracuseStep 12210689 = 9158017) B9158017
theorem B251039 : Blo 147793 251039 := bstep (se 1 (by rfl) ⟨188279, by rfl⟩ : syracuseStep 251039 = 376559) B376559
theorem B611563 : Blo 147793 611563 := bstep (se 1 (by rfl) ⟨458672, by rfl⟩ : syracuseStep 611563 = 917345) B917345
theorem B382745 : Blo 147793 382745 := bstep (se 2 (by rfl) ⟨143529, by rfl⟩ : syracuseStep 382745 = 287059) B287059
theorem B743275 : Blo 147793 743275 := bstep (se 1 (by rfl) ⟨557456, by rfl⟩ : syracuseStep 743275 = 1114913) B1114913
theorem B285481 : Blo 147793 285481 := bstep (se 2 (by rfl) ⟨107055, by rfl⟩ : syracuseStep 285481 = 214111) B214111
theorem B1465199 : Blo 147793 1465199 := bstep (se 1 (by rfl) ⟨1098899, by rfl⟩ : syracuseStep 1465199 = 2197799) B2197799
theorem B188507 : Blo 147793 188507 := bstep (se 1 (by rfl) ⟨141380, by rfl⟩ : syracuseStep 188507 = 282761) B282761
theorem B254279 : Blo 147793 254279 := bstep (se 1 (by rfl) ⟨190709, by rfl⟩ : syracuseStep 254279 = 381419) B381419
theorem B221927 : Blo 147793 221927 := bstep (se 1 (by rfl) ⟨166445, by rfl⟩ : syracuseStep 221927 = 332891) B332891
theorem B255359 : Blo 147793 255359 := bstep (se 1 (by rfl) ⟨191519, by rfl⟩ : syracuseStep 255359 = 383039) B383039
theorem B812539 : Blo 147793 812539 := bstep (se 1 (by rfl) ⟨609404, by rfl⟩ : syracuseStep 812539 = 1218809) B1218809
theorem B222959 : Blo 147793 222959 := bstep (se 1 (by rfl) ⟨167219, by rfl⟩ : syracuseStep 222959 = 334439) B334439
theorem B616423 : Blo 147793 616423 := bstep (se 1 (by rfl) ⟨462317, by rfl⟩ : syracuseStep 616423 = 924635) B924635
theorem B1599859 : Blo 147793 1599859 := bstep (se 1 (by rfl) ⟨1199894, by rfl⟩ : syracuseStep 1599859 = 2399789) B2399789
theorem B223799 : Blo 147793 223799 := bstep (se 1 (by rfl) ⟨167849, by rfl⟩ : syracuseStep 223799 = 335699) B335699
theorem B224009 : Blo 147793 224009 := bstep (se 2 (by rfl) ⟨84003, by rfl⟩ : syracuseStep 224009 = 168007) B168007
theorem B224063 : Blo 147793 224063 := bstep (se 1 (by rfl) ⟨168047, by rfl⟩ : syracuseStep 224063 = 336095) B336095
theorem B224111 : Blo 147793 224111 := bstep (se 1 (by rfl) ⟨168083, by rfl⟩ : syracuseStep 224111 = 336167) B336167
theorem B5958845 : Blo 147793 5958845 := bstep (se 3 (by rfl) ⟨1117283, by rfl⟩ : syracuseStep 5958845 = 2234567) B2234567
theorem B5434559 : Blo 147793 5434559 := bstep (se 1 (by rfl) ⟨4075919, by rfl⟩ : syracuseStep 5434559 = 8151839) B8151839
theorem B224495 : Blo 147793 224495 := bstep (se 1 (by rfl) ⟨168371, by rfl⟩ : syracuseStep 224495 = 336743) B336743
theorem B224603 : Blo 147793 224603 := bstep (se 1 (by rfl) ⟨168452, by rfl⟩ : syracuseStep 224603 = 336905) B336905
theorem B6876647 : Blo 147793 6876647 := bstep (se 1 (by rfl) ⟨5157485, by rfl⟩ : syracuseStep 6876647 = 10314971) B10314971
theorem B225215 : Blo 147793 225215 := bstep (se 1 (by rfl) ⟨168911, by rfl⟩ : syracuseStep 225215 = 337823) B337823
theorem B225383 : Blo 147793 225383 := bstep (se 1 (by rfl) ⟨169037, by rfl⟩ : syracuseStep 225383 = 338075) B338075
theorem B225515 : Blo 147793 225515 := bstep (se 1 (by rfl) ⟨169136, by rfl⟩ : syracuseStep 225515 = 338273) B338273
theorem B225791 : Blo 147793 225791 := bstep (se 1 (by rfl) ⟨169343, by rfl⟩ : syracuseStep 225791 = 338687) B338687
theorem B849149 : Blo 147793 849149 := bstep (se 3 (by rfl) ⟨159215, by rfl⟩ : syracuseStep 849149 = 318431) B318431
theorem B226943 : Blo 147793 226943 := bstep (se 1 (by rfl) ⟨170207, by rfl⟩ : syracuseStep 226943 = 340415) B340415
theorem B5339033 : Blo 147793 5339033 := bstep (se 2 (by rfl) ⟨2002137, by rfl⟩ : syracuseStep 5339033 = 4004275) B4004275
theorem B1702943 : Blo 147793 1702943 := bstep (se 1 (by rfl) ⟨1277207, by rfl⟩ : syracuseStep 1702943 = 2554415) B2554415
theorem B3112991 : Blo 147793 3112991 := bstep (se 1 (by rfl) ⟨2334743, by rfl⟩ : syracuseStep 3112991 = 4669487) B4669487
theorem B491935 : Blo 147793 491935 := bstep (se 1 (by rfl) ⟨368951, by rfl⟩ : syracuseStep 491935 = 737903) B737903
theorem B59081525 : Blo 147793 59081525 := bstep (se 5 (by rfl) ⟨2769446, by rfl⟩ : syracuseStep 59081525 = 5538893) B5538893
theorem B10487657 : Blo 147793 10487657 := bstep (se 2 (by rfl) ⟨3932871, by rfl⟩ : syracuseStep 10487657 = 7865743) B7865743
theorem B1083385 : Blo 147793 1083385 := bstep (se 2 (by rfl) ⟨406269, by rfl⟩ : syracuseStep 1083385 = 812539) B812539
theorem B3606605 : Blo 147793 3606605 := bstep (se 3 (by rfl) ⟨676238, by rfl⟩ : syracuseStep 3606605 = 1352477) B1352477
theorem B362983 : Blo 147793 362983 := bstep (se 1 (by rfl) ⟨272237, by rfl⟩ : syracuseStep 362983 = 544475) B544475
theorem B821897 : Blo 147793 821897 := bstep (se 2 (by rfl) ⟨308211, by rfl⟩ : syracuseStep 821897 = 616423) B616423
theorem B2886749 : Blo 147793 2886749 := bstep (se 3 (by rfl) ⟨541265, by rfl⟩ : syracuseStep 2886749 = 1082531) B1082531
theorem B2133145 : Blo 147793 2133145 := bstep (se 2 (by rfl) ⟨799929, by rfl⟩ : syracuseStep 2133145 = 1599859) B1599859
theorem B167359 : Blo 147793 167359 := bstep (se 1 (by rfl) ⟨125519, by rfl⟩ : syracuseStep 167359 = 251039) B251039
theorem B561437 : Blo 147793 561437 := bstep (se 3 (by rfl) ⟨105269, by rfl⟩ : syracuseStep 561437 = 210539) B210539
theorem B725735 : Blo 147793 725735 := bstep (se 1 (by rfl) ⟨544301, by rfl⟩ : syracuseStep 725735 = 1088603) B1088603
theorem B332711 : Blo 147793 332711 := bstep (se 1 (by rfl) ⟨249533, by rfl⟩ : syracuseStep 332711 = 499067) B499067
theorem B169519 : Blo 147793 169519 := bstep (se 1 (by rfl) ⟨127139, by rfl⟩ : syracuseStep 169519 = 254279) B254279
theorem B268447 : Blo 147793 268447 := bstep (se 1 (by rfl) ⟨201335, by rfl⟩ : syracuseStep 268447 = 402671) B402671
theorem B170239 : Blo 147793 170239 := bstep (se 1 (by rfl) ⟨127679, by rfl⟩ : syracuseStep 170239 = 255359) B255359
theorem B334655 : Blo 147793 334655 := bstep (se 1 (by rfl) ⟨250991, by rfl⟩ : syracuseStep 334655 = 501983) B501983
theorem B3972563 : Blo 147793 3972563 := bstep (se 1 (by rfl) ⟨2979422, by rfl⟩ : syracuseStep 3972563 = 5958845) B5958845
theorem B1285769 : Blo 147793 1285769 := bstep (se 2 (by rfl) ⟨482163, by rfl⟩ : syracuseStep 1285769 = 964327) B964327
theorem B991033 : Blo 147793 991033 := bstep (se 2 (by rfl) ⟨371637, by rfl⟩ : syracuseStep 991033 = 743275) B743275
theorem B566099 : Blo 147793 566099 := bstep (se 1 (by rfl) ⟨424574, by rfl⟩ : syracuseStep 566099 = 849149) B849149
theorem B1287049 : Blo 147793 1287049 := bstep (se 2 (by rfl) ⟨482643, by rfl⟩ : syracuseStep 1287049 = 965287) B965287
theorem B2172359 : Blo 147793 2172359 := bstep (se 1 (by rfl) ⟨1629269, by rfl⟩ : syracuseStep 2172359 = 3258539) B3258539
theorem B337895 : Blo 147793 337895 := bstep (se 1 (by rfl) ⟨253421, by rfl⟩ : syracuseStep 337895 = 506843) B506843
theorem B1124603 : Blo 147793 1124603 := bstep (se 1 (by rfl) ⟨843452, by rfl⟩ : syracuseStep 1124603 = 1686905) B1686905
theorem B502685 : Blo 147793 502685 := bstep (se 3 (by rfl) ⟨94253, by rfl⟩ : syracuseStep 502685 = 188507) B188507
theorem B503009 : Blo 147793 503009 := bstep (se 2 (by rfl) ⟨188628, by rfl⟩ : syracuseStep 503009 = 377257) B377257
theorem B503387 : Blo 147793 503387 := bstep (se 1 (by rfl) ⟨377540, by rfl⟩ : syracuseStep 503387 = 755081) B755081
theorem B340991 : Blo 147793 340991 := bstep (se 1 (by rfl) ⟨255743, by rfl⟩ : syracuseStep 340991 = 511487) B511487
theorem B636281 : Blo 147793 636281 := bstep (se 2 (by rfl) ⟨238605, by rfl⟩ : syracuseStep 636281 = 477211) B477211
theorem B341423 : Blo 147793 341423 := bstep (se 1 (by rfl) ⟨256067, by rfl⟩ : syracuseStep 341423 = 512135) B512135
theorem B767569 : Blo 147793 767569 := bstep (se 2 (by rfl) ⟨287838, by rfl⟩ : syracuseStep 767569 = 575677) B575677
theorem B8140459 : Blo 147793 8140459 := bstep (se 1 (by rfl) ⟨6105344, by rfl⟩ : syracuseStep 8140459 = 12210689) B12210689
theorem B442013 : Blo 147793 442013 := bstep (se 3 (by rfl) ⟨82877, by rfl⟩ : syracuseStep 442013 = 165755) B165755
theorem B2080657 : Blo 147793 2080657 := bstep (se 2 (by rfl) ⟨780246, by rfl⟩ : syracuseStep 2080657 = 1560493) B1560493
theorem B2408555 : Blo 147793 2408555 := bstep (se 1 (by rfl) ⟨1806416, by rfl⟩ : syracuseStep 2408555 = 3612833) B3612833
theorem B147951 : Blo 147793 147951 := bstep (se 1 (by rfl) ⟨110963, by rfl⟩ : syracuseStep 147951 = 221927) B221927
theorem B771119 : Blo 147793 771119 := bstep (se 1 (by rfl) ⟨578339, by rfl⟩ : syracuseStep 771119 = 1156679) B1156679
theorem B148639 : Blo 147793 148639 := bstep (se 1 (by rfl) ⟨111479, by rfl⟩ : syracuseStep 148639 = 222959) B222959
theorem B968057 : Blo 147793 968057 := bstep (se 2 (by rfl) ⟨363021, by rfl⟩ : syracuseStep 968057 = 726043) B726043
theorem B56542697 : Blo 147793 56542697 := bstep (se 2 (by rfl) ⟨21203511, by rfl⟩ : syracuseStep 56542697 = 42407023) B42407023
theorem B149199 : Blo 147793 149199 := bstep (se 1 (by rfl) ⟨111899, by rfl⟩ : syracuseStep 149199 = 223799) B223799
theorem B149339 : Blo 147793 149339 := bstep (se 1 (by rfl) ⟨112004, by rfl⟩ : syracuseStep 149339 = 224009) B224009
theorem B149375 : Blo 147793 149375 := bstep (se 1 (by rfl) ⟨112031, by rfl⟩ : syracuseStep 149375 = 224063) B224063
theorem B149407 : Blo 147793 149407 := bstep (se 1 (by rfl) ⟨112055, by rfl⟩ : syracuseStep 149407 = 224111) B224111
theorem B3623039 : Blo 147793 3623039 := bstep (se 1 (by rfl) ⟨2717279, by rfl⟩ : syracuseStep 3623039 = 5434559) B5434559
theorem B149663 : Blo 147793 149663 := bstep (se 1 (by rfl) ⟨112247, by rfl⟩ : syracuseStep 149663 = 224495) B224495
theorem B149735 : Blo 147793 149735 := bstep (se 1 (by rfl) ⟨112301, by rfl⟩ : syracuseStep 149735 = 224603) B224603
theorem B150143 : Blo 147793 150143 := bstep (se 1 (by rfl) ⟨112607, by rfl⟩ : syracuseStep 150143 = 225215) B225215
theorem B150255 : Blo 147793 150255 := bstep (se 1 (by rfl) ⟨112691, by rfl⟩ : syracuseStep 150255 = 225383) B225383
theorem B150343 : Blo 147793 150343 := bstep (se 1 (by rfl) ⟨112757, by rfl⟩ : syracuseStep 150343 = 225515) B225515
theorem B150527 : Blo 147793 150527 := bstep (se 1 (by rfl) ⟨112895, by rfl⟩ : syracuseStep 150527 = 225791) B225791
theorem B380641 : Blo 147793 380641 := bstep (se 2 (by rfl) ⟨142740, by rfl⟩ : syracuseStep 380641 = 285481) B285481
theorem B151295 : Blo 147793 151295 := bstep (se 1 (by rfl) ⟨113471, by rfl⟩ : syracuseStep 151295 = 226943) B226943
theorem B3559355 : Blo 147793 3559355 := bstep (se 1 (by rfl) ⟨2669516, by rfl⟩ : syracuseStep 3559355 = 5339033) B5339033
theorem B643423 : Blo 147793 643423 := bstep (se 1 (by rfl) ⟨482567, by rfl⟩ : syracuseStep 643423 = 965135) B965135
theorem B1135295 : Blo 147793 1135295 := bstep (se 1 (by rfl) ⟨851471, by rfl⟩ : syracuseStep 1135295 = 1702943) B1702943
theorem B381631 : Blo 147793 381631 := bstep (se 1 (by rfl) ⟨286223, by rfl⟩ : syracuseStep 381631 = 572447) B572447
theorem B283817 : Blo 147793 283817 := bstep (se 2 (by rfl) ⟨106431, by rfl⟩ : syracuseStep 283817 = 212863) B212863
theorem B611819 : Blo 147793 611819 := bstep (se 1 (by rfl) ⟨458864, by rfl⟩ : syracuseStep 611819 = 917729) B917729
theorem B251903 : Blo 147793 251903 := bstep (se 1 (by rfl) ⟨188927, by rfl⟩ : syracuseStep 251903 = 377855) B377855
theorem B383231 : Blo 147793 383231 := bstep (se 1 (by rfl) ⟨287423, by rfl⟩ : syracuseStep 383231 = 574847) B574847
theorem B484489 : Blo 147793 484489 := bstep (se 2 (by rfl) ⟨181683, by rfl⟩ : syracuseStep 484489 = 363367) B363367
theorem B255163 : Blo 147793 255163 := bstep (se 1 (by rfl) ⟨191372, by rfl⟩ : syracuseStep 255163 = 382745) B382745
theorem B976799 : Blo 147793 976799 := bstep (se 1 (by rfl) ⟨732599, by rfl⟩ : syracuseStep 976799 = 1465199) B1465199
theorem B4418023 : Blo 147793 4418023 := bstep (se 1 (by rfl) ⟨3313517, by rfl⟩ : syracuseStep 4418023 = 6627035) B6627035
theorem B223835 : Blo 147793 223835 := bstep (se 1 (by rfl) ⟨167876, by rfl⟩ : syracuseStep 223835 = 335753) B335753
theorem B223871 : Blo 147793 223871 := bstep (se 1 (by rfl) ⟨167903, by rfl⟩ : syracuseStep 223871 = 335807) B335807
theorem B224411 : Blo 147793 224411 := bstep (se 1 (by rfl) ⟨168308, by rfl⟩ : syracuseStep 224411 = 336617) B336617
theorem B1273927 : Blo 147793 1273927 := bstep (se 1 (by rfl) ⟨955445, by rfl⟩ : syracuseStep 1273927 = 1910891) B1910891
theorem B225503 : Blo 147793 225503 := bstep (se 1 (by rfl) ⟨169127, by rfl⟩ : syracuseStep 225503 = 338255) B338255
theorem B815417 : Blo 147793 815417 := bstep (se 2 (by rfl) ⟨305781, by rfl⟩ : syracuseStep 815417 = 611563) B611563
theorem B225833 : Blo 147793 225833 := bstep (se 2 (by rfl) ⟨84687, by rfl⟩ : syracuseStep 225833 = 169375) B169375
theorem B4584431 : Blo 147793 4584431 := bstep (se 1 (by rfl) ⟨3438323, by rfl⟩ : syracuseStep 4584431 = 6876647) B6876647
theorem B226871 : Blo 147793 226871 := bstep (se 1 (by rfl) ⟨170153, by rfl⟩ : syracuseStep 226871 = 340307) B340307
theorem B227687 : Blo 147793 227687 := bstep (se 1 (by rfl) ⟨170765, by rfl⟩ : syracuseStep 227687 = 341531) B341531
theorem B1605703 : Blo 147793 1605703 := bstep (se 1 (by rfl) ⟨1204277, by rfl⟩ : syracuseStep 1605703 = 2408555) B2408555
theorem B39387683 : Blo 147793 39387683 := bstep (se 1 (by rfl) ⟨29540762, by rfl⟩ : syracuseStep 39387683 = 59081525) B59081525
theorem B655913 : Blo 147793 655913 := bstep (se 2 (by rfl) ⟨245967, by rfl⟩ : syracuseStep 655913 = 491935) B491935
theorem B1444513 : Blo 147793 1444513 := bstep (se 2 (by rfl) ⟨541692, by rfl⟩ : syracuseStep 1444513 = 1083385) B1083385
theorem B756863 : Blo 147793 756863 := bstep (se 1 (by rfl) ⟨567647, by rfl⟩ : syracuseStep 756863 = 1135295) B1135295
theorem B167935 : Blo 147793 167935 := bstep (se 1 (by rfl) ⟨125951, by rfl⟩ : syracuseStep 167935 = 251903) B251903
theorem B857179 : Blo 147793 857179 := bstep (se 1 (by rfl) ⟨642884, by rfl⟩ : syracuseStep 857179 = 1285769) B1285769
theorem B857897 : Blo 147793 857897 := bstep (se 2 (by rfl) ⟨321711, by rfl⟩ : syracuseStep 857897 = 643423) B643423
theorem B1448239 : Blo 147793 1448239 := bstep (se 1 (by rfl) ⟨1086179, by rfl⟩ : syracuseStep 1448239 = 2172359) B2172359
theorem B21142037 : Blo 147793 21142037 := bstep (se 6 (by rfl) ⟨495516, by rfl⟩ : syracuseStep 21142037 = 991033) B991033
theorem B335123 : Blo 147793 335123 := bstep (se 1 (by rfl) ⟨251342, by rfl⟩ : syracuseStep 335123 = 502685) B502685
theorem B1023425 : Blo 147793 1023425 := bstep (se 2 (by rfl) ⟨383784, by rfl⟩ : syracuseStep 1023425 = 767569) B767569
theorem B335339 : Blo 147793 335339 := bstep (se 1 (by rfl) ⟨251504, by rfl⟩ : syracuseStep 335339 = 503009) B503009
theorem B10853945 : Blo 147793 10853945 := bstep (se 2 (by rfl) ⟨4070229, by rfl⟩ : syracuseStep 10853945 = 8140459) B8140459
theorem B335591 : Blo 147793 335591 := bstep (se 1 (by rfl) ⟨251693, by rfl⟩ : syracuseStep 335591 = 503387) B503387
theorem B3056287 : Blo 147793 3056287 := bstep (se 1 (by rfl) ⟨2292215, by rfl⟩ : syracuseStep 3056287 = 4584431) B4584431
theorem B2075327 : Blo 147793 2075327 := bstep (se 1 (by rfl) ⟨1556495, by rfl⟩ : syracuseStep 2075327 = 3112991) B3112991
theorem B37695131 : Blo 147793 37695131 := bstep (se 1 (by rfl) ⟨28271348, by rfl⟩ : syracuseStep 37695131 = 56542697) B56542697
theorem B1716065 : Blo 147793 1716065 := bstep (se 2 (by rfl) ⟨643524, by rfl⟩ : syracuseStep 1716065 = 1287049) B1287049
theorem B6991771 : Blo 147793 6991771 := bstep (se 1 (by rfl) ⟨5243828, by rfl⟩ : syracuseStep 6991771 = 10487657) B10487657
theorem B2404403 : Blo 147793 2404403 := bstep (se 1 (by rfl) ⟨1803302, by rfl⟩ : syracuseStep 2404403 = 3606605) B3606605
theorem B340217 : Blo 147793 340217 := bstep (se 2 (by rfl) ⟨127581, by rfl⟩ : syracuseStep 340217 = 255163) B255163
theorem B2372903 : Blo 147793 2372903 := bstep (se 1 (by rfl) ⟨1779677, by rfl⟩ : syracuseStep 2372903 = 3559355) B3559355
theorem B374291 : Blo 147793 374291 := bstep (se 1 (by rfl) ⟨280718, by rfl⟩ : syracuseStep 374291 = 561437) B561437
theorem B407879 : Blo 147793 407879 := bstep (se 1 (by rfl) ⟨305909, by rfl⟩ : syracuseStep 407879 = 611819) B611819
theorem B507521 : Blo 147793 507521 := bstep (se 2 (by rfl) ⟨190320, by rfl⟩ : syracuseStep 507521 = 380641) B380641
theorem B377399 : Blo 147793 377399 := bstep (se 1 (by rfl) ⟨283049, by rfl⟩ : syracuseStep 377399 = 566099) B566099
theorem B508841 : Blo 147793 508841 := bstep (se 2 (by rfl) ⟨190815, by rfl⟩ : syracuseStep 508841 = 381631) B381631
theorem B149223 : Blo 147793 149223 := bstep (se 1 (by rfl) ⟨111917, by rfl⟩ : syracuseStep 149223 = 223835) B223835
theorem B149247 : Blo 147793 149247 := bstep (se 1 (by rfl) ⟨111935, by rfl⟩ : syracuseStep 149247 = 223871) B223871
theorem B149607 : Blo 147793 149607 := bstep (se 1 (by rfl) ⟨112205, by rfl⟩ : syracuseStep 149607 = 224411) B224411
theorem B150335 : Blo 147793 150335 := bstep (se 1 (by rfl) ⟨112751, by rfl⟩ : syracuseStep 150335 = 225503) B225503
theorem B543611 : Blo 147793 543611 := bstep (se 1 (by rfl) ⟨407708, by rfl⟩ : syracuseStep 543611 = 815417) B815417
theorem B150555 : Blo 147793 150555 := bstep (se 1 (by rfl) ⟨112916, by rfl⟩ : syracuseStep 150555 = 225833) B225833
theorem B151247 : Blo 147793 151247 := bstep (se 1 (by rfl) ⟨113435, by rfl⟩ : syracuseStep 151247 = 226871) B226871
theorem B151791 : Blo 147793 151791 := bstep (se 1 (by rfl) ⟨113843, by rfl⟩ : syracuseStep 151791 = 227687) B227687
theorem B11096837 : Blo 147793 11096837 := bstep (se 4 (by rfl) ⟨1040328, by rfl⟩ : syracuseStep 11096837 = 2080657) B2080657
theorem B514079 : Blo 147793 514079 := bstep (se 1 (by rfl) ⟨385559, by rfl⟩ : syracuseStep 514079 = 771119) B771119
theorem B645371 : Blo 147793 645371 := bstep (se 1 (by rfl) ⟨484028, by rfl⟩ : syracuseStep 645371 = 968057) B968057
theorem B2415359 : Blo 147793 2415359 := bstep (se 1 (by rfl) ⟨1811519, by rfl⟩ : syracuseStep 2415359 = 3623039) B3623039
theorem B645985 : Blo 147793 645985 := bstep (se 2 (by rfl) ⟨242244, by rfl⟩ : syracuseStep 645985 = 484489) B484489
theorem B547931 : Blo 147793 547931 := bstep (se 1 (by rfl) ⟨410948, by rfl⟩ : syracuseStep 547931 = 821897) B821897
theorem B1924499 : Blo 147793 1924499 := bstep (se 1 (by rfl) ⟨1443374, by rfl⟩ : syracuseStep 1924499 = 2886749) B2886749
theorem B483823 : Blo 147793 483823 := bstep (se 1 (by rfl) ⟨362867, by rfl⟩ : syracuseStep 483823 = 725735) B725735
theorem B221807 : Blo 147793 221807 := bstep (se 1 (by rfl) ⟨166355, by rfl⟩ : syracuseStep 221807 = 332711) B332711
theorem B483977 : Blo 147793 483977 := bstep (se 2 (by rfl) ⟨181491, by rfl⟩ : syracuseStep 483977 = 362983) B362983
theorem B5890697 : Blo 147793 5890697 := bstep (se 2 (by rfl) ⟨2209011, by rfl⟩ : syracuseStep 5890697 = 4418023) B4418023
theorem B189211 : Blo 147793 189211 := bstep (se 1 (by rfl) ⟨141908, by rfl⟩ : syracuseStep 189211 = 283817) B283817
theorem B255487 : Blo 147793 255487 := bstep (se 1 (by rfl) ⟨191615, by rfl⟩ : syracuseStep 255487 = 383231) B383231
theorem B2844193 : Blo 147793 2844193 := bstep (se 2 (by rfl) ⟨1066572, by rfl⟩ : syracuseStep 2844193 = 2133145) B2133145
theorem B223103 : Blo 147793 223103 := bstep (se 1 (by rfl) ⟨167327, by rfl⟩ : syracuseStep 223103 = 334655) B334655
theorem B223145 : Blo 147793 223145 := bstep (se 2 (by rfl) ⟨83679, by rfl⟩ : syracuseStep 223145 = 167359) B167359
theorem B2648375 : Blo 147793 2648375 := bstep (se 1 (by rfl) ⟨1986281, by rfl⟩ : syracuseStep 2648375 = 3972563) B3972563
theorem B1698569 : Blo 147793 1698569 := bstep (se 2 (by rfl) ⟨636963, by rfl⟩ : syracuseStep 1698569 = 1273927) B1273927
theorem B651199 : Blo 147793 651199 := bstep (se 1 (by rfl) ⟨488399, by rfl⟩ : syracuseStep 651199 = 976799) B976799
theorem B225263 : Blo 147793 225263 := bstep (se 1 (by rfl) ⟨168947, by rfl⟩ : syracuseStep 225263 = 337895) B337895
theorem B749735 : Blo 147793 749735 := bstep (se 1 (by rfl) ⟨562301, by rfl⟩ : syracuseStep 749735 = 1124603) B1124603
theorem B4714805 : Blo 147793 4714805 := bstep (se 5 (by rfl) ⟨221006, by rfl⟩ : syracuseStep 4714805 = 442013) B442013
theorem B226025 : Blo 147793 226025 := bstep (se 2 (by rfl) ⟨84759, by rfl⟩ : syracuseStep 226025 = 169519) B169519
theorem B357929 : Blo 147793 357929 := bstep (se 2 (by rfl) ⟨134223, by rfl⟩ : syracuseStep 357929 = 268447) B268447
theorem B226985 : Blo 147793 226985 := bstep (se 2 (by rfl) ⟨85119, by rfl⟩ : syracuseStep 226985 = 170239) B170239
theorem B227327 : Blo 147793 227327 := bstep (se 1 (by rfl) ⟨170495, by rfl⟩ : syracuseStep 227327 = 340991) B340991
theorem B424187 : Blo 147793 424187 := bstep (se 1 (by rfl) ⟨318140, by rfl⟩ : syracuseStep 424187 = 636281) B636281
theorem B227615 : Blo 147793 227615 := bstep (se 1 (by rfl) ⟨170711, by rfl⟩ : syracuseStep 227615 = 341423) B341423
theorem B362407 : Blo 147793 362407 := bstep (se 1 (by rfl) ⟨271805, by rfl⟩ : syracuseStep 362407 = 543611) B543611
theorem B430247 : Blo 147793 430247 := bstep (se 1 (by rfl) ⟨322685, by rfl⟩ : syracuseStep 430247 = 645371) B645371
theorem B14094691 : Blo 147793 14094691 := bstep (se 1 (by rfl) ⟨10571018, by rfl⟩ : syracuseStep 14094691 = 21142037) B21142037
theorem B1282999 : Blo 147793 1282999 := bstep (se 1 (by rfl) ⟨962249, by rfl⟩ : syracuseStep 1282999 = 1924499) B1924499
theorem B1383551 : Blo 147793 1383551 := bstep (se 1 (by rfl) ⟨1037663, by rfl⟩ : syracuseStep 1383551 = 2075327) B2075327
theorem B499823 : Blo 147793 499823 := bstep (se 1 (by rfl) ⟨374867, by rfl⟩ : syracuseStep 499823 = 749735) B749735
theorem B1581935 : Blo 147793 1581935 := bstep (se 1 (by rfl) ⟨1186451, by rfl⟩ : syracuseStep 1581935 = 2372903) B2372903
theorem B238619 : Blo 147793 238619 := bstep (se 1 (by rfl) ⟨178964, by rfl⟩ : syracuseStep 238619 = 357929) B357929
theorem B861313 : Blo 147793 861313 := bstep (se 2 (by rfl) ⟨322992, by rfl⟩ : syracuseStep 861313 = 645985) B645985
theorem B271919 : Blo 147793 271919 := bstep (se 1 (by rfl) ⟨203939, by rfl⟩ : syracuseStep 271919 = 407879) B407879
theorem B338347 : Blo 147793 338347 := bstep (se 1 (by rfl) ⟨253760, by rfl⟩ : syracuseStep 338347 = 507521) B507521
theorem B2140937 : Blo 147793 2140937 := bstep (se 2 (by rfl) ⟨802851, by rfl⟩ : syracuseStep 2140937 = 1605703) B1605703
theorem B26258455 : Blo 147793 26258455 := bstep (se 1 (by rfl) ⟨19693841, by rfl⟩ : syracuseStep 26258455 = 39387683) B39387683
theorem B437275 : Blo 147793 437275 := bstep (se 1 (by rfl) ⟨327956, by rfl⟩ : syracuseStep 437275 = 655913) B655913
theorem B339227 : Blo 147793 339227 := bstep (se 1 (by rfl) ⟨254420, by rfl⟩ : syracuseStep 339227 = 508841) B508841
theorem B4075049 : Blo 147793 4075049 := bstep (se 2 (by rfl) ⟨1528143, by rfl⟩ : syracuseStep 4075049 = 3056287) B3056287
theorem B340649 : Blo 147793 340649 := bstep (se 2 (by rfl) ⟨127743, by rfl⟩ : syracuseStep 340649 = 255487) B255487
theorem B504575 : Blo 147793 504575 := bstep (se 1 (by rfl) ⟨378431, by rfl⟩ : syracuseStep 504575 = 756863) B756863
theorem B571931 : Blo 147793 571931 := bstep (se 1 (by rfl) ⟨428948, by rfl⟩ : syracuseStep 571931 = 857897) B857897
theorem B342719 : Blo 147793 342719 := bstep (se 1 (by rfl) ⟨257039, by rfl⟩ : syracuseStep 342719 = 514079) B514079
theorem B9322361 : Blo 147793 9322361 := bstep (se 2 (by rfl) ⟨3495885, by rfl⟩ : syracuseStep 9322361 = 6991771) B6991771
theorem B868265 : Blo 147793 868265 := bstep (se 2 (by rfl) ⟨325599, by rfl⟩ : syracuseStep 868265 = 651199) B651199
theorem B147871 : Blo 147793 147871 := bstep (se 1 (by rfl) ⟨110903, by rfl⟩ : syracuseStep 147871 = 221807) B221807
theorem B148735 : Blo 147793 148735 := bstep (se 1 (by rfl) ⟨111551, by rfl⟩ : syracuseStep 148735 = 223103) B223103
theorem B148763 : Blo 147793 148763 := bstep (se 1 (by rfl) ⟨111572, by rfl⟩ : syracuseStep 148763 = 223145) B223145
theorem B1132379 : Blo 147793 1132379 := bstep (se 1 (by rfl) ⟨849284, by rfl⟩ : syracuseStep 1132379 = 1698569) B1698569
theorem B6440957 : Blo 147793 6440957 := bstep (se 3 (by rfl) ⟨1207679, by rfl⟩ : syracuseStep 6440957 = 2415359) B2415359
theorem B150175 : Blo 147793 150175 := bstep (se 1 (by rfl) ⟨112631, by rfl⟩ : syracuseStep 150175 = 225263) B225263
theorem B1461149 : Blo 147793 1461149 := bstep (se 3 (by rfl) ⟨273965, by rfl⟩ : syracuseStep 1461149 = 547931) B547931
theorem B150683 : Blo 147793 150683 := bstep (se 1 (by rfl) ⟨113012, by rfl⟩ : syracuseStep 150683 = 226025) B226025
theorem B249527 : Blo 147793 249527 := bstep (se 1 (by rfl) ⟨187145, by rfl⟩ : syracuseStep 249527 = 374291) B374291
theorem B151323 : Blo 147793 151323 := bstep (se 1 (by rfl) ⟨113492, by rfl⟩ : syracuseStep 151323 = 226985) B226985
theorem B151551 : Blo 147793 151551 := bstep (se 1 (by rfl) ⟨113663, by rfl⟩ : syracuseStep 151551 = 227327) B227327
theorem B282791 : Blo 147793 282791 := bstep (se 1 (by rfl) ⟨212093, by rfl⟩ : syracuseStep 282791 = 424187) B424187
theorem B151743 : Blo 147793 151743 := bstep (se 1 (by rfl) ⟨113807, by rfl⟩ : syracuseStep 151743 = 227615) B227615
theorem B251599 : Blo 147793 251599 := bstep (se 1 (by rfl) ⟨188699, by rfl⟩ : syracuseStep 251599 = 377399) B377399
theorem B645097 : Blo 147793 645097 := bstep (se 2 (by rfl) ⟨241911, by rfl⟩ : syracuseStep 645097 = 483823) B483823
theorem B12572813 : Blo 147793 12572813 := bstep (se 3 (by rfl) ⟨2357402, by rfl⟩ : syracuseStep 12572813 = 4714805) B4714805
theorem B252281 : Blo 147793 252281 := bstep (se 2 (by rfl) ⟨94605, by rfl⟩ : syracuseStep 252281 = 189211) B189211
theorem B3792257 : Blo 147793 3792257 := bstep (se 2 (by rfl) ⟨1422096, by rfl⟩ : syracuseStep 3792257 = 2844193) B2844193
theorem B7397891 : Blo 147793 7397891 := bstep (se 1 (by rfl) ⟨5548418, by rfl⟩ : syracuseStep 7397891 = 11096837) B11096837
theorem B1926017 : Blo 147793 1926017 := bstep (se 2 (by rfl) ⟨722256, by rfl⟩ : syracuseStep 1926017 = 1444513) B1444513
theorem B223415 : Blo 147793 223415 := bstep (se 1 (by rfl) ⟨167561, by rfl⟩ : syracuseStep 223415 = 335123) B335123
theorem B682283 : Blo 147793 682283 := bstep (se 1 (by rfl) ⟨511712, by rfl⟩ : syracuseStep 682283 = 1023425) B1023425
theorem B223559 : Blo 147793 223559 := bstep (se 1 (by rfl) ⟨167669, by rfl⟩ : syracuseStep 223559 = 335339) B335339
theorem B7235963 : Blo 147793 7235963 := bstep (se 1 (by rfl) ⟨5426972, by rfl⟩ : syracuseStep 7235963 = 10853945) B10853945
theorem B223727 : Blo 147793 223727 := bstep (se 1 (by rfl) ⟨167795, by rfl⟩ : syracuseStep 223727 = 335591) B335591
theorem B223913 : Blo 147793 223913 := bstep (se 2 (by rfl) ⟨83967, by rfl⟩ : syracuseStep 223913 = 167935) B167935
theorem B322651 : Blo 147793 322651 := bstep (se 1 (by rfl) ⟨241988, by rfl⟩ : syracuseStep 322651 = 483977) B483977
theorem B3927131 : Blo 147793 3927131 := bstep (se 1 (by rfl) ⟨2945348, by rfl⟩ : syracuseStep 3927131 = 5890697) B5890697
theorem B1142905 : Blo 147793 1142905 := bstep (se 2 (by rfl) ⟨428589, by rfl⟩ : syracuseStep 1142905 = 857179) B857179
theorem B1765583 : Blo 147793 1765583 := bstep (se 1 (by rfl) ⟨1324187, by rfl⟩ : syracuseStep 1765583 = 2648375) B2648375
theorem B25130087 : Blo 147793 25130087 := bstep (se 1 (by rfl) ⟨18847565, by rfl⟩ : syracuseStep 25130087 = 37695131) B37695131
theorem B1144043 : Blo 147793 1144043 := bstep (se 1 (by rfl) ⟨858032, by rfl⟩ : syracuseStep 1144043 = 1716065) B1716065
theorem B1602935 : Blo 147793 1602935 := bstep (se 1 (by rfl) ⟨1202201, by rfl⟩ : syracuseStep 1602935 = 2404403) B2404403
theorem B226811 : Blo 147793 226811 := bstep (se 1 (by rfl) ⟨170108, by rfl⟩ : syracuseStep 226811 = 340217) B340217
theorem B1930985 : Blo 147793 1930985 := bstep (se 2 (by rfl) ⟨724119, by rfl⟩ : syracuseStep 1930985 = 1448239) B1448239
theorem B754109 : Blo 147793 754109 := bstep (se 3 (by rfl) ⟨141395, by rfl⟩ : syracuseStep 754109 = 282791) B282791
theorem B754919 : Blo 147793 754919 := bstep (se 1 (by rfl) ⟨566189, by rfl⟩ : syracuseStep 754919 = 1132379) B1132379
theorem B4293971 : Blo 147793 4293971 := bstep (se 1 (by rfl) ⟨3220478, by rfl⟩ : syracuseStep 4293971 = 6440957) B6440957
theorem B1148417 : Blo 147793 1148417 := bstep (se 2 (by rfl) ⟨430656, by rfl⟩ : syracuseStep 1148417 = 861313) B861313
theorem B75171685 : Blo 147793 75171685 := bstep (se 4 (by rfl) ⟨7047345, by rfl⟩ : syracuseStep 75171685 = 14094691) B14094691
theorem B1804517 : Blo 147793 1804517 := bstep (se 4 (by rfl) ⟨169173, by rfl⟩ : syracuseStep 1804517 = 338347) B338347
theorem B166351 : Blo 147793 166351 := bstep (se 1 (by rfl) ⟨124763, by rfl⟩ : syracuseStep 166351 = 249527) B249527
theorem B430201 : Blo 147793 430201 := bstep (se 2 (by rfl) ⟨161325, by rfl⟩ : syracuseStep 430201 = 322651) B322651
theorem B725117 : Blo 147793 725117 := bstep (se 3 (by rfl) ⟨135959, by rfl⟩ : syracuseStep 725117 = 271919) B271919
theorem B168187 : Blo 147793 168187 := bstep (se 1 (by rfl) ⟨126140, by rfl⟩ : syracuseStep 168187 = 252281) B252281
theorem B922367 : Blo 147793 922367 := bstep (se 1 (by rfl) ⟨691775, by rfl⟩ : syracuseStep 922367 = 1383551) B1383551
theorem B2528171 : Blo 147793 2528171 := bstep (se 1 (by rfl) ⟨1896128, by rfl⟩ : syracuseStep 2528171 = 3792257) B3792257
theorem B333215 : Blo 147793 333215 := bstep (se 1 (by rfl) ⟨249911, by rfl⟩ : syracuseStep 333215 = 499823) B499823
theorem B1284011 : Blo 147793 1284011 := bstep (se 1 (by rfl) ⟨963008, by rfl⟩ : syracuseStep 1284011 = 1926017) B1926017
theorem B1710665 : Blo 147793 1710665 := bstep (se 2 (by rfl) ⟨641499, by rfl⟩ : syracuseStep 1710665 = 1282999) B1282999
theorem B4823975 : Blo 147793 4823975 := bstep (se 1 (by rfl) ⟨3617981, by rfl⟩ : syracuseStep 4823975 = 7235963) B7235963
theorem B335465 : Blo 147793 335465 := bstep (se 2 (by rfl) ⟨125799, by rfl⟩ : syracuseStep 335465 = 251599) B251599
theorem B860129 : Blo 147793 860129 := bstep (se 2 (by rfl) ⟨322548, by rfl⟩ : syracuseStep 860129 = 645097) B645097
theorem B336383 : Blo 147793 336383 := bstep (se 1 (by rfl) ⟨252287, by rfl⟩ : syracuseStep 336383 = 504575) B504575
theorem B16753391 : Blo 147793 16753391 := bstep (se 1 (by rfl) ⟨12565043, by rfl⟩ : syracuseStep 16753391 = 25130087) B25130087
theorem B762695 : Blo 147793 762695 := bstep (se 1 (by rfl) ⟨572021, by rfl⟩ : syracuseStep 762695 = 1144043) B1144043
theorem B1287323 : Blo 147793 1287323 := bstep (se 1 (by rfl) ⟨965492, by rfl⟩ : syracuseStep 1287323 = 1930985) B1930985
theorem B35011273 : Blo 147793 35011273 := bstep (se 2 (by rfl) ⟨13129227, by rfl⟩ : syracuseStep 35011273 = 26258455) B26258455
theorem B1523873 : Blo 147793 1523873 := bstep (se 2 (by rfl) ⟨571452, by rfl⟩ : syracuseStep 1523873 = 1142905) B1142905
theorem B4931927 : Blo 147793 4931927 := bstep (se 1 (by rfl) ⟨3698945, by rfl⟩ : syracuseStep 4931927 = 7397891) B7397891
theorem B148943 : Blo 147793 148943 := bstep (se 1 (by rfl) ⟨111707, by rfl⟩ : syracuseStep 148943 = 223415) B223415
theorem B149039 : Blo 147793 149039 := bstep (se 1 (by rfl) ⟨111779, by rfl⟩ : syracuseStep 149039 = 223559) B223559
theorem B149151 : Blo 147793 149151 := bstep (se 1 (by rfl) ⟨111863, by rfl⟩ : syracuseStep 149151 = 223727) B223727
theorem B149275 : Blo 147793 149275 := bstep (se 1 (by rfl) ⟨111956, by rfl⟩ : syracuseStep 149275 = 223913) B223913
theorem B1427291 : Blo 147793 1427291 := bstep (se 1 (by rfl) ⟨1070468, by rfl⟩ : syracuseStep 1427291 = 2140937) B2140937
theorem B1068623 : Blo 147793 1068623 := bstep (se 1 (by rfl) ⟨801467, by rfl⟩ : syracuseStep 1068623 = 1602935) B1602935
theorem B151207 : Blo 147793 151207 := bstep (se 1 (by rfl) ⟨113405, by rfl⟩ : syracuseStep 151207 = 226811) B226811
theorem B381287 : Blo 147793 381287 := bstep (se 1 (by rfl) ⟨285965, by rfl⟩ : syracuseStep 381287 = 571931) B571931
theorem B6214907 : Blo 147793 6214907 := bstep (se 1 (by rfl) ⟨4661180, by rfl⟩ : syracuseStep 6214907 = 9322361) B9322361
theorem B578843 : Blo 147793 578843 := bstep (se 1 (by rfl) ⟨434132, by rfl⟩ : syracuseStep 578843 = 868265) B868265
theorem B974099 : Blo 147793 974099 := bstep (se 1 (by rfl) ⟨730574, by rfl⟩ : syracuseStep 974099 = 1461149) B1461149
theorem B4218493 : Blo 147793 4218493 := bstep (se 3 (by rfl) ⟨790967, by rfl⟩ : syracuseStep 4218493 = 1581935) B1581935
theorem B483209 : Blo 147793 483209 := bstep (se 2 (by rfl) ⟨181203, by rfl⟩ : syracuseStep 483209 = 362407) B362407
theorem B286831 : Blo 147793 286831 := bstep (se 1 (by rfl) ⟨215123, by rfl⟩ : syracuseStep 286831 = 430247) B430247
theorem B583033 : Blo 147793 583033 := bstep (se 2 (by rfl) ⟨218637, by rfl⟩ : syracuseStep 583033 = 437275) B437275
theorem B8381875 : Blo 147793 8381875 := bstep (se 1 (by rfl) ⟨6286406, by rfl⟩ : syracuseStep 8381875 = 12572813) B12572813
theorem B159079 : Blo 147793 159079 := bstep (se 1 (by rfl) ⟨119309, by rfl⟩ : syracuseStep 159079 = 238619) B238619
theorem B454855 : Blo 147793 454855 := bstep (se 1 (by rfl) ⟨341141, by rfl⟩ : syracuseStep 454855 = 682283) B682283
theorem B2618087 : Blo 147793 2618087 := bstep (se 1 (by rfl) ⟨1963565, by rfl⟩ : syracuseStep 2618087 = 3927131) B3927131
theorem B226151 : Blo 147793 226151 := bstep (se 1 (by rfl) ⟨169613, by rfl⟩ : syracuseStep 226151 = 339227) B339227
theorem B2716699 : Blo 147793 2716699 := bstep (se 1 (by rfl) ⟨2037524, by rfl⟩ : syracuseStep 2716699 = 4075049) B4075049
theorem B1177055 : Blo 147793 1177055 := bstep (se 1 (by rfl) ⟨882791, by rfl⟩ : syracuseStep 1177055 = 1765583) B1765583
theorem B227099 : Blo 147793 227099 := bstep (se 1 (by rfl) ⟨170324, by rfl⟩ : syracuseStep 227099 = 340649) B340649
theorem B228479 : Blo 147793 228479 := bstep (se 1 (by rfl) ⟨171359, by rfl⟩ : syracuseStep 228479 = 342719) B342719
theorem B1015915 : Blo 147793 1015915 := bstep (se 1 (by rfl) ⟨761936, by rfl⟩ : syracuseStep 1015915 = 1523873) B1523873
theorem B1933645 : Blo 147793 1933645 := bstep (se 3 (by rfl) ⟨362558, by rfl⟩ : syracuseStep 1933645 = 725117) B725117
theorem B951527 : Blo 147793 951527 := bstep (se 1 (by rfl) ⟨713645, by rfl⟩ : syracuseStep 951527 = 1427291) B1427291
theorem B11175833 : Blo 147793 11175833 := bstep (se 2 (by rfl) ⟨4190937, by rfl⟩ : syracuseStep 11175833 = 8381875) B8381875
theorem B6981565 : Blo 147793 6981565 := bstep (se 3 (by rfl) ⟨1309043, by rfl⟩ : syracuseStep 6981565 = 2618087) B2618087
theorem B2459645 : Blo 147793 2459645 := bstep (se 3 (by rfl) ⟨461183, by rfl⟩ : syracuseStep 2459645 = 922367) B922367
theorem B856007 : Blo 147793 856007 := bstep (se 1 (by rfl) ⟨642005, by rfl⟩ : syracuseStep 856007 = 1284011) B1284011
theorem B3215983 : Blo 147793 3215983 := bstep (se 1 (by rfl) ⟨2411987, by rfl⟩ : syracuseStep 3215983 = 4823975) B4823975
theorem B858215 : Blo 147793 858215 := bstep (se 1 (by rfl) ⟨643661, by rfl⟩ : syracuseStep 858215 = 1287323) B1287323
theorem B3287951 : Blo 147793 3287951 := bstep (se 1 (by rfl) ⟨2465963, by rfl⟩ : syracuseStep 3287951 = 4931927) B4931927
theorem B502739 : Blo 147793 502739 := bstep (se 1 (by rfl) ⟨377054, by rfl⟩ : syracuseStep 502739 = 754109) B754109
theorem B503279 : Blo 147793 503279 := bstep (se 1 (by rfl) ⟨377459, by rfl⟩ : syracuseStep 503279 = 754919) B754919
theorem B2862647 : Blo 147793 2862647 := bstep (se 1 (by rfl) ⟨2146985, by rfl⟩ : syracuseStep 2862647 = 4293971) B4293971
theorem B765611 : Blo 147793 765611 := bstep (se 1 (by rfl) ⟨574208, by rfl⟩ : syracuseStep 765611 = 1148417) B1148417
theorem B1685447 : Blo 147793 1685447 := bstep (se 1 (by rfl) ⟨1264085, by rfl⟩ : syracuseStep 1685447 = 2528171) B2528171
theorem B4143271 : Blo 147793 4143271 := bstep (se 1 (by rfl) ⟨3107453, by rfl⟩ : syracuseStep 4143271 = 6214907) B6214907
theorem B212105 : Blo 147793 212105 := bstep (se 2 (by rfl) ⟨79539, by rfl⟩ : syracuseStep 212105 = 159079) B159079
theorem B573419 : Blo 147793 573419 := bstep (se 1 (by rfl) ⟨430064, by rfl⟩ : syracuseStep 573419 = 860129) B860129
theorem B573601 : Blo 147793 573601 := bstep (se 2 (by rfl) ⟨215100, by rfl⟩ : syracuseStep 573601 = 430201) B430201
theorem B606473 : Blo 147793 606473 := bstep (se 2 (by rfl) ⟨227427, by rfl⟩ : syracuseStep 606473 = 454855) B454855
theorem B508463 : Blo 147793 508463 := bstep (se 1 (by rfl) ⟨381347, by rfl⟩ : syracuseStep 508463 = 762695) B762695
theorem B3622265 : Blo 147793 3622265 := bstep (se 2 (by rfl) ⟨1358349, by rfl⟩ : syracuseStep 3622265 = 2716699) B2716699
theorem B609277 : Blo 147793 609277 := bstep (se 3 (by rfl) ⟨114239, by rfl⟩ : syracuseStep 609277 = 228479) B228479
theorem B150767 : Blo 147793 150767 := bstep (se 1 (by rfl) ⟨113075, by rfl⟩ : syracuseStep 150767 = 226151) B226151
theorem B46681697 : Blo 147793 46681697 := bstep (se 2 (by rfl) ⟨17505636, by rfl⟩ : syracuseStep 46681697 = 35011273) B35011273
theorem B151399 : Blo 147793 151399 := bstep (se 1 (by rfl) ⟨113549, by rfl⟩ : syracuseStep 151399 = 227099) B227099
theorem B5624657 : Blo 147793 5624657 := bstep (se 2 (by rfl) ⟨2109246, by rfl⟩ : syracuseStep 5624657 = 4218493) B4218493
theorem B382441 : Blo 147793 382441 := bstep (se 2 (by rfl) ⟨143415, by rfl⟩ : syracuseStep 382441 = 286831) B286831
theorem B1203011 : Blo 147793 1203011 := bstep (se 1 (by rfl) ⟨902258, by rfl⟩ : syracuseStep 1203011 = 1804517) B1804517
theorem B777377 : Blo 147793 777377 := bstep (se 2 (by rfl) ⟨291516, by rfl⟩ : syracuseStep 777377 = 583033) B583033
theorem B712415 : Blo 147793 712415 := bstep (se 1 (by rfl) ⟨534311, by rfl⟩ : syracuseStep 712415 = 1068623) B1068623
theorem B100228913 : Blo 147793 100228913 := bstep (se 2 (by rfl) ⟨37585842, by rfl⟩ : syracuseStep 100228913 = 75171685) B75171685
theorem B254191 : Blo 147793 254191 := bstep (se 1 (by rfl) ⟨190643, by rfl⟩ : syracuseStep 254191 = 381287) B381287
theorem B221801 : Blo 147793 221801 := bstep (se 2 (by rfl) ⟨83175, by rfl⟩ : syracuseStep 221801 = 166351) B166351
theorem B385895 : Blo 147793 385895 := bstep (se 1 (by rfl) ⟨289421, by rfl⟩ : syracuseStep 385895 = 578843) B578843
theorem B222143 : Blo 147793 222143 := bstep (se 1 (by rfl) ⟨166607, by rfl⟩ : syracuseStep 222143 = 333215) B333215
theorem B1140443 : Blo 147793 1140443 := bstep (se 1 (by rfl) ⟨855332, by rfl⟩ : syracuseStep 1140443 = 1710665) B1710665
theorem B649399 : Blo 147793 649399 := bstep (se 1 (by rfl) ⟨487049, by rfl⟩ : syracuseStep 649399 = 974099) B974099
theorem B223643 : Blo 147793 223643 := bstep (se 1 (by rfl) ⟨167732, by rfl⟩ : syracuseStep 223643 = 335465) B335465
theorem B322139 : Blo 147793 322139 := bstep (se 1 (by rfl) ⟨241604, by rfl⟩ : syracuseStep 322139 = 483209) B483209
theorem B224249 : Blo 147793 224249 := bstep (se 2 (by rfl) ⟨84093, by rfl⟩ : syracuseStep 224249 = 168187) B168187
theorem B224255 : Blo 147793 224255 := bstep (se 1 (by rfl) ⟨168191, by rfl⟩ : syracuseStep 224255 = 336383) B336383
theorem B11168927 : Blo 147793 11168927 := bstep (se 1 (by rfl) ⟨8376695, by rfl⟩ : syracuseStep 11168927 = 16753391) B16753391
theorem B784703 : Blo 147793 784703 := bstep (se 1 (by rfl) ⟨588527, by rfl⟩ : syracuseStep 784703 = 1177055) B1177055
theorem B1639763 : Blo 147793 1639763 := bstep (se 1 (by rfl) ⟨1229822, by rfl⟩ : syracuseStep 1639763 = 2459645) B2459645
theorem B9308753 : Blo 147793 9308753 := bstep (se 2 (by rfl) ⟨3490782, by rfl⟩ : syracuseStep 9308753 = 6981565) B6981565
theorem B201865 : Blo 147793 201865 := bstep (se 2 (by rfl) ⟨75699, by rfl⟩ : syracuseStep 201865 = 151399) B151399
theorem B66819275 : Blo 147793 66819275 := bstep (se 1 (by rfl) ⟨50114456, by rfl⟩ : syracuseStep 66819275 = 100228913) B100228913
theorem B760295 : Blo 147793 760295 := bstep (se 1 (by rfl) ⟨570221, by rfl⟩ : syracuseStep 760295 = 1140443) B1140443
theorem B335159 : Blo 147793 335159 := bstep (se 1 (by rfl) ⟨251369, by rfl⟩ : syracuseStep 335159 = 502739) B502739
theorem B7445951 : Blo 147793 7445951 := bstep (se 1 (by rfl) ⟨5584463, by rfl⟩ : syracuseStep 7445951 = 11168927) B11168927
theorem B335519 : Blo 147793 335519 := bstep (se 1 (by rfl) ⟨251639, by rfl⟩ : syracuseStep 335519 = 503279) B503279
theorem B1908431 : Blo 147793 1908431 := bstep (se 1 (by rfl) ⟨1431323, by rfl⟩ : syracuseStep 1908431 = 2862647) B2862647
theorem B565613 : Blo 147793 565613 := bstep (se 3 (by rfl) ⟨106052, by rfl⟩ : syracuseStep 565613 = 212105) B212105
theorem B1123631 : Blo 147793 1123631 := bstep (se 1 (by rfl) ⟨842723, by rfl⟩ : syracuseStep 1123631 = 1685447) B1685447
theorem B1354553 : Blo 147793 1354553 := bstep (se 2 (by rfl) ⟨507957, by rfl⟩ : syracuseStep 1354553 = 1015915) B1015915
theorem B404315 : Blo 147793 404315 := bstep (se 1 (by rfl) ⟨303236, by rfl⟩ : syracuseStep 404315 = 606473) B606473
theorem B764801 : Blo 147793 764801 := bstep (se 2 (by rfl) ⟨286800, by rfl⟩ : syracuseStep 764801 = 573601) B573601
theorem B338921 : Blo 147793 338921 := bstep (se 2 (by rfl) ⟨127095, by rfl⟩ : syracuseStep 338921 = 254191) B254191
theorem B338975 : Blo 147793 338975 := bstep (se 1 (by rfl) ⟨254231, by rfl⟩ : syracuseStep 338975 = 508463) B508463
theorem B634351 : Blo 147793 634351 := bstep (se 1 (by rfl) ⟨475763, by rfl⟩ : syracuseStep 634351 = 951527) B951527
theorem B7450555 : Blo 147793 7450555 := bstep (se 1 (by rfl) ⟨5587916, by rfl⟩ : syracuseStep 7450555 = 11175833) B11175833
theorem B570671 : Blo 147793 570671 := bstep (se 1 (by rfl) ⟨428003, by rfl⟩ : syracuseStep 570671 = 856007) B856007
theorem B865865 : Blo 147793 865865 := bstep (se 2 (by rfl) ⟨324699, by rfl⟩ : syracuseStep 865865 = 649399) B649399
theorem B3749771 : Blo 147793 3749771 := bstep (se 1 (by rfl) ⟨2812328, by rfl⟩ : syracuseStep 3749771 = 5624657) B5624657
theorem B572143 : Blo 147793 572143 := bstep (se 1 (by rfl) ⟨429107, by rfl⟩ : syracuseStep 572143 = 858215) B858215
theorem B802007 : Blo 147793 802007 := bstep (se 1 (by rfl) ⟨601505, by rfl⟩ : syracuseStep 802007 = 1203011) B1203011
theorem B147867 : Blo 147793 147867 := bstep (se 1 (by rfl) ⟨110900, by rfl⟩ : syracuseStep 147867 = 221801) B221801
theorem B148095 : Blo 147793 148095 := bstep (se 1 (by rfl) ⟨111071, by rfl⟩ : syracuseStep 148095 = 222143) B222143
theorem B149095 : Blo 147793 149095 := bstep (se 1 (by rfl) ⟨111821, by rfl⟩ : syracuseStep 149095 = 223643) B223643
theorem B214759 : Blo 147793 214759 := bstep (se 1 (by rfl) ⟨161069, by rfl⟩ : syracuseStep 214759 = 322139) B322139
theorem B509921 : Blo 147793 509921 := bstep (se 2 (by rfl) ⟨191220, by rfl⟩ : syracuseStep 509921 = 382441) B382441
theorem B149499 : Blo 147793 149499 := bstep (se 1 (by rfl) ⟨112124, by rfl⟩ : syracuseStep 149499 = 224249) B224249
theorem B149503 : Blo 147793 149503 := bstep (se 1 (by rfl) ⟨112127, by rfl⟩ : syracuseStep 149503 = 224255) B224255
theorem B510407 : Blo 147793 510407 := bstep (se 1 (by rfl) ⟨382805, by rfl⟩ : syracuseStep 510407 = 765611) B765611
theorem B5524361 : Blo 147793 5524361 := bstep (se 2 (by rfl) ⟨2071635, by rfl⟩ : syracuseStep 5524361 = 4143271) B4143271
theorem B382279 : Blo 147793 382279 := bstep (se 1 (by rfl) ⟨286709, by rfl⟩ : syracuseStep 382279 = 573419) B573419
theorem B2578193 : Blo 147793 2578193 := bstep (se 2 (by rfl) ⟨966822, by rfl⟩ : syracuseStep 2578193 = 1933645) B1933645
theorem B2414843 : Blo 147793 2414843 := bstep (se 1 (by rfl) ⟨1811132, by rfl⟩ : syracuseStep 2414843 = 3622265) B3622265
theorem B31121131 : Blo 147793 31121131 := bstep (se 1 (by rfl) ⟨23340848, by rfl⟩ : syracuseStep 31121131 = 46681697) B46681697
theorem B812369 : Blo 147793 812369 := bstep (se 2 (by rfl) ⟨304638, by rfl⟩ : syracuseStep 812369 = 609277) B609277
theorem B518251 : Blo 147793 518251 := bstep (se 1 (by rfl) ⟨388688, by rfl⟩ : syracuseStep 518251 = 777377) B777377
theorem B257263 : Blo 147793 257263 := bstep (se 1 (by rfl) ⟨192947, by rfl⟩ : syracuseStep 257263 = 385895) B385895
theorem B4287977 : Blo 147793 4287977 := bstep (se 2 (by rfl) ⟨1607991, by rfl⟩ : syracuseStep 4287977 = 3215983) B3215983
theorem B2191967 : Blo 147793 2191967 := bstep (se 1 (by rfl) ⟨1643975, by rfl⟩ : syracuseStep 2191967 = 3287951) B3287951
theorem B523135 : Blo 147793 523135 := bstep (se 1 (by rfl) ⟨392351, by rfl⟩ : syracuseStep 523135 = 784703) B784703
theorem B1899773 : Blo 147793 1899773 := bstep (se 3 (by rfl) ⟨356207, by rfl⟩ : syracuseStep 1899773 = 712415) B712415
theorem B691001 : Blo 147793 691001 := bstep (se 2 (by rfl) ⟨259125, by rfl⟩ : syracuseStep 691001 = 518251) B518251
theorem B1609895 : Blo 147793 1609895 := bstep (se 1 (by rfl) ⟨1207421, by rfl⟩ : syracuseStep 1609895 = 2414843) B2414843
theorem B9999389 : Blo 147793 9999389 := bstep (se 3 (by rfl) ⟨1874885, by rfl⟩ : syracuseStep 9999389 = 3749771) B3749771
theorem B9934073 : Blo 147793 9934073 := bstep (se 2 (by rfl) ⟨3725277, by rfl⟩ : syracuseStep 9934073 = 7450555) B7450555
theorem B269153 : Blo 147793 269153 := bstep (se 2 (by rfl) ⟨100932, by rfl⟩ : syracuseStep 269153 = 201865) B201865
theorem B269543 : Blo 147793 269543 := bstep (se 1 (by rfl) ⟨202157, by rfl⟩ : syracuseStep 269543 = 404315) B404315
theorem B2858651 : Blo 147793 2858651 := bstep (se 1 (by rfl) ⟨2143988, by rfl⟩ : syracuseStep 2858651 = 4287977) B4287977
theorem B762857 : Blo 147793 762857 := bstep (se 2 (by rfl) ⟨286071, by rfl⟩ : syracuseStep 762857 = 572143) B572143
theorem B697513 : Blo 147793 697513 := bstep (se 2 (by rfl) ⟨261567, by rfl⟩ : syracuseStep 697513 = 523135) B523135
theorem B534671 : Blo 147793 534671 := bstep (se 1 (by rfl) ⟨401003, by rfl⟩ : syracuseStep 534671 = 802007) B802007
theorem B41494841 : Blo 147793 41494841 := bstep (se 2 (by rfl) ⟨15560565, by rfl⟩ : syracuseStep 41494841 = 31121131) B31121131
theorem B1093175 : Blo 147793 1093175 := bstep (se 1 (by rfl) ⟨819881, by rfl⟩ : syracuseStep 1093175 = 1639763) B1639763
theorem B339947 : Blo 147793 339947 := bstep (se 1 (by rfl) ⟨254960, by rfl⟩ : syracuseStep 339947 = 509921) B509921
theorem B340271 : Blo 147793 340271 := bstep (se 1 (by rfl) ⟨255203, by rfl⟩ : syracuseStep 340271 = 510407) B510407
theorem B6205835 : Blo 147793 6205835 := bstep (se 1 (by rfl) ⟨4654376, by rfl⟩ : syracuseStep 6205835 = 9308753) B9308753
theorem B3682907 : Blo 147793 3682907 := bstep (se 1 (by rfl) ⟨2762180, by rfl⟩ : syracuseStep 3682907 = 5524361) B5524361
theorem B44546183 : Blo 147793 44546183 := bstep (se 1 (by rfl) ⟨33409637, by rfl⟩ : syracuseStep 44546183 = 66819275) B66819275
theorem B1718795 : Blo 147793 1718795 := bstep (se 1 (by rfl) ⟨1289096, by rfl⟩ : syracuseStep 1718795 = 2578193) B2578193
theorem B506863 : Blo 147793 506863 := bstep (se 1 (by rfl) ⟨380147, by rfl⟩ : syracuseStep 506863 = 760295) B760295
theorem B4963967 : Blo 147793 4963967 := bstep (se 1 (by rfl) ⟨3722975, by rfl⟩ : syracuseStep 4963967 = 7445951) B7445951
theorem B377075 : Blo 147793 377075 := bstep (se 1 (by rfl) ⟨282806, by rfl⟩ : syracuseStep 377075 = 565613) B565613
theorem B541579 : Blo 147793 541579 := bstep (se 1 (by rfl) ⟨406184, by rfl⟩ : syracuseStep 541579 = 812369) B812369
theorem B509705 : Blo 147793 509705 := bstep (se 2 (by rfl) ⟨191139, by rfl⟩ : syracuseStep 509705 = 382279) B382279
theorem B903035 : Blo 147793 903035 := bstep (se 1 (by rfl) ⟨677276, by rfl⟩ : syracuseStep 903035 = 1354553) B1354553
theorem B509867 : Blo 147793 509867 := bstep (se 1 (by rfl) ⟨382400, by rfl⟩ : syracuseStep 509867 = 764801) B764801
theorem B1461311 : Blo 147793 1461311 := bstep (se 1 (by rfl) ⟨1095983, by rfl⟩ : syracuseStep 1461311 = 2191967) B2191967
theorem B380447 : Blo 147793 380447 := bstep (se 1 (by rfl) ⟨285335, by rfl⟩ : syracuseStep 380447 = 570671) B570671
theorem B577243 : Blo 147793 577243 := bstep (se 1 (by rfl) ⟨432932, by rfl⟩ : syracuseStep 577243 = 865865) B865865
theorem B1266515 : Blo 147793 1266515 := bstep (se 1 (by rfl) ⟨949886, by rfl⟩ : syracuseStep 1266515 = 1899773) B1899773
theorem B286345 : Blo 147793 286345 := bstep (se 2 (by rfl) ⟨107379, by rfl⟩ : syracuseStep 286345 = 214759) B214759
theorem B845801 : Blo 147793 845801 := bstep (se 2 (by rfl) ⟨317175, by rfl⟩ : syracuseStep 845801 = 634351) B634351
theorem B223439 : Blo 147793 223439 := bstep (se 1 (by rfl) ⟨167579, by rfl⟩ : syracuseStep 223439 = 335159) B335159
theorem B223679 : Blo 147793 223679 := bstep (se 1 (by rfl) ⟨167759, by rfl⟩ : syracuseStep 223679 = 335519) B335519
theorem B1272287 : Blo 147793 1272287 := bstep (se 1 (by rfl) ⟨954215, by rfl⟩ : syracuseStep 1272287 = 1908431) B1908431
theorem B749087 : Blo 147793 749087 := bstep (se 1 (by rfl) ⟨561815, by rfl⟩ : syracuseStep 749087 = 1123631) B1123631
theorem B1372069 : Blo 147793 1372069 := bstep (se 4 (by rfl) ⟨128631, by rfl⟩ : syracuseStep 1372069 = 257263) B257263
theorem B225947 : Blo 147793 225947 := bstep (se 1 (by rfl) ⟨169460, by rfl⟩ : syracuseStep 225947 = 338921) B338921
theorem B225983 : Blo 147793 225983 := bstep (se 1 (by rfl) ⟨169487, by rfl⟩ : syracuseStep 225983 = 338975) B338975
theorem B16548893 : Blo 147793 16548893 := bstep (se 3 (by rfl) ⟨3102917, by rfl⟩ : syracuseStep 16548893 = 6205835) B6205835
theorem B722105 : Blo 147793 722105 := bstep (se 2 (by rfl) ⟨270789, by rfl⟩ : syracuseStep 722105 = 541579) B541579
theorem B460667 : Blo 147793 460667 := bstep (se 1 (by rfl) ⟨345500, by rfl⟩ : syracuseStep 460667 = 691001) B691001
theorem B6622715 : Blo 147793 6622715 := bstep (se 1 (by rfl) ⟨4967036, by rfl⟩ : syracuseStep 6622715 = 9934073) B9934073
theorem B1905767 : Blo 147793 1905767 := bstep (se 1 (by rfl) ⟨1429325, by rfl⟩ : syracuseStep 1905767 = 2858651) B2858651
theorem B563867 : Blo 147793 563867 := bstep (se 1 (by rfl) ⟨422900, by rfl⟩ : syracuseStep 563867 = 845801) B845801
theorem B27663227 : Blo 147793 27663227 := bstep (se 1 (by rfl) ⟨20747420, by rfl⟩ : syracuseStep 27663227 = 41494841) B41494841
theorem B499391 : Blo 147793 499391 := bstep (se 1 (by rfl) ⟨374543, by rfl⟩ : syracuseStep 499391 = 749087) B749087
theorem B728783 : Blo 147793 728783 := bstep (se 1 (by rfl) ⟨546587, by rfl⟩ : syracuseStep 728783 = 1093175) B1093175
theorem B29697455 : Blo 147793 29697455 := bstep (se 1 (by rfl) ⟨22273091, by rfl⟩ : syracuseStep 29697455 = 44546183) B44546183
theorem B7317701 : Blo 147793 7317701 := bstep (se 4 (by rfl) ⟨686034, by rfl⟩ : syracuseStep 7317701 = 1372069) B1372069
theorem B339803 : Blo 147793 339803 := bstep (se 1 (by rfl) ⟨254852, by rfl⟩ : syracuseStep 339803 = 509705) B509705
theorem B339911 : Blo 147793 339911 := bstep (se 1 (by rfl) ⟨254933, by rfl⟩ : syracuseStep 339911 = 509867) B509867
theorem B930017 : Blo 147793 930017 := bstep (se 2 (by rfl) ⟨348756, by rfl⟩ : syracuseStep 930017 = 697513) B697513
theorem B6666259 : Blo 147793 6666259 := bstep (se 1 (by rfl) ⟨4999694, by rfl⟩ : syracuseStep 6666259 = 9999389) B9999389
theorem B179435 : Blo 147793 179435 := bstep (se 1 (by rfl) ⟨134576, by rfl⟩ : syracuseStep 179435 = 269153) B269153
theorem B179695 : Blo 147793 179695 := bstep (se 1 (by rfl) ⟨134771, by rfl⟩ : syracuseStep 179695 = 269543) B269543
theorem B769657 : Blo 147793 769657 := bstep (se 2 (by rfl) ⟨288621, by rfl⟩ : syracuseStep 769657 = 577243) B577243
theorem B2408093 : Blo 147793 2408093 := bstep (se 3 (by rfl) ⟨451517, by rfl⟩ : syracuseStep 2408093 = 903035) B903035
theorem B2703269 : Blo 147793 2703269 := bstep (se 4 (by rfl) ⟨253431, by rfl⟩ : syracuseStep 2703269 = 506863) B506863
theorem B508571 : Blo 147793 508571 := bstep (se 1 (by rfl) ⟨381428, by rfl⟩ : syracuseStep 508571 = 762857) B762857
theorem B148959 : Blo 147793 148959 := bstep (se 1 (by rfl) ⟨111719, by rfl⟩ : syracuseStep 148959 = 223439) B223439
theorem B149119 : Blo 147793 149119 := bstep (se 1 (by rfl) ⟨111839, by rfl⟩ : syracuseStep 149119 = 223679) B223679
theorem B150631 : Blo 147793 150631 := bstep (se 1 (by rfl) ⟨112973, by rfl⟩ : syracuseStep 150631 = 225947) B225947
theorem B150655 : Blo 147793 150655 := bstep (se 1 (by rfl) ⟨112991, by rfl⟩ : syracuseStep 150655 = 225983) B225983
theorem B381793 : Blo 147793 381793 := bstep (se 2 (by rfl) ⟨143172, by rfl⟩ : syracuseStep 381793 = 286345) B286345
theorem B251383 : Blo 147793 251383 := bstep (se 1 (by rfl) ⟨188537, by rfl⟩ : syracuseStep 251383 = 377075) B377075
theorem B974207 : Blo 147793 974207 := bstep (se 1 (by rfl) ⟨730655, by rfl⟩ : syracuseStep 974207 = 1461311) B1461311
theorem B253631 : Blo 147793 253631 := bstep (se 1 (by rfl) ⟨190223, by rfl⟩ : syracuseStep 253631 = 380447) B380447
theorem B1073263 : Blo 147793 1073263 := bstep (se 1 (by rfl) ⟨804947, by rfl⟩ : syracuseStep 1073263 = 1609895) B1609895
theorem B844343 : Blo 147793 844343 := bstep (se 1 (by rfl) ⟨633257, by rfl⟩ : syracuseStep 844343 = 1266515) B1266515
theorem B356447 : Blo 147793 356447 := bstep (se 1 (by rfl) ⟨267335, by rfl⟩ : syracuseStep 356447 = 534671) B534671
theorem B848191 : Blo 147793 848191 := bstep (se 1 (by rfl) ⟨636143, by rfl⟩ : syracuseStep 848191 = 1272287) B1272287
theorem B226631 : Blo 147793 226631 := bstep (se 1 (by rfl) ⟨169973, by rfl⟩ : syracuseStep 226631 = 339947) B339947
theorem B226847 : Blo 147793 226847 := bstep (se 1 (by rfl) ⟨170135, by rfl⟩ : syracuseStep 226847 = 340271) B340271
theorem B2455271 : Blo 147793 2455271 := bstep (se 1 (by rfl) ⟨1841453, by rfl⟩ : syracuseStep 2455271 = 3682907) B3682907
theorem B1145863 : Blo 147793 1145863 := bstep (se 1 (by rfl) ⟨859397, by rfl⟩ : syracuseStep 1145863 = 1718795) B1718795
theorem B3309311 : Blo 147793 3309311 := bstep (se 1 (by rfl) ⟨2481983, by rfl⟩ : syracuseStep 3309311 = 4963967) B4963967
theorem B950525 : Blo 147793 950525 := bstep (se 3 (by rfl) ⟨178223, by rfl⟩ : syracuseStep 950525 = 356447) B356447
theorem B332927 : Blo 147793 332927 := bstep (se 1 (by rfl) ⟨249695, by rfl⟩ : syracuseStep 332927 = 499391) B499391
theorem B169087 : Blo 147793 169087 := bstep (se 1 (by rfl) ⟨126815, by rfl⟩ : syracuseStep 169087 = 253631) B253631
theorem B562895 : Blo 147793 562895 := bstep (se 1 (by rfl) ⟨422171, by rfl⟩ : syracuseStep 562895 = 844343) B844343
theorem B335177 : Blo 147793 335177 := bstep (se 2 (by rfl) ⟨125691, by rfl⟩ : syracuseStep 335177 = 251383) B251383
theorem B8888345 : Blo 147793 8888345 := bstep (se 2 (by rfl) ⟨3333129, by rfl⟩ : syracuseStep 8888345 = 6666259) B6666259
theorem B239593 : Blo 147793 239593 := bstep (se 2 (by rfl) ⟨89847, by rfl⟩ : syracuseStep 239593 = 179695) B179695
theorem B1026209 : Blo 147793 1026209 := bstep (se 2 (by rfl) ⟨384828, by rfl⟩ : syracuseStep 1026209 = 769657) B769657
theorem B2206207 : Blo 147793 2206207 := bstep (se 1 (by rfl) ⟨1654655, by rfl⟩ : syracuseStep 2206207 = 3309311) B3309311
theorem B339047 : Blo 147793 339047 := bstep (se 1 (by rfl) ⟨254285, by rfl⟩ : syracuseStep 339047 = 508571) B508571
theorem B307111 : Blo 147793 307111 := bstep (se 1 (by rfl) ⟨230333, by rfl⟩ : syracuseStep 307111 = 460667) B460667
theorem B375911 : Blo 147793 375911 := bstep (se 1 (by rfl) ⟨281933, by rfl⟩ : syracuseStep 375911 = 563867) B563867
theorem B1130921 : Blo 147793 1130921 := bstep (se 2 (by rfl) ⟨424095, by rfl⟩ : syracuseStep 1130921 = 848191) B848191
theorem B509057 : Blo 147793 509057 := bstep (se 2 (by rfl) ⟨190896, by rfl⟩ : syracuseStep 509057 = 381793) B381793
theorem B478493 : Blo 147793 478493 := bstep (se 3 (by rfl) ⟨89717, by rfl⟩ : syracuseStep 478493 = 179435) B179435
theorem B151087 : Blo 147793 151087 := bstep (se 1 (by rfl) ⟨113315, by rfl⟩ : syracuseStep 151087 = 226631) B226631
theorem B151231 : Blo 147793 151231 := bstep (se 1 (by rfl) ⟨113423, by rfl⟩ : syracuseStep 151231 = 226847) B226847
theorem B1527817 : Blo 147793 1527817 := bstep (se 2 (by rfl) ⟨572931, by rfl⟩ : syracuseStep 1527817 = 1145863) B1145863
theorem B1431017 : Blo 147793 1431017 := bstep (se 2 (by rfl) ⟨536631, by rfl⟩ : syracuseStep 1431017 = 1073263) B1073263
theorem B11032595 : Blo 147793 11032595 := bstep (se 1 (by rfl) ⟨8274446, by rfl⟩ : syracuseStep 11032595 = 16548893) B16548893
theorem B481403 : Blo 147793 481403 := bstep (se 1 (by rfl) ⟨361052, by rfl⟩ : syracuseStep 481403 = 722105) B722105
theorem B4415143 : Blo 147793 4415143 := bstep (se 1 (by rfl) ⟨3311357, by rfl⟩ : syracuseStep 4415143 = 6622715) B6622715
theorem B1270511 : Blo 147793 1270511 := bstep (se 1 (by rfl) ⟨952883, by rfl⟩ : syracuseStep 1270511 = 1905767) B1905767
theorem B79193213 : Blo 147793 79193213 := bstep (se 3 (by rfl) ⟨14848727, by rfl⟩ : syracuseStep 79193213 = 29697455) B29697455
theorem B18442151 : Blo 147793 18442151 := bstep (se 1 (by rfl) ⟨13831613, by rfl⟩ : syracuseStep 18442151 = 27663227) B27663227
theorem B649471 : Blo 147793 649471 := bstep (se 1 (by rfl) ⟨487103, by rfl⟩ : syracuseStep 649471 = 974207) B974207
theorem B485855 : Blo 147793 485855 := bstep (se 1 (by rfl) ⟨364391, by rfl⟩ : syracuseStep 485855 = 728783) B728783
theorem B4878467 : Blo 147793 4878467 := bstep (se 1 (by rfl) ⟨3658850, by rfl⟩ : syracuseStep 4878467 = 7317701) B7317701
theorem B226535 : Blo 147793 226535 := bstep (se 1 (by rfl) ⟨169901, by rfl⟩ : syracuseStep 226535 = 339803) B339803
theorem B226607 : Blo 147793 226607 := bstep (se 1 (by rfl) ⟨169955, by rfl⟩ : syracuseStep 226607 = 339911) B339911
theorem B620011 : Blo 147793 620011 := bstep (se 1 (by rfl) ⟨465008, by rfl⟩ : syracuseStep 620011 = 930017) B930017
theorem B1636847 : Blo 147793 1636847 := bstep (se 1 (by rfl) ⟨1227635, by rfl⟩ : syracuseStep 1636847 = 2455271) B2455271
theorem B1605395 : Blo 147793 1605395 := bstep (se 1 (by rfl) ⟨1204046, by rfl⟩ : syracuseStep 1605395 = 2408093) B2408093
theorem B1802179 : Blo 147793 1802179 := bstep (se 1 (by rfl) ⟨1351634, by rfl⟩ : syracuseStep 1802179 = 2703269) B2703269
theorem B753947 : Blo 147793 753947 := bstep (se 1 (by rfl) ⟨565460, by rfl⟩ : syracuseStep 753947 = 1130921) B1130921
theorem B11766437 : Blo 147793 11766437 := bstep (se 4 (by rfl) ⟨1103103, by rfl⟩ : syracuseStep 11766437 = 2206207) B2206207
theorem B954011 : Blo 147793 954011 := bstep (se 1 (by rfl) ⟨715508, by rfl⟩ : syracuseStep 954011 = 1431017) B1431017
theorem B2037089 : Blo 147793 2037089 := bstep (se 2 (by rfl) ⟨763908, by rfl⟩ : syracuseStep 2037089 = 1527817) B1527817
theorem B52795475 : Blo 147793 52795475 := bstep (se 1 (by rfl) ⟨39596606, by rfl⟩ : syracuseStep 52795475 = 79193213) B79193213
theorem B12294767 : Blo 147793 12294767 := bstep (se 1 (by rfl) ⟨9221075, by rfl⟩ : syracuseStep 12294767 = 18442151) B18442151
theorem B826681 : Blo 147793 826681 := bstep (se 2 (by rfl) ⟨310005, by rfl⟩ : syracuseStep 826681 = 620011) B620011
theorem B3252311 : Blo 147793 3252311 := bstep (se 1 (by rfl) ⟨2439233, by rfl⟩ : syracuseStep 3252311 = 4878467) B4878467
theorem B1091231 : Blo 147793 1091231 := bstep (se 1 (by rfl) ⟨818423, by rfl⟩ : syracuseStep 1091231 = 1636847) B1636847
theorem B2402905 : Blo 147793 2402905 := bstep (se 2 (by rfl) ⟨901089, by rfl⟩ : syracuseStep 2402905 = 1802179) B1802179
theorem B633683 : Blo 147793 633683 := bstep (se 1 (by rfl) ⟨475262, by rfl⟩ : syracuseStep 633683 = 950525) B950525
theorem B339371 : Blo 147793 339371 := bstep (se 1 (by rfl) ⟨254528, by rfl⟩ : syracuseStep 339371 = 509057) B509057
theorem B865961 : Blo 147793 865961 := bstep (se 2 (by rfl) ⟨324735, by rfl⟩ : syracuseStep 865961 = 649471) B649471
theorem B375263 : Blo 147793 375263 := bstep (se 1 (by rfl) ⟨281447, by rfl⟩ : syracuseStep 375263 = 562895) B562895
theorem B7355063 : Blo 147793 7355063 := bstep (se 1 (by rfl) ⟨5516297, by rfl⟩ : syracuseStep 7355063 = 11032595) B11032595
theorem B409481 : Blo 147793 409481 := bstep (se 2 (by rfl) ⟨153555, by rfl⟩ : syracuseStep 409481 = 307111) B307111
theorem B151023 : Blo 147793 151023 := bstep (se 1 (by rfl) ⟨113267, by rfl⟩ : syracuseStep 151023 = 226535) B226535
theorem B151071 : Blo 147793 151071 := bstep (se 1 (by rfl) ⟨113303, by rfl⟩ : syracuseStep 151071 = 226607) B226607
theorem B250607 : Blo 147793 250607 := bstep (se 1 (by rfl) ⟨187955, by rfl⟩ : syracuseStep 250607 = 375911) B375911
theorem B5886857 : Blo 147793 5886857 := bstep (se 2 (by rfl) ⟨2207571, by rfl⟩ : syracuseStep 5886857 = 4415143) B4415143
theorem B1070263 : Blo 147793 1070263 := bstep (se 1 (by rfl) ⟨802697, by rfl⟩ : syracuseStep 1070263 = 1605395) B1605395
theorem B318995 : Blo 147793 318995 := bstep (se 1 (by rfl) ⟨239246, by rfl⟩ : syracuseStep 318995 = 478493) B478493
theorem B319457 : Blo 147793 319457 := bstep (se 2 (by rfl) ⟨119796, by rfl⟩ : syracuseStep 319457 = 239593) B239593
theorem B221951 : Blo 147793 221951 := bstep (se 1 (by rfl) ⟨166463, by rfl⟩ : syracuseStep 221951 = 332927) B332927
theorem B320935 : Blo 147793 320935 := bstep (se 1 (by rfl) ⟨240701, by rfl⟩ : syracuseStep 320935 = 481403) B481403
theorem B223451 : Blo 147793 223451 := bstep (se 1 (by rfl) ⟨167588, by rfl⟩ : syracuseStep 223451 = 335177) B335177
theorem B5925563 : Blo 147793 5925563 := bstep (se 1 (by rfl) ⟨4444172, by rfl⟩ : syracuseStep 5925563 = 8888345) B8888345
theorem B847007 : Blo 147793 847007 := bstep (se 1 (by rfl) ⟨635255, by rfl⟩ : syracuseStep 847007 = 1270511) B1270511
theorem B684139 : Blo 147793 684139 := bstep (se 1 (by rfl) ⟨513104, by rfl⟩ : syracuseStep 684139 = 1026209) B1026209
theorem B225449 : Blo 147793 225449 := bstep (se 2 (by rfl) ⟨84543, by rfl⟩ : syracuseStep 225449 = 169087) B169087
theorem B323903 : Blo 147793 323903 := bstep (se 1 (by rfl) ⟨242927, by rfl⟩ : syracuseStep 323903 = 485855) B485855
theorem B226031 : Blo 147793 226031 := bstep (se 1 (by rfl) ⟨169523, by rfl⟩ : syracuseStep 226031 = 339047) B339047
theorem B427913 : Blo 147793 427913 := bstep (se 2 (by rfl) ⟨160467, by rfl⟩ : syracuseStep 427913 = 320935) B320935
theorem B167071 : Blo 147793 167071 := bstep (se 1 (by rfl) ⟨125303, by rfl⟩ : syracuseStep 167071 = 250607) B250607
theorem B35196983 : Blo 147793 35196983 := bstep (se 1 (by rfl) ⟨26397737, by rfl⟩ : syracuseStep 35196983 = 52795475) B52795475
theorem B8196511 : Blo 147793 8196511 := bstep (se 1 (by rfl) ⟨6147383, by rfl⟩ : syracuseStep 8196511 = 12294767) B12294767
theorem B2168207 : Blo 147793 2168207 := bstep (se 1 (by rfl) ⟨1626155, by rfl⟩ : syracuseStep 2168207 = 3252311) B3252311
theorem B5708069 : Blo 147793 5708069 := bstep (se 4 (by rfl) ⟨535131, by rfl⟩ : syracuseStep 5708069 = 1070263) B1070263
theorem B727487 : Blo 147793 727487 := bstep (se 1 (by rfl) ⟨545615, by rfl⟩ : syracuseStep 727487 = 1091231) B1091231
theorem B564671 : Blo 147793 564671 := bstep (se 1 (by rfl) ⟨423503, by rfl⟩ : syracuseStep 564671 = 847007) B847007
theorem B272987 : Blo 147793 272987 := bstep (se 1 (by rfl) ⟨204740, by rfl⟩ : syracuseStep 272987 = 409481) B409481
theorem B502631 : Blo 147793 502631 := bstep (se 1 (by rfl) ⟨376973, by rfl⟩ : syracuseStep 502631 = 753947) B753947
theorem B7844291 : Blo 147793 7844291 := bstep (se 1 (by rfl) ⟨5883218, by rfl⟩ : syracuseStep 7844291 = 11766437) B11766437
theorem B636007 : Blo 147793 636007 := bstep (se 1 (by rfl) ⟨477005, by rfl⟩ : syracuseStep 636007 = 954011) B954011
theorem B1358059 : Blo 147793 1358059 := bstep (se 1 (by rfl) ⟨1018544, by rfl⟩ : syracuseStep 1358059 = 2037089) B2037089
theorem B212663 : Blo 147793 212663 := bstep (se 1 (by rfl) ⟨159497, by rfl⟩ : syracuseStep 212663 = 318995) B318995
theorem B212971 : Blo 147793 212971 := bstep (se 1 (by rfl) ⟨159728, by rfl⟩ : syracuseStep 212971 = 319457) B319457
theorem B147967 : Blo 147793 147967 := bstep (se 1 (by rfl) ⟨110975, by rfl⟩ : syracuseStep 147967 = 221951) B221951
theorem B148967 : Blo 147793 148967 := bstep (se 1 (by rfl) ⟨111725, by rfl⟩ : syracuseStep 148967 = 223451) B223451
theorem B3950375 : Blo 147793 3950375 := bstep (se 1 (by rfl) ⟨2962781, by rfl⟩ : syracuseStep 3950375 = 5925563) B5925563
theorem B1689821 : Blo 147793 1689821 := bstep (se 3 (by rfl) ⟨316841, by rfl⟩ : syracuseStep 1689821 = 633683) B633683
theorem B150299 : Blo 147793 150299 := bstep (se 1 (by rfl) ⟨112724, by rfl⟩ : syracuseStep 150299 = 225449) B225449
theorem B215935 : Blo 147793 215935 := bstep (se 1 (by rfl) ⟨161951, by rfl⟩ : syracuseStep 215935 = 323903) B323903
theorem B150687 : Blo 147793 150687 := bstep (se 1 (by rfl) ⟨113015, by rfl⟩ : syracuseStep 150687 = 226031) B226031
theorem B577307 : Blo 147793 577307 := bstep (se 1 (by rfl) ⟨432980, by rfl⟩ : syracuseStep 577307 = 865961) B865961
theorem B250175 : Blo 147793 250175 := bstep (se 1 (by rfl) ⟨187631, by rfl⟩ : syracuseStep 250175 = 375263) B375263
theorem B1102241 : Blo 147793 1102241 := bstep (se 2 (by rfl) ⟨413340, by rfl⟩ : syracuseStep 1102241 = 826681) B826681
theorem B4903375 : Blo 147793 4903375 := bstep (se 1 (by rfl) ⟨3677531, by rfl⟩ : syracuseStep 4903375 = 7355063) B7355063
theorem B3924571 : Blo 147793 3924571 := bstep (se 1 (by rfl) ⟨2943428, by rfl⟩ : syracuseStep 3924571 = 5886857) B5886857
theorem B3203873 : Blo 147793 3203873 := bstep (se 2 (by rfl) ⟨1201452, by rfl⟩ : syracuseStep 3203873 = 2402905) B2402905
theorem B912185 : Blo 147793 912185 := bstep (se 2 (by rfl) ⟨342069, by rfl⟩ : syracuseStep 912185 = 684139) B684139
theorem B226247 : Blo 147793 226247 := bstep (se 1 (by rfl) ⟨169685, by rfl⟩ : syracuseStep 226247 = 339371) B339371
theorem B23464655 : Blo 147793 23464655 := bstep (se 1 (by rfl) ⟨17598491, by rfl⟩ : syracuseStep 23464655 = 35196983) B35196983
theorem B166783 : Blo 147793 166783 := bstep (se 1 (by rfl) ⟨125087, by rfl⟩ : syracuseStep 166783 = 250175) B250175
theorem B1445471 : Blo 147793 1445471 := bstep (se 1 (by rfl) ⟨1084103, by rfl⟩ : syracuseStep 1445471 = 2168207) B2168207
theorem B3805379 : Blo 147793 3805379 := bstep (se 1 (by rfl) ⟨2854034, by rfl⟩ : syracuseStep 3805379 = 5708069) B5708069
theorem B1151653 : Blo 147793 1151653 := bstep (se 4 (by rfl) ⟨107967, by rfl⟩ : syracuseStep 1151653 = 215935) B215935
theorem B2135915 : Blo 147793 2135915 := bstep (se 1 (by rfl) ⟨1601936, by rfl⟩ : syracuseStep 2135915 = 3203873) B3203873
theorem B335087 : Blo 147793 335087 := bstep (se 1 (by rfl) ⟨251315, by rfl⟩ : syracuseStep 335087 = 502631) B502631
theorem B1810745 : Blo 147793 1810745 := bstep (se 2 (by rfl) ⟨679029, by rfl⟩ : syracuseStep 1810745 = 1358059) B1358059
theorem B567101 : Blo 147793 567101 := bstep (se 3 (by rfl) ⟨106331, by rfl⟩ : syracuseStep 567101 = 212663) B212663
theorem B1126547 : Blo 147793 1126547 := bstep (se 1 (by rfl) ⟨844910, by rfl⟩ : syracuseStep 1126547 = 1689821) B1689821
theorem B734827 : Blo 147793 734827 := bstep (se 1 (by rfl) ⟨551120, by rfl⟩ : syracuseStep 734827 = 1102241) B1102241
theorem B376447 : Blo 147793 376447 := bstep (se 1 (by rfl) ⟨282335, by rfl⟩ : syracuseStep 376447 = 564671) B564671
theorem B10928681 : Blo 147793 10928681 := bstep (se 2 (by rfl) ⟨4098255, by rfl⟩ : syracuseStep 10928681 = 8196511) B8196511
theorem B6537833 : Blo 147793 6537833 := bstep (se 2 (by rfl) ⟨2451687, by rfl⟩ : syracuseStep 6537833 = 4903375) B4903375
theorem B181991 : Blo 147793 181991 := bstep (se 1 (by rfl) ⟨136493, by rfl⟩ : syracuseStep 181991 = 272987) B272987
theorem B608123 : Blo 147793 608123 := bstep (se 1 (by rfl) ⟨456092, by rfl⟩ : syracuseStep 608123 = 912185) B912185
theorem B5229527 : Blo 147793 5229527 := bstep (se 1 (by rfl) ⟨3922145, by rfl⟩ : syracuseStep 5229527 = 7844291) B7844291
theorem B150831 : Blo 147793 150831 := bstep (se 1 (by rfl) ⟨113123, by rfl⟩ : syracuseStep 150831 = 226247) B226247
theorem B283961 : Blo 147793 283961 := bstep (se 2 (by rfl) ⟨106485, by rfl⟩ : syracuseStep 283961 = 212971) B212971
theorem B5232761 : Blo 147793 5232761 := bstep (se 2 (by rfl) ⟨1962285, by rfl⟩ : syracuseStep 5232761 = 3924571) B3924571
theorem B285275 : Blo 147793 285275 := bstep (se 1 (by rfl) ⟨213956, by rfl⟩ : syracuseStep 285275 = 427913) B427913
theorem B384871 : Blo 147793 384871 := bstep (se 1 (by rfl) ⟨288653, by rfl⟩ : syracuseStep 384871 = 577307) B577307
theorem B222761 : Blo 147793 222761 := bstep (se 2 (by rfl) ⟨83535, by rfl⟩ : syracuseStep 222761 = 167071) B167071
theorem B484991 : Blo 147793 484991 := bstep (se 1 (by rfl) ⟨363743, by rfl⟩ : syracuseStep 484991 = 727487) B727487
theorem B848009 : Blo 147793 848009 := bstep (se 2 (by rfl) ⟨318003, by rfl⟩ : syracuseStep 848009 = 636007) B636007
theorem B42137333 : Blo 147793 42137333 := bstep (se 5 (by rfl) ⟨1975187, by rfl⟩ : syracuseStep 42137333 = 3950375) B3950375
theorem B4358555 : Blo 147793 4358555 := bstep (se 1 (by rfl) ⟨3268916, by rfl⟩ : syracuseStep 4358555 = 6537833) B6537833
theorem B565339 : Blo 147793 565339 := bstep (se 1 (by rfl) ⟨424004, by rfl⟩ : syracuseStep 565339 = 848009) B848009
theorem B28091555 : Blo 147793 28091555 := bstep (se 1 (by rfl) ⟨21068666, by rfl⟩ : syracuseStep 28091555 = 42137333) B42137333
theorem B501929 : Blo 147793 501929 := bstep (se 2 (by rfl) ⟨188223, by rfl⟩ : syracuseStep 501929 = 376447) B376447
theorem B7285787 : Blo 147793 7285787 := bstep (se 1 (by rfl) ⟨5464340, by rfl⟩ : syracuseStep 7285787 = 10928681) B10928681
theorem B405415 : Blo 147793 405415 := bstep (se 1 (by rfl) ⟨304061, by rfl⟩ : syracuseStep 405415 = 608123) B608123
theorem B15643103 : Blo 147793 15643103 := bstep (se 1 (by rfl) ⟨11732327, by rfl⟩ : syracuseStep 15643103 = 23464655) B23464655
theorem B963647 : Blo 147793 963647 := bstep (se 1 (by rfl) ⟨722735, by rfl⟩ : syracuseStep 963647 = 1445471) B1445471
theorem B2536919 : Blo 147793 2536919 := bstep (se 1 (by rfl) ⟨1902689, by rfl⟩ : syracuseStep 2536919 = 3805379) B3805379
theorem B1423943 : Blo 147793 1423943 := bstep (se 1 (by rfl) ⟨1067957, by rfl⟩ : syracuseStep 1423943 = 2135915) B2135915
theorem B3488507 : Blo 147793 3488507 := bstep (se 1 (by rfl) ⟨2616380, by rfl⟩ : syracuseStep 3488507 = 5232761) B5232761
theorem B148507 : Blo 147793 148507 := bstep (se 1 (by rfl) ⟨111380, by rfl⟩ : syracuseStep 148507 = 222761) B222761
theorem B378067 : Blo 147793 378067 := bstep (se 1 (by rfl) ⟨283550, by rfl⟩ : syracuseStep 378067 = 567101) B567101
theorem B13945405 : Blo 147793 13945405 := bstep (se 3 (by rfl) ⟨2614763, by rfl⟩ : syracuseStep 13945405 = 5229527) B5229527
theorem B513161 : Blo 147793 513161 := bstep (se 2 (by rfl) ⟨192435, by rfl⟩ : syracuseStep 513161 = 384871) B384871
theorem B189307 : Blo 147793 189307 := bstep (se 1 (by rfl) ⟨141980, by rfl⟩ : syracuseStep 189307 = 283961) B283961
theorem B222377 : Blo 147793 222377 := bstep (se 2 (by rfl) ⟨83391, by rfl⟩ : syracuseStep 222377 = 166783) B166783
theorem B190183 : Blo 147793 190183 := bstep (se 1 (by rfl) ⟨142637, by rfl⟩ : syracuseStep 190183 = 285275) B285275
theorem B485309 : Blo 147793 485309 := bstep (se 3 (by rfl) ⟨90995, by rfl⟩ : syracuseStep 485309 = 181991) B181991
theorem B223391 : Blo 147793 223391 := bstep (se 1 (by rfl) ⟨167543, by rfl⟩ : syracuseStep 223391 = 335087) B335087
theorem B1207163 : Blo 147793 1207163 := bstep (se 1 (by rfl) ⟨905372, by rfl⟩ : syracuseStep 1207163 = 1810745) B1810745
theorem B1535537 : Blo 147793 1535537 := bstep (se 2 (by rfl) ⟨575826, by rfl⟩ : syracuseStep 1535537 = 1151653) B1151653
theorem B323327 : Blo 147793 323327 := bstep (se 1 (by rfl) ⟨242495, by rfl⟩ : syracuseStep 323327 = 484991) B484991
theorem B979769 : Blo 147793 979769 := bstep (se 2 (by rfl) ⟨367413, by rfl⟩ : syracuseStep 979769 = 734827) B734827
theorem B751031 : Blo 147793 751031 := bstep (se 1 (by rfl) ⟨563273, by rfl⟩ : syracuseStep 751031 = 1126547) B1126547
theorem B753785 : Blo 147793 753785 := bstep (se 2 (by rfl) ⟨282669, by rfl⟩ : syracuseStep 753785 = 565339) B565339
theorem B41714941 : Blo 147793 41714941 := bstep (se 3 (by rfl) ⟨7821551, by rfl⟩ : syracuseStep 41714941 = 15643103) B15643103
theorem B334619 : Blo 147793 334619 := bstep (se 1 (by rfl) ⟨250964, by rfl⟩ : syracuseStep 334619 = 501929) B501929
theorem B4857191 : Blo 147793 4857191 := bstep (se 1 (by rfl) ⟨3642893, by rfl⟩ : syracuseStep 4857191 = 7285787) B7285787
theorem B1023691 : Blo 147793 1023691 := bstep (se 1 (by rfl) ⟨767768, by rfl⟩ : syracuseStep 1023691 = 1535537) B1535537
theorem B500687 : Blo 147793 500687 := bstep (se 1 (by rfl) ⟨375515, by rfl⟩ : syracuseStep 500687 = 751031) B751031
theorem B504089 : Blo 147793 504089 := bstep (se 2 (by rfl) ⟨189033, by rfl⟩ : syracuseStep 504089 = 378067) B378067
theorem B18593873 : Blo 147793 18593873 := bstep (se 2 (by rfl) ⟨6972702, by rfl⟩ : syracuseStep 18593873 = 13945405) B13945405
theorem B342107 : Blo 147793 342107 := bstep (se 1 (by rfl) ⟨256580, by rfl⟩ : syracuseStep 342107 = 513161) B513161
theorem B1294157 : Blo 147793 1294157 := bstep (se 3 (by rfl) ⟨242654, by rfl⟩ : syracuseStep 1294157 = 485309) B485309
theorem B18727703 : Blo 147793 18727703 := bstep (se 1 (by rfl) ⟨14045777, by rfl⟩ : syracuseStep 18727703 = 28091555) B28091555
theorem B148251 : Blo 147793 148251 := bstep (se 1 (by rfl) ⟨111188, by rfl⟩ : syracuseStep 148251 = 222377) B222377
theorem B148927 : Blo 147793 148927 := bstep (se 1 (by rfl) ⟨111695, by rfl⟩ : syracuseStep 148927 = 223391) B223391
theorem B804775 : Blo 147793 804775 := bstep (se 1 (by rfl) ⟨603581, by rfl⟩ : syracuseStep 804775 = 1207163) B1207163
theorem B215551 : Blo 147793 215551 := bstep (se 1 (by rfl) ⟨161663, by rfl⟩ : syracuseStep 215551 = 323327) B323327
theorem B642431 : Blo 147793 642431 := bstep (se 1 (by rfl) ⟨481823, by rfl⟩ : syracuseStep 642431 = 963647) B963647
theorem B1691279 : Blo 147793 1691279 := bstep (se 1 (by rfl) ⟨1268459, by rfl⟩ : syracuseStep 1691279 = 2536919) B2536919
theorem B2905703 : Blo 147793 2905703 := bstep (se 1 (by rfl) ⟨2179277, by rfl⟩ : syracuseStep 2905703 = 4358555) B4358555
theorem B252409 : Blo 147793 252409 := bstep (se 2 (by rfl) ⟨94653, by rfl⟩ : syracuseStep 252409 = 189307) B189307
theorem B253577 : Blo 147793 253577 := bstep (se 2 (by rfl) ⟨95091, by rfl⟩ : syracuseStep 253577 = 190183) B190183
theorem B653179 : Blo 147793 653179 := bstep (se 1 (by rfl) ⟨489884, by rfl⟩ : syracuseStep 653179 = 979769) B979769
theorem B949295 : Blo 147793 949295 := bstep (se 1 (by rfl) ⟨711971, by rfl⟩ : syracuseStep 949295 = 1423943) B1423943
theorem B2325671 : Blo 147793 2325671 := bstep (se 1 (by rfl) ⟨1744253, by rfl⟩ : syracuseStep 2325671 = 3488507) B3488507
theorem B2162213 : Blo 147793 2162213 := bstep (se 4 (by rfl) ⟨202707, by rfl⟩ : syracuseStep 2162213 = 405415) B405415
theorem B12485135 : Blo 147793 12485135 := bstep (se 1 (by rfl) ⟨9363851, by rfl⟩ : syracuseStep 12485135 = 18727703) B18727703
theorem B1937135 : Blo 147793 1937135 := bstep (se 1 (by rfl) ⟨1452851, by rfl⟩ : syracuseStep 1937135 = 2905703) B2905703
theorem B169051 : Blo 147793 169051 := bstep (se 1 (by rfl) ⟨126788, by rfl⟩ : syracuseStep 169051 = 253577) B253577
theorem B333791 : Blo 147793 333791 := bstep (se 1 (by rfl) ⟨250343, by rfl⟩ : syracuseStep 333791 = 500687) B500687
theorem B336059 : Blo 147793 336059 := bstep (se 1 (by rfl) ⟨252044, by rfl⟩ : syracuseStep 336059 = 504089) B504089
theorem B336545 : Blo 147793 336545 := bstep (se 2 (by rfl) ⟨126204, by rfl⟩ : syracuseStep 336545 = 252409) B252409
theorem B1713149 : Blo 147793 1713149 := bstep (se 3 (by rfl) ⟨321215, by rfl⟩ : syracuseStep 1713149 = 642431) B642431
theorem B12395915 : Blo 147793 12395915 := bstep (se 1 (by rfl) ⟨9296936, by rfl⟩ : syracuseStep 12395915 = 18593873) B18593873
theorem B632863 : Blo 147793 632863 := bstep (se 1 (by rfl) ⟨474647, by rfl⟩ : syracuseStep 632863 = 949295) B949295
theorem B1550447 : Blo 147793 1550447 := bstep (se 1 (by rfl) ⟨1162835, by rfl⟩ : syracuseStep 1550447 = 2325671) B2325671
theorem B862771 : Blo 147793 862771 := bstep (se 1 (by rfl) ⟨647078, by rfl⟩ : syracuseStep 862771 = 1294157) B1294157
theorem B502523 : Blo 147793 502523 := bstep (se 1 (by rfl) ⟨376892, by rfl⟩ : syracuseStep 502523 = 753785) B753785
theorem B55619921 : Blo 147793 55619921 := bstep (se 2 (by rfl) ⟨20857470, by rfl⟩ : syracuseStep 55619921 = 41714941) B41714941
theorem B1127519 : Blo 147793 1127519 := bstep (se 1 (by rfl) ⟨845639, by rfl⟩ : syracuseStep 1127519 = 1691279) B1691279
theorem B870905 : Blo 147793 870905 := bstep (se 2 (by rfl) ⟨326589, by rfl⟩ : syracuseStep 870905 = 653179) B653179
theorem B1364921 : Blo 147793 1364921 := bstep (se 2 (by rfl) ⟨511845, by rfl⟩ : syracuseStep 1364921 = 1023691) B1023691
theorem B1073033 : Blo 147793 1073033 := bstep (se 2 (by rfl) ⟨402387, by rfl⟩ : syracuseStep 1073033 = 804775) B804775
theorem B287401 : Blo 147793 287401 := bstep (se 2 (by rfl) ⟨107775, by rfl⟩ : syracuseStep 287401 = 215551) B215551
theorem B223079 : Blo 147793 223079 := bstep (se 1 (by rfl) ⟨167309, by rfl⟩ : syracuseStep 223079 = 334619) B334619
theorem B3238127 : Blo 147793 3238127 := bstep (se 1 (by rfl) ⟨2428595, by rfl⟩ : syracuseStep 3238127 = 4857191) B4857191
theorem B228071 : Blo 147793 228071 := bstep (se 1 (by rfl) ⟨171053, by rfl⟩ : syracuseStep 228071 = 342107) B342107
theorem B1441475 : Blo 147793 1441475 := bstep (se 1 (by rfl) ⟨1081106, by rfl⟩ : syracuseStep 1441475 = 2162213) B2162213
theorem B33293693 : Blo 147793 33293693 := bstep (se 3 (by rfl) ⟨6242567, by rfl⟩ : syracuseStep 33293693 = 12485135) B12485135
theorem B1150361 : Blo 147793 1150361 := bstep (se 2 (by rfl) ⟨431385, by rfl⟩ : syracuseStep 1150361 = 862771) B862771
theorem B8263943 : Blo 147793 8263943 := bstep (se 1 (by rfl) ⟨6197957, by rfl⟩ : syracuseStep 8263943 = 12395915) B12395915
theorem B335015 : Blo 147793 335015 := bstep (se 1 (by rfl) ⟨251261, by rfl⟩ : syracuseStep 335015 = 502523) B502523
theorem B960983 : Blo 147793 960983 := bstep (se 1 (by rfl) ⟨720737, by rfl⟩ : syracuseStep 960983 = 1441475) B1441475
theorem B1291423 : Blo 147793 1291423 := bstep (se 1 (by rfl) ⟨968567, by rfl⟩ : syracuseStep 1291423 = 1937135) B1937135
theorem B148719 : Blo 147793 148719 := bstep (se 1 (by rfl) ⟨111539, by rfl⟩ : syracuseStep 148719 = 223079) B223079
theorem B1033631 : Blo 147793 1033631 := bstep (se 1 (by rfl) ⟨775223, by rfl⟩ : syracuseStep 1033631 = 1550447) B1550447
theorem B37079947 : Blo 147793 37079947 := bstep (se 1 (by rfl) ⟨27809960, by rfl⟩ : syracuseStep 37079947 = 55619921) B55619921
theorem B152047 : Blo 147793 152047 := bstep (se 1 (by rfl) ⟨114035, by rfl⟩ : syracuseStep 152047 = 228071) B228071
theorem B383201 : Blo 147793 383201 := bstep (se 2 (by rfl) ⟨143700, by rfl⟩ : syracuseStep 383201 = 287401) B287401
theorem B580603 : Blo 147793 580603 := bstep (se 1 (by rfl) ⟨435452, by rfl⟩ : syracuseStep 580603 = 870905) B870905
theorem B843817 : Blo 147793 843817 := bstep (se 2 (by rfl) ⟨316431, by rfl⟩ : syracuseStep 843817 = 632863) B632863
theorem B909947 : Blo 147793 909947 := bstep (se 1 (by rfl) ⟨682460, by rfl⟩ : syracuseStep 909947 = 1364921) B1364921
theorem B222527 : Blo 147793 222527 := bstep (se 1 (by rfl) ⟨166895, by rfl⟩ : syracuseStep 222527 = 333791) B333791
theorem B715355 : Blo 147793 715355 := bstep (se 1 (by rfl) ⟨536516, by rfl⟩ : syracuseStep 715355 = 1073033) B1073033
theorem B224039 : Blo 147793 224039 := bstep (se 1 (by rfl) ⟨168029, by rfl⟩ : syracuseStep 224039 = 336059) B336059
theorem B224363 : Blo 147793 224363 := bstep (se 1 (by rfl) ⟨168272, by rfl⟩ : syracuseStep 224363 = 336545) B336545
theorem B1142099 : Blo 147793 1142099 := bstep (se 1 (by rfl) ⟨856574, by rfl⟩ : syracuseStep 1142099 = 1713149) B1713149
theorem B225401 : Blo 147793 225401 := bstep (se 2 (by rfl) ⟨84525, by rfl⟩ : syracuseStep 225401 = 169051) B169051
theorem B2158751 : Blo 147793 2158751 := bstep (se 1 (by rfl) ⟨1619063, by rfl⟩ : syracuseStep 2158751 = 3238127) B3238127
theorem B751679 : Blo 147793 751679 := bstep (se 1 (by rfl) ⟨563759, by rfl⟩ : syracuseStep 751679 = 1127519) B1127519
theorem B689087 : Blo 147793 689087 := bstep (se 1 (by rfl) ⟨516815, by rfl⟩ : syracuseStep 689087 = 1033631) B1033631
theorem B5509295 : Blo 147793 5509295 := bstep (se 1 (by rfl) ⟨4131971, by rfl⟩ : syracuseStep 5509295 = 8263943) B8263943
theorem B197759717 : Blo 147793 197759717 := bstep (se 4 (by rfl) ⟨18539973, by rfl⟩ : syracuseStep 197759717 = 37079947) B37079947
theorem B761399 : Blo 147793 761399 := bstep (se 1 (by rfl) ⟨571049, by rfl⟩ : syracuseStep 761399 = 1142099) B1142099
theorem B501119 : Blo 147793 501119 := bstep (se 1 (by rfl) ⟨375839, by rfl⟩ : syracuseStep 501119 = 751679) B751679
theorem B1125089 : Blo 147793 1125089 := bstep (se 2 (by rfl) ⟨421908, by rfl⟩ : syracuseStep 1125089 = 843817) B843817
theorem B22195795 : Blo 147793 22195795 := bstep (se 1 (by rfl) ⟨16646846, by rfl⟩ : syracuseStep 22195795 = 33293693) B33293693
theorem B766907 : Blo 147793 766907 := bstep (se 1 (by rfl) ⟨575180, by rfl⟩ : syracuseStep 766907 = 1150361) B1150361
theorem B606631 : Blo 147793 606631 := bstep (se 1 (by rfl) ⟨454973, by rfl⟩ : syracuseStep 606631 = 909947) B909947
theorem B148351 : Blo 147793 148351 := bstep (se 1 (by rfl) ⟨111263, by rfl⟩ : syracuseStep 148351 = 222527) B222527
theorem B1721897 : Blo 147793 1721897 := bstep (se 2 (by rfl) ⟨645711, by rfl⟩ : syracuseStep 1721897 = 1291423) B1291423
theorem B640655 : Blo 147793 640655 := bstep (se 1 (by rfl) ⟨480491, by rfl⟩ : syracuseStep 640655 = 960983) B960983
theorem B476903 : Blo 147793 476903 := bstep (se 1 (by rfl) ⟨357677, by rfl⟩ : syracuseStep 476903 = 715355) B715355
theorem B149359 : Blo 147793 149359 := bstep (se 1 (by rfl) ⟨112019, by rfl⟩ : syracuseStep 149359 = 224039) B224039
theorem B149575 : Blo 147793 149575 := bstep (se 1 (by rfl) ⟨112181, by rfl⟩ : syracuseStep 149575 = 224363) B224363
theorem B150267 : Blo 147793 150267 := bstep (se 1 (by rfl) ⟨112700, by rfl⟩ : syracuseStep 150267 = 225401) B225401
theorem B774137 : Blo 147793 774137 := bstep (se 2 (by rfl) ⟨290301, by rfl⟩ : syracuseStep 774137 = 580603) B580603
theorem B810917 : Blo 147793 810917 := bstep (se 4 (by rfl) ⟨76023, by rfl⟩ : syracuseStep 810917 = 152047) B152047
theorem B255467 : Blo 147793 255467 := bstep (se 1 (by rfl) ⟨191600, by rfl⟩ : syracuseStep 255467 = 383201) B383201
theorem B223343 : Blo 147793 223343 := bstep (se 1 (by rfl) ⟨167507, by rfl⟩ : syracuseStep 223343 = 335015) B335015
theorem B1439167 : Blo 147793 1439167 := bstep (se 1 (by rfl) ⟨1079375, by rfl⟩ : syracuseStep 1439167 = 2158751) B2158751
theorem B459391 : Blo 147793 459391 := bstep (se 1 (by rfl) ⟨344543, by rfl⟩ : syracuseStep 459391 = 689087) B689087
theorem B1147931 : Blo 147793 1147931 := bstep (se 1 (by rfl) ⟨860948, by rfl⟩ : syracuseStep 1147931 = 1721897) B1721897
theorem B427103 : Blo 147793 427103 := bstep (se 1 (by rfl) ⟨320327, by rfl⟩ : syracuseStep 427103 = 640655) B640655
theorem B3672863 : Blo 147793 3672863 := bstep (se 1 (by rfl) ⟨2754647, by rfl⟩ : syracuseStep 3672863 = 5509295) B5509295
theorem B29594393 : Blo 147793 29594393 := bstep (se 2 (by rfl) ⟨11097897, by rfl⟩ : syracuseStep 29594393 = 22195795) B22195795
theorem B334079 : Blo 147793 334079 := bstep (se 1 (by rfl) ⟨250559, by rfl⟩ : syracuseStep 334079 = 501119) B501119
theorem B170311 : Blo 147793 170311 := bstep (se 1 (by rfl) ⟨127733, by rfl⟩ : syracuseStep 170311 = 255467) B255467
theorem B131839811 : Blo 147793 131839811 := bstep (se 1 (by rfl) ⟨98879858, by rfl⟩ : syracuseStep 131839811 = 197759717) B197759717
theorem B507599 : Blo 147793 507599 := bstep (se 1 (by rfl) ⟨380699, by rfl⟩ : syracuseStep 507599 = 761399) B761399
theorem B540611 : Blo 147793 540611 := bstep (se 1 (by rfl) ⟨405458, by rfl⟩ : syracuseStep 540611 = 810917) B810917
theorem B148895 : Blo 147793 148895 := bstep (se 1 (by rfl) ⟨111671, by rfl⟩ : syracuseStep 148895 = 223343) B223343
theorem B1918889 : Blo 147793 1918889 := bstep (se 2 (by rfl) ⟨719583, by rfl⟩ : syracuseStep 1918889 = 1439167) B1439167
theorem B511271 : Blo 147793 511271 := bstep (se 1 (by rfl) ⟨383453, by rfl⟩ : syracuseStep 511271 = 766907) B766907
theorem B808841 : Blo 147793 808841 := bstep (se 2 (by rfl) ⟨303315, by rfl⟩ : syracuseStep 808841 = 606631) B606631
theorem B317935 : Blo 147793 317935 := bstep (se 1 (by rfl) ⟨238451, by rfl⟩ : syracuseStep 317935 = 476903) B476903
theorem B516091 : Blo 147793 516091 := bstep (se 1 (by rfl) ⟨387068, by rfl⟩ : syracuseStep 516091 = 774137) B774137
theorem B750059 : Blo 147793 750059 := bstep (se 1 (by rfl) ⟨562544, by rfl⟩ : syracuseStep 750059 = 1125089) B1125089
theorem B1279259 : Blo 147793 1279259 := bstep (se 1 (by rfl) ⟨959444, by rfl⟩ : syracuseStep 1279259 = 1918889) B1918889
theorem B19729595 : Blo 147793 19729595 := bstep (se 1 (by rfl) ⟨14797196, by rfl⟩ : syracuseStep 19729595 = 29594393) B29594393
theorem B500039 : Blo 147793 500039 := bstep (se 1 (by rfl) ⟨375029, by rfl⟩ : syracuseStep 500039 = 750059) B750059
theorem B87893207 : Blo 147793 87893207 := bstep (se 1 (by rfl) ⟨65919905, by rfl⟩ : syracuseStep 87893207 = 131839811) B131839811
theorem B338399 : Blo 147793 338399 := bstep (se 1 (by rfl) ⟨253799, by rfl⟩ : syracuseStep 338399 = 507599) B507599
theorem B765287 : Blo 147793 765287 := bstep (se 1 (by rfl) ⟨573965, by rfl⟩ : syracuseStep 765287 = 1147931) B1147931
theorem B340847 : Blo 147793 340847 := bstep (se 1 (by rfl) ⟨255635, by rfl⟩ : syracuseStep 340847 = 511271) B511271
theorem B539227 : Blo 147793 539227 := bstep (se 1 (by rfl) ⟨404420, by rfl⟩ : syracuseStep 539227 = 808841) B808841
theorem B284735 : Blo 147793 284735 := bstep (se 1 (by rfl) ⟨213551, by rfl⟩ : syracuseStep 284735 = 427103) B427103
theorem B612521 : Blo 147793 612521 := bstep (se 2 (by rfl) ⟨229695, by rfl⟩ : syracuseStep 612521 = 459391) B459391
theorem B2448575 : Blo 147793 2448575 := bstep (se 1 (by rfl) ⟨1836431, by rfl⟩ : syracuseStep 2448575 = 3672863) B3672863
theorem B1695653 : Blo 147793 1695653 := bstep (se 4 (by rfl) ⟨158967, by rfl⟩ : syracuseStep 1695653 = 317935) B317935
theorem B222719 : Blo 147793 222719 := bstep (se 1 (by rfl) ⟨167039, by rfl⟩ : syracuseStep 222719 = 334079) B334079
theorem B227081 : Blo 147793 227081 := bstep (se 2 (by rfl) ⟨85155, by rfl⟩ : syracuseStep 227081 = 170311) B170311
theorem B360407 : Blo 147793 360407 := bstep (se 1 (by rfl) ⟨270305, by rfl⟩ : syracuseStep 360407 = 540611) B540611
theorem B688121 : Blo 147793 688121 := bstep (se 2 (by rfl) ⟨258045, by rfl⟩ : syracuseStep 688121 = 516091) B516091
theorem B852839 : Blo 147793 852839 := bstep (se 1 (by rfl) ⟨639629, by rfl⟩ : syracuseStep 852839 = 1279259) B1279259
theorem B759293 : Blo 147793 759293 := bstep (se 3 (by rfl) ⟨142367, by rfl⟩ : syracuseStep 759293 = 284735) B284735
theorem B333359 : Blo 147793 333359 := bstep (se 1 (by rfl) ⟨250019, by rfl⟩ : syracuseStep 333359 = 500039) B500039
theorem B58595471 : Blo 147793 58595471 := bstep (se 1 (by rfl) ⟨43946603, by rfl⟩ : syracuseStep 58595471 = 87893207) B87893207
theorem B961085 : Blo 147793 961085 := bstep (se 3 (by rfl) ⟨180203, by rfl⟩ : syracuseStep 961085 = 360407) B360407
theorem B13153063 : Blo 147793 13153063 := bstep (se 1 (by rfl) ⟨9864797, by rfl⟩ : syracuseStep 13153063 = 19729595) B19729595
theorem B408347 : Blo 147793 408347 := bstep (se 1 (by rfl) ⟨306260, by rfl⟩ : syracuseStep 408347 = 612521) B612521
theorem B1130435 : Blo 147793 1130435 := bstep (se 1 (by rfl) ⟨847826, by rfl⟩ : syracuseStep 1130435 = 1695653) B1695653
theorem B148479 : Blo 147793 148479 := bstep (se 1 (by rfl) ⟨111359, by rfl⟩ : syracuseStep 148479 = 222719) B222719
theorem B510191 : Blo 147793 510191 := bstep (se 1 (by rfl) ⟨382643, by rfl⟩ : syracuseStep 510191 = 765287) B765287
theorem B151387 : Blo 147793 151387 := bstep (se 1 (by rfl) ⟨113540, by rfl⟩ : syracuseStep 151387 = 227081) B227081
theorem B1632383 : Blo 147793 1632383 := bstep (se 1 (by rfl) ⟨1224287, by rfl⟩ : syracuseStep 1632383 = 2448575) B2448575
theorem B225599 : Blo 147793 225599 := bstep (se 1 (by rfl) ⟨169199, by rfl⟩ : syracuseStep 225599 = 338399) B338399
theorem B227231 : Blo 147793 227231 := bstep (se 1 (by rfl) ⟨170423, by rfl⟩ : syracuseStep 227231 = 340847) B340847
theorem B718969 : Blo 147793 718969 := bstep (se 2 (by rfl) ⟨269613, by rfl⟩ : syracuseStep 718969 = 539227) B539227
theorem B458747 : Blo 147793 458747 := bstep (se 1 (by rfl) ⟨344060, by rfl⟩ : syracuseStep 458747 = 688121) B688121
theorem B39063647 : Blo 147793 39063647 := bstep (se 1 (by rfl) ⟨29297735, by rfl⟩ : syracuseStep 39063647 = 58595471) B58595471
theorem B17537417 : Blo 147793 17537417 := bstep (se 2 (by rfl) ⟨6576531, by rfl⟩ : syracuseStep 17537417 = 13153063) B13153063
theorem B1088255 : Blo 147793 1088255 := bstep (se 1 (by rfl) ⟨816191, by rfl⟩ : syracuseStep 1088255 = 1632383) B1632383
theorem B958625 : Blo 147793 958625 := bstep (se 2 (by rfl) ⟨359484, by rfl⟩ : syracuseStep 958625 = 718969) B718969
theorem B272231 : Blo 147793 272231 := bstep (se 1 (by rfl) ⟨204173, by rfl⟩ : syracuseStep 272231 = 408347) B408347
theorem B305831 : Blo 147793 305831 := bstep (se 1 (by rfl) ⟨229373, by rfl⟩ : syracuseStep 305831 = 458747) B458747
theorem B568559 : Blo 147793 568559 := bstep (se 1 (by rfl) ⟨426419, by rfl⟩ : syracuseStep 568559 = 852839) B852839
theorem B340127 : Blo 147793 340127 := bstep (se 1 (by rfl) ⟨255095, by rfl⟩ : syracuseStep 340127 = 510191) B510191
theorem B506195 : Blo 147793 506195 := bstep (se 1 (by rfl) ⟨379646, by rfl⟩ : syracuseStep 506195 = 759293) B759293
theorem B640723 : Blo 147793 640723 := bstep (se 1 (by rfl) ⟨480542, by rfl⟩ : syracuseStep 640723 = 961085) B961085
theorem B150399 : Blo 147793 150399 := bstep (se 1 (by rfl) ⟨112799, by rfl⟩ : syracuseStep 150399 = 225599) B225599
theorem B151487 : Blo 147793 151487 := bstep (se 1 (by rfl) ⟨113615, by rfl⟩ : syracuseStep 151487 = 227231) B227231
theorem B222239 : Blo 147793 222239 := bstep (se 1 (by rfl) ⟨166679, by rfl⟩ : syracuseStep 222239 = 333359) B333359
theorem B753623 : Blo 147793 753623 := bstep (se 1 (by rfl) ⟨565217, by rfl⟩ : syracuseStep 753623 = 1130435) B1130435
theorem B854297 : Blo 147793 854297 := bstep (se 2 (by rfl) ⟨320361, by rfl⟩ : syracuseStep 854297 = 640723) B640723
theorem B203887 : Blo 147793 203887 := bstep (se 1 (by rfl) ⟨152915, by rfl⟩ : syracuseStep 203887 = 305831) B305831
theorem B337463 : Blo 147793 337463 := bstep (se 1 (by rfl) ⟨253097, by rfl⟩ : syracuseStep 337463 = 506195) B506195
theorem B502415 : Blo 147793 502415 := bstep (se 1 (by rfl) ⟨376811, by rfl⟩ : syracuseStep 502415 = 753623) B753623
theorem B639083 : Blo 147793 639083 := bstep (se 1 (by rfl) ⟨479312, by rfl⟩ : syracuseStep 639083 = 958625) B958625
theorem B148159 : Blo 147793 148159 := bstep (se 1 (by rfl) ⟨111119, by rfl⟩ : syracuseStep 148159 = 222239) B222239
theorem B181487 : Blo 147793 181487 := bstep (se 1 (by rfl) ⟨136115, by rfl⟩ : syracuseStep 181487 = 272231) B272231
theorem B2902013 : Blo 147793 2902013 := bstep (se 3 (by rfl) ⟨544127, by rfl⟩ : syracuseStep 2902013 = 1088255) B1088255
theorem B379039 : Blo 147793 379039 := bstep (se 1 (by rfl) ⟨284279, by rfl⟩ : syracuseStep 379039 = 568559) B568559
theorem B26042431 : Blo 147793 26042431 := bstep (se 1 (by rfl) ⟨19531823, by rfl⟩ : syracuseStep 26042431 = 39063647) B39063647
theorem B11691611 : Blo 147793 11691611 := bstep (se 1 (by rfl) ⟨8768708, by rfl⟩ : syracuseStep 11691611 = 17537417) B17537417
theorem B226751 : Blo 147793 226751 := bstep (se 1 (by rfl) ⟨170063, by rfl⟩ : syracuseStep 226751 = 340127) B340127
theorem B426055 : Blo 147793 426055 := bstep (se 1 (by rfl) ⟨319541, by rfl⟩ : syracuseStep 426055 = 639083) B639083
theorem B1934675 : Blo 147793 1934675 := bstep (se 1 (by rfl) ⟨1451006, by rfl⟩ : syracuseStep 1934675 = 2902013) B2902013
theorem B334943 : Blo 147793 334943 := bstep (se 1 (by rfl) ⟨251207, by rfl⟩ : syracuseStep 334943 = 502415) B502415
theorem B271849 : Blo 147793 271849 := bstep (se 2 (by rfl) ⟨101943, by rfl⟩ : syracuseStep 271849 = 203887) B203887
theorem B569531 : Blo 147793 569531 := bstep (se 1 (by rfl) ⟨427148, by rfl⟩ : syracuseStep 569531 = 854297) B854297
theorem B505385 : Blo 147793 505385 := bstep (se 2 (by rfl) ⟨189519, by rfl⟩ : syracuseStep 505385 = 379039) B379039
theorem B151167 : Blo 147793 151167 := bstep (se 1 (by rfl) ⟨113375, by rfl⟩ : syracuseStep 151167 = 226751) B226751
theorem B34723241 : Blo 147793 34723241 := bstep (se 2 (by rfl) ⟨13021215, by rfl⟩ : syracuseStep 34723241 = 26042431) B26042431
theorem B483965 : Blo 147793 483965 := bstep (se 3 (by rfl) ⟨90743, by rfl⟩ : syracuseStep 483965 = 181487) B181487
theorem B224975 : Blo 147793 224975 := bstep (se 1 (by rfl) ⟨168731, by rfl⟩ : syracuseStep 224975 = 337463) B337463
theorem B7794407 : Blo 147793 7794407 := bstep (se 1 (by rfl) ⟨5845805, by rfl⟩ : syracuseStep 7794407 = 11691611) B11691611
theorem B362465 : Blo 147793 362465 := bstep (se 2 (by rfl) ⟨135924, by rfl⟩ : syracuseStep 362465 = 271849) B271849
theorem B336923 : Blo 147793 336923 := bstep (se 1 (by rfl) ⟨252692, by rfl⟩ : syracuseStep 336923 = 505385) B505385
theorem B568073 : Blo 147793 568073 := bstep (se 2 (by rfl) ⟨213027, by rfl⟩ : syracuseStep 568073 = 426055) B426055
theorem B1289783 : Blo 147793 1289783 := bstep (se 1 (by rfl) ⟨967337, by rfl⟩ : syracuseStep 1289783 = 1934675) B1934675
theorem B23148827 : Blo 147793 23148827 := bstep (se 1 (by rfl) ⟨17361620, by rfl⟩ : syracuseStep 23148827 = 34723241) B34723241
theorem B149983 : Blo 147793 149983 := bstep (se 1 (by rfl) ⟨112487, by rfl⟩ : syracuseStep 149983 = 224975) B224975
theorem B5196271 : Blo 147793 5196271 := bstep (se 1 (by rfl) ⟨3897203, by rfl⟩ : syracuseStep 5196271 = 7794407) B7794407
theorem B379687 : Blo 147793 379687 := bstep (se 1 (by rfl) ⟨284765, by rfl⟩ : syracuseStep 379687 = 569531) B569531
theorem B223295 : Blo 147793 223295 := bstep (se 1 (by rfl) ⟨167471, by rfl⟩ : syracuseStep 223295 = 334943) B334943
theorem B322643 : Blo 147793 322643 := bstep (se 1 (by rfl) ⟨241982, by rfl⟩ : syracuseStep 322643 = 483965) B483965
theorem B859855 : Blo 147793 859855 := bstep (se 1 (by rfl) ⟨644891, by rfl⟩ : syracuseStep 859855 = 1289783) B1289783
theorem B860381 : Blo 147793 860381 := bstep (se 3 (by rfl) ⟨161321, by rfl⟩ : syracuseStep 860381 = 322643) B322643
theorem B241643 : Blo 147793 241643 := bstep (se 1 (by rfl) ⟨181232, by rfl⟩ : syracuseStep 241643 = 362465) B362465
theorem B6928361 : Blo 147793 6928361 := bstep (se 2 (by rfl) ⟨2598135, by rfl⟩ : syracuseStep 6928361 = 5196271) B5196271
theorem B506249 : Blo 147793 506249 := bstep (se 2 (by rfl) ⟨189843, by rfl⟩ : syracuseStep 506249 = 379687) B379687
theorem B148863 : Blo 147793 148863 := bstep (se 1 (by rfl) ⟨111647, by rfl⟩ : syracuseStep 148863 = 223295) B223295
theorem B378715 : Blo 147793 378715 := bstep (se 1 (by rfl) ⟨284036, by rfl⟩ : syracuseStep 378715 = 568073) B568073
theorem B224615 : Blo 147793 224615 := bstep (se 1 (by rfl) ⟨168461, by rfl⟩ : syracuseStep 224615 = 336923) B336923
theorem B15432551 : Blo 147793 15432551 := bstep (se 1 (by rfl) ⟨11574413, by rfl⟩ : syracuseStep 15432551 = 23148827) B23148827
theorem B337499 : Blo 147793 337499 := bstep (se 1 (by rfl) ⟨253124, by rfl⟩ : syracuseStep 337499 = 506249) B506249
theorem B504953 : Blo 147793 504953 := bstep (se 2 (by rfl) ⟨189357, by rfl⟩ : syracuseStep 504953 = 378715) B378715
theorem B573587 : Blo 147793 573587 := bstep (se 1 (by rfl) ⟨430190, by rfl⟩ : syracuseStep 573587 = 860381) B860381
theorem B149743 : Blo 147793 149743 := bstep (se 1 (by rfl) ⟨112307, by rfl⟩ : syracuseStep 149743 = 224615) B224615
theorem B644381 : Blo 147793 644381 := bstep (se 3 (by rfl) ⟨120821, by rfl⟩ : syracuseStep 644381 = 241643) B241643
theorem B4618907 : Blo 147793 4618907 := bstep (se 1 (by rfl) ⟨3464180, by rfl⟩ : syracuseStep 4618907 = 6928361) B6928361
theorem B10288367 : Blo 147793 10288367 := bstep (se 1 (by rfl) ⟨7716275, by rfl⟩ : syracuseStep 10288367 = 15432551) B15432551
theorem B1146473 : Blo 147793 1146473 := bstep (se 2 (by rfl) ⟨429927, by rfl⟩ : syracuseStep 1146473 = 859855) B859855
theorem B429587 : Blo 147793 429587 := bstep (se 1 (by rfl) ⟨322190, by rfl⟩ : syracuseStep 429587 = 644381) B644381
theorem B336635 : Blo 147793 336635 := bstep (se 1 (by rfl) ⟨252476, by rfl⟩ : syracuseStep 336635 = 504953) B504953
theorem B6858911 : Blo 147793 6858911 := bstep (se 1 (by rfl) ⟨5144183, by rfl⟩ : syracuseStep 6858911 = 10288367) B10288367
theorem B764315 : Blo 147793 764315 := bstep (se 1 (by rfl) ⟨573236, by rfl⟩ : syracuseStep 764315 = 1146473) B1146473
theorem B382391 : Blo 147793 382391 := bstep (se 1 (by rfl) ⟨286793, by rfl⟩ : syracuseStep 382391 = 573587) B573587
theorem B224999 : Blo 147793 224999 := bstep (se 1 (by rfl) ⟨168749, by rfl⟩ : syracuseStep 224999 = 337499) B337499
theorem B3079271 : Blo 147793 3079271 := bstep (se 1 (by rfl) ⟨2309453, by rfl⟩ : syracuseStep 3079271 = 4618907) B4618907
theorem B4572607 : Blo 147793 4572607 := bstep (se 1 (by rfl) ⟨3429455, by rfl⟩ : syracuseStep 4572607 = 6858911) B6858911
theorem B509543 : Blo 147793 509543 := bstep (se 1 (by rfl) ⟨382157, by rfl⟩ : syracuseStep 509543 = 764315) B764315
theorem B149999 : Blo 147793 149999 := bstep (se 1 (by rfl) ⟨112499, by rfl⟩ : syracuseStep 149999 = 224999) B224999
theorem B2052847 : Blo 147793 2052847 := bstep (se 1 (by rfl) ⟨1539635, by rfl⟩ : syracuseStep 2052847 = 3079271) B3079271
theorem B286391 : Blo 147793 286391 := bstep (se 1 (by rfl) ⟨214793, by rfl⟩ : syracuseStep 286391 = 429587) B429587
theorem B254927 : Blo 147793 254927 := bstep (se 1 (by rfl) ⟨191195, by rfl⟩ : syracuseStep 254927 = 382391) B382391
theorem B224423 : Blo 147793 224423 := bstep (se 1 (by rfl) ⟨168317, by rfl⟩ : syracuseStep 224423 = 336635) B336635
theorem B6096809 : Blo 147793 6096809 := bstep (se 2 (by rfl) ⟨2286303, by rfl⟩ : syracuseStep 6096809 = 4572607) B4572607
theorem B10948517 : Blo 147793 10948517 := bstep (se 4 (by rfl) ⟨1026423, by rfl⟩ : syracuseStep 10948517 = 2052847) B2052847
theorem B169951 : Blo 147793 169951 := bstep (se 1 (by rfl) ⟨127463, by rfl⟩ : syracuseStep 169951 = 254927) B254927
theorem B339695 : Blo 147793 339695 := bstep (se 1 (by rfl) ⟨254771, by rfl⟩ : syracuseStep 339695 = 509543) B509543
theorem B149615 : Blo 147793 149615 := bstep (se 1 (by rfl) ⟨112211, by rfl⟩ : syracuseStep 149615 = 224423) B224423
theorem B190927 : Blo 147793 190927 := bstep (se 1 (by rfl) ⟨143195, by rfl⟩ : syracuseStep 190927 = 286391) B286391
theorem B16258157 : Blo 147793 16258157 := bstep (se 3 (by rfl) ⟨3048404, by rfl⟩ : syracuseStep 16258157 = 6096809) B6096809
theorem B7299011 : Blo 147793 7299011 := bstep (se 1 (by rfl) ⟨5474258, by rfl⟩ : syracuseStep 7299011 = 10948517) B10948517
theorem B254569 : Blo 147793 254569 := bstep (se 2 (by rfl) ⟨95463, by rfl⟩ : syracuseStep 254569 = 190927) B190927
theorem B226463 : Blo 147793 226463 := bstep (se 1 (by rfl) ⟨169847, by rfl⟩ : syracuseStep 226463 = 339695) B339695
theorem B226601 : Blo 147793 226601 := bstep (se 2 (by rfl) ⟨84975, by rfl⟩ : syracuseStep 226601 = 169951) B169951
theorem B339425 : Blo 147793 339425 := bstep (se 2 (by rfl) ⟨127284, by rfl⟩ : syracuseStep 339425 = 254569) B254569
theorem B4866007 : Blo 147793 4866007 := bstep (se 1 (by rfl) ⟨3649505, by rfl⟩ : syracuseStep 4866007 = 7299011) B7299011
theorem B150975 : Blo 147793 150975 := bstep (se 1 (by rfl) ⟨113231, by rfl⟩ : syracuseStep 150975 = 226463) B226463
theorem B151067 : Blo 147793 151067 := bstep (se 1 (by rfl) ⟨113300, by rfl⟩ : syracuseStep 151067 = 226601) B226601
theorem B10838771 : Blo 147793 10838771 := bstep (se 1 (by rfl) ⟨8129078, by rfl⟩ : syracuseStep 10838771 = 16258157) B16258157
theorem B7225847 : Blo 147793 7225847 := bstep (se 1 (by rfl) ⟨5419385, by rfl⟩ : syracuseStep 7225847 = 10838771) B10838771
theorem B226283 : Blo 147793 226283 := bstep (se 1 (by rfl) ⟨169712, by rfl⟩ : syracuseStep 226283 = 339425) B339425
theorem B6488009 : Blo 147793 6488009 := bstep (se 2 (by rfl) ⟨2433003, by rfl⟩ : syracuseStep 6488009 = 4866007) B4866007
theorem B4817231 : Blo 147793 4817231 := bstep (se 1 (by rfl) ⟨3612923, by rfl⟩ : syracuseStep 4817231 = 7225847) B7225847
theorem B150855 : Blo 147793 150855 := bstep (se 1 (by rfl) ⟨113141, by rfl⟩ : syracuseStep 150855 = 226283) B226283
theorem B4325339 : Blo 147793 4325339 := bstep (se 1 (by rfl) ⟨3244004, by rfl⟩ : syracuseStep 4325339 = 6488009) B6488009
theorem B3211487 : Blo 147793 3211487 := bstep (se 1 (by rfl) ⟨2408615, by rfl⟩ : syracuseStep 3211487 = 4817231) B4817231
theorem B2883559 : Blo 147793 2883559 := bstep (se 1 (by rfl) ⟨2162669, by rfl⟩ : syracuseStep 2883559 = 4325339) B4325339
theorem B3844745 : Blo 147793 3844745 := bstep (se 2 (by rfl) ⟨1441779, by rfl⟩ : syracuseStep 3844745 = 2883559) B2883559
theorem B2140991 : Blo 147793 2140991 := bstep (se 1 (by rfl) ⟨1605743, by rfl⟩ : syracuseStep 2140991 = 3211487) B3211487
theorem B2563163 : Blo 147793 2563163 := bstep (se 1 (by rfl) ⟨1922372, by rfl⟩ : syracuseStep 2563163 = 3844745) B3844745
theorem B1427327 : Blo 147793 1427327 := bstep (se 1 (by rfl) ⟨1070495, by rfl⟩ : syracuseStep 1427327 = 2140991) B2140991
theorem B951551 : Blo 147793 951551 := bstep (se 1 (by rfl) ⟨713663, by rfl⟩ : syracuseStep 951551 = 1427327) B1427327
theorem B1708775 : Blo 147793 1708775 := bstep (se 1 (by rfl) ⟨1281581, by rfl⟩ : syracuseStep 1708775 = 2563163) B2563163
theorem B634367 : Blo 147793 634367 := bstep (se 1 (by rfl) ⟨475775, by rfl⟩ : syracuseStep 634367 = 951551) B951551
theorem B1139183 : Blo 147793 1139183 := bstep (se 1 (by rfl) ⟨854387, by rfl⟩ : syracuseStep 1139183 = 1708775) B1708775
theorem B759455 : Blo 147793 759455 := bstep (se 1 (by rfl) ⟨569591, by rfl⟩ : syracuseStep 759455 = 1139183) B1139183
theorem B422911 : Blo 147793 422911 := bstep (se 1 (by rfl) ⟨317183, by rfl⟩ : syracuseStep 422911 = 634367) B634367
theorem B563881 : Blo 147793 563881 := bstep (se 2 (by rfl) ⟨211455, by rfl⟩ : syracuseStep 563881 = 422911) B422911
theorem B506303 : Blo 147793 506303 := bstep (se 1 (by rfl) ⟨379727, by rfl⟩ : syracuseStep 506303 = 759455) B759455
theorem B337535 : Blo 147793 337535 := bstep (se 1 (by rfl) ⟨253151, by rfl⟩ : syracuseStep 337535 = 506303) B506303
theorem B751841 : Blo 147793 751841 := bstep (se 2 (by rfl) ⟨281940, by rfl⟩ : syracuseStep 751841 = 563881) B563881
theorem B501227 : Blo 147793 501227 := bstep (se 1 (by rfl) ⟨375920, by rfl⟩ : syracuseStep 501227 = 751841) B751841
theorem B225023 : Blo 147793 225023 := bstep (se 1 (by rfl) ⟨168767, by rfl⟩ : syracuseStep 225023 = 337535) B337535
theorem B334151 : Blo 147793 334151 := bstep (se 1 (by rfl) ⟨250613, by rfl⟩ : syracuseStep 334151 = 501227) B501227
theorem B150015 : Blo 147793 150015 := bstep (se 1 (by rfl) ⟨112511, by rfl⟩ : syracuseStep 150015 = 225023) B225023
theorem B222767 : Blo 147793 222767 := bstep (se 1 (by rfl) ⟨167075, by rfl⟩ : syracuseStep 222767 = 334151) B334151
theorem B148511 : Blo 147793 148511 := bstep (se 1 (by rfl) ⟨111383, by rfl⟩ : syracuseStep 148511 = 222767) B222767

theorem C0 (j : ℕ) (h1 : 36948 ≤ j) (h2 : j ≤ 37647) : Blo 147793 (4 * j + 3) := by
  interval_cases j
  · exact B147795
  · exact B147799
  · exact B147803
  · exact B147807
  · exact B147811
  · exact B147815
  · exact B147819
  · exact B147823
  · exact B147827
  · exact B147831
  · exact B147835
  · exact B147839
  · exact B147843
  · exact B147847
  · exact B147851
  · exact B147855
  · exact B147859
  · exact B147863
  · exact B147867
  · exact B147871
  · exact B147875
  · exact B147879
  · exact B147883
  · exact B147887
  · exact B147891
  · exact B147895
  · exact B147899
  · exact B147903
  · exact B147907
  · exact B147911
  · exact B147915
  · exact B147919
  · exact B147923
  · exact B147927
  · exact B147931
  · exact B147935
  · exact B147939
  · exact B147943
  · exact B147947
  · exact B147951
  · exact B147955
  · exact B147959
  · exact B147963
  · exact B147967
  · exact B147971
  · exact B147975
  · exact B147979
  · exact B147983
  · exact B147987
  · exact B147991
  · exact B147995
  · exact B147999
  · exact B148003
  · exact B148007
  · exact B148011
  · exact B148015
  · exact B148019
  · exact B148023
  · exact B148027
  · exact B148031
  · exact B148035
  · exact B148039
  · exact B148043
  · exact B148047
  · exact B148051
  · exact B148055
  · exact B148059
  · exact B148063
  · exact B148067
  · exact B148071
  · exact B148075
  · exact B148079
  · exact B148083
  · exact B148087
  · exact B148091
  · exact B148095
  · exact B148099
  · exact B148103
  · exact B148107
  · exact B148111
  · exact B148115
  · exact B148119
  · exact B148123
  · exact B148127
  · exact B148131
  · exact B148135
  · exact B148139
  · exact B148143
  · exact B148147
  · exact B148151
  · exact B148155
  · exact B148159
  · exact B148163
  · exact B148167
  · exact B148171
  · exact B148175
  · exact B148179
  · exact B148183
  · exact B148187
  · exact B148191
  · exact B148195
  · exact B148199
  · exact B148203
  · exact B148207
  · exact B148211
  · exact B148215
  · exact B148219
  · exact B148223
  · exact B148227
  · exact B148231
  · exact B148235
  · exact B148239
  · exact B148243
  · exact B148247
  · exact B148251
  · exact B148255
  · exact B148259
  · exact B148263
  · exact B148267
  · exact B148271
  · exact B148275
  · exact B148279
  · exact B148283
  · exact B148287
  · exact B148291
  · exact B148295
  · exact B148299
  · exact B148303
  · exact B148307
  · exact B148311
  · exact B148315
  · exact B148319
  · exact B148323
  · exact B148327
  · exact B148331
  · exact B148335
  · exact B148339
  · exact B148343
  · exact B148347
  · exact B148351
  · exact B148355
  · exact B148359
  · exact B148363
  · exact B148367
  · exact B148371
  · exact B148375
  · exact B148379
  · exact B148383
  · exact B148387
  · exact B148391
  · exact B148395
  · exact B148399
  · exact B148403
  · exact B148407
  · exact B148411
  · exact B148415
  · exact B148419
  · exact B148423
  · exact B148427
  · exact B148431
  · exact B148435
  · exact B148439
  · exact B148443
  · exact B148447
  · exact B148451
  · exact B148455
  · exact B148459
  · exact B148463
  · exact B148467
  · exact B148471
  · exact B148475
  · exact B148479
  · exact B148483
  · exact B148487
  · exact B148491
  · exact B148495
  · exact B148499
  · exact B148503
  · exact B148507
  · exact B148511
  · exact B148515
  · exact B148519
  · exact B148523
  · exact B148527
  · exact B148531
  · exact B148535
  · exact B148539
  · exact B148543
  · exact B148547
  · exact B148551
  · exact B148555
  · exact B148559
  · exact B148563
  · exact B148567
  · exact B148571
  · exact B148575
  · exact B148579
  · exact B148583
  · exact B148587
  · exact B148591
  · exact B148595
  · exact B148599
  · exact B148603
  · exact B148607
  · exact B148611
  · exact B148615
  · exact B148619
  · exact B148623
  · exact B148627
  · exact B148631
  · exact B148635
  · exact B148639
  · exact B148643
  · exact B148647
  · exact B148651
  · exact B148655
  · exact B148659
  · exact B148663
  · exact B148667
  · exact B148671
  · exact B148675
  · exact B148679
  · exact B148683
  · exact B148687
  · exact B148691
  · exact B148695
  · exact B148699
  · exact B148703
  · exact B148707
  · exact B148711
  · exact B148715
  · exact B148719
  · exact B148723
  · exact B148727
  · exact B148731
  · exact B148735
  · exact B148739
  · exact B148743
  · exact B148747
  · exact B148751
  · exact B148755
  · exact B148759
  · exact B148763
  · exact B148767
  · exact B148771
  · exact B148775
  · exact B148779
  · exact B148783
  · exact B148787
  · exact B148791
  · exact B148795
  · exact B148799
  · exact B148803
  · exact B148807
  · exact B148811
  · exact B148815
  · exact B148819
  · exact B148823
  · exact B148827
  · exact B148831
  · exact B148835
  · exact B148839
  · exact B148843
  · exact B148847
  · exact B148851
  · exact B148855
  · exact B148859
  · exact B148863
  · exact B148867
  · exact B148871
  · exact B148875
  · exact B148879
  · exact B148883
  · exact B148887
  · exact B148891
  · exact B148895
  · exact B148899
  · exact B148903
  · exact B148907
  · exact B148911
  · exact B148915
  · exact B148919
  · exact B148923
  · exact B148927
  · exact B148931
  · exact B148935
  · exact B148939
  · exact B148943
  · exact B148947
  · exact B148951
  · exact B148955
  · exact B148959
  · exact B148963
  · exact B148967
  · exact B148971
  · exact B148975
  · exact B148979
  · exact B148983
  · exact B148987
  · exact B148991
  · exact B148995
  · exact B148999
  · exact B149003
  · exact B149007
  · exact B149011
  · exact B149015
  · exact B149019
  · exact B149023
  · exact B149027
  · exact B149031
  · exact B149035
  · exact B149039
  · exact B149043
  · exact B149047
  · exact B149051
  · exact B149055
  · exact B149059
  · exact B149063
  · exact B149067
  · exact B149071
  · exact B149075
  · exact B149079
  · exact B149083
  · exact B149087
  · exact B149091
  · exact B149095
  · exact B149099
  · exact B149103
  · exact B149107
  · exact B149111
  · exact B149115
  · exact B149119
  · exact B149123
  · exact B149127
  · exact B149131
  · exact B149135
  · exact B149139
  · exact B149143
  · exact B149147
  · exact B149151
  · exact B149155
  · exact B149159
  · exact B149163
  · exact B149167
  · exact B149171
  · exact B149175
  · exact B149179
  · exact B149183
  · exact B149187
  · exact B149191
  · exact B149195
  · exact B149199
  · exact B149203
  · exact B149207
  · exact B149211
  · exact B149215
  · exact B149219
  · exact B149223
  · exact B149227
  · exact B149231
  · exact B149235
  · exact B149239
  · exact B149243
  · exact B149247
  · exact B149251
  · exact B149255
  · exact B149259
  · exact B149263
  · exact B149267
  · exact B149271
  · exact B149275
  · exact B149279
  · exact B149283
  · exact B149287
  · exact B149291
  · exact B149295
  · exact B149299
  · exact B149303
  · exact B149307
  · exact B149311
  · exact B149315
  · exact B149319
  · exact B149323
  · exact B149327
  · exact B149331
  · exact B149335
  · exact B149339
  · exact B149343
  · exact B149347
  · exact B149351
  · exact B149355
  · exact B149359
  · exact B149363
  · exact B149367
  · exact B149371
  · exact B149375
  · exact B149379
  · exact B149383
  · exact B149387
  · exact B149391
  · exact B149395
  · exact B149399
  · exact B149403
  · exact B149407
  · exact B149411
  · exact B149415
  · exact B149419
  · exact B149423
  · exact B149427
  · exact B149431
  · exact B149435
  · exact B149439
  · exact B149443
  · exact B149447
  · exact B149451
  · exact B149455
  · exact B149459
  · exact B149463
  · exact B149467
  · exact B149471
  · exact B149475
  · exact B149479
  · exact B149483
  · exact B149487
  · exact B149491
  · exact B149495
  · exact B149499
  · exact B149503
  · exact B149507
  · exact B149511
  · exact B149515
  · exact B149519
  · exact B149523
  · exact B149527
  · exact B149531
  · exact B149535
  · exact B149539
  · exact B149543
  · exact B149547
  · exact B149551
  · exact B149555
  · exact B149559
  · exact B149563
  · exact B149567
  · exact B149571
  · exact B149575
  · exact B149579
  · exact B149583
  · exact B149587
  · exact B149591
  · exact B149595
  · exact B149599
  · exact B149603
  · exact B149607
  · exact B149611
  · exact B149615
  · exact B149619
  · exact B149623
  · exact B149627
  · exact B149631
  · exact B149635
  · exact B149639
  · exact B149643
  · exact B149647
  · exact B149651
  · exact B149655
  · exact B149659
  · exact B149663
  · exact B149667
  · exact B149671
  · exact B149675
  · exact B149679
  · exact B149683
  · exact B149687
  · exact B149691
  · exact B149695
  · exact B149699
  · exact B149703
  · exact B149707
  · exact B149711
  · exact B149715
  · exact B149719
  · exact B149723
  · exact B149727
  · exact B149731
  · exact B149735
  · exact B149739
  · exact B149743
  · exact B149747
  · exact B149751
  · exact B149755
  · exact B149759
  · exact B149763
  · exact B149767
  · exact B149771
  · exact B149775
  · exact B149779
  · exact B149783
  · exact B149787
  · exact B149791
  · exact B149795
  · exact B149799
  · exact B149803
  · exact B149807
  · exact B149811
  · exact B149815
  · exact B149819
  · exact B149823
  · exact B149827
  · exact B149831
  · exact B149835
  · exact B149839
  · exact B149843
  · exact B149847
  · exact B149851
  · exact B149855
  · exact B149859
  · exact B149863
  · exact B149867
  · exact B149871
  · exact B149875
  · exact B149879
  · exact B149883
  · exact B149887
  · exact B149891
  · exact B149895
  · exact B149899
  · exact B149903
  · exact B149907
  · exact B149911
  · exact B149915
  · exact B149919
  · exact B149923
  · exact B149927
  · exact B149931
  · exact B149935
  · exact B149939
  · exact B149943
  · exact B149947
  · exact B149951
  · exact B149955
  · exact B149959
  · exact B149963
  · exact B149967
  · exact B149971
  · exact B149975
  · exact B149979
  · exact B149983
  · exact B149987
  · exact B149991
  · exact B149995
  · exact B149999
  · exact B150003
  · exact B150007
  · exact B150011
  · exact B150015
  · exact B150019
  · exact B150023
  · exact B150027
  · exact B150031
  · exact B150035
  · exact B150039
  · exact B150043
  · exact B150047
  · exact B150051
  · exact B150055
  · exact B150059
  · exact B150063
  · exact B150067
  · exact B150071
  · exact B150075
  · exact B150079
  · exact B150083
  · exact B150087
  · exact B150091
  · exact B150095
  · exact B150099
  · exact B150103
  · exact B150107
  · exact B150111
  · exact B150115
  · exact B150119
  · exact B150123
  · exact B150127
  · exact B150131
  · exact B150135
  · exact B150139
  · exact B150143
  · exact B150147
  · exact B150151
  · exact B150155
  · exact B150159
  · exact B150163
  · exact B150167
  · exact B150171
  · exact B150175
  · exact B150179
  · exact B150183
  · exact B150187
  · exact B150191
  · exact B150195
  · exact B150199
  · exact B150203
  · exact B150207
  · exact B150211
  · exact B150215
  · exact B150219
  · exact B150223
  · exact B150227
  · exact B150231
  · exact B150235
  · exact B150239
  · exact B150243
  · exact B150247
  · exact B150251
  · exact B150255
  · exact B150259
  · exact B150263
  · exact B150267
  · exact B150271
  · exact B150275
  · exact B150279
  · exact B150283
  · exact B150287
  · exact B150291
  · exact B150295
  · exact B150299
  · exact B150303
  · exact B150307
  · exact B150311
  · exact B150315
  · exact B150319
  · exact B150323
  · exact B150327
  · exact B150331
  · exact B150335
  · exact B150339
  · exact B150343
  · exact B150347
  · exact B150351
  · exact B150355
  · exact B150359
  · exact B150363
  · exact B150367
  · exact B150371
  · exact B150375
  · exact B150379
  · exact B150383
  · exact B150387
  · exact B150391
  · exact B150395
  · exact B150399
  · exact B150403
  · exact B150407
  · exact B150411
  · exact B150415
  · exact B150419
  · exact B150423
  · exact B150427
  · exact B150431
  · exact B150435
  · exact B150439
  · exact B150443
  · exact B150447
  · exact B150451
  · exact B150455
  · exact B150459
  · exact B150463
  · exact B150467
  · exact B150471
  · exact B150475
  · exact B150479
  · exact B150483
  · exact B150487
  · exact B150491
  · exact B150495
  · exact B150499
  · exact B150503
  · exact B150507
  · exact B150511
  · exact B150515
  · exact B150519
  · exact B150523
  · exact B150527
  · exact B150531
  · exact B150535
  · exact B150539
  · exact B150543
  · exact B150547
  · exact B150551
  · exact B150555
  · exact B150559
  · exact B150563
  · exact B150567
  · exact B150571
  · exact B150575
  · exact B150579
  · exact B150583
  · exact B150587
  · exact B150591

theorem C1 (j : ℕ) (h1 : 37648 ≤ j) (h2 : j ≤ 37947) : Blo 147793 (4 * j + 3) := by
  interval_cases j
  · exact B150595
  · exact B150599
  · exact B150603
  · exact B150607
  · exact B150611
  · exact B150615
  · exact B150619
  · exact B150623
  · exact B150627
  · exact B150631
  · exact B150635
  · exact B150639
  · exact B150643
  · exact B150647
  · exact B150651
  · exact B150655
  · exact B150659
  · exact B150663
  · exact B150667
  · exact B150671
  · exact B150675
  · exact B150679
  · exact B150683
  · exact B150687
  · exact B150691
  · exact B150695
  · exact B150699
  · exact B150703
  · exact B150707
  · exact B150711
  · exact B150715
  · exact B150719
  · exact B150723
  · exact B150727
  · exact B150731
  · exact B150735
  · exact B150739
  · exact B150743
  · exact B150747
  · exact B150751
  · exact B150755
  · exact B150759
  · exact B150763
  · exact B150767
  · exact B150771
  · exact B150775
  · exact B150779
  · exact B150783
  · exact B150787
  · exact B150791
  · exact B150795
  · exact B150799
  · exact B150803
  · exact B150807
  · exact B150811
  · exact B150815
  · exact B150819
  · exact B150823
  · exact B150827
  · exact B150831
  · exact B150835
  · exact B150839
  · exact B150843
  · exact B150847
  · exact B150851
  · exact B150855
  · exact B150859
  · exact B150863
  · exact B150867
  · exact B150871
  · exact B150875
  · exact B150879
  · exact B150883
  · exact B150887
  · exact B150891
  · exact B150895
  · exact B150899
  · exact B150903
  · exact B150907
  · exact B150911
  · exact B150915
  · exact B150919
  · exact B150923
  · exact B150927
  · exact B150931
  · exact B150935
  · exact B150939
  · exact B150943
  · exact B150947
  · exact B150951
  · exact B150955
  · exact B150959
  · exact B150963
  · exact B150967
  · exact B150971
  · exact B150975
  · exact B150979
  · exact B150983
  · exact B150987
  · exact B150991
  · exact B150995
  · exact B150999
  · exact B151003
  · exact B151007
  · exact B151011
  · exact B151015
  · exact B151019
  · exact B151023
  · exact B151027
  · exact B151031
  · exact B151035
  · exact B151039
  · exact B151043
  · exact B151047
  · exact B151051
  · exact B151055
  · exact B151059
  · exact B151063
  · exact B151067
  · exact B151071
  · exact B151075
  · exact B151079
  · exact B151083
  · exact B151087
  · exact B151091
  · exact B151095
  · exact B151099
  · exact B151103
  · exact B151107
  · exact B151111
  · exact B151115
  · exact B151119
  · exact B151123
  · exact B151127
  · exact B151131
  · exact B151135
  · exact B151139
  · exact B151143
  · exact B151147
  · exact B151151
  · exact B151155
  · exact B151159
  · exact B151163
  · exact B151167
  · exact B151171
  · exact B151175
  · exact B151179
  · exact B151183
  · exact B151187
  · exact B151191
  · exact B151195
  · exact B151199
  · exact B151203
  · exact B151207
  · exact B151211
  · exact B151215
  · exact B151219
  · exact B151223
  · exact B151227
  · exact B151231
  · exact B151235
  · exact B151239
  · exact B151243
  · exact B151247
  · exact B151251
  · exact B151255
  · exact B151259
  · exact B151263
  · exact B151267
  · exact B151271
  · exact B151275
  · exact B151279
  · exact B151283
  · exact B151287
  · exact B151291
  · exact B151295
  · exact B151299
  · exact B151303
  · exact B151307
  · exact B151311
  · exact B151315
  · exact B151319
  · exact B151323
  · exact B151327
  · exact B151331
  · exact B151335
  · exact B151339
  · exact B151343
  · exact B151347
  · exact B151351
  · exact B151355
  · exact B151359
  · exact B151363
  · exact B151367
  · exact B151371
  · exact B151375
  · exact B151379
  · exact B151383
  · exact B151387
  · exact B151391
  · exact B151395
  · exact B151399
  · exact B151403
  · exact B151407
  · exact B151411
  · exact B151415
  · exact B151419
  · exact B151423
  · exact B151427
  · exact B151431
  · exact B151435
  · exact B151439
  · exact B151443
  · exact B151447
  · exact B151451
  · exact B151455
  · exact B151459
  · exact B151463
  · exact B151467
  · exact B151471
  · exact B151475
  · exact B151479
  · exact B151483
  · exact B151487
  · exact B151491
  · exact B151495
  · exact B151499
  · exact B151503
  · exact B151507
  · exact B151511
  · exact B151515
  · exact B151519
  · exact B151523
  · exact B151527
  · exact B151531
  · exact B151535
  · exact B151539
  · exact B151543
  · exact B151547
  · exact B151551
  · exact B151555
  · exact B151559
  · exact B151563
  · exact B151567
  · exact B151571
  · exact B151575
  · exact B151579
  · exact B151583
  · exact B151587
  · exact B151591
  · exact B151595
  · exact B151599
  · exact B151603
  · exact B151607
  · exact B151611
  · exact B151615
  · exact B151619
  · exact B151623
  · exact B151627
  · exact B151631
  · exact B151635
  · exact B151639
  · exact B151643
  · exact B151647
  · exact B151651
  · exact B151655
  · exact B151659
  · exact B151663
  · exact B151667
  · exact B151671
  · exact B151675
  · exact B151679
  · exact B151683
  · exact B151687
  · exact B151691
  · exact B151695
  · exact B151699
  · exact B151703
  · exact B151707
  · exact B151711
  · exact B151715
  · exact B151719
  · exact B151723
  · exact B151727
  · exact B151731
  · exact B151735
  · exact B151739
  · exact B151743
  · exact B151747
  · exact B151751
  · exact B151755
  · exact B151759
  · exact B151763
  · exact B151767
  · exact B151771
  · exact B151775
  · exact B151779
  · exact B151783
  · exact B151787
  · exact B151791

theorem solution (m : ℕ) (hlo : 147793 ≤ m) (hhi : m ≤ 151793) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 36948 ≤ j := by omega
    have hj2 : j ≤ 37947 := by omega
    have hb : Blo 147793 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 37648 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
