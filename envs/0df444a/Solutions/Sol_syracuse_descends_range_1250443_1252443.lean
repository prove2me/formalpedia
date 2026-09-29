-- Prove2me | solution 1 for syracuse_descends_range_1250443_1252443
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:17.254955+00:00
-- url     : https://prove2.me/submissions/3f07faea-ed9d-449d-b934-0e6ac3bc7a8e

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


theorem B1875989 : Blo 1250443 1875989 := bbase (se 6 (by rfl) ⟨43968, by rfl⟩ : syracuseStep 1875989 = 87937) (by norm_num)
theorem B1876013 : Blo 1250443 1876013 := bbase (se 3 (by rfl) ⟨351752, by rfl⟩ : syracuseStep 1876013 = 703505) (by norm_num)
theorem B2670661 : Blo 1250443 2670661 := bbase (se 4 (by rfl) ⟨250374, by rfl⟩ : syracuseStep 2670661 = 500749) (by norm_num)
theorem B1876037 : Blo 1250443 1876037 := bbase (se 4 (by rfl) ⟨175878, by rfl⟩ : syracuseStep 1876037 = 351757) (by norm_num)
theorem B1876061 : Blo 1250443 1876061 := bbase (se 3 (by rfl) ⟨351761, by rfl⟩ : syracuseStep 1876061 = 703523) (by norm_num)
theorem B1876085 : Blo 1250443 1876085 := bbase (se 5 (by rfl) ⟨87941, by rfl⟩ : syracuseStep 1876085 = 175883) (by norm_num)
theorem B1876109 : Blo 1250443 1876109 := bbase (se 3 (by rfl) ⟨351770, by rfl⟩ : syracuseStep 1876109 = 703541) (by norm_num)
theorem B1876133 : Blo 1250443 1876133 := bbase (se 4 (by rfl) ⟨175887, by rfl⟩ : syracuseStep 1876133 = 351775) (by norm_num)
theorem B1876157 : Blo 1250443 1876157 := bbase (se 3 (by rfl) ⟨351779, by rfl⟩ : syracuseStep 1876157 = 703559) (by norm_num)
theorem B1876181 : Blo 1250443 1876181 := bbase (se 7 (by rfl) ⟨21986, by rfl⟩ : syracuseStep 1876181 = 43973) (by norm_num)
theorem B1876205 : Blo 1250443 1876205 := bbase (se 3 (by rfl) ⟨351788, by rfl⟩ : syracuseStep 1876205 = 703577) (by norm_num)
theorem B1876229 : Blo 1250443 1876229 := bbase (se 4 (by rfl) ⟨175896, by rfl⟩ : syracuseStep 1876229 = 351793) (by norm_num)
theorem B3006733 : Blo 1250443 3006733 := bbase (se 3 (by rfl) ⟨563762, by rfl⟩ : syracuseStep 3006733 = 1127525) (by norm_num)
theorem B3563797 : Blo 1250443 3563797 := bbase (se 6 (by rfl) ⟨83526, by rfl⟩ : syracuseStep 3563797 = 167053) (by norm_num)
theorem B1876253 : Blo 1250443 1876253 := bbase (se 3 (by rfl) ⟨351797, by rfl⟩ : syracuseStep 1876253 = 703595) (by norm_num)
theorem B1876277 : Blo 1250443 1876277 := bbase (se 5 (by rfl) ⟨87950, by rfl⟩ : syracuseStep 1876277 = 175901) (by norm_num)
theorem B6332741 : Blo 1250443 6332741 := bbase (se 4 (by rfl) ⟨593694, by rfl⟩ : syracuseStep 6332741 = 1187389) (by norm_num)
theorem B1876301 : Blo 1250443 1876301 := bbase (se 3 (by rfl) ⟨351806, by rfl⟩ : syracuseStep 1876301 = 703613) (by norm_num)
theorem B1876325 : Blo 1250443 1876325 := bbase (se 4 (by rfl) ⟨175905, by rfl⟩ : syracuseStep 1876325 = 351811) (by norm_num)
theorem B3006829 : Blo 1250443 3006829 := bbase (se 3 (by rfl) ⟨563780, by rfl⟩ : syracuseStep 3006829 = 1127561) (by norm_num)
theorem B1876349 : Blo 1250443 1876349 := bbase (se 3 (by rfl) ⟨351815, by rfl⟩ : syracuseStep 1876349 = 703631) (by norm_num)
theorem B1335685 : Blo 1250443 1335685 := bbase (se 4 (by rfl) ⟨125220, by rfl⟩ : syracuseStep 1335685 = 250441) (by norm_num)
theorem B1876373 : Blo 1250443 1876373 := bbase (se 6 (by rfl) ⟨43977, by rfl⟩ : syracuseStep 1876373 = 87955) (by norm_num)
theorem B5349797 : Blo 1250443 5349797 := bbase (se 4 (by rfl) ⟨501543, by rfl⟩ : syracuseStep 5349797 = 1003087) (by norm_num)
theorem B1876397 : Blo 1250443 1876397 := bbase (se 3 (by rfl) ⟨351824, by rfl⟩ : syracuseStep 1876397 = 703649) (by norm_num)
theorem B1876421 : Blo 1250443 1876421 := bbase (se 4 (by rfl) ⟨175914, by rfl⟩ : syracuseStep 1876421 = 351829) (by norm_num)
theorem B1876445 : Blo 1250443 1876445 := bbase (se 3 (by rfl) ⟨351833, by rfl⟩ : syracuseStep 1876445 = 703667) (by norm_num)
theorem B1876469 : Blo 1250443 1876469 := bbase (se 5 (by rfl) ⟨87959, by rfl⟩ : syracuseStep 1876469 = 175919) (by norm_num)
theorem B1335809 : Blo 1250443 1335809 := bbase (se 2 (by rfl) ⟨500928, by rfl⟩ : syracuseStep 1335809 = 1001857) (by norm_num)
theorem B4882949 : Blo 1250443 4882949 := bbase (se 4 (by rfl) ⟨457776, by rfl⟩ : syracuseStep 4882949 = 915553) (by norm_num)
theorem B1876493 : Blo 1250443 1876493 := bbase (se 3 (by rfl) ⟨351842, by rfl⟩ : syracuseStep 1876493 = 703685) (by norm_num)
theorem B5341733 : Blo 1250443 5341733 := bbase (se 4 (by rfl) ⟨500787, by rfl⟩ : syracuseStep 5341733 = 1001575) (by norm_num)
theorem B1876517 : Blo 1250443 1876517 := bbase (se 4 (by rfl) ⟨175923, by rfl⟩ : syracuseStep 1876517 = 351847) (by norm_num)
theorem B2376229 : Blo 1250443 2376229 := bbase (se 4 (by rfl) ⟨222771, by rfl⟩ : syracuseStep 2376229 = 445543) (by norm_num)
theorem B12182069 : Blo 1250443 12182069 := bbase (se 5 (by rfl) ⟨571034, by rfl⟩ : syracuseStep 12182069 = 1142069) (by norm_num)
theorem B1876541 : Blo 1250443 1876541 := bbase (se 3 (by rfl) ⟨351851, by rfl⟩ : syracuseStep 1876541 = 703703) (by norm_num)
theorem B1876565 : Blo 1250443 1876565 := bbase (se 8 (by rfl) ⟨10995, by rfl⟩ : syracuseStep 1876565 = 21991) (by norm_num)
theorem B1876589 : Blo 1250443 1876589 := bbase (se 3 (by rfl) ⟨351860, by rfl⟩ : syracuseStep 1876589 = 703721) (by norm_num)
theorem B1876613 : Blo 1250443 1876613 := bbase (se 4 (by rfl) ⟨175932, by rfl⟩ : syracuseStep 1876613 = 351865) (by norm_num)
theorem B1876637 : Blo 1250443 1876637 := bbase (se 3 (by rfl) ⟨351869, by rfl⟩ : syracuseStep 1876637 = 703739) (by norm_num)
theorem B1876661 : Blo 1250443 1876661 := bbase (se 5 (by rfl) ⟨87968, by rfl⟩ : syracuseStep 1876661 = 175937) (by norm_num)
theorem B2376373 : Blo 1250443 2376373 := bbase (se 5 (by rfl) ⟨111392, by rfl⟩ : syracuseStep 2376373 = 222785) (by norm_num)
theorem B1876685 : Blo 1250443 1876685 := bbase (se 3 (by rfl) ⟨351878, by rfl⟩ : syracuseStep 1876685 = 703757) (by norm_num)
theorem B1876709 : Blo 1250443 1876709 := bbase (se 4 (by rfl) ⟨175941, by rfl⟩ : syracuseStep 1876709 = 351883) (by norm_num)
theorem B7127797 : Blo 1250443 7127797 := bbase (se 5 (by rfl) ⟨334115, by rfl⟩ : syracuseStep 7127797 = 668231) (by norm_num)
theorem B1336061 : Blo 1250443 1336061 := bbase (se 3 (by rfl) ⟨250511, by rfl⟩ : syracuseStep 1336061 = 501023) (by norm_num)
theorem B1876733 : Blo 1250443 1876733 := bbase (se 3 (by rfl) ⟨351887, by rfl⟩ : syracuseStep 1876733 = 703775) (by norm_num)
theorem B1876757 : Blo 1250443 1876757 := bbase (se 6 (by rfl) ⟨43986, by rfl⟩ : syracuseStep 1876757 = 87973) (by norm_num)
theorem B1876781 : Blo 1250443 1876781 := bbase (se 3 (by rfl) ⟨351896, by rfl⟩ : syracuseStep 1876781 = 703793) (by norm_num)
theorem B5342021 : Blo 1250443 5342021 := bbase (se 4 (by rfl) ⟨500814, by rfl⟩ : syracuseStep 5342021 = 1001629) (by norm_num)
theorem B1876805 : Blo 1250443 1876805 := bbase (se 4 (by rfl) ⟨175950, by rfl⟩ : syracuseStep 1876805 = 351901) (by norm_num)
theorem B2376533 : Blo 1250443 2376533 := bbase (se 9 (by rfl) ⟨6962, by rfl⟩ : syracuseStep 2376533 = 13925) (by norm_num)
theorem B1876829 : Blo 1250443 1876829 := bbase (se 3 (by rfl) ⟨351905, by rfl⟩ : syracuseStep 1876829 = 703811) (by norm_num)
theorem B4752229 : Blo 1250443 4752229 := bbase (se 4 (by rfl) ⟨445521, by rfl⟩ : syracuseStep 4752229 = 891043) (by norm_num)
theorem B1876853 : Blo 1250443 1876853 := bbase (se 5 (by rfl) ⟨87977, by rfl⟩ : syracuseStep 1876853 = 175955) (by norm_num)
theorem B1876877 : Blo 1250443 1876877 := bbase (se 3 (by rfl) ⟨351914, by rfl⟩ : syracuseStep 1876877 = 703829) (by norm_num)
theorem B1524629 : Blo 1250443 1524629 := bbase (se 6 (by rfl) ⟨35733, by rfl⟩ : syracuseStep 1524629 = 71467) (by norm_num)
theorem B1901477 : Blo 1250443 1901477 := bbase (se 4 (by rfl) ⟨178263, by rfl⟩ : syracuseStep 1901477 = 356527) (by norm_num)
theorem B1876901 : Blo 1250443 1876901 := bbase (se 4 (by rfl) ⟨175959, by rfl⟩ : syracuseStep 1876901 = 351919) (by norm_num)
theorem B1876925 : Blo 1250443 1876925 := bbase (se 3 (by rfl) ⟨351923, by rfl⟩ : syracuseStep 1876925 = 703847) (by norm_num)
theorem B2253781 : Blo 1250443 2253781 := bbase (se 7 (by rfl) ⟨26411, by rfl⟩ : syracuseStep 2253781 = 52823) (by norm_num)
theorem B1876949 : Blo 1250443 1876949 := bbase (se 7 (by rfl) ⟨21995, by rfl⟩ : syracuseStep 1876949 = 43991) (by norm_num)
theorem B2376677 : Blo 1250443 2376677 := bbase (se 4 (by rfl) ⟨222813, by rfl⟩ : syracuseStep 2376677 = 445627) (by norm_num)
theorem B1876973 : Blo 1250443 1876973 := bbase (se 3 (by rfl) ⟨351932, by rfl⟩ : syracuseStep 1876973 = 703865) (by norm_num)
theorem B1876997 : Blo 1250443 1876997 := bbase (se 4 (by rfl) ⟨175968, by rfl⟩ : syracuseStep 1876997 = 351937) (by norm_num)
theorem B1877021 : Blo 1250443 1877021 := bbase (se 3 (by rfl) ⟨351941, by rfl⟩ : syracuseStep 1877021 = 703883) (by norm_num)
theorem B1877045 : Blo 1250443 1877045 := bbase (se 5 (by rfl) ⟨87986, by rfl⟩ : syracuseStep 1877045 = 175973) (by norm_num)
theorem B1877069 : Blo 1250443 1877069 := bbase (se 3 (by rfl) ⟨351950, by rfl⟩ : syracuseStep 1877069 = 703901) (by norm_num)
theorem B1877093 : Blo 1250443 1877093 := bbase (se 4 (by rfl) ⟨175977, by rfl⟩ : syracuseStep 1877093 = 351955) (by norm_num)
theorem B4007029 : Blo 1250443 4007029 := bbase (se 5 (by rfl) ⟨187829, by rfl⟩ : syracuseStep 4007029 = 375659) (by norm_num)
theorem B1877117 : Blo 1250443 1877117 := bbase (se 3 (by rfl) ⟨351959, by rfl⟩ : syracuseStep 1877117 = 703919) (by norm_num)
theorem B1877141 : Blo 1250443 1877141 := bbase (se 6 (by rfl) ⟨43995, by rfl⟩ : syracuseStep 1877141 = 87991) (by norm_num)
theorem B4752533 : Blo 1250443 4752533 := bbase (se 6 (by rfl) ⟨111387, by rfl⟩ : syracuseStep 4752533 = 222775) (by norm_num)
theorem B1877165 : Blo 1250443 1877165 := bbase (se 3 (by rfl) ⟨351968, by rfl⟩ : syracuseStep 1877165 = 703937) (by norm_num)
theorem B1336505 : Blo 1250443 1336505 := bbase (se 2 (by rfl) ⟨501189, by rfl⟩ : syracuseStep 1336505 = 1002379) (by norm_num)
theorem B1877189 : Blo 1250443 1877189 := bbase (se 4 (by rfl) ⟨175986, by rfl⟩ : syracuseStep 1877189 = 351973) (by norm_num)
theorem B1877213 : Blo 1250443 1877213 := bbase (se 3 (by rfl) ⟨351977, by rfl⟩ : syracuseStep 1877213 = 703955) (by norm_num)
theorem B1877237 : Blo 1250443 1877237 := bbase (se 5 (by rfl) ⟨87995, by rfl⟩ : syracuseStep 1877237 = 175991) (by norm_num)
theorem B2376965 : Blo 1250443 2376965 := bbase (se 4 (by rfl) ⟨222840, by rfl⟩ : syracuseStep 2376965 = 445681) (by norm_num)
theorem B3212549 : Blo 1250443 3212549 := bbase (se 4 (by rfl) ⟨301176, by rfl⟩ : syracuseStep 3212549 = 602353) (by norm_num)
theorem B1877261 : Blo 1250443 1877261 := bbase (se 3 (by rfl) ⟨351986, by rfl⟩ : syracuseStep 1877261 = 703973) (by norm_num)
theorem B1877285 : Blo 1250443 1877285 := bbase (se 4 (by rfl) ⟨175995, by rfl⟩ : syracuseStep 1877285 = 351991) (by norm_num)
theorem B1877309 : Blo 1250443 1877309 := bbase (se 3 (by rfl) ⟨351995, by rfl⟩ : syracuseStep 1877309 = 703991) (by norm_num)
theorem B1877333 : Blo 1250443 1877333 := bbase (se 12 (by rfl) ⟨687, by rfl⟩ : syracuseStep 1877333 = 1375) (by norm_num)
theorem B4220261 : Blo 1250443 4220261 := bbase (se 4 (by rfl) ⟨395649, by rfl⟩ : syracuseStep 4220261 = 791299) (by norm_num)
theorem B3564901 : Blo 1250443 3564901 := bbase (se 4 (by rfl) ⟨334209, by rfl⟩ : syracuseStep 3564901 = 668419) (by norm_num)
theorem B1877357 : Blo 1250443 1877357 := bbase (se 3 (by rfl) ⟨352004, by rfl⟩ : syracuseStep 1877357 = 704009) (by norm_num)
theorem B8562037 : Blo 1250443 8562037 := bbase (se 5 (by rfl) ⟨401345, by rfl⟩ : syracuseStep 8562037 = 802691) (by norm_num)
theorem B1877381 : Blo 1250443 1877381 := bbase (se 4 (by rfl) ⟨176004, by rfl⟩ : syracuseStep 1877381 = 352009) (by norm_num)
theorem B1877405 : Blo 1250443 1877405 := bbase (se 3 (by rfl) ⟨352013, by rfl⟩ : syracuseStep 1877405 = 704027) (by norm_num)
theorem B2377117 : Blo 1250443 2377117 := bbase (se 3 (by rfl) ⟨445709, by rfl⟩ : syracuseStep 2377117 = 891419) (by norm_num)
theorem B1336753 : Blo 1250443 1336753 := bbase (se 2 (by rfl) ⟨501282, by rfl⟩ : syracuseStep 1336753 = 1002565) (by norm_num)
theorem B1877429 : Blo 1250443 1877429 := bbase (se 5 (by rfl) ⟨88004, by rfl⟩ : syracuseStep 1877429 = 176009) (by norm_num)
theorem B3007925 : Blo 1250443 3007925 := bbase (se 5 (by rfl) ⟨140996, by rfl⟩ : syracuseStep 3007925 = 281993) (by norm_num)
theorem B1713613 : Blo 1250443 1713613 := bbase (se 3 (by rfl) ⟨321302, by rfl⟩ : syracuseStep 1713613 = 642605) (by norm_num)
theorem B1877453 : Blo 1250443 1877453 := bbase (se 3 (by rfl) ⟨352022, by rfl⟩ : syracuseStep 1877453 = 704045) (by norm_num)
theorem B1877477 : Blo 1250443 1877477 := bbase (se 4 (by rfl) ⟨176013, by rfl⟩ : syracuseStep 1877477 = 352027) (by norm_num)
theorem B1877501 : Blo 1250443 1877501 := bbase (se 3 (by rfl) ⟨352031, by rfl⟩ : syracuseStep 1877501 = 704063) (by norm_num)
theorem B1877525 : Blo 1250443 1877525 := bbase (se 6 (by rfl) ⟨44004, by rfl⟩ : syracuseStep 1877525 = 88009) (by norm_num)
theorem B2672165 : Blo 1250443 2672165 := bbase (se 4 (by rfl) ⟨250515, by rfl⟩ : syracuseStep 2672165 = 501031) (by norm_num)
theorem B2033189 : Blo 1250443 2033189 := bbase (se 4 (by rfl) ⟨190611, by rfl⟩ : syracuseStep 2033189 = 381223) (by norm_num)
theorem B1877549 : Blo 1250443 1877549 := bbase (se 3 (by rfl) ⟨352040, by rfl⟩ : syracuseStep 1877549 = 704081) (by norm_num)
theorem B5342773 : Blo 1250443 5342773 := bbase (se 5 (by rfl) ⟨250442, by rfl⟩ : syracuseStep 5342773 = 500885) (by norm_num)
theorem B1877573 : Blo 1250443 1877573 := bbase (se 4 (by rfl) ⟨176022, by rfl⟩ : syracuseStep 1877573 = 352045) (by norm_num)
theorem B1582669 : Blo 1250443 1582669 := bbase (se 3 (by rfl) ⟨296750, by rfl⟩ : syracuseStep 1582669 = 593501) (by norm_num)
theorem B6334037 : Blo 1250443 6334037 := bbase (se 8 (by rfl) ⟨37113, by rfl⟩ : syracuseStep 6334037 = 74227) (by norm_num)
theorem B1877597 : Blo 1250443 1877597 := bbase (se 3 (by rfl) ⟨352049, by rfl⟩ : syracuseStep 1877597 = 704099) (by norm_num)
theorem B1877621 : Blo 1250443 1877621 := bbase (se 5 (by rfl) ⟨88013, by rfl⟩ : syracuseStep 1877621 = 176027) (by norm_num)
theorem B1877645 : Blo 1250443 1877645 := bbase (se 3 (by rfl) ⟨352058, by rfl⟩ : syracuseStep 1877645 = 704117) (by norm_num)
theorem B1877669 : Blo 1250443 1877669 := bbase (se 4 (by rfl) ⟨176031, by rfl⟩ : syracuseStep 1877669 = 352063) (by norm_num)
theorem B2672309 : Blo 1250443 2672309 := bbase (se 5 (by rfl) ⟨125264, by rfl⟩ : syracuseStep 2672309 = 250529) (by norm_num)
theorem B1877693 : Blo 1250443 1877693 := bbase (se 3 (by rfl) ⟨352067, by rfl⟩ : syracuseStep 1877693 = 704135) (by norm_num)
theorem B2377421 : Blo 1250443 2377421 := bbase (se 3 (by rfl) ⟨445766, by rfl⟩ : syracuseStep 2377421 = 891533) (by norm_num)
theorem B32057045 : Blo 1250443 32057045 := bbase (se 7 (by rfl) ⟨375668, by rfl⟩ : syracuseStep 32057045 = 751337) (by norm_num)
theorem B1877717 : Blo 1250443 1877717 := bbase (se 7 (by rfl) ⟨22004, by rfl⟩ : syracuseStep 1877717 = 44009) (by norm_num)
theorem B1877741 : Blo 1250443 1877741 := bbase (se 3 (by rfl) ⟨352076, by rfl⟩ : syracuseStep 1877741 = 704153) (by norm_num)
theorem B1582841 : Blo 1250443 1582841 := bbase (se 2 (by rfl) ⟨593565, by rfl⟩ : syracuseStep 1582841 = 1187131) (by norm_num)
theorem B1877765 : Blo 1250443 1877765 := bbase (se 4 (by rfl) ⟨176040, by rfl⟩ : syracuseStep 1877765 = 352081) (by norm_num)
theorem B4220693 : Blo 1250443 4220693 := bbase (se 6 (by rfl) ⟨98922, by rfl⟩ : syracuseStep 4220693 = 197845) (by norm_num)
theorem B1877789 : Blo 1250443 1877789 := bbase (se 3 (by rfl) ⟨352085, by rfl⟩ : syracuseStep 1877789 = 704171) (by norm_num)
theorem B1582897 : Blo 1250443 1582897 := bbase (se 2 (by rfl) ⟨593586, by rfl⟩ : syracuseStep 1582897 = 1187173) (by norm_num)
theorem B1877813 : Blo 1250443 1877813 := bbase (se 5 (by rfl) ⟨88022, by rfl⟩ : syracuseStep 1877813 = 176045) (by norm_num)
theorem B1877837 : Blo 1250443 1877837 := bbase (se 3 (by rfl) ⟨352094, by rfl⟩ : syracuseStep 1877837 = 704189) (by norm_num)
theorem B1877861 : Blo 1250443 1877861 := bbase (se 4 (by rfl) ⟨176049, by rfl⟩ : syracuseStep 1877861 = 352099) (by norm_num)
theorem B1337197 : Blo 1250443 1337197 := bbase (se 3 (by rfl) ⟨250724, by rfl⟩ : syracuseStep 1337197 = 501449) (by norm_num)
theorem B6096757 : Blo 1250443 6096757 := bbase (se 5 (by rfl) ⟨285785, by rfl⟩ : syracuseStep 6096757 = 571571) (by norm_num)
theorem B1877885 : Blo 1250443 1877885 := bbase (se 3 (by rfl) ⟨352103, by rfl⟩ : syracuseStep 1877885 = 704207) (by norm_num)
theorem B1582993 : Blo 1250443 1582993 := bbase (se 2 (by rfl) ⟨593622, by rfl⟩ : syracuseStep 1582993 = 1187245) (by norm_num)
theorem B1877909 : Blo 1250443 1877909 := bbase (se 6 (by rfl) ⟨44013, by rfl⟩ : syracuseStep 1877909 = 88027) (by norm_num)
theorem B1337257 : Blo 1250443 1337257 := bbase (se 2 (by rfl) ⟨501471, by rfl⟩ : syracuseStep 1337257 = 1002943) (by norm_num)
theorem B1877933 : Blo 1250443 1877933 := bbase (se 3 (by rfl) ⟨352112, by rfl⟩ : syracuseStep 1877933 = 704225) (by norm_num)
theorem B1877957 : Blo 1250443 1877957 := bbase (se 4 (by rfl) ⟨176058, by rfl⟩ : syracuseStep 1877957 = 352117) (by norm_num)
theorem B1877981 : Blo 1250443 1877981 := bbase (se 3 (by rfl) ⟨352121, by rfl⟩ : syracuseStep 1877981 = 704243) (by norm_num)
theorem B1878005 : Blo 1250443 1878005 := bbase (se 5 (by rfl) ⟨88031, by rfl⟩ : syracuseStep 1878005 = 176063) (by norm_num)
theorem B1878029 : Blo 1250443 1878029 := bbase (se 3 (by rfl) ⟨352130, by rfl⟩ : syracuseStep 1878029 = 704261) (by norm_num)
theorem B2672669 : Blo 1250443 2672669 := bbase (se 3 (by rfl) ⟨501125, by rfl⟩ : syracuseStep 2672669 = 1002251) (by norm_num)
theorem B3213341 : Blo 1250443 3213341 := bbase (se 3 (by rfl) ⟨602501, by rfl⟩ : syracuseStep 3213341 = 1205003) (by norm_num)
theorem B1878053 : Blo 1250443 1878053 := bbase (se 4 (by rfl) ⟨176067, by rfl⟩ : syracuseStep 1878053 = 352135) (by norm_num)
theorem B1583165 : Blo 1250443 1583165 := bbase (se 3 (by rfl) ⟨296843, by rfl⟩ : syracuseStep 1583165 = 593687) (by norm_num)
theorem B1878077 : Blo 1250443 1878077 := bbase (se 3 (by rfl) ⟨352139, by rfl⟩ : syracuseStep 1878077 = 704279) (by norm_num)
theorem B1878101 : Blo 1250443 1878101 := bbase (se 8 (by rfl) ⟨11004, by rfl⟩ : syracuseStep 1878101 = 22009) (by norm_num)
theorem B1878125 : Blo 1250443 1878125 := bbase (se 3 (by rfl) ⟨352148, by rfl⟩ : syracuseStep 1878125 = 704297) (by norm_num)
theorem B1583221 : Blo 1250443 1583221 := bbase (se 5 (by rfl) ⟨74213, by rfl⟩ : syracuseStep 1583221 = 148427) (by norm_num)
theorem B9021557 : Blo 1250443 9021557 := bbase (se 5 (by rfl) ⟨422885, by rfl⟩ : syracuseStep 9021557 = 845771) (by norm_num)
theorem B1878149 : Blo 1250443 1878149 := bbase (se 4 (by rfl) ⟨176076, by rfl⟩ : syracuseStep 1878149 = 352153) (by norm_num)
theorem B1353865 : Blo 1250443 1353865 := bbase (se 2 (by rfl) ⟨507699, by rfl⟩ : syracuseStep 1353865 = 1015399) (by norm_num)
theorem B1878173 : Blo 1250443 1878173 := bbase (se 3 (by rfl) ⟨352157, by rfl⟩ : syracuseStep 1878173 = 704315) (by norm_num)
theorem B1878197 : Blo 1250443 1878197 := bbase (se 5 (by rfl) ⟨88040, by rfl⟩ : syracuseStep 1878197 = 176081) (by norm_num)
theorem B4221125 : Blo 1250443 4221125 := bbase (se 4 (by rfl) ⟨395730, by rfl⟩ : syracuseStep 4221125 = 791461) (by norm_num)
theorem B1878221 : Blo 1250443 1878221 := bbase (se 3 (by rfl) ⟨352166, by rfl⟩ : syracuseStep 1878221 = 704333) (by norm_num)
theorem B1583317 : Blo 1250443 1583317 := bbase (se 7 (by rfl) ⟨18554, by rfl⟩ : syracuseStep 1583317 = 37109) (by norm_num)
theorem B2140373 : Blo 1250443 2140373 := bbase (se 7 (by rfl) ⟨25082, by rfl⟩ : syracuseStep 2140373 = 50165) (by norm_num)
theorem B1878245 : Blo 1250443 1878245 := bbase (se 4 (by rfl) ⟨176085, by rfl⟩ : syracuseStep 1878245 = 352171) (by norm_num)
theorem B1878269 : Blo 1250443 1878269 := bbase (se 3 (by rfl) ⟨352175, by rfl⟩ : syracuseStep 1878269 = 704351) (by norm_num)
theorem B5343509 : Blo 1250443 5343509 := bbase (se 6 (by rfl) ⟨125238, by rfl⟩ : syracuseStep 5343509 = 250477) (by norm_num)
theorem B1878293 : Blo 1250443 1878293 := bbase (se 6 (by rfl) ⟨44022, by rfl⟩ : syracuseStep 1878293 = 88045) (by norm_num)
theorem B1878317 : Blo 1250443 1878317 := bbase (se 3 (by rfl) ⟨352184, by rfl⟩ : syracuseStep 1878317 = 704369) (by norm_num)
theorem B2255165 : Blo 1250443 2255165 := bbase (se 3 (by rfl) ⟨422843, by rfl⟩ : syracuseStep 2255165 = 845687) (by norm_num)
theorem B1878341 : Blo 1250443 1878341 := bbase (se 4 (by rfl) ⟨176094, by rfl⟩ : syracuseStep 1878341 = 352189) (by norm_num)
theorem B1878365 : Blo 1250443 1878365 := bbase (se 3 (by rfl) ⟨352193, by rfl⟩ : syracuseStep 1878365 = 704387) (by norm_num)
theorem B1427809 : Blo 1250443 1427809 := bbase (se 2 (by rfl) ⟨535428, by rfl⟩ : syracuseStep 1427809 = 1070857) (by norm_num)
theorem B1878389 : Blo 1250443 1878389 := bbase (se 5 (by rfl) ⟨88049, by rfl⟩ : syracuseStep 1878389 = 176099) (by norm_num)
theorem B3008885 : Blo 1250443 3008885 := bbase (se 5 (by rfl) ⟨141041, by rfl⟩ : syracuseStep 3008885 = 282083) (by norm_num)
theorem B1583489 : Blo 1250443 1583489 := bbase (se 2 (by rfl) ⟨593808, by rfl⟩ : syracuseStep 1583489 = 1187617) (by norm_num)
theorem B1878413 : Blo 1250443 1878413 := bbase (se 3 (by rfl) ⟨352202, by rfl⟩ : syracuseStep 1878413 = 704405) (by norm_num)
theorem B1878437 : Blo 1250443 1878437 := bbase (se 4 (by rfl) ⟨176103, by rfl⟩ : syracuseStep 1878437 = 352207) (by norm_num)
theorem B1583545 : Blo 1250443 1583545 := bbase (se 2 (by rfl) ⟨593829, by rfl⟩ : syracuseStep 1583545 = 1187659) (by norm_num)
theorem B1878461 : Blo 1250443 1878461 := bbase (se 3 (by rfl) ⟨352211, by rfl⟩ : syracuseStep 1878461 = 704423) (by norm_num)
theorem B2853317 : Blo 1250443 2853317 := bbase (se 4 (by rfl) ⟨267498, by rfl⟩ : syracuseStep 2853317 = 534997) (by norm_num)
theorem B1878485 : Blo 1250443 1878485 := bbase (se 7 (by rfl) ⟨22013, by rfl⟩ : syracuseStep 1878485 = 44027) (by norm_num)
theorem B1878509 : Blo 1250443 1878509 := bbase (se 3 (by rfl) ⟨352220, by rfl⟩ : syracuseStep 1878509 = 704441) (by norm_num)
theorem B4573685 : Blo 1250443 4573685 := bbase (se 5 (by rfl) ⟨214391, by rfl⟩ : syracuseStep 4573685 = 428783) (by norm_num)
theorem B1878533 : Blo 1250443 1878533 := bbase (se 4 (by rfl) ⟨176112, by rfl⟩ : syracuseStep 1878533 = 352225) (by norm_num)
theorem B1583641 : Blo 1250443 1583641 := bbase (se 2 (by rfl) ⟨593865, by rfl⟩ : syracuseStep 1583641 = 1187731) (by norm_num)
theorem B1878557 : Blo 1250443 1878557 := bbase (se 3 (by rfl) ⟨352229, by rfl⟩ : syracuseStep 1878557 = 704459) (by norm_num)
theorem B6015541 : Blo 1250443 6015541 := bbase (se 5 (by rfl) ⟨281978, by rfl⟩ : syracuseStep 6015541 = 563957) (by norm_num)
theorem B1878581 : Blo 1250443 1878581 := bbase (se 5 (by rfl) ⟨88058, by rfl⟩ : syracuseStep 1878581 = 176117) (by norm_num)
theorem B1878605 : Blo 1250443 1878605 := bbase (se 3 (by rfl) ⟨352238, by rfl⟩ : syracuseStep 1878605 = 704477) (by norm_num)
theorem B1878629 : Blo 1250443 1878629 := bbase (se 4 (by rfl) ⟨176121, by rfl⟩ : syracuseStep 1878629 = 352243) (by norm_num)
theorem B4221557 : Blo 1250443 4221557 := bbase (se 5 (by rfl) ⟨197885, by rfl⟩ : syracuseStep 4221557 = 395771) (by norm_num)
theorem B1878653 : Blo 1250443 1878653 := bbase (se 3 (by rfl) ⟨352247, by rfl⟩ : syracuseStep 1878653 = 704495) (by norm_num)
theorem B7129781 : Blo 1250443 7129781 := bbase (se 5 (by rfl) ⟨334208, by rfl⟩ : syracuseStep 7129781 = 668417) (by norm_num)
theorem B1583813 : Blo 1250443 1583813 := bbase (se 4 (by rfl) ⟨148482, by rfl⟩ : syracuseStep 1583813 = 296965) (by norm_num)
theorem B7219925 : Blo 1250443 7219925 := bbase (se 7 (by rfl) ⟨84608, by rfl⟩ : syracuseStep 7219925 = 169217) (by norm_num)
theorem B1583869 : Blo 1250443 1583869 := bbase (se 3 (by rfl) ⟨296975, by rfl⟩ : syracuseStep 1583869 = 593951) (by norm_num)
theorem B3566405 : Blo 1250443 3566405 := bbase (se 4 (by rfl) ⟨334350, by rfl⟩ : syracuseStep 3566405 = 668701) (by norm_num)
theorem B1583965 : Blo 1250443 1583965 := bbase (se 3 (by rfl) ⟨296993, by rfl⟩ : syracuseStep 1583965 = 593987) (by norm_num)
theorem B6335333 : Blo 1250443 6335333 := bbase (se 4 (by rfl) ⟨593937, by rfl⟩ : syracuseStep 6335333 = 1187875) (by norm_num)
theorem B2673557 : Blo 1250443 2673557 := bbase (se 6 (by rfl) ⟨62661, by rfl⟩ : syracuseStep 2673557 = 125323) (by norm_num)
theorem B1584137 : Blo 1250443 1584137 := bbase (se 2 (by rfl) ⟨594051, by rfl⟩ : syracuseStep 1584137 = 1188103) (by norm_num)
theorem B2853901 : Blo 1250443 2853901 := bbase (se 3 (by rfl) ⟨535106, by rfl⟩ : syracuseStep 2853901 = 1070213) (by norm_num)
theorem B4516901 : Blo 1250443 4516901 := bbase (se 4 (by rfl) ⟨423459, by rfl⟩ : syracuseStep 4516901 = 846919) (by norm_num)
theorem B4221989 : Blo 1250443 4221989 := bbase (se 4 (by rfl) ⟨395811, by rfl⟩ : syracuseStep 4221989 = 791623) (by norm_num)
theorem B1584193 : Blo 1250443 1584193 := bbase (se 2 (by rfl) ⟨594072, by rfl⟩ : syracuseStep 1584193 = 1188145) (by norm_num)
theorem B1780805 : Blo 1250443 1780805 := bbase (se 4 (by rfl) ⟨166950, by rfl⟩ : syracuseStep 1780805 = 333901) (by norm_num)
theorem B3165277 : Blo 1250443 3165277 := bbase (se 3 (by rfl) ⟨593489, by rfl⟩ : syracuseStep 3165277 = 1186979) (by norm_num)
theorem B1502329 : Blo 1250443 1502329 := bbase (se 2 (by rfl) ⟨563373, by rfl⟩ : syracuseStep 1502329 = 1126747) (by norm_num)
theorem B2673805 : Blo 1250443 2673805 := bbase (se 3 (by rfl) ⟨501338, by rfl⟩ : syracuseStep 2673805 = 1002677) (by norm_num)
theorem B1584289 : Blo 1250443 1584289 := bbase (se 2 (by rfl) ⟨594108, by rfl⟩ : syracuseStep 1584289 = 1188217) (by norm_num)
theorem B3165389 : Blo 1250443 3165389 := bbase (se 3 (by rfl) ⟨593510, by rfl⟩ : syracuseStep 3165389 = 1187021) (by norm_num)
theorem B4754645 : Blo 1250443 4754645 := bbase (se 7 (by rfl) ⟨55718, by rfl⟩ : syracuseStep 4754645 = 111437) (by norm_num)
theorem B1502425 : Blo 1250443 1502425 := bbase (se 2 (by rfl) ⟨563409, by rfl⟩ : syracuseStep 1502425 = 1126819) (by norm_num)
theorem B16043285 : Blo 1250443 16043285 := bbase (se 6 (by rfl) ⟨376014, by rfl⟩ : syracuseStep 16043285 = 752029) (by norm_num)
theorem B5705029 : Blo 1250443 5705029 := bbase (se 4 (by rfl) ⟨534846, by rfl⟩ : syracuseStep 5705029 = 1069693) (by norm_num)
theorem B2895173 : Blo 1250443 2895173 := bbase (se 4 (by rfl) ⟨271422, by rfl⟩ : syracuseStep 2895173 = 542845) (by norm_num)
theorem B1584461 : Blo 1250443 1584461 := bbase (se 3 (by rfl) ⟨297086, by rfl⟩ : syracuseStep 1584461 = 594173) (by norm_num)
theorem B7605589 : Blo 1250443 7605589 := bbase (se 11 (by rfl) ⟨5570, by rfl⟩ : syracuseStep 7605589 = 11141) (by norm_num)
theorem B1584517 : Blo 1250443 1584517 := bbase (se 4 (by rfl) ⟨148548, by rfl⟩ : syracuseStep 1584517 = 297097) (by norm_num)
theorem B3165581 : Blo 1250443 3165581 := bbase (se 3 (by rfl) ⟨593546, by rfl⟩ : syracuseStep 3165581 = 1187093) (by norm_num)
theorem B4222421 : Blo 1250443 4222421 := bbase (se 7 (by rfl) ⟨49481, by rfl⟩ : syracuseStep 4222421 = 98963) (by norm_num)
theorem B1584613 : Blo 1250443 1584613 := bbase (se 4 (by rfl) ⟨148557, by rfl⟩ : syracuseStep 1584613 = 297115) (by norm_num)
theorem B4754933 : Blo 1250443 4754933 := bbase (se 5 (by rfl) ⟨222887, by rfl⟩ : syracuseStep 4754933 = 445775) (by norm_num)
theorem B1502713 : Blo 1250443 1502713 := bbase (se 2 (by rfl) ⟨563517, by rfl⟩ : syracuseStep 1502713 = 1127035) (by norm_num)
theorem B2813525 : Blo 1250443 2813525 := bbase (se 8 (by rfl) ⟨16485, by rfl⟩ : syracuseStep 2813525 = 32971) (by norm_num)
theorem B1781357 : Blo 1250443 1781357 := bbase (se 3 (by rfl) ⟨334004, by rfl⟩ : syracuseStep 1781357 = 668009) (by norm_num)
theorem B2674309 : Blo 1250443 2674309 := bbase (se 4 (by rfl) ⟨250716, by rfl⟩ : syracuseStep 2674309 = 501433) (by norm_num)
theorem B1584785 : Blo 1250443 1584785 := bbase (se 2 (by rfl) ⟨594294, by rfl⟩ : syracuseStep 1584785 = 1188589) (by norm_num)
theorem B2813597 : Blo 1250443 2813597 := bbase (se 3 (by rfl) ⟨527549, by rfl⟩ : syracuseStep 2813597 = 1055099) (by norm_num)
theorem B1805981 : Blo 1250443 1805981 := bbase (se 3 (by rfl) ⟨338621, by rfl⟩ : syracuseStep 1805981 = 677243) (by norm_num)
theorem B1502905 : Blo 1250443 1502905 := bbase (se 2 (by rfl) ⟨563589, by rfl⟩ : syracuseStep 1502905 = 1127179) (by norm_num)
theorem B1584841 : Blo 1250443 1584841 := bbase (se 2 (by rfl) ⟨594315, by rfl⟩ : syracuseStep 1584841 = 1188631) (by norm_num)
theorem B2813669 : Blo 1250443 2813669 := bbase (se 4 (by rfl) ⟨263781, by rfl⟩ : syracuseStep 2813669 = 527563) (by norm_num)
theorem B3165925 : Blo 1250443 3165925 := bbase (se 4 (by rfl) ⟨296805, by rfl⟩ : syracuseStep 3165925 = 593611) (by norm_num)
theorem B1584937 : Blo 1250443 1584937 := bbase (se 2 (by rfl) ⟨594351, by rfl⟩ : syracuseStep 1584937 = 1188703) (by norm_num)
theorem B2813741 : Blo 1250443 2813741 := bbase (se 3 (by rfl) ⟨527576, by rfl⟩ : syracuseStep 2813741 = 1055153) (by norm_num)
theorem B5074757 : Blo 1250443 5074757 := bbase (se 4 (by rfl) ⟨475758, by rfl⟩ : syracuseStep 5074757 = 951517) (by norm_num)
theorem B3166037 : Blo 1250443 3166037 := bbase (se 9 (by rfl) ⟨9275, by rfl⟩ : syracuseStep 3166037 = 18551) (by norm_num)
theorem B9506645 : Blo 1250443 9506645 := bbase (se 9 (by rfl) ⟨27851, by rfl⟩ : syracuseStep 9506645 = 55703) (by norm_num)
theorem B2813813 : Blo 1250443 2813813 := bbase (se 5 (by rfl) ⟨131897, by rfl⟩ : syracuseStep 2813813 = 263795) (by norm_num)
theorem B4222853 : Blo 1250443 4222853 := bbase (se 4 (by rfl) ⟨395892, by rfl⟩ : syracuseStep 4222853 = 791785) (by norm_num)
theorem B1691525 : Blo 1250443 1691525 := bbase (se 4 (by rfl) ⟨158580, by rfl⟩ : syracuseStep 1691525 = 317161) (by norm_num)
theorem B1806229 : Blo 1250443 1806229 := bbase (se 6 (by rfl) ⟨42333, by rfl⟩ : syracuseStep 1806229 = 84667) (by norm_num)
theorem B2813885 : Blo 1250443 2813885 := bbase (se 3 (by rfl) ⟨527603, by rfl⟩ : syracuseStep 2813885 = 1055207) (by norm_num)
theorem B4009925 : Blo 1250443 4009925 := bbase (se 4 (by rfl) ⟨375930, by rfl⟩ : syracuseStep 4009925 = 751861) (by norm_num)
theorem B1585109 : Blo 1250443 1585109 := bbase (se 7 (by rfl) ⟨18575, by rfl⟩ : syracuseStep 1585109 = 37151) (by norm_num)
theorem B2813957 : Blo 1250443 2813957 := bbase (se 4 (by rfl) ⟨263808, by rfl⟩ : syracuseStep 2813957 = 527617) (by norm_num)
theorem B3166229 : Blo 1250443 3166229 := bbase (se 6 (by rfl) ⟨74208, by rfl⟩ : syracuseStep 3166229 = 148417) (by norm_num)
theorem B2814029 : Blo 1250443 2814029 := bbase (se 3 (by rfl) ⟨527630, by rfl⟩ : syracuseStep 2814029 = 1055261) (by norm_num)
theorem B2854997 : Blo 1250443 2854997 := bbase (se 8 (by rfl) ⟨16728, by rfl⟩ : syracuseStep 2854997 = 33457) (by norm_num)
theorem B2003053 : Blo 1250443 2003053 := bbase (se 3 (by rfl) ⟨375572, by rfl⟩ : syracuseStep 2003053 = 751145) (by norm_num)
theorem B6336629 : Blo 1250443 6336629 := bbase (se 5 (by rfl) ⟨297029, by rfl⟩ : syracuseStep 6336629 = 594059) (by norm_num)
theorem B2814101 : Blo 1250443 2814101 := bbase (se 6 (by rfl) ⟨65955, by rfl⟩ : syracuseStep 2814101 = 131911) (by norm_num)
theorem B2855069 : Blo 1250443 2855069 := bbase (se 3 (by rfl) ⟨535325, by rfl⟩ : syracuseStep 2855069 = 1070651) (by norm_num)
theorem B2814173 : Blo 1250443 2814173 := bbase (se 3 (by rfl) ⟨527657, by rfl⟩ : syracuseStep 2814173 = 1055315) (by norm_num)
theorem B9498869 : Blo 1250443 9498869 := bbase (se 5 (by rfl) ⟨445259, by rfl⟩ : syracuseStep 9498869 = 890519) (by norm_num)
theorem B8024309 : Blo 1250443 8024309 := bbase (se 5 (by rfl) ⟨376139, by rfl⟩ : syracuseStep 8024309 = 752279) (by norm_num)
theorem B2814245 : Blo 1250443 2814245 := bbase (se 4 (by rfl) ⟨263835, by rfl⟩ : syracuseStep 2814245 = 527671) (by norm_num)
theorem B4223285 : Blo 1250443 4223285 := bbase (se 5 (by rfl) ⟨197966, by rfl⟩ : syracuseStep 4223285 = 395933) (by norm_num)
theorem B1782109 : Blo 1250443 1782109 := bbase (se 3 (by rfl) ⟨334145, by rfl⟩ : syracuseStep 1782109 = 668291) (by norm_num)
theorem B2814317 : Blo 1250443 2814317 := bbase (se 3 (by rfl) ⟨527684, by rfl⟩ : syracuseStep 2814317 = 1055369) (by norm_num)
theorem B3166573 : Blo 1250443 3166573 := bbase (se 3 (by rfl) ⟨593732, by rfl⟩ : syracuseStep 3166573 = 1187465) (by norm_num)
theorem B2814389 : Blo 1250443 2814389 := bbase (se 5 (by rfl) ⟨131924, by rfl⟩ : syracuseStep 2814389 = 263849) (by norm_num)
theorem B5706197 : Blo 1250443 5706197 := bbase (se 7 (by rfl) ⟨66869, by rfl⟩ : syracuseStep 5706197 = 133739) (by norm_num)
theorem B3166685 : Blo 1250443 3166685 := bbase (se 3 (by rfl) ⟨593753, by rfl⟩ : syracuseStep 3166685 = 1187507) (by norm_num)
theorem B2814461 : Blo 1250443 2814461 := bbase (se 3 (by rfl) ⟨527711, by rfl⟩ : syracuseStep 2814461 = 1055423) (by norm_num)
theorem B1503785 : Blo 1250443 1503785 := bbase (se 2 (by rfl) ⟨563919, by rfl⟩ : syracuseStep 1503785 = 1127839) (by norm_num)
theorem B2814533 : Blo 1250443 2814533 := bbase (se 4 (by rfl) ⟨263862, by rfl⟩ : syracuseStep 2814533 = 527725) (by norm_num)
theorem B2814605 : Blo 1250443 2814605 := bbase (se 3 (by rfl) ⟨527738, by rfl⟩ : syracuseStep 2814605 = 1055477) (by norm_num)
theorem B3166877 : Blo 1250443 3166877 := bbase (se 3 (by rfl) ⟨593789, by rfl⟩ : syracuseStep 3166877 = 1187579) (by norm_num)
theorem B2814677 : Blo 1250443 2814677 := bbase (se 7 (by rfl) ⟨32984, by rfl⟩ : syracuseStep 2814677 = 65969) (by norm_num)
theorem B4223717 : Blo 1250443 4223717 := bbase (se 4 (by rfl) ⟨395973, by rfl⟩ : syracuseStep 4223717 = 791947) (by norm_num)
theorem B1807093 : Blo 1250443 1807093 := bbase (se 5 (by rfl) ⟨84707, by rfl⟩ : syracuseStep 1807093 = 169415) (by norm_num)
theorem B2110205 : Blo 1250443 2110205 := bbase (se 3 (by rfl) ⟨395663, by rfl⟩ : syracuseStep 2110205 = 791327) (by norm_num)
theorem B2814749 : Blo 1250443 2814749 := bbase (se 3 (by rfl) ⟨527765, by rfl⟩ : syracuseStep 2814749 = 1055531) (by norm_num)
theorem B2855717 : Blo 1250443 2855717 := bbase (se 4 (by rfl) ⟨267723, by rfl⟩ : syracuseStep 2855717 = 535447) (by norm_num)
theorem B7131989 : Blo 1250443 7131989 := bbase (se 9 (by rfl) ⟨20894, by rfl⟩ : syracuseStep 7131989 = 41789) (by norm_num)
theorem B2814821 : Blo 1250443 2814821 := bbase (se 4 (by rfl) ⟨263889, by rfl⟩ : syracuseStep 2814821 = 527779) (by norm_num)
theorem B2110333 : Blo 1250443 2110333 := bbase (se 3 (by rfl) ⟨395687, by rfl⟩ : syracuseStep 2110333 = 791375) (by norm_num)
theorem B2814893 : Blo 1250443 2814893 := bbase (se 3 (by rfl) ⟨527792, by rfl⟩ : syracuseStep 2814893 = 1055585) (by norm_num)
theorem B2110421 : Blo 1250443 2110421 := bbase (se 7 (by rfl) ⟨24731, by rfl⟩ : syracuseStep 2110421 = 49463) (by norm_num)
theorem B2814965 : Blo 1250443 2814965 := bbase (se 5 (by rfl) ⟨131951, by rfl⟩ : syracuseStep 2814965 = 263903) (by norm_num)
theorem B3167221 : Blo 1250443 3167221 := bbase (se 5 (by rfl) ⟨148463, by rfl⟩ : syracuseStep 3167221 = 296927) (by norm_num)
theorem B1504289 : Blo 1250443 1504289 := bbase (se 2 (by rfl) ⟨564108, by rfl⟩ : syracuseStep 1504289 = 1128217) (by norm_num)
theorem B2536493 : Blo 1250443 2536493 := bbase (se 3 (by rfl) ⟨475592, by rfl⟩ : syracuseStep 2536493 = 951185) (by norm_num)
theorem B4748341 : Blo 1250443 4748341 := bbase (se 5 (by rfl) ⟨222578, by rfl⟩ : syracuseStep 4748341 = 445157) (by norm_num)
theorem B2815037 : Blo 1250443 2815037 := bbase (se 3 (by rfl) ⟨527819, by rfl⟩ : syracuseStep 2815037 = 1055639) (by norm_num)
theorem B1504337 : Blo 1250443 1504337 := bbase (se 2 (by rfl) ⟨564126, by rfl⟩ : syracuseStep 1504337 = 1128253) (by norm_num)
theorem B2110549 : Blo 1250443 2110549 := bbase (se 8 (by rfl) ⟨12366, by rfl⟩ : syracuseStep 2110549 = 24733) (by norm_num)
theorem B3167333 : Blo 1250443 3167333 := bbase (se 4 (by rfl) ⟨296937, by rfl⟩ : syracuseStep 3167333 = 593875) (by norm_num)
theorem B10695797 : Blo 1250443 10695797 := bbase (se 5 (by rfl) ⟨501365, by rfl⟩ : syracuseStep 10695797 = 1002731) (by norm_num)
theorem B1782901 : Blo 1250443 1782901 := bbase (se 5 (by rfl) ⟨83573, by rfl⟩ : syracuseStep 1782901 = 167147) (by norm_num)
theorem B2815109 : Blo 1250443 2815109 := bbase (se 4 (by rfl) ⟨263916, by rfl⟩ : syracuseStep 2815109 = 527833) (by norm_num)
theorem B4224149 : Blo 1250443 4224149 := bbase (se 6 (by rfl) ⟨99003, by rfl⟩ : syracuseStep 4224149 = 198007) (by norm_num)
theorem B2110637 : Blo 1250443 2110637 := bbase (se 3 (by rfl) ⟨395744, by rfl⟩ : syracuseStep 2110637 = 791489) (by norm_num)
theorem B2815181 : Blo 1250443 2815181 := bbase (se 3 (by rfl) ⟨527846, by rfl⟩ : syracuseStep 2815181 = 1055693) (by norm_num)
theorem B4011221 : Blo 1250443 4011221 := bbase (se 7 (by rfl) ⟨47006, by rfl⟩ : syracuseStep 4011221 = 94013) (by norm_num)
theorem B10687733 : Blo 1250443 10687733 := bbase (se 5 (by rfl) ⟨500987, by rfl⟩ : syracuseStep 10687733 = 1001975) (by norm_num)
theorem B2815253 : Blo 1250443 2815253 := bbase (se 6 (by rfl) ⟨65982, by rfl⟩ : syracuseStep 2815253 = 131965) (by norm_num)
theorem B3167525 : Blo 1250443 3167525 := bbase (se 4 (by rfl) ⟨296955, by rfl⟩ : syracuseStep 3167525 = 593911) (by norm_num)
theorem B2110765 : Blo 1250443 2110765 := bbase (se 3 (by rfl) ⟨395768, by rfl⟩ : syracuseStep 2110765 = 791537) (by norm_num)
theorem B5862709 : Blo 1250443 5862709 := bbase (se 5 (by rfl) ⟨274814, by rfl⟩ : syracuseStep 5862709 = 549629) (by norm_num)
theorem B1504597 : Blo 1250443 1504597 := bbase (se 13 (by rfl) ⟨275, by rfl⟩ : syracuseStep 1504597 = 551) (by norm_num)
theorem B2815325 : Blo 1250443 2815325 := bbase (se 3 (by rfl) ⟨527873, by rfl⟩ : syracuseStep 2815325 = 1055747) (by norm_num)
theorem B4748645 : Blo 1250443 4748645 := bbase (se 4 (by rfl) ⟨445185, by rfl⟩ : syracuseStep 4748645 = 890371) (by norm_num)
theorem B2110853 : Blo 1250443 2110853 := bbase (se 4 (by rfl) ⟨197892, by rfl⟩ : syracuseStep 2110853 = 395785) (by norm_num)
theorem B6337925 : Blo 1250443 6337925 := bbase (se 4 (by rfl) ⟨594180, by rfl⟩ : syracuseStep 6337925 = 1188361) (by norm_num)
theorem B2815397 : Blo 1250443 2815397 := bbase (se 4 (by rfl) ⟨263943, by rfl⟩ : syracuseStep 2815397 = 527887) (by norm_num)
theorem B1447345 : Blo 1250443 1447345 := bbase (se 2 (by rfl) ⟨542754, by rfl⟩ : syracuseStep 1447345 = 1085509) (by norm_num)
theorem B1783237 : Blo 1250443 1783237 := bbase (se 4 (by rfl) ⟨167178, by rfl⟩ : syracuseStep 1783237 = 334357) (by norm_num)
theorem B2004437 : Blo 1250443 2004437 := bbase (se 7 (by rfl) ⟨23489, by rfl⟩ : syracuseStep 2004437 = 46979) (by norm_num)
theorem B2815469 : Blo 1250443 2815469 := bbase (se 3 (by rfl) ⟨527900, by rfl⟩ : syracuseStep 2815469 = 1055801) (by norm_num)
theorem B5346805 : Blo 1250443 5346805 := bbase (se 5 (by rfl) ⟨250631, by rfl⟩ : syracuseStep 5346805 = 501263) (by norm_num)
theorem B2110981 : Blo 1250443 2110981 := bbase (se 4 (by rfl) ⟨197904, by rfl⟩ : syracuseStep 2110981 = 395809) (by norm_num)
theorem B2815541 : Blo 1250443 2815541 := bbase (se 5 (by rfl) ⟨131978, by rfl⟩ : syracuseStep 2815541 = 263957) (by norm_num)
theorem B3561029 : Blo 1250443 3561029 := bbase (se 4 (by rfl) ⟨333846, by rfl⟩ : syracuseStep 3561029 = 667693) (by norm_num)
theorem B4224581 : Blo 1250443 4224581 := bbase (se 4 (by rfl) ⟨396054, by rfl⟩ : syracuseStep 4224581 = 792109) (by norm_num)
theorem B2111069 : Blo 1250443 2111069 := bbase (se 3 (by rfl) ⟨395825, by rfl⟩ : syracuseStep 2111069 = 791651) (by norm_num)
theorem B6010469 : Blo 1250443 6010469 := bbase (se 4 (by rfl) ⟨563481, by rfl⟩ : syracuseStep 6010469 = 1126963) (by norm_num)
theorem B2815613 : Blo 1250443 2815613 := bbase (se 3 (by rfl) ⟨527927, by rfl⟩ : syracuseStep 2815613 = 1055855) (by norm_num)
theorem B3167869 : Blo 1250443 3167869 := bbase (se 3 (by rfl) ⟨593975, by rfl⟩ : syracuseStep 3167869 = 1187951) (by norm_num)
theorem B2537125 : Blo 1250443 2537125 := bbase (se 4 (by rfl) ⟨237855, by rfl⟩ : syracuseStep 2537125 = 475711) (by norm_num)
theorem B2815685 : Blo 1250443 2815685 := bbase (se 4 (by rfl) ⟨263970, by rfl⟩ : syracuseStep 2815685 = 527941) (by norm_num)
theorem B2111197 : Blo 1250443 2111197 := bbase (se 3 (by rfl) ⟨395849, by rfl⟩ : syracuseStep 2111197 = 791699) (by norm_num)
theorem B3167981 : Blo 1250443 3167981 := bbase (se 3 (by rfl) ⟨593996, by rfl⟩ : syracuseStep 3167981 = 1187993) (by norm_num)
theorem B2815757 : Blo 1250443 2815757 := bbase (se 3 (by rfl) ⟨527954, by rfl⟩ : syracuseStep 2815757 = 1055909) (by norm_num)
theorem B1406749 : Blo 1250443 1406749 := bbase (se 3 (by rfl) ⟨263765, by rfl⟩ : syracuseStep 1406749 = 527531) (by norm_num)
theorem B2111285 : Blo 1250443 2111285 := bbase (se 5 (by rfl) ⟨98966, by rfl⟩ : syracuseStep 2111285 = 197933) (by norm_num)
theorem B1406785 : Blo 1250443 1406785 := bbase (se 2 (by rfl) ⟨527544, by rfl⟩ : syracuseStep 1406785 = 1055089) (by norm_num)
theorem B1267525 : Blo 1250443 1267525 := bbase (se 4 (by rfl) ⟨118830, by rfl⟩ : syracuseStep 1267525 = 237661) (by norm_num)
theorem B2815829 : Blo 1250443 2815829 := bbase (se 9 (by rfl) ⟨8249, by rfl⟩ : syracuseStep 2815829 = 16499) (by norm_num)
theorem B1406821 : Blo 1250443 1406821 := bbase (se 4 (by rfl) ⟨131889, by rfl⟩ : syracuseStep 1406821 = 263779) (by norm_num)
theorem B1406857 : Blo 1250443 1406857 := bbase (se 2 (by rfl) ⟨527571, by rfl⟩ : syracuseStep 1406857 = 1055143) (by norm_num)
theorem B16267157 : Blo 1250443 16267157 := bbase (se 6 (by rfl) ⟨381261, by rfl⟩ : syracuseStep 16267157 = 762523) (by norm_num)
theorem B2815901 : Blo 1250443 2815901 := bbase (se 3 (by rfl) ⟨527981, by rfl⟩ : syracuseStep 2815901 = 1055963) (by norm_num)
theorem B1406893 : Blo 1250443 1406893 := bbase (se 3 (by rfl) ⟨263792, by rfl⟩ : syracuseStep 1406893 = 527585) (by norm_num)
theorem B3168173 : Blo 1250443 3168173 := bbase (se 3 (by rfl) ⟨594032, by rfl⟩ : syracuseStep 3168173 = 1188065) (by norm_num)
theorem B2111413 : Blo 1250443 2111413 := bbase (se 5 (by rfl) ⟨98972, by rfl⟩ : syracuseStep 2111413 = 197945) (by norm_num)
theorem B1406929 : Blo 1250443 1406929 := bbase (se 2 (by rfl) ⟨527598, by rfl⟩ : syracuseStep 1406929 = 1055197) (by norm_num)
theorem B2815973 : Blo 1250443 2815973 := bbase (se 4 (by rfl) ⟨263997, by rfl⟩ : syracuseStep 2815973 = 527995) (by norm_num)
theorem B1406965 : Blo 1250443 1406965 := bbase (se 5 (by rfl) ⟨65951, by rfl⟩ : syracuseStep 1406965 = 131903) (by norm_num)
theorem B4225013 : Blo 1250443 4225013 := bbase (se 5 (by rfl) ⟨198047, by rfl⟩ : syracuseStep 4225013 = 396095) (by norm_num)
theorem B2111501 : Blo 1250443 2111501 := bbase (se 3 (by rfl) ⟨395906, by rfl⟩ : syracuseStep 2111501 = 791813) (by norm_num)
theorem B1407001 : Blo 1250443 1407001 := bbase (se 2 (by rfl) ⟨527625, by rfl⟩ : syracuseStep 1407001 = 1055251) (by norm_num)
theorem B2816045 : Blo 1250443 2816045 := bbase (se 3 (by rfl) ⟨528008, by rfl⟩ : syracuseStep 2816045 = 1056017) (by norm_num)
theorem B1407037 : Blo 1250443 1407037 := bbase (se 3 (by rfl) ⟨263819, by rfl⟩ : syracuseStep 1407037 = 527639) (by norm_num)
theorem B1407073 : Blo 1250443 1407073 := bbase (se 2 (by rfl) ⟨527652, by rfl⟩ : syracuseStep 1407073 = 1055305) (by norm_num)
theorem B2537581 : Blo 1250443 2537581 := bbase (se 3 (by rfl) ⟨475796, by rfl⟩ : syracuseStep 2537581 = 951593) (by norm_num)
theorem B2816117 : Blo 1250443 2816117 := bbase (se 5 (by rfl) ⟨132005, by rfl⟩ : syracuseStep 2816117 = 264011) (by norm_num)
theorem B1407109 : Blo 1250443 1407109 := bbase (se 4 (by rfl) ⟨131916, by rfl⟩ : syracuseStep 1407109 = 263833) (by norm_num)
theorem B2111629 : Blo 1250443 2111629 := bbase (se 3 (by rfl) ⟨395930, by rfl⟩ : syracuseStep 2111629 = 791861) (by norm_num)
theorem B1407145 : Blo 1250443 1407145 := bbase (se 2 (by rfl) ⟨527679, by rfl⟩ : syracuseStep 1407145 = 1055359) (by norm_num)
theorem B2816189 : Blo 1250443 2816189 := bbase (se 3 (by rfl) ⟨528035, by rfl⟩ : syracuseStep 2816189 = 1056071) (by norm_num)
theorem B1407181 : Blo 1250443 1407181 := bbase (se 3 (by rfl) ⟨263846, by rfl⟩ : syracuseStep 1407181 = 527693) (by norm_num)
theorem B2111717 : Blo 1250443 2111717 := bbase (se 4 (by rfl) ⟨197973, by rfl⟩ : syracuseStep 2111717 = 395947) (by norm_num)
theorem B1407217 : Blo 1250443 1407217 := bbase (se 2 (by rfl) ⟨527706, by rfl⟩ : syracuseStep 1407217 = 1055413) (by norm_num)
theorem B2816261 : Blo 1250443 2816261 := bbase (se 4 (by rfl) ⟨264024, by rfl⟩ : syracuseStep 2816261 = 528049) (by norm_num)
theorem B3168517 : Blo 1250443 3168517 := bbase (se 4 (by rfl) ⟨297048, by rfl⟩ : syracuseStep 3168517 = 594097) (by norm_num)
theorem B1407253 : Blo 1250443 1407253 := bbase (se 6 (by rfl) ⟨32982, by rfl⟩ : syracuseStep 1407253 = 65965) (by norm_num)
theorem B1407289 : Blo 1250443 1407289 := bbase (se 2 (by rfl) ⟨527733, by rfl⟩ : syracuseStep 1407289 = 1055467) (by norm_num)
theorem B3004733 : Blo 1250443 3004733 := bbase (se 3 (by rfl) ⟨563387, by rfl⟩ : syracuseStep 3004733 = 1126775) (by norm_num)
theorem B2816333 : Blo 1250443 2816333 := bbase (se 3 (by rfl) ⟨528062, by rfl⟩ : syracuseStep 2816333 = 1056125) (by norm_num)
theorem B8018261 : Blo 1250443 8018261 := bbase (se 10 (by rfl) ⟨11745, by rfl⟩ : syracuseStep 8018261 = 23491) (by norm_num)
theorem B1407325 : Blo 1250443 1407325 := bbase (se 3 (by rfl) ⟨263873, by rfl⟩ : syracuseStep 1407325 = 527747) (by norm_num)
theorem B2111845 : Blo 1250443 2111845 := bbase (se 4 (by rfl) ⟨197985, by rfl⟩ : syracuseStep 2111845 = 395971) (by norm_num)
theorem B3168629 : Blo 1250443 3168629 := bbase (se 5 (by rfl) ⟨148529, by rfl⟩ : syracuseStep 3168629 = 297059) (by norm_num)
theorem B1268093 : Blo 1250443 1268093 := bbase (se 3 (by rfl) ⟨237767, by rfl⟩ : syracuseStep 1268093 = 475535) (by norm_num)
theorem B2005373 : Blo 1250443 2005373 := bbase (se 3 (by rfl) ⟨376007, by rfl⟩ : syracuseStep 2005373 = 752015) (by norm_num)
theorem B1407361 : Blo 1250443 1407361 := bbase (se 2 (by rfl) ⟨527760, by rfl⟩ : syracuseStep 1407361 = 1055521) (by norm_num)
theorem B2816405 : Blo 1250443 2816405 := bbase (se 6 (by rfl) ⟨66009, by rfl⟩ : syracuseStep 2816405 = 132019) (by norm_num)
theorem B1407397 : Blo 1250443 1407397 := bbase (se 4 (by rfl) ⟨131943, by rfl⟩ : syracuseStep 1407397 = 263887) (by norm_num)
theorem B4225445 : Blo 1250443 4225445 := bbase (se 4 (by rfl) ⟨396135, by rfl⟩ : syracuseStep 4225445 = 792271) (by norm_num)
theorem B2111933 : Blo 1250443 2111933 := bbase (se 3 (by rfl) ⟨395987, by rfl⟩ : syracuseStep 2111933 = 791975) (by norm_num)
theorem B1407433 : Blo 1250443 1407433 := bbase (se 2 (by rfl) ⟨527787, by rfl⟩ : syracuseStep 1407433 = 1055575) (by norm_num)
theorem B2816477 : Blo 1250443 2816477 := bbase (se 3 (by rfl) ⟨528089, by rfl⟩ : syracuseStep 2816477 = 1056179) (by norm_num)
theorem B1407469 : Blo 1250443 1407469 := bbase (se 3 (by rfl) ⟨263900, by rfl⟩ : syracuseStep 1407469 = 527801) (by norm_num)
theorem B1407505 : Blo 1250443 1407505 := bbase (se 2 (by rfl) ⟨527814, by rfl⟩ : syracuseStep 1407505 = 1055629) (by norm_num)
theorem B4512277 : Blo 1250443 4512277 := bbase (se 6 (by rfl) ⟨105756, by rfl⟩ : syracuseStep 4512277 = 211513) (by norm_num)
theorem B2816549 : Blo 1250443 2816549 := bbase (se 4 (by rfl) ⟨264051, by rfl⟩ : syracuseStep 2816549 = 528103) (by norm_num)
theorem B1407541 : Blo 1250443 1407541 := bbase (se 5 (by rfl) ⟨65978, by rfl⟩ : syracuseStep 1407541 = 131957) (by norm_num)
theorem B3168821 : Blo 1250443 3168821 := bbase (se 5 (by rfl) ⟨148538, by rfl⟩ : syracuseStep 3168821 = 297077) (by norm_num)
theorem B2112061 : Blo 1250443 2112061 := bbase (se 3 (by rfl) ⟨396011, by rfl⟩ : syracuseStep 2112061 = 792023) (by norm_num)
theorem B1407577 : Blo 1250443 1407577 := bbase (se 2 (by rfl) ⟨527841, by rfl⟩ : syracuseStep 1407577 = 1055683) (by norm_num)
theorem B2816621 : Blo 1250443 2816621 := bbase (se 3 (by rfl) ⟨528116, by rfl⟩ : syracuseStep 2816621 = 1056233) (by norm_num)
theorem B1407613 : Blo 1250443 1407613 := bbase (se 3 (by rfl) ⟨263927, by rfl⟩ : syracuseStep 1407613 = 527855) (by norm_num)
theorem B2374285 : Blo 1250443 2374285 := bbase (se 3 (by rfl) ⟨445178, by rfl⟩ : syracuseStep 2374285 = 890357) (by norm_num)
theorem B2112149 : Blo 1250443 2112149 := bbase (se 6 (by rfl) ⟨49503, by rfl⟩ : syracuseStep 2112149 = 99007) (by norm_num)
theorem B6339221 : Blo 1250443 6339221 := bbase (se 6 (by rfl) ⟨148575, by rfl⟩ : syracuseStep 6339221 = 297151) (by norm_num)
theorem B1407649 : Blo 1250443 1407649 := bbase (se 2 (by rfl) ⟨527868, by rfl⟩ : syracuseStep 1407649 = 1055737) (by norm_num)
theorem B2816693 : Blo 1250443 2816693 := bbase (se 5 (by rfl) ⟨132032, by rfl⟩ : syracuseStep 2816693 = 264065) (by norm_num)
theorem B1407685 : Blo 1250443 1407685 := bbase (se 4 (by rfl) ⟨131970, by rfl⟩ : syracuseStep 1407685 = 263941) (by norm_num)
theorem B3562213 : Blo 1250443 3562213 := bbase (se 4 (by rfl) ⟨333957, by rfl⟩ : syracuseStep 3562213 = 667915) (by norm_num)
theorem B1407721 : Blo 1250443 1407721 := bbase (se 2 (by rfl) ⟨527895, by rfl⟩ : syracuseStep 1407721 = 1055791) (by norm_num)
theorem B2538229 : Blo 1250443 2538229 := bbase (se 5 (by rfl) ⟨118979, by rfl⟩ : syracuseStep 2538229 = 237959) (by norm_num)
theorem B2816765 : Blo 1250443 2816765 := bbase (se 3 (by rfl) ⟨528143, by rfl⟩ : syracuseStep 2816765 = 1056287) (by norm_num)
theorem B1407757 : Blo 1250443 1407757 := bbase (se 3 (by rfl) ⟨263954, by rfl⟩ : syracuseStep 1407757 = 527909) (by norm_num)
theorem B2112277 : Blo 1250443 2112277 := bbase (se 6 (by rfl) ⟨49506, by rfl⟩ : syracuseStep 2112277 = 99013) (by norm_num)
theorem B2374429 : Blo 1250443 2374429 := bbase (se 3 (by rfl) ⟨445205, by rfl⟩ : syracuseStep 2374429 = 890411) (by norm_num)
theorem B1407793 : Blo 1250443 1407793 := bbase (se 2 (by rfl) ⟨527922, by rfl⟩ : syracuseStep 1407793 = 1055845) (by norm_num)
theorem B2816837 : Blo 1250443 2816837 := bbase (se 4 (by rfl) ⟨264078, by rfl⟩ : syracuseStep 2816837 = 528157) (by norm_num)
theorem B1407829 : Blo 1250443 1407829 := bbase (se 9 (by rfl) ⟨4124, by rfl⟩ : syracuseStep 1407829 = 8249) (by norm_num)
theorem B4225877 : Blo 1250443 4225877 := bbase (se 9 (by rfl) ⟨12380, by rfl⟩ : syracuseStep 4225877 = 24761) (by norm_num)
theorem B2112365 : Blo 1250443 2112365 := bbase (se 3 (by rfl) ⟨396068, by rfl⟩ : syracuseStep 2112365 = 792137) (by norm_num)
theorem B1407865 : Blo 1250443 1407865 := bbase (se 2 (by rfl) ⟨527949, by rfl⟩ : syracuseStep 1407865 = 1055899) (by norm_num)
theorem B3562373 : Blo 1250443 3562373 := bbase (se 4 (by rfl) ⟨333972, by rfl⟩ : syracuseStep 3562373 = 667945) (by norm_num)
theorem B2816909 : Blo 1250443 2816909 := bbase (se 3 (by rfl) ⟨528170, by rfl⟩ : syracuseStep 2816909 = 1056341) (by norm_num)
theorem B3169165 : Blo 1250443 3169165 := bbase (se 3 (by rfl) ⟨594218, by rfl⟩ : syracuseStep 3169165 = 1188437) (by norm_num)
theorem B1465237 : Blo 1250443 1465237 := bbase (se 6 (by rfl) ⟨34341, by rfl⟩ : syracuseStep 1465237 = 68683) (by norm_num)
theorem B3382165 : Blo 1250443 3382165 := bbase (se 6 (by rfl) ⟨79269, by rfl⟩ : syracuseStep 3382165 = 158539) (by norm_num)
theorem B1407901 : Blo 1250443 1407901 := bbase (se 3 (by rfl) ⟨263981, by rfl⟩ : syracuseStep 1407901 = 527963) (by norm_num)
theorem B6011813 : Blo 1250443 6011813 := bbase (se 4 (by rfl) ⟨563607, by rfl⟩ : syracuseStep 6011813 = 1127215) (by norm_num)
theorem B3611557 : Blo 1250443 3611557 := bbase (se 4 (by rfl) ⟨338583, by rfl⟩ : syracuseStep 3611557 = 677167) (by norm_num)
theorem B4283317 : Blo 1250443 4283317 := bbase (se 5 (by rfl) ⟨200780, by rfl⟩ : syracuseStep 4283317 = 401561) (by norm_num)
theorem B2374589 : Blo 1250443 2374589 := bbase (se 3 (by rfl) ⟨445235, by rfl⟩ : syracuseStep 2374589 = 890471) (by norm_num)
theorem B1407937 : Blo 1250443 1407937 := bbase (se 2 (by rfl) ⟨527976, by rfl⟩ : syracuseStep 1407937 = 1055953) (by norm_num)
theorem B3382229 : Blo 1250443 3382229 := bbase (se 7 (by rfl) ⟨39635, by rfl⟩ : syracuseStep 3382229 = 79271) (by norm_num)
theorem B2816981 : Blo 1250443 2816981 := bbase (se 7 (by rfl) ⟨33011, by rfl⟩ : syracuseStep 2816981 = 66023) (by norm_num)
theorem B1407973 : Blo 1250443 1407973 := bbase (se 4 (by rfl) ⟨131997, by rfl⟩ : syracuseStep 1407973 = 263995) (by norm_num)
theorem B2112493 : Blo 1250443 2112493 := bbase (se 3 (by rfl) ⟨396092, by rfl⟩ : syracuseStep 2112493 = 792185) (by norm_num)
theorem B3169277 : Blo 1250443 3169277 := bbase (se 3 (by rfl) ⟨594239, by rfl⟩ : syracuseStep 3169277 = 1188479) (by norm_num)
theorem B2006021 : Blo 1250443 2006021 := bbase (se 4 (by rfl) ⟨188064, by rfl⟩ : syracuseStep 2006021 = 376129) (by norm_num)
theorem B1408009 : Blo 1250443 1408009 := bbase (se 2 (by rfl) ⟨528003, by rfl⟩ : syracuseStep 1408009 = 1056007) (by norm_num)
theorem B2817053 : Blo 1250443 2817053 := bbase (se 3 (by rfl) ⟨528197, by rfl⟩ : syracuseStep 2817053 = 1056395) (by norm_num)
theorem B1408045 : Blo 1250443 1408045 := bbase (se 3 (by rfl) ⟨264008, by rfl⟩ : syracuseStep 1408045 = 528017) (by norm_num)
theorem B6331445 : Blo 1250443 6331445 := bbase (se 5 (by rfl) ⟨296786, by rfl⟩ : syracuseStep 6331445 = 593573) (by norm_num)
theorem B2112581 : Blo 1250443 2112581 := bbase (se 4 (by rfl) ⟨198054, by rfl⟩ : syracuseStep 2112581 = 396109) (by norm_num)
theorem B2374733 : Blo 1250443 2374733 := bbase (se 3 (by rfl) ⟨445262, by rfl⟩ : syracuseStep 2374733 = 890525) (by norm_num)
theorem B1408081 : Blo 1250443 1408081 := bbase (se 2 (by rfl) ⟨528030, by rfl⟩ : syracuseStep 1408081 = 1056061) (by norm_num)
theorem B2817125 : Blo 1250443 2817125 := bbase (se 4 (by rfl) ⟨264105, by rfl⟩ : syracuseStep 2817125 = 528211) (by norm_num)
theorem B3562613 : Blo 1250443 3562613 := bbase (se 5 (by rfl) ⟨166997, by rfl⟩ : syracuseStep 3562613 = 333995) (by norm_num)
theorem B2407541 : Blo 1250443 2407541 := bbase (se 5 (by rfl) ⟨112853, by rfl⟩ : syracuseStep 2407541 = 225707) (by norm_num)
theorem B1408117 : Blo 1250443 1408117 := bbase (se 5 (by rfl) ⟨66005, by rfl⟩ : syracuseStep 1408117 = 132011) (by norm_num)
theorem B2784397 : Blo 1250443 2784397 := bbase (se 3 (by rfl) ⟨522074, by rfl⟩ : syracuseStep 2784397 = 1044149) (by norm_num)
theorem B1408153 : Blo 1250443 1408153 := bbase (se 2 (by rfl) ⟨528057, by rfl⟩ : syracuseStep 1408153 = 1056115) (by norm_num)
theorem B2817197 : Blo 1250443 2817197 := bbase (se 3 (by rfl) ⟨528224, by rfl⟩ : syracuseStep 2817197 = 1056449) (by norm_num)
theorem B1408189 : Blo 1250443 1408189 := bbase (se 3 (by rfl) ⟨264035, by rfl⟩ : syracuseStep 1408189 = 528071) (by norm_num)
theorem B3169469 : Blo 1250443 3169469 := bbase (se 3 (by rfl) ⟨594275, by rfl⟩ : syracuseStep 3169469 = 1188551) (by norm_num)
theorem B2112709 : Blo 1250443 2112709 := bbase (se 4 (by rfl) ⟨198066, by rfl⟩ : syracuseStep 2112709 = 396133) (by norm_num)
theorem B1408225 : Blo 1250443 1408225 := bbase (se 2 (by rfl) ⟨528084, by rfl⟩ : syracuseStep 1408225 = 1056169) (by norm_num)
theorem B2817269 : Blo 1250443 2817269 := bbase (se 5 (by rfl) ⟨132059, by rfl⟩ : syracuseStep 2817269 = 264119) (by norm_num)
theorem B1408261 : Blo 1250443 1408261 := bbase (se 4 (by rfl) ⟨132024, by rfl⟩ : syracuseStep 1408261 = 264049) (by norm_num)
theorem B4226309 : Blo 1250443 4226309 := bbase (se 4 (by rfl) ⟨396216, by rfl⟩ : syracuseStep 4226309 = 792433) (by norm_num)
theorem B2112797 : Blo 1250443 2112797 := bbase (se 3 (by rfl) ⟨396149, by rfl⟩ : syracuseStep 2112797 = 792299) (by norm_num)
theorem B1408297 : Blo 1250443 1408297 := bbase (se 2 (by rfl) ⟨528111, by rfl⟩ : syracuseStep 1408297 = 1056223) (by norm_num)
theorem B2284853 : Blo 1250443 2284853 := bbase (se 5 (by rfl) ⟨107102, by rfl⟩ : syracuseStep 2284853 = 214205) (by norm_num)
theorem B3562805 : Blo 1250443 3562805 := bbase (se 5 (by rfl) ⟨167006, by rfl⟩ : syracuseStep 3562805 = 334013) (by norm_num)
theorem B2817341 : Blo 1250443 2817341 := bbase (se 3 (by rfl) ⟨528251, by rfl⟩ : syracuseStep 2817341 = 1056503) (by norm_num)
theorem B1408333 : Blo 1250443 1408333 := bbase (se 3 (by rfl) ⟨264062, by rfl⟩ : syracuseStep 1408333 = 528125) (by norm_num)
theorem B2375021 : Blo 1250443 2375021 := bbase (se 3 (by rfl) ⟨445316, by rfl⟩ : syracuseStep 2375021 = 890633) (by norm_num)
theorem B1408369 : Blo 1250443 1408369 := bbase (se 2 (by rfl) ⟨528138, by rfl⟩ : syracuseStep 1408369 = 1056277) (by norm_num)
theorem B2817413 : Blo 1250443 2817413 := bbase (se 4 (by rfl) ⟨264132, by rfl⟩ : syracuseStep 2817413 = 528265) (by norm_num)
theorem B3612053 : Blo 1250443 3612053 := bbase (se 6 (by rfl) ⟨84657, by rfl⟩ : syracuseStep 3612053 = 169315) (by norm_num)
theorem B1408405 : Blo 1250443 1408405 := bbase (se 6 (by rfl) ⟨33009, by rfl⟩ : syracuseStep 1408405 = 66019) (by norm_num)
theorem B2112925 : Blo 1250443 2112925 := bbase (se 3 (by rfl) ⟨396173, by rfl⟩ : syracuseStep 2112925 = 792347) (by norm_num)
theorem B4750757 : Blo 1250443 4750757 := bbase (se 4 (by rfl) ⟨445383, by rfl⟩ : syracuseStep 4750757 = 890767) (by norm_num)
theorem B1408441 : Blo 1250443 1408441 := bbase (se 2 (by rfl) ⟨528165, by rfl⟩ : syracuseStep 1408441 = 1056331) (by norm_num)
theorem B2817485 : Blo 1250443 2817485 := bbase (se 3 (by rfl) ⟨528278, by rfl⟩ : syracuseStep 2817485 = 1056557) (by norm_num)
theorem B1408477 : Blo 1250443 1408477 := bbase (se 3 (by rfl) ⟨264089, by rfl⟩ : syracuseStep 1408477 = 528179) (by norm_num)
theorem B2113013 : Blo 1250443 2113013 := bbase (se 5 (by rfl) ⟨99047, by rfl⟩ : syracuseStep 2113013 = 198095) (by norm_num)
theorem B1408513 : Blo 1250443 1408513 := bbase (se 2 (by rfl) ⟨528192, by rfl⟩ : syracuseStep 1408513 = 1056385) (by norm_num)
theorem B2375173 : Blo 1250443 2375173 := bbase (se 4 (by rfl) ⟨222672, by rfl⟩ : syracuseStep 2375173 = 445345) (by norm_num)
theorem B2817557 : Blo 1250443 2817557 := bbase (se 6 (by rfl) ⟨66036, by rfl⟩ : syracuseStep 2817557 = 132073) (by norm_num)
theorem B3169813 : Blo 1250443 3169813 := bbase (se 6 (by rfl) ⟨74292, by rfl⟩ : syracuseStep 3169813 = 148585) (by norm_num)
theorem B1408549 : Blo 1250443 1408549 := bbase (se 4 (by rfl) ⟨132051, by rfl⟩ : syracuseStep 1408549 = 264103) (by norm_num)
theorem B1408585 : Blo 1250443 1408585 := bbase (se 2 (by rfl) ⟨528219, by rfl⟩ : syracuseStep 1408585 = 1056439) (by norm_num)
theorem B7126613 : Blo 1250443 7126613 := bbase (se 8 (by rfl) ⟨41757, by rfl⟩ : syracuseStep 7126613 = 83515) (by norm_num)
theorem B2817629 : Blo 1250443 2817629 := bbase (se 3 (by rfl) ⟨528305, by rfl⟩ : syracuseStep 2817629 = 1056611) (by norm_num)
theorem B1408621 : Blo 1250443 1408621 := bbase (se 3 (by rfl) ⟨264116, by rfl⟩ : syracuseStep 1408621 = 528233) (by norm_num)
theorem B2113141 : Blo 1250443 2113141 := bbase (se 5 (by rfl) ⟨99053, by rfl⟩ : syracuseStep 2113141 = 198107) (by norm_num)
theorem B3210877 : Blo 1250443 3210877 := bbase (se 3 (by rfl) ⟨602039, by rfl⟩ : syracuseStep 3210877 = 1204079) (by norm_num)
theorem B1523333 : Blo 1250443 1523333 := bbase (se 4 (by rfl) ⟨142812, by rfl⟩ : syracuseStep 1523333 = 285625) (by norm_num)
theorem B3169925 : Blo 1250443 3169925 := bbase (se 4 (by rfl) ⟨297180, by rfl⟩ : syracuseStep 3169925 = 594361) (by norm_num)
theorem B1408657 : Blo 1250443 1408657 := bbase (se 2 (by rfl) ⟨528246, by rfl⟩ : syracuseStep 1408657 = 1056493) (by norm_num)
theorem B2817701 : Blo 1250443 2817701 := bbase (se 4 (by rfl) ⟨264159, by rfl⟩ : syracuseStep 2817701 = 528319) (by norm_num)
theorem B4513445 : Blo 1250443 4513445 := bbase (se 4 (by rfl) ⟨423135, by rfl⟩ : syracuseStep 4513445 = 846271) (by norm_num)
theorem B1408693 : Blo 1250443 1408693 := bbase (se 5 (by rfl) ⟨66032, by rfl⟩ : syracuseStep 1408693 = 132065) (by norm_num)
theorem B4226741 : Blo 1250443 4226741 := bbase (se 5 (by rfl) ⟨198128, by rfl⟩ : syracuseStep 4226741 = 396257) (by norm_num)
theorem B4751045 : Blo 1250443 4751045 := bbase (se 4 (by rfl) ⟨445410, by rfl⟩ : syracuseStep 4751045 = 890821) (by norm_num)
theorem B2113229 : Blo 1250443 2113229 := bbase (se 3 (by rfl) ⟨396230, by rfl⟩ : syracuseStep 2113229 = 792461) (by norm_num)
theorem B1408729 : Blo 1250443 1408729 := bbase (se 2 (by rfl) ⟨528273, by rfl⟩ : syracuseStep 1408729 = 1056547) (by norm_num)
theorem B1875677 : Blo 1250443 1875677 := bbase (se 3 (by rfl) ⟨351689, by rfl⟩ : syracuseStep 1875677 = 703379) (by norm_num)
theorem B2817773 : Blo 1250443 2817773 := bbase (se 3 (by rfl) ⟨528332, by rfl⟩ : syracuseStep 2817773 = 1056665) (by norm_num)
theorem B1875701 : Blo 1250443 1875701 := bbase (se 5 (by rfl) ⟨87923, by rfl⟩ : syracuseStep 1875701 = 175847) (by norm_num)
theorem B1408765 : Blo 1250443 1408765 := bbase (se 3 (by rfl) ⟨264143, by rfl⟩ : syracuseStep 1408765 = 528287) (by norm_num)
theorem B1875725 : Blo 1250443 1875725 := bbase (se 3 (by rfl) ⟨351698, by rfl⟩ : syracuseStep 1875725 = 703397) (by norm_num)
theorem B1408801 : Blo 1250443 1408801 := bbase (se 2 (by rfl) ⟨528300, by rfl⟩ : syracuseStep 1408801 = 1056601) (by norm_num)
theorem B1875749 : Blo 1250443 1875749 := bbase (se 4 (by rfl) ⟨175851, by rfl⟩ : syracuseStep 1875749 = 351703) (by norm_num)
theorem B4570933 : Blo 1250443 4570933 := bbase (se 5 (by rfl) ⟨214262, by rfl⟩ : syracuseStep 4570933 = 428525) (by norm_num)
theorem B2375477 : Blo 1250443 2375477 := bbase (se 5 (by rfl) ⟨111350, by rfl⟩ : syracuseStep 2375477 = 222701) (by norm_num)
theorem B3383093 : Blo 1250443 3383093 := bbase (se 5 (by rfl) ⟨158582, by rfl⟩ : syracuseStep 3383093 = 317165) (by norm_num)
theorem B2817845 : Blo 1250443 2817845 := bbase (se 5 (by rfl) ⟨132086, by rfl⟩ : syracuseStep 2817845 = 264173) (by norm_num)
theorem B1875773 : Blo 1250443 1875773 := bbase (se 3 (by rfl) ⟨351707, by rfl⟩ : syracuseStep 1875773 = 703415) (by norm_num)
theorem B1408837 : Blo 1250443 1408837 := bbase (se 4 (by rfl) ⟨132078, by rfl⟩ : syracuseStep 1408837 = 264157) (by norm_num)
theorem B3170117 : Blo 1250443 3170117 := bbase (se 4 (by rfl) ⟨297198, by rfl⟩ : syracuseStep 3170117 = 594397) (by norm_num)
theorem B2113357 : Blo 1250443 2113357 := bbase (se 3 (by rfl) ⟨396254, by rfl⟩ : syracuseStep 2113357 = 792509) (by norm_num)
theorem B1875797 : Blo 1250443 1875797 := bbase (se 9 (by rfl) ⟨5495, by rfl⟩ : syracuseStep 1875797 = 10991) (by norm_num)
theorem B1408873 : Blo 1250443 1408873 := bbase (se 2 (by rfl) ⟨528327, by rfl⟩ : syracuseStep 1408873 = 1056655) (by norm_num)
theorem B1875821 : Blo 1250443 1875821 := bbase (se 3 (by rfl) ⟨351716, by rfl⟩ : syracuseStep 1875821 = 703433) (by norm_num)
theorem B9633653 : Blo 1250443 9633653 := bbase (se 5 (by rfl) ⟨451577, by rfl⟩ : syracuseStep 9633653 = 903155) (by norm_num)
theorem B2817917 : Blo 1250443 2817917 := bbase (se 3 (by rfl) ⟨528359, by rfl⟩ : syracuseStep 2817917 = 1056719) (by norm_num)
theorem B1875845 : Blo 1250443 1875845 := bbase (se 4 (by rfl) ⟨175860, by rfl⟩ : syracuseStep 1875845 = 351721) (by norm_num)
theorem B1408909 : Blo 1250443 1408909 := bbase (se 3 (by rfl) ⟨264170, by rfl⟩ : syracuseStep 1408909 = 528341) (by norm_num)
theorem B1875869 : Blo 1250443 1875869 := bbase (se 3 (by rfl) ⟨351725, by rfl⟩ : syracuseStep 1875869 = 703451) (by norm_num)
theorem B2113445 : Blo 1250443 2113445 := bbase (se 4 (by rfl) ⟨198135, by rfl⟩ : syracuseStep 2113445 = 396271) (by norm_num)
theorem B1408945 : Blo 1250443 1408945 := bbase (se 2 (by rfl) ⟨528354, by rfl⟩ : syracuseStep 1408945 = 1056709) (by norm_num)
theorem B1875893 : Blo 1250443 1875893 := bbase (se 5 (by rfl) ⟨87932, by rfl⟩ : syracuseStep 1875893 = 175865) (by norm_num)
theorem B2408381 : Blo 1250443 2408381 := bbase (se 3 (by rfl) ⟨451571, by rfl⟩ : syracuseStep 2408381 = 903143) (by norm_num)
theorem B2817989 : Blo 1250443 2817989 := bbase (se 4 (by rfl) ⟨264186, by rfl⟩ : syracuseStep 2817989 = 528373) (by norm_num)
theorem B1875917 : Blo 1250443 1875917 := bbase (se 3 (by rfl) ⟨351734, by rfl⟩ : syracuseStep 1875917 = 703469) (by norm_num)
theorem B1408981 : Blo 1250443 1408981 := bbase (se 7 (by rfl) ⟨16511, by rfl⟩ : syracuseStep 1408981 = 33023) (by norm_num)
theorem B1875941 : Blo 1250443 1875941 := bbase (se 4 (by rfl) ⟨175869, by rfl⟩ : syracuseStep 1875941 = 351739) (by norm_num)
theorem B1875965 : Blo 1250443 1875965 := bbase (se 3 (by rfl) ⟨351743, by rfl⟩ : syracuseStep 1875965 = 703487) (by norm_num)
theorem B1875971 : Blo 1250443 1875971 := bstep (se 1 (by rfl) ⟨1406978, by rfl⟩ : syracuseStep 1875971 = 2813957) B2813957
theorem B1876001 : Blo 1250443 1876001 := bstep (se 2 (by rfl) ⟨703500, by rfl⟩ : syracuseStep 1876001 = 1407001) B1407001
theorem B1876019 : Blo 1250443 1876019 := bstep (se 1 (by rfl) ⟨1407014, by rfl⟩ : syracuseStep 1876019 = 2814029) B2814029
theorem B1876049 : Blo 1250443 1876049 := bstep (se 2 (by rfl) ⟨703518, by rfl⟩ : syracuseStep 1876049 = 1407037) B1407037
theorem B1876067 : Blo 1250443 1876067 := bstep (se 1 (by rfl) ⟨1407050, by rfl⟩ : syracuseStep 1876067 = 2814101) B2814101
theorem B1876097 : Blo 1250443 1876097 := bstep (se 2 (by rfl) ⟨703536, by rfl⟩ : syracuseStep 1876097 = 1407073) B1407073
theorem B2670737 : Blo 1250443 2670737 := bstep (se 2 (by rfl) ⟨1001526, by rfl⟩ : syracuseStep 2670737 = 2003053) B2003053
theorem B3383441 : Blo 1250443 3383441 := bstep (se 2 (by rfl) ⟨1268790, by rfl⟩ : syracuseStep 3383441 = 2537581) B2537581
theorem B1876115 : Blo 1250443 1876115 := bstep (se 1 (by rfl) ⟨1407086, by rfl⟩ : syracuseStep 1876115 = 2814173) B2814173
theorem B6332579 : Blo 1250443 6332579 := bstep (se 1 (by rfl) ⟨4749434, by rfl⟩ : syracuseStep 6332579 = 9498869) B9498869
theorem B5349539 : Blo 1250443 5349539 := bstep (se 1 (by rfl) ⟨4012154, by rfl⟩ : syracuseStep 5349539 = 8024309) B8024309
theorem B1876145 : Blo 1250443 1876145 := bstep (se 2 (by rfl) ⟨703554, by rfl⟩ : syracuseStep 1876145 = 1407109) B1407109
theorem B1876163 : Blo 1250443 1876163 := bstep (se 1 (by rfl) ⟨1407122, by rfl⟩ : syracuseStep 1876163 = 2814245) B2814245
theorem B1876193 : Blo 1250443 1876193 := bstep (se 2 (by rfl) ⟨703572, by rfl⟩ : syracuseStep 1876193 = 1407145) B1407145
theorem B1876211 : Blo 1250443 1876211 := bstep (se 1 (by rfl) ⟨1407158, by rfl⟩ : syracuseStep 1876211 = 2814317) B2814317
theorem B1876241 : Blo 1250443 1876241 := bstep (se 2 (by rfl) ⟨703590, by rfl⟩ : syracuseStep 1876241 = 1407181) B1407181
theorem B1876259 : Blo 1250443 1876259 := bstep (se 1 (by rfl) ⟨1407194, by rfl⟩ : syracuseStep 1876259 = 2814389) B2814389
theorem B1876289 : Blo 1250443 1876289 := bstep (se 2 (by rfl) ⟨703608, by rfl⟩ : syracuseStep 1876289 = 1407217) B1407217
theorem B1876307 : Blo 1250443 1876307 := bstep (se 1 (by rfl) ⟨1407230, by rfl⟩ : syracuseStep 1876307 = 2814461) B2814461
theorem B1876337 : Blo 1250443 1876337 := bstep (se 2 (by rfl) ⟨703626, by rfl⟩ : syracuseStep 1876337 = 1407253) B1407253
theorem B4751729 : Blo 1250443 4751729 := bstep (se 2 (by rfl) ⟨1781898, by rfl⟩ : syracuseStep 4751729 = 3563797) B3563797
theorem B1876355 : Blo 1250443 1876355 := bstep (se 1 (by rfl) ⟨1407266, by rfl⟩ : syracuseStep 1876355 = 2814533) B2814533
theorem B1876385 : Blo 1250443 1876385 := bstep (se 2 (by rfl) ⟨703644, by rfl⟩ : syracuseStep 1876385 = 1407289) B1407289
theorem B1876403 : Blo 1250443 1876403 := bstep (se 1 (by rfl) ⟨1407302, by rfl⟩ : syracuseStep 1876403 = 2814605) B2814605
theorem B1876433 : Blo 1250443 1876433 := bstep (se 2 (by rfl) ⟨703662, by rfl⟩ : syracuseStep 1876433 = 1407325) B1407325
theorem B2376145 : Blo 1250443 2376145 := bstep (se 2 (by rfl) ⟨891054, by rfl⟩ : syracuseStep 2376145 = 1782109) B1782109
theorem B1876451 : Blo 1250443 1876451 := bstep (se 1 (by rfl) ⟨1407338, by rfl⟩ : syracuseStep 1876451 = 2814677) B2814677
theorem B3564013 : Blo 1250443 3564013 := bstep (se 3 (by rfl) ⟨668252, by rfl⟩ : syracuseStep 3564013 = 1336505) B1336505
theorem B1876481 : Blo 1250443 1876481 := bstep (se 2 (by rfl) ⟨703680, by rfl⟩ : syracuseStep 1876481 = 1407361) B1407361
theorem B1876499 : Blo 1250443 1876499 := bstep (se 1 (by rfl) ⟨1407374, by rfl⟩ : syracuseStep 1876499 = 2814749) B2814749
theorem B1876529 : Blo 1250443 1876529 := bstep (se 2 (by rfl) ⟨703698, by rfl⟩ : syracuseStep 1876529 = 1407397) B1407397
theorem B1876547 : Blo 1250443 1876547 := bstep (se 1 (by rfl) ⟨1407410, by rfl⟩ : syracuseStep 1876547 = 2814821) B2814821
theorem B1876577 : Blo 1250443 1876577 := bstep (se 2 (by rfl) ⟨703716, by rfl⟩ : syracuseStep 1876577 = 1407433) B1407433
theorem B1876595 : Blo 1250443 1876595 := bstep (se 1 (by rfl) ⟨1407446, by rfl⟩ : syracuseStep 1876595 = 2814893) B2814893
theorem B1876625 : Blo 1250443 1876625 := bstep (se 2 (by rfl) ⟨703734, by rfl⟩ : syracuseStep 1876625 = 1407469) B1407469
theorem B1876643 : Blo 1250443 1876643 := bstep (se 1 (by rfl) ⟨1407482, by rfl⟩ : syracuseStep 1876643 = 2814965) B2814965
theorem B1876673 : Blo 1250443 1876673 := bstep (se 2 (by rfl) ⟨703752, by rfl⟩ : syracuseStep 1876673 = 1407505) B1407505
theorem B1876691 : Blo 1250443 1876691 := bstep (se 1 (by rfl) ⟨1407518, by rfl⟩ : syracuseStep 1876691 = 2815037) B2815037
theorem B1876721 : Blo 1250443 1876721 := bstep (se 2 (by rfl) ⟨703770, by rfl⟩ : syracuseStep 1876721 = 1407541) B1407541
theorem B8020721 : Blo 1250443 8020721 := bstep (se 2 (by rfl) ⟨3007770, by rfl⟩ : syracuseStep 8020721 = 6015541) B6015541
theorem B1876739 : Blo 1250443 1876739 := bstep (se 1 (by rfl) ⟨1407554, by rfl⟩ : syracuseStep 1876739 = 2815109) B2815109
theorem B54125333 : Blo 1250443 54125333 := bstep (se 6 (by rfl) ⟨1268562, by rfl⟩ : syracuseStep 54125333 = 2537125) B2537125
theorem B1876769 : Blo 1250443 1876769 := bstep (se 2 (by rfl) ⟨703788, by rfl⟩ : syracuseStep 1876769 = 1407577) B1407577
theorem B1876787 : Blo 1250443 1876787 := bstep (se 1 (by rfl) ⟨1407590, by rfl⟩ : syracuseStep 1876787 = 2815181) B2815181
theorem B8012621 : Blo 1250443 8012621 := bstep (se 3 (by rfl) ⟨1502366, by rfl⟩ : syracuseStep 8012621 = 3004733) B3004733
theorem B1876817 : Blo 1250443 1876817 := bstep (se 2 (by rfl) ⟨703806, by rfl⟩ : syracuseStep 1876817 = 1407613) B1407613
theorem B1876835 : Blo 1250443 1876835 := bstep (se 1 (by rfl) ⟨1407626, by rfl⟩ : syracuseStep 1876835 = 2815253) B2815253
theorem B1876865 : Blo 1250443 1876865 := bstep (se 2 (by rfl) ⟨703824, by rfl⟩ : syracuseStep 1876865 = 1407649) B1407649
theorem B1876883 : Blo 1250443 1876883 := bstep (se 1 (by rfl) ⟨1407662, by rfl⟩ : syracuseStep 1876883 = 2815325) B2815325
theorem B1876913 : Blo 1250443 1876913 := bstep (se 2 (by rfl) ⟨703842, by rfl⟩ : syracuseStep 1876913 = 1407685) B1407685
theorem B1876931 : Blo 1250443 1876931 := bstep (se 1 (by rfl) ⟨1407698, by rfl⟩ : syracuseStep 1876931 = 2815397) B2815397
theorem B6333389 : Blo 1250443 6333389 := bstep (se 3 (by rfl) ⟨1187510, by rfl⟩ : syracuseStep 6333389 = 2375021) B2375021
theorem B1876961 : Blo 1250443 1876961 := bstep (se 2 (by rfl) ⟨703860, by rfl⟩ : syracuseStep 1876961 = 1407721) B1407721
theorem B9503729 : Blo 1250443 9503729 := bstep (se 2 (by rfl) ⟨3563898, by rfl⟩ : syracuseStep 9503729 = 7127797) B7127797
theorem B3384305 : Blo 1250443 3384305 := bstep (se 2 (by rfl) ⟨1269114, by rfl⟩ : syracuseStep 3384305 = 2538229) B2538229
theorem B1876979 : Blo 1250443 1876979 := bstep (se 1 (by rfl) ⟨1407734, by rfl⟩ : syracuseStep 1876979 = 2815469) B2815469
theorem B1877009 : Blo 1250443 1877009 := bstep (se 2 (by rfl) ⟨703878, by rfl⟩ : syracuseStep 1877009 = 1407757) B1407757
theorem B1877027 : Blo 1250443 1877027 := bstep (se 1 (by rfl) ⟨1407770, by rfl⟩ : syracuseStep 1877027 = 2815541) B2815541
theorem B1877057 : Blo 1250443 1877057 := bstep (se 2 (by rfl) ⟨703896, by rfl⟩ : syracuseStep 1877057 = 1407793) B1407793
theorem B4006979 : Blo 1250443 4006979 := bstep (se 1 (by rfl) ⟨3005234, by rfl⟩ : syracuseStep 4006979 = 6010469) B6010469
theorem B1877075 : Blo 1250443 1877075 := bstep (se 1 (by rfl) ⟨1407806, by rfl⟩ : syracuseStep 1877075 = 2815613) B2815613
theorem B1877105 : Blo 1250443 1877105 := bstep (se 2 (by rfl) ⟨703914, by rfl⟩ : syracuseStep 1877105 = 1407829) B1407829
theorem B1877123 : Blo 1250443 1877123 := bstep (se 1 (by rfl) ⟨1407842, by rfl⟩ : syracuseStep 1877123 = 2815685) B2815685
theorem B1877153 : Blo 1250443 1877153 := bstep (se 2 (by rfl) ⟨703932, by rfl⟩ : syracuseStep 1877153 = 1407865) B1407865
theorem B1877171 : Blo 1250443 1877171 := bstep (se 1 (by rfl) ⟨1407878, by rfl⟩ : syracuseStep 1877171 = 2815757) B2815757
theorem B1877201 : Blo 1250443 1877201 := bstep (se 2 (by rfl) ⟨703950, by rfl⟩ : syracuseStep 1877201 = 1407901) B1407901
theorem B1877219 : Blo 1250443 1877219 := bstep (se 1 (by rfl) ⟨1407914, by rfl⟩ : syracuseStep 1877219 = 2815829) B2815829
theorem B5711089 : Blo 1250443 5711089 := bstep (se 2 (by rfl) ⟨2141658, by rfl⟩ : syracuseStep 5711089 = 4283317) B4283317
theorem B1877249 : Blo 1250443 1877249 := bstep (se 2 (by rfl) ⟨703968, by rfl⟩ : syracuseStep 1877249 = 1407937) B1407937
theorem B1877267 : Blo 1250443 1877267 := bstep (se 1 (by rfl) ⟨1407950, by rfl⟩ : syracuseStep 1877267 = 2815901) B2815901
theorem B1877297 : Blo 1250443 1877297 := bstep (se 2 (by rfl) ⟨703986, by rfl⟩ : syracuseStep 1877297 = 1407973) B1407973
theorem B1877315 : Blo 1250443 1877315 := bstep (se 1 (by rfl) ⟨1407986, by rfl⟩ : syracuseStep 1877315 = 2815973) B2815973
theorem B1877345 : Blo 1250443 1877345 := bstep (se 2 (by rfl) ⟨704004, by rfl⟩ : syracuseStep 1877345 = 1408009) B1408009
theorem B1877363 : Blo 1250443 1877363 := bstep (se 1 (by rfl) ⟨1408022, by rfl⟩ : syracuseStep 1877363 = 2816045) B2816045
theorem B1877393 : Blo 1250443 1877393 := bstep (se 2 (by rfl) ⟨704022, by rfl⟩ : syracuseStep 1877393 = 1408045) B1408045
theorem B6014371 : Blo 1250443 6014371 := bstep (se 1 (by rfl) ⟨4510778, by rfl⟩ : syracuseStep 6014371 = 9021557) B9021557
theorem B1877411 : Blo 1250443 1877411 := bstep (se 1 (by rfl) ⟨1408058, by rfl⟩ : syracuseStep 1877411 = 2816117) B2816117
theorem B1877441 : Blo 1250443 1877441 := bstep (se 2 (by rfl) ⟨704040, by rfl⟩ : syracuseStep 1877441 = 1408081) B1408081
theorem B4220369 : Blo 1250443 4220369 := bstep (se 2 (by rfl) ⟨1582638, by rfl⟩ : syracuseStep 4220369 = 3165277) B3165277
theorem B1877459 : Blo 1250443 1877459 := bstep (se 1 (by rfl) ⟨1408094, by rfl⟩ : syracuseStep 1877459 = 2816189) B2816189
theorem B1426915 : Blo 1250443 1426915 := bstep (se 1 (by rfl) ⟨1070186, by rfl⟩ : syracuseStep 1426915 = 2140373) B2140373
theorem B5342705 : Blo 1250443 5342705 := bstep (se 2 (by rfl) ⟨2003514, by rfl⟩ : syracuseStep 5342705 = 4007029) B4007029
theorem B1877489 : Blo 1250443 1877489 := bstep (se 2 (by rfl) ⟨704058, by rfl⟩ : syracuseStep 1877489 = 1408117) B1408117
theorem B2377201 : Blo 1250443 2377201 := bstep (se 2 (by rfl) ⟨891450, by rfl⟩ : syracuseStep 2377201 = 1782901) B1782901
theorem B1877507 : Blo 1250443 1877507 := bstep (se 1 (by rfl) ⟨1408130, by rfl⟩ : syracuseStep 1877507 = 2816261) B2816261
theorem B3712529 : Blo 1250443 3712529 := bstep (se 2 (by rfl) ⟨1392198, by rfl⟩ : syracuseStep 3712529 = 2784397) B2784397
theorem B3565073 : Blo 1250443 3565073 := bstep (se 2 (by rfl) ⟨1336902, by rfl⟩ : syracuseStep 3565073 = 2673805) B2673805
theorem B1877537 : Blo 1250443 1877537 := bstep (se 2 (by rfl) ⟨704076, by rfl⟩ : syracuseStep 1877537 = 1408153) B1408153
theorem B1877555 : Blo 1250443 1877555 := bstep (se 1 (by rfl) ⟨1408166, by rfl⟩ : syracuseStep 1877555 = 2816333) B2816333
theorem B1877585 : Blo 1250443 1877585 := bstep (se 2 (by rfl) ⟨704094, by rfl⟩ : syracuseStep 1877585 = 1408189) B1408189
theorem B1336915 : Blo 1250443 1336915 := bstep (se 1 (by rfl) ⟨1002686, by rfl⟩ : syracuseStep 1336915 = 2005373) B2005373
theorem B1877603 : Blo 1250443 1877603 := bstep (se 1 (by rfl) ⟨1408202, by rfl⟩ : syracuseStep 1877603 = 2816405) B2816405
theorem B1877633 : Blo 1250443 1877633 := bstep (se 2 (by rfl) ⟨704112, by rfl⟩ : syracuseStep 1877633 = 1408225) B1408225
theorem B1877651 : Blo 1250443 1877651 := bstep (se 1 (by rfl) ⟨1408238, by rfl⟩ : syracuseStep 1877651 = 2816477) B2816477
theorem B3049123 : Blo 1250443 3049123 := bstep (se 1 (by rfl) ⟨2286842, by rfl⟩ : syracuseStep 3049123 = 4573685) B4573685
theorem B1877681 : Blo 1250443 1877681 := bstep (se 2 (by rfl) ⟨704130, by rfl⟩ : syracuseStep 1877681 = 1408261) B1408261
theorem B1877699 : Blo 1250443 1877699 := bstep (se 1 (by rfl) ⟨1408274, by rfl⟩ : syracuseStep 1877699 = 2816549) B2816549
theorem B1877729 : Blo 1250443 1877729 := bstep (se 2 (by rfl) ⟨704148, by rfl⟩ : syracuseStep 1877729 = 1408297) B1408297
theorem B1877747 : Blo 1250443 1877747 := bstep (se 1 (by rfl) ⟨1408310, by rfl⟩ : syracuseStep 1877747 = 2816621) B2816621
theorem B1877777 : Blo 1250443 1877777 := bstep (se 2 (by rfl) ⟨704166, by rfl⟩ : syracuseStep 1877777 = 1408333) B1408333
theorem B1877795 : Blo 1250443 1877795 := bstep (se 1 (by rfl) ⟨1408346, by rfl⟩ : syracuseStep 1877795 = 2816693) B2816693
theorem B4753187 : Blo 1250443 4753187 := bstep (se 1 (by rfl) ⟨3564890, by rfl⟩ : syracuseStep 4753187 = 7129781) B7129781
theorem B4753201 : Blo 1250443 4753201 := bstep (se 2 (by rfl) ⟨1782450, by rfl⟩ : syracuseStep 4753201 = 3564901) B3564901
theorem B1877825 : Blo 1250443 1877825 := bstep (se 2 (by rfl) ⟨704184, by rfl⟩ : syracuseStep 1877825 = 1408369) B1408369
theorem B1877843 : Blo 1250443 1877843 := bstep (se 1 (by rfl) ⟨1408382, by rfl⟩ : syracuseStep 1877843 = 2816765) B2816765
theorem B1877873 : Blo 1250443 1877873 := bstep (se 2 (by rfl) ⟨704202, by rfl⟩ : syracuseStep 1877873 = 1408405) B1408405
theorem B1877891 : Blo 1250443 1877891 := bstep (se 1 (by rfl) ⟨1408418, by rfl⟩ : syracuseStep 1877891 = 2816837) B2816837
theorem B2377603 : Blo 1250443 2377603 := bstep (se 1 (by rfl) ⟨1783202, by rfl⟩ : syracuseStep 2377603 = 3566405) B3566405
theorem B1877921 : Blo 1250443 1877921 := bstep (se 2 (by rfl) ⟨704220, by rfl⟩ : syracuseStep 1877921 = 1408441) B1408441
theorem B2377649 : Blo 1250443 2377649 := bstep (se 2 (by rfl) ⟨891618, by rfl⟩ : syracuseStep 2377649 = 1783237) B1783237
theorem B1877939 : Blo 1250443 1877939 := bstep (se 1 (by rfl) ⟨1408454, by rfl⟩ : syracuseStep 1877939 = 2816909) B2816909
theorem B4007875 : Blo 1250443 4007875 := bstep (se 1 (by rfl) ⟨3005906, by rfl⟩ : syracuseStep 4007875 = 6011813) B6011813
theorem B1877969 : Blo 1250443 1877969 := bstep (se 2 (by rfl) ⟨704238, by rfl⟩ : syracuseStep 1877969 = 1408477) B1408477
theorem B1583059 : Blo 1250443 1583059 := bstep (se 1 (by rfl) ⟨1187294, by rfl⟩ : syracuseStep 1583059 = 2374589) B2374589
theorem B2254819 : Blo 1250443 2254819 := bstep (se 1 (by rfl) ⟨1691114, by rfl⟩ : syracuseStep 2254819 = 3382229) B3382229
theorem B1877987 : Blo 1250443 1877987 := bstep (se 1 (by rfl) ⟨1408490, by rfl⟩ : syracuseStep 1877987 = 2816981) B2816981
theorem B4220909 : Blo 1250443 4220909 := bstep (se 3 (by rfl) ⟨791420, by rfl⟩ : syracuseStep 4220909 = 1582841) B1582841
theorem B7129073 : Blo 1250443 7129073 := bstep (se 2 (by rfl) ⟨2673402, by rfl⟩ : syracuseStep 7129073 = 5346805) B5346805
theorem B1878017 : Blo 1250443 1878017 := bstep (se 2 (by rfl) ⟨704256, by rfl⟩ : syracuseStep 1878017 = 1408513) B1408513
theorem B1337347 : Blo 1250443 1337347 := bstep (se 1 (by rfl) ⟨1003010, by rfl⟩ : syracuseStep 1337347 = 2006021) B2006021
theorem B1878035 : Blo 1250443 1878035 := bstep (se 1 (by rfl) ⟨1408526, by rfl⟩ : syracuseStep 1878035 = 2817053) B2817053
theorem B4220963 : Blo 1250443 4220963 := bstep (se 1 (by rfl) ⟨3165722, by rfl⟩ : syracuseStep 4220963 = 6331445) B6331445
theorem B1878065 : Blo 1250443 1878065 := bstep (se 2 (by rfl) ⟨704274, by rfl⟩ : syracuseStep 1878065 = 1408549) B1408549
theorem B1583155 : Blo 1250443 1583155 := bstep (se 1 (by rfl) ⟨1187366, by rfl⟩ : syracuseStep 1583155 = 2374733) B2374733
theorem B1878083 : Blo 1250443 1878083 := bstep (se 1 (by rfl) ⟨1408562, by rfl⟩ : syracuseStep 1878083 = 2817125) B2817125
theorem B1878113 : Blo 1250443 1878113 := bstep (se 2 (by rfl) ⟨704292, by rfl⟩ : syracuseStep 1878113 = 1408585) B1408585
theorem B1878131 : Blo 1250443 1878131 := bstep (se 1 (by rfl) ⟨1408598, by rfl⟩ : syracuseStep 1878131 = 2817197) B2817197
theorem B9021581 : Blo 1250443 9021581 := bstep (se 3 (by rfl) ⟨1691546, by rfl⟩ : syracuseStep 9021581 = 3383093) B3383093
theorem B1878161 : Blo 1250443 1878161 := bstep (se 2 (by rfl) ⟨704310, by rfl⟩ : syracuseStep 1878161 = 1408621) B1408621
theorem B1878179 : Blo 1250443 1878179 := bstep (se 1 (by rfl) ⟨1408634, by rfl⟩ : syracuseStep 1878179 = 2817269) B2817269
theorem B3565745 : Blo 1250443 3565745 := bstep (se 2 (by rfl) ⟨1337154, by rfl⟩ : syracuseStep 3565745 = 2674309) B2674309
theorem B1878209 : Blo 1250443 1878209 := bstep (se 2 (by rfl) ⟨704328, by rfl⟩ : syracuseStep 1878209 = 1408657) B1408657
theorem B1878227 : Blo 1250443 1878227 := bstep (se 1 (by rfl) ⟨1408670, by rfl⟩ : syracuseStep 1878227 = 2817341) B2817341
theorem B1878257 : Blo 1250443 1878257 := bstep (se 2 (by rfl) ⟨704346, by rfl⟩ : syracuseStep 1878257 = 1408693) B1408693
theorem B1878275 : Blo 1250443 1878275 := bstep (se 1 (by rfl) ⟨1408706, by rfl⟩ : syracuseStep 1878275 = 2817413) B2817413
theorem B1878305 : Blo 1250443 1878305 := bstep (se 2 (by rfl) ⟨704364, by rfl⟩ : syracuseStep 1878305 = 1408729) B1408729
theorem B4221233 : Blo 1250443 4221233 := bstep (se 2 (by rfl) ⟨1582962, by rfl⟩ : syracuseStep 4221233 = 3165925) B3165925
theorem B1878323 : Blo 1250443 1878323 := bstep (se 1 (by rfl) ⟨1408742, by rfl⟩ : syracuseStep 1878323 = 2817485) B2817485
theorem B1878353 : Blo 1250443 1878353 := bstep (se 2 (by rfl) ⟨704382, by rfl⟩ : syracuseStep 1878353 = 1408765) B1408765
theorem B1878371 : Blo 1250443 1878371 := bstep (se 1 (by rfl) ⟨1408778, by rfl⟩ : syracuseStep 1878371 = 2817557) B2817557
theorem B1878401 : Blo 1250443 1878401 := bstep (se 2 (by rfl) ⟨704400, by rfl⟩ : syracuseStep 1878401 = 1408801) B1408801
theorem B4065677 : Blo 1250443 4065677 := bstep (se 3 (by rfl) ⟨762314, by rfl⟩ : syracuseStep 4065677 = 1524629) B1524629
theorem B1878419 : Blo 1250443 1878419 := bstep (se 1 (by rfl) ⟨1408814, by rfl⟩ : syracuseStep 1878419 = 2817629) B2817629
theorem B1690033 : Blo 1250443 1690033 := bstep (se 2 (by rfl) ⟨633762, by rfl⟩ : syracuseStep 1690033 = 1267525) B1267525
theorem B1878449 : Blo 1250443 1878449 := bstep (se 2 (by rfl) ⟨704418, by rfl⟩ : syracuseStep 1878449 = 1408837) B1408837
theorem B1878467 : Blo 1250443 1878467 := bstep (se 1 (by rfl) ⟨1408850, by rfl⟩ : syracuseStep 1878467 = 2817701) B2817701
theorem B3008963 : Blo 1250443 3008963 := bstep (se 1 (by rfl) ⟨2256722, by rfl⟩ : syracuseStep 3008963 = 4513445) B4513445
theorem B1878497 : Blo 1250443 1878497 := bstep (se 2 (by rfl) ⟨704436, by rfl⟩ : syracuseStep 1878497 = 1408873) B1408873
theorem B8129009 : Blo 1250443 8129009 := bstep (se 2 (by rfl) ⟨3048378, by rfl⟩ : syracuseStep 8129009 = 6096757) B6096757
theorem B1878515 : Blo 1250443 1878515 := bstep (se 1 (by rfl) ⟨1408886, by rfl⟩ : syracuseStep 1878515 = 2817773) B2817773
theorem B10693133 : Blo 1250443 10693133 := bstep (se 3 (by rfl) ⟨2004962, by rfl⟩ : syracuseStep 10693133 = 4009925) B4009925
theorem B1878545 : Blo 1250443 1878545 := bstep (se 2 (by rfl) ⟨704454, by rfl⟩ : syracuseStep 1878545 = 1408909) B1408909
theorem B1583651 : Blo 1250443 1583651 := bstep (se 1 (by rfl) ⟨1187738, by rfl⟩ : syracuseStep 1583651 = 2375477) B2375477
theorem B1878563 : Blo 1250443 1878563 := bstep (se 1 (by rfl) ⟨1408922, by rfl⟩ : syracuseStep 1878563 = 2817845) B2817845
theorem B1878593 : Blo 1250443 1878593 := bstep (se 2 (by rfl) ⟨704472, by rfl⟩ : syracuseStep 1878593 = 1408945) B1408945
theorem B1878611 : Blo 1250443 1878611 := bstep (se 1 (by rfl) ⟨1408958, by rfl⟩ : syracuseStep 1878611 = 2817917) B2817917
theorem B1878641 : Blo 1250443 1878641 := bstep (se 2 (by rfl) ⟨704490, by rfl⟩ : syracuseStep 1878641 = 1408981) B1408981
theorem B1878659 : Blo 1250443 1878659 := bstep (se 1 (by rfl) ⟨1408994, by rfl⟩ : syracuseStep 1878659 = 2817989) B2817989
theorem B1903331 : Blo 1250443 1903331 := bstep (se 1 (by rfl) ⟨1427498, by rfl⟩ : syracuseStep 1903331 = 2854997) B2854997
theorem B1903379 : Blo 1250443 1903379 := bstep (se 1 (by rfl) ⟨1427534, by rfl⟩ : syracuseStep 1903379 = 2855069) B2855069
theorem B4221773 : Blo 1250443 4221773 := bstep (se 3 (by rfl) ⟨791582, by rfl⟩ : syracuseStep 4221773 = 1583165) B1583165
theorem B1805153 : Blo 1250443 1805153 := bstep (se 2 (by rfl) ⟨676932, by rfl⟩ : syracuseStep 1805153 = 1353865) B1353865
theorem B4221827 : Blo 1250443 4221827 := bstep (se 1 (by rfl) ⟨3166370, by rfl⟩ : syracuseStep 4221827 = 6332741) B6332741
theorem B3566531 : Blo 1250443 3566531 := bstep (se 1 (by rfl) ⟨2674898, by rfl⟩ : syracuseStep 3566531 = 5349797) B5349797
theorem B3804131 : Blo 1250443 3804131 := bstep (se 1 (by rfl) ⟨2853098, by rfl⟩ : syracuseStep 3804131 = 5706197) B5706197
theorem B3255299 : Blo 1250443 3255299 := bstep (se 1 (by rfl) ⟨2441474, by rfl⟩ : syracuseStep 3255299 = 4882949) B4882949
theorem B4008977 : Blo 1250443 4008977 := bstep (se 2 (by rfl) ⟨1503366, by rfl⟩ : syracuseStep 4008977 = 3006733) B3006733
theorem B8121379 : Blo 1250443 8121379 := bstep (se 1 (by rfl) ⟨6091034, by rfl⟩ : syracuseStep 8121379 = 12182069) B12182069
theorem B30460981 : Blo 1250443 30460981 := bstep (se 5 (by rfl) ⟨1427858, by rfl⟩ : syracuseStep 30460981 = 2855717) B2855717
theorem B1903745 : Blo 1250443 1903745 := bstep (se 2 (by rfl) ⟨713904, by rfl⟩ : syracuseStep 1903745 = 1427809) B1427809
theorem B4222097 : Blo 1250443 4222097 := bstep (se 2 (by rfl) ⟨1583286, by rfl⟩ : syracuseStep 4222097 = 3166573) B3166573
theorem B4009105 : Blo 1250443 4009105 := bstep (se 2 (by rfl) ⟨1503414, by rfl⟩ : syracuseStep 4009105 = 3006829) B3006829
theorem B1780913 : Blo 1250443 1780913 := bstep (se 2 (by rfl) ⟨667842, by rfl⟩ : syracuseStep 1780913 = 1335685) B1335685
theorem B1584355 : Blo 1250443 1584355 := bstep (se 1 (by rfl) ⟨1188266, by rfl⟩ : syracuseStep 1584355 = 2376533) B2376533
theorem B4754659 : Blo 1250443 4754659 := bstep (se 1 (by rfl) ⟨3565994, by rfl⟩ : syracuseStep 4754659 = 7131989) B7131989
theorem B1584451 : Blo 1250443 1584451 := bstep (se 1 (by rfl) ⟨1188338, by rfl⟩ : syracuseStep 1584451 = 2376677) B2376677
theorem B6016369 : Blo 1250443 6016369 := bstep (se 2 (by rfl) ⟨2256138, by rfl⟩ : syracuseStep 6016369 = 4512277) B4512277
theorem B7130531 : Blo 1250443 7130531 := bstep (se 1 (by rfl) ⟨5347898, by rfl⟩ : syracuseStep 7130531 = 10695797) B10695797
theorem B2674147 : Blo 1250443 2674147 := bstep (se 1 (by rfl) ⟨2005610, by rfl⟩ : syracuseStep 2674147 = 4011221) B4011221
theorem B2141699 : Blo 1250443 2141699 := bstep (se 1 (by rfl) ⟨1606274, by rfl⟩ : syracuseStep 2141699 = 3212549) B3212549
theorem B3165713 : Blo 1250443 3165713 := bstep (se 2 (by rfl) ⟨1187142, by rfl⟩ : syracuseStep 3165713 = 2374285) B2374285
theorem B2813507 : Blo 1250443 2813507 := bstep (se 1 (by rfl) ⟨2110130, by rfl⟩ : syracuseStep 2813507 = 4220261) B4220261
theorem B3165763 : Blo 1250443 3165763 := bstep (se 1 (by rfl) ⟨2374322, by rfl⟩ : syracuseStep 3165763 = 4748645) B4748645
theorem B8023693 : Blo 1250443 8023693 := bstep (se 3 (by rfl) ⟨1504442, by rfl⟩ : syracuseStep 8023693 = 3008885) B3008885
theorem B4222637 : Blo 1250443 4222637 := bstep (se 3 (by rfl) ⟨791744, by rfl⟩ : syracuseStep 4222637 = 1583489) B1583489
theorem B1781443 : Blo 1250443 1781443 := bstep (se 1 (by rfl) ⟨1336082, by rfl⟩ : syracuseStep 1781443 = 2672165) B2672165
theorem B1355459 : Blo 1250443 1355459 := bstep (se 1 (by rfl) ⟨1016594, by rfl⟩ : syracuseStep 1355459 = 2033189) B2033189
theorem B3165905 : Blo 1250443 3165905 := bstep (se 2 (by rfl) ⟨1187214, by rfl⟩ : syracuseStep 3165905 = 2374429) B2374429
theorem B4222691 : Blo 1250443 4222691 := bstep (se 1 (by rfl) ⟨3167018, by rfl⟩ : syracuseStep 4222691 = 6334037) B6334037
theorem B6336305 : Blo 1250443 6336305 := bstep (se 2 (by rfl) ⟨2376114, by rfl⟩ : syracuseStep 6336305 = 4752229) B4752229
theorem B1584947 : Blo 1250443 1584947 := bstep (se 1 (by rfl) ⟨1188710, by rfl⟩ : syracuseStep 1584947 = 2377421) B2377421
theorem B2813777 : Blo 1250443 2813777 := bstep (se 2 (by rfl) ⟨1055166, by rfl⟩ : syracuseStep 2813777 = 2110333) B2110333
theorem B2813795 : Blo 1250443 2813795 := bstep (se 1 (by rfl) ⟨2110346, by rfl⟩ : syracuseStep 2813795 = 4220693) B4220693
theorem B1953649 : Blo 1250443 1953649 := bstep (se 2 (by rfl) ⟨732618, by rfl⟩ : syracuseStep 1953649 = 1465237) B1465237
theorem B4509553 : Blo 1250443 4509553 := bstep (se 2 (by rfl) ⟨1691082, by rfl⟩ : syracuseStep 4509553 = 3382165) B3382165
theorem B5345165 : Blo 1250443 5345165 := bstep (se 3 (by rfl) ⟨1002218, by rfl⟩ : syracuseStep 5345165 = 2004437) B2004437
theorem B9637829 : Blo 1250443 9637829 := bstep (se 4 (by rfl) ⟨903546, by rfl⟩ : syracuseStep 9637829 = 1807093) B1807093
theorem B4222961 : Blo 1250443 4222961 := bstep (se 2 (by rfl) ⟨1583610, by rfl⟩ : syracuseStep 4222961 = 3167221) B3167221
theorem B3805201 : Blo 1250443 3805201 := bstep (se 2 (by rfl) ⟨1426950, by rfl⟩ : syracuseStep 3805201 = 2853901) B2853901
theorem B1781779 : Blo 1250443 1781779 := bstep (se 1 (by rfl) ⟨1336334, by rfl⟩ : syracuseStep 1781779 = 2672669) B2672669
theorem B2142227 : Blo 1250443 2142227 := bstep (se 1 (by rfl) ⟨1606670, by rfl⟩ : syracuseStep 2142227 = 3213341) B3213341
theorem B4010093 : Blo 1250443 4010093 := bstep (se 3 (by rfl) ⟨751892, by rfl⟩ : syracuseStep 4010093 = 1503785) B1503785
theorem B2814065 : Blo 1250443 2814065 := bstep (se 2 (by rfl) ⟨1055274, by rfl⟩ : syracuseStep 2814065 = 2110549) B2110549
theorem B2814083 : Blo 1250443 2814083 := bstep (se 1 (by rfl) ⟨2110562, by rfl⟩ : syracuseStep 2814083 = 4221125) B4221125
theorem B2003105 : Blo 1250443 2003105 := bstep (se 2 (by rfl) ⟨751164, by rfl⟩ : syracuseStep 2003105 = 1502329) B1502329
theorem B1503443 : Blo 1250443 1503443 := bstep (se 1 (by rfl) ⟨1127582, by rfl⟩ : syracuseStep 1503443 = 2255165) B2255165
theorem B5345507 : Blo 1250443 5345507 := bstep (se 1 (by rfl) ⟨4009130, by rfl⟩ : syracuseStep 5345507 = 8018261) B8018261
theorem B2003233 : Blo 1250443 2003233 := bstep (se 2 (by rfl) ⟨751212, by rfl⟩ : syracuseStep 2003233 = 1502425) B1502425
theorem B2814353 : Blo 1250443 2814353 := bstep (se 2 (by rfl) ⟨1055382, by rfl⟩ : syracuseStep 2814353 = 2110765) B2110765
theorem B2814371 : Blo 1250443 2814371 := bstep (se 1 (by rfl) ⟨2110778, by rfl⟩ : syracuseStep 2814371 = 4221557) B4221557
theorem B7606705 : Blo 1250443 7606705 := bstep (se 2 (by rfl) ⟨2852514, by rfl⟩ : syracuseStep 7606705 = 5705029) B5705029
theorem B4813283 : Blo 1250443 4813283 := bstep (se 1 (by rfl) ⟨3609962, by rfl⟩ : syracuseStep 4813283 = 7219925) B7219925
theorem B11416049 : Blo 1250443 11416049 := bstep (se 2 (by rfl) ⟨4281018, by rfl⟩ : syracuseStep 11416049 = 8562037) B8562037
theorem B4223501 : Blo 1250443 4223501 := bstep (se 3 (by rfl) ⟨791906, by rfl⟩ : syracuseStep 4223501 = 1583813) B1583813
theorem B1782337 : Blo 1250443 1782337 := bstep (se 2 (by rfl) ⟨668376, by rfl⟩ : syracuseStep 1782337 = 1336753) B1336753
theorem B4223555 : Blo 1250443 4223555 := bstep (se 1 (by rfl) ⟨3167666, by rfl⟩ : syracuseStep 4223555 = 6335333) B6335333
theorem B1929793 : Blo 1250443 1929793 := bstep (se 2 (by rfl) ⟨723672, by rfl⟩ : syracuseStep 1929793 = 1447345) B1447345
theorem B1782371 : Blo 1250443 1782371 := bstep (se 1 (by rfl) ⟨1336778, by rfl⟩ : syracuseStep 1782371 = 2673557) B2673557
theorem B2003617 : Blo 1250443 2003617 := bstep (se 2 (by rfl) ⟨751356, by rfl⟩ : syracuseStep 2003617 = 1502713) B1502713
theorem B2814641 : Blo 1250443 2814641 := bstep (se 2 (by rfl) ⟨1055490, by rfl⟩ : syracuseStep 2814641 = 2110981) B2110981
theorem B3166897 : Blo 1250443 3166897 := bstep (se 2 (by rfl) ⟨1187586, by rfl⟩ : syracuseStep 3166897 = 2375173) B2375173
theorem B3011267 : Blo 1250443 3011267 := bstep (se 1 (by rfl) ⟨2258450, by rfl⟩ : syracuseStep 3011267 = 4516901) B4516901
theorem B2814659 : Blo 1250443 2814659 := bstep (se 1 (by rfl) ⟨2110994, by rfl⟩ : syracuseStep 2814659 = 4221989) B4221989
theorem B7123697 : Blo 1250443 7123697 := bstep (se 2 (by rfl) ⟨2671386, by rfl⟩ : syracuseStep 7123697 = 5342773) B5342773
theorem B2110225 : Blo 1250443 2110225 := bstep (se 2 (by rfl) ⟨791334, by rfl⟩ : syracuseStep 2110225 = 1582669) B1582669
theorem B2110259 : Blo 1250443 2110259 := bstep (se 1 (by rfl) ⟨1582694, by rfl⟩ : syracuseStep 2110259 = 3165389) B3165389
theorem B4281169 : Blo 1250443 4281169 := bstep (se 2 (by rfl) ⟨1605438, by rfl⟩ : syracuseStep 4281169 = 3210877) B3210877
theorem B4223825 : Blo 1250443 4223825 := bstep (se 2 (by rfl) ⟨1583934, by rfl⟩ : syracuseStep 4223825 = 3167869) B3167869
theorem B10695523 : Blo 1250443 10695523 := bstep (se 1 (by rfl) ⟨8021642, by rfl⟩ : syracuseStep 10695523 = 16043285) B16043285
theorem B1930115 : Blo 1250443 1930115 := bstep (se 1 (by rfl) ⟨1447586, by rfl⟩ : syracuseStep 1930115 = 2895173) B2895173
theorem B2003873 : Blo 1250443 2003873 := bstep (se 2 (by rfl) ⟨751452, by rfl⟩ : syracuseStep 2003873 = 1502905) B1502905
theorem B2110387 : Blo 1250443 2110387 := bstep (se 1 (by rfl) ⟨1582790, by rfl⟩ : syracuseStep 2110387 = 3165581) B3165581
theorem B3167171 : Blo 1250443 3167171 := bstep (se 1 (by rfl) ⟨2375378, by rfl⟩ : syracuseStep 3167171 = 4750757) B4750757
theorem B2814929 : Blo 1250443 2814929 := bstep (se 2 (by rfl) ⟨1055598, by rfl⟩ : syracuseStep 2814929 = 2111197) B2111197
theorem B2814947 : Blo 1250443 2814947 := bstep (se 1 (by rfl) ⟨2111210, by rfl⟩ : syracuseStep 2814947 = 4222421) B4222421
theorem B4510733 : Blo 1250443 4510733 := bstep (se 3 (by rfl) ⟨845762, by rfl⟩ : syracuseStep 4510733 = 1691525) B1691525
theorem B2110529 : Blo 1250443 2110529 := bstep (se 2 (by rfl) ⟨791448, by rfl⟩ : syracuseStep 2110529 = 1582897) B1582897
theorem B3167363 : Blo 1250443 3167363 := bstep (se 1 (by rfl) ⟨2375522, by rfl⟩ : syracuseStep 3167363 = 4751045) B4751045
theorem B1782929 : Blo 1250443 1782929 := bstep (se 2 (by rfl) ⟨668598, by rfl⟩ : syracuseStep 1782929 = 1337197) B1337197
theorem B1250451 : Blo 1250443 1250451 := bstep (se 1 (by rfl) ⟨937838, by rfl⟩ : syracuseStep 1250451 = 1875677) B1875677
theorem B1250467 : Blo 1250443 1250467 := bstep (se 1 (by rfl) ⟨937850, by rfl⟩ : syracuseStep 1250467 = 1875701) B1875701
theorem B1250483 : Blo 1250443 1250483 := bstep (se 1 (by rfl) ⟨937862, by rfl⟩ : syracuseStep 1250483 = 1875725) B1875725
theorem B2110657 : Blo 1250443 2110657 := bstep (se 2 (by rfl) ⟨791496, by rfl⟩ : syracuseStep 2110657 = 1582993) B1582993
theorem B1250499 : Blo 1250443 1250499 := bstep (se 1 (by rfl) ⟨937874, by rfl⟩ : syracuseStep 1250499 = 1875749) B1875749
theorem B1250515 : Blo 1250443 1250515 := bstep (se 1 (by rfl) ⟨937886, by rfl⟩ : syracuseStep 1250515 = 1875773) B1875773
theorem B1783009 : Blo 1250443 1783009 := bstep (se 2 (by rfl) ⟨668628, by rfl⟩ : syracuseStep 1783009 = 1337257) B1337257
theorem B1250531 : Blo 1250443 1250531 := bstep (se 1 (by rfl) ⟨937898, by rfl⟩ : syracuseStep 1250531 = 1875797) B1875797
theorem B2110691 : Blo 1250443 2110691 := bstep (se 1 (by rfl) ⟨1583018, by rfl⟩ : syracuseStep 2110691 = 3166037) B3166037
theorem B6337763 : Blo 1250443 6337763 := bstep (se 1 (by rfl) ⟨4753322, by rfl⟩ : syracuseStep 6337763 = 9506645) B9506645
theorem B2815217 : Blo 1250443 2815217 := bstep (se 2 (by rfl) ⟨1055706, by rfl⟩ : syracuseStep 2815217 = 2111413) B2111413
theorem B1250547 : Blo 1250443 1250547 := bstep (se 1 (by rfl) ⟨937910, by rfl⟩ : syracuseStep 1250547 = 1875821) B1875821
theorem B1250563 : Blo 1250443 1250563 := bstep (se 1 (by rfl) ⟨937922, by rfl⟩ : syracuseStep 1250563 = 1875845) B1875845
theorem B2815235 : Blo 1250443 2815235 := bstep (se 1 (by rfl) ⟨2111426, by rfl⟩ : syracuseStep 2815235 = 4222853) B4222853
theorem B1250579 : Blo 1250443 1250579 := bstep (se 1 (by rfl) ⟨937934, by rfl⟩ : syracuseStep 1250579 = 1875869) B1875869
theorem B1250595 : Blo 1250443 1250595 := bstep (se 1 (by rfl) ⟨937946, by rfl⟩ : syracuseStep 1250595 = 1875893) B1875893
theorem B1250611 : Blo 1250443 1250611 := bstep (se 1 (by rfl) ⟨937958, by rfl⟩ : syracuseStep 1250611 = 1875917) B1875917
theorem B1250627 : Blo 1250443 1250627 := bstep (se 1 (by rfl) ⟨937970, by rfl⟩ : syracuseStep 1250627 = 1875941) B1875941
theorem B1250643 : Blo 1250443 1250643 := bstep (se 1 (by rfl) ⟨937982, by rfl⟩ : syracuseStep 1250643 = 1875965) B1875965
theorem B1250659 : Blo 1250443 1250659 := bstep (se 1 (by rfl) ⟨937994, by rfl⟩ : syracuseStep 1250659 = 1875989) B1875989
theorem B2110819 : Blo 1250443 2110819 := bstep (se 1 (by rfl) ⟨1583114, by rfl⟩ : syracuseStep 2110819 = 3166229) B3166229
theorem B4224365 : Blo 1250443 4224365 := bstep (se 3 (by rfl) ⟨792068, by rfl⟩ : syracuseStep 4224365 = 1584137) B1584137
theorem B1250675 : Blo 1250443 1250675 := bstep (se 1 (by rfl) ⟨938006, by rfl⟩ : syracuseStep 1250675 = 1876013) B1876013
theorem B1250691 : Blo 1250443 1250691 := bstep (se 1 (by rfl) ⟨938018, by rfl⟩ : syracuseStep 1250691 = 1876037) B1876037
theorem B1250707 : Blo 1250443 1250707 := bstep (se 1 (by rfl) ⟨938030, by rfl⟩ : syracuseStep 1250707 = 1876061) B1876061
theorem B1250723 : Blo 1250443 1250723 := bstep (se 1 (by rfl) ⟨938042, by rfl⟩ : syracuseStep 1250723 = 1876085) B1876085
theorem B4224419 : Blo 1250443 4224419 := bstep (se 1 (by rfl) ⟨3168314, by rfl⟩ : syracuseStep 4224419 = 6336629) B6336629
theorem B4011437 : Blo 1250443 4011437 := bstep (se 3 (by rfl) ⟨752144, by rfl⟩ : syracuseStep 4011437 = 1504289) B1504289
theorem B3560881 : Blo 1250443 3560881 := bstep (se 2 (by rfl) ⟨1335330, by rfl⟩ : syracuseStep 3560881 = 2670661) B2670661
theorem B1250739 : Blo 1250443 1250739 := bstep (se 1 (by rfl) ⟨938054, by rfl⟩ : syracuseStep 1250739 = 1876109) B1876109
theorem B1250755 : Blo 1250443 1250755 := bstep (se 1 (by rfl) ⟨938066, by rfl⟩ : syracuseStep 1250755 = 1876133) B1876133
theorem B6763981 : Blo 1250443 6763981 := bstep (se 3 (by rfl) ⟨1268246, by rfl⟩ : syracuseStep 6763981 = 2536493) B2536493
theorem B1250771 : Blo 1250443 1250771 := bstep (se 1 (by rfl) ⟨938078, by rfl⟩ : syracuseStep 1250771 = 1876157) B1876157
theorem B1250787 : Blo 1250443 1250787 := bstep (se 1 (by rfl) ⟨938090, by rfl⟩ : syracuseStep 1250787 = 1876181) B1876181
theorem B2110961 : Blo 1250443 2110961 := bstep (se 2 (by rfl) ⟨791610, by rfl⟩ : syracuseStep 2110961 = 1583221) B1583221
theorem B1250803 : Blo 1250443 1250803 := bstep (se 1 (by rfl) ⟨938102, by rfl⟩ : syracuseStep 1250803 = 1876205) B1876205
theorem B1250819 : Blo 1250443 1250819 := bstep (se 1 (by rfl) ⟨938114, by rfl⟩ : syracuseStep 1250819 = 1876229) B1876229
theorem B4748813 : Blo 1250443 4748813 := bstep (se 3 (by rfl) ⟨890402, by rfl⟩ : syracuseStep 4748813 = 1780805) B1780805
theorem B2815505 : Blo 1250443 2815505 := bstep (se 2 (by rfl) ⟨1055814, by rfl⟩ : syracuseStep 2815505 = 2111629) B2111629
theorem B1250835 : Blo 1250443 1250835 := bstep (se 1 (by rfl) ⟨938126, by rfl⟩ : syracuseStep 1250835 = 1876253) B1876253
theorem B1250851 : Blo 1250443 1250851 := bstep (se 1 (by rfl) ⟨938138, by rfl⟩ : syracuseStep 1250851 = 1876277) B1876277
theorem B2815523 : Blo 1250443 2815523 := bstep (se 1 (by rfl) ⟨2111642, by rfl⟩ : syracuseStep 2815523 = 4223285) B4223285
theorem B1250867 : Blo 1250443 1250867 := bstep (se 1 (by rfl) ⟨938150, by rfl⟩ : syracuseStep 1250867 = 1876301) B1876301
theorem B1250883 : Blo 1250443 1250883 := bstep (se 1 (by rfl) ⟨938162, by rfl⟩ : syracuseStep 1250883 = 1876325) B1876325
theorem B1250899 : Blo 1250443 1250899 := bstep (se 1 (by rfl) ⟨938174, by rfl⟩ : syracuseStep 1250899 = 1876349) B1876349
theorem B1250915 : Blo 1250443 1250915 := bstep (se 1 (by rfl) ⟨938186, by rfl⟩ : syracuseStep 1250915 = 1876373) B1876373
theorem B2111089 : Blo 1250443 2111089 := bstep (se 2 (by rfl) ⟨791658, by rfl⟩ : syracuseStep 2111089 = 1583317) B1583317
theorem B1250931 : Blo 1250443 1250931 := bstep (se 1 (by rfl) ⟨938198, by rfl⟩ : syracuseStep 1250931 = 1876397) B1876397
theorem B1250947 : Blo 1250443 1250947 := bstep (se 1 (by rfl) ⟨938210, by rfl⟩ : syracuseStep 1250947 = 1876421) B1876421
theorem B6420109 : Blo 1250443 6420109 := bstep (se 3 (by rfl) ⟨1203770, by rfl⟩ : syracuseStep 6420109 = 2407541) B2407541
theorem B1250963 : Blo 1250443 1250963 := bstep (se 1 (by rfl) ⟨938222, by rfl⟩ : syracuseStep 1250963 = 1876445) B1876445
theorem B2111123 : Blo 1250443 2111123 := bstep (se 1 (by rfl) ⟨1583342, by rfl⟩ : syracuseStep 2111123 = 3166685) B3166685
theorem B1250979 : Blo 1250443 1250979 := bstep (se 1 (by rfl) ⟨938234, by rfl⟩ : syracuseStep 1250979 = 1876469) B1876469
theorem B4224689 : Blo 1250443 4224689 := bstep (se 2 (by rfl) ⟨1584258, by rfl⟩ : syracuseStep 4224689 = 3168517) B3168517
theorem B1250995 : Blo 1250443 1250995 := bstep (se 1 (by rfl) ⟨938246, by rfl⟩ : syracuseStep 1250995 = 1876493) B1876493
theorem B3561155 : Blo 1250443 3561155 := bstep (se 1 (by rfl) ⟨2670866, by rfl⟩ : syracuseStep 3561155 = 5341733) B5341733
theorem B1251011 : Blo 1250443 1251011 := bstep (se 1 (by rfl) ⟨938258, by rfl⟩ : syracuseStep 1251011 = 1876517) B1876517
theorem B1251027 : Blo 1250443 1251027 := bstep (se 1 (by rfl) ⟨938270, by rfl⟩ : syracuseStep 1251027 = 1876541) B1876541
theorem B1251043 : Blo 1250443 1251043 := bstep (se 1 (by rfl) ⟨938282, by rfl⟩ : syracuseStep 1251043 = 1876565) B1876565
theorem B1251059 : Blo 1250443 1251059 := bstep (se 1 (by rfl) ⟨938294, by rfl⟩ : syracuseStep 1251059 = 1876589) B1876589
theorem B1251075 : Blo 1250443 1251075 := bstep (se 1 (by rfl) ⟨938306, by rfl⟩ : syracuseStep 1251075 = 1876613) B1876613
theorem B1251091 : Blo 1250443 1251091 := bstep (se 1 (by rfl) ⟨938318, by rfl⟩ : syracuseStep 1251091 = 1876637) B1876637
theorem B2111251 : Blo 1250443 2111251 := bstep (se 1 (by rfl) ⟨1583438, by rfl⟩ : syracuseStep 2111251 = 3166877) B3166877
theorem B1251107 : Blo 1250443 1251107 := bstep (se 1 (by rfl) ⟨938330, by rfl⟩ : syracuseStep 1251107 = 1876661) B1876661
theorem B2815793 : Blo 1250443 2815793 := bstep (se 2 (by rfl) ⟨1055922, by rfl⟩ : syracuseStep 2815793 = 2111845) B2111845
theorem B1251123 : Blo 1250443 1251123 := bstep (se 1 (by rfl) ⟨938342, by rfl⟩ : syracuseStep 1251123 = 1876685) B1876685
theorem B1251139 : Blo 1250443 1251139 := bstep (se 1 (by rfl) ⟨938354, by rfl⟩ : syracuseStep 1251139 = 1876709) B1876709
theorem B2815811 : Blo 1250443 2815811 := bstep (se 1 (by rfl) ⟨2111858, by rfl⟩ : syracuseStep 2815811 = 4223717) B4223717
theorem B1406803 : Blo 1250443 1406803 := bstep (se 1 (by rfl) ⟨1055102, by rfl⟩ : syracuseStep 1406803 = 2110205) B2110205
theorem B1251155 : Blo 1250443 1251155 := bstep (se 1 (by rfl) ⟨938366, by rfl⟩ : syracuseStep 1251155 = 1876733) B1876733
theorem B1251171 : Blo 1250443 1251171 := bstep (se 1 (by rfl) ⟨938378, by rfl⟩ : syracuseStep 1251171 = 1876757) B1876757
theorem B1251187 : Blo 1250443 1251187 := bstep (se 1 (by rfl) ⟨938390, by rfl⟩ : syracuseStep 1251187 = 1876781) B1876781
theorem B3561347 : Blo 1250443 3561347 := bstep (se 1 (by rfl) ⟨2671010, by rfl⟩ : syracuseStep 3561347 = 5342021) B5342021
theorem B1251203 : Blo 1250443 1251203 := bstep (se 1 (by rfl) ⟨938402, by rfl⟩ : syracuseStep 1251203 = 1876805) B1876805
theorem B1251219 : Blo 1250443 1251219 := bstep (se 1 (by rfl) ⟨938414, by rfl⟩ : syracuseStep 1251219 = 1876829) B1876829
theorem B2111393 : Blo 1250443 2111393 := bstep (se 2 (by rfl) ⟨791772, by rfl⟩ : syracuseStep 2111393 = 1583545) B1583545
theorem B1251235 : Blo 1250443 1251235 := bstep (se 1 (by rfl) ⟨938426, by rfl⟩ : syracuseStep 1251235 = 1876853) B1876853
theorem B1251251 : Blo 1250443 1251251 := bstep (se 1 (by rfl) ⟨938438, by rfl⟩ : syracuseStep 1251251 = 1876877) B1876877
theorem B1267651 : Blo 1250443 1267651 := bstep (se 1 (by rfl) ⟨950738, by rfl⟩ : syracuseStep 1267651 = 1901477) B1901477
theorem B1251267 : Blo 1250443 1251267 := bstep (se 1 (by rfl) ⟨938450, by rfl⟩ : syracuseStep 1251267 = 1876901) B1876901
theorem B1251283 : Blo 1250443 1251283 := bstep (se 1 (by rfl) ⟨938462, by rfl⟩ : syracuseStep 1251283 = 1876925) B1876925
theorem B1406947 : Blo 1250443 1406947 := bstep (se 1 (by rfl) ⟨1055210, by rfl⟩ : syracuseStep 1406947 = 2110421) B2110421
theorem B1251299 : Blo 1250443 1251299 := bstep (se 1 (by rfl) ⟨938474, by rfl⟩ : syracuseStep 1251299 = 1876949) B1876949
theorem B1251315 : Blo 1250443 1251315 := bstep (se 1 (by rfl) ⟨938486, by rfl⟩ : syracuseStep 1251315 = 1876973) B1876973
theorem B1251331 : Blo 1250443 1251331 := bstep (se 1 (by rfl) ⟨938498, by rfl⟩ : syracuseStep 1251331 = 1876997) B1876997
theorem B6338573 : Blo 1250443 6338573 := bstep (se 3 (by rfl) ⟨1188482, by rfl⟩ : syracuseStep 6338573 = 2376965) B2376965
theorem B1251347 : Blo 1250443 1251347 := bstep (se 1 (by rfl) ⟨938510, by rfl⟩ : syracuseStep 1251347 = 1877021) B1877021
theorem B2111521 : Blo 1250443 2111521 := bstep (se 2 (by rfl) ⟨791820, by rfl⟩ : syracuseStep 2111521 = 1583641) B1583641
theorem B1251363 : Blo 1250443 1251363 := bstep (se 1 (by rfl) ⟨938522, by rfl⟩ : syracuseStep 1251363 = 1877045) B1877045
theorem B3168305 : Blo 1250443 3168305 := bstep (se 2 (by rfl) ⟨1188114, by rfl⟩ : syracuseStep 3168305 = 2376229) B2376229
theorem B1251379 : Blo 1250443 1251379 := bstep (se 1 (by rfl) ⟨938534, by rfl⟩ : syracuseStep 1251379 = 1877069) B1877069
theorem B2111555 : Blo 1250443 2111555 := bstep (se 1 (by rfl) ⟨1583666, by rfl⟩ : syracuseStep 2111555 = 3167333) B3167333
theorem B1251395 : Blo 1250443 1251395 := bstep (se 1 (by rfl) ⟨938546, by rfl⟩ : syracuseStep 1251395 = 1877093) B1877093
theorem B2816081 : Blo 1250443 2816081 := bstep (se 2 (by rfl) ⟨1056030, by rfl⟩ : syracuseStep 2816081 = 2112061) B2112061
theorem B1251411 : Blo 1250443 1251411 := bstep (se 1 (by rfl) ⟨938558, by rfl⟩ : syracuseStep 1251411 = 1877117) B1877117
theorem B1251427 : Blo 1250443 1251427 := bstep (se 1 (by rfl) ⟨938570, by rfl⟩ : syracuseStep 1251427 = 1877141) B1877141
theorem B2816099 : Blo 1250443 2816099 := bstep (se 1 (by rfl) ⟨2112074, by rfl⟩ : syracuseStep 2816099 = 4224149) B4224149
theorem B3168355 : Blo 1250443 3168355 := bstep (se 1 (by rfl) ⟨2376266, by rfl⟩ : syracuseStep 3168355 = 4752533) B4752533
theorem B1407091 : Blo 1250443 1407091 := bstep (se 1 (by rfl) ⟨1055318, by rfl⟩ : syracuseStep 1407091 = 2110637) B2110637
theorem B1251443 : Blo 1250443 1251443 := bstep (se 1 (by rfl) ⟨938582, by rfl⟩ : syracuseStep 1251443 = 1877165) B1877165
theorem B1251459 : Blo 1250443 1251459 := bstep (se 1 (by rfl) ⟨938594, by rfl⟩ : syracuseStep 1251459 = 1877189) B1877189
theorem B6092941 : Blo 1250443 6092941 := bstep (se 3 (by rfl) ⟨1142426, by rfl⟩ : syracuseStep 6092941 = 2284853) B2284853
theorem B9500813 : Blo 1250443 9500813 := bstep (se 3 (by rfl) ⟨1781402, by rfl⟩ : syracuseStep 9500813 = 3562805) B3562805
theorem B1251475 : Blo 1250443 1251475 := bstep (se 1 (by rfl) ⟨938606, by rfl⟩ : syracuseStep 1251475 = 1877213) B1877213
theorem B7125155 : Blo 1250443 7125155 := bstep (se 1 (by rfl) ⟨5343866, by rfl⟩ : syracuseStep 7125155 = 10687733) B10687733
theorem B1251491 : Blo 1250443 1251491 := bstep (se 1 (by rfl) ⟨938618, by rfl⟩ : syracuseStep 1251491 = 1877237) B1877237
theorem B1251507 : Blo 1250443 1251507 := bstep (se 1 (by rfl) ⟨938630, by rfl⟩ : syracuseStep 1251507 = 1877261) B1877261
theorem B16046261 : Blo 1250443 16046261 := bstep (se 5 (by rfl) ⟨752168, by rfl⟩ : syracuseStep 16046261 = 1504337) B1504337
theorem B2111683 : Blo 1250443 2111683 := bstep (se 1 (by rfl) ⟨1583762, by rfl⟩ : syracuseStep 2111683 = 3167525) B3167525
theorem B1251523 : Blo 1250443 1251523 := bstep (se 1 (by rfl) ⟨938642, by rfl⟩ : syracuseStep 1251523 = 1877285) B1877285
theorem B4225229 : Blo 1250443 4225229 := bstep (se 3 (by rfl) ⟨792230, by rfl⟩ : syracuseStep 4225229 = 1584461) B1584461
theorem B1251539 : Blo 1250443 1251539 := bstep (se 1 (by rfl) ⟨938654, by rfl⟩ : syracuseStep 1251539 = 1877309) B1877309
theorem B1251555 : Blo 1250443 1251555 := bstep (se 1 (by rfl) ⟨938666, by rfl⟩ : syracuseStep 1251555 = 1877333) B1877333
theorem B3168497 : Blo 1250443 3168497 := bstep (se 2 (by rfl) ⟨1188186, by rfl⟩ : syracuseStep 3168497 = 2376373) B2376373
theorem B1251571 : Blo 1250443 1251571 := bstep (se 1 (by rfl) ⟨938678, by rfl⟩ : syracuseStep 1251571 = 1877357) B1877357
theorem B1407235 : Blo 1250443 1407235 := bstep (se 1 (by rfl) ⟨1055426, by rfl⟩ : syracuseStep 1407235 = 2110853) B2110853
theorem B1251587 : Blo 1250443 1251587 := bstep (se 1 (by rfl) ⟨938690, by rfl⟩ : syracuseStep 1251587 = 1877381) B1877381
theorem B4225283 : Blo 1250443 4225283 := bstep (se 1 (by rfl) ⟨3168962, by rfl⟩ : syracuseStep 4225283 = 6337925) B6337925
theorem B1251603 : Blo 1250443 1251603 := bstep (se 1 (by rfl) ⟨938702, by rfl⟩ : syracuseStep 1251603 = 1877405) B1877405
theorem B1251619 : Blo 1250443 1251619 := bstep (se 1 (by rfl) ⟨938714, by rfl⟩ : syracuseStep 1251619 = 1877429) B1877429
theorem B2005283 : Blo 1250443 2005283 := bstep (se 1 (by rfl) ⟨1503962, by rfl⟩ : syracuseStep 2005283 = 3007925) B3007925
theorem B4749617 : Blo 1250443 4749617 := bstep (se 2 (by rfl) ⟨1781106, by rfl⟩ : syracuseStep 4749617 = 3562213) B3562213
theorem B1251635 : Blo 1250443 1251635 := bstep (se 1 (by rfl) ⟨938726, by rfl⟩ : syracuseStep 1251635 = 1877453) B1877453
theorem B1251651 : Blo 1250443 1251651 := bstep (se 1 (by rfl) ⟨938738, by rfl⟩ : syracuseStep 1251651 = 1877477) B1877477
theorem B3381581 : Blo 1250443 3381581 := bstep (se 3 (by rfl) ⟨634046, by rfl⟩ : syracuseStep 3381581 = 1268093) B1268093
theorem B2111825 : Blo 1250443 2111825 := bstep (se 2 (by rfl) ⟨791934, by rfl⟩ : syracuseStep 2111825 = 1583869) B1583869
theorem B1251667 : Blo 1250443 1251667 := bstep (se 1 (by rfl) ⟨938750, by rfl⟩ : syracuseStep 1251667 = 1877501) B1877501
theorem B1251683 : Blo 1250443 1251683 := bstep (se 1 (by rfl) ⟨938762, by rfl⟩ : syracuseStep 1251683 = 1877525) B1877525
theorem B2816369 : Blo 1250443 2816369 := bstep (se 2 (by rfl) ⟨1056138, by rfl⟩ : syracuseStep 2816369 = 2112277) B2112277
theorem B1251699 : Blo 1250443 1251699 := bstep (se 1 (by rfl) ⟨938774, by rfl⟩ : syracuseStep 1251699 = 1877549) B1877549
theorem B2374019 : Blo 1250443 2374019 := bstep (se 1 (by rfl) ⟨1780514, by rfl⟩ : syracuseStep 2374019 = 3561029) B3561029
theorem B1251715 : Blo 1250443 1251715 := bstep (se 1 (by rfl) ⟨938786, by rfl⟩ : syracuseStep 1251715 = 1877573) B1877573
theorem B2816387 : Blo 1250443 2816387 := bstep (se 1 (by rfl) ⟨2112290, by rfl⟩ : syracuseStep 2816387 = 4224581) B4224581
theorem B9632141 : Blo 1250443 9632141 := bstep (se 3 (by rfl) ⟨1806026, by rfl⟩ : syracuseStep 9632141 = 3612053) B3612053
theorem B1407379 : Blo 1250443 1407379 := bstep (se 1 (by rfl) ⟨1055534, by rfl⟩ : syracuseStep 1407379 = 2111069) B2111069
theorem B1251731 : Blo 1250443 1251731 := bstep (se 1 (by rfl) ⟨938798, by rfl⟩ : syracuseStep 1251731 = 1877597) B1877597
theorem B1251747 : Blo 1250443 1251747 := bstep (se 1 (by rfl) ⟨938810, by rfl⟩ : syracuseStep 1251747 = 1877621) B1877621
theorem B1251763 : Blo 1250443 1251763 := bstep (se 1 (by rfl) ⟨938822, by rfl⟩ : syracuseStep 1251763 = 1877645) B1877645
theorem B1251779 : Blo 1250443 1251779 := bstep (se 1 (by rfl) ⟨938834, by rfl⟩ : syracuseStep 1251779 = 1877669) B1877669
theorem B2111953 : Blo 1250443 2111953 := bstep (se 2 (by rfl) ⟨791982, by rfl⟩ : syracuseStep 2111953 = 1583965) B1583965
theorem B1251795 : Blo 1250443 1251795 := bstep (se 1 (by rfl) ⟨938846, by rfl⟩ : syracuseStep 1251795 = 1877693) B1877693
theorem B21371363 : Blo 1250443 21371363 := bstep (se 1 (by rfl) ⟨16028522, by rfl⟩ : syracuseStep 21371363 = 32057045) B32057045
theorem B1251811 : Blo 1250443 1251811 := bstep (se 1 (by rfl) ⟨938858, by rfl⟩ : syracuseStep 1251811 = 1877717) B1877717
theorem B2111987 : Blo 1250443 2111987 := bstep (se 1 (by rfl) ⟨1583990, by rfl⟩ : syracuseStep 2111987 = 3167981) B3167981
theorem B1251827 : Blo 1250443 1251827 := bstep (se 1 (by rfl) ⟨938870, by rfl⟩ : syracuseStep 1251827 = 1877741) B1877741
theorem B1251843 : Blo 1250443 1251843 := bstep (se 1 (by rfl) ⟨938882, by rfl⟩ : syracuseStep 1251843 = 1877765) B1877765
theorem B7608845 : Blo 1250443 7608845 := bstep (se 3 (by rfl) ⟨1426658, by rfl⟩ : syracuseStep 7608845 = 2853317) B2853317
theorem B4225553 : Blo 1250443 4225553 := bstep (se 2 (by rfl) ⟨1584582, by rfl⟩ : syracuseStep 4225553 = 3169165) B3169165
theorem B1251859 : Blo 1250443 1251859 := bstep (se 1 (by rfl) ⟨938894, by rfl⟩ : syracuseStep 1251859 = 1877789) B1877789
theorem B1407523 : Blo 1250443 1407523 := bstep (se 1 (by rfl) ⟨1055642, by rfl⟩ : syracuseStep 1407523 = 2111285) B2111285
theorem B1251875 : Blo 1250443 1251875 := bstep (se 1 (by rfl) ⟨938906, by rfl⟩ : syracuseStep 1251875 = 1877813) B1877813
theorem B4815409 : Blo 1250443 4815409 := bstep (se 2 (by rfl) ⟨1805778, by rfl⟩ : syracuseStep 4815409 = 3611557) B3611557
theorem B1251891 : Blo 1250443 1251891 := bstep (se 1 (by rfl) ⟨938918, by rfl⟩ : syracuseStep 1251891 = 1877837) B1877837
theorem B1251907 : Blo 1250443 1251907 := bstep (se 1 (by rfl) ⟨938930, by rfl⟩ : syracuseStep 1251907 = 1877861) B1877861
theorem B1251923 : Blo 1250443 1251923 := bstep (se 1 (by rfl) ⟨938942, by rfl⟩ : syracuseStep 1251923 = 1877885) B1877885
theorem B1251939 : Blo 1250443 1251939 := bstep (se 1 (by rfl) ⟨938954, by rfl⟩ : syracuseStep 1251939 = 1877909) B1877909
theorem B10844771 : Blo 1250443 10844771 := bstep (se 1 (by rfl) ⟨8133578, by rfl⟩ : syracuseStep 10844771 = 16267157) B16267157
theorem B3005041 : Blo 1250443 3005041 := bstep (se 2 (by rfl) ⟨1126890, by rfl⟩ : syracuseStep 3005041 = 2253781) B2253781
theorem B2112115 : Blo 1250443 2112115 := bstep (se 1 (by rfl) ⟨1584086, by rfl⟩ : syracuseStep 2112115 = 3168173) B3168173
theorem B1251955 : Blo 1250443 1251955 := bstep (se 1 (by rfl) ⟨938966, by rfl⟩ : syracuseStep 1251955 = 1877933) B1877933
theorem B1251971 : Blo 1250443 1251971 := bstep (se 1 (by rfl) ⟨938978, by rfl⟩ : syracuseStep 1251971 = 1877957) B1877957
theorem B2816657 : Blo 1250443 2816657 := bstep (se 2 (by rfl) ⟨1056246, by rfl⟩ : syracuseStep 2816657 = 2112493) B2112493
theorem B1251987 : Blo 1250443 1251987 := bstep (se 1 (by rfl) ⟨938990, by rfl⟩ : syracuseStep 1251987 = 1877981) B1877981
theorem B2816675 : Blo 1250443 2816675 := bstep (se 1 (by rfl) ⟨2112506, by rfl⟩ : syracuseStep 2816675 = 4225013) B4225013
theorem B1252003 : Blo 1250443 1252003 := bstep (se 1 (by rfl) ⟨939002, by rfl⟩ : syracuseStep 1252003 = 1878005) B1878005
theorem B3562157 : Blo 1250443 3562157 := bstep (se 3 (by rfl) ⟨667904, by rfl⟩ : syracuseStep 3562157 = 1335809) B1335809
theorem B1407667 : Blo 1250443 1407667 := bstep (se 1 (by rfl) ⟨1055750, by rfl⟩ : syracuseStep 1407667 = 2111501) B2111501
theorem B1252019 : Blo 1250443 1252019 := bstep (se 1 (by rfl) ⟨939014, by rfl⟩ : syracuseStep 1252019 = 1878029) B1878029
theorem B1252035 : Blo 1250443 1252035 := bstep (se 1 (by rfl) ⟨939026, by rfl⟩ : syracuseStep 1252035 = 1878053) B1878053
theorem B1252051 : Blo 1250443 1252051 := bstep (se 1 (by rfl) ⟨939038, by rfl⟩ : syracuseStep 1252051 = 1878077) B1878077
theorem B1252067 : Blo 1250443 1252067 := bstep (se 1 (by rfl) ⟨939050, by rfl⟩ : syracuseStep 1252067 = 1878101) B1878101
theorem B6331121 : Blo 1250443 6331121 := bstep (se 2 (by rfl) ⟨2374170, by rfl⟩ : syracuseStep 6331121 = 4748341) B4748341
theorem B1252083 : Blo 1250443 1252083 := bstep (se 1 (by rfl) ⟨939062, by rfl⟩ : syracuseStep 1252083 = 1878125) B1878125
theorem B2112257 : Blo 1250443 2112257 := bstep (se 2 (by rfl) ⟨792096, by rfl⟩ : syracuseStep 2112257 = 1584193) B1584193
theorem B1252099 : Blo 1250443 1252099 := bstep (se 1 (by rfl) ⟨939074, by rfl⟩ : syracuseStep 1252099 = 1878149) B1878149
theorem B1252115 : Blo 1250443 1252115 := bstep (se 1 (by rfl) ⟨939086, by rfl⟩ : syracuseStep 1252115 = 1878173) B1878173
theorem B1252131 : Blo 1250443 1252131 := bstep (se 1 (by rfl) ⟨939098, by rfl⟩ : syracuseStep 1252131 = 1878197) B1878197
theorem B1252147 : Blo 1250443 1252147 := bstep (se 1 (by rfl) ⟨939110, by rfl⟩ : syracuseStep 1252147 = 1878221) B1878221
theorem B1407811 : Blo 1250443 1407811 := bstep (se 1 (by rfl) ⟨1055858, by rfl⟩ : syracuseStep 1407811 = 2111717) B2111717
theorem B1252163 : Blo 1250443 1252163 := bstep (se 1 (by rfl) ⟨939122, by rfl⟩ : syracuseStep 1252163 = 1878245) B1878245
theorem B1252179 : Blo 1250443 1252179 := bstep (se 1 (by rfl) ⟨939134, by rfl⟩ : syracuseStep 1252179 = 1878269) B1878269
theorem B3562339 : Blo 1250443 3562339 := bstep (se 1 (by rfl) ⟨2671754, by rfl⟩ : syracuseStep 3562339 = 5343509) B5343509
theorem B1252195 : Blo 1250443 1252195 := bstep (se 1 (by rfl) ⟨939146, by rfl⟩ : syracuseStep 1252195 = 1878293) B1878293
theorem B1252211 : Blo 1250443 1252211 := bstep (se 1 (by rfl) ⟨939158, by rfl⟩ : syracuseStep 1252211 = 1878317) B1878317
theorem B2112385 : Blo 1250443 2112385 := bstep (se 2 (by rfl) ⟨792144, by rfl⟩ : syracuseStep 2112385 = 1584289) B1584289
theorem B1252227 : Blo 1250443 1252227 := bstep (se 1 (by rfl) ⟨939170, by rfl⟩ : syracuseStep 1252227 = 1878341) B1878341
theorem B1252243 : Blo 1250443 1252243 := bstep (se 1 (by rfl) ⟨939182, by rfl⟩ : syracuseStep 1252243 = 1878365) B1878365
theorem B2112419 : Blo 1250443 2112419 := bstep (se 1 (by rfl) ⟨1584314, by rfl⟩ : syracuseStep 2112419 = 3168629) B3168629
theorem B1252259 : Blo 1250443 1252259 := bstep (se 1 (by rfl) ⟨939194, by rfl⟩ : syracuseStep 1252259 = 1878389) B1878389
theorem B2816945 : Blo 1250443 2816945 := bstep (se 2 (by rfl) ⟨1056354, by rfl⟩ : syracuseStep 2816945 = 2112709) B2112709
theorem B1252275 : Blo 1250443 1252275 := bstep (se 1 (by rfl) ⟨939206, by rfl⟩ : syracuseStep 1252275 = 1878413) B1878413
theorem B2816963 : Blo 1250443 2816963 := bstep (se 1 (by rfl) ⟨2112722, by rfl⟩ : syracuseStep 2816963 = 4225445) B4225445
theorem B1252291 : Blo 1250443 1252291 := bstep (se 1 (by rfl) ⟨939218, by rfl⟩ : syracuseStep 1252291 = 1878437) B1878437
theorem B31267781 : Blo 1250443 31267781 := bstep (se 4 (by rfl) ⟨2931354, by rfl⟩ : syracuseStep 31267781 = 5862709) B5862709
theorem B4750285 : Blo 1250443 4750285 := bstep (se 3 (by rfl) ⟨890678, by rfl⟩ : syracuseStep 4750285 = 1781357) B1781357
theorem B1407955 : Blo 1250443 1407955 := bstep (se 1 (by rfl) ⟨1055966, by rfl⟩ : syracuseStep 1407955 = 2111933) B2111933
theorem B1252307 : Blo 1250443 1252307 := bstep (se 1 (by rfl) ⟨939230, by rfl⟩ : syracuseStep 1252307 = 1878461) B1878461
theorem B1252323 : Blo 1250443 1252323 := bstep (se 1 (by rfl) ⟨939242, by rfl⟩ : syracuseStep 1252323 = 1878485) B1878485
theorem B1252339 : Blo 1250443 1252339 := bstep (se 1 (by rfl) ⟨939254, by rfl⟩ : syracuseStep 1252339 = 1878509) B1878509
theorem B1252355 : Blo 1250443 1252355 := bstep (se 1 (by rfl) ⟨939266, by rfl⟩ : syracuseStep 1252355 = 1878533) B1878533
theorem B4062221 : Blo 1250443 4062221 := bstep (se 3 (by rfl) ⟨761666, by rfl⟩ : syracuseStep 4062221 = 1523333) B1523333
theorem B1252371 : Blo 1250443 1252371 := bstep (se 1 (by rfl) ⟨939278, by rfl⟩ : syracuseStep 1252371 = 1878557) B1878557
theorem B2112547 : Blo 1250443 2112547 := bstep (se 1 (by rfl) ⟨1584410, by rfl⟩ : syracuseStep 2112547 = 3168821) B3168821
theorem B1252387 : Blo 1250443 1252387 := bstep (se 1 (by rfl) ⟨939290, by rfl⟩ : syracuseStep 1252387 = 1878581) B1878581
theorem B4226093 : Blo 1250443 4226093 := bstep (se 3 (by rfl) ⟨792392, by rfl⟩ : syracuseStep 4226093 = 1584785) B1584785
theorem B1252403 : Blo 1250443 1252403 := bstep (se 1 (by rfl) ⟨939302, by rfl⟩ : syracuseStep 1252403 = 1878605) B1878605
theorem B1252419 : Blo 1250443 1252419 := bstep (se 1 (by rfl) ⟨939314, by rfl⟩ : syracuseStep 1252419 = 1878629) B1878629
theorem B4815949 : Blo 1250443 4815949 := bstep (se 3 (by rfl) ⟨902990, by rfl⟩ : syracuseStep 4815949 = 1805981) B1805981
theorem B1252435 : Blo 1250443 1252435 := bstep (se 1 (by rfl) ⟨939326, by rfl⟩ : syracuseStep 1252435 = 1878653) B1878653
theorem B1408099 : Blo 1250443 1408099 := bstep (se 1 (by rfl) ⟨1056074, by rfl⟩ : syracuseStep 1408099 = 2112149) B2112149
theorem B4226147 : Blo 1250443 4226147 := bstep (se 1 (by rfl) ⟨3169610, by rfl⟩ : syracuseStep 4226147 = 6339221) B6339221
theorem B10140785 : Blo 1250443 10140785 := bstep (se 2 (by rfl) ⟨3802794, by rfl⟩ : syracuseStep 10140785 = 7605589) B7605589
theorem B2006129 : Blo 1250443 2006129 := bstep (se 2 (by rfl) ⟨752298, by rfl⟩ : syracuseStep 2006129 = 1504597) B1504597
theorem B7126157 : Blo 1250443 7126157 := bstep (se 3 (by rfl) ⟨1336154, by rfl⟩ : syracuseStep 7126157 = 2672309) B2672309
theorem B2112689 : Blo 1250443 2112689 := bstep (se 2 (by rfl) ⟨792258, by rfl⟩ : syracuseStep 2112689 = 1584517) B1584517
theorem B2817233 : Blo 1250443 2817233 := bstep (se 2 (by rfl) ⟨1056462, by rfl⟩ : syracuseStep 2817233 = 2112925) B2112925
theorem B3169489 : Blo 1250443 3169489 := bstep (se 2 (by rfl) ⟨1188558, by rfl⟩ : syracuseStep 3169489 = 2377117) B2377117
theorem B2817251 : Blo 1250443 2817251 := bstep (se 1 (by rfl) ⟨2112938, by rfl⟩ : syracuseStep 2817251 = 4225877) B4225877
theorem B1408243 : Blo 1250443 1408243 := bstep (se 1 (by rfl) ⟨1056182, by rfl⟩ : syracuseStep 1408243 = 2112365) B2112365
theorem B2374915 : Blo 1250443 2374915 := bstep (se 1 (by rfl) ⟨1781186, by rfl⟩ : syracuseStep 2374915 = 3562373) B3562373
theorem B2284817 : Blo 1250443 2284817 := bstep (se 2 (by rfl) ⟨856806, by rfl⟩ : syracuseStep 2284817 = 1713613) B1713613
theorem B2112817 : Blo 1250443 2112817 := bstep (se 2 (by rfl) ⟨792306, by rfl⟩ : syracuseStep 2112817 = 1584613) B1584613
theorem B3562829 : Blo 1250443 3562829 := bstep (se 3 (by rfl) ⟨668030, by rfl⟩ : syracuseStep 3562829 = 1336061) B1336061
theorem B2112851 : Blo 1250443 2112851 := bstep (se 1 (by rfl) ⟨1584638, by rfl⟩ : syracuseStep 2112851 = 3169277) B3169277
theorem B4226417 : Blo 1250443 4226417 := bstep (se 2 (by rfl) ⟨1584906, by rfl⟩ : syracuseStep 4226417 = 3169813) B3169813
theorem B1408387 : Blo 1250443 1408387 := bstep (se 1 (by rfl) ⟨1056290, by rfl⟩ : syracuseStep 1408387 = 2112581) B2112581
theorem B2375075 : Blo 1250443 2375075 := bstep (se 1 (by rfl) ⟨1781306, by rfl⟩ : syracuseStep 2375075 = 3562613) B3562613
theorem B2112979 : Blo 1250443 2112979 := bstep (se 1 (by rfl) ⟨1584734, by rfl⟩ : syracuseStep 2112979 = 3169469) B3169469
theorem B3169763 : Blo 1250443 3169763 := bstep (se 1 (by rfl) ⟨2377322, by rfl⟩ : syracuseStep 3169763 = 4754645) B4754645
theorem B2817521 : Blo 1250443 2817521 := bstep (se 2 (by rfl) ⟨1056570, by rfl⟩ : syracuseStep 2817521 = 2113141) B2113141
theorem B2817539 : Blo 1250443 2817539 := bstep (se 1 (by rfl) ⟨2113154, by rfl⟩ : syracuseStep 2817539 = 4226309) B4226309
theorem B1408531 : Blo 1250443 1408531 := bstep (se 1 (by rfl) ⟨1056398, by rfl⟩ : syracuseStep 1408531 = 2112797) B2112797
theorem B2113121 : Blo 1250443 2113121 := bstep (se 2 (by rfl) ⟨792420, by rfl⟩ : syracuseStep 2113121 = 1584841) B1584841
theorem B1408675 : Blo 1250443 1408675 := bstep (se 1 (by rfl) ⟨1056506, by rfl⟩ : syracuseStep 1408675 = 2113013) B2113013
theorem B3169955 : Blo 1250443 3169955 := bstep (se 1 (by rfl) ⟨2377466, by rfl⟩ : syracuseStep 3169955 = 4754933) B4754933
theorem B1875665 : Blo 1250443 1875665 := bstep (se 2 (by rfl) ⟨703374, by rfl⟩ : syracuseStep 1875665 = 1406749) B1406749
theorem B2113249 : Blo 1250443 2113249 := bstep (se 2 (by rfl) ⟨792468, by rfl⟩ : syracuseStep 2113249 = 1584937) B1584937
theorem B1875683 : Blo 1250443 1875683 := bstep (se 1 (by rfl) ⟨1406762, by rfl⟩ : syracuseStep 1875683 = 2813525) B2813525
theorem B4751075 : Blo 1250443 4751075 := bstep (se 1 (by rfl) ⟨3563306, by rfl⟩ : syracuseStep 4751075 = 7126613) B7126613
theorem B6094577 : Blo 1250443 6094577 := bstep (se 2 (by rfl) ⟨2285466, by rfl⟩ : syracuseStep 6094577 = 4570933) B4570933
theorem B1875713 : Blo 1250443 1875713 := bstep (se 2 (by rfl) ⟨703392, by rfl⟩ : syracuseStep 1875713 = 1406785) B1406785
theorem B2113283 : Blo 1250443 2113283 := bstep (se 1 (by rfl) ⟨1584962, by rfl⟩ : syracuseStep 2113283 = 3169925) B3169925
theorem B2817809 : Blo 1250443 2817809 := bstep (se 2 (by rfl) ⟨1056678, by rfl⟩ : syracuseStep 2817809 = 2113357) B2113357
theorem B1875731 : Blo 1250443 1875731 := bstep (se 1 (by rfl) ⟨1406798, by rfl⟩ : syracuseStep 1875731 = 2813597) B2813597
theorem B2817827 : Blo 1250443 2817827 := bstep (se 1 (by rfl) ⟨2113370, by rfl⟩ : syracuseStep 2817827 = 4226741) B4226741
theorem B1875761 : Blo 1250443 1875761 := bstep (se 2 (by rfl) ⟨703410, by rfl⟩ : syracuseStep 1875761 = 1406821) B1406821
theorem B1408819 : Blo 1250443 1408819 := bstep (se 1 (by rfl) ⟨1056614, by rfl⟩ : syracuseStep 1408819 = 2113229) B2113229
theorem B1875779 : Blo 1250443 1875779 := bstep (se 1 (by rfl) ⟨1406834, by rfl⟩ : syracuseStep 1875779 = 2813669) B2813669
theorem B1875809 : Blo 1250443 1875809 := bstep (se 2 (by rfl) ⟨703428, by rfl⟩ : syracuseStep 1875809 = 1406857) B1406857
theorem B2408305 : Blo 1250443 2408305 := bstep (se 2 (by rfl) ⟨903114, by rfl⟩ : syracuseStep 2408305 = 1806229) B1806229
theorem B1875827 : Blo 1250443 1875827 := bstep (se 1 (by rfl) ⟨1406870, by rfl⟩ : syracuseStep 1875827 = 2813741) B2813741
theorem B3383171 : Blo 1250443 3383171 := bstep (se 1 (by rfl) ⟨2537378, by rfl⟩ : syracuseStep 3383171 = 5074757) B5074757
theorem B2113411 : Blo 1250443 2113411 := bstep (se 1 (by rfl) ⟨1585058, by rfl⟩ : syracuseStep 2113411 = 3170117) B3170117
theorem B4226957 : Blo 1250443 4226957 := bstep (se 3 (by rfl) ⟨792554, by rfl⟩ : syracuseStep 4226957 = 1585109) B1585109
theorem B1875857 : Blo 1250443 1875857 := bstep (se 2 (by rfl) ⟨703446, by rfl⟩ : syracuseStep 1875857 = 1406893) B1406893
theorem B1875875 : Blo 1250443 1875875 := bstep (se 1 (by rfl) ⟨1406906, by rfl⟩ : syracuseStep 1875875 = 2813813) B2813813
theorem B6422435 : Blo 1250443 6422435 := bstep (se 1 (by rfl) ⟨4816826, by rfl⟩ : syracuseStep 6422435 = 9633653) B9633653
theorem B1875905 : Blo 1250443 1875905 := bstep (se 2 (by rfl) ⟨703464, by rfl⟩ : syracuseStep 1875905 = 1406929) B1406929
theorem B1408963 : Blo 1250443 1408963 := bstep (se 1 (by rfl) ⟨1056722, by rfl⟩ : syracuseStep 1408963 = 2113445) B2113445
theorem B1875923 : Blo 1250443 1875923 := bstep (se 1 (by rfl) ⟨1406942, by rfl⟩ : syracuseStep 1875923 = 2813885) B2813885
theorem B1605587 : Blo 1250443 1605587 := bstep (se 1 (by rfl) ⟨1204190, by rfl⟩ : syracuseStep 1605587 = 2408381) B2408381
theorem B1875953 : Blo 1250443 1875953 := bstep (se 2 (by rfl) ⟨703482, by rfl⟩ : syracuseStep 1875953 = 1406965) B1406965
theorem B2375705 : Blo 1250443 2375705 := bstep (se 2 (by rfl) ⟨890889, by rfl⟩ : syracuseStep 2375705 = 1781779) B1781779
theorem B1876043 : Blo 1250443 1876043 := bstep (se 1 (by rfl) ⟨1407032, by rfl⟩ : syracuseStep 1876043 = 2814065) B2814065
theorem B1876055 : Blo 1250443 1876055 := bstep (se 1 (by rfl) ⟨1407041, by rfl⟩ : syracuseStep 1876055 = 2814083) B2814083
theorem B1335403 : Blo 1250443 1335403 := bstep (se 1 (by rfl) ⟨1001552, by rfl⟩ : syracuseStep 1335403 = 2003105) B2003105
theorem B3563671 : Blo 1250443 3563671 := bstep (se 1 (by rfl) ⟨2672753, by rfl⟩ : syracuseStep 3563671 = 5345507) B5345507
theorem B1876121 : Blo 1250443 1876121 := bstep (se 2 (by rfl) ⟨703545, by rfl⟩ : syracuseStep 1876121 = 1407091) B1407091
theorem B24371381 : Blo 1250443 24371381 := bstep (se 5 (by rfl) ⟨1142408, by rfl⟩ : syracuseStep 24371381 = 2284817) B2284817
theorem B1876235 : Blo 1250443 1876235 := bstep (se 1 (by rfl) ⟨1407176, by rfl⟩ : syracuseStep 1876235 = 2814353) B2814353
theorem B1876247 : Blo 1250443 1876247 := bstep (se 1 (by rfl) ⟨1407185, by rfl⟩ : syracuseStep 1876247 = 2814371) B2814371
theorem B7610699 : Blo 1250443 7610699 := bstep (se 1 (by rfl) ⟨5708024, by rfl⟩ : syracuseStep 7610699 = 11416049) B11416049
theorem B1876313 : Blo 1250443 1876313 := bstep (se 2 (by rfl) ⟨703617, by rfl⟩ : syracuseStep 1876313 = 1407235) B1407235
theorem B2670977 : Blo 1250443 2670977 := bstep (se 2 (by rfl) ⟨1001616, by rfl⟩ : syracuseStep 2670977 = 2003233) B2003233
theorem B1876427 : Blo 1250443 1876427 := bstep (se 1 (by rfl) ⟨1407320, by rfl⟩ : syracuseStep 1876427 = 2814641) B2814641
theorem B1876439 : Blo 1250443 1876439 := bstep (se 1 (by rfl) ⟨1407329, by rfl⟩ : syracuseStep 1876439 = 2814659) B2814659
theorem B1876505 : Blo 1250443 1876505 := bstep (se 2 (by rfl) ⟨703689, by rfl⟩ : syracuseStep 1876505 = 1407379) B1407379
theorem B2253377 : Blo 1250443 2253377 := bstep (se 2 (by rfl) ⟨845016, by rfl⟩ : syracuseStep 2253377 = 1690033) B1690033
theorem B10142273 : Blo 1250443 10142273 := bstep (se 2 (by rfl) ⟨3803352, by rfl⟩ : syracuseStep 10142273 = 7606705) B7606705
theorem B1876619 : Blo 1250443 1876619 := bstep (se 1 (by rfl) ⟨1407464, by rfl⟩ : syracuseStep 1876619 = 2814929) B2814929
theorem B4752017 : Blo 1250443 4752017 := bstep (se 2 (by rfl) ⟨1782006, by rfl⟩ : syracuseStep 4752017 = 3564013) B3564013
theorem B1876631 : Blo 1250443 1876631 := bstep (se 1 (by rfl) ⟨1407473, by rfl⟩ : syracuseStep 1876631 = 2814947) B2814947
theorem B2671319 : Blo 1250443 2671319 := bstep (se 1 (by rfl) ⟨2003489, by rfl⟩ : syracuseStep 2671319 = 4006979) B4006979
theorem B1876697 : Blo 1250443 1876697 := bstep (se 2 (by rfl) ⟨703761, by rfl⟩ : syracuseStep 1876697 = 1407523) B1407523
theorem B2376449 : Blo 1250443 2376449 := bstep (se 2 (by rfl) ⟨891168, by rfl⟩ : syracuseStep 2376449 = 1782337) B1782337
theorem B2573057 : Blo 1250443 2573057 := bstep (se 2 (by rfl) ⟨964896, by rfl⟩ : syracuseStep 2573057 = 1929793) B1929793
theorem B4006721 : Blo 1250443 4006721 := bstep (se 2 (by rfl) ⟨1502520, by rfl⟩ : syracuseStep 4006721 = 3005041) B3005041
theorem B1876811 : Blo 1250443 1876811 := bstep (se 1 (by rfl) ⟨1407608, by rfl⟩ : syracuseStep 1876811 = 2815217) B2815217
theorem B1876823 : Blo 1250443 1876823 := bstep (se 1 (by rfl) ⟨1407617, by rfl⟩ : syracuseStep 1876823 = 2815235) B2815235
theorem B2671489 : Blo 1250443 2671489 := bstep (se 2 (by rfl) ⟨1001808, by rfl⟩ : syracuseStep 2671489 = 2003617) B2003617
theorem B1876889 : Blo 1250443 1876889 := bstep (se 2 (by rfl) ⟨703833, by rfl⟩ : syracuseStep 1876889 = 1407667) B1407667
theorem B1877003 : Blo 1250443 1877003 := bstep (se 1 (by rfl) ⟨1407752, by rfl⟩ : syracuseStep 1877003 = 2815505) B2815505
theorem B2475019 : Blo 1250443 2475019 := bstep (se 1 (by rfl) ⟨1856264, by rfl⟩ : syracuseStep 2475019 = 3712529) B3712529
theorem B2376715 : Blo 1250443 2376715 := bstep (se 1 (by rfl) ⟨1782536, by rfl⟩ : syracuseStep 2376715 = 3565073) B3565073
theorem B1877015 : Blo 1250443 1877015 := bstep (se 1 (by rfl) ⟨1407761, by rfl⟩ : syracuseStep 1877015 = 2815523) B2815523
theorem B1877081 : Blo 1250443 1877081 := bstep (se 2 (by rfl) ⟨703905, by rfl⟩ : syracuseStep 1877081 = 1407811) B1407811
theorem B1877195 : Blo 1250443 1877195 := bstep (se 1 (by rfl) ⟨1407896, by rfl⟩ : syracuseStep 1877195 = 2815793) B2815793
theorem B1877207 : Blo 1250443 1877207 := bstep (se 1 (by rfl) ⟨1407905, by rfl⟩ : syracuseStep 1877207 = 2815811) B2815811
theorem B6333713 : Blo 1250443 6333713 := bstep (se 2 (by rfl) ⟨2375142, by rfl⟩ : syracuseStep 6333713 = 4750285) B4750285
theorem B1877273 : Blo 1250443 1877273 := bstep (se 2 (by rfl) ⟨703977, by rfl⟩ : syracuseStep 1877273 = 1407955) B1407955
theorem B21677357 : Blo 1250443 21677357 := bstep (se 3 (by rfl) ⟨4064504, by rfl⟩ : syracuseStep 21677357 = 8129009) B8129009
theorem B4752715 : Blo 1250443 4752715 := bstep (se 1 (by rfl) ⟨3564536, by rfl⟩ : syracuseStep 4752715 = 7129073) B7129073
theorem B5711197 : Blo 1250443 5711197 := bstep (se 3 (by rfl) ⟨1070849, by rfl⟩ : syracuseStep 5711197 = 2141699) B2141699
theorem B1877387 : Blo 1250443 1877387 := bstep (se 1 (by rfl) ⟨1408040, by rfl⟩ : syracuseStep 1877387 = 2816081) B2816081
theorem B1877399 : Blo 1250443 1877399 := bstep (se 1 (by rfl) ⟨1408049, by rfl⟩ : syracuseStep 1877399 = 2816099) B2816099
theorem B6333875 : Blo 1250443 6333875 := bstep (se 1 (by rfl) ⟨4750406, by rfl⟩ : syracuseStep 6333875 = 9500813) B9500813
theorem B6014387 : Blo 1250443 6014387 := bstep (se 1 (by rfl) ⟨4510790, by rfl⟩ : syracuseStep 6014387 = 9021581) B9021581
theorem B2377163 : Blo 1250443 2377163 := bstep (se 1 (by rfl) ⟨1782872, by rfl⟩ : syracuseStep 2377163 = 3565745) B3565745
theorem B1877465 : Blo 1250443 1877465 := bstep (se 2 (by rfl) ⟨704049, by rfl⟩ : syracuseStep 1877465 = 1408099) B1408099
theorem B2254387 : Blo 1250443 2254387 := bstep (se 1 (by rfl) ⟨1690790, by rfl⟩ : syracuseStep 2254387 = 3381581) B3381581
theorem B1877579 : Blo 1250443 1877579 := bstep (se 1 (by rfl) ⟨1408184, by rfl⟩ : syracuseStep 1877579 = 2816369) B2816369
theorem B1582679 : Blo 1250443 1582679 := bstep (se 1 (by rfl) ⟨1187009, by rfl⟩ : syracuseStep 1582679 = 2374019) B2374019
theorem B1877591 : Blo 1250443 1877591 := bstep (se 1 (by rfl) ⟨1408193, by rfl⟩ : syracuseStep 1877591 = 2816387) B2816387
theorem B4752989 : Blo 1250443 4752989 := bstep (se 3 (by rfl) ⟨891185, by rfl⟩ : syracuseStep 4752989 = 1782371) B1782371
theorem B2377345 : Blo 1250443 2377345 := bstep (se 2 (by rfl) ⟨891504, by rfl⟩ : syracuseStep 2377345 = 1783009) B1783009
theorem B14247575 : Blo 1250443 14247575 := bstep (se 1 (by rfl) ⟨10685681, by rfl⟩ : syracuseStep 14247575 = 21371363) B21371363
theorem B1877657 : Blo 1250443 1877657 := bstep (se 2 (by rfl) ⟨704121, by rfl⟩ : syracuseStep 1877657 = 1408243) B1408243
theorem B5072563 : Blo 1250443 5072563 := bstep (se 1 (by rfl) ⟨3804422, by rfl⟩ : syracuseStep 5072563 = 7608845) B7608845
theorem B7128755 : Blo 1250443 7128755 := bstep (se 1 (by rfl) ⟨5346566, by rfl⟩ : syracuseStep 7128755 = 10693133) B10693133
theorem B1877771 : Blo 1250443 1877771 := bstep (se 1 (by rfl) ⟨1408328, by rfl⟩ : syracuseStep 1877771 = 2816657) B2816657
theorem B1877783 : Blo 1250443 1877783 := bstep (se 1 (by rfl) ⟨1408337, by rfl⟩ : syracuseStep 1877783 = 2816675) B2816675
theorem B8021825 : Blo 1250443 8021825 := bstep (se 2 (by rfl) ⟨3008184, by rfl⟩ : syracuseStep 8021825 = 6016369) B6016369
theorem B4220747 : Blo 1250443 4220747 := bstep (se 1 (by rfl) ⟨3165560, by rfl⟩ : syracuseStep 4220747 = 6331121) B6331121
theorem B1877849 : Blo 1250443 1877849 := bstep (se 2 (by rfl) ⟨704193, by rfl⟩ : syracuseStep 1877849 = 1408387) B1408387
theorem B8030045 : Blo 1250443 8030045 := bstep (se 3 (by rfl) ⟨1505633, by rfl⟩ : syracuseStep 8030045 = 3011267) B3011267
theorem B3614557 : Blo 1250443 3614557 := bstep (se 3 (by rfl) ⟨677729, by rfl⟩ : syracuseStep 3614557 = 1355459) B1355459
theorem B1877963 : Blo 1250443 1877963 := bstep (se 1 (by rfl) ⟨1408472, by rfl⟩ : syracuseStep 1877963 = 2816945) B2816945
theorem B1877975 : Blo 1250443 1877975 := bstep (se 1 (by rfl) ⟨1408481, by rfl⟩ : syracuseStep 1877975 = 2816963) B2816963
theorem B2377687 : Blo 1250443 2377687 := bstep (se 1 (by rfl) ⟨1783265, by rfl⟩ : syracuseStep 2377687 = 3566531) B3566531
theorem B3565529 : Blo 1250443 3565529 := bstep (se 2 (by rfl) ⟨1337073, by rfl⟩ : syracuseStep 3565529 = 2674147) B2674147
theorem B2672651 : Blo 1250443 2672651 := bstep (se 1 (by rfl) ⟨2004488, by rfl⟩ : syracuseStep 2672651 = 4008977) B4008977
theorem B1878041 : Blo 1250443 1878041 := bstep (se 2 (by rfl) ⟨704265, by rfl⟩ : syracuseStep 1878041 = 1408531) B1408531
theorem B6760523 : Blo 1250443 6760523 := bstep (se 1 (by rfl) ⟨5070392, by rfl⟩ : syracuseStep 6760523 = 10140785) B10140785
theorem B1337419 : Blo 1250443 1337419 := bstep (se 1 (by rfl) ⟨1003064, by rfl⟩ : syracuseStep 1337419 = 2006129) B2006129
theorem B4221017 : Blo 1250443 4221017 := bstep (se 2 (by rfl) ⟨1582881, by rfl⟩ : syracuseStep 4221017 = 3165763) B3165763
theorem B1878155 : Blo 1250443 1878155 := bstep (se 1 (by rfl) ⟨1408616, by rfl⟩ : syracuseStep 1878155 = 2817233) B2817233
theorem B1878167 : Blo 1250443 1878167 := bstep (se 1 (by rfl) ⟨1408625, by rfl⟩ : syracuseStep 1878167 = 2817251) B2817251
theorem B21366989 : Blo 1250443 21366989 := bstep (se 3 (by rfl) ⟨4006310, by rfl⟩ : syracuseStep 21366989 = 8012621) B8012621
theorem B4065497 : Blo 1250443 4065497 := bstep (se 2 (by rfl) ⟨1524561, by rfl⟩ : syracuseStep 4065497 = 3049123) B3049123
theorem B1878233 : Blo 1250443 1878233 := bstep (se 2 (by rfl) ⟨704337, by rfl⟩ : syracuseStep 1878233 = 1408675) B1408675
theorem B1583383 : Blo 1250443 1583383 := bstep (se 1 (by rfl) ⟨1187537, by rfl⟩ : syracuseStep 1583383 = 2375075) B2375075
theorem B4753687 : Blo 1250443 4753687 := bstep (se 1 (by rfl) ⟨3565265, by rfl⟩ : syracuseStep 4753687 = 7130531) B7130531
theorem B1878347 : Blo 1250443 1878347 := bstep (se 1 (by rfl) ⟨1408760, by rfl⟩ : syracuseStep 1878347 = 2817521) B2817521
theorem B1878359 : Blo 1250443 1878359 := bstep (se 1 (by rfl) ⟨1408769, by rfl⟩ : syracuseStep 1878359 = 2817539) B2817539
theorem B9496925 : Blo 1250443 9496925 := bstep (se 3 (by rfl) ⟨1780673, by rfl⟩ : syracuseStep 9496925 = 3561347) B3561347
theorem B5146973 : Blo 1250443 5146973 := bstep (se 3 (by rfl) ⟨965057, by rfl⟩ : syracuseStep 5146973 = 1930115) B1930115
theorem B1878425 : Blo 1250443 1878425 := bstep (se 2 (by rfl) ⟨704409, by rfl⟩ : syracuseStep 1878425 = 1408819) B1408819
theorem B5343661 : Blo 1250443 5343661 := bstep (se 3 (by rfl) ⟨1001936, by rfl⟩ : syracuseStep 5343661 = 2003873) B2003873
theorem B1878539 : Blo 1250443 1878539 := bstep (se 1 (by rfl) ⟨1408904, by rfl⟩ : syracuseStep 1878539 = 2817809) B2817809
theorem B1878551 : Blo 1250443 1878551 := bstep (se 1 (by rfl) ⟨1408913, by rfl⟩ : syracuseStep 1878551 = 2817827) B2817827
theorem B2255447 : Blo 1250443 2255447 := bstep (se 1 (by rfl) ⟨1691585, by rfl⟩ : syracuseStep 2255447 = 3383171) B3383171
theorem B1690201 : Blo 1250443 1690201 := bstep (se 2 (by rfl) ⟨633825, by rfl⟩ : syracuseStep 1690201 = 1267651) B1267651
theorem B5343833 : Blo 1250443 5343833 := bstep (se 2 (by rfl) ⟨2003937, by rfl⟩ : syracuseStep 5343833 = 4007875) B4007875
theorem B10144349 : Blo 1250443 10144349 := bstep (se 3 (by rfl) ⟨1902065, by rfl⟩ : syracuseStep 10144349 = 3804131) B3804131
theorem B1878617 : Blo 1250443 1878617 := bstep (se 2 (by rfl) ⟨704481, by rfl⟩ : syracuseStep 1878617 = 1408963) B1408963
theorem B6425219 : Blo 1250443 6425219 := bstep (se 1 (by rfl) ⟨4818914, by rfl⟩ : syracuseStep 6425219 = 9637829) B9637829
theorem B5073601 : Blo 1250443 5073601 := bstep (se 2 (by rfl) ⟨1902600, by rfl⟩ : syracuseStep 5073601 = 3805201) B3805201
theorem B12028621 : Blo 1250443 12028621 := bstep (se 3 (by rfl) ⟨2255366, by rfl⟩ : syracuseStep 12028621 = 4510733) B4510733
theorem B5712605 : Blo 1250443 5712605 := bstep (se 3 (by rfl) ⟨1071113, by rfl⟩ : syracuseStep 5712605 = 2142227) B2142227
theorem B2673395 : Blo 1250443 2673395 := bstep (se 1 (by rfl) ⟨2005046, by rfl⟩ : syracuseStep 2673395 = 4010093) B4010093
theorem B2255627 : Blo 1250443 2255627 := bstep (se 1 (by rfl) ⟨1691720, by rfl⟩ : syracuseStep 2255627 = 3383441) B3383441
theorem B4221719 : Blo 1250443 4221719 := bstep (se 1 (by rfl) ⟨3166289, by rfl⟩ : syracuseStep 4221719 = 6332579) B6332579
theorem B3566359 : Blo 1250443 3566359 := bstep (se 1 (by rfl) ⟨2674769, by rfl⟩ : syracuseStep 3566359 = 5349539) B5349539
theorem B7121965 : Blo 1250443 7121965 := bstep (se 3 (by rfl) ⟨1335368, by rfl⟩ : syracuseStep 7121965 = 2670737) B2670737
theorem B4754477 : Blo 1250443 4754477 := bstep (se 3 (by rfl) ⟨891464, by rfl⟩ : syracuseStep 4754477 = 1782929) B1782929
theorem B7130213 : Blo 1250443 7130213 := bstep (se 4 (by rfl) ⟨668457, by rfl⟩ : syracuseStep 7130213 = 1336915) B1336915
theorem B4009181 : Blo 1250443 4009181 := bstep (se 3 (by rfl) ⟨751721, by rfl⟩ : syracuseStep 4009181 = 1503443) B1503443
theorem B4222259 : Blo 1250443 4222259 := bstep (se 1 (by rfl) ⟨3166694, by rfl⟩ : syracuseStep 4222259 = 6333389) B6333389
theorem B6335819 : Blo 1250443 6335819 := bstep (se 1 (by rfl) ⟨4751864, by rfl⟩ : syracuseStep 6335819 = 9503729) B9503729
theorem B2256203 : Blo 1250443 2256203 := bstep (se 1 (by rfl) ⟨1692152, by rfl⟩ : syracuseStep 2256203 = 3384305) B3384305
theorem B4222529 : Blo 1250443 4222529 := bstep (se 2 (by rfl) ⟨1583448, by rfl⟩ : syracuseStep 4222529 = 3166897) B3166897
theorem B2674291 : Blo 1250443 2674291 := bstep (se 1 (by rfl) ⟨2005718, by rfl⟩ : syracuseStep 2674291 = 4011437) B4011437
theorem B2813579 : Blo 1250443 2813579 := bstep (se 1 (by rfl) ⟨2110184, by rfl⟩ : syracuseStep 2813579 = 4220369) B4220369
theorem B3165875 : Blo 1250443 3165875 := bstep (se 1 (by rfl) ⟨2374406, by rfl⟩ : syracuseStep 3165875 = 4748813) B4748813
theorem B2813633 : Blo 1250443 2813633 := bstep (se 2 (by rfl) ⟨1055112, by rfl⟩ : syracuseStep 2813633 = 2110225) B2110225
theorem B2813849 : Blo 1250443 2813849 := bstep (se 2 (by rfl) ⟨1055193, by rfl⟩ : syracuseStep 2813849 = 2110387) B2110387
theorem B1585099 : Blo 1250443 1585099 := bstep (se 1 (by rfl) ⟨1188824, by rfl⟩ : syracuseStep 1585099 = 2377649) B2377649
theorem B2813939 : Blo 1250443 2813939 := bstep (se 1 (by rfl) ⟨2110454, by rfl⟩ : syracuseStep 2813939 = 4220909) B4220909
theorem B2813975 : Blo 1250443 2813975 := bstep (se 1 (by rfl) ⟨2110481, by rfl⟩ : syracuseStep 2813975 = 4220963) B4220963
theorem B4223069 : Blo 1250443 4223069 := bstep (se 3 (by rfl) ⟨791825, by rfl⟩ : syracuseStep 4223069 = 1583651) B1583651
theorem B5345473 : Blo 1250443 5345473 := bstep (se 2 (by rfl) ⟨2004552, by rfl⟩ : syracuseStep 5345473 = 4009105) B4009105
theorem B2814155 : Blo 1250443 2814155 := bstep (se 1 (by rfl) ⟨2110616, by rfl⟩ : syracuseStep 2814155 = 4221233) B4221233
theorem B3166411 : Blo 1250443 3166411 := bstep (se 1 (by rfl) ⟨2374808, by rfl⟩ : syracuseStep 3166411 = 4749617) B4749617
theorem B2814209 : Blo 1250443 2814209 := bstep (se 2 (by rfl) ⟨1055328, by rfl⟩ : syracuseStep 2814209 = 2110657) B2110657
theorem B7614785 : Blo 1250443 7614785 := bstep (se 2 (by rfl) ⟨2855544, by rfl⟩ : syracuseStep 7614785 = 5711089) B5711089
theorem B3166553 : Blo 1250443 3166553 := bstep (se 2 (by rfl) ⟨1187457, by rfl⟩ : syracuseStep 3166553 = 2374915) B2374915
theorem B2814425 : Blo 1250443 2814425 := bstep (se 2 (by rfl) ⟨1055409, by rfl⟩ : syracuseStep 2814425 = 2110819) B2110819
theorem B2814515 : Blo 1250443 2814515 := bstep (se 1 (by rfl) ⟨2110886, by rfl⟩ : syracuseStep 2814515 = 4221773) B4221773
theorem B4747841 : Blo 1250443 4747841 := bstep (se 2 (by rfl) ⟨1780440, by rfl⟩ : syracuseStep 4747841 = 3560881) B3560881
theorem B2814551 : Blo 1250443 2814551 := bstep (se 1 (by rfl) ⟨2110913, by rfl⟩ : syracuseStep 2814551 = 4221827) B4221827
theorem B5075549 : Blo 1250443 5075549 := bstep (se 3 (by rfl) ⟨951665, by rfl⟩ : syracuseStep 5075549 = 1903331) B1903331
theorem B20845187 : Blo 1250443 20845187 := bstep (se 1 (by rfl) ⟨15633890, by rfl⟩ : syracuseStep 20845187 = 31267781) B31267781
theorem B2708147 : Blo 1250443 2708147 := bstep (se 1 (by rfl) ⟨2031110, by rfl⟩ : syracuseStep 2708147 = 4062221) B4062221
theorem B5075677 : Blo 1250443 5075677 := bstep (se 3 (by rfl) ⟨951689, by rfl⟩ : syracuseStep 5075677 = 1903379) B1903379
theorem B2814731 : Blo 1250443 2814731 := bstep (se 1 (by rfl) ⟨2111048, by rfl⟩ : syracuseStep 2814731 = 4222097) B4222097
theorem B2814785 : Blo 1250443 2814785 := bstep (se 2 (by rfl) ⟨1055544, by rfl⟩ : syracuseStep 2814785 = 2111089) B2111089
theorem B17126261 : Blo 1250443 17126261 := bstep (se 5 (by rfl) ⟨802793, by rfl⟩ : syracuseStep 17126261 = 1605587) B1605587
theorem B4813741 : Blo 1250443 4813741 := bstep (se 3 (by rfl) ⟨902576, by rfl⟩ : syracuseStep 4813741 = 1805153) B1805153
theorem B2110475 : Blo 1250443 2110475 := bstep (se 1 (by rfl) ⟨1582856, by rfl⟩ : syracuseStep 2110475 = 3165713) B3165713
theorem B2815001 : Blo 1250443 2815001 := bstep (se 2 (by rfl) ⟨1055625, by rfl⟩ : syracuseStep 2815001 = 2111251) B2111251
theorem B6337601 : Blo 1250443 6337601 := bstep (se 2 (by rfl) ⟨2376600, by rfl⟩ : syracuseStep 6337601 = 4753201) B4753201
theorem B2815091 : Blo 1250443 2815091 := bstep (se 1 (by rfl) ⟨2111318, by rfl⟩ : syracuseStep 2815091 = 4222637) B4222637
theorem B1250443 : Blo 1250443 1250443 := bstep (se 1 (by rfl) ⟨937832, by rfl⟩ : syracuseStep 1250443 = 1875665) B1875665
theorem B2110603 : Blo 1250443 2110603 := bstep (se 1 (by rfl) ⟨1582952, by rfl⟩ : syracuseStep 2110603 = 3165905) B3165905
theorem B1250455 : Blo 1250443 1250455 := bstep (se 1 (by rfl) ⟨937841, by rfl⟩ : syracuseStep 1250455 = 1875683) B1875683
theorem B2815127 : Blo 1250443 2815127 := bstep (se 1 (by rfl) ⟨2111345, by rfl⟩ : syracuseStep 2815127 = 4222691) B4222691
theorem B3167383 : Blo 1250443 3167383 := bstep (se 1 (by rfl) ⟨2375537, by rfl⟩ : syracuseStep 3167383 = 4751075) B4751075
theorem B1250475 : Blo 1250443 1250475 := bstep (se 1 (by rfl) ⟨937856, by rfl⟩ : syracuseStep 1250475 = 1875713) B1875713
theorem B1250487 : Blo 1250443 1250487 := bstep (se 1 (by rfl) ⟨937865, by rfl⟩ : syracuseStep 1250487 = 1875731) B1875731
theorem B1250507 : Blo 1250443 1250507 := bstep (se 1 (by rfl) ⟨937880, by rfl⟩ : syracuseStep 1250507 = 1875761) B1875761
theorem B4224203 : Blo 1250443 4224203 := bstep (se 1 (by rfl) ⟨3168152, by rfl⟩ : syracuseStep 4224203 = 6336305) B6336305
theorem B1250519 : Blo 1250443 1250519 := bstep (se 1 (by rfl) ⟨937889, by rfl⟩ : syracuseStep 1250519 = 1875779) B1875779
theorem B1250539 : Blo 1250443 1250539 := bstep (se 1 (by rfl) ⟨937904, by rfl⟩ : syracuseStep 1250539 = 1875809) B1875809
theorem B1250551 : Blo 1250443 1250551 := bstep (se 1 (by rfl) ⟨937913, by rfl⟩ : syracuseStep 1250551 = 1875827) B1875827
theorem B1250571 : Blo 1250443 1250571 := bstep (se 1 (by rfl) ⟨937928, by rfl⟩ : syracuseStep 1250571 = 1875857) B1875857
theorem B1250583 : Blo 1250443 1250583 := bstep (se 1 (by rfl) ⟨937937, by rfl⟩ : syracuseStep 1250583 = 1875875) B1875875
theorem B4281623 : Blo 1250443 4281623 := bstep (se 1 (by rfl) ⟨3211217, by rfl⟩ : syracuseStep 4281623 = 6422435) B6422435
theorem B2110745 : Blo 1250443 2110745 := bstep (se 2 (by rfl) ⟨791529, by rfl⟩ : syracuseStep 2110745 = 1583059) B1583059
theorem B1250603 : Blo 1250443 1250603 := bstep (se 1 (by rfl) ⟨937952, by rfl⟩ : syracuseStep 1250603 = 1875905) B1875905
theorem B1250615 : Blo 1250443 1250615 := bstep (se 1 (by rfl) ⟨937961, by rfl⟩ : syracuseStep 1250615 = 1875923) B1875923
theorem B1250635 : Blo 1250443 1250635 := bstep (se 1 (by rfl) ⟨937976, by rfl⟩ : syracuseStep 1250635 = 1875953) B1875953
theorem B2815307 : Blo 1250443 2815307 := bstep (se 1 (by rfl) ⟨2111480, by rfl⟩ : syracuseStep 2815307 = 4222961) B4222961
theorem B1250647 : Blo 1250443 1250647 := bstep (se 1 (by rfl) ⟨937985, by rfl⟩ : syracuseStep 1250647 = 1875971) B1875971
theorem B1783129 : Blo 1250443 1783129 := bstep (se 2 (by rfl) ⟨668673, by rfl⟩ : syracuseStep 1783129 = 1337347) B1337347
theorem B1250667 : Blo 1250443 1250667 := bstep (se 1 (by rfl) ⟨938000, by rfl⟩ : syracuseStep 1250667 = 1876001) B1876001
theorem B1250679 : Blo 1250443 1250679 := bstep (se 1 (by rfl) ⟨938009, by rfl⟩ : syracuseStep 1250679 = 1876019) B1876019
theorem B2815361 : Blo 1250443 2815361 := bstep (se 2 (by rfl) ⟨1055760, by rfl⟩ : syracuseStep 2815361 = 2111521) B2111521
theorem B1250699 : Blo 1250443 1250699 := bstep (se 1 (by rfl) ⟨938024, by rfl⟩ : syracuseStep 1250699 = 1876049) B1876049
theorem B1250711 : Blo 1250443 1250711 := bstep (se 1 (by rfl) ⟨938033, by rfl⟩ : syracuseStep 1250711 = 1876067) B1876067
theorem B2110873 : Blo 1250443 2110873 := bstep (se 2 (by rfl) ⟨791577, by rfl⟩ : syracuseStep 2110873 = 1583155) B1583155
theorem B1250731 : Blo 1250443 1250731 := bstep (se 1 (by rfl) ⟨938048, by rfl⟩ : syracuseStep 1250731 = 1876097) B1876097
theorem B1250743 : Blo 1250443 1250743 := bstep (se 1 (by rfl) ⟨938057, by rfl⟩ : syracuseStep 1250743 = 1876115) B1876115
theorem B1250763 : Blo 1250443 1250763 := bstep (se 1 (by rfl) ⟨938072, by rfl⟩ : syracuseStep 1250763 = 1876145) B1876145
theorem B1250775 : Blo 1250443 1250775 := bstep (se 1 (by rfl) ⟨938081, by rfl⟩ : syracuseStep 1250775 = 1876163) B1876163
theorem B4224473 : Blo 1250443 4224473 := bstep (se 2 (by rfl) ⟨1584177, by rfl⟩ : syracuseStep 4224473 = 3168355) B3168355
theorem B1250795 : Blo 1250443 1250795 := bstep (se 1 (by rfl) ⟨938096, by rfl⟩ : syracuseStep 1250795 = 1876193) B1876193
theorem B1250807 : Blo 1250443 1250807 := bstep (se 1 (by rfl) ⟨938105, by rfl⟩ : syracuseStep 1250807 = 1876211) B1876211
theorem B1250827 : Blo 1250443 1250827 := bstep (se 1 (by rfl) ⟨938120, by rfl⟩ : syracuseStep 1250827 = 1876241) B1876241
theorem B8123921 : Blo 1250443 8123921 := bstep (se 2 (by rfl) ⟨3046470, by rfl⟩ : syracuseStep 8123921 = 6092941) B6092941
theorem B1250839 : Blo 1250443 1250839 := bstep (se 1 (by rfl) ⟨938129, by rfl⟩ : syracuseStep 1250839 = 1876259) B1876259
theorem B1250859 : Blo 1250443 1250859 := bstep (se 1 (by rfl) ⟨938144, by rfl⟩ : syracuseStep 1250859 = 1876289) B1876289
theorem B1250871 : Blo 1250443 1250871 := bstep (se 1 (by rfl) ⟨938153, by rfl⟩ : syracuseStep 1250871 = 1876307) B1876307
theorem B1250891 : Blo 1250443 1250891 := bstep (se 1 (by rfl) ⟨938168, by rfl⟩ : syracuseStep 1250891 = 1876337) B1876337
theorem B3167819 : Blo 1250443 3167819 := bstep (se 1 (by rfl) ⟨2375864, by rfl⟩ : syracuseStep 3167819 = 4751729) B4751729
theorem B1250903 : Blo 1250443 1250903 := bstep (se 1 (by rfl) ⟨938177, by rfl⟩ : syracuseStep 1250903 = 1876355) B1876355
theorem B2815577 : Blo 1250443 2815577 := bstep (se 2 (by rfl) ⟨1055841, by rfl⟩ : syracuseStep 2815577 = 2111683) B2111683
theorem B1250923 : Blo 1250443 1250923 := bstep (se 1 (by rfl) ⟨938192, by rfl⟩ : syracuseStep 1250923 = 1876385) B1876385
theorem B1250935 : Blo 1250443 1250935 := bstep (se 1 (by rfl) ⟨938201, by rfl⟩ : syracuseStep 1250935 = 1876403) B1876403
theorem B1250955 : Blo 1250443 1250955 := bstep (se 1 (by rfl) ⟨938216, by rfl⟩ : syracuseStep 1250955 = 1876433) B1876433
theorem B1250967 : Blo 1250443 1250967 := bstep (se 1 (by rfl) ⟨938225, by rfl⟩ : syracuseStep 1250967 = 1876451) B1876451
theorem B1250987 : Blo 1250443 1250987 := bstep (se 1 (by rfl) ⟨938240, by rfl⟩ : syracuseStep 1250987 = 1876481) B1876481
theorem B2815667 : Blo 1250443 2815667 := bstep (se 1 (by rfl) ⟨2111750, by rfl⟩ : syracuseStep 2815667 = 4223501) B4223501
theorem B1250999 : Blo 1250443 1250999 := bstep (se 1 (by rfl) ⟨938249, by rfl⟩ : syracuseStep 1250999 = 1876499) B1876499
theorem B1251019 : Blo 1250443 1251019 := bstep (se 1 (by rfl) ⟨938264, by rfl⟩ : syracuseStep 1251019 = 1876529) B1876529
theorem B1251031 : Blo 1250443 1251031 := bstep (se 1 (by rfl) ⟨938273, by rfl⟩ : syracuseStep 1251031 = 1876547) B1876547
theorem B2815703 : Blo 1250443 2815703 := bstep (se 1 (by rfl) ⟨2111777, by rfl⟩ : syracuseStep 2815703 = 4223555) B4223555
theorem B1251051 : Blo 1250443 1251051 := bstep (se 1 (by rfl) ⟨938288, by rfl⟩ : syracuseStep 1251051 = 1876577) B1876577
theorem B1251063 : Blo 1250443 1251063 := bstep (se 1 (by rfl) ⟨938297, by rfl⟩ : syracuseStep 1251063 = 1876595) B1876595
theorem B1251083 : Blo 1250443 1251083 := bstep (se 1 (by rfl) ⟨938312, by rfl⟩ : syracuseStep 1251083 = 1876625) B1876625
theorem B1251095 : Blo 1250443 1251095 := bstep (se 1 (by rfl) ⟨938321, by rfl⟩ : syracuseStep 1251095 = 1876643) B1876643
theorem B1251115 : Blo 1250443 1251115 := bstep (se 1 (by rfl) ⟨938336, by rfl⟩ : syracuseStep 1251115 = 1876673) B1876673
theorem B4749101 : Blo 1250443 4749101 := bstep (se 3 (by rfl) ⟨890456, by rfl⟩ : syracuseStep 4749101 = 1780913) B1780913
theorem B1251127 : Blo 1250443 1251127 := bstep (se 1 (by rfl) ⟨938345, by rfl⟩ : syracuseStep 1251127 = 1876691) B1876691
theorem B4749131 : Blo 1250443 4749131 := bstep (se 1 (by rfl) ⟨3561848, by rfl⟩ : syracuseStep 4749131 = 7123697) B7123697
theorem B1251147 : Blo 1250443 1251147 := bstep (se 1 (by rfl) ⟨938360, by rfl⟩ : syracuseStep 1251147 = 1876721) B1876721
theorem B5347147 : Blo 1250443 5347147 := bstep (se 1 (by rfl) ⟨4010360, by rfl⟩ : syracuseStep 5347147 = 8020721) B8020721
theorem B1251159 : Blo 1250443 1251159 := bstep (se 1 (by rfl) ⟨938369, by rfl⟩ : syracuseStep 1251159 = 1876739) B1876739
theorem B36083555 : Blo 1250443 36083555 := bstep (se 1 (by rfl) ⟨27062666, by rfl⟩ : syracuseStep 36083555 = 54125333) B54125333
theorem B1251179 : Blo 1250443 1251179 := bstep (se 1 (by rfl) ⟨938384, by rfl⟩ : syracuseStep 1251179 = 1876769) B1876769
theorem B1406839 : Blo 1250443 1406839 := bstep (se 1 (by rfl) ⟨1055129, by rfl⟩ : syracuseStep 1406839 = 2110259) B2110259
theorem B1251191 : Blo 1250443 1251191 := bstep (se 1 (by rfl) ⟨938393, by rfl⟩ : syracuseStep 1251191 = 1876787) B1876787
theorem B1251211 : Blo 1250443 1251211 := bstep (se 1 (by rfl) ⟨938408, by rfl⟩ : syracuseStep 1251211 = 1876817) B1876817
theorem B2815883 : Blo 1250443 2815883 := bstep (se 1 (by rfl) ⟨2111912, by rfl⟩ : syracuseStep 2815883 = 4223825) B4223825
theorem B1251223 : Blo 1250443 1251223 := bstep (se 1 (by rfl) ⟨938417, by rfl⟩ : syracuseStep 1251223 = 1876835) B1876835
theorem B1251243 : Blo 1250443 1251243 := bstep (se 1 (by rfl) ⟨938432, by rfl⟩ : syracuseStep 1251243 = 1876865) B1876865
theorem B1251255 : Blo 1250443 1251255 := bstep (se 1 (by rfl) ⟨938441, by rfl⟩ : syracuseStep 1251255 = 1876883) B1876883
theorem B2815937 : Blo 1250443 2815937 := bstep (se 2 (by rfl) ⟨1055976, by rfl⟩ : syracuseStep 2815937 = 2111953) B2111953
theorem B3168193 : Blo 1250443 3168193 := bstep (se 2 (by rfl) ⟨1188072, by rfl⟩ : syracuseStep 3168193 = 2376145) B2376145
theorem B1251275 : Blo 1250443 1251275 := bstep (se 1 (by rfl) ⟨938456, by rfl⟩ : syracuseStep 1251275 = 1876913) B1876913
theorem B2111447 : Blo 1250443 2111447 := bstep (se 1 (by rfl) ⟨1583585, by rfl⟩ : syracuseStep 2111447 = 3167171) B3167171
theorem B1251287 : Blo 1250443 1251287 := bstep (se 1 (by rfl) ⟨938465, by rfl⟩ : syracuseStep 1251287 = 1876931) B1876931
theorem B1251307 : Blo 1250443 1251307 := bstep (se 1 (by rfl) ⟨938480, by rfl⟩ : syracuseStep 1251307 = 1876961) B1876961
theorem B1251319 : Blo 1250443 1251319 := bstep (se 1 (by rfl) ⟨938489, by rfl⟩ : syracuseStep 1251319 = 1876979) B1876979
theorem B1251339 : Blo 1250443 1251339 := bstep (se 1 (by rfl) ⟨938504, by rfl⟩ : syracuseStep 1251339 = 1877009) B1877009
theorem B1251351 : Blo 1250443 1251351 := bstep (se 1 (by rfl) ⟨938513, by rfl⟩ : syracuseStep 1251351 = 1877027) B1877027
theorem B1407019 : Blo 1250443 1407019 := bstep (se 1 (by rfl) ⟨1055264, by rfl⟩ : syracuseStep 1407019 = 2110529) B2110529
theorem B1251371 : Blo 1250443 1251371 := bstep (se 1 (by rfl) ⟨938528, by rfl⟩ : syracuseStep 1251371 = 1877057) B1877057
theorem B1251383 : Blo 1250443 1251383 := bstep (se 1 (by rfl) ⟨938537, by rfl⟩ : syracuseStep 1251383 = 1877075) B1877075
theorem B6420545 : Blo 1250443 6420545 := bstep (se 2 (by rfl) ⟨2407704, by rfl⟩ : syracuseStep 6420545 = 4815409) B4815409
theorem B1251403 : Blo 1250443 1251403 := bstep (se 1 (by rfl) ⟨938552, by rfl⟩ : syracuseStep 1251403 = 1877105) B1877105
theorem B2111575 : Blo 1250443 2111575 := bstep (se 1 (by rfl) ⟨1583681, by rfl⟩ : syracuseStep 2111575 = 3167363) B3167363
theorem B1251415 : Blo 1250443 1251415 := bstep (se 1 (by rfl) ⟨938561, by rfl⟩ : syracuseStep 1251415 = 1877123) B1877123
theorem B5347421 : Blo 1250443 5347421 := bstep (se 3 (by rfl) ⟨1002641, by rfl⟩ : syracuseStep 5347421 = 2005283) B2005283
theorem B1251435 : Blo 1250443 1251435 := bstep (se 1 (by rfl) ⟨938576, by rfl⟩ : syracuseStep 1251435 = 1877153) B1877153
theorem B1251447 : Blo 1250443 1251447 := bstep (se 1 (by rfl) ⟨938585, by rfl⟩ : syracuseStep 1251447 = 1877171) B1877171
theorem B1251467 : Blo 1250443 1251467 := bstep (se 1 (by rfl) ⟨938600, by rfl⟩ : syracuseStep 1251467 = 1877201) B1877201
theorem B1407127 : Blo 1250443 1407127 := bstep (se 1 (by rfl) ⟨1055345, by rfl⟩ : syracuseStep 1407127 = 2110691) B2110691
theorem B1251479 : Blo 1250443 1251479 := bstep (se 1 (by rfl) ⟨938609, by rfl⟩ : syracuseStep 1251479 = 1877219) B1877219
theorem B2816153 : Blo 1250443 2816153 := bstep (se 2 (by rfl) ⟨1056057, by rfl⟩ : syracuseStep 2816153 = 2112115) B2112115
theorem B4225175 : Blo 1250443 4225175 := bstep (se 1 (by rfl) ⟨3168881, by rfl⟩ : syracuseStep 4225175 = 6337763) B6337763
theorem B1251499 : Blo 1250443 1251499 := bstep (se 1 (by rfl) ⟨938624, by rfl⟩ : syracuseStep 1251499 = 1877249) B1877249
theorem B1251511 : Blo 1250443 1251511 := bstep (se 1 (by rfl) ⟨938633, by rfl⟩ : syracuseStep 1251511 = 1877267) B1877267
theorem B1251531 : Blo 1250443 1251531 := bstep (se 1 (by rfl) ⟨938648, by rfl⟩ : syracuseStep 1251531 = 1877297) B1877297
theorem B1251543 : Blo 1250443 1251543 := bstep (se 1 (by rfl) ⟨938657, by rfl⟩ : syracuseStep 1251543 = 1877315) B1877315
theorem B1251563 : Blo 1250443 1251563 := bstep (se 1 (by rfl) ⟨938672, by rfl⟩ : syracuseStep 1251563 = 1877345) B1877345
theorem B2816243 : Blo 1250443 2816243 := bstep (se 1 (by rfl) ⟨2112182, by rfl⟩ : syracuseStep 2816243 = 4224365) B4224365
theorem B1251575 : Blo 1250443 1251575 := bstep (se 1 (by rfl) ⟨938681, by rfl⟩ : syracuseStep 1251575 = 1877363) B1877363
theorem B1251595 : Blo 1250443 1251595 := bstep (se 1 (by rfl) ⟨938696, by rfl⟩ : syracuseStep 1251595 = 1877393) B1877393
theorem B1251607 : Blo 1250443 1251607 := bstep (se 1 (by rfl) ⟨938705, by rfl⟩ : syracuseStep 1251607 = 1877411) B1877411
theorem B2816279 : Blo 1250443 2816279 := bstep (se 1 (by rfl) ⟨2112209, by rfl⟩ : syracuseStep 2816279 = 4224419) B4224419
theorem B1251627 : Blo 1250443 1251627 := bstep (se 1 (by rfl) ⟨938720, by rfl⟩ : syracuseStep 1251627 = 1877441) B1877441
theorem B1251639 : Blo 1250443 1251639 := bstep (se 1 (by rfl) ⟨938729, by rfl⟩ : syracuseStep 1251639 = 1877459) B1877459
theorem B3561803 : Blo 1250443 3561803 := bstep (se 1 (by rfl) ⟨2671352, by rfl⟩ : syracuseStep 3561803 = 5342705) B5342705
theorem B1407307 : Blo 1250443 1407307 := bstep (se 1 (by rfl) ⟨1055480, by rfl⟩ : syracuseStep 1407307 = 2110961) B2110961
theorem B1251659 : Blo 1250443 1251659 := bstep (se 1 (by rfl) ⟨938744, by rfl⟩ : syracuseStep 1251659 = 1877489) B1877489
theorem B1251671 : Blo 1250443 1251671 := bstep (se 1 (by rfl) ⟨938753, by rfl⟩ : syracuseStep 1251671 = 1877507) B1877507
theorem B1251691 : Blo 1250443 1251691 := bstep (se 1 (by rfl) ⟨938768, by rfl⟩ : syracuseStep 1251691 = 1877537) B1877537
theorem B115677557 : Blo 1250443 115677557 := bstep (se 5 (by rfl) ⟨5422385, by rfl⟩ : syracuseStep 115677557 = 10844771) B10844771
theorem B1251703 : Blo 1250443 1251703 := bstep (se 1 (by rfl) ⟨938777, by rfl⟩ : syracuseStep 1251703 = 1877555) B1877555
theorem B1251723 : Blo 1250443 1251723 := bstep (se 1 (by rfl) ⟨938792, by rfl⟩ : syracuseStep 1251723 = 1877585) B1877585
theorem B1251735 : Blo 1250443 1251735 := bstep (se 1 (by rfl) ⟨938801, by rfl⟩ : syracuseStep 1251735 = 1877603) B1877603
theorem B1251755 : Blo 1250443 1251755 := bstep (se 1 (by rfl) ⟨938816, by rfl⟩ : syracuseStep 1251755 = 1877633) B1877633
theorem B1407415 : Blo 1250443 1407415 := bstep (se 1 (by rfl) ⟨1055561, by rfl⟩ : syracuseStep 1407415 = 2111123) B2111123
theorem B1251767 : Blo 1250443 1251767 := bstep (se 1 (by rfl) ⟨938825, by rfl⟩ : syracuseStep 1251767 = 1877651) B1877651
theorem B5708225 : Blo 1250443 5708225 := bstep (se 2 (by rfl) ⟨2140584, by rfl⟩ : syracuseStep 5708225 = 4281169) B4281169
theorem B2816459 : Blo 1250443 2816459 := bstep (se 1 (by rfl) ⟨2112344, by rfl⟩ : syracuseStep 2816459 = 4224689) B4224689
theorem B1251787 : Blo 1250443 1251787 := bstep (se 1 (by rfl) ⟨938840, by rfl⟩ : syracuseStep 1251787 = 1877681) B1877681
theorem B2374103 : Blo 1250443 2374103 := bstep (se 1 (by rfl) ⟨1780577, by rfl⟩ : syracuseStep 2374103 = 3561155) B3561155
theorem B1251799 : Blo 1250443 1251799 := bstep (se 1 (by rfl) ⟨938849, by rfl⟩ : syracuseStep 1251799 = 1877699) B1877699
theorem B4749785 : Blo 1250443 4749785 := bstep (se 2 (by rfl) ⟨1781169, by rfl⟩ : syracuseStep 4749785 = 3562339) B3562339
theorem B14260697 : Blo 1250443 14260697 := bstep (se 2 (by rfl) ⟨5347761, by rfl⟩ : syracuseStep 14260697 = 10695523) B10695523
theorem B1251819 : Blo 1250443 1251819 := bstep (se 1 (by rfl) ⟨938864, by rfl⟩ : syracuseStep 1251819 = 1877729) B1877729
theorem B1251831 : Blo 1250443 1251831 := bstep (se 1 (by rfl) ⟨938873, by rfl⟩ : syracuseStep 1251831 = 1877747) B1877747
theorem B2816513 : Blo 1250443 2816513 := bstep (se 2 (by rfl) ⟨1056192, by rfl⟩ : syracuseStep 2816513 = 2112385) B2112385
theorem B1251851 : Blo 1250443 1251851 := bstep (se 1 (by rfl) ⟨938888, by rfl⟩ : syracuseStep 1251851 = 1877777) B1877777
theorem B1251863 : Blo 1250443 1251863 := bstep (se 1 (by rfl) ⟨938897, by rfl⟩ : syracuseStep 1251863 = 1877795) B1877795
theorem B3168791 : Blo 1250443 3168791 := bstep (se 1 (by rfl) ⟨2376593, by rfl⟩ : syracuseStep 3168791 = 4753187) B4753187
theorem B1251883 : Blo 1250443 1251883 := bstep (se 1 (by rfl) ⟨938912, by rfl⟩ : syracuseStep 1251883 = 1877825) B1877825
theorem B1251895 : Blo 1250443 1251895 := bstep (se 1 (by rfl) ⟨938921, by rfl⟩ : syracuseStep 1251895 = 1877843) B1877843
theorem B1251915 : Blo 1250443 1251915 := bstep (se 1 (by rfl) ⟨938936, by rfl⟩ : syracuseStep 1251915 = 1877873) B1877873
theorem B1251927 : Blo 1250443 1251927 := bstep (se 1 (by rfl) ⟨938945, by rfl⟩ : syracuseStep 1251927 = 1877891) B1877891
theorem B12835421 : Blo 1250443 12835421 := bstep (se 3 (by rfl) ⟨2406641, by rfl⟩ : syracuseStep 12835421 = 4813283) B4813283
theorem B1407595 : Blo 1250443 1407595 := bstep (se 1 (by rfl) ⟨1055696, by rfl⟩ : syracuseStep 1407595 = 2111393) B2111393
theorem B1251947 : Blo 1250443 1251947 := bstep (se 1 (by rfl) ⟨938960, by rfl⟩ : syracuseStep 1251947 = 1877921) B1877921
theorem B1251959 : Blo 1250443 1251959 := bstep (se 1 (by rfl) ⟨938969, by rfl⟩ : syracuseStep 1251959 = 1877939) B1877939
theorem B1251979 : Blo 1250443 1251979 := bstep (se 1 (by rfl) ⟨938984, by rfl⟩ : syracuseStep 1251979 = 1877969) B1877969
theorem B1251991 : Blo 1250443 1251991 := bstep (se 1 (by rfl) ⟨938993, by rfl⟩ : syracuseStep 1251991 = 1877987) B1877987
theorem B1252011 : Blo 1250443 1252011 := bstep (se 1 (by rfl) ⟨939008, by rfl⟩ : syracuseStep 1252011 = 1878017) B1878017
theorem B4225715 : Blo 1250443 4225715 := bstep (se 1 (by rfl) ⟨3169286, by rfl⟩ : syracuseStep 4225715 = 6338573) B6338573
theorem B1252023 : Blo 1250443 1252023 := bstep (se 1 (by rfl) ⟨939017, by rfl⟩ : syracuseStep 1252023 = 1878035) B1878035
theorem B2112203 : Blo 1250443 2112203 := bstep (se 1 (by rfl) ⟨1584152, by rfl⟩ : syracuseStep 2112203 = 3168305) B3168305
theorem B1252043 : Blo 1250443 1252043 := bstep (se 1 (by rfl) ⟨939032, by rfl⟩ : syracuseStep 1252043 = 1878065) B1878065
theorem B1407703 : Blo 1250443 1407703 := bstep (se 1 (by rfl) ⟨1055777, by rfl⟩ : syracuseStep 1407703 = 2111555) B2111555
theorem B10828505 : Blo 1250443 10828505 := bstep (se 2 (by rfl) ⟨4060689, by rfl⟩ : syracuseStep 10828505 = 8121379) B8121379
theorem B2816729 : Blo 1250443 2816729 := bstep (se 2 (by rfl) ⟨1056273, by rfl⟩ : syracuseStep 2816729 = 2112547) B2112547
theorem B1252055 : Blo 1250443 1252055 := bstep (se 1 (by rfl) ⟨939041, by rfl⟩ : syracuseStep 1252055 = 1878083) B1878083
theorem B1252075 : Blo 1250443 1252075 := bstep (se 1 (by rfl) ⟨939056, by rfl⟩ : syracuseStep 1252075 = 1878113) B1878113
theorem B40614641 : Blo 1250443 40614641 := bstep (se 2 (by rfl) ⟨15230490, by rfl⟩ : syracuseStep 40614641 = 30460981) B30460981
theorem B1252087 : Blo 1250443 1252087 := bstep (se 1 (by rfl) ⟨939065, by rfl⟩ : syracuseStep 1252087 = 1878131) B1878131
theorem B1252107 : Blo 1250443 1252107 := bstep (se 1 (by rfl) ⟨939080, by rfl⟩ : syracuseStep 1252107 = 1878161) B1878161
theorem B6421265 : Blo 1250443 6421265 := bstep (se 2 (by rfl) ⟨2407974, by rfl⟩ : syracuseStep 6421265 = 4815949) B4815949
theorem B4750103 : Blo 1250443 4750103 := bstep (se 1 (by rfl) ⟨3562577, by rfl⟩ : syracuseStep 4750103 = 7125155) B7125155
theorem B1252119 : Blo 1250443 1252119 := bstep (se 1 (by rfl) ⟨939089, by rfl⟩ : syracuseStep 1252119 = 1878179) B1878179
theorem B10697507 : Blo 1250443 10697507 := bstep (se 1 (by rfl) ⟨8023130, by rfl⟩ : syracuseStep 10697507 = 16046261) B16046261
theorem B1252139 : Blo 1250443 1252139 := bstep (se 1 (by rfl) ⟨939104, by rfl⟩ : syracuseStep 1252139 = 1878209) B1878209
theorem B2816819 : Blo 1250443 2816819 := bstep (se 1 (by rfl) ⟨2112614, by rfl⟩ : syracuseStep 2816819 = 4225229) B4225229
theorem B1252151 : Blo 1250443 1252151 := bstep (se 1 (by rfl) ⟨939113, by rfl⟩ : syracuseStep 1252151 = 1878227) B1878227
theorem B2112331 : Blo 1250443 2112331 := bstep (se 1 (by rfl) ⟨1584248, by rfl⟩ : syracuseStep 2112331 = 3168497) B3168497
theorem B1252171 : Blo 1250443 1252171 := bstep (se 1 (by rfl) ⟨939128, by rfl⟩ : syracuseStep 1252171 = 1878257) B1878257
theorem B2816855 : Blo 1250443 2816855 := bstep (se 1 (by rfl) ⟨2112641, by rfl⟩ : syracuseStep 2816855 = 4225283) B4225283
theorem B1252183 : Blo 1250443 1252183 := bstep (se 1 (by rfl) ⟨939137, by rfl⟩ : syracuseStep 1252183 = 1878275) B1878275
theorem B1252203 : Blo 1250443 1252203 := bstep (se 1 (by rfl) ⟨939152, by rfl⟩ : syracuseStep 1252203 = 1878305) B1878305
theorem B1252215 : Blo 1250443 1252215 := bstep (se 1 (by rfl) ⟨939161, by rfl⟩ : syracuseStep 1252215 = 1878323) B1878323
theorem B1407883 : Blo 1250443 1407883 := bstep (se 1 (by rfl) ⟨1055912, by rfl⟩ : syracuseStep 1407883 = 2111825) B2111825
theorem B1252235 : Blo 1250443 1252235 := bstep (se 1 (by rfl) ⟨939176, by rfl⟩ : syracuseStep 1252235 = 1878353) B1878353
theorem B1252247 : Blo 1250443 1252247 := bstep (se 1 (by rfl) ⟨939185, by rfl⟩ : syracuseStep 1252247 = 1878371) B1878371
theorem B1252267 : Blo 1250443 1252267 := bstep (se 1 (by rfl) ⟨939200, by rfl⟩ : syracuseStep 1252267 = 1878401) B1878401
theorem B6421427 : Blo 1250443 6421427 := bstep (se 1 (by rfl) ⟨4816070, by rfl⟩ : syracuseStep 6421427 = 9632141) B9632141
theorem B2710451 : Blo 1250443 2710451 := bstep (se 1 (by rfl) ⟨2032838, by rfl⟩ : syracuseStep 2710451 = 4065677) B4065677
theorem B1252279 : Blo 1250443 1252279 := bstep (se 1 (by rfl) ⟨939209, by rfl⟩ : syracuseStep 1252279 = 1878419) B1878419
theorem B4225985 : Blo 1250443 4225985 := bstep (se 2 (by rfl) ⟨1584744, by rfl⟩ : syracuseStep 4225985 = 3169489) B3169489
theorem B1252299 : Blo 1250443 1252299 := bstep (se 1 (by rfl) ⟨939224, by rfl⟩ : syracuseStep 1252299 = 1878449) B1878449
theorem B1252311 : Blo 1250443 1252311 := bstep (se 1 (by rfl) ⟨939233, by rfl⟩ : syracuseStep 1252311 = 1878467) B1878467
theorem B2005975 : Blo 1250443 2005975 := bstep (se 1 (by rfl) ⟨1504481, by rfl⟩ : syracuseStep 2005975 = 3008963) B3008963
theorem B2112473 : Blo 1250443 2112473 := bstep (se 2 (by rfl) ⟨792177, by rfl⟩ : syracuseStep 2112473 = 1584355) B1584355
theorem B6339545 : Blo 1250443 6339545 := bstep (se 2 (by rfl) ⟨2377329, by rfl⟩ : syracuseStep 6339545 = 4754659) B4754659
theorem B1252331 : Blo 1250443 1252331 := bstep (se 1 (by rfl) ⟨939248, by rfl⟩ : syracuseStep 1252331 = 1878497) B1878497
theorem B1407991 : Blo 1250443 1407991 := bstep (se 1 (by rfl) ⟨1055993, by rfl⟩ : syracuseStep 1407991 = 2111987) B2111987
theorem B1252343 : Blo 1250443 1252343 := bstep (se 1 (by rfl) ⟨939257, by rfl⟩ : syracuseStep 1252343 = 1878515) B1878515
theorem B2817035 : Blo 1250443 2817035 := bstep (se 1 (by rfl) ⟨2112776, by rfl⟩ : syracuseStep 2817035 = 4225553) B4225553
theorem B1252363 : Blo 1250443 1252363 := bstep (se 1 (by rfl) ⟨939272, by rfl⟩ : syracuseStep 1252363 = 1878545) B1878545
theorem B1252375 : Blo 1250443 1252375 := bstep (se 1 (by rfl) ⟨939281, by rfl⟩ : syracuseStep 1252375 = 1878563) B1878563
theorem B1252395 : Blo 1250443 1252395 := bstep (se 1 (by rfl) ⟨939296, by rfl⟩ : syracuseStep 1252395 = 1878593) B1878593
theorem B1252407 : Blo 1250443 1252407 := bstep (se 1 (by rfl) ⟨939305, by rfl⟩ : syracuseStep 1252407 = 1878611) B1878611
theorem B2817089 : Blo 1250443 2817089 := bstep (se 2 (by rfl) ⟨1056408, by rfl⟩ : syracuseStep 2817089 = 2112817) B2112817
theorem B1252427 : Blo 1250443 1252427 := bstep (se 1 (by rfl) ⟨939320, by rfl⟩ : syracuseStep 1252427 = 1878641) B1878641
theorem B1252439 : Blo 1250443 1252439 := bstep (se 1 (by rfl) ⟨939329, by rfl⟩ : syracuseStep 1252439 = 1878659) B1878659
theorem B2112601 : Blo 1250443 2112601 := bstep (se 2 (by rfl) ⟨792225, by rfl⟩ : syracuseStep 2112601 = 1584451) B1584451
theorem B2374771 : Blo 1250443 2374771 := bstep (se 1 (by rfl) ⟨1781078, by rfl⟩ : syracuseStep 2374771 = 3562157) B3562157
theorem B1408171 : Blo 1250443 1408171 := bstep (se 1 (by rfl) ⟨1056128, by rfl⟩ : syracuseStep 1408171 = 2112257) B2112257
theorem B8019161 : Blo 1250443 8019161 := bstep (se 2 (by rfl) ⟨3007185, by rfl⟩ : syracuseStep 8019161 = 6014371) B6014371
theorem B10419461 : Blo 1250443 10419461 := bstep (se 4 (by rfl) ⟨976824, by rfl⟩ : syracuseStep 10419461 = 1953649) B1953649
theorem B9018641 : Blo 1250443 9018641 := bstep (se 2 (by rfl) ⟨3381990, by rfl⟩ : syracuseStep 9018641 = 6763981) B6763981
theorem B1408279 : Blo 1250443 1408279 := bstep (se 1 (by rfl) ⟨1056209, by rfl⟩ : syracuseStep 1408279 = 2112419) B2112419
theorem B2817305 : Blo 1250443 2817305 := bstep (se 2 (by rfl) ⟨1056489, by rfl⟩ : syracuseStep 2817305 = 2112979) B2112979
theorem B3169601 : Blo 1250443 3169601 := bstep (se 2 (by rfl) ⟨1188600, by rfl⟩ : syracuseStep 3169601 = 2377201) B2377201
theorem B2170199 : Blo 1250443 2170199 := bstep (se 1 (by rfl) ⟨1627649, by rfl⟩ : syracuseStep 2170199 = 3255299) B3255299
theorem B2817395 : Blo 1250443 2817395 := bstep (se 1 (by rfl) ⟨2113046, by rfl⟩ : syracuseStep 2817395 = 4226093) B4226093
theorem B2817431 : Blo 1250443 2817431 := bstep (se 1 (by rfl) ⟨2113073, by rfl⟩ : syracuseStep 2817431 = 4226147) B4226147
theorem B1269163 : Blo 1250443 1269163 := bstep (se 1 (by rfl) ⟨951872, by rfl⟩ : syracuseStep 1269163 = 1903745) B1903745
theorem B4750771 : Blo 1250443 4750771 := bstep (se 1 (by rfl) ⟨3563078, by rfl⟩ : syracuseStep 4750771 = 7126157) B7126157
theorem B1408459 : Blo 1250443 1408459 := bstep (se 1 (by rfl) ⟨1056344, by rfl⟩ : syracuseStep 1408459 = 2112689) B2112689
theorem B4226525 : Blo 1250443 4226525 := bstep (se 3 (by rfl) ⟨792473, by rfl⟩ : syracuseStep 4226525 = 1584947) B1584947
theorem B8560145 : Blo 1250443 8560145 := bstep (se 2 (by rfl) ⟨3210054, by rfl⟩ : syracuseStep 8560145 = 6420109) B6420109
theorem B10698257 : Blo 1250443 10698257 := bstep (se 2 (by rfl) ⟨4011846, by rfl⟩ : syracuseStep 10698257 = 8023693) B8023693
theorem B2375219 : Blo 1250443 2375219 := bstep (se 1 (by rfl) ⟨1781414, by rfl⟩ : syracuseStep 2375219 = 3562829) B3562829
theorem B1408567 : Blo 1250443 1408567 := bstep (se 1 (by rfl) ⟨1056425, by rfl⟩ : syracuseStep 1408567 = 2112851) B2112851
theorem B2817611 : Blo 1250443 2817611 := bstep (se 1 (by rfl) ⟨2113208, by rfl⟩ : syracuseStep 2817611 = 4226417) B4226417
theorem B2375257 : Blo 1250443 2375257 := bstep (se 2 (by rfl) ⟨890721, by rfl⟩ : syracuseStep 2375257 = 1781443) B1781443
theorem B2817665 : Blo 1250443 2817665 := bstep (se 2 (by rfl) ⟨1056624, by rfl⟩ : syracuseStep 2817665 = 2113249) B2113249
theorem B2113175 : Blo 1250443 2113175 := bstep (se 1 (by rfl) ⟨1584881, by rfl⟩ : syracuseStep 2113175 = 3169763) B3169763
theorem B1875671 : Blo 1250443 1875671 := bstep (se 1 (by rfl) ⟨1406753, by rfl⟩ : syracuseStep 1875671 = 2813507) B2813507
theorem B1408747 : Blo 1250443 1408747 := bstep (se 1 (by rfl) ⟨1056560, by rfl⟩ : syracuseStep 1408747 = 2113121) B2113121
theorem B2113303 : Blo 1250443 2113303 := bstep (se 1 (by rfl) ⟨1584977, by rfl⟩ : syracuseStep 2113303 = 3169955) B3169955
theorem B1875737 : Blo 1250443 1875737 := bstep (se 2 (by rfl) ⟨703401, by rfl⟩ : syracuseStep 1875737 = 1406803) B1406803
theorem B6012737 : Blo 1250443 6012737 := bstep (se 2 (by rfl) ⟨2254776, by rfl⟩ : syracuseStep 6012737 = 4509553) B4509553
theorem B3211073 : Blo 1250443 3211073 := bstep (se 2 (by rfl) ⟨1204152, by rfl⟩ : syracuseStep 3211073 = 2408305) B2408305
theorem B4063051 : Blo 1250443 4063051 := bstep (se 1 (by rfl) ⟨3047288, by rfl⟩ : syracuseStep 4063051 = 6094577) B6094577
theorem B1408855 : Blo 1250443 1408855 := bstep (se 1 (by rfl) ⟨1056641, by rfl⟩ : syracuseStep 1408855 = 2113283) B2113283
theorem B2817881 : Blo 1250443 2817881 := bstep (se 2 (by rfl) ⟨1056705, by rfl⟩ : syracuseStep 2817881 = 2113411) B2113411
theorem B3170137 : Blo 1250443 3170137 := bstep (se 2 (by rfl) ⟨1188801, by rfl⟩ : syracuseStep 3170137 = 2377603) B2377603
theorem B7610213 : Blo 1250443 7610213 := bstep (se 4 (by rfl) ⟨713457, by rfl⟩ : syracuseStep 7610213 = 1426915) B1426915
theorem B1875851 : Blo 1250443 1875851 := bstep (se 1 (by rfl) ⟨1406888, by rfl⟩ : syracuseStep 1875851 = 2813777) B2813777
theorem B1875863 : Blo 1250443 1875863 := bstep (se 1 (by rfl) ⟨1406897, by rfl⟩ : syracuseStep 1875863 = 2813795) B2813795
theorem B3563443 : Blo 1250443 3563443 := bstep (se 1 (by rfl) ⟨2672582, by rfl⟩ : syracuseStep 3563443 = 5345165) B5345165
theorem B2817971 : Blo 1250443 2817971 := bstep (se 1 (by rfl) ⟨2113478, by rfl⟩ : syracuseStep 2817971 = 4226957) B4226957
theorem B1875929 : Blo 1250443 1875929 := bstep (se 2 (by rfl) ⟨703473, by rfl⟩ : syracuseStep 1875929 = 1406947) B1406947
theorem B3006425 : Blo 1250443 3006425 := bstep (se 2 (by rfl) ⟨1127409, by rfl⟩ : syracuseStep 3006425 = 2254819) B2254819
theorem B1875983 : Blo 1250443 1875983 := bstep (se 1 (by rfl) ⟨1406987, by rfl⟩ : syracuseStep 1875983 = 2813975) B2813975
theorem B1876025 : Blo 1250443 1876025 := bstep (se 2 (by rfl) ⟨703509, by rfl⟩ : syracuseStep 1876025 = 1407019) B1407019
theorem B1876103 : Blo 1250443 1876103 := bstep (se 1 (by rfl) ⟨1407077, by rfl⟩ : syracuseStep 1876103 = 2814155) B2814155
theorem B1876139 : Blo 1250443 1876139 := bstep (se 1 (by rfl) ⟨1407104, by rfl⟩ : syracuseStep 1876139 = 2814209) B2814209
theorem B1876169 : Blo 1250443 1876169 := bstep (se 2 (by rfl) ⟨703563, by rfl⟩ : syracuseStep 1876169 = 1407127) B1407127
theorem B4751561 : Blo 1250443 4751561 := bstep (se 2 (by rfl) ⟨1781835, by rfl⟩ : syracuseStep 4751561 = 3563671) B3563671
theorem B7127297 : Blo 1250443 7127297 := bstep (se 2 (by rfl) ⟨2672736, by rfl⟩ : syracuseStep 7127297 = 5345473) B5345473
theorem B1876283 : Blo 1250443 1876283 := bstep (se 1 (by rfl) ⟨1407212, by rfl⟩ : syracuseStep 1876283 = 2814425) B2814425
theorem B1876343 : Blo 1250443 1876343 := bstep (se 1 (by rfl) ⟨1407257, by rfl⟩ : syracuseStep 1876343 = 2814515) B2814515
theorem B1876367 : Blo 1250443 1876367 := bstep (se 1 (by rfl) ⟨1407275, by rfl⟩ : syracuseStep 1876367 = 2814551) B2814551
theorem B3383699 : Blo 1250443 3383699 := bstep (se 1 (by rfl) ⟨2537774, by rfl⟩ : syracuseStep 3383699 = 5075549) B5075549
theorem B1876409 : Blo 1250443 1876409 := bstep (se 2 (by rfl) ⟨703653, by rfl⟩ : syracuseStep 1876409 = 1407307) B1407307
theorem B1876487 : Blo 1250443 1876487 := bstep (se 1 (by rfl) ⟨1407365, by rfl⟩ : syracuseStep 1876487 = 2814731) B2814731
theorem B2671147 : Blo 1250443 2671147 := bstep (se 1 (by rfl) ⟨2003360, by rfl⟩ : syracuseStep 2671147 = 4006721) B4006721
theorem B1876523 : Blo 1250443 1876523 := bstep (se 1 (by rfl) ⟨1407392, by rfl⟩ : syracuseStep 1876523 = 2814785) B2814785
theorem B1876553 : Blo 1250443 1876553 := bstep (se 2 (by rfl) ⟨703707, by rfl⟩ : syracuseStep 1876553 = 1407415) B1407415
theorem B10691149 : Blo 1250443 10691149 := bstep (se 3 (by rfl) ⟨2004590, by rfl⟩ : syracuseStep 10691149 = 4009181) B4009181
theorem B1876667 : Blo 1250443 1876667 := bstep (se 1 (by rfl) ⟨1407500, by rfl⟩ : syracuseStep 1876667 = 2815001) B2815001
theorem B1876727 : Blo 1250443 1876727 := bstep (se 1 (by rfl) ⟨1407545, by rfl⟩ : syracuseStep 1876727 = 2815091) B2815091
theorem B1876751 : Blo 1250443 1876751 := bstep (se 1 (by rfl) ⟨1407563, by rfl⟩ : syracuseStep 1876751 = 2815127) B2815127
theorem B2253601 : Blo 1250443 2253601 := bstep (se 2 (by rfl) ⟨845100, by rfl⟩ : syracuseStep 2253601 = 1690201) B1690201
theorem B1876793 : Blo 1250443 1876793 := bstep (se 2 (by rfl) ⟨703797, by rfl⟩ : syracuseStep 1876793 = 1407595) B1407595
theorem B14451571 : Blo 1250443 14451571 := bstep (se 1 (by rfl) ⟨10838678, by rfl⟩ : syracuseStep 14451571 = 21677357) B21677357
theorem B1876871 : Blo 1250443 1876871 := bstep (se 1 (by rfl) ⟨1407653, by rfl⟩ : syracuseStep 1876871 = 2815307) B2815307
theorem B1876907 : Blo 1250443 1876907 := bstep (se 1 (by rfl) ⟨1407680, by rfl⟩ : syracuseStep 1876907 = 2815361) B2815361
theorem B1876937 : Blo 1250443 1876937 := bstep (se 2 (by rfl) ⟨703851, by rfl⟩ : syracuseStep 1876937 = 1407703) B1407703
theorem B6767569 : Blo 1250443 6767569 := bstep (se 2 (by rfl) ⟨2537838, by rfl⟩ : syracuseStep 6767569 = 5075677) B5075677
theorem B5415947 : Blo 1250443 5415947 := bstep (se 1 (by rfl) ⟨4061960, by rfl⟩ : syracuseStep 5415947 = 8123921) B8123921
theorem B1877051 : Blo 1250443 1877051 := bstep (se 1 (by rfl) ⟨1407788, by rfl⟩ : syracuseStep 1877051 = 2815577) B2815577
theorem B1877111 : Blo 1250443 1877111 := bstep (se 1 (by rfl) ⟨1407833, by rfl⟩ : syracuseStep 1877111 = 2815667) B2815667
theorem B4752503 : Blo 1250443 4752503 := bstep (se 1 (by rfl) ⟨3564377, by rfl⟩ : syracuseStep 4752503 = 7128755) B7128755
theorem B1877135 : Blo 1250443 1877135 := bstep (se 1 (by rfl) ⟨1407851, by rfl⟩ : syracuseStep 1877135 = 2815703) B2815703
theorem B1877177 : Blo 1250443 1877177 := bstep (se 2 (by rfl) ⟨703941, by rfl⟩ : syracuseStep 1877177 = 1407883) B1407883
theorem B1877255 : Blo 1250443 1877255 := bstep (se 1 (by rfl) ⟨1407941, by rfl⟩ : syracuseStep 1877255 = 2815883) B2815883
theorem B1877291 : Blo 1250443 1877291 := bstep (se 1 (by rfl) ⟨1407968, by rfl⟩ : syracuseStep 1877291 = 2815937) B2815937
theorem B2377019 : Blo 1250443 2377019 := bstep (se 1 (by rfl) ⟨1782764, by rfl⟩ : syracuseStep 2377019 = 3565529) B3565529
theorem B1877321 : Blo 1250443 1877321 := bstep (se 2 (by rfl) ⟨703995, by rfl⟩ : syracuseStep 1877321 = 1407991) B1407991
theorem B4507015 : Blo 1250443 4507015 := bstep (se 1 (by rfl) ⟨3380261, by rfl⟩ : syracuseStep 4507015 = 6760523) B6760523
theorem B9495953 : Blo 1250443 9495953 := bstep (se 2 (by rfl) ⟨3560982, by rfl⟩ : syracuseStep 9495953 = 7121965) B7121965
theorem B3564947 : Blo 1250443 3564947 := bstep (se 1 (by rfl) ⟨2673710, by rfl⟩ : syracuseStep 3564947 = 5347421) B5347421
theorem B1877435 : Blo 1250443 1877435 := bstep (se 1 (by rfl) ⟨1408076, by rfl⟩ : syracuseStep 1877435 = 2816153) B2816153
theorem B1877495 : Blo 1250443 1877495 := bstep (se 1 (by rfl) ⟨1408121, by rfl⟩ : syracuseStep 1877495 = 2816243) B2816243
theorem B1877519 : Blo 1250443 1877519 := bstep (se 1 (by rfl) ⟨1408139, by rfl⟩ : syracuseStep 1877519 = 2816279) B2816279
theorem B1877561 : Blo 1250443 1877561 := bstep (se 2 (by rfl) ⟨704085, by rfl⟩ : syracuseStep 1877561 = 1408171) B1408171
theorem B4220477 : Blo 1250443 4220477 := bstep (se 3 (by rfl) ⟨791339, by rfl⟩ : syracuseStep 4220477 = 1582679) B1582679
theorem B1877639 : Blo 1250443 1877639 := bstep (se 1 (by rfl) ⟨1408229, by rfl⟩ : syracuseStep 1877639 = 2816459) B2816459
theorem B1582735 : Blo 1250443 1582735 := bstep (se 1 (by rfl) ⟨1187051, by rfl⟩ : syracuseStep 1582735 = 2374103) B2374103
theorem B1877675 : Blo 1250443 1877675 := bstep (se 1 (by rfl) ⟨1408256, by rfl⟩ : syracuseStep 1877675 = 2816513) B2816513
theorem B1877705 : Blo 1250443 1877705 := bstep (se 2 (by rfl) ⟨704139, by rfl⟩ : syracuseStep 1877705 = 1408279) B1408279
theorem B2377505 : Blo 1250443 2377505 := bstep (se 2 (by rfl) ⟨891564, by rfl⟩ : syracuseStep 2377505 = 1783129) B1783129
theorem B7219003 : Blo 1250443 7219003 := bstep (se 1 (by rfl) ⟨5414252, by rfl⟩ : syracuseStep 7219003 = 10828505) B10828505
theorem B1877819 : Blo 1250443 1877819 := bstep (se 1 (by rfl) ⟨1408364, by rfl⟩ : syracuseStep 1877819 = 2816729) B2816729
theorem B27076427 : Blo 1250443 27076427 := bstep (se 1 (by rfl) ⟨20307320, by rfl⟩ : syracuseStep 27076427 = 40614641) B40614641
theorem B1877879 : Blo 1250443 1877879 := bstep (se 1 (by rfl) ⟨1408409, by rfl⟩ : syracuseStep 1877879 = 2816819) B2816819
theorem B1877903 : Blo 1250443 1877903 := bstep (se 1 (by rfl) ⟨1408427, by rfl⟩ : syracuseStep 1877903 = 2816855) B2816855
theorem B6334361 : Blo 1250443 6334361 := bstep (se 2 (by rfl) ⟨2375385, by rfl⟩ : syracuseStep 6334361 = 4750771) B4750771
theorem B1877945 : Blo 1250443 1877945 := bstep (se 2 (by rfl) ⟨704229, by rfl⟩ : syracuseStep 1877945 = 1408459) B1408459
theorem B1878023 : Blo 1250443 1878023 := bstep (se 1 (by rfl) ⟨1408517, by rfl⟩ : syracuseStep 1878023 = 2817035) B2817035
theorem B1878059 : Blo 1250443 1878059 := bstep (se 1 (by rfl) ⟨1408544, by rfl⟩ : syracuseStep 1878059 = 2817089) B2817089
theorem B4753475 : Blo 1250443 4753475 := bstep (se 1 (by rfl) ⟨3565106, by rfl⟩ : syracuseStep 4753475 = 7130213) B7130213
theorem B1878089 : Blo 1250443 1878089 := bstep (se 2 (by rfl) ⟨704283, by rfl⟩ : syracuseStep 1878089 = 1408567) B1408567
theorem B3565721 : Blo 1250443 3565721 := bstep (se 2 (by rfl) ⟨1337145, by rfl⟩ : syracuseStep 3565721 = 2674291) B2674291
theorem B1878203 : Blo 1250443 1878203 := bstep (se 1 (by rfl) ⟨1408652, by rfl⟩ : syracuseStep 1878203 = 2817305) B2817305
theorem B1878263 : Blo 1250443 1878263 := bstep (se 1 (by rfl) ⟨1408697, by rfl⟩ : syracuseStep 1878263 = 2817395) B2817395
theorem B1878287 : Blo 1250443 1878287 := bstep (se 1 (by rfl) ⟨1408715, by rfl⟩ : syracuseStep 1878287 = 2817431) B2817431
theorem B1878329 : Blo 1250443 1878329 := bstep (se 2 (by rfl) ⟨704373, by rfl⟩ : syracuseStep 1878329 = 1408747) B1408747
theorem B1583479 : Blo 1250443 1583479 := bstep (se 1 (by rfl) ⟨1187609, by rfl⟩ : syracuseStep 1583479 = 2375219) B2375219
theorem B1878407 : Blo 1250443 1878407 := bstep (se 1 (by rfl) ⟨1408805, by rfl⟩ : syracuseStep 1878407 = 2817611) B2817611
theorem B1878443 : Blo 1250443 1878443 := bstep (se 1 (by rfl) ⟨1408832, by rfl⟩ : syracuseStep 1878443 = 2817665) B2817665
theorem B5417401 : Blo 1250443 5417401 := bstep (se 2 (by rfl) ⟨2031525, by rfl⟩ : syracuseStep 5417401 = 4063051) B4063051
theorem B7129529 : Blo 1250443 7129529 := bstep (se 2 (by rfl) ⟨2673573, by rfl⟩ : syracuseStep 7129529 = 5347147) B5347147
theorem B1878473 : Blo 1250443 1878473 := bstep (se 2 (by rfl) ⟨704427, by rfl⟩ : syracuseStep 1878473 = 1408855) B1408855
theorem B4819409 : Blo 1250443 4819409 := bstep (se 2 (by rfl) ⟨1807278, by rfl⟩ : syracuseStep 4819409 = 3614557) B3614557
theorem B4008491 : Blo 1250443 4008491 := bstep (se 1 (by rfl) ⟨3006368, by rfl⟩ : syracuseStep 4008491 = 6012737) B6012737
theorem B2140715 : Blo 1250443 2140715 := bstep (se 1 (by rfl) ⟨1605536, by rfl⟩ : syracuseStep 2140715 = 3211073) B3211073
theorem B1878587 : Blo 1250443 1878587 := bstep (se 1 (by rfl) ⟨1408940, by rfl⟩ : syracuseStep 1878587 = 2817881) B2817881
theorem B5073475 : Blo 1250443 5073475 := bstep (se 1 (by rfl) ⟨3805106, by rfl⟩ : syracuseStep 5073475 = 7610213) B7610213
theorem B1878647 : Blo 1250443 1878647 := bstep (se 1 (by rfl) ⟨1408985, by rfl⟩ : syracuseStep 1878647 = 2817971) B2817971
theorem B1583803 : Blo 1250443 1583803 := bstep (se 1 (by rfl) ⟨1187852, by rfl⟩ : syracuseStep 1583803 = 2375705) B2375705
theorem B13200101 : Blo 1250443 13200101 := bstep (se 4 (by rfl) ⟨1237509, by rfl⟩ : syracuseStep 13200101 = 2475019) B2475019
theorem B1780537 : Blo 1250443 1780537 := bstep (se 2 (by rfl) ⟨667701, by rfl⟩ : syracuseStep 1780537 = 1335403) B1335403
theorem B5073799 : Blo 1250443 5073799 := bstep (se 1 (by rfl) ⟨3805349, by rfl⟩ : syracuseStep 5073799 = 7610699) B7610699
theorem B1780651 : Blo 1250443 1780651 := bstep (se 1 (by rfl) ⟨1335488, by rfl⟩ : syracuseStep 1780651 = 2670977) B2670977
theorem B4221881 : Blo 1250443 4221881 := bstep (se 2 (by rfl) ⟨1583205, by rfl⟩ : syracuseStep 4221881 = 3166411) B3166411
theorem B3165227 : Blo 1250443 3165227 := bstep (se 1 (by rfl) ⟨2373920, by rfl⟩ : syracuseStep 3165227 = 4747841) B4747841
theorem B13896791 : Blo 1250443 13896791 := bstep (se 1 (by rfl) ⟨10422593, by rfl⟩ : syracuseStep 13896791 = 20845187) B20845187
theorem B1805431 : Blo 1250443 1805431 := bstep (se 1 (by rfl) ⟨1354073, by rfl⟩ : syracuseStep 1805431 = 2708147) B2708147
theorem B64990349 : Blo 1250443 64990349 := bstep (se 3 (by rfl) ⟨12185690, by rfl⟩ : syracuseStep 64990349 = 24371381) B24371381
theorem B1780879 : Blo 1250443 1780879 := bstep (se 1 (by rfl) ⟨1335659, by rfl⟩ : syracuseStep 1780879 = 2671319) B2671319
theorem B1584299 : Blo 1250443 1584299 := bstep (se 1 (by rfl) ⟨1188224, by rfl⟩ : syracuseStep 1584299 = 2376449) B2376449
theorem B4222475 : Blo 1250443 4222475 := bstep (se 1 (by rfl) ⟨3166856, by rfl⟩ : syracuseStep 4222475 = 6333713) B6333713
theorem B2854415 : Blo 1250443 2854415 := bstep (se 1 (by rfl) ⟨2140811, by rfl⟩ : syracuseStep 2854415 = 4281623) B4281623
theorem B27053669 : Blo 1250443 27053669 := bstep (se 4 (by rfl) ⟨2536281, by rfl⟩ : syracuseStep 27053669 = 5072563) B5072563
theorem B4222583 : Blo 1250443 4222583 := bstep (se 1 (by rfl) ⟨3166937, by rfl⟩ : syracuseStep 4222583 = 6333875) B6333875
theorem B4009591 : Blo 1250443 4009591 := bstep (se 1 (by rfl) ⟨3007193, by rfl⟩ : syracuseStep 4009591 = 6014387) B6014387
theorem B1584775 : Blo 1250443 1584775 := bstep (se 1 (by rfl) ⟨1188581, by rfl⟩ : syracuseStep 1584775 = 2377163) B2377163
theorem B4755145 : Blo 1250443 4755145 := bstep (se 2 (by rfl) ⟨1783179, by rfl⟩ : syracuseStep 4755145 = 3566359) B3566359
theorem B9498383 : Blo 1250443 9498383 := bstep (se 1 (by rfl) ⟨7123787, by rfl⟩ : syracuseStep 9498383 = 14247575) B14247575
theorem B3166067 : Blo 1250443 3166067 := bstep (se 1 (by rfl) ⟨2374550, by rfl⟩ : syracuseStep 3166067 = 4749101) B4749101
theorem B2813831 : Blo 1250443 2813831 := bstep (se 1 (by rfl) ⟨2110373, by rfl⟩ : syracuseStep 2813831 = 4220747) B4220747
theorem B3166087 : Blo 1250443 3166087 := bstep (se 1 (by rfl) ⟨2374565, by rfl⟩ : syracuseStep 3166087 = 4749131) B4749131
theorem B6418321 : Blo 1250443 6418321 := bstep (se 2 (by rfl) ⟨2406870, by rfl⟩ : syracuseStep 6418321 = 4813741) B4813741
theorem B5353363 : Blo 1250443 5353363 := bstep (se 1 (by rfl) ⟨4015022, by rfl⟩ : syracuseStep 5353363 = 8030045) B8030045
theorem B24055703 : Blo 1250443 24055703 := bstep (se 1 (by rfl) ⟨18041777, by rfl⟩ : syracuseStep 24055703 = 36083555) B36083555
theorem B2674633 : Blo 1250443 2674633 := bstep (se 2 (by rfl) ⟨1002987, by rfl⟩ : syracuseStep 2674633 = 2005975) B2005975
theorem B1781767 : Blo 1250443 1781767 := bstep (se 1 (by rfl) ⟨1336325, by rfl⟩ : syracuseStep 1781767 = 2672651) B2672651
theorem B4280363 : Blo 1250443 4280363 := bstep (se 1 (by rfl) ⟨3210272, by rfl⟩ : syracuseStep 4280363 = 6420545) B6420545
theorem B2814011 : Blo 1250443 2814011 := bstep (se 1 (by rfl) ⟨2110508, by rfl⟩ : syracuseStep 2814011 = 4221017) B4221017
theorem B3166361 : Blo 1250443 3166361 := bstep (se 2 (by rfl) ⟨1187385, by rfl⟩ : syracuseStep 3166361 = 2374771) B2374771
theorem B6009005 : Blo 1250443 6009005 := bstep (se 3 (by rfl) ⟨1126688, by rfl⟩ : syracuseStep 6009005 = 2253377) B2253377
theorem B27046061 : Blo 1250443 27046061 := bstep (se 3 (by rfl) ⟨5071136, by rfl⟩ : syracuseStep 27046061 = 10142273) B10142273
theorem B2814137 : Blo 1250443 2814137 := bstep (se 2 (by rfl) ⟨1055301, by rfl⟩ : syracuseStep 2814137 = 2110603) B2110603
theorem B4223177 : Blo 1250443 4223177 := bstep (se 2 (by rfl) ⟨1583691, by rfl⟩ : syracuseStep 4223177 = 3167383) B3167383
theorem B3805483 : Blo 1250443 3805483 := bstep (se 1 (by rfl) ⟨2854112, by rfl⟩ : syracuseStep 3805483 = 5708225) B5708225
theorem B3166523 : Blo 1250443 3166523 := bstep (se 1 (by rfl) ⟨2374892, by rfl⟩ : syracuseStep 3166523 = 4749785) B4749785
theorem B9507131 : Blo 1250443 9507131 := bstep (se 1 (by rfl) ⟨7130348, by rfl⟩ : syracuseStep 9507131 = 14260697) B14260697
theorem B1503631 : Blo 1250443 1503631 := bstep (se 1 (by rfl) ⟨1127723, by rfl⟩ : syracuseStep 1503631 = 2255447) B2255447
theorem B8556947 : Blo 1250443 8556947 := bstep (se 1 (by rfl) ⟨6417710, by rfl⟩ : syracuseStep 8556947 = 12835421) B12835421
theorem B6762899 : Blo 1250443 6762899 := bstep (se 1 (by rfl) ⟨5072174, by rfl⟩ : syracuseStep 6762899 = 10144349) B10144349
theorem B6336953 : Blo 1250443 6336953 := bstep (se 2 (by rfl) ⟨2376357, by rfl⟩ : syracuseStep 6336953 = 4752715) B4752715
theorem B7614929 : Blo 1250443 7614929 := bstep (se 2 (by rfl) ⟨2855598, by rfl⟩ : syracuseStep 7614929 = 5711197) B5711197
theorem B1782263 : Blo 1250443 1782263 := bstep (se 1 (by rfl) ⟨1336697, by rfl⟩ : syracuseStep 1782263 = 2673395) B2673395
theorem B1503751 : Blo 1250443 1503751 := bstep (se 1 (by rfl) ⟨1127813, by rfl⟩ : syracuseStep 1503751 = 2255627) B2255627
theorem B4280843 : Blo 1250443 4280843 := bstep (se 1 (by rfl) ⟨3210632, by rfl⟩ : syracuseStep 4280843 = 6421265) B6421265
theorem B2814479 : Blo 1250443 2814479 := bstep (se 1 (by rfl) ⟨2110859, by rfl⟩ : syracuseStep 2814479 = 4221719) B4221719
theorem B3166735 : Blo 1250443 3166735 := bstep (se 1 (by rfl) ⟨2375051, by rfl⟩ : syracuseStep 3166735 = 4750103) B4750103
theorem B7131671 : Blo 1250443 7131671 := bstep (se 1 (by rfl) ⟨5348753, by rfl⟩ : syracuseStep 7131671 = 10697507) B10697507
theorem B2814497 : Blo 1250443 2814497 := bstep (se 2 (by rfl) ⟨1055436, by rfl⟩ : syracuseStep 2814497 = 2110873) B2110873
theorem B1692217 : Blo 1250443 1692217 := bstep (se 2 (by rfl) ⟨634581, by rfl⟩ : syracuseStep 1692217 = 1269163) B1269163
theorem B4280951 : Blo 1250443 4280951 := bstep (se 1 (by rfl) ⟨3210713, by rfl⟩ : syracuseStep 4280951 = 6421427) B6421427
theorem B1806967 : Blo 1250443 1806967 := bstep (se 1 (by rfl) ⟨1355225, by rfl⟩ : syracuseStep 1806967 = 2710451) B2710451
theorem B6861485 : Blo 1250443 6861485 := bstep (se 3 (by rfl) ⟨1286528, by rfl⟩ : syracuseStep 6861485 = 2573057) B2573057
theorem B3167009 : Blo 1250443 3167009 := bstep (se 2 (by rfl) ⟨1187628, by rfl⟩ : syracuseStep 3167009 = 2375257) B2375257
theorem B5346107 : Blo 1250443 5346107 := bstep (se 1 (by rfl) ⟨4009580, by rfl⟩ : syracuseStep 5346107 = 8019161) B8019161
theorem B2814839 : Blo 1250443 2814839 := bstep (se 1 (by rfl) ⟨2111129, by rfl⟩ : syracuseStep 2814839 = 4222259) B4222259
theorem B4223879 : Blo 1250443 4223879 := bstep (se 1 (by rfl) ⟨3167909, by rfl⟩ : syracuseStep 4223879 = 6335819) B6335819
theorem B1504135 : Blo 1250443 1504135 := bstep (se 1 (by rfl) ⟨1128101, by rfl⟩ : syracuseStep 1504135 = 2256203) B2256203
theorem B1446799 : Blo 1250443 1446799 := bstep (se 1 (by rfl) ⟨1085099, by rfl⟩ : syracuseStep 1446799 = 2170199) B2170199
theorem B5706763 : Blo 1250443 5706763 := bstep (se 1 (by rfl) ⟨4280072, by rfl⟩ : syracuseStep 5706763 = 8560145) B8560145
theorem B7132171 : Blo 1250443 7132171 := bstep (se 1 (by rfl) ⟨5349128, by rfl⟩ : syracuseStep 7132171 = 10698257) B10698257
theorem B2815019 : Blo 1250443 2815019 := bstep (se 1 (by rfl) ⟨2111264, by rfl⟩ : syracuseStep 2815019 = 4222529) B4222529
theorem B2110583 : Blo 1250443 2110583 := bstep (se 1 (by rfl) ⟨1582937, by rfl⟩ : syracuseStep 2110583 = 3165875) B3165875
theorem B1250447 : Blo 1250443 1250447 := bstep (se 1 (by rfl) ⟨937835, by rfl⟩ : syracuseStep 1250447 = 1875671) B1875671
theorem B1250491 : Blo 1250443 1250491 := bstep (se 1 (by rfl) ⟨937868, by rfl⟩ : syracuseStep 1250491 = 1875737) B1875737
theorem B4224257 : Blo 1250443 4224257 := bstep (se 2 (by rfl) ⟨1584096, by rfl⟩ : syracuseStep 4224257 = 3168193) B3168193
theorem B1250567 : Blo 1250443 1250567 := bstep (se 1 (by rfl) ⟨937925, by rfl⟩ : syracuseStep 1250567 = 1875851) B1875851
theorem B1250575 : Blo 1250443 1250575 := bstep (se 1 (by rfl) ⟨937931, by rfl⟩ : syracuseStep 1250575 = 1875863) B1875863
theorem B1250619 : Blo 1250443 1250619 := bstep (se 1 (by rfl) ⟨937964, by rfl⟩ : syracuseStep 1250619 = 1875929) B1875929
theorem B2004283 : Blo 1250443 2004283 := bstep (se 1 (by rfl) ⟨1503212, by rfl⟩ : syracuseStep 2004283 = 3006425) B3006425
theorem B1250695 : Blo 1250443 1250695 := bstep (se 1 (by rfl) ⟨938021, by rfl⟩ : syracuseStep 1250695 = 1876043) B1876043
theorem B1250703 : Blo 1250443 1250703 := bstep (se 1 (by rfl) ⟨938027, by rfl⟩ : syracuseStep 1250703 = 1876055) B1876055
theorem B2815379 : Blo 1250443 2815379 := bstep (se 1 (by rfl) ⟨2111534, by rfl⟩ : syracuseStep 2815379 = 4223069) B4223069
theorem B1783225 : Blo 1250443 1783225 := bstep (se 2 (by rfl) ⟨668709, by rfl⟩ : syracuseStep 1783225 = 1337419) B1337419
theorem B1250747 : Blo 1250443 1250747 := bstep (se 1 (by rfl) ⟨938060, by rfl⟩ : syracuseStep 1250747 = 1876121) B1876121
theorem B2815433 : Blo 1250443 2815433 := bstep (se 2 (by rfl) ⟨1055787, by rfl⟩ : syracuseStep 2815433 = 2111575) B2111575
theorem B1250823 : Blo 1250443 1250823 := bstep (se 1 (by rfl) ⟨938117, by rfl⟩ : syracuseStep 1250823 = 1876235) B1876235
theorem B1250831 : Blo 1250443 1250831 := bstep (se 1 (by rfl) ⟨938123, by rfl⟩ : syracuseStep 1250831 = 1876247) B1876247
theorem B5076523 : Blo 1250443 5076523 := bstep (se 1 (by rfl) ⟨3807392, by rfl⟩ : syracuseStep 5076523 = 7614785) B7614785
theorem B1250875 : Blo 1250443 1250875 := bstep (se 1 (by rfl) ⟨938156, by rfl⟩ : syracuseStep 1250875 = 1876313) B1876313
theorem B2111035 : Blo 1250443 2111035 := bstep (se 1 (by rfl) ⟨1583276, by rfl⟩ : syracuseStep 2111035 = 3166553) B3166553
theorem B1250951 : Blo 1250443 1250951 := bstep (se 1 (by rfl) ⟨938213, by rfl⟩ : syracuseStep 1250951 = 1876427) B1876427
theorem B1250959 : Blo 1250443 1250959 := bstep (se 1 (by rfl) ⟨938219, by rfl⟩ : syracuseStep 1250959 = 1876439) B1876439
theorem B1251003 : Blo 1250443 1251003 := bstep (se 1 (by rfl) ⟨938252, by rfl⟩ : syracuseStep 1251003 = 1876505) B1876505
theorem B2111177 : Blo 1250443 2111177 := bstep (se 2 (by rfl) ⟨791691, by rfl⟩ : syracuseStep 2111177 = 1583383) B1583383
theorem B6338249 : Blo 1250443 6338249 := bstep (se 2 (by rfl) ⟨2376843, by rfl⟩ : syracuseStep 6338249 = 4753687) B4753687
theorem B1251079 : Blo 1250443 1251079 := bstep (se 1 (by rfl) ⟨938309, by rfl⟩ : syracuseStep 1251079 = 1876619) B1876619
theorem B3168011 : Blo 1250443 3168011 := bstep (se 1 (by rfl) ⟨2376008, by rfl⟩ : syracuseStep 3168011 = 4752017) B4752017
theorem B1251087 : Blo 1250443 1251087 := bstep (se 1 (by rfl) ⟨938315, by rfl⟩ : syracuseStep 1251087 = 1876631) B1876631
theorem B1251131 : Blo 1250443 1251131 := bstep (se 1 (by rfl) ⟨938348, by rfl⟩ : syracuseStep 1251131 = 1876697) B1876697
theorem B1251207 : Blo 1250443 1251207 := bstep (se 1 (by rfl) ⟨938405, by rfl⟩ : syracuseStep 1251207 = 1876811) B1876811
theorem B1251215 : Blo 1250443 1251215 := bstep (se 1 (by rfl) ⟨938411, by rfl⟩ : syracuseStep 1251215 = 1876823) B1876823
theorem B7124881 : Blo 1250443 7124881 := bstep (se 2 (by rfl) ⟨2671830, by rfl⟩ : syracuseStep 7124881 = 5343661) B5343661
theorem B11417507 : Blo 1250443 11417507 := bstep (se 1 (by rfl) ⟨8563130, by rfl⟩ : syracuseStep 11417507 = 17126261) B17126261
theorem B1251259 : Blo 1250443 1251259 := bstep (se 1 (by rfl) ⟨938444, by rfl⟩ : syracuseStep 1251259 = 1876889) B1876889
theorem B1406983 : Blo 1250443 1406983 := bstep (se 1 (by rfl) ⟨1055237, by rfl⟩ : syracuseStep 1406983 = 2110475) B2110475
theorem B1251335 : Blo 1250443 1251335 := bstep (se 1 (by rfl) ⟨938501, by rfl⟩ : syracuseStep 1251335 = 1877003) B1877003
theorem B1251343 : Blo 1250443 1251343 := bstep (se 1 (by rfl) ⟨938507, by rfl⟩ : syracuseStep 1251343 = 1877015) B1877015
theorem B24049709 : Blo 1250443 24049709 := bstep (se 3 (by rfl) ⟨4509320, by rfl⟩ : syracuseStep 24049709 = 9018641) B9018641
theorem B4225067 : Blo 1250443 4225067 := bstep (se 1 (by rfl) ⟨3168800, by rfl⟩ : syracuseStep 4225067 = 6337601) B6337601
theorem B1251387 : Blo 1250443 1251387 := bstep (se 1 (by rfl) ⟨938540, by rfl⟩ : syracuseStep 1251387 = 1877081) B1877081
theorem B1251463 : Blo 1250443 1251463 := bstep (se 1 (by rfl) ⟨938597, by rfl⟩ : syracuseStep 1251463 = 1877195) B1877195
theorem B2816135 : Blo 1250443 2816135 := bstep (se 1 (by rfl) ⟨2112101, by rfl⟩ : syracuseStep 2816135 = 4224203) B4224203
theorem B1251471 : Blo 1250443 1251471 := bstep (se 1 (by rfl) ⟨938603, by rfl⟩ : syracuseStep 1251471 = 1877207) B1877207
theorem B1407163 : Blo 1250443 1407163 := bstep (se 1 (by rfl) ⟨1055372, by rfl⟩ : syracuseStep 1407163 = 2110745) B2110745
theorem B1251515 : Blo 1250443 1251515 := bstep (se 1 (by rfl) ⟨938636, by rfl⟩ : syracuseStep 1251515 = 1877273) B1877273
theorem B6764801 : Blo 1250443 6764801 := bstep (se 2 (by rfl) ⟨2536800, by rfl⟩ : syracuseStep 6764801 = 5073601) B5073601
theorem B1251591 : Blo 1250443 1251591 := bstep (se 1 (by rfl) ⟨938693, by rfl⟩ : syracuseStep 1251591 = 1877387) B1877387
theorem B1251599 : Blo 1250443 1251599 := bstep (se 1 (by rfl) ⟨938699, by rfl⟩ : syracuseStep 1251599 = 1877399) B1877399
theorem B16038161 : Blo 1250443 16038161 := bstep (se 2 (by rfl) ⟨6014310, by rfl⟩ : syracuseStep 16038161 = 12028621) B12028621
theorem B1251643 : Blo 1250443 1251643 := bstep (se 1 (by rfl) ⟨938732, by rfl⟩ : syracuseStep 1251643 = 1877465) B1877465
theorem B2816315 : Blo 1250443 2816315 := bstep (se 1 (by rfl) ⟨2112236, by rfl⟩ : syracuseStep 2816315 = 4224473) B4224473
theorem B2111879 : Blo 1250443 2111879 := bstep (se 1 (by rfl) ⟨1583909, by rfl⟩ : syracuseStep 2111879 = 3167819) B3167819
theorem B1251719 : Blo 1250443 1251719 := bstep (se 1 (by rfl) ⟨938789, by rfl⟩ : syracuseStep 1251719 = 1877579) B1877579
theorem B1251727 : Blo 1250443 1251727 := bstep (se 1 (by rfl) ⟨938795, by rfl⟩ : syracuseStep 1251727 = 1877591) B1877591
theorem B3168659 : Blo 1250443 3168659 := bstep (se 1 (by rfl) ⟨2376494, by rfl⟩ : syracuseStep 3168659 = 4752989) B4752989
theorem B2816441 : Blo 1250443 2816441 := bstep (se 2 (by rfl) ⟨1056165, by rfl⟩ : syracuseStep 2816441 = 2112331) B2112331
theorem B1251771 : Blo 1250443 1251771 := bstep (se 1 (by rfl) ⟨938828, by rfl⟩ : syracuseStep 1251771 = 1877657) B1877657
theorem B3561985 : Blo 1250443 3561985 := bstep (se 2 (by rfl) ⟨1335744, by rfl⟩ : syracuseStep 3561985 = 2671489) B2671489
theorem B1251847 : Blo 1250443 1251847 := bstep (se 1 (by rfl) ⟨938885, by rfl⟩ : syracuseStep 1251847 = 1877771) B1877771
theorem B1251855 : Blo 1250443 1251855 := bstep (se 1 (by rfl) ⟨938891, by rfl⟩ : syracuseStep 1251855 = 1877783) B1877783
theorem B5347883 : Blo 1250443 5347883 := bstep (se 1 (by rfl) ⟨4010912, by rfl⟩ : syracuseStep 5347883 = 8021825) B8021825
theorem B1251899 : Blo 1250443 1251899 := bstep (se 1 (by rfl) ⟨938924, by rfl⟩ : syracuseStep 1251899 = 1877849) B1877849
theorem B1251975 : Blo 1250443 1251975 := bstep (se 1 (by rfl) ⟨938981, by rfl⟩ : syracuseStep 1251975 = 1877963) B1877963
theorem B1407631 : Blo 1250443 1407631 := bstep (se 1 (by rfl) ⟨1055723, by rfl⟩ : syracuseStep 1407631 = 2111447) B2111447
theorem B1251983 : Blo 1250443 1251983 := bstep (se 1 (by rfl) ⟨938987, by rfl⟩ : syracuseStep 1251983 = 1877975) B1877975
theorem B3168953 : Blo 1250443 3168953 := bstep (se 2 (by rfl) ⟨1188357, by rfl⟩ : syracuseStep 3168953 = 2376715) B2376715
theorem B1252027 : Blo 1250443 1252027 := bstep (se 1 (by rfl) ⟨939020, by rfl⟩ : syracuseStep 1252027 = 1878041) B1878041
theorem B1252103 : Blo 1250443 1252103 := bstep (se 1 (by rfl) ⟨939077, by rfl⟩ : syracuseStep 1252103 = 1878155) B1878155
theorem B2816783 : Blo 1250443 2816783 := bstep (se 1 (by rfl) ⟨2112587, by rfl⟩ : syracuseStep 2816783 = 4225175) B4225175
theorem B1252111 : Blo 1250443 1252111 := bstep (se 1 (by rfl) ⟨939083, by rfl⟩ : syracuseStep 1252111 = 1878167) B1878167
theorem B2816801 : Blo 1250443 2816801 := bstep (se 2 (by rfl) ⟨1056300, by rfl⟩ : syracuseStep 2816801 = 2112601) B2112601
theorem B14244659 : Blo 1250443 14244659 := bstep (se 1 (by rfl) ⟨10683494, by rfl⟩ : syracuseStep 14244659 = 21366989) B21366989
theorem B2710331 : Blo 1250443 2710331 := bstep (se 1 (by rfl) ⟨2032748, by rfl⟩ : syracuseStep 2710331 = 4065497) B4065497
theorem B1252155 : Blo 1250443 1252155 := bstep (se 1 (by rfl) ⟨939116, by rfl⟩ : syracuseStep 1252155 = 1878233) B1878233
theorem B2374535 : Blo 1250443 2374535 := bstep (se 1 (by rfl) ⟨1780901, by rfl⟩ : syracuseStep 2374535 = 3561803) B3561803
theorem B1252231 : Blo 1250443 1252231 := bstep (se 1 (by rfl) ⟨939173, by rfl⟩ : syracuseStep 1252231 = 1878347) B1878347
theorem B1252239 : Blo 1250443 1252239 := bstep (se 1 (by rfl) ⟨939179, by rfl⟩ : syracuseStep 1252239 = 1878359) B1878359
theorem B6331283 : Blo 1250443 6331283 := bstep (se 1 (by rfl) ⟨4748462, by rfl⟩ : syracuseStep 6331283 = 9496925) B9496925
theorem B3431315 : Blo 1250443 3431315 := bstep (se 1 (by rfl) ⟨2573486, by rfl⟩ : syracuseStep 3431315 = 5146973) B5146973
theorem B77118371 : Blo 1250443 77118371 := bstep (se 1 (by rfl) ⟨57838778, by rfl⟩ : syracuseStep 77118371 = 115677557) B115677557
theorem B1252283 : Blo 1250443 1252283 := bstep (se 1 (by rfl) ⟨939212, by rfl⟩ : syracuseStep 1252283 = 1878425) B1878425
theorem B1252359 : Blo 1250443 1252359 := bstep (se 1 (by rfl) ⟨939269, by rfl⟩ : syracuseStep 1252359 = 1878539) B1878539
theorem B2112527 : Blo 1250443 2112527 := bstep (se 1 (by rfl) ⟨1584395, by rfl⟩ : syracuseStep 2112527 = 3168791) B3168791
theorem B1252367 : Blo 1250443 1252367 := bstep (se 1 (by rfl) ⟨939275, by rfl⟩ : syracuseStep 1252367 = 1878551) B1878551
theorem B3562555 : Blo 1250443 3562555 := bstep (se 1 (by rfl) ⟨2671916, by rfl⟩ : syracuseStep 3562555 = 5343833) B5343833
theorem B1252411 : Blo 1250443 1252411 := bstep (se 1 (by rfl) ⟨939308, by rfl⟩ : syracuseStep 1252411 = 1878617) B1878617
theorem B4283479 : Blo 1250443 4283479 := bstep (se 1 (by rfl) ⟨3212609, by rfl⟩ : syracuseStep 4283479 = 6425219) B6425219
theorem B2817143 : Blo 1250443 2817143 := bstep (se 1 (by rfl) ⟨2112857, by rfl⟩ : syracuseStep 2817143 = 4225715) B4225715
theorem B1408135 : Blo 1250443 1408135 := bstep (se 1 (by rfl) ⟨1056101, by rfl⟩ : syracuseStep 1408135 = 2112203) B2112203
theorem B3808403 : Blo 1250443 3808403 := bstep (se 1 (by rfl) ⟨2856302, by rfl⟩ : syracuseStep 3808403 = 5712605) B5712605
theorem B2817323 : Blo 1250443 2817323 := bstep (se 1 (by rfl) ⟨2112992, by rfl⟩ : syracuseStep 2817323 = 4225985) B4225985
theorem B1408315 : Blo 1250443 1408315 := bstep (se 1 (by rfl) ⟨1056236, by rfl⟩ : syracuseStep 1408315 = 2112473) B2112473
theorem B4226363 : Blo 1250443 4226363 := bstep (se 1 (by rfl) ⟨3169772, by rfl⟩ : syracuseStep 4226363 = 6339545) B6339545
theorem B3169651 : Blo 1250443 3169651 := bstep (se 1 (by rfl) ⟨2377238, by rfl⟩ : syracuseStep 3169651 = 4754477) B4754477
theorem B3005849 : Blo 1250443 3005849 := bstep (se 2 (by rfl) ⟨1127193, by rfl⟩ : syracuseStep 3005849 = 2254387) B2254387
theorem B3169793 : Blo 1250443 3169793 := bstep (se 2 (by rfl) ⟨1188672, by rfl⟩ : syracuseStep 3169793 = 2377345) B2377345
theorem B6946307 : Blo 1250443 6946307 := bstep (se 1 (by rfl) ⟨5209730, by rfl⟩ : syracuseStep 6946307 = 10419461) B10419461
theorem B2113067 : Blo 1250443 2113067 := bstep (se 1 (by rfl) ⟨1584800, by rfl⟩ : syracuseStep 2113067 = 3169601) B3169601
theorem B2817683 : Blo 1250443 2817683 := bstep (se 1 (by rfl) ⟨2113262, by rfl⟩ : syracuseStep 2817683 = 4226525) B4226525
theorem B2817737 : Blo 1250443 2817737 := bstep (se 2 (by rfl) ⟨1056651, by rfl⟩ : syracuseStep 2817737 = 2113303) B2113303
theorem B1875719 : Blo 1250443 1875719 := bstep (se 1 (by rfl) ⟨1406789, by rfl⟩ : syracuseStep 1875719 = 2813579) B2813579
theorem B1408783 : Blo 1250443 1408783 := bstep (se 1 (by rfl) ⟨1056587, by rfl⟩ : syracuseStep 1408783 = 2113175) B2113175
theorem B4226849 : Blo 1250443 4226849 := bstep (se 2 (by rfl) ⟨1585068, by rfl⟩ : syracuseStep 4226849 = 3170137) B3170137
theorem B1875755 : Blo 1250443 1875755 := bstep (se 1 (by rfl) ⟨1406816, by rfl⟩ : syracuseStep 1875755 = 2813633) B2813633
theorem B1875785 : Blo 1250443 1875785 := bstep (se 2 (by rfl) ⟨703419, by rfl⟩ : syracuseStep 1875785 = 1406839) B1406839
theorem B4751257 : Blo 1250443 4751257 := bstep (se 2 (by rfl) ⟨1781721, by rfl⟩ : syracuseStep 4751257 = 3563443) B3563443
theorem B2113465 : Blo 1250443 2113465 := bstep (se 2 (by rfl) ⟨792549, by rfl⟩ : syracuseStep 2113465 = 1585099) B1585099
theorem B1875899 : Blo 1250443 1875899 := bstep (se 1 (by rfl) ⟨1406924, by rfl⟩ : syracuseStep 1875899 = 2813849) B2813849
theorem B3170249 : Blo 1250443 3170249 := bstep (se 2 (by rfl) ⟨1188843, by rfl⟩ : syracuseStep 3170249 = 2377687) B2377687
theorem B1875959 : Blo 1250443 1875959 := bstep (se 1 (by rfl) ⟨1406969, by rfl⟩ : syracuseStep 1875959 = 2813939) B2813939
theorem B1875977 : Blo 1250443 1875977 := bstep (se 2 (by rfl) ⟨703491, by rfl⟩ : syracuseStep 1875977 = 1406983) B1406983
theorem B9502757 : Blo 1250443 9502757 := bstep (se 4 (by rfl) ⟨890883, by rfl⟩ : syracuseStep 9502757 = 1781767) B1781767
theorem B1876007 : Blo 1250443 1876007 := bstep (se 1 (by rfl) ⟨1407005, by rfl⟩ : syracuseStep 1876007 = 2814011) B2814011
theorem B18030707 : Blo 1250443 18030707 := bstep (se 1 (by rfl) ⟨13523030, by rfl⟩ : syracuseStep 18030707 = 27046061) B27046061
theorem B1876091 : Blo 1250443 1876091 := bstep (se 1 (by rfl) ⟨1407068, by rfl⟩ : syracuseStep 1876091 = 2814137) B2814137
theorem B4751531 : Blo 1250443 4751531 := bstep (se 1 (by rfl) ⟨3563648, by rfl⟩ : syracuseStep 4751531 = 7127297) B7127297
theorem B14246117 : Blo 1250443 14246117 := bstep (se 4 (by rfl) ⟨1335573, by rfl⟩ : syracuseStep 14246117 = 2671147) B2671147
theorem B1876217 : Blo 1250443 1876217 := bstep (se 2 (by rfl) ⟨703581, by rfl⟩ : syracuseStep 1876217 = 1407163) B1407163
theorem B1876319 : Blo 1250443 1876319 := bstep (se 1 (by rfl) ⟨1407239, by rfl⟩ : syracuseStep 1876319 = 2814479) B2814479
theorem B1876331 : Blo 1250443 1876331 := bstep (se 1 (by rfl) ⟨1407248, by rfl⟩ : syracuseStep 1876331 = 2814497) B2814497
theorem B16024013 : Blo 1250443 16024013 := bstep (se 3 (by rfl) ⟨3004502, by rfl⟩ : syracuseStep 16024013 = 6009005) B6009005
theorem B3564071 : Blo 1250443 3564071 := bstep (se 1 (by rfl) ⟨2673053, by rfl⟩ : syracuseStep 3564071 = 5346107) B5346107
theorem B1876559 : Blo 1250443 1876559 := bstep (se 1 (by rfl) ⟨1407419, by rfl⟩ : syracuseStep 1876559 = 2814839) B2814839
theorem B1876679 : Blo 1250443 1876679 := bstep (se 1 (by rfl) ⟨1407509, by rfl⟩ : syracuseStep 1876679 = 2815019) B2815019
theorem B14254865 : Blo 1250443 14254865 := bstep (se 2 (by rfl) ⟨5345574, by rfl⟩ : syracuseStep 14254865 = 10691149) B10691149
theorem B1876841 : Blo 1250443 1876841 := bstep (se 2 (by rfl) ⟨703815, by rfl⟩ : syracuseStep 1876841 = 1407631) B1407631
theorem B1876919 : Blo 1250443 1876919 := bstep (se 1 (by rfl) ⟨1407689, by rfl⟩ : syracuseStep 1876919 = 2815379) B2815379
theorem B2376631 : Blo 1250443 2376631 := bstep (se 1 (by rfl) ⟨1782473, by rfl⟩ : syracuseStep 2376631 = 3564947) B3564947
theorem B1876955 : Blo 1250443 1876955 := bstep (se 1 (by rfl) ⟨1407716, by rfl⟩ : syracuseStep 1876955 = 2815433) B2815433
theorem B19268761 : Blo 1250443 19268761 := bstep (se 2 (by rfl) ⟨7225785, by rfl⟩ : syracuseStep 19268761 = 14451571) B14451571
theorem B7611671 : Blo 1250443 7611671 := bstep (se 1 (by rfl) ⟨5708753, by rfl⟩ : syracuseStep 7611671 = 11417507) B11417507
theorem B4752701 : Blo 1250443 4752701 := bstep (se 3 (by rfl) ⟨891131, by rfl⟩ : syracuseStep 4752701 = 1782263) B1782263
theorem B16033139 : Blo 1250443 16033139 := bstep (se 1 (by rfl) ⟨12024854, by rfl⟩ : syracuseStep 16033139 = 24049709) B24049709
theorem B1877423 : Blo 1250443 1877423 := bstep (se 1 (by rfl) ⟨1408067, by rfl⟩ : syracuseStep 1877423 = 2816135) B2816135
theorem B5711305 : Blo 1250443 5711305 := bstep (se 2 (by rfl) ⟨2141739, by rfl⟩ : syracuseStep 5711305 = 4283479) B4283479
theorem B12019205 : Blo 1250443 12019205 := bstep (se 4 (by rfl) ⟨1126800, by rfl⟩ : syracuseStep 12019205 = 2253601) B2253601
theorem B1877513 : Blo 1250443 1877513 := bstep (se 2 (by rfl) ⟨704067, by rfl⟩ : syracuseStep 1877513 = 1408135) B1408135
theorem B10692107 : Blo 1250443 10692107 := bstep (se 1 (by rfl) ⟨8019080, by rfl⟩ : syracuseStep 10692107 = 16038161) B16038161
theorem B1877543 : Blo 1250443 1877543 := bstep (se 1 (by rfl) ⟨1408157, by rfl⟩ : syracuseStep 1877543 = 2816315) B2816315
theorem B1877627 : Blo 1250443 1877627 := bstep (se 1 (by rfl) ⟨1408220, by rfl⟩ : syracuseStep 1877627 = 2816441) B2816441
theorem B4753019 : Blo 1250443 4753019 := bstep (se 1 (by rfl) ⟨3564764, by rfl⟩ : syracuseStep 4753019 = 7129529) B7129529
theorem B3212939 : Blo 1250443 3212939 := bstep (se 1 (by rfl) ⟨2409704, by rfl⟩ : syracuseStep 3212939 = 4819409) B4819409
theorem B2672327 : Blo 1250443 2672327 := bstep (se 1 (by rfl) ⟨2004245, by rfl⟩ : syracuseStep 2672327 = 4008491) B4008491
theorem B1427143 : Blo 1250443 1427143 := bstep (se 1 (by rfl) ⟨1070357, by rfl⟩ : syracuseStep 1427143 = 2140715) B2140715
theorem B3565255 : Blo 1250443 3565255 := bstep (se 1 (by rfl) ⟨2673941, by rfl⟩ : syracuseStep 3565255 = 5347883) B5347883
theorem B1877753 : Blo 1250443 1877753 := bstep (se 2 (by rfl) ⟨704157, by rfl⟩ : syracuseStep 1877753 = 1408315) B1408315
theorem B8800067 : Blo 1250443 8800067 := bstep (se 1 (by rfl) ⟨6600050, by rfl⟩ : syracuseStep 8800067 = 13200101) B13200101
theorem B1877855 : Blo 1250443 1877855 := bstep (se 1 (by rfl) ⟨1408391, by rfl⟩ : syracuseStep 1877855 = 2816783) B2816783
theorem B1877867 : Blo 1250443 1877867 := bstep (se 1 (by rfl) ⟨1408400, by rfl⟩ : syracuseStep 1877867 = 2816801) B2816801
theorem B9496439 : Blo 1250443 9496439 := bstep (se 1 (by rfl) ⟨7122329, by rfl⟩ : syracuseStep 9496439 = 14244659) B14244659
theorem B4220855 : Blo 1250443 4220855 := bstep (se 1 (by rfl) ⟨3165641, by rfl⟩ : syracuseStep 4220855 = 6331283) B6331283
theorem B2287543 : Blo 1250443 2287543 := bstep (se 1 (by rfl) ⟨1715657, by rfl⟩ : syracuseStep 2287543 = 3431315) B3431315
theorem B8022053 : Blo 1250443 8022053 := bstep (se 4 (by rfl) ⟨752067, by rfl⟩ : syracuseStep 8022053 = 1504135) B1504135
theorem B6768697 : Blo 1250443 6768697 := bstep (se 2 (by rfl) ⟨2538261, by rfl⟩ : syracuseStep 6768697 = 5076523) B5076523
theorem B1878095 : Blo 1250443 1878095 := bstep (se 1 (by rfl) ⟨1408571, by rfl⟩ : syracuseStep 1878095 = 2817143) B2817143
theorem B1878215 : Blo 1250443 1878215 := bstep (se 1 (by rfl) ⟨1408661, by rfl⟩ : syracuseStep 1878215 = 2817323) B2817323
theorem B4630871 : Blo 1250443 4630871 := bstep (se 1 (by rfl) ⟨3473153, by rfl⟩ : syracuseStep 4630871 = 6946307) B6946307
theorem B1902943 : Blo 1250443 1902943 := bstep (se 1 (by rfl) ⟨1427207, by rfl⟩ : syracuseStep 1902943 = 2854415) B2854415
theorem B1878377 : Blo 1250443 1878377 := bstep (se 2 (by rfl) ⟨704391, by rfl⟩ : syracuseStep 1878377 = 1408783) B1408783
theorem B1878455 : Blo 1250443 1878455 := bstep (se 1 (by rfl) ⟨1408841, by rfl⟩ : syracuseStep 1878455 = 2817683) B2817683
theorem B1878491 : Blo 1250443 1878491 := bstep (se 1 (by rfl) ⟨1408868, by rfl⟩ : syracuseStep 1878491 = 2817737) B2817737
theorem B4221449 : Blo 1250443 4221449 := bstep (se 2 (by rfl) ⟨1583043, by rfl⟩ : syracuseStep 4221449 = 3166087) B3166087
theorem B7137817 : Blo 1250443 7137817 := bstep (se 2 (by rfl) ⟨2676681, by rfl⟩ : syracuseStep 7137817 = 5353363) B5353363
theorem B6335009 : Blo 1250443 6335009 := bstep (se 2 (by rfl) ⟨2375628, by rfl⟩ : syracuseStep 6335009 = 4751257) B4751257
theorem B3566177 : Blo 1250443 3566177 := bstep (se 2 (by rfl) ⟨1337316, by rfl⟩ : syracuseStep 3566177 = 2674633) B2674633
theorem B72157877 : Blo 1250443 72157877 := bstep (se 5 (by rfl) ⟨3382400, by rfl⟩ : syracuseStep 72157877 = 6764801) B6764801
theorem B2853575 : Blo 1250443 2853575 := bstep (se 1 (by rfl) ⟨2140181, by rfl⟩ : syracuseStep 2853575 = 4280363) B4280363
theorem B30436069 : Blo 1250443 30436069 := bstep (se 4 (by rfl) ⟨2853381, by rfl⟩ : syracuseStep 30436069 = 5706763) B5706763
theorem B5704631 : Blo 1250443 5704631 := bstep (se 1 (by rfl) ⟨4278473, by rfl⟩ : syracuseStep 5704631 = 8556947) B8556947
theorem B2853895 : Blo 1250443 2853895 := bstep (se 1 (by rfl) ⟨2140421, by rfl⟩ : syracuseStep 2853895 = 4280843) B4280843
theorem B4754447 : Blo 1250443 4754447 := bstep (se 1 (by rfl) ⟨3565835, by rfl⟩ : syracuseStep 4754447 = 7131671) B7131671
theorem B5073977 : Blo 1250443 5073977 := bstep (se 2 (by rfl) ⟨1902741, by rfl⟩ : syracuseStep 5073977 = 3805483) B3805483
theorem B2853967 : Blo 1250443 2853967 := bstep (se 1 (by rfl) ⟨2140475, by rfl⟩ : syracuseStep 2853967 = 4280951) B4280951
theorem B4574323 : Blo 1250443 4574323 := bstep (se 1 (by rfl) ⟨3430742, by rfl⟩ : syracuseStep 4574323 = 6861485) B6861485
theorem B21384485 : Blo 1250443 21384485 := bstep (se 4 (by rfl) ⟨2004795, by rfl⟩ : syracuseStep 21384485 = 4009591) B4009591
theorem B9637157 : Blo 1250443 9637157 := bstep (se 4 (by rfl) ⟨903483, by rfl⟩ : syracuseStep 9637157 = 1806967) B1806967
theorem B4222313 : Blo 1250443 4222313 := bstep (se 2 (by rfl) ⟨1583367, by rfl⟩ : syracuseStep 4222313 = 3166735) B3166735
theorem B1584679 : Blo 1250443 1584679 := bstep (se 1 (by rfl) ⟨1188509, by rfl⟩ : syracuseStep 1584679 = 2377019) B2377019
theorem B2813651 : Blo 1250443 2813651 := bstep (se 1 (by rfl) ⟨2110238, by rfl⟩ : syracuseStep 2813651 = 4220477) B4220477
theorem B18034397 : Blo 1250443 18034397 := bstep (se 3 (by rfl) ⟨3381449, by rfl⟩ : syracuseStep 18034397 = 6762899) B6762899
theorem B9023197 : Blo 1250443 9023197 := bstep (se 3 (by rfl) ⟨1691849, by rfl⟩ : syracuseStep 9023197 = 3383699) B3383699
theorem B8015597 : Blo 1250443 8015597 := bstep (se 3 (by rfl) ⟨1502924, by rfl⟩ : syracuseStep 8015597 = 3005849) B3005849
theorem B1929065 : Blo 1250443 1929065 := bstep (se 2 (by rfl) ⟨723399, by rfl⟩ : syracuseStep 1929065 = 1446799) B1446799
theorem B1585003 : Blo 1250443 1585003 := bstep (se 1 (by rfl) ⟨1188752, by rfl⟩ : syracuseStep 1585003 = 2377505) B2377505
theorem B18050951 : Blo 1250443 18050951 := bstep (se 1 (by rfl) ⟨13538213, by rfl⟩ : syracuseStep 18050951 = 27076427) B27076427
theorem B4222907 : Blo 1250443 4222907 := bstep (se 1 (by rfl) ⟨3167180, by rfl⟩ : syracuseStep 4222907 = 6334361) B6334361
theorem B6009353 : Blo 1250443 6009353 := bstep (se 2 (by rfl) ⟨2253507, by rfl⟩ : syracuseStep 6009353 = 4507015) B4507015
theorem B1806887 : Blo 1250443 1806887 := bstep (se 1 (by rfl) ⟨1355165, by rfl⟩ : syracuseStep 1806887 = 2710331) B2710331
theorem B2814587 : Blo 1250443 2814587 := bstep (se 1 (by rfl) ⟨2110940, by rfl⟩ : syracuseStep 2814587 = 4221881) B4221881
theorem B2110151 : Blo 1250443 2110151 := bstep (se 1 (by rfl) ⟨1582613, by rfl⟩ : syracuseStep 2110151 = 3165227) B3165227
theorem B2814713 : Blo 1250443 2814713 := bstep (se 2 (by rfl) ⟨1055517, by rfl⟩ : syracuseStep 2814713 = 2111035) B2111035
theorem B34231045 : Blo 1250443 34231045 := bstep (se 4 (by rfl) ⟨3209160, by rfl⟩ : syracuseStep 34231045 = 6418321) B6418321
theorem B2110313 : Blo 1250443 2110313 := bstep (se 2 (by rfl) ⟨791367, by rfl⟩ : syracuseStep 2110313 = 1582735) B1582735
theorem B2814983 : Blo 1250443 2814983 := bstep (se 1 (by rfl) ⟨2111237, by rfl⟩ : syracuseStep 2814983 = 4222475) B4222475
theorem B18035779 : Blo 1250443 18035779 := bstep (se 1 (by rfl) ⟨13526834, by rfl⟩ : syracuseStep 18035779 = 27053669) B27053669
theorem B2815055 : Blo 1250443 2815055 := bstep (se 1 (by rfl) ⟨2111291, by rfl⟩ : syracuseStep 2815055 = 4222583) B4222583
theorem B1250479 : Blo 1250443 1250479 := bstep (se 1 (by rfl) ⟨937859, by rfl⟩ : syracuseStep 1250479 = 1875719) B1875719
theorem B9499841 : Blo 1250443 9499841 := bstep (se 2 (by rfl) ⟨3562440, by rfl⟩ : syracuseStep 9499841 = 7124881) B7124881
theorem B1250503 : Blo 1250443 1250503 := bstep (se 1 (by rfl) ⟨937877, by rfl⟩ : syracuseStep 1250503 = 1875755) B1875755
theorem B1250523 : Blo 1250443 1250523 := bstep (se 1 (by rfl) ⟨937892, by rfl⟩ : syracuseStep 1250523 = 1875785) B1875785
theorem B2110711 : Blo 1250443 2110711 := bstep (se 1 (by rfl) ⟨1583033, by rfl⟩ : syracuseStep 2110711 = 3166067) B3166067
theorem B16037135 : Blo 1250443 16037135 := bstep (se 1 (by rfl) ⟨12027851, by rfl⟩ : syracuseStep 16037135 = 24055703) B24055703
theorem B1250599 : Blo 1250443 1250599 := bstep (se 1 (by rfl) ⟨937949, by rfl⟩ : syracuseStep 1250599 = 1875899) B1875899
theorem B1250639 : Blo 1250443 1250639 := bstep (se 1 (by rfl) ⟨937979, by rfl⟩ : syracuseStep 1250639 = 1875959) B1875959
theorem B1250655 : Blo 1250443 1250655 := bstep (se 1 (by rfl) ⟨937991, by rfl⟩ : syracuseStep 1250655 = 1875983) B1875983
theorem B1250683 : Blo 1250443 1250683 := bstep (se 1 (by rfl) ⟨938012, by rfl⟩ : syracuseStep 1250683 = 1876025) B1876025
theorem B1250735 : Blo 1250443 1250735 := bstep (se 1 (by rfl) ⟨938051, by rfl⟩ : syracuseStep 1250735 = 1876103) B1876103
theorem B2110907 : Blo 1250443 2110907 := bstep (se 1 (by rfl) ⟨1583180, by rfl⟩ : syracuseStep 2110907 = 3166361) B3166361
theorem B1250759 : Blo 1250443 1250759 := bstep (se 1 (by rfl) ⟨938069, by rfl⟩ : syracuseStep 1250759 = 1876139) B1876139
theorem B1250779 : Blo 1250443 1250779 := bstep (se 1 (by rfl) ⟨938084, by rfl⟩ : syracuseStep 1250779 = 1876169) B1876169
theorem B2815451 : Blo 1250443 2815451 := bstep (se 1 (by rfl) ⟨2111588, by rfl⟩ : syracuseStep 2815451 = 4223177) B4223177
theorem B3167707 : Blo 1250443 3167707 := bstep (se 1 (by rfl) ⟨2375780, by rfl⟩ : syracuseStep 3167707 = 4751561) B4751561
theorem B1250855 : Blo 1250443 1250855 := bstep (se 1 (by rfl) ⟨938141, by rfl⟩ : syracuseStep 1250855 = 1876283) B1876283
theorem B2111015 : Blo 1250443 2111015 := bstep (se 1 (by rfl) ⟨1583261, by rfl⟩ : syracuseStep 2111015 = 3166523) B3166523
theorem B6338087 : Blo 1250443 6338087 := bstep (se 1 (by rfl) ⟨4753565, by rfl⟩ : syracuseStep 6338087 = 9507131) B9507131
theorem B1250895 : Blo 1250443 1250895 := bstep (se 1 (by rfl) ⟨938171, by rfl⟩ : syracuseStep 1250895 = 1876343) B1876343
theorem B1250911 : Blo 1250443 1250911 := bstep (se 1 (by rfl) ⟨938183, by rfl⟩ : syracuseStep 1250911 = 1876367) B1876367
theorem B1250939 : Blo 1250443 1250939 := bstep (se 1 (by rfl) ⟨938204, by rfl⟩ : syracuseStep 1250939 = 1876409) B1876409
theorem B4224635 : Blo 1250443 4224635 := bstep (se 1 (by rfl) ⟨3168476, by rfl⟩ : syracuseStep 4224635 = 6336953) B6336953
theorem B9025157 : Blo 1250443 9025157 := bstep (se 4 (by rfl) ⟨846108, by rfl⟩ : syracuseStep 9025157 = 1692217) B1692217
theorem B1250991 : Blo 1250443 1250991 := bstep (se 1 (by rfl) ⟨938243, by rfl⟩ : syracuseStep 1250991 = 1876487) B1876487
theorem B1251015 : Blo 1250443 1251015 := bstep (se 1 (by rfl) ⟨938261, by rfl⟩ : syracuseStep 1251015 = 1876523) B1876523
theorem B1251035 : Blo 1250443 1251035 := bstep (se 1 (by rfl) ⟨938276, by rfl⟩ : syracuseStep 1251035 = 1876553) B1876553
theorem B9508589 : Blo 1250443 9508589 := bstep (se 3 (by rfl) ⟨1782860, by rfl⟩ : syracuseStep 9508589 = 3565721) B3565721
theorem B4224797 : Blo 1250443 4224797 := bstep (se 3 (by rfl) ⟨792149, by rfl⟩ : syracuseStep 4224797 = 1584299) B1584299
theorem B1251111 : Blo 1250443 1251111 := bstep (se 1 (by rfl) ⟨938333, by rfl⟩ : syracuseStep 1251111 = 1876667) B1876667
theorem B2111305 : Blo 1250443 2111305 := bstep (se 2 (by rfl) ⟨791739, by rfl⟩ : syracuseStep 2111305 = 1583479) B1583479
theorem B1251151 : Blo 1250443 1251151 := bstep (se 1 (by rfl) ⟨938363, by rfl⟩ : syracuseStep 1251151 = 1876727) B1876727
theorem B1251167 : Blo 1250443 1251167 := bstep (se 1 (by rfl) ⟨938375, by rfl⟩ : syracuseStep 1251167 = 1876751) B1876751
theorem B2004841 : Blo 1250443 2004841 := bstep (se 2 (by rfl) ⟨751815, by rfl⟩ : syracuseStep 2004841 = 1503631) B1503631
theorem B2111339 : Blo 1250443 2111339 := bstep (se 1 (by rfl) ⟨1583504, by rfl⟩ : syracuseStep 2111339 = 3167009) B3167009
theorem B1251195 : Blo 1250443 1251195 := bstep (se 1 (by rfl) ⟨938396, by rfl⟩ : syracuseStep 1251195 = 1876793) B1876793
theorem B7223201 : Blo 1250443 7223201 := bstep (se 2 (by rfl) ⟨2708700, by rfl⟩ : syracuseStep 7223201 = 5417401) B5417401
theorem B1251247 : Blo 1250443 1251247 := bstep (se 1 (by rfl) ⟨938435, by rfl⟩ : syracuseStep 1251247 = 1876871) B1876871
theorem B2815919 : Blo 1250443 2815919 := bstep (se 1 (by rfl) ⟨2111939, by rfl⟩ : syracuseStep 2815919 = 4223879) B4223879
theorem B1251271 : Blo 1250443 1251271 := bstep (se 1 (by rfl) ⟨938453, by rfl⟩ : syracuseStep 1251271 = 1876907) B1876907
theorem B1251291 : Blo 1250443 1251291 := bstep (se 1 (by rfl) ⟨938468, by rfl⟩ : syracuseStep 1251291 = 1876937) B1876937
theorem B4749313 : Blo 1250443 4749313 := bstep (se 2 (by rfl) ⟨1780992, by rfl⟩ : syracuseStep 4749313 = 3561985) B3561985
theorem B3610631 : Blo 1250443 3610631 := bstep (se 1 (by rfl) ⟨2707973, by rfl⟩ : syracuseStep 3610631 = 5415947) B5415947
theorem B2005001 : Blo 1250443 2005001 := bstep (se 2 (by rfl) ⟨751875, by rfl⟩ : syracuseStep 2005001 = 1503751) B1503751
theorem B1251367 : Blo 1250443 1251367 := bstep (se 1 (by rfl) ⟨938525, by rfl⟩ : syracuseStep 1251367 = 1877051) B1877051
theorem B1407055 : Blo 1250443 1407055 := bstep (se 1 (by rfl) ⟨1055291, by rfl⟩ : syracuseStep 1407055 = 2110583) B2110583
theorem B1251407 : Blo 1250443 1251407 := bstep (se 1 (by rfl) ⟨938555, by rfl⟩ : syracuseStep 1251407 = 1877111) B1877111
theorem B3168335 : Blo 1250443 3168335 := bstep (se 1 (by rfl) ⟨2376251, by rfl⟩ : syracuseStep 3168335 = 4752503) B4752503
theorem B6764633 : Blo 1250443 6764633 := bstep (se 2 (by rfl) ⟨2536737, by rfl⟩ : syracuseStep 6764633 = 5073475) B5073475
theorem B1251423 : Blo 1250443 1251423 := bstep (se 1 (by rfl) ⟨938567, by rfl⟩ : syracuseStep 1251423 = 1877135) B1877135
theorem B1251451 : Blo 1250443 1251451 := bstep (se 1 (by rfl) ⟨938588, by rfl⟩ : syracuseStep 1251451 = 1877177) B1877177
theorem B2816171 : Blo 1250443 2816171 := bstep (se 1 (by rfl) ⟨2112128, by rfl⟩ : syracuseStep 2816171 = 4224257) B4224257
theorem B1251503 : Blo 1250443 1251503 := bstep (se 1 (by rfl) ⟨938627, by rfl⟩ : syracuseStep 1251503 = 1877255) B1877255
theorem B1251527 : Blo 1250443 1251527 := bstep (se 1 (by rfl) ⟨938645, by rfl⟩ : syracuseStep 1251527 = 1877291) B1877291
theorem B1251547 : Blo 1250443 1251547 := bstep (se 1 (by rfl) ⟨938660, by rfl⟩ : syracuseStep 1251547 = 1877321) B1877321
theorem B2111737 : Blo 1250443 2111737 := bstep (se 2 (by rfl) ⟨791901, by rfl⟩ : syracuseStep 2111737 = 1583803) B1583803
theorem B6330635 : Blo 1250443 6330635 := bstep (se 1 (by rfl) ⟨4747976, by rfl⟩ : syracuseStep 6330635 = 9495953) B9495953
theorem B1251623 : Blo 1250443 1251623 := bstep (se 1 (by rfl) ⟨938717, by rfl⟩ : syracuseStep 1251623 = 1877435) B1877435
theorem B1251663 : Blo 1250443 1251663 := bstep (se 1 (by rfl) ⟨938747, by rfl⟩ : syracuseStep 1251663 = 1877495) B1877495
theorem B1251679 : Blo 1250443 1251679 := bstep (se 1 (by rfl) ⟨938759, by rfl⟩ : syracuseStep 1251679 = 1877519) B1877519
theorem B1251707 : Blo 1250443 1251707 := bstep (se 1 (by rfl) ⟨938780, by rfl⟩ : syracuseStep 1251707 = 1877561) B1877561
theorem B2374049 : Blo 1250443 2374049 := bstep (se 2 (by rfl) ⟨890268, by rfl⟩ : syracuseStep 2374049 = 1780537) B1780537
theorem B1251759 : Blo 1250443 1251759 := bstep (se 1 (by rfl) ⟨938819, by rfl⟩ : syracuseStep 1251759 = 1877639) B1877639
theorem B1251783 : Blo 1250443 1251783 := bstep (se 1 (by rfl) ⟨938837, by rfl⟩ : syracuseStep 1251783 = 1877675) B1877675
theorem B1407451 : Blo 1250443 1407451 := bstep (se 1 (by rfl) ⟨1055588, by rfl⟩ : syracuseStep 1407451 = 2111177) B2111177
theorem B1251803 : Blo 1250443 1251803 := bstep (se 1 (by rfl) ⟨938852, by rfl⟩ : syracuseStep 1251803 = 1877705) B1877705
theorem B4225499 : Blo 1250443 4225499 := bstep (se 1 (by rfl) ⟨3169124, by rfl⟩ : syracuseStep 4225499 = 6338249) B6338249
theorem B2112007 : Blo 1250443 2112007 := bstep (se 1 (by rfl) ⟨1584005, by rfl⟩ : syracuseStep 2112007 = 3168011) B3168011
theorem B6765065 : Blo 1250443 6765065 := bstep (se 2 (by rfl) ⟨2536899, by rfl⟩ : syracuseStep 6765065 = 5073799) B5073799
theorem B1251879 : Blo 1250443 1251879 := bstep (se 1 (by rfl) ⟨938909, by rfl⟩ : syracuseStep 1251879 = 1877819) B1877819
theorem B20306477 : Blo 1250443 20306477 := bstep (se 3 (by rfl) ⟨3807464, by rfl⟩ : syracuseStep 20306477 = 7614929) B7614929
theorem B2374201 : Blo 1250443 2374201 := bstep (se 2 (by rfl) ⟨890325, by rfl⟩ : syracuseStep 2374201 = 1780651) B1780651
theorem B1251919 : Blo 1250443 1251919 := bstep (se 1 (by rfl) ⟨938939, by rfl⟩ : syracuseStep 1251919 = 1877879) B1877879
theorem B1251935 : Blo 1250443 1251935 := bstep (se 1 (by rfl) ⟨938951, by rfl⟩ : syracuseStep 1251935 = 1877903) B1877903
theorem B1251963 : Blo 1250443 1251963 := bstep (se 1 (by rfl) ⟨938972, by rfl⟩ : syracuseStep 1251963 = 1877945) B1877945
theorem B1252015 : Blo 1250443 1252015 := bstep (se 1 (by rfl) ⟨939011, by rfl⟩ : syracuseStep 1252015 = 1878023) B1878023
theorem B9509561 : Blo 1250443 9509561 := bstep (se 2 (by rfl) ⟨3566085, by rfl⟩ : syracuseStep 9509561 = 7132171) B7132171
theorem B2816711 : Blo 1250443 2816711 := bstep (se 1 (by rfl) ⟨2112533, by rfl⟩ : syracuseStep 2816711 = 4225067) B4225067
theorem B1252039 : Blo 1250443 1252039 := bstep (se 1 (by rfl) ⟨939029, by rfl⟩ : syracuseStep 1252039 = 1878059) B1878059
theorem B3168983 : Blo 1250443 3168983 := bstep (se 1 (by rfl) ⟨2376737, by rfl⟩ : syracuseStep 3168983 = 4753475) B4753475
theorem B1252059 : Blo 1250443 1252059 := bstep (se 1 (by rfl) ⟨939044, by rfl⟩ : syracuseStep 1252059 = 1878089) B1878089
theorem B4750073 : Blo 1250443 4750073 := bstep (se 2 (by rfl) ⟨1781277, by rfl⟩ : syracuseStep 4750073 = 3562555) B3562555
theorem B1252135 : Blo 1250443 1252135 := bstep (se 1 (by rfl) ⟨939101, by rfl⟩ : syracuseStep 1252135 = 1878203) B1878203
theorem B2407241 : Blo 1250443 2407241 := bstep (se 2 (by rfl) ⟨902715, by rfl⟩ : syracuseStep 2407241 = 1805431) B1805431
theorem B1252175 : Blo 1250443 1252175 := bstep (se 1 (by rfl) ⟨939131, by rfl⟩ : syracuseStep 1252175 = 1878263) B1878263
theorem B1252191 : Blo 1250443 1252191 := bstep (se 1 (by rfl) ⟨939143, by rfl⟩ : syracuseStep 1252191 = 1878287) B1878287
theorem B2374505 : Blo 1250443 2374505 := bstep (se 2 (by rfl) ⟨890439, by rfl⟩ : syracuseStep 2374505 = 1780879) B1780879
theorem B1252219 : Blo 1250443 1252219 := bstep (se 1 (by rfl) ⟨939164, by rfl⟩ : syracuseStep 1252219 = 1878329) B1878329
theorem B1407919 : Blo 1250443 1407919 := bstep (se 1 (by rfl) ⟨1055939, by rfl⟩ : syracuseStep 1407919 = 2111879) B2111879
theorem B1252271 : Blo 1250443 1252271 := bstep (se 1 (by rfl) ⟨939203, by rfl⟩ : syracuseStep 1252271 = 1878407) B1878407
theorem B2112439 : Blo 1250443 2112439 := bstep (se 1 (by rfl) ⟨1584329, by rfl⟩ : syracuseStep 2112439 = 3168659) B3168659
theorem B1252295 : Blo 1250443 1252295 := bstep (se 1 (by rfl) ⟨939221, by rfl⟩ : syracuseStep 1252295 = 1878443) B1878443
theorem B1252315 : Blo 1250443 1252315 := bstep (se 1 (by rfl) ⟨939236, by rfl⟩ : syracuseStep 1252315 = 1878473) B1878473
theorem B10689509 : Blo 1250443 10689509 := bstep (se 4 (by rfl) ⟨1002141, by rfl⟩ : syracuseStep 10689509 = 2004283) B2004283
theorem B1252391 : Blo 1250443 1252391 := bstep (se 1 (by rfl) ⟨939293, by rfl⟩ : syracuseStep 1252391 = 1878587) B1878587
theorem B1252431 : Blo 1250443 1252431 := bstep (se 1 (by rfl) ⟨939323, by rfl⟩ : syracuseStep 1252431 = 1878647) B1878647
theorem B2112635 : Blo 1250443 2112635 := bstep (se 1 (by rfl) ⟨1584476, by rfl⟩ : syracuseStep 2112635 = 3168953) B3168953
theorem B4226201 : Blo 1250443 4226201 := bstep (se 2 (by rfl) ⟨1584825, by rfl⟩ : syracuseStep 4226201 = 3169651) B3169651
theorem B51412247 : Blo 1250443 51412247 := bstep (se 1 (by rfl) ⟨38559185, by rfl⟩ : syracuseStep 51412247 = 77118371) B77118371
theorem B1408351 : Blo 1250443 1408351 := bstep (se 1 (by rfl) ⟨1056263, by rfl⟩ : syracuseStep 1408351 = 2112527) B2112527
theorem B9264527 : Blo 1250443 9264527 := bstep (se 1 (by rfl) ⟨6948395, by rfl⟩ : syracuseStep 9264527 = 13896791) B13896791
theorem B43326899 : Blo 1250443 43326899 := bstep (se 1 (by rfl) ⟨32495174, by rfl⟩ : syracuseStep 43326899 = 64990349) B64990349
theorem B2538935 : Blo 1250443 2538935 := bstep (se 1 (by rfl) ⟨1904201, by rfl⟩ : syracuseStep 2538935 = 3808403) B3808403
theorem B2113033 : Blo 1250443 2113033 := bstep (se 2 (by rfl) ⟨792387, by rfl⟩ : syracuseStep 2113033 = 1584775) B1584775
theorem B2817575 : Blo 1250443 2817575 := bstep (se 1 (by rfl) ⟨2113181, by rfl⟩ : syracuseStep 2817575 = 4226363) B4226363
theorem B6340193 : Blo 1250443 6340193 := bstep (se 2 (by rfl) ⟨2377572, by rfl⟩ : syracuseStep 6340193 = 4755145) B4755145
theorem B9510533 : Blo 1250443 9510533 := bstep (se 4 (by rfl) ⟨891612, by rfl⟩ : syracuseStep 9510533 = 1783225) B1783225
theorem B2113195 : Blo 1250443 2113195 := bstep (se 1 (by rfl) ⟨1584896, by rfl⟩ : syracuseStep 2113195 = 3169793) B3169793
theorem B6332093 : Blo 1250443 6332093 := bstep (se 3 (by rfl) ⟨1187267, by rfl⟩ : syracuseStep 6332093 = 2374535) B2374535
theorem B1408711 : Blo 1250443 1408711 := bstep (se 1 (by rfl) ⟨1056533, by rfl⟩ : syracuseStep 1408711 = 2113067) B2113067
theorem B9625337 : Blo 1250443 9625337 := bstep (se 2 (by rfl) ⟨3609501, by rfl⟩ : syracuseStep 9625337 = 7219003) B7219003
theorem B36093701 : Blo 1250443 36093701 := bstep (se 4 (by rfl) ⟨3383784, by rfl⟩ : syracuseStep 36093701 = 6767569) B6767569
theorem B6332255 : Blo 1250443 6332255 := bstep (se 1 (by rfl) ⟨4749191, by rfl⟩ : syracuseStep 6332255 = 9498383) B9498383
theorem B2817899 : Blo 1250443 2817899 := bstep (se 1 (by rfl) ⟨2113424, by rfl⟩ : syracuseStep 2817899 = 4226849) B4226849
theorem B2817953 : Blo 1250443 2817953 := bstep (se 2 (by rfl) ⟨1056732, by rfl⟩ : syracuseStep 2817953 = 2113465) B2113465
theorem B1875887 : Blo 1250443 1875887 := bstep (se 1 (by rfl) ⟨1406915, by rfl⟩ : syracuseStep 1875887 = 2813831) B2813831
theorem B2113499 : Blo 1250443 2113499 := bstep (se 1 (by rfl) ⟨1585124, by rfl⟩ : syracuseStep 2113499 = 3170249) B3170249
theorem B6332417 : Blo 1250443 6332417 := bstep (se 2 (by rfl) ⟨2374656, by rfl⟩ : syracuseStep 6332417 = 4749313) B4749313
theorem B1876073 : Blo 1250443 1876073 := bstep (se 2 (by rfl) ⟨703527, by rfl⟩ : syracuseStep 1876073 = 1407055) B1407055
theorem B10682675 : Blo 1250443 10682675 := bstep (se 1 (by rfl) ⟨8012006, by rfl⟩ : syracuseStep 10682675 = 16024013) B16024013
theorem B4006235 : Blo 1250443 4006235 := bstep (se 1 (by rfl) ⟨3004676, by rfl⟩ : syracuseStep 4006235 = 6009353) B6009353
theorem B2376047 : Blo 1250443 2376047 := bstep (se 1 (by rfl) ⟨1782035, by rfl⟩ : syracuseStep 2376047 = 3564071) B3564071
theorem B1876391 : Blo 1250443 1876391 := bstep (se 1 (by rfl) ⟨1407293, by rfl⟩ : syracuseStep 1876391 = 2814587) B2814587
theorem B1876475 : Blo 1250443 1876475 := bstep (se 1 (by rfl) ⟨1407356, by rfl⟩ : syracuseStep 1876475 = 2814713) B2814713
theorem B9503243 : Blo 1250443 9503243 := bstep (se 1 (by rfl) ⟨7127432, by rfl⟩ : syracuseStep 9503243 = 14254865) B14254865
theorem B152273429 : Blo 1250443 152273429 := bstep (se 6 (by rfl) ⟨3568908, by rfl⟩ : syracuseStep 152273429 = 7137817) B7137817
theorem B24396389 : Blo 1250443 24396389 := bstep (se 4 (by rfl) ⟨2287161, by rfl⟩ : syracuseStep 24396389 = 4574323) B4574323
theorem B1876601 : Blo 1250443 1876601 := bstep (se 2 (by rfl) ⟨703725, by rfl⟩ : syracuseStep 1876601 = 1407451) B1407451
theorem B1876655 : Blo 1250443 1876655 := bstep (se 1 (by rfl) ⟨1407491, by rfl⟩ : syracuseStep 1876655 = 2814983) B2814983
theorem B1876703 : Blo 1250443 1876703 := bstep (se 1 (by rfl) ⟨1407527, by rfl⟩ : syracuseStep 1876703 = 2815055) B2815055
theorem B6333227 : Blo 1250443 6333227 := bstep (se 1 (by rfl) ⟨4749920, by rfl⟩ : syracuseStep 6333227 = 9499841) B9499841
theorem B10691423 : Blo 1250443 10691423 := bstep (se 1 (by rfl) ⟨8018567, by rfl⟩ : syracuseStep 10691423 = 16037135) B16037135
theorem B1876967 : Blo 1250443 1876967 := bstep (se 1 (by rfl) ⟨1407725, by rfl⟩ : syracuseStep 1876967 = 2815451) B2815451
theorem B8012803 : Blo 1250443 8012803 := bstep (se 1 (by rfl) ⟨6009602, by rfl⟩ : syracuseStep 8012803 = 12019205) B12019205
theorem B7128071 : Blo 1250443 7128071 := bstep (se 1 (by rfl) ⟨5346053, by rfl⟩ : syracuseStep 7128071 = 10692107) B10692107
theorem B5866711 : Blo 1250443 5866711 := bstep (se 1 (by rfl) ⟨4400033, by rfl⟩ : syracuseStep 5866711 = 8800067) B8800067
theorem B1877225 : Blo 1250443 1877225 := bstep (se 2 (by rfl) ⟨703959, by rfl⟩ : syracuseStep 1877225 = 1407919) B1407919
theorem B1877279 : Blo 1250443 1877279 := bstep (se 1 (by rfl) ⟨1407959, by rfl⟩ : syracuseStep 1877279 = 2815919) B2815919
theorem B1336667 : Blo 1250443 1336667 := bstep (se 1 (by rfl) ⟨1002500, by rfl⟩ : syracuseStep 1336667 = 2005001) B2005001
theorem B4818365 : Blo 1250443 4818365 := bstep (se 3 (by rfl) ⟨903443, by rfl⟩ : syracuseStep 4818365 = 1806887) B1806887
theorem B1877447 : Blo 1250443 1877447 := bstep (se 1 (by rfl) ⟨1408085, by rfl⟩ : syracuseStep 1877447 = 2816171) B2816171
theorem B4220423 : Blo 1250443 4220423 := bstep (se 1 (by rfl) ⟨3165317, by rfl⟩ : syracuseStep 4220423 = 6330635) B6330635
theorem B25691681 : Blo 1250443 25691681 := bstep (se 2 (by rfl) ⟨9634380, by rfl⟩ : syracuseStep 25691681 = 19268761) B19268761
theorem B2377451 : Blo 1250443 2377451 := bstep (se 1 (by rfl) ⟨1783088, by rfl⟩ : syracuseStep 2377451 = 3566177) B3566177
theorem B48105251 : Blo 1250443 48105251 := bstep (se 1 (by rfl) ⟨36078938, by rfl⟩ : syracuseStep 48105251 = 72157877) B72157877
theorem B1877801 : Blo 1250443 1877801 := bstep (se 2 (by rfl) ⟨704175, by rfl⟩ : syracuseStep 1877801 = 1408351) B1408351
theorem B1902383 : Blo 1250443 1902383 := bstep (se 1 (by rfl) ⟨1426787, by rfl⟩ : syracuseStep 1902383 = 2853575) B2853575
theorem B1877807 : Blo 1250443 1877807 := bstep (se 1 (by rfl) ⟨1408355, by rfl⟩ : syracuseStep 1877807 = 2816711) B2816711
theorem B10692485 : Blo 1250443 10692485 := bstep (se 4 (by rfl) ⟨1002420, by rfl⟩ : syracuseStep 10692485 = 2004841) B2004841
theorem B1583003 : Blo 1250443 1583003 := bstep (se 1 (by rfl) ⟨1187252, by rfl⟩ : syracuseStep 1583003 = 2374505) B2374505
theorem B3803087 : Blo 1250443 3803087 := bstep (se 1 (by rfl) ⟨2852315, by rfl⟩ : syracuseStep 3803087 = 5704631) B5704631
theorem B14256323 : Blo 1250443 14256323 := bstep (se 1 (by rfl) ⟨10692242, by rfl⟩ : syracuseStep 14256323 = 21384485) B21384485
theorem B6424771 : Blo 1250443 6424771 := bstep (se 1 (by rfl) ⟨4818578, by rfl⟩ : syracuseStep 6424771 = 9637157) B9637157
theorem B1902857 : Blo 1250443 1902857 := bstep (se 2 (by rfl) ⟨713571, by rfl⟩ : syracuseStep 1902857 = 1427143) B1427143
theorem B4753673 : Blo 1250443 4753673 := bstep (se 2 (by rfl) ⟨1782627, by rfl⟩ : syracuseStep 4753673 = 3565255) B3565255
theorem B1878281 : Blo 1250443 1878281 := bstep (se 2 (by rfl) ⟨704355, by rfl⟩ : syracuseStep 1878281 = 1408711) B1408711
theorem B1878383 : Blo 1250443 1878383 := bstep (se 1 (by rfl) ⟨1408787, by rfl⟩ : syracuseStep 1878383 = 2817575) B2817575
theorem B4221395 : Blo 1250443 4221395 := bstep (se 1 (by rfl) ⟨3166046, by rfl⟩ : syracuseStep 4221395 = 6332093) B6332093
theorem B5343731 : Blo 1250443 5343731 := bstep (se 1 (by rfl) ⟨4007798, by rfl⟩ : syracuseStep 5343731 = 8015597) B8015597
theorem B6416891 : Blo 1250443 6416891 := bstep (se 1 (by rfl) ⟨4812668, by rfl⟩ : syracuseStep 6416891 = 9625337) B9625337
theorem B24062467 : Blo 1250443 24062467 := bstep (se 1 (by rfl) ⟨18046850, by rfl⟩ : syracuseStep 24062467 = 36093701) B36093701
theorem B4221503 : Blo 1250443 4221503 := bstep (se 1 (by rfl) ⟨3166127, by rfl⟩ : syracuseStep 4221503 = 6332255) B6332255
theorem B1878599 : Blo 1250443 1878599 := bstep (se 1 (by rfl) ⟨1408949, by rfl⟩ : syracuseStep 1878599 = 2817899) B2817899
theorem B3050057 : Blo 1250443 3050057 := bstep (se 2 (by rfl) ⟨1143771, by rfl⟩ : syracuseStep 3050057 = 2287543) B2287543
theorem B1878635 : Blo 1250443 1878635 := bstep (se 1 (by rfl) ⟨1408976, by rfl⟩ : syracuseStep 1878635 = 2817953) B2817953
theorem B6335171 : Blo 1250443 6335171 := bstep (se 1 (by rfl) ⟨4751378, by rfl⟩ : syracuseStep 6335171 = 9502757) B9502757
theorem B12020471 : Blo 1250443 12020471 := bstep (se 1 (by rfl) ⟨9015353, by rfl⟩ : syracuseStep 12020471 = 18030707) B18030707
theorem B9497411 : Blo 1250443 9497411 := bstep (se 1 (by rfl) ⟨7123058, by rfl⟩ : syracuseStep 9497411 = 14246117) B14246117
theorem B3165601 : Blo 1250443 3165601 := bstep (se 2 (by rfl) ⟨1187100, by rfl⟩ : syracuseStep 3165601 = 2374201) B2374201
theorem B45641393 : Blo 1250443 45641393 := bstep (se 2 (by rfl) ⟨17115522, by rfl⟩ : syracuseStep 45641393 = 34231045) B34231045
theorem B6016771 : Blo 1250443 6016771 := bstep (se 1 (by rfl) ⟨4512578, by rfl⟩ : syracuseStep 6016771 = 9025157) B9025157
theorem B2141959 : Blo 1250443 2141959 := bstep (se 1 (by rfl) ⟨1606469, by rfl⟩ : syracuseStep 2141959 = 3212939) B3212939
theorem B1781551 : Blo 1250443 1781551 := bstep (se 1 (by rfl) ⟨1336163, by rfl⟩ : syracuseStep 1781551 = 2672327) B2672327
theorem B2813903 : Blo 1250443 2813903 := bstep (se 1 (by rfl) ⟨2110427, by rfl⟩ : syracuseStep 2813903 = 4220855) B4220855
theorem B3805193 : Blo 1250443 3805193 := bstep (se 2 (by rfl) ⟨1426947, by rfl⟩ : syracuseStep 3805193 = 2853895) B2853895
theorem B4509755 : Blo 1250443 4509755 := bstep (se 1 (by rfl) ⟨3382316, by rfl⟩ : syracuseStep 4509755 = 6764633) B6764633
theorem B24047705 : Blo 1250443 24047705 := bstep (se 2 (by rfl) ⟨9017889, by rfl⟩ : syracuseStep 24047705 = 18035779) B18035779
theorem B3805289 : Blo 1250443 3805289 := bstep (se 2 (by rfl) ⟨1426983, by rfl⟩ : syracuseStep 3805289 = 2853967) B2853967
theorem B2814281 : Blo 1250443 2814281 := bstep (se 2 (by rfl) ⟨1055355, by rfl⟩ : syracuseStep 2814281 = 2110711) B2110711
theorem B2814299 : Blo 1250443 2814299 := bstep (se 1 (by rfl) ⟨2110724, by rfl⟩ : syracuseStep 2814299 = 4221449) B4221449
theorem B4510043 : Blo 1250443 4510043 := bstep (se 1 (by rfl) ⟨3382532, by rfl⟩ : syracuseStep 4510043 = 6765065) B6765065
theorem B4223339 : Blo 1250443 4223339 := bstep (se 1 (by rfl) ⟨3167504, by rfl⟩ : syracuseStep 4223339 = 6335009) B6335009
theorem B13537651 : Blo 1250443 13537651 := bstep (se 1 (by rfl) ⟨10153238, by rfl⟩ : syracuseStep 13537651 = 20306477) B20306477
theorem B3166715 : Blo 1250443 3166715 := bstep (se 1 (by rfl) ⟨2375036, by rfl⟩ : syracuseStep 3166715 = 4750073) B4750073
theorem B7615073 : Blo 1250443 7615073 := bstep (se 2 (by rfl) ⟨2855652, by rfl⟩ : syracuseStep 7615073 = 5711305) B5711305
theorem B4223609 : Blo 1250443 4223609 := bstep (se 2 (by rfl) ⟨1583853, by rfl⟩ : syracuseStep 4223609 = 3167707) B3167707
theorem B2814875 : Blo 1250443 2814875 := bstep (se 1 (by rfl) ⟨2111156, by rfl⟩ : syracuseStep 2814875 = 4222313) B4222313
theorem B1692623 : Blo 1250443 1692623 := bstep (se 1 (by rfl) ⟨1269467, by rfl⟩ : syracuseStep 1692623 = 2538935) B2538935
theorem B12030929 : Blo 1250443 12030929 := bstep (se 2 (by rfl) ⟨4511598, by rfl⟩ : syracuseStep 12030929 = 9023197) B9023197
theorem B2815073 : Blo 1250443 2815073 := bstep (se 2 (by rfl) ⟨1055652, by rfl⟩ : syracuseStep 2815073 = 2111305) B2111305
theorem B12022931 : Blo 1250443 12022931 := bstep (se 1 (by rfl) ⟨9017198, by rfl⟩ : syracuseStep 12022931 = 18034397) B18034397
theorem B1250591 : Blo 1250443 1250591 := bstep (se 1 (by rfl) ⟨937943, by rfl⟩ : syracuseStep 1250591 = 1875887) B1875887
theorem B2815271 : Blo 1250443 2815271 := bstep (se 1 (by rfl) ⟨2111453, by rfl⟩ : syracuseStep 2815271 = 4222907) B4222907
theorem B1250651 : Blo 1250443 1250651 := bstep (se 1 (by rfl) ⟨937988, by rfl⟩ : syracuseStep 1250651 = 1875977) B1875977
theorem B1250671 : Blo 1250443 1250671 := bstep (se 1 (by rfl) ⟨938003, by rfl⟩ : syracuseStep 1250671 = 1876007) B1876007
theorem B9024929 : Blo 1250443 9024929 := bstep (se 2 (by rfl) ⟨3384348, by rfl⟩ : syracuseStep 9024929 = 6768697) B6768697
theorem B1250727 : Blo 1250443 1250727 := bstep (se 1 (by rfl) ⟨938045, by rfl⟩ : syracuseStep 1250727 = 1876091) B1876091
theorem B3167687 : Blo 1250443 3167687 := bstep (se 1 (by rfl) ⟨2375765, by rfl⟩ : syracuseStep 3167687 = 4751531) B4751531
theorem B1250811 : Blo 1250443 1250811 := bstep (se 1 (by rfl) ⟨938108, by rfl⟩ : syracuseStep 1250811 = 1876217) B1876217
theorem B1250879 : Blo 1250443 1250879 := bstep (se 1 (by rfl) ⟨938159, by rfl⟩ : syracuseStep 1250879 = 1876319) B1876319
theorem B1250887 : Blo 1250443 1250887 := bstep (se 1 (by rfl) ⟨938165, by rfl⟩ : syracuseStep 1250887 = 1876331) B1876331
theorem B2815649 : Blo 1250443 2815649 := bstep (se 2 (by rfl) ⟨1055868, by rfl⟩ : syracuseStep 2815649 = 2111737) B2111737
theorem B1251039 : Blo 1250443 1251039 := bstep (se 1 (by rfl) ⟨938279, by rfl⟩ : syracuseStep 1251039 = 1876559) B1876559
theorem B2537257 : Blo 1250443 2537257 := bstep (se 2 (by rfl) ⟨951471, by rfl⟩ : syracuseStep 2537257 = 1902943) B1902943
theorem B1406767 : Blo 1250443 1406767 := bstep (se 1 (by rfl) ⟨1055075, by rfl⟩ : syracuseStep 1406767 = 2110151) B2110151
theorem B1251119 : Blo 1250443 1251119 := bstep (se 1 (by rfl) ⟨938339, by rfl⟩ : syracuseStep 1251119 = 1876679) B1876679
theorem B1406875 : Blo 1250443 1406875 := bstep (se 1 (by rfl) ⟨1055156, by rfl⟩ : syracuseStep 1406875 = 2110313) B2110313
theorem B1251227 : Blo 1250443 1251227 := bstep (se 1 (by rfl) ⟨938420, by rfl⟩ : syracuseStep 1251227 = 1876841) B1876841
theorem B1251279 : Blo 1250443 1251279 := bstep (se 1 (by rfl) ⟨938459, by rfl⟩ : syracuseStep 1251279 = 1876919) B1876919
theorem B1251303 : Blo 1250443 1251303 := bstep (se 1 (by rfl) ⟨938477, by rfl⟩ : syracuseStep 1251303 = 1876955) B1876955
theorem B2816009 : Blo 1250443 2816009 := bstep (se 2 (by rfl) ⟨1056003, by rfl⟩ : syracuseStep 2816009 = 2112007) B2112007
theorem B20297789 : Blo 1250443 20297789 := bstep (se 3 (by rfl) ⟨3805835, by rfl⟩ : syracuseStep 20297789 = 7611671) B7611671
theorem B3168467 : Blo 1250443 3168467 := bstep (se 1 (by rfl) ⟨2376350, by rfl⟩ : syracuseStep 3168467 = 4752701) B4752701
theorem B10688759 : Blo 1250443 10688759 := bstep (se 1 (by rfl) ⟨8016569, by rfl⟩ : syracuseStep 10688759 = 16033139) B16033139
theorem B1251615 : Blo 1250443 1251615 := bstep (se 1 (by rfl) ⟨938711, by rfl⟩ : syracuseStep 1251615 = 1877423) B1877423
theorem B1407271 : Blo 1250443 1407271 := bstep (se 1 (by rfl) ⟨1055453, by rfl⟩ : syracuseStep 1407271 = 2110907) B2110907
theorem B40581425 : Blo 1250443 40581425 := bstep (se 2 (by rfl) ⟨15218034, by rfl⟩ : syracuseStep 40581425 = 30436069) B30436069
theorem B1251675 : Blo 1250443 1251675 := bstep (se 1 (by rfl) ⟨938756, by rfl⟩ : syracuseStep 1251675 = 1877513) B1877513
theorem B1407343 : Blo 1250443 1407343 := bstep (se 1 (by rfl) ⟨1055507, by rfl⟩ : syracuseStep 1407343 = 2111015) B2111015
theorem B1251695 : Blo 1250443 1251695 := bstep (se 1 (by rfl) ⟨938771, by rfl⟩ : syracuseStep 1251695 = 1877543) B1877543
theorem B4225391 : Blo 1250443 4225391 := bstep (se 1 (by rfl) ⟨3169043, by rfl⟩ : syracuseStep 4225391 = 6338087) B6338087
theorem B2816423 : Blo 1250443 2816423 := bstep (se 1 (by rfl) ⟨2112317, by rfl⟩ : syracuseStep 2816423 = 4224635) B4224635
theorem B1251751 : Blo 1250443 1251751 := bstep (se 1 (by rfl) ⟨938813, by rfl⟩ : syracuseStep 1251751 = 1877627) B1877627
theorem B3168679 : Blo 1250443 3168679 := bstep (se 1 (by rfl) ⟨2376509, by rfl⟩ : syracuseStep 3168679 = 4753019) B4753019
theorem B6330797 : Blo 1250443 6330797 := bstep (se 3 (by rfl) ⟨1187024, by rfl⟩ : syracuseStep 6330797 = 2374049) B2374049
theorem B20576693 : Blo 1250443 20576693 := bstep (se 5 (by rfl) ⟨964532, by rfl⟩ : syracuseStep 20576693 = 1929065) B1929065
theorem B6339059 : Blo 1250443 6339059 := bstep (se 1 (by rfl) ⟨4754294, by rfl⟩ : syracuseStep 6339059 = 9508589) B9508589
theorem B1251835 : Blo 1250443 1251835 := bstep (se 1 (by rfl) ⟨938876, by rfl⟩ : syracuseStep 1251835 = 1877753) B1877753
theorem B2816531 : Blo 1250443 2816531 := bstep (se 1 (by rfl) ⟨2112398, by rfl⟩ : syracuseStep 2816531 = 4224797) B4224797
theorem B1251903 : Blo 1250443 1251903 := bstep (se 1 (by rfl) ⟨938927, by rfl⟩ : syracuseStep 1251903 = 1877855) B1877855
theorem B1407559 : Blo 1250443 1407559 := bstep (se 1 (by rfl) ⟨1055669, by rfl⟩ : syracuseStep 1407559 = 2111339) B2111339
theorem B1251911 : Blo 1250443 1251911 := bstep (se 1 (by rfl) ⟨938933, by rfl⟩ : syracuseStep 1251911 = 1877867) B1877867
theorem B2816585 : Blo 1250443 2816585 := bstep (se 2 (by rfl) ⟨1056219, by rfl⟩ : syracuseStep 2816585 = 2112439) B2112439
theorem B3168841 : Blo 1250443 3168841 := bstep (se 2 (by rfl) ⟨1188315, by rfl⟩ : syracuseStep 3168841 = 2376631) B2376631
theorem B6330959 : Blo 1250443 6330959 := bstep (se 1 (by rfl) ⟨4748219, by rfl⟩ : syracuseStep 6330959 = 9496439) B9496439
theorem B4815467 : Blo 1250443 4815467 := bstep (se 1 (by rfl) ⟨3611600, by rfl⟩ : syracuseStep 4815467 = 7223201) B7223201
theorem B2407087 : Blo 1250443 2407087 := bstep (se 1 (by rfl) ⟨1805315, by rfl⟩ : syracuseStep 2407087 = 3610631) B3610631
theorem B5348035 : Blo 1250443 5348035 := bstep (se 1 (by rfl) ⟨4011026, by rfl⟩ : syracuseStep 5348035 = 8022053) B8022053
theorem B2112223 : Blo 1250443 2112223 := bstep (se 1 (by rfl) ⟨1584167, by rfl⟩ : syracuseStep 2112223 = 3168335) B3168335
theorem B1252063 : Blo 1250443 1252063 := bstep (se 1 (by rfl) ⟨939047, by rfl⟩ : syracuseStep 1252063 = 1878095) B1878095
theorem B1252143 : Blo 1250443 1252143 := bstep (se 1 (by rfl) ⟨939107, by rfl⟩ : syracuseStep 1252143 = 1878215) B1878215
theorem B3087247 : Blo 1250443 3087247 := bstep (se 1 (by rfl) ⟨2315435, by rfl⟩ : syracuseStep 3087247 = 4630871) B4630871
theorem B1252251 : Blo 1250443 1252251 := bstep (se 1 (by rfl) ⟨939188, by rfl⟩ : syracuseStep 1252251 = 1878377) B1878377
theorem B1252303 : Blo 1250443 1252303 := bstep (se 1 (by rfl) ⟨939227, by rfl⟩ : syracuseStep 1252303 = 1878455) B1878455
theorem B2816999 : Blo 1250443 2816999 := bstep (se 1 (by rfl) ⟨2112749, by rfl⟩ : syracuseStep 2816999 = 4225499) B4225499
theorem B1252327 : Blo 1250443 1252327 := bstep (se 1 (by rfl) ⟨939245, by rfl⟩ : syracuseStep 1252327 = 1878491) B1878491
theorem B6339707 : Blo 1250443 6339707 := bstep (se 1 (by rfl) ⟨4754780, by rfl⟩ : syracuseStep 6339707 = 9509561) B9509561
theorem B2112655 : Blo 1250443 2112655 := bstep (se 1 (by rfl) ⟨1584491, by rfl⟩ : syracuseStep 2112655 = 3168983) B3168983
theorem B1604827 : Blo 1250443 1604827 := bstep (se 1 (by rfl) ⟨1203620, by rfl⟩ : syracuseStep 1604827 = 2407241) B2407241
theorem B7126339 : Blo 1250443 7126339 := bstep (se 1 (by rfl) ⟨5344754, by rfl⟩ : syracuseStep 7126339 = 10689509) B10689509
theorem B2817377 : Blo 1250443 2817377 := bstep (se 2 (by rfl) ⟨1056516, by rfl⟩ : syracuseStep 2817377 = 2113033) B2113033
theorem B3169631 : Blo 1250443 3169631 := bstep (se 1 (by rfl) ⟨2377223, by rfl⟩ : syracuseStep 3169631 = 4754447) B4754447
theorem B3382651 : Blo 1250443 3382651 := bstep (se 1 (by rfl) ⟨2536988, by rfl⟩ : syracuseStep 3382651 = 5073977) B5073977
theorem B2112905 : Blo 1250443 2112905 := bstep (se 2 (by rfl) ⟨792339, by rfl⟩ : syracuseStep 2112905 = 1584679) B1584679
theorem B1408423 : Blo 1250443 1408423 := bstep (se 1 (by rfl) ⟨1056317, by rfl⟩ : syracuseStep 1408423 = 2112635) B2112635
theorem B2817467 : Blo 1250443 2817467 := bstep (se 1 (by rfl) ⟨2113100, by rfl⟩ : syracuseStep 2817467 = 4226201) B4226201
theorem B34274831 : Blo 1250443 34274831 := bstep (se 1 (by rfl) ⟨25706123, by rfl⟩ : syracuseStep 34274831 = 51412247) B51412247
theorem B2817593 : Blo 1250443 2817593 := bstep (se 2 (by rfl) ⟨1056597, by rfl⟩ : syracuseStep 2817593 = 2113195) B2113195
theorem B6176351 : Blo 1250443 6176351 := bstep (se 1 (by rfl) ⟨4632263, by rfl⟩ : syracuseStep 6176351 = 9264527) B9264527
theorem B28884599 : Blo 1250443 28884599 := bstep (se 1 (by rfl) ⟨21663449, by rfl⟩ : syracuseStep 28884599 = 43326899) B43326899
theorem B4226795 : Blo 1250443 4226795 := bstep (se 1 (by rfl) ⟨3170096, by rfl⟩ : syracuseStep 4226795 = 6340193) B6340193
theorem B6340355 : Blo 1250443 6340355 := bstep (se 1 (by rfl) ⟨4755266, by rfl⟩ : syracuseStep 6340355 = 9510533) B9510533
theorem B1875767 : Blo 1250443 1875767 := bstep (se 1 (by rfl) ⟨1406825, by rfl⟩ : syracuseStep 1875767 = 2813651) B2813651
theorem B2113337 : Blo 1250443 2113337 := bstep (se 2 (by rfl) ⟨792501, by rfl⟩ : syracuseStep 2113337 = 1585003) B1585003
theorem B12033967 : Blo 1250443 12033967 := bstep (se 1 (by rfl) ⟨9025475, by rfl⟩ : syracuseStep 12033967 = 18050951) B18050951
theorem B1408999 : Blo 1250443 1408999 := bstep (se 1 (by rfl) ⟨1056749, by rfl⟩ : syracuseStep 1408999 = 2113499) B2113499
theorem B3006503 : Blo 1250443 3006503 := bstep (se 1 (by rfl) ⟨2254877, by rfl⟩ : syracuseStep 3006503 = 4509755) B4509755
theorem B16031803 : Blo 1250443 16031803 := bstep (se 1 (by rfl) ⟨12023852, by rfl⟩ : syracuseStep 16031803 = 24047705) B24047705
theorem B1876187 : Blo 1250443 1876187 := bstep (se 1 (by rfl) ⟨1407140, by rfl⟩ : syracuseStep 1876187 = 2814281) B2814281
theorem B2670823 : Blo 1250443 2670823 := bstep (se 1 (by rfl) ⟨2003117, by rfl⟩ : syracuseStep 2670823 = 4006235) B4006235
theorem B1876199 : Blo 1250443 1876199 := bstep (se 1 (by rfl) ⟨1407149, by rfl⟩ : syracuseStep 1876199 = 2814299) B2814299
theorem B3006695 : Blo 1250443 3006695 := bstep (se 1 (by rfl) ⟨2255021, by rfl⟩ : syracuseStep 3006695 = 4510043) B4510043
theorem B101515619 : Blo 1250443 101515619 := bstep (se 1 (by rfl) ⟨76136714, by rfl⟩ : syracuseStep 101515619 = 152273429) B152273429
theorem B1876361 : Blo 1250443 1876361 := bstep (se 2 (by rfl) ⟨703635, by rfl⟩ : syracuseStep 1876361 = 1407271) B1407271
theorem B1876457 : Blo 1250443 1876457 := bstep (se 2 (by rfl) ⟨703671, by rfl⟩ : syracuseStep 1876457 = 1407343) B1407343
theorem B7127615 : Blo 1250443 7127615 := bstep (se 1 (by rfl) ⟨5345711, by rfl⟩ : syracuseStep 7127615 = 10691423) B10691423
theorem B1876583 : Blo 1250443 1876583 := bstep (se 1 (by rfl) ⟨1407437, by rfl⟩ : syracuseStep 1876583 = 2814875) B2814875
theorem B8020619 : Blo 1250443 8020619 := bstep (se 1 (by rfl) ⟨6015464, by rfl⟩ : syracuseStep 8020619 = 12030929) B12030929
theorem B4752047 : Blo 1250443 4752047 := bstep (se 1 (by rfl) ⟨3564035, by rfl⟩ : syracuseStep 4752047 = 7128071) B7128071
theorem B1876715 : Blo 1250443 1876715 := bstep (se 1 (by rfl) ⟨1407536, by rfl⟩ : syracuseStep 1876715 = 2815073) B2815073
theorem B1876745 : Blo 1250443 1876745 := bstep (se 2 (by rfl) ⟨703779, by rfl⟩ : syracuseStep 1876745 = 1407559) B1407559
theorem B1876847 : Blo 1250443 1876847 := bstep (se 1 (by rfl) ⟨1407635, by rfl⟩ : syracuseStep 1876847 = 2815271) B2815271
theorem B12837797 : Blo 1250443 12837797 := bstep (se 4 (by rfl) ⟨1203543, by rfl⟩ : syracuseStep 12837797 = 2407087) B2407087
theorem B3212243 : Blo 1250443 3212243 := bstep (se 1 (by rfl) ⟨2409182, by rfl⟩ : syracuseStep 3212243 = 4818365) B4818365
theorem B1877099 : Blo 1250443 1877099 := bstep (se 1 (by rfl) ⟨1407824, by rfl⟩ : syracuseStep 1877099 = 2815649) B2815649
theorem B7128323 : Blo 1250443 7128323 := bstep (se 1 (by rfl) ⟨5346242, by rfl⟩ : syracuseStep 7128323 = 10692485) B10692485
theorem B10683737 : Blo 1250443 10683737 := bstep (se 2 (by rfl) ⟨4006401, by rfl⟩ : syracuseStep 10683737 = 8012803) B8012803
theorem B1877339 : Blo 1250443 1877339 := bstep (se 1 (by rfl) ⟨1408004, by rfl⟩ : syracuseStep 1877339 = 2816009) B2816009
theorem B91399549 : Blo 1250443 91399549 := bstep (se 3 (by rfl) ⟨17137415, by rfl⟩ : syracuseStep 91399549 = 34274831) B34274831
theorem B9504215 : Blo 1250443 9504215 := bstep (se 1 (by rfl) ⟨7128161, by rfl⟩ : syracuseStep 9504215 = 14256323) B14256323
theorem B1877615 : Blo 1250443 1877615 := bstep (se 1 (by rfl) ⟨1408211, by rfl⟩ : syracuseStep 1877615 = 2816423) B2816423
theorem B4220531 : Blo 1250443 4220531 := bstep (se 1 (by rfl) ⟨3165398, by rfl⟩ : syracuseStep 4220531 = 6330797) B6330797
theorem B2139769 : Blo 1250443 2139769 := bstep (se 2 (by rfl) ⟨802413, by rfl⟩ : syracuseStep 2139769 = 1604827) B1604827
theorem B4277927 : Blo 1250443 4277927 := bstep (se 1 (by rfl) ⟨3208445, by rfl⟩ : syracuseStep 4277927 = 6416891) B6416891
theorem B1877687 : Blo 1250443 1877687 := bstep (se 1 (by rfl) ⟨1408265, by rfl⟩ : syracuseStep 1877687 = 2816531) B2816531
theorem B1877723 : Blo 1250443 1877723 := bstep (se 1 (by rfl) ⟨1408292, by rfl⟩ : syracuseStep 1877723 = 2816585) B2816585
theorem B2033371 : Blo 1250443 2033371 := bstep (se 1 (by rfl) ⟨1525028, by rfl⟩ : syracuseStep 2033371 = 3050057) B3050057
theorem B4220639 : Blo 1250443 4220639 := bstep (se 1 (by rfl) ⟨3165479, by rfl⟩ : syracuseStep 4220639 = 6330959) B6330959
theorem B8013647 : Blo 1250443 8013647 := bstep (se 1 (by rfl) ⟨6010235, by rfl⟩ : syracuseStep 8013647 = 12020471) B12020471
theorem B4220801 : Blo 1250443 4220801 := bstep (se 2 (by rfl) ⟨1582800, by rfl⟩ : syracuseStep 4220801 = 3165601) B3165601
theorem B1877897 : Blo 1250443 1877897 := bstep (se 2 (by rfl) ⟨704211, by rfl⟩ : syracuseStep 1877897 = 1408423) B1408423
theorem B18040805 : Blo 1250443 18040805 := bstep (se 4 (by rfl) ⟨1691325, by rfl⟩ : syracuseStep 18040805 = 3382651) B3382651
theorem B1877999 : Blo 1250443 1877999 := bstep (se 1 (by rfl) ⟨1408499, by rfl⟩ : syracuseStep 1877999 = 2816999) B2816999
theorem B1878251 : Blo 1250443 1878251 := bstep (se 1 (by rfl) ⟨1408688, by rfl⟩ : syracuseStep 1878251 = 2817377) B2817377
theorem B1878311 : Blo 1250443 1878311 := bstep (se 1 (by rfl) ⟨1408733, by rfl⟩ : syracuseStep 1878311 = 2817467) B2817467
theorem B8022361 : Blo 1250443 8022361 := bstep (se 2 (by rfl) ⟨3008385, by rfl⟩ : syracuseStep 8022361 = 6016771) B6016771
theorem B1878395 : Blo 1250443 1878395 := bstep (se 1 (by rfl) ⟨1408796, by rfl⟩ : syracuseStep 1878395 = 2817593) B2817593
theorem B4221341 : Blo 1250443 4221341 := bstep (se 3 (by rfl) ⟨791501, by rfl⟩ : syracuseStep 4221341 = 1583003) B1583003
theorem B30427595 : Blo 1250443 30427595 := bstep (se 1 (by rfl) ⟨22820696, by rfl⟩ : syracuseStep 30427595 = 45641393) B45641393
theorem B1878665 : Blo 1250443 1878665 := bstep (se 2 (by rfl) ⟨704499, by rfl⟩ : syracuseStep 1878665 = 1408999) B1408999
theorem B4221611 : Blo 1250443 4221611 := bstep (se 1 (by rfl) ⟨3166208, by rfl⟩ : syracuseStep 4221611 = 6332417) B6332417
theorem B7121783 : Blo 1250443 7121783 := bstep (se 1 (by rfl) ⟨5341337, by rfl⟩ : syracuseStep 7121783 = 10682675) B10682675
theorem B1584031 : Blo 1250443 1584031 := bstep (se 1 (by rfl) ⟨1188023, by rfl⟩ : syracuseStep 1584031 = 2376047) B2376047
theorem B6335495 : Blo 1250443 6335495 := bstep (se 1 (by rfl) ⟨4751621, by rfl⟩ : syracuseStep 6335495 = 9503243) B9503243
theorem B16264259 : Blo 1250443 16264259 := bstep (se 1 (by rfl) ⟨12198194, by rfl⟩ : syracuseStep 16264259 = 24396389) B24396389
theorem B18050201 : Blo 1250443 18050201 := bstep (se 2 (by rfl) ⟨6768825, by rfl⟩ : syracuseStep 18050201 = 13537651) B13537651
theorem B4222151 : Blo 1250443 4222151 := bstep (se 1 (by rfl) ⟨3166613, by rfl⟩ : syracuseStep 4222151 = 6333227) B6333227
theorem B32083289 : Blo 1250443 32083289 := bstep (se 2 (by rfl) ⟨12031233, by rfl⟩ : syracuseStep 32083289 = 24062467) B24062467
theorem B5074285 : Blo 1250443 5074285 := bstep (se 3 (by rfl) ⟨951428, by rfl⟩ : syracuseStep 5074285 = 1902857) B1902857
theorem B8015287 : Blo 1250443 8015287 := bstep (se 1 (by rfl) ⟨6011465, by rfl⟩ : syracuseStep 8015287 = 12022931) B12022931
theorem B7130713 : Blo 1250443 7130713 := bstep (se 2 (by rfl) ⟨2674017, by rfl⟩ : syracuseStep 7130713 = 5348035) B5348035
theorem B6016619 : Blo 1250443 6016619 := bstep (se 1 (by rfl) ⟨4512464, by rfl⟩ : syracuseStep 6016619 = 9024929) B9024929
theorem B14257781 : Blo 1250443 14257781 := bstep (se 5 (by rfl) ⟨668333, by rfl⟩ : syracuseStep 14257781 = 1336667) B1336667
theorem B2813615 : Blo 1250443 2813615 := bstep (se 1 (by rfl) ⟨2110211, by rfl⟩ : syracuseStep 2813615 = 4220423) B4220423
theorem B31289125 : Blo 1250443 31289125 := bstep (se 4 (by rfl) ⟨2933355, by rfl⟩ : syracuseStep 31289125 = 5866711) B5866711
theorem B4116329 : Blo 1250443 4116329 := bstep (se 2 (by rfl) ⟨1543623, by rfl⟩ : syracuseStep 4116329 = 3087247) B3087247
theorem B2535391 : Blo 1250443 2535391 := bstep (se 1 (by rfl) ⟨1901543, by rfl⟩ : syracuseStep 2535391 = 3803087) B3803087
theorem B27054283 : Blo 1250443 27054283 := bstep (se 1 (by rfl) ⟨20290712, by rfl⟩ : syracuseStep 27054283 = 40581425) B40581425
theorem B13717795 : Blo 1250443 13717795 := bstep (se 1 (by rfl) ⟨10288346, by rfl⟩ : syracuseStep 13717795 = 20576693) B20576693
theorem B2814263 : Blo 1250443 2814263 := bstep (se 1 (by rfl) ⟨2110697, by rfl⟩ : syracuseStep 2814263 = 4221395) B4221395
theorem B2814335 : Blo 1250443 2814335 := bstep (se 1 (by rfl) ⟨2110751, by rfl⟩ : syracuseStep 2814335 = 4221503) B4221503
theorem B4223447 : Blo 1250443 4223447 := bstep (se 1 (by rfl) ⟨3167585, by rfl⟩ : syracuseStep 4223447 = 6335171) B6335171
theorem B2855945 : Blo 1250443 2855945 := bstep (se 2 (by rfl) ⟨1070979, by rfl⟩ : syracuseStep 2855945 = 2141959) B2141959
theorem B4117567 : Blo 1250443 4117567 := bstep (se 1 (by rfl) ⟨3088175, by rfl⟩ : syracuseStep 4117567 = 6176351) B6176351
theorem B19256399 : Blo 1250443 19256399 := bstep (se 1 (by rfl) ⟨14442299, by rfl⟩ : syracuseStep 19256399 = 28884599) B28884599
theorem B1250511 : Blo 1250443 1250511 := bstep (se 1 (by rfl) ⟨937883, by rfl⟩ : syracuseStep 1250511 = 1875767) B1875767
theorem B16045289 : Blo 1250443 16045289 := bstep (se 2 (by rfl) ⟨6016983, by rfl⟩ : syracuseStep 16045289 = 12033967) B12033967
theorem B2536795 : Blo 1250443 2536795 := bstep (se 1 (by rfl) ⟨1902596, by rfl⟩ : syracuseStep 2536795 = 3805193) B3805193
theorem B1250715 : Blo 1250443 1250715 := bstep (se 1 (by rfl) ⟨938036, by rfl⟩ : syracuseStep 1250715 = 1876073) B1876073
theorem B2536859 : Blo 1250443 2536859 := bstep (se 1 (by rfl) ⟨1902644, by rfl⟩ : syracuseStep 2536859 = 3805289) B3805289
theorem B2815559 : Blo 1250443 2815559 := bstep (se 1 (by rfl) ⟨2111669, by rfl⟩ : syracuseStep 2815559 = 4223339) B4223339
theorem B8566361 : Blo 1250443 8566361 := bstep (se 2 (by rfl) ⟨3212385, by rfl⟩ : syracuseStep 8566361 = 6424771) B6424771
theorem B1250927 : Blo 1250443 1250927 := bstep (se 1 (by rfl) ⟨938195, by rfl⟩ : syracuseStep 1250927 = 1876391) B1876391
theorem B1250983 : Blo 1250443 1250983 := bstep (se 1 (by rfl) ⟨938237, by rfl⟩ : syracuseStep 1250983 = 1876475) B1876475
theorem B2111143 : Blo 1250443 2111143 := bstep (se 1 (by rfl) ⟨1583357, by rfl⟩ : syracuseStep 2111143 = 3166715) B3166715
theorem B1251067 : Blo 1250443 1251067 := bstep (se 1 (by rfl) ⟨938300, by rfl⟩ : syracuseStep 1251067 = 1876601) B1876601
theorem B2815739 : Blo 1250443 2815739 := bstep (se 1 (by rfl) ⟨2111804, by rfl⟩ : syracuseStep 2815739 = 4223609) B4223609
theorem B1251103 : Blo 1250443 1251103 := bstep (se 1 (by rfl) ⟨938327, by rfl⟩ : syracuseStep 1251103 = 1876655) B1876655
theorem B1251135 : Blo 1250443 1251135 := bstep (se 1 (by rfl) ⟨938351, by rfl⟩ : syracuseStep 1251135 = 1876703) B1876703
theorem B4224905 : Blo 1250443 4224905 := bstep (se 2 (by rfl) ⟨1584339, by rfl⟩ : syracuseStep 4224905 = 3168679) B3168679
theorem B1251311 : Blo 1250443 1251311 := bstep (se 1 (by rfl) ⟨938483, by rfl⟩ : syracuseStep 1251311 = 1876967) B1876967
theorem B4225121 : Blo 1250443 4225121 := bstep (se 2 (by rfl) ⟨1584420, by rfl⟩ : syracuseStep 4225121 = 3168841) B3168841
theorem B1251483 : Blo 1250443 1251483 := bstep (se 1 (by rfl) ⟨938612, by rfl⟩ : syracuseStep 1251483 = 1877225) B1877225
theorem B1251519 : Blo 1250443 1251519 := bstep (se 1 (by rfl) ⟨938639, by rfl⟩ : syracuseStep 1251519 = 1877279) B1877279
theorem B2816297 : Blo 1250443 2816297 := bstep (se 2 (by rfl) ⟨1056111, by rfl⟩ : syracuseStep 2816297 = 2112223) B2112223
theorem B2111791 : Blo 1250443 2111791 := bstep (se 1 (by rfl) ⟨1583843, by rfl⟩ : syracuseStep 2111791 = 3167687) B3167687
theorem B1251631 : Blo 1250443 1251631 := bstep (se 1 (by rfl) ⟨938723, by rfl⟩ : syracuseStep 1251631 = 1877447) B1877447
theorem B17127787 : Blo 1250443 17127787 := bstep (se 1 (by rfl) ⟨12845840, by rfl⟩ : syracuseStep 17127787 = 25691681) B25691681
theorem B32070167 : Blo 1250443 32070167 := bstep (se 1 (by rfl) ⟨24052625, by rfl⟩ : syracuseStep 32070167 = 48105251) B48105251
theorem B1251867 : Blo 1250443 1251867 := bstep (se 1 (by rfl) ⟨938900, by rfl⟩ : syracuseStep 1251867 = 1877801) B1877801
theorem B1268255 : Blo 1250443 1268255 := bstep (se 1 (by rfl) ⟨951191, by rfl⟩ : syracuseStep 1268255 = 1902383) B1902383
theorem B1251871 : Blo 1250443 1251871 := bstep (se 1 (by rfl) ⟨938903, by rfl⟩ : syracuseStep 1251871 = 1877807) B1877807
theorem B13531859 : Blo 1250443 13531859 := bstep (se 1 (by rfl) ⟨10148894, by rfl⟩ : syracuseStep 13531859 = 20297789) B20297789
theorem B2112311 : Blo 1250443 2112311 := bstep (se 1 (by rfl) ⟨1584233, by rfl⟩ : syracuseStep 2112311 = 3168467) B3168467
theorem B7125839 : Blo 1250443 7125839 := bstep (se 1 (by rfl) ⟨5344379, by rfl⟩ : syracuseStep 7125839 = 10688759) B10688759
theorem B3169115 : Blo 1250443 3169115 := bstep (se 1 (by rfl) ⟨2376836, by rfl⟩ : syracuseStep 3169115 = 4753673) B4753673
theorem B1252187 : Blo 1250443 1252187 := bstep (se 1 (by rfl) ⟨939140, by rfl⟩ : syracuseStep 1252187 = 1878281) B1878281
theorem B2816873 : Blo 1250443 2816873 := bstep (se 2 (by rfl) ⟨1056327, by rfl⟩ : syracuseStep 2816873 = 2112655) B2112655
theorem B2816927 : Blo 1250443 2816927 := bstep (se 1 (by rfl) ⟨2112695, by rfl⟩ : syracuseStep 2816927 = 4225391) B4225391
theorem B1252255 : Blo 1250443 1252255 := bstep (se 1 (by rfl) ⟨939191, by rfl⟩ : syracuseStep 1252255 = 1878383) B1878383
theorem B20306861 : Blo 1250443 20306861 := bstep (se 3 (by rfl) ⟨3807536, by rfl⟩ : syracuseStep 20306861 = 7615073) B7615073
theorem B3562487 : Blo 1250443 3562487 := bstep (se 1 (by rfl) ⟨2671865, by rfl⟩ : syracuseStep 3562487 = 5343731) B5343731
theorem B4226039 : Blo 1250443 4226039 := bstep (se 1 (by rfl) ⟨3169529, by rfl⟩ : syracuseStep 4226039 = 6339059) B6339059
theorem B1252399 : Blo 1250443 1252399 := bstep (se 1 (by rfl) ⟨939299, by rfl⟩ : syracuseStep 1252399 = 1878599) B1878599
theorem B3210311 : Blo 1250443 3210311 := bstep (se 1 (by rfl) ⟨2407733, by rfl⟩ : syracuseStep 3210311 = 4815467) B4815467
theorem B1252423 : Blo 1250443 1252423 := bstep (se 1 (by rfl) ⟨939317, by rfl⟩ : syracuseStep 1252423 = 1878635) B1878635
theorem B9501785 : Blo 1250443 9501785 := bstep (se 2 (by rfl) ⟨3563169, by rfl⟩ : syracuseStep 9501785 = 7126339) B7126339
theorem B6331607 : Blo 1250443 6331607 := bstep (se 1 (by rfl) ⟨4748705, by rfl⟩ : syracuseStep 6331607 = 9497411) B9497411
theorem B6339869 : Blo 1250443 6339869 := bstep (se 3 (by rfl) ⟨1188725, by rfl⟩ : syracuseStep 6339869 = 2377451) B2377451
theorem B4226471 : Blo 1250443 4226471 := bstep (se 1 (by rfl) ⟨3169853, by rfl⟩ : syracuseStep 4226471 = 6339707) B6339707
theorem B2113087 : Blo 1250443 2113087 := bstep (se 1 (by rfl) ⟨1584815, by rfl⟩ : syracuseStep 2113087 = 3169631) B3169631
theorem B1408603 : Blo 1250443 1408603 := bstep (se 1 (by rfl) ⟨1056452, by rfl⟩ : syracuseStep 1408603 = 2112905) B2112905
theorem B3383009 : Blo 1250443 3383009 := bstep (se 2 (by rfl) ⟨1268628, by rfl⟩ : syracuseStep 3383009 = 2537257) B2537257
theorem B1875689 : Blo 1250443 1875689 := bstep (se 2 (by rfl) ⟨703383, by rfl⟩ : syracuseStep 1875689 = 1406767) B1406767
theorem B2375401 : Blo 1250443 2375401 := bstep (se 2 (by rfl) ⟨890775, by rfl⟩ : syracuseStep 2375401 = 1781551) B1781551
theorem B2817863 : Blo 1250443 2817863 := bstep (se 1 (by rfl) ⟨2113397, by rfl⟩ : syracuseStep 2817863 = 4226795) B4226795
theorem B4226903 : Blo 1250443 4226903 := bstep (se 1 (by rfl) ⟨3170177, by rfl⟩ : syracuseStep 4226903 = 6340355) B6340355
theorem B1875833 : Blo 1250443 1875833 := bstep (se 2 (by rfl) ⟨703437, by rfl⟩ : syracuseStep 1875833 = 1406875) B1406875
theorem B1408891 : Blo 1250443 1408891 := bstep (se 1 (by rfl) ⟨1056668, by rfl⟩ : syracuseStep 1408891 = 2113337) B2113337
theorem B4513661 : Blo 1250443 4513661 := bstep (se 3 (by rfl) ⟨846311, by rfl⟩ : syracuseStep 4513661 = 1692623) B1692623
theorem B1875935 : Blo 1250443 1875935 := bstep (se 1 (by rfl) ⟨1406951, by rfl⟩ : syracuseStep 1875935 = 2813903) B2813903
theorem B8560829 : Blo 1250443 8560829 := bstep (se 3 (by rfl) ⟨1605155, by rfl⟩ : syracuseStep 8560829 = 3210311) B3210311
theorem B1876175 : Blo 1250443 1876175 := bstep (se 1 (by rfl) ⟨1407131, by rfl⟩ : syracuseStep 1876175 = 2814263) B2814263
theorem B1876223 : Blo 1250443 1876223 := bstep (se 1 (by rfl) ⟨1407167, by rfl⟩ : syracuseStep 1876223 = 2814335) B2814335
theorem B4751743 : Blo 1250443 4751743 := bstep (se 1 (by rfl) ⟨3563807, by rfl⟩ : syracuseStep 4751743 = 7127615) B7127615
theorem B12837599 : Blo 1250443 12837599 := bstep (se 1 (by rfl) ⟨9628199, by rfl⟩ : syracuseStep 12837599 = 19256399) B19256399
theorem B4752215 : Blo 1250443 4752215 := bstep (se 1 (by rfl) ⟨3564161, by rfl⟩ : syracuseStep 4752215 = 7128323) B7128323
theorem B1877039 : Blo 1250443 1877039 := bstep (se 1 (by rfl) ⟨1407779, by rfl⟩ : syracuseStep 1877039 = 2815559) B2815559
theorem B5710907 : Blo 1250443 5710907 := bstep (se 1 (by rfl) ⟨4283180, by rfl⟩ : syracuseStep 5710907 = 8566361) B8566361
theorem B2851951 : Blo 1250443 2851951 := bstep (se 1 (by rfl) ⟨2138963, by rfl⟩ : syracuseStep 2851951 = 4277927) B4277927
theorem B1877159 : Blo 1250443 1877159 := bstep (se 1 (by rfl) ⟨1407869, by rfl⟩ : syracuseStep 1877159 = 2815739) B2815739
theorem B5342431 : Blo 1250443 5342431 := bstep (se 1 (by rfl) ⟨4006823, by rfl⟩ : syracuseStep 5342431 = 8013647) B8013647
theorem B12027203 : Blo 1250443 12027203 := bstep (se 1 (by rfl) ⟨9020402, by rfl⟩ : syracuseStep 12027203 = 18040805) B18040805
theorem B5490089 : Blo 1250443 5490089 := bstep (se 2 (by rfl) ⟨2058783, by rfl⟩ : syracuseStep 5490089 = 4117567) B4117567
theorem B1877531 : Blo 1250443 1877531 := bstep (se 1 (by rfl) ⟨1408148, by rfl⟩ : syracuseStep 1877531 = 2816297) B2816297
theorem B20285063 : Blo 1250443 20285063 := bstep (se 1 (by rfl) ⟨15213797, by rfl⟩ : syracuseStep 20285063 = 30427595) B30427595
theorem B9021239 : Blo 1250443 9021239 := bstep (se 1 (by rfl) ⟨6765929, by rfl⟩ : syracuseStep 9021239 = 13531859) B13531859
theorem B121866065 : Blo 1250443 121866065 := bstep (se 2 (by rfl) ⟨45699774, by rfl⟩ : syracuseStep 121866065 = 91399549) B91399549
theorem B1877915 : Blo 1250443 1877915 := bstep (se 1 (by rfl) ⟨1408436, by rfl⟩ : syracuseStep 1877915 = 2816873) B2816873
theorem B1877951 : Blo 1250443 1877951 := bstep (se 1 (by rfl) ⟨1408463, by rfl⟩ : syracuseStep 1877951 = 2816927) B2816927
theorem B6334523 : Blo 1250443 6334523 := bstep (se 1 (by rfl) ⟨4750892, by rfl⟩ : syracuseStep 6334523 = 9501785) B9501785
theorem B1878137 : Blo 1250443 1878137 := bstep (se 2 (by rfl) ⟨704301, by rfl⟩ : syracuseStep 1878137 = 1408603) B1408603
theorem B4221071 : Blo 1250443 4221071 := bstep (se 1 (by rfl) ⟨3165803, by rfl⟩ : syracuseStep 4221071 = 6331607) B6331607
theorem B2853025 : Blo 1250443 2853025 := bstep (se 2 (by rfl) ⟨1069884, by rfl⟩ : syracuseStep 2853025 = 2139769) B2139769
theorem B9505187 : Blo 1250443 9505187 := bstep (se 1 (by rfl) ⟨7128890, by rfl⟩ : syracuseStep 9505187 = 14257781) B14257781
theorem B2255339 : Blo 1250443 2255339 := bstep (se 1 (by rfl) ⟨1691504, by rfl⟩ : syracuseStep 2255339 = 3383009) B3383009
theorem B1878521 : Blo 1250443 1878521 := bstep (se 2 (by rfl) ⟨704445, by rfl⟩ : syracuseStep 1878521 = 1408891) B1408891
theorem B1878575 : Blo 1250443 1878575 := bstep (se 1 (by rfl) ⟨1408931, by rfl⟩ : syracuseStep 1878575 = 2817863) B2817863
theorem B3009107 : Blo 1250443 3009107 := bstep (se 1 (by rfl) ⟨2256830, by rfl⟩ : syracuseStep 3009107 = 4513661) B4513661
theorem B21375737 : Blo 1250443 21375737 := bstep (se 2 (by rfl) ⟨8015901, by rfl⟩ : syracuseStep 21375737 = 16031803) B16031803
theorem B67677079 : Blo 1250443 67677079 := bstep (se 1 (by rfl) ⟨50757809, by rfl⟩ : syracuseStep 67677079 = 101515619) B101515619
theorem B36072377 : Blo 1250443 36072377 := bstep (se 2 (by rfl) ⟨13527141, by rfl⟩ : syracuseStep 36072377 = 27054283) B27054283
theorem B2141495 : Blo 1250443 2141495 := bstep (se 1 (by rfl) ⟨1606121, by rfl⟩ : syracuseStep 2141495 = 3212243) B3212243
theorem B7122491 : Blo 1250443 7122491 := bstep (se 1 (by rfl) ⟨5341868, by rfl⟩ : syracuseStep 7122491 = 10683737) B10683737
theorem B6336143 : Blo 1250443 6336143 := bstep (se 1 (by rfl) ⟨4752107, by rfl⟩ : syracuseStep 6336143 = 9504215) B9504215
theorem B2813687 : Blo 1250443 2813687 := bstep (se 1 (by rfl) ⟨2110265, by rfl⟩ : syracuseStep 2813687 = 4220531) B4220531
theorem B2813759 : Blo 1250443 2813759 := bstep (se 1 (by rfl) ⟨2110319, by rfl⟩ : syracuseStep 2813759 = 4220639) B4220639
theorem B2813867 : Blo 1250443 2813867 := bstep (se 1 (by rfl) ⟨2110400, by rfl⟩ : syracuseStep 2813867 = 4220801) B4220801
theorem B2814227 : Blo 1250443 2814227 := bstep (se 1 (by rfl) ⟨2110670, by rfl⟩ : syracuseStep 2814227 = 4221341) B4221341
theorem B2814407 : Blo 1250443 2814407 := bstep (se 1 (by rfl) ⟨2110805, by rfl⟩ : syracuseStep 2814407 = 4221611) B4221611
theorem B10687049 : Blo 1250443 10687049 := bstep (se 2 (by rfl) ⟨4007643, by rfl⟩ : syracuseStep 10687049 = 8015287) B8015287
theorem B4747855 : Blo 1250443 4747855 := bstep (se 1 (by rfl) ⟨3560891, by rfl⟩ : syracuseStep 4747855 = 7121783) B7121783
theorem B13537907 : Blo 1250443 13537907 := bstep (se 1 (by rfl) ⟨10153430, by rfl⟩ : syracuseStep 13537907 = 20306861) B20306861
theorem B4223663 : Blo 1250443 4223663 := bstep (se 1 (by rfl) ⟨3167747, by rfl⟩ : syracuseStep 4223663 = 6335495) B6335495
theorem B10842839 : Blo 1250443 10842839 := bstep (se 1 (by rfl) ⟨8132129, by rfl⟩ : syracuseStep 10842839 = 16264259) B16264259
theorem B9507617 : Blo 1250443 9507617 := bstep (se 2 (by rfl) ⟨3565356, by rfl⟩ : syracuseStep 9507617 = 7130713) B7130713
theorem B2814767 : Blo 1250443 2814767 := bstep (se 1 (by rfl) ⟨2111075, by rfl⟩ : syracuseStep 2814767 = 4222151) B4222151
theorem B2814857 : Blo 1250443 2814857 := bstep (se 2 (by rfl) ⟨1055571, by rfl⟩ : syracuseStep 2814857 = 2111143) B2111143
theorem B3167201 : Blo 1250443 3167201 := bstep (se 2 (by rfl) ⟨1187700, by rfl⟩ : syracuseStep 3167201 = 2375401) B2375401
theorem B41718833 : Blo 1250443 41718833 := bstep (se 2 (by rfl) ⟨15644562, by rfl⟩ : syracuseStep 41718833 = 31289125) B31289125
theorem B4011079 : Blo 1250443 4011079 := bstep (se 1 (by rfl) ⟨3008309, by rfl⟩ : syracuseStep 4011079 = 6016619) B6016619
theorem B1250459 : Blo 1250443 1250459 := bstep (se 1 (by rfl) ⟨937844, by rfl⟩ : syracuseStep 1250459 = 1875689) B1875689
theorem B13522085 : Blo 1250443 13522085 := bstep (se 4 (by rfl) ⟨1267695, by rfl⟩ : syracuseStep 13522085 = 2535391) B2535391
theorem B1250555 : Blo 1250443 1250555 := bstep (se 1 (by rfl) ⟨937916, by rfl⟩ : syracuseStep 1250555 = 1875833) B1875833
theorem B1250623 : Blo 1250443 1250623 := bstep (se 1 (by rfl) ⟨937967, by rfl⟩ : syracuseStep 1250623 = 1875935) B1875935
theorem B7615853 : Blo 1250443 7615853 := bstep (se 3 (by rfl) ⟨1427972, by rfl⟩ : syracuseStep 7615853 = 2855945) B2855945
theorem B2004335 : Blo 1250443 2004335 := bstep (se 1 (by rfl) ⟨1503251, by rfl⟩ : syracuseStep 2004335 = 3006503) B3006503
theorem B1250791 : Blo 1250443 1250791 := bstep (se 1 (by rfl) ⟨938093, by rfl⟩ : syracuseStep 1250791 = 1876187) B1876187
theorem B1250799 : Blo 1250443 1250799 := bstep (se 1 (by rfl) ⟨938099, by rfl⟩ : syracuseStep 1250799 = 1876199) B1876199
theorem B2004463 : Blo 1250443 2004463 := bstep (se 1 (by rfl) ⟨1503347, by rfl⟩ : syracuseStep 2004463 = 3006695) B3006695
theorem B1250907 : Blo 1250443 1250907 := bstep (se 1 (by rfl) ⟨938180, by rfl⟩ : syracuseStep 1250907 = 1876361) B1876361
theorem B3561097 : Blo 1250443 3561097 := bstep (se 2 (by rfl) ⟨1335411, by rfl⟩ : syracuseStep 3561097 = 2670823) B2670823
theorem B2815631 : Blo 1250443 2815631 := bstep (se 1 (by rfl) ⟨2111723, by rfl⟩ : syracuseStep 2815631 = 4223447) B4223447
theorem B1250971 : Blo 1250443 1250971 := bstep (se 1 (by rfl) ⟨938228, by rfl⟩ : syracuseStep 1250971 = 1876457) B1876457
theorem B18290393 : Blo 1250443 18290393 := bstep (se 2 (by rfl) ⟨6858897, by rfl⟩ : syracuseStep 18290393 = 13717795) B13717795
theorem B2815721 : Blo 1250443 2815721 := bstep (se 2 (by rfl) ⟨1055895, by rfl⟩ : syracuseStep 2815721 = 2111791) B2111791
theorem B1251055 : Blo 1250443 1251055 := bstep (se 1 (by rfl) ⟨938291, by rfl⟩ : syracuseStep 1251055 = 1876583) B1876583
theorem B5347079 : Blo 1250443 5347079 := bstep (se 1 (by rfl) ⟨4010309, by rfl⟩ : syracuseStep 5347079 = 8020619) B8020619
theorem B3168031 : Blo 1250443 3168031 := bstep (se 1 (by rfl) ⟨2376023, by rfl⟩ : syracuseStep 3168031 = 4752047) B4752047
theorem B10696481 : Blo 1250443 10696481 := bstep (se 2 (by rfl) ⟨4011180, by rfl⟩ : syracuseStep 10696481 = 8022361) B8022361
theorem B22837049 : Blo 1250443 22837049 := bstep (se 2 (by rfl) ⟨8563893, by rfl⟩ : syracuseStep 22837049 = 17127787) B17127787
theorem B1251143 : Blo 1250443 1251143 := bstep (se 1 (by rfl) ⟨938357, by rfl⟩ : syracuseStep 1251143 = 1876715) B1876715
theorem B1251163 : Blo 1250443 1251163 := bstep (se 1 (by rfl) ⟨938372, by rfl⟩ : syracuseStep 1251163 = 1876745) B1876745
theorem B1251231 : Blo 1250443 1251231 := bstep (se 1 (by rfl) ⟨938423, by rfl⟩ : syracuseStep 1251231 = 1876847) B1876847
theorem B8558531 : Blo 1250443 8558531 := bstep (se 1 (by rfl) ⟨6418898, by rfl⟩ : syracuseStep 8558531 = 12837797) B12837797
theorem B1251399 : Blo 1250443 1251399 := bstep (se 1 (by rfl) ⟨938549, by rfl⟩ : syracuseStep 1251399 = 1877099) B1877099
theorem B10696859 : Blo 1250443 10696859 := bstep (se 1 (by rfl) ⟨8022644, by rfl⟩ : syracuseStep 10696859 = 16045289) B16045289
theorem B1251559 : Blo 1250443 1251559 := bstep (se 1 (by rfl) ⟨938669, by rfl⟩ : syracuseStep 1251559 = 1877339) B1877339
theorem B6764957 : Blo 1250443 6764957 := bstep (se 3 (by rfl) ⟨1268429, by rfl⟩ : syracuseStep 6764957 = 2536859) B2536859
theorem B1251743 : Blo 1250443 1251743 := bstep (se 1 (by rfl) ⟨938807, by rfl⟩ : syracuseStep 1251743 = 1877615) B1877615
theorem B1251791 : Blo 1250443 1251791 := bstep (se 1 (by rfl) ⟨938843, by rfl⟩ : syracuseStep 1251791 = 1877687) B1877687
theorem B1251815 : Blo 1250443 1251815 := bstep (se 1 (by rfl) ⟨938861, by rfl⟩ : syracuseStep 1251815 = 1877723) B1877723
theorem B2112041 : Blo 1250443 2112041 := bstep (se 2 (by rfl) ⟨792015, by rfl⟩ : syracuseStep 2112041 = 1584031) B1584031
theorem B2816603 : Blo 1250443 2816603 := bstep (se 1 (by rfl) ⟨2112452, by rfl⟩ : syracuseStep 2816603 = 4224905) B4224905
theorem B1251931 : Blo 1250443 1251931 := bstep (se 1 (by rfl) ⟨938948, by rfl⟩ : syracuseStep 1251931 = 1877897) B1877897
theorem B1251999 : Blo 1250443 1251999 := bstep (se 1 (by rfl) ⟨938999, by rfl⟩ : syracuseStep 1251999 = 1877999) B1877999
theorem B2816747 : Blo 1250443 2816747 := bstep (se 1 (by rfl) ⟨2112560, by rfl⟩ : syracuseStep 2816747 = 4225121) B4225121
theorem B3382013 : Blo 1250443 3382013 := bstep (se 3 (by rfl) ⟨634127, by rfl⟩ : syracuseStep 3382013 = 1268255) B1268255
theorem B1252167 : Blo 1250443 1252167 := bstep (se 1 (by rfl) ⟨939125, by rfl⟩ : syracuseStep 1252167 = 1878251) B1878251
theorem B1252207 : Blo 1250443 1252207 := bstep (se 1 (by rfl) ⟨939155, by rfl⟩ : syracuseStep 1252207 = 1878311) B1878311
theorem B1252263 : Blo 1250443 1252263 := bstep (se 1 (by rfl) ⟨939197, by rfl⟩ : syracuseStep 1252263 = 1878395) B1878395
theorem B21380111 : Blo 1250443 21380111 := bstep (se 1 (by rfl) ⟨16035083, by rfl⟩ : syracuseStep 21380111 = 32070167) B32070167
theorem B1252443 : Blo 1250443 1252443 := bstep (se 1 (by rfl) ⟨939332, by rfl⟩ : syracuseStep 1252443 = 1878665) B1878665
theorem B3382393 : Blo 1250443 3382393 := bstep (se 2 (by rfl) ⟨1268397, by rfl⟩ : syracuseStep 3382393 = 2536795) B2536795
theorem B6765713 : Blo 1250443 6765713 := bstep (se 2 (by rfl) ⟨2537142, by rfl⟩ : syracuseStep 6765713 = 5074285) B5074285
theorem B1408207 : Blo 1250443 1408207 := bstep (se 1 (by rfl) ⟨1056155, by rfl⟩ : syracuseStep 1408207 = 2112311) B2112311
theorem B4750559 : Blo 1250443 4750559 := bstep (se 1 (by rfl) ⟨3562919, by rfl⟩ : syracuseStep 4750559 = 7125839) B7125839
theorem B2112743 : Blo 1250443 2112743 := bstep (se 1 (by rfl) ⟨1584557, by rfl⟩ : syracuseStep 2112743 = 3169115) B3169115
theorem B2374991 : Blo 1250443 2374991 := bstep (se 1 (by rfl) ⟨1781243, by rfl⟩ : syracuseStep 2374991 = 3562487) B3562487
theorem B2817359 : Blo 1250443 2817359 := bstep (se 1 (by rfl) ⟨2113019, by rfl⟩ : syracuseStep 2817359 = 4226039) B4226039
theorem B2817449 : Blo 1250443 2817449 := bstep (se 2 (by rfl) ⟨1056543, by rfl⟩ : syracuseStep 2817449 = 2113087) B2113087
theorem B12033467 : Blo 1250443 12033467 := bstep (se 1 (by rfl) ⟨9025100, by rfl⟩ : syracuseStep 12033467 = 18050201) B18050201
theorem B4226579 : Blo 1250443 4226579 := bstep (se 1 (by rfl) ⟨3169934, by rfl⟩ : syracuseStep 4226579 = 6339869) B6339869
theorem B21388859 : Blo 1250443 21388859 := bstep (se 1 (by rfl) ⟨16041644, by rfl⟩ : syracuseStep 21388859 = 32083289) B32083289
theorem B2817647 : Blo 1250443 2817647 := bstep (se 1 (by rfl) ⟨2113235, by rfl⟩ : syracuseStep 2817647 = 4226471) B4226471
theorem B2711161 : Blo 1250443 2711161 := bstep (se 2 (by rfl) ⟨1016685, by rfl⟩ : syracuseStep 2711161 = 2033371) B2033371
theorem B1875743 : Blo 1250443 1875743 := bstep (se 1 (by rfl) ⟨1406807, by rfl⟩ : syracuseStep 1875743 = 2813615) B2813615
theorem B2817935 : Blo 1250443 2817935 := bstep (se 1 (by rfl) ⟨2113451, by rfl⟩ : syracuseStep 2817935 = 4226903) B4226903
theorem B2744219 : Blo 1250443 2744219 := bstep (se 1 (by rfl) ⟨2058164, by rfl⟩ : syracuseStep 2744219 = 4116329) B4116329
theorem B1876151 : Blo 1250443 1876151 := bstep (se 1 (by rfl) ⟨1407113, by rfl⟩ : syracuseStep 1876151 = 2814227) B2814227
theorem B1876271 : Blo 1250443 1876271 := bstep (se 1 (by rfl) ⟨1407203, by rfl⟩ : syracuseStep 1876271 = 2814407) B2814407
theorem B1876511 : Blo 1250443 1876511 := bstep (se 1 (by rfl) ⟨1407383, by rfl⟩ : syracuseStep 1876511 = 2814767) B2814767
theorem B1876571 : Blo 1250443 1876571 := bstep (se 1 (by rfl) ⟨1407428, by rfl⟩ : syracuseStep 1876571 = 2814857) B2814857
theorem B27812555 : Blo 1250443 27812555 := bstep (se 1 (by rfl) ⟨20859416, by rfl⟩ : syracuseStep 27812555 = 41718833) B41718833
theorem B1336223 : Blo 1250443 1336223 := bstep (se 1 (by rfl) ⟨1002167, by rfl⟩ : syracuseStep 1336223 = 2004335) B2004335
theorem B1877087 : Blo 1250443 1877087 := bstep (se 1 (by rfl) ⟨1407815, by rfl⟩ : syracuseStep 1877087 = 2815631) B2815631
theorem B1877147 : Blo 1250443 1877147 := bstep (se 1 (by rfl) ⟨1407860, by rfl⟩ : syracuseStep 1877147 = 2815721) B2815721
theorem B3564719 : Blo 1250443 3564719 := bstep (se 1 (by rfl) ⟨2673539, by rfl⟩ : syracuseStep 3564719 = 5347079) B5347079
theorem B90236105 : Blo 1250443 90236105 := bstep (se 2 (by rfl) ⟨33838539, by rfl⟩ : syracuseStep 90236105 = 67677079) B67677079
theorem B6014159 : Blo 1250443 6014159 := bstep (se 1 (by rfl) ⟨4510619, by rfl⟩ : syracuseStep 6014159 = 9021239) B9021239
theorem B3802601 : Blo 1250443 3802601 := bstep (se 2 (by rfl) ⟨1425975, by rfl⟩ : syracuseStep 3802601 = 2851951) B2851951
theorem B1877609 : Blo 1250443 1877609 := bstep (se 2 (by rfl) ⟨704103, by rfl⟩ : syracuseStep 1877609 = 1408207) B1408207
theorem B1877735 : Blo 1250443 1877735 := bstep (se 1 (by rfl) ⟨1408301, by rfl⟩ : syracuseStep 1877735 = 2816603) B2816603
theorem B1877831 : Blo 1250443 1877831 := bstep (se 1 (by rfl) ⟨1408373, by rfl⟩ : syracuseStep 1877831 = 2816747) B2816747
theorem B2672617 : Blo 1250443 2672617 := bstep (se 2 (by rfl) ⟨1002231, by rfl⟩ : syracuseStep 2672617 = 2004463) B2004463
theorem B3614881 : Blo 1250443 3614881 := bstep (se 2 (by rfl) ⟨1355580, by rfl⟩ : syracuseStep 3614881 = 2711161) B2711161
theorem B1427663 : Blo 1250443 1427663 := bstep (se 1 (by rfl) ⟨1070747, by rfl⟩ : syracuseStep 1427663 = 2141495) B2141495
theorem B1583327 : Blo 1250443 1583327 := bstep (se 1 (by rfl) ⟨1187495, by rfl⟩ : syracuseStep 1583327 = 2374991) B2374991
theorem B1878239 : Blo 1250443 1878239 := bstep (se 1 (by rfl) ⟨1408679, by rfl⟩ : syracuseStep 1878239 = 2817359) B2817359
theorem B1878299 : Blo 1250443 1878299 := bstep (se 1 (by rfl) ⟨1408724, by rfl⟩ : syracuseStep 1878299 = 2817449) B2817449
theorem B8022311 : Blo 1250443 8022311 := bstep (se 1 (by rfl) ⟨6016733, by rfl⟩ : syracuseStep 8022311 = 12033467) B12033467
theorem B1878431 : Blo 1250443 1878431 := bstep (se 1 (by rfl) ⟨1408823, by rfl⟩ : syracuseStep 1878431 = 2817647) B2817647
theorem B1878623 : Blo 1250443 1878623 := bstep (se 1 (by rfl) ⟨1408967, by rfl⟩ : syracuseStep 1878623 = 2817935) B2817935
theorem B1829479 : Blo 1250443 1829479 := bstep (se 1 (by rfl) ⟨1372109, by rfl⟩ : syracuseStep 1829479 = 2744219) B2744219
theorem B7228559 : Blo 1250443 7228559 := bstep (se 1 (by rfl) ⟨5421419, by rfl⟩ : syracuseStep 7228559 = 10842839) B10842839
theorem B6335657 : Blo 1250443 6335657 := bstep (se 2 (by rfl) ⟨2375871, by rfl⟩ : syracuseStep 6335657 = 4751743) B4751743
theorem B9014723 : Blo 1250443 9014723 := bstep (se 1 (by rfl) ⟨6761042, by rfl⟩ : syracuseStep 9014723 = 13522085) B13522085
theorem B15216133 : Blo 1250443 15216133 := bstep (se 4 (by rfl) ⟨1426512, by rfl⟩ : syracuseStep 15216133 = 2853025) B2853025
theorem B12193595 : Blo 1250443 12193595 := bstep (se 1 (by rfl) ⟨9145196, by rfl⟩ : syracuseStep 12193595 = 18290393) B18290393
theorem B7130987 : Blo 1250443 7130987 := bstep (se 1 (by rfl) ⟨5348240, by rfl⟩ : syracuseStep 7130987 = 10696481) B10696481
theorem B15224699 : Blo 1250443 15224699 := bstep (se 1 (by rfl) ⟨11418524, by rfl⟩ : syracuseStep 15224699 = 22837049) B22837049
theorem B81244043 : Blo 1250443 81244043 := bstep (se 1 (by rfl) ⟨60933032, by rfl⟩ : syracuseStep 81244043 = 121866065) B121866065
theorem B5705687 : Blo 1250443 5705687 := bstep (se 1 (by rfl) ⟨4279265, by rfl⟩ : syracuseStep 5705687 = 8558531) B8558531
theorem B4223015 : Blo 1250443 4223015 := bstep (se 1 (by rfl) ⟨3167261, by rfl⟩ : syracuseStep 4223015 = 6334523) B6334523
theorem B2814047 : Blo 1250443 2814047 := bstep (se 1 (by rfl) ⟨2110535, by rfl⟩ : syracuseStep 2814047 = 4221071) B4221071
theorem B7131239 : Blo 1250443 7131239 := bstep (se 1 (by rfl) ⟨5348429, by rfl⟩ : syracuseStep 7131239 = 10696859) B10696859
theorem B4509857 : Blo 1250443 4509857 := bstep (se 2 (by rfl) ⟨1691196, by rfl⟩ : syracuseStep 4509857 = 3382393) B3382393
theorem B8024285 : Blo 1250443 8024285 := bstep (se 3 (by rfl) ⟨1504553, by rfl⟩ : syracuseStep 8024285 = 3009107) B3009107
theorem B4509971 : Blo 1250443 4509971 := bstep (se 1 (by rfl) ⟨3382478, by rfl⟩ : syracuseStep 4509971 = 6764957) B6764957
theorem B6336791 : Blo 1250443 6336791 := bstep (se 1 (by rfl) ⟨4752593, by rfl⟩ : syracuseStep 6336791 = 9505187) B9505187
theorem B7123241 : Blo 1250443 7123241 := bstep (se 2 (by rfl) ⟨2671215, by rfl⟩ : syracuseStep 7123241 = 5342431) B5342431
theorem B1503559 : Blo 1250443 1503559 := bstep (se 1 (by rfl) ⟨1127669, by rfl⟩ : syracuseStep 1503559 = 2255339) B2255339
theorem B14250491 : Blo 1250443 14250491 := bstep (se 1 (by rfl) ⟨10687868, by rfl⟩ : syracuseStep 14250491 = 21375737) B21375737
theorem B24048251 : Blo 1250443 24048251 := bstep (se 1 (by rfl) ⟨18036188, by rfl⟩ : syracuseStep 24048251 = 36072377) B36072377
theorem B4510475 : Blo 1250443 4510475 := bstep (se 1 (by rfl) ⟨3382856, by rfl⟩ : syracuseStep 4510475 = 6765713) B6765713
theorem B3167039 : Blo 1250443 3167039 := bstep (se 1 (by rfl) ⟨2375279, by rfl⟩ : syracuseStep 3167039 = 4750559) B4750559
theorem B4748129 : Blo 1250443 4748129 := bstep (se 2 (by rfl) ⟨1780548, by rfl⟩ : syracuseStep 4748129 = 3561097) B3561097
theorem B4748327 : Blo 1250443 4748327 := bstep (se 1 (by rfl) ⟨3561245, by rfl⟩ : syracuseStep 4748327 = 7122491) B7122491
theorem B14259239 : Blo 1250443 14259239 := bstep (se 1 (by rfl) ⟨10694429, by rfl⟩ : syracuseStep 14259239 = 21388859) B21388859
theorem B4224041 : Blo 1250443 4224041 := bstep (se 2 (by rfl) ⟨1584015, by rfl⟩ : syracuseStep 4224041 = 3168031) B3168031
theorem B4224095 : Blo 1250443 4224095 := bstep (se 1 (by rfl) ⟨3168071, by rfl⟩ : syracuseStep 4224095 = 6336143) B6336143
theorem B1250495 : Blo 1250443 1250495 := bstep (se 1 (by rfl) ⟨937871, by rfl⟩ : syracuseStep 1250495 = 1875743) B1875743
theorem B1250783 : Blo 1250443 1250783 := bstep (se 1 (by rfl) ⟨938087, by rfl⟩ : syracuseStep 1250783 = 1876175) B1876175
theorem B1250815 : Blo 1250443 1250815 := bstep (se 1 (by rfl) ⟨938111, by rfl⟩ : syracuseStep 1250815 = 1876223) B1876223
theorem B7124699 : Blo 1250443 7124699 := bstep (se 1 (by rfl) ⟨5343524, by rfl⟩ : syracuseStep 7124699 = 10687049) B10687049
theorem B9025271 : Blo 1250443 9025271 := bstep (se 1 (by rfl) ⟨6768953, by rfl⟩ : syracuseStep 9025271 = 13537907) B13537907
theorem B2815775 : Blo 1250443 2815775 := bstep (se 1 (by rfl) ⟨2111831, by rfl⟩ : syracuseStep 2815775 = 4223663) B4223663
theorem B8558399 : Blo 1250443 8558399 := bstep (se 1 (by rfl) ⟨6418799, by rfl⟩ : syracuseStep 8558399 = 12837599) B12837599
theorem B22828877 : Blo 1250443 22828877 := bstep (se 3 (by rfl) ⟨4280414, by rfl⟩ : syracuseStep 22828877 = 8560829) B8560829
theorem B6338411 : Blo 1250443 6338411 := bstep (se 1 (by rfl) ⟨4753808, by rfl⟩ : syracuseStep 6338411 = 9507617) B9507617
theorem B3168143 : Blo 1250443 3168143 := bstep (se 1 (by rfl) ⟨2376107, by rfl⟩ : syracuseStep 3168143 = 4752215) B4752215
theorem B2111467 : Blo 1250443 2111467 := bstep (se 1 (by rfl) ⟨1583600, by rfl⟩ : syracuseStep 2111467 = 3167201) B3167201
theorem B1251359 : Blo 1250443 1251359 := bstep (se 1 (by rfl) ⟨938519, by rfl⟩ : syracuseStep 1251359 = 1877039) B1877039
theorem B3807271 : Blo 1250443 3807271 := bstep (se 1 (by rfl) ⟨2855453, by rfl⟩ : syracuseStep 3807271 = 5710907) B5710907
theorem B6330473 : Blo 1250443 6330473 := bstep (se 2 (by rfl) ⟨2373927, by rfl⟩ : syracuseStep 6330473 = 4747855) B4747855
theorem B1251439 : Blo 1250443 1251439 := bstep (se 1 (by rfl) ⟨938579, by rfl⟩ : syracuseStep 1251439 = 1877159) B1877159
theorem B8018135 : Blo 1250443 8018135 := bstep (se 1 (by rfl) ⟨6013601, by rfl⟩ : syracuseStep 8018135 = 12027203) B12027203
theorem B5077235 : Blo 1250443 5077235 := bstep (se 1 (by rfl) ⟨3807926, by rfl⟩ : syracuseStep 5077235 = 7615853) B7615853
theorem B3660059 : Blo 1250443 3660059 := bstep (se 1 (by rfl) ⟨2745044, by rfl⟩ : syracuseStep 3660059 = 5490089) B5490089
theorem B1251687 : Blo 1250443 1251687 := bstep (se 1 (by rfl) ⟨938765, by rfl⟩ : syracuseStep 1251687 = 1877531) B1877531
theorem B13523375 : Blo 1250443 13523375 := bstep (se 1 (by rfl) ⟨10142531, by rfl⟩ : syracuseStep 13523375 = 20285063) B20285063
theorem B1251943 : Blo 1250443 1251943 := bstep (se 1 (by rfl) ⟨938957, by rfl⟩ : syracuseStep 1251943 = 1877915) B1877915
theorem B1251967 : Blo 1250443 1251967 := bstep (se 1 (by rfl) ⟨938975, by rfl⟩ : syracuseStep 1251967 = 1877951) B1877951
theorem B1252091 : Blo 1250443 1252091 := bstep (se 1 (by rfl) ⟨939068, by rfl⟩ : syracuseStep 1252091 = 1878137) B1878137
theorem B5348105 : Blo 1250443 5348105 := bstep (se 2 (by rfl) ⟨2005539, by rfl⟩ : syracuseStep 5348105 = 4011079) B4011079
theorem B1252347 : Blo 1250443 1252347 := bstep (se 1 (by rfl) ⟨939260, by rfl⟩ : syracuseStep 1252347 = 1878521) B1878521
theorem B1408027 : Blo 1250443 1408027 := bstep (se 1 (by rfl) ⟨1056020, by rfl⟩ : syracuseStep 1408027 = 2112041) B2112041
theorem B1252383 : Blo 1250443 1252383 := bstep (se 1 (by rfl) ⟨939287, by rfl⟩ : syracuseStep 1252383 = 1878575) B1878575
theorem B9018701 : Blo 1250443 9018701 := bstep (se 3 (by rfl) ⟨1691006, by rfl⟩ : syracuseStep 9018701 = 3382013) B3382013
theorem B14253407 : Blo 1250443 14253407 := bstep (se 1 (by rfl) ⟨10690055, by rfl⟩ : syracuseStep 14253407 = 21380111) B21380111
theorem B1408495 : Blo 1250443 1408495 := bstep (se 1 (by rfl) ⟨1056371, by rfl⟩ : syracuseStep 1408495 = 2112743) B2112743
theorem B2817719 : Blo 1250443 2817719 := bstep (se 1 (by rfl) ⟨2113289, by rfl⟩ : syracuseStep 2817719 = 4226579) B4226579
theorem B1875791 : Blo 1250443 1875791 := bstep (se 1 (by rfl) ⟨1406843, by rfl⟩ : syracuseStep 1875791 = 2813687) B2813687
theorem B1875839 : Blo 1250443 1875839 := bstep (se 1 (by rfl) ⟨1406879, by rfl⟩ : syracuseStep 1875839 = 2813759) B2813759
theorem B1875911 : Blo 1250443 1875911 := bstep (se 1 (by rfl) ⟨1406933, by rfl⟩ : syracuseStep 1875911 = 2813867) B2813867
theorem B1876031 : Blo 1250443 1876031 := bstep (se 1 (by rfl) ⟨1407023, by rfl⟩ : syracuseStep 1876031 = 2814047) B2814047
theorem B3006571 : Blo 1250443 3006571 := bstep (se 1 (by rfl) ⟨2254928, by rfl⟩ : syracuseStep 3006571 = 4509857) B4509857
theorem B5349523 : Blo 1250443 5349523 := bstep (se 1 (by rfl) ⟨4012142, by rfl⟩ : syracuseStep 5349523 = 8024285) B8024285
theorem B3006647 : Blo 1250443 3006647 := bstep (se 1 (by rfl) ⟨2254985, by rfl⟩ : syracuseStep 3006647 = 4509971) B4509971
theorem B19276157 : Blo 1250443 19276157 := bstep (se 3 (by rfl) ⟨3614279, by rfl⟩ : syracuseStep 19276157 = 7228559) B7228559
theorem B16032167 : Blo 1250443 16032167 := bstep (se 1 (by rfl) ⟨12024125, by rfl⟩ : syracuseStep 16032167 = 24048251) B24048251
theorem B3006983 : Blo 1250443 3006983 := bstep (se 1 (by rfl) ⟨2255237, by rfl⟩ : syracuseStep 3006983 = 4510475) B4510475
theorem B2376479 : Blo 1250443 2376479 := bstep (se 1 (by rfl) ⟨1782359, by rfl⟩ : syracuseStep 2376479 = 3564719) B3564719
theorem B36062333 : Blo 1250443 36062333 := bstep (se 3 (by rfl) ⟨6761687, by rfl⟩ : syracuseStep 36062333 = 13523375) B13523375
theorem B1877183 : Blo 1250443 1877183 := bstep (se 1 (by rfl) ⟨1407887, by rfl⟩ : syracuseStep 1877183 = 2815775) B2815775
theorem B1877369 : Blo 1250443 1877369 := bstep (se 2 (by rfl) ⟨704013, by rfl⟩ : syracuseStep 1877369 = 1408027) B1408027
theorem B4220315 : Blo 1250443 4220315 := bstep (se 1 (by rfl) ⟨3165236, by rfl⟩ : syracuseStep 4220315 = 6330473) B6330473
theorem B3384823 : Blo 1250443 3384823 := bstep (se 1 (by rfl) ⟨2538617, by rfl⟩ : syracuseStep 3384823 = 5077235) B5077235
theorem B3565403 : Blo 1250443 3565403 := bstep (se 1 (by rfl) ⟨2674052, by rfl⟩ : syracuseStep 3565403 = 5348105) B5348105
theorem B1877993 : Blo 1250443 1877993 := bstep (se 2 (by rfl) ⟨704247, by rfl⟩ : syracuseStep 1877993 = 1408495) B1408495
theorem B1878479 : Blo 1250443 1878479 := bstep (se 1 (by rfl) ⟨1408859, by rfl⟩ : syracuseStep 1878479 = 2817719) B2817719
theorem B8129063 : Blo 1250443 8129063 := bstep (se 1 (by rfl) ⟨6096797, by rfl⟩ : syracuseStep 8129063 = 12193595) B12193595
theorem B15215165 : Blo 1250443 15215165 := bstep (se 3 (by rfl) ⟨2852843, by rfl⟩ : syracuseStep 15215165 = 5705687) B5705687
theorem B4753991 : Blo 1250443 4753991 := bstep (se 1 (by rfl) ⟨3565493, by rfl⟩ : syracuseStep 4753991 = 7130987) B7130987
theorem B4754159 : Blo 1250443 4754159 := bstep (se 1 (by rfl) ⟨3565619, by rfl⟩ : syracuseStep 4754159 = 7131239) B7131239
theorem B4819841 : Blo 1250443 4819841 := bstep (se 2 (by rfl) ⟨1807440, by rfl⟩ : syracuseStep 4819841 = 3614881) B3614881
theorem B18541703 : Blo 1250443 18541703 := bstep (se 1 (by rfl) ⟨13906277, by rfl⟩ : syracuseStep 18541703 = 27812555) B27812555
theorem B3165419 : Blo 1250443 3165419 := bstep (se 1 (by rfl) ⟨2374064, by rfl⟩ : syracuseStep 3165419 = 4748129) B4748129
theorem B4222205 : Blo 1250443 4222205 := bstep (se 3 (by rfl) ⟨791663, by rfl⟩ : syracuseStep 4222205 = 1583327) B1583327
theorem B3165551 : Blo 1250443 3165551 := bstep (se 1 (by rfl) ⟨2374163, by rfl⟩ : syracuseStep 3165551 = 4748327) B4748327
theorem B9506159 : Blo 1250443 9506159 := bstep (se 1 (by rfl) ⟨7129619, by rfl⟩ : syracuseStep 9506159 = 14259239) B14259239
theorem B60157403 : Blo 1250443 60157403 := bstep (se 1 (by rfl) ⟨45118052, by rfl⟩ : syracuseStep 60157403 = 90236105) B90236105
theorem B4009439 : Blo 1250443 4009439 := bstep (se 1 (by rfl) ⟨3007079, by rfl⟩ : syracuseStep 4009439 = 6014159) B6014159
theorem B2535067 : Blo 1250443 2535067 := bstep (se 1 (by rfl) ⟨1901300, by rfl⟩ : syracuseStep 2535067 = 3802601) B3802601
theorem B6016847 : Blo 1250443 6016847 := bstep (se 1 (by rfl) ⟨4512635, by rfl⟩ : syracuseStep 6016847 = 9025271) B9025271
theorem B5705599 : Blo 1250443 5705599 := bstep (se 1 (by rfl) ⟨4279199, by rfl⟩ : syracuseStep 5705599 = 8558399) B8558399
theorem B5345423 : Blo 1250443 5345423 := bstep (se 1 (by rfl) ⟨4009067, by rfl⟩ : syracuseStep 5345423 = 8018135) B8018135
theorem B20288177 : Blo 1250443 20288177 := bstep (se 2 (by rfl) ⟨7608066, by rfl⟩ : syracuseStep 20288177 = 15216133) B15216133
theorem B4223771 : Blo 1250443 4223771 := bstep (se 1 (by rfl) ⟨3167828, by rfl⟩ : syracuseStep 4223771 = 6335657) B6335657
theorem B6009815 : Blo 1250443 6009815 := bstep (se 1 (by rfl) ⟨4507361, by rfl⟩ : syracuseStep 6009815 = 9014723) B9014723
theorem B1250527 : Blo 1250443 1250527 := bstep (se 1 (by rfl) ⟨937895, by rfl⟩ : syracuseStep 1250527 = 1875791) B1875791
theorem B1250559 : Blo 1250443 1250559 := bstep (se 1 (by rfl) ⟨937919, by rfl⟩ : syracuseStep 1250559 = 1875839) B1875839
theorem B54162695 : Blo 1250443 54162695 := bstep (se 1 (by rfl) ⟨40622021, by rfl⟩ : syracuseStep 54162695 = 81244043) B81244043
theorem B1250607 : Blo 1250443 1250607 := bstep (se 1 (by rfl) ⟨937955, by rfl⟩ : syracuseStep 1250607 = 1875911) B1875911
theorem B2815289 : Blo 1250443 2815289 := bstep (se 2 (by rfl) ⟨1055733, by rfl⟩ : syracuseStep 2815289 = 2111467) B2111467
theorem B2815343 : Blo 1250443 2815343 := bstep (se 1 (by rfl) ⟨2111507, by rfl⟩ : syracuseStep 2815343 = 4223015) B4223015
theorem B5076361 : Blo 1250443 5076361 := bstep (se 2 (by rfl) ⟨1903635, by rfl⟩ : syracuseStep 5076361 = 3807271) B3807271
theorem B1250767 : Blo 1250443 1250767 := bstep (se 1 (by rfl) ⟨938075, by rfl⟩ : syracuseStep 1250767 = 1876151) B1876151
theorem B4224527 : Blo 1250443 4224527 := bstep (se 1 (by rfl) ⟨3168395, by rfl⟩ : syracuseStep 4224527 = 6336791) B6336791
theorem B4748827 : Blo 1250443 4748827 := bstep (se 1 (by rfl) ⟨3561620, by rfl⟩ : syracuseStep 4748827 = 7123241) B7123241
theorem B1250847 : Blo 1250443 1250847 := bstep (se 1 (by rfl) ⟨938135, by rfl⟩ : syracuseStep 1250847 = 1876271) B1876271
theorem B9500327 : Blo 1250443 9500327 := bstep (se 1 (by rfl) ⟨7125245, by rfl⟩ : syracuseStep 9500327 = 14250491) B14250491
theorem B1251007 : Blo 1250443 1251007 := bstep (se 1 (by rfl) ⟨938255, by rfl⟩ : syracuseStep 1251007 = 1876511) B1876511
theorem B1251047 : Blo 1250443 1251047 := bstep (se 1 (by rfl) ⟨938285, by rfl⟩ : syracuseStep 1251047 = 1876571) B1876571
theorem B2004745 : Blo 1250443 2004745 := bstep (se 2 (by rfl) ⟨751779, by rfl⟩ : syracuseStep 2004745 = 1503559) B1503559
theorem B3807101 : Blo 1250443 3807101 := bstep (se 3 (by rfl) ⟨713831, by rfl⟩ : syracuseStep 3807101 = 1427663) B1427663
theorem B2111359 : Blo 1250443 2111359 := bstep (se 1 (by rfl) ⟨1583519, by rfl⟩ : syracuseStep 2111359 = 3167039) B3167039
theorem B2816027 : Blo 1250443 2816027 := bstep (se 1 (by rfl) ⟨2112020, by rfl⟩ : syracuseStep 2816027 = 4224041) B4224041
theorem B1251391 : Blo 1250443 1251391 := bstep (se 1 (by rfl) ⟨938543, by rfl⟩ : syracuseStep 1251391 = 1877087) B1877087
theorem B2816063 : Blo 1250443 2816063 := bstep (se 1 (by rfl) ⟨2112047, by rfl⟩ : syracuseStep 2816063 = 4224095) B4224095
theorem B1251431 : Blo 1250443 1251431 := bstep (se 1 (by rfl) ⟨938573, by rfl⟩ : syracuseStep 1251431 = 1877147) B1877147
theorem B2439305 : Blo 1250443 2439305 := bstep (se 2 (by rfl) ⟨914739, by rfl⟩ : syracuseStep 2439305 = 1829479) B1829479
theorem B1251739 : Blo 1250443 1251739 := bstep (se 1 (by rfl) ⟨938804, by rfl⟩ : syracuseStep 1251739 = 1877609) B1877609
theorem B4749799 : Blo 1250443 4749799 := bstep (se 1 (by rfl) ⟨3562349, by rfl⟩ : syracuseStep 4749799 = 7124699) B7124699
theorem B1251823 : Blo 1250443 1251823 := bstep (se 1 (by rfl) ⟨938867, by rfl⟩ : syracuseStep 1251823 = 1877735) B1877735
theorem B1251887 : Blo 1250443 1251887 := bstep (se 1 (by rfl) ⟨938915, by rfl⟩ : syracuseStep 1251887 = 1877831) B1877831
theorem B15219251 : Blo 1250443 15219251 := bstep (se 1 (by rfl) ⟨11414438, by rfl⟩ : syracuseStep 15219251 = 22828877) B22828877
theorem B4225607 : Blo 1250443 4225607 := bstep (se 1 (by rfl) ⟨3169205, by rfl⟩ : syracuseStep 4225607 = 6338411) B6338411
theorem B2112095 : Blo 1250443 2112095 := bstep (se 1 (by rfl) ⟨1584071, by rfl⟩ : syracuseStep 2112095 = 3168143) B3168143
theorem B1252159 : Blo 1250443 1252159 := bstep (se 1 (by rfl) ⟨939119, by rfl⟩ : syracuseStep 1252159 = 1878239) B1878239
theorem B2440039 : Blo 1250443 2440039 := bstep (se 1 (by rfl) ⟨1830029, by rfl⟩ : syracuseStep 2440039 = 3660059) B3660059
theorem B1252199 : Blo 1250443 1252199 := bstep (se 1 (by rfl) ⟨939149, by rfl⟩ : syracuseStep 1252199 = 1878299) B1878299
theorem B5348207 : Blo 1250443 5348207 := bstep (se 1 (by rfl) ⟨4011155, by rfl⟩ : syracuseStep 5348207 = 8022311) B8022311
theorem B1252287 : Blo 1250443 1252287 := bstep (se 1 (by rfl) ⟨939215, by rfl⟩ : syracuseStep 1252287 = 1878431) B1878431
theorem B1252415 : Blo 1250443 1252415 := bstep (se 1 (by rfl) ⟨939311, by rfl⟩ : syracuseStep 1252415 = 1878623) B1878623
theorem B6012467 : Blo 1250443 6012467 := bstep (se 1 (by rfl) ⟨4509350, by rfl⟩ : syracuseStep 6012467 = 9018701) B9018701
theorem B9502271 : Blo 1250443 9502271 := bstep (se 1 (by rfl) ⟨7126703, by rfl⟩ : syracuseStep 9502271 = 14253407) B14253407
theorem B3563261 : Blo 1250443 3563261 := bstep (se 3 (by rfl) ⟨668111, by rfl⟩ : syracuseStep 3563261 = 1336223) B1336223
theorem B10149799 : Blo 1250443 10149799 := bstep (se 1 (by rfl) ⟨7612349, by rfl⟩ : syracuseStep 10149799 = 15224699) B15224699
theorem B3563489 : Blo 1250443 3563489 := bstep (se 2 (by rfl) ⟨1336308, by rfl⟩ : syracuseStep 3563489 = 2672617) B2672617
theorem B3563615 : Blo 1250443 3563615 := bstep (se 1 (by rfl) ⟨2672711, by rfl⟩ : syracuseStep 3563615 = 5345423) B5345423
theorem B13525451 : Blo 1250443 13525451 := bstep (se 1 (by rfl) ⟨10144088, by rfl⟩ : syracuseStep 13525451 = 20288177) B20288177
theorem B6333065 : Blo 1250443 6333065 := bstep (se 2 (by rfl) ⟨2374899, by rfl⟩ : syracuseStep 6333065 = 4749799) B4749799
theorem B4006543 : Blo 1250443 4006543 := bstep (se 1 (by rfl) ⟨3004907, by rfl⟩ : syracuseStep 4006543 = 6009815) B6009815
theorem B1876859 : Blo 1250443 1876859 := bstep (se 1 (by rfl) ⟨1407644, by rfl⟩ : syracuseStep 1876859 = 2815289) B2815289
theorem B1876895 : Blo 1250443 1876895 := bstep (se 1 (by rfl) ⟨1407671, by rfl⟩ : syracuseStep 1876895 = 2815343) B2815343
theorem B6333551 : Blo 1250443 6333551 := bstep (se 1 (by rfl) ⟨4750163, by rfl⟩ : syracuseStep 6333551 = 9500327) B9500327
theorem B3253385 : Blo 1250443 3253385 := bstep (se 2 (by rfl) ⟨1220019, by rfl⟩ : syracuseStep 3253385 = 2440039) B2440039
theorem B2376935 : Blo 1250443 2376935 := bstep (se 1 (by rfl) ⟨1782701, by rfl⟩ : syracuseStep 2376935 = 3565403) B3565403
theorem B1877351 : Blo 1250443 1877351 := bstep (se 1 (by rfl) ⟨1408013, by rfl⟩ : syracuseStep 1877351 = 2816027) B2816027
theorem B1877375 : Blo 1250443 1877375 := bstep (se 1 (by rfl) ⟨1408031, by rfl⟩ : syracuseStep 1877375 = 2816063) B2816063
theorem B10143443 : Blo 1250443 10143443 := bstep (se 1 (by rfl) ⟨7607582, by rfl⟩ : syracuseStep 10143443 = 15215165) B15215165
theorem B6768481 : Blo 1250443 6768481 := bstep (se 2 (by rfl) ⟨2538180, by rfl⟩ : syracuseStep 6768481 = 5076361) B5076361
theorem B3565471 : Blo 1250443 3565471 := bstep (se 1 (by rfl) ⟨2674103, by rfl⟩ : syracuseStep 3565471 = 5348207) B5348207
theorem B3213227 : Blo 1250443 3213227 := bstep (se 1 (by rfl) ⟨2409920, by rfl⟩ : syracuseStep 3213227 = 4819841) B4819841
theorem B2672959 : Blo 1250443 2672959 := bstep (se 1 (by rfl) ⟨2004719, by rfl⟩ : syracuseStep 2672959 = 4009439) B4009439
theorem B2672993 : Blo 1250443 2672993 := bstep (se 2 (by rfl) ⟨1002372, by rfl⟩ : syracuseStep 2672993 = 2004745) B2004745
theorem B4008311 : Blo 1250443 4008311 := bstep (se 1 (by rfl) ⟨3006233, by rfl⟩ : syracuseStep 4008311 = 6012467) B6012467
theorem B6334847 : Blo 1250443 6334847 := bstep (se 1 (by rfl) ⟨4751135, by rfl⟩ : syracuseStep 6334847 = 9502271) B9502271
theorem B4008761 : Blo 1250443 4008761 := bstep (se 2 (by rfl) ⟨1503285, by rfl⟩ : syracuseStep 4008761 = 3006571) B3006571
theorem B2813543 : Blo 1250443 2813543 := bstep (se 1 (by rfl) ⟨2110157, by rfl⟩ : syracuseStep 2813543 = 4220315) B4220315
theorem B1626203 : Blo 1250443 1626203 := bstep (se 1 (by rfl) ⟨1219652, by rfl⟩ : syracuseStep 1626203 = 2439305) B2439305
theorem B5419375 : Blo 1250443 5419375 := bstep (se 1 (by rfl) ⟨4064531, by rfl⟩ : syracuseStep 5419375 = 8129063) B8129063
theorem B10146167 : Blo 1250443 10146167 := bstep (se 1 (by rfl) ⟨7609625, by rfl⟩ : syracuseStep 10146167 = 15219251) B15219251
theorem B6337277 : Blo 1250443 6337277 := bstep (se 3 (by rfl) ⟨1188239, by rfl⟩ : syracuseStep 6337277 = 2376479) B2376479
theorem B2110279 : Blo 1250443 2110279 := bstep (se 1 (by rfl) ⟨1582709, by rfl⟩ : syracuseStep 2110279 = 3165419) B3165419
theorem B2814803 : Blo 1250443 2814803 := bstep (se 1 (by rfl) ⟨2111102, by rfl⟩ : syracuseStep 2814803 = 4222205) B4222205
theorem B3380089 : Blo 1250443 3380089 := bstep (se 2 (by rfl) ⟨1267533, by rfl⟩ : syracuseStep 3380089 = 2535067) B2535067
theorem B16044925 : Blo 1250443 16044925 := bstep (se 3 (by rfl) ⟨3008423, by rfl⟩ : syracuseStep 16044925 = 6016847) B6016847
theorem B2110367 : Blo 1250443 2110367 := bstep (se 1 (by rfl) ⟨1582775, by rfl⟩ : syracuseStep 2110367 = 3165551) B3165551
theorem B6337439 : Blo 1250443 6337439 := bstep (se 1 (by rfl) ⟨4753079, by rfl⟩ : syracuseStep 6337439 = 9506159) B9506159
theorem B40104935 : Blo 1250443 40104935 := bstep (se 1 (by rfl) ⟨30078701, by rfl⟩ : syracuseStep 40104935 = 60157403) B60157403
theorem B7607465 : Blo 1250443 7607465 := bstep (se 2 (by rfl) ⟨2852799, by rfl⟩ : syracuseStep 7607465 = 5705599) B5705599
theorem B2815145 : Blo 1250443 2815145 := bstep (se 2 (by rfl) ⟨1055679, by rfl⟩ : syracuseStep 2815145 = 2111359) B2111359
theorem B1250687 : Blo 1250443 1250687 := bstep (se 1 (by rfl) ⟨938015, by rfl⟩ : syracuseStep 1250687 = 1876031) B1876031
theorem B2004431 : Blo 1250443 2004431 := bstep (se 1 (by rfl) ⟨1503323, by rfl⟩ : syracuseStep 2004431 = 3006647) B3006647
theorem B7132697 : Blo 1250443 7132697 := bstep (se 2 (by rfl) ⟨2674761, by rfl⟩ : syracuseStep 7132697 = 5349523) B5349523
theorem B12850771 : Blo 1250443 12850771 := bstep (se 1 (by rfl) ⟨9638078, by rfl⟩ : syracuseStep 12850771 = 19276157) B19276157
theorem B10688111 : Blo 1250443 10688111 := bstep (se 1 (by rfl) ⟨8016083, by rfl⟩ : syracuseStep 10688111 = 16032167) B16032167
theorem B2815847 : Blo 1250443 2815847 := bstep (se 1 (by rfl) ⟨2111885, by rfl⟩ : syracuseStep 2815847 = 4223771) B4223771
theorem B24041555 : Blo 1250443 24041555 := bstep (se 1 (by rfl) ⟨18031166, by rfl⟩ : syracuseStep 24041555 = 36062333) B36062333
theorem B1251455 : Blo 1250443 1251455 := bstep (se 1 (by rfl) ⟨938591, by rfl⟩ : syracuseStep 1251455 = 1877183) B1877183
theorem B36108463 : Blo 1250443 36108463 := bstep (se 1 (by rfl) ⟨27081347, by rfl⟩ : syracuseStep 36108463 = 54162695) B54162695
theorem B1251579 : Blo 1250443 1251579 := bstep (se 1 (by rfl) ⟨938684, by rfl⟩ : syracuseStep 1251579 = 1877369) B1877369
theorem B2816351 : Blo 1250443 2816351 := bstep (se 1 (by rfl) ⟨2112263, by rfl⟩ : syracuseStep 2816351 = 4224527) B4224527
theorem B2538067 : Blo 1250443 2538067 := bstep (se 1 (by rfl) ⟨1903550, by rfl⟩ : syracuseStep 2538067 = 3807101) B3807101
theorem B1251995 : Blo 1250443 1251995 := bstep (se 1 (by rfl) ⟨938996, by rfl⟩ : syracuseStep 1251995 = 1877993) B1877993
theorem B8018621 : Blo 1250443 8018621 := bstep (se 3 (by rfl) ⟨1503491, by rfl⟩ : syracuseStep 8018621 = 3006983) B3006983
theorem B1252319 : Blo 1250443 1252319 := bstep (se 1 (by rfl) ⟨939239, by rfl⟩ : syracuseStep 1252319 = 1878479) B1878479
theorem B2817071 : Blo 1250443 2817071 := bstep (se 1 (by rfl) ⟨2112803, by rfl⟩ : syracuseStep 2817071 = 4225607) B4225607
theorem B3169327 : Blo 1250443 3169327 := bstep (se 1 (by rfl) ⟨2376995, by rfl⟩ : syracuseStep 3169327 = 4753991) B4753991
theorem B1408063 : Blo 1250443 1408063 := bstep (se 1 (by rfl) ⟨1056047, by rfl⟩ : syracuseStep 1408063 = 2112095) B2112095
theorem B3169439 : Blo 1250443 3169439 := bstep (se 1 (by rfl) ⟨2377079, by rfl⟩ : syracuseStep 3169439 = 4754159) B4754159
theorem B4513097 : Blo 1250443 4513097 := bstep (se 2 (by rfl) ⟨1692411, by rfl⟩ : syracuseStep 4513097 = 3384823) B3384823
theorem B6331769 : Blo 1250443 6331769 := bstep (se 2 (by rfl) ⟨2374413, by rfl⟩ : syracuseStep 6331769 = 4748827) B4748827
theorem B12361135 : Blo 1250443 12361135 := bstep (se 1 (by rfl) ⟨9270851, by rfl⟩ : syracuseStep 12361135 = 18541703) B18541703
theorem B2375507 : Blo 1250443 2375507 := bstep (se 1 (by rfl) ⟨1781630, by rfl⟩ : syracuseStep 2375507 = 3563261) B3563261
theorem B13533065 : Blo 1250443 13533065 := bstep (se 2 (by rfl) ⟨5074899, by rfl⟩ : syracuseStep 13533065 = 10149799) B10149799
theorem B2375659 : Blo 1250443 2375659 := bstep (se 1 (by rfl) ⟨1781744, by rfl⟩ : syracuseStep 2375659 = 3563489) B3563489
theorem B2375743 : Blo 1250443 2375743 := bstep (se 1 (by rfl) ⟨1781807, by rfl⟩ : syracuseStep 2375743 = 3563615) B3563615
theorem B48144617 : Blo 1250443 48144617 := bstep (se 2 (by rfl) ⟨18054231, by rfl⟩ : syracuseStep 48144617 = 36108463) B36108463
theorem B8675693 : Blo 1250443 8675693 := bstep (se 3 (by rfl) ⟨1626692, by rfl⟩ : syracuseStep 8675693 = 3253385) B3253385
theorem B3563945 : Blo 1250443 3563945 := bstep (se 2 (by rfl) ⟨1336479, by rfl⟩ : syracuseStep 3563945 = 2672959) B2672959
theorem B1876535 : Blo 1250443 1876535 := bstep (se 1 (by rfl) ⟨1407401, by rfl⟩ : syracuseStep 1876535 = 2814803) B2814803
theorem B3384089 : Blo 1250443 3384089 := bstep (se 2 (by rfl) ⟨1269033, by rfl⟩ : syracuseStep 3384089 = 2538067) B2538067
theorem B5071643 : Blo 1250443 5071643 := bstep (se 1 (by rfl) ⟨3803732, by rfl⟩ : syracuseStep 5071643 = 7607465) B7607465
theorem B1876763 : Blo 1250443 1876763 := bstep (se 1 (by rfl) ⟨1407572, by rfl⟩ : syracuseStep 1876763 = 2815145) B2815145
theorem B5342057 : Blo 1250443 5342057 := bstep (se 2 (by rfl) ⟨2003271, by rfl⟩ : syracuseStep 5342057 = 4006543) B4006543
theorem B12034925 : Blo 1250443 12034925 := bstep (se 3 (by rfl) ⟨2256548, by rfl⟩ : syracuseStep 12034925 = 4513097) B4513097
theorem B4506785 : Blo 1250443 4506785 := bstep (se 2 (by rfl) ⟨1690044, by rfl⟩ : syracuseStep 4506785 = 3380089) B3380089
theorem B1877231 : Blo 1250443 1877231 := bstep (se 1 (by rfl) ⟨1407923, by rfl⟩ : syracuseStep 1877231 = 2815847) B2815847
theorem B1877417 : Blo 1250443 1877417 := bstep (se 2 (by rfl) ⟨704031, by rfl⟩ : syracuseStep 1877417 = 1408063) B1408063
theorem B1877567 : Blo 1250443 1877567 := bstep (se 1 (by rfl) ⟨1408175, by rfl⟩ : syracuseStep 1877567 = 2816351) B2816351
theorem B2672207 : Blo 1250443 2672207 := bstep (se 1 (by rfl) ⟨2004155, by rfl⟩ : syracuseStep 2672207 = 4008311) B4008311
theorem B2672507 : Blo 1250443 2672507 := bstep (se 1 (by rfl) ⟨2004380, by rfl⟩ : syracuseStep 2672507 = 4008761) B4008761
theorem B28903333 : Blo 1250443 28903333 := bstep (se 4 (by rfl) ⟨2709687, by rfl⟩ : syracuseStep 28903333 = 5419375) B5419375
theorem B1878047 : Blo 1250443 1878047 := bstep (se 1 (by rfl) ⟨1408535, by rfl⟩ : syracuseStep 1878047 = 2817071) B2817071
theorem B6334685 : Blo 1250443 6334685 := bstep (se 3 (by rfl) ⟨1187753, by rfl⟩ : syracuseStep 6334685 = 2375507) B2375507
theorem B4221179 : Blo 1250443 4221179 := bstep (se 1 (by rfl) ⟨3165884, by rfl⟩ : syracuseStep 4221179 = 6331769) B6331769
theorem B4753961 : Blo 1250443 4753961 := bstep (se 2 (by rfl) ⟨1782735, by rfl⟩ : syracuseStep 4753961 = 3565471) B3565471
theorem B9022043 : Blo 1250443 9022043 := bstep (se 1 (by rfl) ⟨6766532, by rfl⟩ : syracuseStep 9022043 = 13533065) B13533065
theorem B4336541 : Blo 1250443 4336541 := bstep (se 3 (by rfl) ⟨813101, by rfl⟩ : syracuseStep 4336541 = 1626203) B1626203
theorem B4222043 : Blo 1250443 4222043 := bstep (se 1 (by rfl) ⟨3166532, by rfl⟩ : syracuseStep 4222043 = 6333065) B6333065
theorem B4222367 : Blo 1250443 4222367 := bstep (se 1 (by rfl) ⟨3166775, by rfl⟩ : syracuseStep 4222367 = 6333551) B6333551
theorem B1584623 : Blo 1250443 1584623 := bstep (se 1 (by rfl) ⟨1188467, by rfl⟩ : syracuseStep 1584623 = 2376935) B2376935
theorem B4755131 : Blo 1250443 4755131 := bstep (se 1 (by rfl) ⟨3566348, by rfl⟩ : syracuseStep 4755131 = 7132697) B7132697
theorem B2813705 : Blo 1250443 2813705 := bstep (se 2 (by rfl) ⟨1055139, by rfl⟩ : syracuseStep 2813705 = 2110279) B2110279
theorem B6762295 : Blo 1250443 6762295 := bstep (se 1 (by rfl) ⟨5071721, by rfl⟩ : syracuseStep 6762295 = 10143443) B10143443
theorem B21393233 : Blo 1250443 21393233 := bstep (se 2 (by rfl) ⟨8022462, by rfl⟩ : syracuseStep 21393233 = 16044925) B16044925
theorem B5345149 : Blo 1250443 5345149 := bstep (se 3 (by rfl) ⟨1002215, by rfl⟩ : syracuseStep 5345149 = 2004431) B2004431
theorem B16027703 : Blo 1250443 16027703 := bstep (se 1 (by rfl) ⟨12020777, by rfl⟩ : syracuseStep 16027703 = 24041555) B24041555
theorem B1781995 : Blo 1250443 1781995 := bstep (se 1 (by rfl) ⟨1336496, by rfl⟩ : syracuseStep 1781995 = 2672993) B2672993
theorem B4223231 : Blo 1250443 4223231 := bstep (se 1 (by rfl) ⟨3167423, by rfl⟩ : syracuseStep 4223231 = 6334847) B6334847
theorem B5345747 : Blo 1250443 5345747 := bstep (se 1 (by rfl) ⟨4009310, by rfl⟩ : syracuseStep 5345747 = 8018621) B8018621
theorem B17134361 : Blo 1250443 17134361 := bstep (se 2 (by rfl) ⟨6425385, by rfl⟩ : syracuseStep 17134361 = 12850771) B12850771
theorem B9024641 : Blo 1250443 9024641 := bstep (se 2 (by rfl) ⟨3384240, by rfl⟩ : syracuseStep 9024641 = 6768481) B6768481
theorem B3167545 : Blo 1250443 3167545 := bstep (se 2 (by rfl) ⟨1187829, by rfl⟩ : syracuseStep 3167545 = 2375659) B2375659
theorem B6764111 : Blo 1250443 6764111 := bstep (se 1 (by rfl) ⟨5073083, by rfl⟩ : syracuseStep 6764111 = 10146167) B10146167
theorem B9016967 : Blo 1250443 9016967 := bstep (se 1 (by rfl) ⟨6762725, by rfl⟩ : syracuseStep 9016967 = 13525451) B13525451
theorem B4224851 : Blo 1250443 4224851 := bstep (se 1 (by rfl) ⟨3168638, by rfl⟩ : syracuseStep 4224851 = 6337277) B6337277
theorem B1251239 : Blo 1250443 1251239 := bstep (se 1 (by rfl) ⟨938429, by rfl⟩ : syracuseStep 1251239 = 1876859) B1876859
theorem B1406911 : Blo 1250443 1406911 := bstep (se 1 (by rfl) ⟨1055183, by rfl⟩ : syracuseStep 1406911 = 2110367) B2110367
theorem B1251263 : Blo 1250443 1251263 := bstep (se 1 (by rfl) ⟨938447, by rfl⟩ : syracuseStep 1251263 = 1876895) B1876895
theorem B4224959 : Blo 1250443 4224959 := bstep (se 1 (by rfl) ⟨3168719, by rfl⟩ : syracuseStep 4224959 = 6337439) B6337439
theorem B26736623 : Blo 1250443 26736623 := bstep (se 1 (by rfl) ⟨20052467, by rfl⟩ : syracuseStep 26736623 = 40104935) B40104935
theorem B1251567 : Blo 1250443 1251567 := bstep (se 1 (by rfl) ⟨938675, by rfl⟩ : syracuseStep 1251567 = 1877351) B1877351
theorem B1251583 : Blo 1250443 1251583 := bstep (se 1 (by rfl) ⟨938687, by rfl⟩ : syracuseStep 1251583 = 1877375) B1877375
theorem B7125407 : Blo 1250443 7125407 := bstep (se 1 (by rfl) ⟨5344055, by rfl⟩ : syracuseStep 7125407 = 10688111) B10688111
theorem B4225769 : Blo 1250443 4225769 := bstep (se 2 (by rfl) ⟨1584663, by rfl⟩ : syracuseStep 4225769 = 3169327) B3169327
theorem B16481513 : Blo 1250443 16481513 := bstep (se 2 (by rfl) ⟨6180567, by rfl⟩ : syracuseStep 16481513 = 12361135) B12361135
theorem B2112959 : Blo 1250443 2112959 := bstep (se 1 (by rfl) ⟨1584719, by rfl⟩ : syracuseStep 2112959 = 3169439) B3169439
theorem B1875695 : Blo 1250443 1875695 := bstep (se 1 (by rfl) ⟨1406771, by rfl⟩ : syracuseStep 1875695 = 2813543) B2813543
theorem B8568605 : Blo 1250443 8568605 := bstep (se 3 (by rfl) ⟨1606613, by rfl⟩ : syracuseStep 8568605 = 3213227) B3213227
theorem B32096411 : Blo 1250443 32096411 := bstep (se 1 (by rfl) ⟨24072308, by rfl⟩ : syracuseStep 32096411 = 48144617) B48144617
theorem B5783795 : Blo 1250443 5783795 := bstep (se 1 (by rfl) ⟨4337846, by rfl⟩ : syracuseStep 5783795 = 8675693) B8675693
theorem B2375963 : Blo 1250443 2375963 := bstep (se 1 (by rfl) ⟨1781972, by rfl⟩ : syracuseStep 2375963 = 3563945) B3563945
theorem B3563831 : Blo 1250443 3563831 := bstep (se 1 (by rfl) ⟨2672873, by rfl⟩ : syracuseStep 3563831 = 5345747) B5345747
theorem B2375993 : Blo 1250443 2375993 := bstep (se 2 (by rfl) ⟨890997, by rfl⟩ : syracuseStep 2375993 = 1781995) B1781995
theorem B43950701 : Blo 1250443 43950701 := bstep (se 3 (by rfl) ⟨8240756, by rfl⟩ : syracuseStep 43950701 = 16481513) B16481513
theorem B24045245 : Blo 1250443 24045245 := bstep (se 3 (by rfl) ⟨4508483, by rfl⟩ : syracuseStep 24045245 = 9016967) B9016967
theorem B6014695 : Blo 1250443 6014695 := bstep (se 1 (by rfl) ⟨4511021, by rfl⟩ : syracuseStep 6014695 = 9022043) B9022043
theorem B285190645 : Blo 1250443 285190645 := bstep (se 5 (by rfl) ⟨13368311, by rfl⟩ : syracuseStep 285190645 = 26736623) B26736623
theorem B5712403 : Blo 1250443 5712403 := bstep (se 1 (by rfl) ⟨4284302, by rfl⟩ : syracuseStep 5712403 = 8568605) B8568605
theorem B38537777 : Blo 1250443 38537777 := bstep (se 2 (by rfl) ⟨14451666, by rfl⟩ : syracuseStep 38537777 = 28903333) B28903333
theorem B10685135 : Blo 1250443 10685135 := bstep (se 1 (by rfl) ⟨8013851, by rfl⟩ : syracuseStep 10685135 = 16027703) B16027703
theorem B2256059 : Blo 1250443 2256059 := bstep (se 1 (by rfl) ⟨1692044, by rfl⟩ : syracuseStep 2256059 = 3384089) B3384089
theorem B11422907 : Blo 1250443 11422907 := bstep (se 1 (by rfl) ⟨8567180, by rfl⟩ : syracuseStep 11422907 = 17134361) B17134361
theorem B8023283 : Blo 1250443 8023283 := bstep (se 1 (by rfl) ⟨6017462, by rfl⟩ : syracuseStep 8023283 = 12034925) B12034925
theorem B6016427 : Blo 1250443 6016427 := bstep (se 1 (by rfl) ⟨4512320, by rfl⟩ : syracuseStep 6016427 = 9024641) B9024641
theorem B4509407 : Blo 1250443 4509407 := bstep (se 1 (by rfl) ⟨3382055, by rfl⟩ : syracuseStep 4509407 = 6764111) B6764111
theorem B1781471 : Blo 1250443 1781471 := bstep (se 1 (by rfl) ⟨1336103, by rfl⟩ : syracuseStep 1781471 = 2672207) B2672207
theorem B1781671 : Blo 1250443 1781671 := bstep (se 1 (by rfl) ⟨1336253, by rfl⟩ : syracuseStep 1781671 = 2672507) B2672507
theorem B4223123 : Blo 1250443 4223123 := bstep (se 1 (by rfl) ⟨3167342, by rfl⟩ : syracuseStep 4223123 = 6334685) B6334685
theorem B2814119 : Blo 1250443 2814119 := bstep (se 1 (by rfl) ⟨2110589, by rfl⟩ : syracuseStep 2814119 = 4221179) B4221179
theorem B4223393 : Blo 1250443 4223393 := bstep (se 2 (by rfl) ⟨1583772, by rfl⟩ : syracuseStep 4223393 = 3167545) B3167545
theorem B2814695 : Blo 1250443 2814695 := bstep (se 1 (by rfl) ⟨2111021, by rfl⟩ : syracuseStep 2814695 = 4222043) B4222043
theorem B2814911 : Blo 1250443 2814911 := bstep (se 1 (by rfl) ⟨2111183, by rfl⟩ : syracuseStep 2814911 = 4222367) B4222367
theorem B9016393 : Blo 1250443 9016393 := bstep (se 2 (by rfl) ⟨3381147, by rfl⟩ : syracuseStep 9016393 = 6762295) B6762295
theorem B1250463 : Blo 1250443 1250463 := bstep (se 1 (by rfl) ⟨937847, by rfl⟩ : syracuseStep 1250463 = 1875695) B1875695
theorem B3167657 : Blo 1250443 3167657 := bstep (se 2 (by rfl) ⟨1187871, by rfl⟩ : syracuseStep 3167657 = 2375743) B2375743
theorem B2815487 : Blo 1250443 2815487 := bstep (se 1 (by rfl) ⟨2111615, by rfl⟩ : syracuseStep 2815487 = 4223231) B4223231
theorem B1251023 : Blo 1250443 1251023 := bstep (se 1 (by rfl) ⟨938267, by rfl⟩ : syracuseStep 1251023 = 1876535) B1876535
theorem B3381095 : Blo 1250443 3381095 := bstep (se 1 (by rfl) ⟨2535821, by rfl⟩ : syracuseStep 3381095 = 5071643) B5071643
theorem B1251175 : Blo 1250443 1251175 := bstep (se 1 (by rfl) ⟨938381, by rfl⟩ : syracuseStep 1251175 = 1876763) B1876763
theorem B3561371 : Blo 1250443 3561371 := bstep (se 1 (by rfl) ⟨2671028, by rfl⟩ : syracuseStep 3561371 = 5342057) B5342057
theorem B3004523 : Blo 1250443 3004523 := bstep (se 1 (by rfl) ⟨2253392, by rfl⟩ : syracuseStep 3004523 = 4506785) B4506785
theorem B1251487 : Blo 1250443 1251487 := bstep (se 1 (by rfl) ⟨938615, by rfl⟩ : syracuseStep 1251487 = 1877231) B1877231
theorem B1251611 : Blo 1250443 1251611 := bstep (se 1 (by rfl) ⟨938708, by rfl⟩ : syracuseStep 1251611 = 1877417) B1877417
theorem B1251711 : Blo 1250443 1251711 := bstep (se 1 (by rfl) ⟨938783, by rfl⟩ : syracuseStep 1251711 = 1877567) B1877567
theorem B2816567 : Blo 1250443 2816567 := bstep (se 1 (by rfl) ⟨2112425, by rfl⟩ : syracuseStep 2816567 = 4224851) B4224851
theorem B4225661 : Blo 1250443 4225661 := bstep (se 3 (by rfl) ⟨792311, by rfl⟩ : syracuseStep 4225661 = 1584623) B1584623
theorem B2816639 : Blo 1250443 2816639 := bstep (se 1 (by rfl) ⟨2112479, by rfl⟩ : syracuseStep 2816639 = 4224959) B4224959
theorem B1252031 : Blo 1250443 1252031 := bstep (se 1 (by rfl) ⟨939023, by rfl⟩ : syracuseStep 1252031 = 1878047) B1878047
theorem B4750271 : Blo 1250443 4750271 := bstep (se 1 (by rfl) ⟨3562703, by rfl⟩ : syracuseStep 4750271 = 7125407) B7125407
theorem B3169307 : Blo 1250443 3169307 := bstep (se 1 (by rfl) ⟨2376980, by rfl⟩ : syracuseStep 3169307 = 4753961) B4753961
theorem B2817179 : Blo 1250443 2817179 := bstep (se 1 (by rfl) ⟨2112884, by rfl⟩ : syracuseStep 2817179 = 4225769) B4225769
theorem B2891027 : Blo 1250443 2891027 := bstep (se 1 (by rfl) ⟨2168270, by rfl⟩ : syracuseStep 2891027 = 4336541) B4336541
theorem B1408639 : Blo 1250443 1408639 := bstep (se 1 (by rfl) ⟨1056479, by rfl⟩ : syracuseStep 1408639 = 2112959) B2112959
theorem B3170087 : Blo 1250443 3170087 := bstep (se 1 (by rfl) ⟨2377565, by rfl⟩ : syracuseStep 3170087 = 4755131) B4755131
theorem B7126865 : Blo 1250443 7126865 := bstep (se 2 (by rfl) ⟨2672574, by rfl⟩ : syracuseStep 7126865 = 5345149) B5345149
theorem B1875803 : Blo 1250443 1875803 := bstep (se 1 (by rfl) ⟨1406852, by rfl⟩ : syracuseStep 1875803 = 2813705) B2813705
theorem B14262155 : Blo 1250443 14262155 := bstep (se 1 (by rfl) ⟨10696616, by rfl⟩ : syracuseStep 14262155 = 21393233) B21393233
theorem B1875881 : Blo 1250443 1875881 := bstep (se 2 (by rfl) ⟨703455, by rfl⟩ : syracuseStep 1875881 = 1406911) B1406911
theorem B21397607 : Blo 1250443 21397607 := bstep (se 1 (by rfl) ⟨16048205, by rfl⟩ : syracuseStep 21397607 = 32096411) B32096411
theorem B1876079 : Blo 1250443 1876079 := bstep (se 1 (by rfl) ⟨1407059, by rfl⟩ : syracuseStep 1876079 = 2814119) B2814119
theorem B2375887 : Blo 1250443 2375887 := bstep (se 1 (by rfl) ⟨1781915, by rfl⟩ : syracuseStep 2375887 = 3563831) B3563831
theorem B1876463 : Blo 1250443 1876463 := bstep (se 1 (by rfl) ⟨1407347, by rfl⟩ : syracuseStep 1876463 = 2814695) B2814695
theorem B1876607 : Blo 1250443 1876607 := bstep (se 1 (by rfl) ⟨1407455, by rfl⟩ : syracuseStep 1876607 = 2814911) B2814911
theorem B1876991 : Blo 1250443 1876991 := bstep (se 1 (by rfl) ⟨1407743, by rfl⟩ : syracuseStep 1876991 = 2815487) B2815487
theorem B2254063 : Blo 1250443 2254063 := bstep (se 1 (by rfl) ⟨1690547, by rfl⟩ : syracuseStep 2254063 = 3381095) B3381095
theorem B25691851 : Blo 1250443 25691851 := bstep (se 1 (by rfl) ⟨19268888, by rfl⟩ : syracuseStep 25691851 = 38537777) B38537777
theorem B1877711 : Blo 1250443 1877711 := bstep (se 1 (by rfl) ⟨1408283, by rfl⟩ : syracuseStep 1877711 = 2816567) B2816567
theorem B1877759 : Blo 1250443 1877759 := bstep (se 1 (by rfl) ⟨1408319, by rfl⟩ : syracuseStep 1877759 = 2816639) B2816639
theorem B1878119 : Blo 1250443 1878119 := bstep (se 1 (by rfl) ⟨1408589, by rfl⟩ : syracuseStep 1878119 = 2817179) B2817179
theorem B1878185 : Blo 1250443 1878185 := bstep (se 2 (by rfl) ⟨704319, by rfl⟩ : syracuseStep 1878185 = 1408639) B1408639
theorem B1927351 : Blo 1250443 1927351 := bstep (se 1 (by rfl) ⟨1445513, by rfl⟩ : syracuseStep 1927351 = 2891027) B2891027
theorem B1583975 : Blo 1250443 1583975 := bstep (se 1 (by rfl) ⟨1187981, by rfl⟩ : syracuseStep 1583975 = 2375963) B2375963
theorem B6016157 : Blo 1250443 6016157 := bstep (se 3 (by rfl) ⟨1128029, by rfl⟩ : syracuseStep 6016157 = 2256059) B2256059
theorem B6335981 : Blo 1250443 6335981 := bstep (se 3 (by rfl) ⟨1187996, by rfl⟩ : syracuseStep 6335981 = 2375993) B2375993
theorem B2003015 : Blo 1250443 2003015 := bstep (se 1 (by rfl) ⟨1502261, by rfl⟩ : syracuseStep 2003015 = 3004523) B3004523
theorem B12021857 : Blo 1250443 12021857 := bstep (se 2 (by rfl) ⟨4508196, by rfl⟩ : syracuseStep 12021857 = 9016393) B9016393
theorem B7123423 : Blo 1250443 7123423 := bstep (se 1 (by rfl) ⟨5342567, by rfl⟩ : syracuseStep 7123423 = 10685135) B10685135
theorem B3166847 : Blo 1250443 3166847 := bstep (se 1 (by rfl) ⟨2375135, by rfl⟩ : syracuseStep 3166847 = 4750271) B4750271
theorem B7615271 : Blo 1250443 7615271 := bstep (se 1 (by rfl) ⟨5711453, by rfl⟩ : syracuseStep 7615271 = 11422907) B11422907
theorem B4010951 : Blo 1250443 4010951 := bstep (se 1 (by rfl) ⟨3008213, by rfl⟩ : syracuseStep 4010951 = 6016427) B6016427
theorem B1250535 : Blo 1250443 1250535 := bstep (se 1 (by rfl) ⟨937901, by rfl⟩ : syracuseStep 1250535 = 1875803) B1875803
theorem B9508103 : Blo 1250443 9508103 := bstep (se 1 (by rfl) ⟨7131077, by rfl⟩ : syracuseStep 9508103 = 14262155) B14262155
theorem B1250587 : Blo 1250443 1250587 := bstep (se 1 (by rfl) ⟨937940, by rfl⟩ : syracuseStep 1250587 = 1875881) B1875881
theorem B2815415 : Blo 1250443 2815415 := bstep (se 1 (by rfl) ⟨2111561, by rfl⟩ : syracuseStep 2815415 = 4223123) B4223123
theorem B3855863 : Blo 1250443 3855863 := bstep (se 1 (by rfl) ⟨2891897, by rfl⟩ : syracuseStep 3855863 = 5783795) B5783795
theorem B2815595 : Blo 1250443 2815595 := bstep (se 1 (by rfl) ⟨2111696, by rfl⟩ : syracuseStep 2815595 = 4223393) B4223393
theorem B29300467 : Blo 1250443 29300467 := bstep (se 1 (by rfl) ⟨21975350, by rfl⟩ : syracuseStep 29300467 = 43950701) B43950701
theorem B380254193 : Blo 1250443 380254193 := bstep (se 2 (by rfl) ⟨142595322, by rfl⟩ : syracuseStep 380254193 = 285190645) B285190645
theorem B7616537 : Blo 1250443 7616537 := bstep (se 2 (by rfl) ⟨2856201, by rfl⟩ : syracuseStep 7616537 = 5712403) B5712403
theorem B2111771 : Blo 1250443 2111771 := bstep (se 1 (by rfl) ⟨1583828, by rfl⟩ : syracuseStep 2111771 = 3167657) B3167657
theorem B16030163 : Blo 1250443 16030163 := bstep (se 1 (by rfl) ⟨12022622, by rfl⟩ : syracuseStep 16030163 = 24045245) B24045245
theorem B2374247 : Blo 1250443 2374247 := bstep (se 1 (by rfl) ⟨1780685, by rfl⟩ : syracuseStep 2374247 = 3561371) B3561371
theorem B2817107 : Blo 1250443 2817107 := bstep (se 1 (by rfl) ⟨2112830, by rfl⟩ : syracuseStep 2817107 = 4225661) B4225661
theorem B4750589 : Blo 1250443 4750589 := bstep (se 3 (by rfl) ⟨890735, by rfl⟩ : syracuseStep 4750589 = 1781471) B1781471
theorem B2112871 : Blo 1250443 2112871 := bstep (se 1 (by rfl) ⟨1584653, by rfl⟩ : syracuseStep 2112871 = 3169307) B3169307
theorem B5348855 : Blo 1250443 5348855 := bstep (se 1 (by rfl) ⟨4011641, by rfl⟩ : syracuseStep 5348855 = 8023283) B8023283
theorem B8019593 : Blo 1250443 8019593 := bstep (se 2 (by rfl) ⟨3007347, by rfl⟩ : syracuseStep 8019593 = 6014695) B6014695
theorem B3006271 : Blo 1250443 3006271 := bstep (se 1 (by rfl) ⟨2254703, by rfl⟩ : syracuseStep 3006271 = 4509407) B4509407
theorem B2113391 : Blo 1250443 2113391 := bstep (se 1 (by rfl) ⟨1585043, by rfl⟩ : syracuseStep 2113391 = 3170087) B3170087
theorem B2375561 : Blo 1250443 2375561 := bstep (se 2 (by rfl) ⟨890835, by rfl⟩ : syracuseStep 2375561 = 1781671) B1781671
theorem B4751243 : Blo 1250443 4751243 := bstep (se 1 (by rfl) ⟨3563432, by rfl⟩ : syracuseStep 4751243 = 7126865) B7126865
theorem B5341373 : Blo 1250443 5341373 := bstep (se 3 (by rfl) ⟨1001507, by rfl⟩ : syracuseStep 5341373 = 2003015) B2003015
theorem B1876943 : Blo 1250443 1876943 := bstep (se 1 (by rfl) ⟨1407707, by rfl⟩ : syracuseStep 1876943 = 2815415) B2815415
theorem B1877063 : Blo 1250443 1877063 := bstep (se 1 (by rfl) ⟨1407797, by rfl⟩ : syracuseStep 1877063 = 2815595) B2815595
theorem B10282301 : Blo 1250443 10282301 := bstep (se 3 (by rfl) ⟨1927931, by rfl⟩ : syracuseStep 10282301 = 3855863) B3855863
theorem B14263613 : Blo 1250443 14263613 := bstep (se 3 (by rfl) ⟨2674427, by rfl⟩ : syracuseStep 14263613 = 5348855) B5348855
theorem B253502795 : Blo 1250443 253502795 := bstep (se 1 (by rfl) ⟨190127096, by rfl⟩ : syracuseStep 253502795 = 380254193) B380254193
theorem B1582831 : Blo 1250443 1582831 := bstep (se 1 (by rfl) ⟨1187123, by rfl⟩ : syracuseStep 1582831 = 2374247) B2374247
theorem B1878071 : Blo 1250443 1878071 := bstep (se 1 (by rfl) ⟨1408553, by rfl⟩ : syracuseStep 1878071 = 2817107) B2817107
theorem B4008361 : Blo 1250443 4008361 := bstep (se 2 (by rfl) ⟨1503135, by rfl⟩ : syracuseStep 4008361 = 3006271) B3006271
theorem B1583707 : Blo 1250443 1583707 := bstep (se 1 (by rfl) ⟨1187780, by rfl⟩ : syracuseStep 1583707 = 2375561) B2375561
theorem B8014571 : Blo 1250443 8014571 := bstep (se 1 (by rfl) ⟨6010928, by rfl⟩ : syracuseStep 8014571 = 12021857) B12021857
theorem B14265071 : Blo 1250443 14265071 := bstep (se 1 (by rfl) ⟨10698803, by rfl⟩ : syracuseStep 14265071 = 21397607) B21397607
theorem B9497897 : Blo 1250443 9497897 := bstep (se 2 (by rfl) ⟨3561711, by rfl⟩ : syracuseStep 9497897 = 7123423) B7123423
theorem B2673967 : Blo 1250443 2673967 := bstep (se 1 (by rfl) ⟨2005475, by rfl⟩ : syracuseStep 2673967 = 4010951) B4010951
theorem B10686775 : Blo 1250443 10686775 := bstep (se 1 (by rfl) ⟨8015081, by rfl⟩ : syracuseStep 10686775 = 16030163) B16030163
theorem B4010771 : Blo 1250443 4010771 := bstep (se 1 (by rfl) ⟨3008078, by rfl⟩ : syracuseStep 4010771 = 6016157) B6016157
theorem B3167059 : Blo 1250443 3167059 := bstep (se 1 (by rfl) ⟨2375294, by rfl⟩ : syracuseStep 3167059 = 4750589) B4750589
theorem B34255801 : Blo 1250443 34255801 := bstep (se 2 (by rfl) ⟨12845925, by rfl⟩ : syracuseStep 34255801 = 25691851) B25691851
theorem B4223933 : Blo 1250443 4223933 := bstep (se 3 (by rfl) ⟨791987, by rfl⟩ : syracuseStep 4223933 = 1583975) B1583975
theorem B4223987 : Blo 1250443 4223987 := bstep (se 1 (by rfl) ⟨3167990, by rfl⟩ : syracuseStep 4223987 = 6335981) B6335981
theorem B5346395 : Blo 1250443 5346395 := bstep (se 1 (by rfl) ⟨4009796, by rfl⟩ : syracuseStep 5346395 = 8019593) B8019593
theorem B3167495 : Blo 1250443 3167495 := bstep (se 1 (by rfl) ⟨2375621, by rfl⟩ : syracuseStep 3167495 = 4751243) B4751243
theorem B1250719 : Blo 1250443 1250719 := bstep (se 1 (by rfl) ⟨938039, by rfl⟩ : syracuseStep 1250719 = 1876079) B1876079
theorem B2569801 : Blo 1250443 2569801 := bstep (se 2 (by rfl) ⟨963675, by rfl⟩ : syracuseStep 2569801 = 1927351) B1927351
theorem B3167849 : Blo 1250443 3167849 := bstep (se 2 (by rfl) ⟨1187943, by rfl⟩ : syracuseStep 3167849 = 2375887) B2375887
theorem B1250975 : Blo 1250443 1250975 := bstep (se 1 (by rfl) ⟨938231, by rfl⟩ : syracuseStep 1250975 = 1876463) B1876463
theorem B1251071 : Blo 1250443 1251071 := bstep (se 1 (by rfl) ⟨938303, by rfl⟩ : syracuseStep 1251071 = 1876607) B1876607
theorem B2111231 : Blo 1250443 2111231 := bstep (se 1 (by rfl) ⟨1583423, by rfl⟩ : syracuseStep 2111231 = 3166847) B3166847
theorem B5076847 : Blo 1250443 5076847 := bstep (se 1 (by rfl) ⟨3807635, by rfl⟩ : syracuseStep 5076847 = 7615271) B7615271
theorem B1251327 : Blo 1250443 1251327 := bstep (se 1 (by rfl) ⟨938495, by rfl⟩ : syracuseStep 1251327 = 1876991) B1876991
theorem B6338735 : Blo 1250443 6338735 := bstep (se 1 (by rfl) ⟨4754051, by rfl⟩ : syracuseStep 6338735 = 9508103) B9508103
theorem B1251807 : Blo 1250443 1251807 := bstep (se 1 (by rfl) ⟨938855, by rfl⟩ : syracuseStep 1251807 = 1877711) B1877711
theorem B1251839 : Blo 1250443 1251839 := bstep (se 1 (by rfl) ⟨938879, by rfl⟩ : syracuseStep 1251839 = 1877759) B1877759
theorem B5077691 : Blo 1250443 5077691 := bstep (se 1 (by rfl) ⟨3808268, by rfl⟩ : syracuseStep 5077691 = 7616537) B7616537
theorem B1252079 : Blo 1250443 1252079 := bstep (se 1 (by rfl) ⟨939059, by rfl⟩ : syracuseStep 1252079 = 1878119) B1878119
theorem B1252123 : Blo 1250443 1252123 := bstep (se 1 (by rfl) ⟨939092, by rfl⟩ : syracuseStep 1252123 = 1878185) B1878185
theorem B1407847 : Blo 1250443 1407847 := bstep (se 1 (by rfl) ⟨1055885, by rfl⟩ : syracuseStep 1407847 = 2111771) B2111771
theorem B3005417 : Blo 1250443 3005417 := bstep (se 2 (by rfl) ⟨1127031, by rfl⟩ : syracuseStep 3005417 = 2254063) B2254063
theorem B2817161 : Blo 1250443 2817161 := bstep (se 2 (by rfl) ⟨1056435, by rfl⟩ : syracuseStep 2817161 = 2112871) B2112871
theorem B39067289 : Blo 1250443 39067289 := bstep (se 2 (by rfl) ⟨14650233, by rfl⟩ : syracuseStep 39067289 = 29300467) B29300467
theorem B1408927 : Blo 1250443 1408927 := bstep (se 1 (by rfl) ⟨1056695, by rfl⟩ : syracuseStep 1408927 = 2113391) B2113391
theorem B3564263 : Blo 1250443 3564263 := bstep (se 1 (by rfl) ⟨2673197, by rfl⟩ : syracuseStep 3564263 = 5346395) B5346395
theorem B1877129 : Blo 1250443 1877129 := bstep (se 2 (by rfl) ⟨703923, by rfl⟩ : syracuseStep 1877129 = 1407847) B1407847
theorem B3565289 : Blo 1250443 3565289 := bstep (se 2 (by rfl) ⟨1336983, by rfl⟩ : syracuseStep 3565289 = 2673967) B2673967
theorem B3385127 : Blo 1250443 3385127 := bstep (se 1 (by rfl) ⟨2538845, by rfl⟩ : syracuseStep 3385127 = 5077691) B5077691
theorem B5343047 : Blo 1250443 5343047 := bstep (se 1 (by rfl) ⟨4007285, by rfl⟩ : syracuseStep 5343047 = 8014571) B8014571
theorem B1878107 : Blo 1250443 1878107 := bstep (se 1 (by rfl) ⟨1408580, by rfl⟩ : syracuseStep 1878107 = 2817161) B2817161
theorem B3426401 : Blo 1250443 3426401 := bstep (se 2 (by rfl) ⟨1284900, by rfl⟩ : syracuseStep 3426401 = 2569801) B2569801
theorem B26044859 : Blo 1250443 26044859 := bstep (se 1 (by rfl) ⟨19533644, by rfl⟩ : syracuseStep 26044859 = 39067289) B39067289
theorem B6769129 : Blo 1250443 6769129 := bstep (se 2 (by rfl) ⟨2538423, by rfl⟩ : syracuseStep 6769129 = 5076847) B5076847
theorem B1878569 : Blo 1250443 1878569 := bstep (se 2 (by rfl) ⟨704463, by rfl⟩ : syracuseStep 1878569 = 1408927) B1408927
theorem B14249033 : Blo 1250443 14249033 := bstep (se 2 (by rfl) ⟨5343387, by rfl⟩ : syracuseStep 14249033 = 10686775) B10686775
theorem B2673847 : Blo 1250443 2673847 := bstep (se 1 (by rfl) ⟨2005385, by rfl⟩ : syracuseStep 2673847 = 4010771) B4010771
theorem B5344481 : Blo 1250443 5344481 := bstep (se 2 (by rfl) ⟨2004180, by rfl⟩ : syracuseStep 5344481 = 4008361) B4008361
theorem B676007453 : Blo 1250443 676007453 := bstep (se 3 (by rfl) ⟨126751397, by rfl⟩ : syracuseStep 676007453 = 253502795) B253502795
theorem B4222745 : Blo 1250443 4222745 := bstep (se 2 (by rfl) ⟨1583529, by rfl⟩ : syracuseStep 4222745 = 3167059) B3167059
theorem B45674401 : Blo 1250443 45674401 := bstep (se 2 (by rfl) ⟨17127900, by rfl⟩ : syracuseStep 45674401 = 34255801) B34255801
theorem B2003611 : Blo 1250443 2003611 := bstep (se 1 (by rfl) ⟨1502708, by rfl⟩ : syracuseStep 2003611 = 3005417) B3005417
theorem B2110441 : Blo 1250443 2110441 := bstep (se 2 (by rfl) ⟨791415, by rfl⟩ : syracuseStep 2110441 = 1582831) B1582831
theorem B3560915 : Blo 1250443 3560915 := bstep (se 1 (by rfl) ⟨2670686, by rfl⟩ : syracuseStep 3560915 = 5341373) B5341373
theorem B2815955 : Blo 1250443 2815955 := bstep (se 1 (by rfl) ⟨2111966, by rfl⟩ : syracuseStep 2815955 = 4223933) B4223933
theorem B1251295 : Blo 1250443 1251295 := bstep (se 1 (by rfl) ⟨938471, by rfl⟩ : syracuseStep 1251295 = 1876943) B1876943
theorem B2815991 : Blo 1250443 2815991 := bstep (se 1 (by rfl) ⟨2111993, by rfl⟩ : syracuseStep 2815991 = 4223987) B4223987
theorem B1251375 : Blo 1250443 1251375 := bstep (se 1 (by rfl) ⟨938531, by rfl⟩ : syracuseStep 1251375 = 1877063) B1877063
theorem B2111609 : Blo 1250443 2111609 := bstep (se 2 (by rfl) ⟨791853, by rfl⟩ : syracuseStep 2111609 = 1583707) B1583707
theorem B2111663 : Blo 1250443 2111663 := bstep (se 1 (by rfl) ⟨1583747, by rfl⟩ : syracuseStep 2111663 = 3167495) B3167495
theorem B6854867 : Blo 1250443 6854867 := bstep (se 1 (by rfl) ⟨5141150, by rfl⟩ : syracuseStep 6854867 = 10282301) B10282301
theorem B9509075 : Blo 1250443 9509075 := bstep (se 1 (by rfl) ⟨7131806, by rfl⟩ : syracuseStep 9509075 = 14263613) B14263613
theorem B2111899 : Blo 1250443 2111899 := bstep (se 1 (by rfl) ⟨1583924, by rfl⟩ : syracuseStep 2111899 = 3167849) B3167849
theorem B1407487 : Blo 1250443 1407487 := bstep (se 1 (by rfl) ⟨1055615, by rfl⟩ : syracuseStep 1407487 = 2111231) B2111231
theorem B1252047 : Blo 1250443 1252047 := bstep (se 1 (by rfl) ⟨939035, by rfl⟩ : syracuseStep 1252047 = 1878071) B1878071
theorem B4225823 : Blo 1250443 4225823 := bstep (se 1 (by rfl) ⟨3169367, by rfl⟩ : syracuseStep 4225823 = 6338735) B6338735
theorem B9510047 : Blo 1250443 9510047 := bstep (se 1 (by rfl) ⟨7132535, by rfl⟩ : syracuseStep 9510047 = 14265071) B14265071
theorem B6331931 : Blo 1250443 6331931 := bstep (se 1 (by rfl) ⟨4748948, by rfl⟩ : syracuseStep 6331931 = 9497897) B9497897
theorem B1876649 : Blo 1250443 1876649 := bstep (se 2 (by rfl) ⟨703743, by rfl⟩ : syracuseStep 1876649 = 1407487) B1407487
theorem B2671481 : Blo 1250443 2671481 := bstep (se 2 (by rfl) ⟨1001805, by rfl⟩ : syracuseStep 2671481 = 2003611) B2003611
theorem B2376859 : Blo 1250443 2376859 := bstep (se 1 (by rfl) ⟨1782644, by rfl⟩ : syracuseStep 2376859 = 3565289) B3565289
theorem B69452957 : Blo 1250443 69452957 := bstep (se 3 (by rfl) ⟨13022429, by rfl⟩ : syracuseStep 69452957 = 26044859) B26044859
theorem B1877303 : Blo 1250443 1877303 := bstep (se 1 (by rfl) ⟨1407977, by rfl⟩ : syracuseStep 1877303 = 2815955) B2815955
theorem B1877327 : Blo 1250443 1877327 := bstep (se 1 (by rfl) ⟨1407995, by rfl⟩ : syracuseStep 1877327 = 2815991) B2815991
theorem B3565129 : Blo 1250443 3565129 := bstep (se 2 (by rfl) ⟨1336923, by rfl⟩ : syracuseStep 3565129 = 2673847) B2673847
theorem B9504701 : Blo 1250443 9504701 := bstep (se 3 (by rfl) ⟨1782131, by rfl⟩ : syracuseStep 9504701 = 3564263) B3564263
theorem B4221287 : Blo 1250443 4221287 := bstep (se 1 (by rfl) ⟨3165965, by rfl⟩ : syracuseStep 4221287 = 6331931) B6331931
theorem B9137069 : Blo 1250443 9137069 := bstep (se 3 (by rfl) ⟨1713200, by rfl⟩ : syracuseStep 9137069 = 3426401) B3426401
theorem B2256751 : Blo 1250443 2256751 := bstep (se 1 (by rfl) ⟨1692563, by rfl⟩ : syracuseStep 2256751 = 3385127) B3385127
theorem B2813921 : Blo 1250443 2813921 := bstep (se 2 (by rfl) ⟨1055220, by rfl⟩ : syracuseStep 2813921 = 2110441) B2110441
theorem B9499355 : Blo 1250443 9499355 := bstep (se 1 (by rfl) ⟨7124516, by rfl⟩ : syracuseStep 9499355 = 14249033) B14249033
theorem B450671635 : Blo 1250443 450671635 := bstep (se 1 (by rfl) ⟨338003726, by rfl⟩ : syracuseStep 450671635 = 676007453) B676007453
theorem B2815163 : Blo 1250443 2815163 := bstep (se 1 (by rfl) ⟨2111372, by rfl⟩ : syracuseStep 2815163 = 4222745) B4222745
theorem B2815865 : Blo 1250443 2815865 := bstep (se 2 (by rfl) ⟨1055949, by rfl⟩ : syracuseStep 2815865 = 2111899) B2111899
theorem B14251949 : Blo 1250443 14251949 := bstep (se 3 (by rfl) ⟨2672240, by rfl⟩ : syracuseStep 14251949 = 5344481) B5344481
theorem B9025505 : Blo 1250443 9025505 := bstep (se 2 (by rfl) ⟨3384564, by rfl⟩ : syracuseStep 9025505 = 6769129) B6769129
theorem B1251419 : Blo 1250443 1251419 := bstep (se 1 (by rfl) ⟨938564, by rfl⟩ : syracuseStep 1251419 = 1877129) B1877129
theorem B2373943 : Blo 1250443 2373943 := bstep (se 1 (by rfl) ⟨1780457, by rfl⟩ : syracuseStep 2373943 = 3560915) B3560915
theorem B3562031 : Blo 1250443 3562031 := bstep (se 1 (by rfl) ⟨2671523, by rfl⟩ : syracuseStep 3562031 = 5343047) B5343047
theorem B1252071 : Blo 1250443 1252071 := bstep (se 1 (by rfl) ⟨939053, by rfl⟩ : syracuseStep 1252071 = 1878107) B1878107
theorem B1407739 : Blo 1250443 1407739 := bstep (se 1 (by rfl) ⟨1055804, by rfl⟩ : syracuseStep 1407739 = 2111609) B2111609
theorem B1407775 : Blo 1250443 1407775 := bstep (se 1 (by rfl) ⟨1055831, by rfl⟩ : syracuseStep 1407775 = 2111663) B2111663
theorem B4569911 : Blo 1250443 4569911 := bstep (se 1 (by rfl) ⟨3427433, by rfl⟩ : syracuseStep 4569911 = 6854867) B6854867
theorem B6339383 : Blo 1250443 6339383 := bstep (se 1 (by rfl) ⟨4754537, by rfl⟩ : syracuseStep 6339383 = 9509075) B9509075
theorem B1252379 : Blo 1250443 1252379 := bstep (se 1 (by rfl) ⟨939284, by rfl⟩ : syracuseStep 1252379 = 1878569) B1878569
theorem B2817215 : Blo 1250443 2817215 := bstep (se 1 (by rfl) ⟨2112911, by rfl⟩ : syracuseStep 2817215 = 4225823) B4225823
theorem B6340031 : Blo 1250443 6340031 := bstep (se 1 (by rfl) ⟨4755023, by rfl⟩ : syracuseStep 6340031 = 9510047) B9510047
theorem B60899201 : Blo 1250443 60899201 := bstep (se 2 (by rfl) ⟨22837200, by rfl⟩ : syracuseStep 60899201 = 45674401) B45674401
theorem B6332903 : Blo 1250443 6332903 := bstep (se 1 (by rfl) ⟨4749677, by rfl⟩ : syracuseStep 6332903 = 9499355) B9499355
theorem B46301971 : Blo 1250443 46301971 := bstep (se 1 (by rfl) ⟨34726478, by rfl⟩ : syracuseStep 46301971 = 69452957) B69452957
theorem B1876775 : Blo 1250443 1876775 := bstep (se 1 (by rfl) ⟨1407581, by rfl⟩ : syracuseStep 1876775 = 2815163) B2815163
theorem B1876985 : Blo 1250443 1876985 := bstep (se 2 (by rfl) ⟨703869, by rfl⟩ : syracuseStep 1876985 = 1407739) B1407739
theorem B1877033 : Blo 1250443 1877033 := bstep (se 2 (by rfl) ⟨703887, by rfl⟩ : syracuseStep 1877033 = 1407775) B1407775
theorem B1877243 : Blo 1250443 1877243 := bstep (se 1 (by rfl) ⟨1407932, by rfl⟩ : syracuseStep 1877243 = 2815865) B2815865
theorem B4753505 : Blo 1250443 4753505 := bstep (se 2 (by rfl) ⟨1782564, by rfl⟩ : syracuseStep 4753505 = 3565129) B3565129
theorem B1878143 : Blo 1250443 1878143 := bstep (se 1 (by rfl) ⟨1408607, by rfl⟩ : syracuseStep 1878143 = 2817215) B2817215
theorem B3009001 : Blo 1250443 3009001 := bstep (se 2 (by rfl) ⟨1128375, by rfl⟩ : syracuseStep 3009001 = 2256751) B2256751
theorem B3165257 : Blo 1250443 3165257 := bstep (se 2 (by rfl) ⟨1186971, by rfl⟩ : syracuseStep 3165257 = 2373943) B2373943
theorem B6336467 : Blo 1250443 6336467 := bstep (se 1 (by rfl) ⟨4752350, by rfl⟩ : syracuseStep 6336467 = 9504701) B9504701
theorem B6017003 : Blo 1250443 6017003 := bstep (se 1 (by rfl) ⟨4512752, by rfl⟩ : syracuseStep 6017003 = 9025505) B9025505
theorem B600895513 : Blo 1250443 600895513 := bstep (se 2 (by rfl) ⟨225335817, by rfl⟩ : syracuseStep 600895513 = 450671635) B450671635
theorem B2814191 : Blo 1250443 2814191 := bstep (se 1 (by rfl) ⟨2110643, by rfl⟩ : syracuseStep 2814191 = 4221287) B4221287
theorem B6091379 : Blo 1250443 6091379 := bstep (se 1 (by rfl) ⟨4568534, by rfl⟩ : syracuseStep 6091379 = 9137069) B9137069
theorem B7123949 : Blo 1250443 7123949 := bstep (se 3 (by rfl) ⟨1335740, by rfl⟩ : syracuseStep 7123949 = 2671481) B2671481
theorem B1251099 : Blo 1250443 1251099 := bstep (se 1 (by rfl) ⟨938324, by rfl⟩ : syracuseStep 1251099 = 1876649) B1876649
theorem B1251535 : Blo 1250443 1251535 := bstep (se 1 (by rfl) ⟨938651, by rfl⟩ : syracuseStep 1251535 = 1877303) B1877303
theorem B1251551 : Blo 1250443 1251551 := bstep (se 1 (by rfl) ⟨938663, by rfl⟩ : syracuseStep 1251551 = 1877327) B1877327
theorem B9501299 : Blo 1250443 9501299 := bstep (se 1 (by rfl) ⟨7125974, by rfl⟩ : syracuseStep 9501299 = 14251949) B14251949
theorem B3169145 : Blo 1250443 3169145 := bstep (se 2 (by rfl) ⟨1188429, by rfl⟩ : syracuseStep 3169145 = 2376859) B2376859
theorem B2374687 : Blo 1250443 2374687 := bstep (se 1 (by rfl) ⟨1781015, by rfl⟩ : syracuseStep 2374687 = 3562031) B3562031
theorem B3046607 : Blo 1250443 3046607 := bstep (se 1 (by rfl) ⟨2284955, by rfl⟩ : syracuseStep 3046607 = 4569911) B4569911
theorem B4226255 : Blo 1250443 4226255 := bstep (se 1 (by rfl) ⟨3169691, by rfl⟩ : syracuseStep 4226255 = 6339383) B6339383
theorem B4226687 : Blo 1250443 4226687 := bstep (se 1 (by rfl) ⟨3170015, by rfl⟩ : syracuseStep 4226687 = 6340031) B6340031
theorem B40599467 : Blo 1250443 40599467 := bstep (se 1 (by rfl) ⟨30449600, by rfl⟩ : syracuseStep 40599467 = 60899201) B60899201
theorem B1875947 : Blo 1250443 1875947 := bstep (se 1 (by rfl) ⟨1406960, by rfl⟩ : syracuseStep 1875947 = 2813921) B2813921
theorem B801194017 : Blo 1250443 801194017 := bstep (se 2 (by rfl) ⟨300447756, by rfl⟩ : syracuseStep 801194017 = 600895513) B600895513
theorem B1876127 : Blo 1250443 1876127 := bstep (se 1 (by rfl) ⟨1407095, by rfl⟩ : syracuseStep 1876127 = 2814191) B2814191
theorem B61735961 : Blo 1250443 61735961 := bstep (se 2 (by rfl) ⟨23150985, by rfl⟩ : syracuseStep 61735961 = 46301971) B46301971
theorem B6334199 : Blo 1250443 6334199 := bstep (se 1 (by rfl) ⟨4750649, by rfl⟩ : syracuseStep 6334199 = 9501299) B9501299
theorem B4221935 : Blo 1250443 4221935 := bstep (se 1 (by rfl) ⟨3166451, by rfl⟩ : syracuseStep 4221935 = 6332903) B6332903
theorem B3166249 : Blo 1250443 3166249 := bstep (se 2 (by rfl) ⟨1187343, by rfl⟩ : syracuseStep 3166249 = 2374687) B2374687
theorem B2110171 : Blo 1250443 2110171 := bstep (se 1 (by rfl) ⟨1582628, by rfl⟩ : syracuseStep 2110171 = 3165257) B3165257
theorem B4224311 : Blo 1250443 4224311 := bstep (se 1 (by rfl) ⟨3168233, by rfl⟩ : syracuseStep 4224311 = 6336467) B6336467
theorem B1250631 : Blo 1250443 1250631 := bstep (se 1 (by rfl) ⟨937973, by rfl⟩ : syracuseStep 1250631 = 1875947) B1875947
theorem B4011335 : Blo 1250443 4011335 := bstep (se 1 (by rfl) ⟨3008501, by rfl⟩ : syracuseStep 4011335 = 6017003) B6017003
theorem B4060919 : Blo 1250443 4060919 := bstep (se 1 (by rfl) ⟨3045689, by rfl⟩ : syracuseStep 4060919 = 6091379) B6091379
theorem B1251183 : Blo 1250443 1251183 := bstep (se 1 (by rfl) ⟨938387, by rfl⟩ : syracuseStep 1251183 = 1876775) B1876775
theorem B4012001 : Blo 1250443 4012001 := bstep (se 2 (by rfl) ⟨1504500, by rfl⟩ : syracuseStep 4012001 = 3009001) B3009001
theorem B4749299 : Blo 1250443 4749299 := bstep (se 1 (by rfl) ⟨3561974, by rfl⟩ : syracuseStep 4749299 = 7123949) B7123949
theorem B1251323 : Blo 1250443 1251323 := bstep (se 1 (by rfl) ⟨938492, by rfl⟩ : syracuseStep 1251323 = 1876985) B1876985
theorem B1251355 : Blo 1250443 1251355 := bstep (se 1 (by rfl) ⟨938516, by rfl⟩ : syracuseStep 1251355 = 1877033) B1877033
theorem B1251495 : Blo 1250443 1251495 := bstep (se 1 (by rfl) ⟨938621, by rfl⟩ : syracuseStep 1251495 = 1877243) B1877243
theorem B3169003 : Blo 1250443 3169003 := bstep (se 1 (by rfl) ⟨2376752, by rfl⟩ : syracuseStep 3169003 = 4753505) B4753505
theorem B1252095 : Blo 1250443 1252095 := bstep (se 1 (by rfl) ⟨939071, by rfl⟩ : syracuseStep 1252095 = 1878143) B1878143
theorem B2112763 : Blo 1250443 2112763 := bstep (se 1 (by rfl) ⟨1584572, by rfl⟩ : syracuseStep 2112763 = 3169145) B3169145
theorem B2031071 : Blo 1250443 2031071 := bstep (se 1 (by rfl) ⟨1523303, by rfl⟩ : syracuseStep 2031071 = 3046607) B3046607
theorem B2817503 : Blo 1250443 2817503 := bstep (se 1 (by rfl) ⟨2113127, by rfl⟩ : syracuseStep 2817503 = 4226255) B4226255
theorem B2817791 : Blo 1250443 2817791 := bstep (se 1 (by rfl) ⟨2113343, by rfl⟩ : syracuseStep 2817791 = 4226687) B4226687
theorem B27066311 : Blo 1250443 27066311 := bstep (se 1 (by rfl) ⟨20299733, by rfl⟩ : syracuseStep 27066311 = 40599467) B40599467
theorem B41157307 : Blo 1250443 41157307 := bstep (se 1 (by rfl) ⟨30867980, by rfl⟩ : syracuseStep 41157307 = 61735961) B61735961
theorem B5416189 : Blo 1250443 5416189 := bstep (se 3 (by rfl) ⟨1015535, by rfl⟩ : syracuseStep 5416189 = 2031071) B2031071
theorem B1878335 : Blo 1250443 1878335 := bstep (se 1 (by rfl) ⟨1408751, by rfl⟩ : syracuseStep 1878335 = 2817503) B2817503
theorem B1878527 : Blo 1250443 1878527 := bstep (se 1 (by rfl) ⟨1408895, by rfl⟩ : syracuseStep 1878527 = 2817791) B2817791
theorem B4221665 : Blo 1250443 4221665 := bstep (se 2 (by rfl) ⟨1583124, by rfl⟩ : syracuseStep 4221665 = 3166249) B3166249
theorem B2674223 : Blo 1250443 2674223 := bstep (se 1 (by rfl) ⟨2005667, by rfl⟩ : syracuseStep 2674223 = 4011335) B4011335
theorem B2813561 : Blo 1250443 2813561 := bstep (se 2 (by rfl) ⟨1055085, by rfl⟩ : syracuseStep 2813561 = 2110171) B2110171
theorem B4222799 : Blo 1250443 4222799 := bstep (se 1 (by rfl) ⟨3167099, by rfl⟩ : syracuseStep 4222799 = 6334199) B6334199
theorem B2674667 : Blo 1250443 2674667 := bstep (se 1 (by rfl) ⟨2006000, by rfl⟩ : syracuseStep 2674667 = 4012001) B4012001
theorem B3166199 : Blo 1250443 3166199 := bstep (se 1 (by rfl) ⟨2374649, by rfl⟩ : syracuseStep 3166199 = 4749299) B4749299
theorem B2814623 : Blo 1250443 2814623 := bstep (se 1 (by rfl) ⟨2110967, by rfl⟩ : syracuseStep 2814623 = 4221935) B4221935
theorem B18044207 : Blo 1250443 18044207 := bstep (se 1 (by rfl) ⟨13533155, by rfl⟩ : syracuseStep 18044207 = 27066311) B27066311
theorem B1068258689 : Blo 1250443 1068258689 := bstep (se 2 (by rfl) ⟨400597008, by rfl⟩ : syracuseStep 1068258689 = 801194017) B801194017
theorem B1250751 : Blo 1250443 1250751 := bstep (se 1 (by rfl) ⟨938063, by rfl⟩ : syracuseStep 1250751 = 1876127) B1876127
theorem B2816207 : Blo 1250443 2816207 := bstep (se 1 (by rfl) ⟨2112155, by rfl⟩ : syracuseStep 2816207 = 4224311) B4224311
theorem B4225337 : Blo 1250443 4225337 := bstep (se 2 (by rfl) ⟨1584501, by rfl⟩ : syracuseStep 4225337 = 3169003) B3169003
theorem B2817017 : Blo 1250443 2817017 := bstep (se 2 (by rfl) ⟨1056381, by rfl⟩ : syracuseStep 2817017 = 2112763) B2112763
theorem B10829117 : Blo 1250443 10829117 := bstep (se 3 (by rfl) ⟨2030459, by rfl⟩ : syracuseStep 10829117 = 4060919) B4060919
theorem B1876415 : Blo 1250443 1876415 := bstep (se 1 (by rfl) ⟨1407311, by rfl⟩ : syracuseStep 1876415 = 2814623) B2814623
theorem B712172459 : Blo 1250443 712172459 := bstep (se 1 (by rfl) ⟨534129344, by rfl⟩ : syracuseStep 712172459 = 1068258689) B1068258689
theorem B28886341 : Blo 1250443 28886341 := bstep (se 4 (by rfl) ⟨2708094, by rfl⟩ : syracuseStep 28886341 = 5416189) B5416189
theorem B1877471 : Blo 1250443 1877471 := bstep (se 1 (by rfl) ⟨1408103, by rfl⟩ : syracuseStep 1877471 = 2816207) B2816207
theorem B1878011 : Blo 1250443 1878011 := bstep (se 1 (by rfl) ⟨1408508, by rfl⟩ : syracuseStep 1878011 = 2817017) B2817017
theorem B7219411 : Blo 1250443 7219411 := bstep (se 1 (by rfl) ⟨5414558, by rfl⟩ : syracuseStep 7219411 = 10829117) B10829117
theorem B12029471 : Blo 1250443 12029471 := bstep (se 1 (by rfl) ⟨9022103, by rfl⟩ : syracuseStep 12029471 = 18044207) B18044207
theorem B2814443 : Blo 1250443 2814443 := bstep (se 1 (by rfl) ⟨2110832, by rfl⟩ : syracuseStep 2814443 = 4221665) B4221665
theorem B1782815 : Blo 1250443 1782815 := bstep (se 1 (by rfl) ⟨1337111, by rfl⟩ : syracuseStep 1782815 = 2674223) B2674223
theorem B2815199 : Blo 1250443 2815199 := bstep (se 1 (by rfl) ⟨2111399, by rfl⟩ : syracuseStep 2815199 = 4222799) B4222799
theorem B7132445 : Blo 1250443 7132445 := bstep (se 3 (by rfl) ⟨1337333, by rfl⟩ : syracuseStep 7132445 = 2674667) B2674667
theorem B2110799 : Blo 1250443 2110799 := bstep (se 1 (by rfl) ⟨1583099, by rfl⟩ : syracuseStep 2110799 = 3166199) B3166199
theorem B54876409 : Blo 1250443 54876409 := bstep (se 2 (by rfl) ⟨20578653, by rfl⟩ : syracuseStep 54876409 = 41157307) B41157307
theorem B2816891 : Blo 1250443 2816891 := bstep (se 1 (by rfl) ⟨2112668, by rfl⟩ : syracuseStep 2816891 = 4225337) B4225337
theorem B1252223 : Blo 1250443 1252223 := bstep (se 1 (by rfl) ⟨939167, by rfl⟩ : syracuseStep 1252223 = 1878335) B1878335
theorem B1252351 : Blo 1250443 1252351 := bstep (se 1 (by rfl) ⟨939263, by rfl⟩ : syracuseStep 1252351 = 1878527) B1878527
theorem B1875707 : Blo 1250443 1875707 := bstep (se 1 (by rfl) ⟨1406780, by rfl⟩ : syracuseStep 1875707 = 2813561) B2813561
theorem B1876295 : Blo 1250443 1876295 := bstep (se 1 (by rfl) ⟨1407221, by rfl⟩ : syracuseStep 1876295 = 2814443) B2814443
theorem B1876799 : Blo 1250443 1876799 := bstep (se 1 (by rfl) ⟨1407599, by rfl⟩ : syracuseStep 1876799 = 2815199) B2815199
theorem B38503525 : Blo 1250443 38503525 := bstep (se 4 (by rfl) ⟨3609705, by rfl⟩ : syracuseStep 38503525 = 7219411) B7219411
theorem B1877927 : Blo 1250443 1877927 := bstep (se 1 (by rfl) ⟨1408445, by rfl⟩ : syracuseStep 1877927 = 2816891) B2816891
theorem B4754173 : Blo 1250443 4754173 := bstep (se 3 (by rfl) ⟨891407, by rfl⟩ : syracuseStep 4754173 = 1782815) B1782815
theorem B4754963 : Blo 1250443 4754963 := bstep (se 1 (by rfl) ⟨3566222, by rfl⟩ : syracuseStep 4754963 = 7132445) B7132445
theorem B38515121 : Blo 1250443 38515121 := bstep (se 2 (by rfl) ⟨14443170, by rfl⟩ : syracuseStep 38515121 = 28886341) B28886341
theorem B1250471 : Blo 1250443 1250471 := bstep (se 1 (by rfl) ⟨937853, by rfl⟩ : syracuseStep 1250471 = 1875707) B1875707
theorem B1250943 : Blo 1250443 1250943 := bstep (se 1 (by rfl) ⟨938207, by rfl⟩ : syracuseStep 1250943 = 1876415) B1876415
theorem B1407199 : Blo 1250443 1407199 := bstep (se 1 (by rfl) ⟨1055399, by rfl⟩ : syracuseStep 1407199 = 2110799) B2110799
theorem B1251647 : Blo 1250443 1251647 := bstep (se 1 (by rfl) ⟨938735, by rfl⟩ : syracuseStep 1251647 = 1877471) B1877471
theorem B292674181 : Blo 1250443 292674181 := bstep (se 4 (by rfl) ⟨27438204, by rfl⟩ : syracuseStep 292674181 = 54876409) B54876409
theorem B1252007 : Blo 1250443 1252007 := bstep (se 1 (by rfl) ⟨939005, by rfl⟩ : syracuseStep 1252007 = 1878011) B1878011
theorem B8019647 : Blo 1250443 8019647 := bstep (se 1 (by rfl) ⟨6014735, by rfl⟩ : syracuseStep 8019647 = 12029471) B12029471
theorem B1899126557 : Blo 1250443 1899126557 := bstep (se 3 (by rfl) ⟨356086229, by rfl⟩ : syracuseStep 1899126557 = 712172459) B712172459
theorem B1876265 : Blo 1250443 1876265 := bstep (se 2 (by rfl) ⟨703599, by rfl⟩ : syracuseStep 1876265 = 1407199) B1407199
theorem B1266084371 : Blo 1250443 1266084371 := bstep (se 1 (by rfl) ⟨949563278, by rfl⟩ : syracuseStep 1266084371 = 1899126557) B1899126557
theorem B25676747 : Blo 1250443 25676747 := bstep (se 1 (by rfl) ⟨19257560, by rfl⟩ : syracuseStep 25676747 = 38515121) B38515121
theorem B5346431 : Blo 1250443 5346431 := bstep (se 1 (by rfl) ⟨4009823, by rfl⟩ : syracuseStep 5346431 = 8019647) B8019647
theorem B1250863 : Blo 1250443 1250863 := bstep (se 1 (by rfl) ⟨938147, by rfl⟩ : syracuseStep 1250863 = 1876295) B1876295
theorem B1251199 : Blo 1250443 1251199 := bstep (se 1 (by rfl) ⟨938399, by rfl⟩ : syracuseStep 1251199 = 1876799) B1876799
theorem B390232241 : Blo 1250443 390232241 := bstep (se 2 (by rfl) ⟨146337090, by rfl⟩ : syracuseStep 390232241 = 292674181) B292674181
theorem B6338897 : Blo 1250443 6338897 := bstep (se 2 (by rfl) ⟨2377086, by rfl⟩ : syracuseStep 6338897 = 4754173) B4754173
theorem B1251951 : Blo 1250443 1251951 := bstep (se 1 (by rfl) ⟨938963, by rfl⟩ : syracuseStep 1251951 = 1877927) B1877927
theorem B51338033 : Blo 1250443 51338033 := bstep (se 2 (by rfl) ⟨19251762, by rfl⟩ : syracuseStep 51338033 = 38503525) B38503525
theorem B3169975 : Blo 1250443 3169975 := bstep (se 1 (by rfl) ⟨2377481, by rfl⟩ : syracuseStep 3169975 = 4754963) B4754963
theorem B3564287 : Blo 1250443 3564287 := bstep (se 1 (by rfl) ⟨2673215, by rfl⟩ : syracuseStep 3564287 = 5346431) B5346431
theorem B260154827 : Blo 1250443 260154827 := bstep (se 1 (by rfl) ⟨195116120, by rfl⟩ : syracuseStep 260154827 = 390232241) B390232241
theorem B844056247 : Blo 1250443 844056247 := bstep (se 1 (by rfl) ⟨633042185, by rfl⟩ : syracuseStep 844056247 = 1266084371) B1266084371
theorem B17117831 : Blo 1250443 17117831 := bstep (se 1 (by rfl) ⟨12838373, by rfl⟩ : syracuseStep 17117831 = 25676747) B25676747
theorem B1250843 : Blo 1250443 1250843 := bstep (se 1 (by rfl) ⟨938132, by rfl⟩ : syracuseStep 1250843 = 1876265) B1876265
theorem B4225931 : Blo 1250443 4225931 := bstep (se 1 (by rfl) ⟨3169448, by rfl⟩ : syracuseStep 4225931 = 6338897) B6338897
theorem B34225355 : Blo 1250443 34225355 := bstep (se 1 (by rfl) ⟨25669016, by rfl⟩ : syracuseStep 34225355 = 51338033) B51338033
theorem B4226633 : Blo 1250443 4226633 := bstep (se 2 (by rfl) ⟨1584987, by rfl⟩ : syracuseStep 4226633 = 3169975) B3169975
theorem B11411887 : Blo 1250443 11411887 := bstep (se 1 (by rfl) ⟨8558915, by rfl⟩ : syracuseStep 11411887 = 17117831) B17117831
theorem B2376191 : Blo 1250443 2376191 := bstep (se 1 (by rfl) ⟨1782143, by rfl⟩ : syracuseStep 2376191 = 3564287) B3564287
theorem B22816903 : Blo 1250443 22816903 := bstep (se 1 (by rfl) ⟨17112677, by rfl⟩ : syracuseStep 22816903 = 34225355) B34225355
theorem B173436551 : Blo 1250443 173436551 := bstep (se 1 (by rfl) ⟨130077413, by rfl⟩ : syracuseStep 173436551 = 260154827) B260154827
theorem B2817287 : Blo 1250443 2817287 := bstep (se 1 (by rfl) ⟨2112965, by rfl⟩ : syracuseStep 2817287 = 4225931) B4225931
theorem B1125408329 : Blo 1250443 1125408329 := bstep (se 2 (by rfl) ⟨422028123, by rfl⟩ : syracuseStep 1125408329 = 844056247) B844056247
theorem B2817755 : Blo 1250443 2817755 := bstep (se 1 (by rfl) ⟨2113316, by rfl⟩ : syracuseStep 2817755 = 4226633) B4226633
theorem B1878191 : Blo 1250443 1878191 := bstep (se 1 (by rfl) ⟨1408643, by rfl⟩ : syracuseStep 1878191 = 2817287) B2817287
theorem B115624367 : Blo 1250443 115624367 := bstep (se 1 (by rfl) ⟨86718275, by rfl⟩ : syracuseStep 115624367 = 173436551) B173436551
theorem B1878503 : Blo 1250443 1878503 := bstep (se 1 (by rfl) ⟨1408877, by rfl⟩ : syracuseStep 1878503 = 2817755) B2817755
theorem B1584127 : Blo 1250443 1584127 := bstep (se 1 (by rfl) ⟨1188095, by rfl⟩ : syracuseStep 1584127 = 2376191) B2376191
theorem B15215849 : Blo 1250443 15215849 := bstep (se 2 (by rfl) ⟨5705943, by rfl⟩ : syracuseStep 15215849 = 11411887) B11411887
theorem B30422537 : Blo 1250443 30422537 := bstep (se 2 (by rfl) ⟨11408451, by rfl⟩ : syracuseStep 30422537 = 22816903) B22816903
theorem B750272219 : Blo 1250443 750272219 := bstep (se 1 (by rfl) ⟨562704164, by rfl⟩ : syracuseStep 750272219 = 1125408329) B1125408329
theorem B10143899 : Blo 1250443 10143899 := bstep (se 1 (by rfl) ⟨7607924, by rfl⟩ : syracuseStep 10143899 = 15215849) B15215849
theorem B500181479 : Blo 1250443 500181479 := bstep (se 1 (by rfl) ⟨375136109, by rfl⟩ : syracuseStep 500181479 = 750272219) B750272219
theorem B77082911 : Blo 1250443 77082911 := bstep (se 1 (by rfl) ⟨57812183, by rfl⟩ : syracuseStep 77082911 = 115624367) B115624367
theorem B20281691 : Blo 1250443 20281691 := bstep (se 1 (by rfl) ⟨15211268, by rfl⟩ : syracuseStep 20281691 = 30422537) B30422537
theorem B2112169 : Blo 1250443 2112169 := bstep (se 2 (by rfl) ⟨792063, by rfl⟩ : syracuseStep 2112169 = 1584127) B1584127
theorem B1252127 : Blo 1250443 1252127 := bstep (se 1 (by rfl) ⟨939095, by rfl⟩ : syracuseStep 1252127 = 1878191) B1878191
theorem B1252335 : Blo 1250443 1252335 := bstep (se 1 (by rfl) ⟨939251, by rfl⟩ : syracuseStep 1252335 = 1878503) B1878503
theorem B51388607 : Blo 1250443 51388607 := bstep (se 1 (by rfl) ⟨38541455, by rfl⟩ : syracuseStep 51388607 = 77082911) B77082911
theorem B54084509 : Blo 1250443 54084509 := bstep (se 3 (by rfl) ⟨10140845, by rfl⟩ : syracuseStep 54084509 = 20281691) B20281691
theorem B6762599 : Blo 1250443 6762599 := bstep (se 1 (by rfl) ⟨5071949, by rfl⟩ : syracuseStep 6762599 = 10143899) B10143899
theorem B2816225 : Blo 1250443 2816225 := bstep (se 2 (by rfl) ⟨1056084, by rfl⟩ : syracuseStep 2816225 = 2112169) B2112169
theorem B333454319 : Blo 1250443 333454319 := bstep (se 1 (by rfl) ⟨250090739, by rfl⟩ : syracuseStep 333454319 = 500181479) B500181479
theorem B34259071 : Blo 1250443 34259071 := bstep (se 1 (by rfl) ⟨25694303, by rfl⟩ : syracuseStep 34259071 = 51388607) B51388607
theorem B1877483 : Blo 1250443 1877483 := bstep (se 1 (by rfl) ⟨1408112, by rfl⟩ : syracuseStep 1877483 = 2816225) B2816225
theorem B4508399 : Blo 1250443 4508399 := bstep (se 1 (by rfl) ⟨3381299, by rfl⟩ : syracuseStep 4508399 = 6762599) B6762599
theorem B36056339 : Blo 1250443 36056339 := bstep (se 1 (by rfl) ⟨27042254, by rfl⟩ : syracuseStep 36056339 = 54084509) B54084509
theorem B222302879 : Blo 1250443 222302879 := bstep (se 1 (by rfl) ⟨166727159, by rfl⟩ : syracuseStep 222302879 = 333454319) B333454319
theorem B45678761 : Blo 1250443 45678761 := bstep (se 2 (by rfl) ⟨17129535, by rfl⟩ : syracuseStep 45678761 = 34259071) B34259071
theorem B148201919 : Blo 1250443 148201919 := bstep (se 1 (by rfl) ⟨111151439, by rfl⟩ : syracuseStep 148201919 = 222302879) B222302879
theorem B24037559 : Blo 1250443 24037559 := bstep (se 1 (by rfl) ⟨18028169, by rfl⟩ : syracuseStep 24037559 = 36056339) B36056339
theorem B1251655 : Blo 1250443 1251655 := bstep (se 1 (by rfl) ⟨938741, by rfl⟩ : syracuseStep 1251655 = 1877483) B1877483
theorem B3005599 : Blo 1250443 3005599 := bstep (se 1 (by rfl) ⟨2254199, by rfl⟩ : syracuseStep 3005599 = 4508399) B4508399
theorem B16025039 : Blo 1250443 16025039 := bstep (se 1 (by rfl) ⟨12018779, by rfl⟩ : syracuseStep 16025039 = 24037559) B24037559
theorem B4007465 : Blo 1250443 4007465 := bstep (se 2 (by rfl) ⟨1502799, by rfl⟩ : syracuseStep 4007465 = 3005599) B3005599
theorem B30452507 : Blo 1250443 30452507 := bstep (se 1 (by rfl) ⟨22839380, by rfl⟩ : syracuseStep 30452507 = 45678761) B45678761
theorem B98801279 : Blo 1250443 98801279 := bstep (se 1 (by rfl) ⟨74100959, by rfl⟩ : syracuseStep 98801279 = 148201919) B148201919
theorem B10683359 : Blo 1250443 10683359 := bstep (se 1 (by rfl) ⟨8012519, by rfl⟩ : syracuseStep 10683359 = 16025039) B16025039
theorem B2671643 : Blo 1250443 2671643 := bstep (se 1 (by rfl) ⟨2003732, by rfl⟩ : syracuseStep 2671643 = 4007465) B4007465
theorem B20301671 : Blo 1250443 20301671 := bstep (se 1 (by rfl) ⟨15226253, by rfl⟩ : syracuseStep 20301671 = 30452507) B30452507
theorem B65867519 : Blo 1250443 65867519 := bstep (se 1 (by rfl) ⟨49400639, by rfl⟩ : syracuseStep 65867519 = 98801279) B98801279
theorem B13534447 : Blo 1250443 13534447 := bstep (se 1 (by rfl) ⟨10150835, by rfl⟩ : syracuseStep 13534447 = 20301671) B20301671
theorem B175646717 : Blo 1250443 175646717 := bstep (se 3 (by rfl) ⟨32933759, by rfl⟩ : syracuseStep 175646717 = 65867519) B65867519
theorem B7122239 : Blo 1250443 7122239 := bstep (se 1 (by rfl) ⟨5341679, by rfl⟩ : syracuseStep 7122239 = 10683359) B10683359
theorem B7124381 : Blo 1250443 7124381 := bstep (se 3 (by rfl) ⟨1335821, by rfl⟩ : syracuseStep 7124381 = 2671643) B2671643
theorem B117097811 : Blo 1250443 117097811 := bstep (se 1 (by rfl) ⟨87823358, by rfl⟩ : syracuseStep 117097811 = 175646717) B175646717
theorem B4748159 : Blo 1250443 4748159 := bstep (se 1 (by rfl) ⟨3561119, by rfl⟩ : syracuseStep 4748159 = 7122239) B7122239
theorem B4749587 : Blo 1250443 4749587 := bstep (se 1 (by rfl) ⟨3562190, by rfl⟩ : syracuseStep 4749587 = 7124381) B7124381
theorem B18045929 : Blo 1250443 18045929 := bstep (se 2 (by rfl) ⟨6767223, by rfl⟩ : syracuseStep 18045929 = 13534447) B13534447
theorem B3165439 : Blo 1250443 3165439 := bstep (se 1 (by rfl) ⟨2374079, by rfl⟩ : syracuseStep 3165439 = 4748159) B4748159
theorem B78065207 : Blo 1250443 78065207 := bstep (se 1 (by rfl) ⟨58548905, by rfl⟩ : syracuseStep 78065207 = 117097811) B117097811
theorem B3166391 : Blo 1250443 3166391 := bstep (se 1 (by rfl) ⟨2374793, by rfl⟩ : syracuseStep 3166391 = 4749587) B4749587
theorem B12030619 : Blo 1250443 12030619 := bstep (se 1 (by rfl) ⟨9022964, by rfl⟩ : syracuseStep 12030619 = 18045929) B18045929
theorem B16040825 : Blo 1250443 16040825 := bstep (se 2 (by rfl) ⟨6015309, by rfl⟩ : syracuseStep 16040825 = 12030619) B12030619
theorem B4220585 : Blo 1250443 4220585 := bstep (se 2 (by rfl) ⟨1582719, by rfl⟩ : syracuseStep 4220585 = 3165439) B3165439
theorem B2110927 : Blo 1250443 2110927 := bstep (se 1 (by rfl) ⟨1583195, by rfl⟩ : syracuseStep 2110927 = 3166391) B3166391
theorem B52043471 : Blo 1250443 52043471 := bstep (se 1 (by rfl) ⟨39032603, by rfl⟩ : syracuseStep 52043471 = 78065207) B78065207
theorem B34695647 : Blo 1250443 34695647 := bstep (se 1 (by rfl) ⟨26021735, by rfl⟩ : syracuseStep 34695647 = 52043471) B52043471
theorem B10693883 : Blo 1250443 10693883 := bstep (se 1 (by rfl) ⟨8020412, by rfl⟩ : syracuseStep 10693883 = 16040825) B16040825
theorem B2813723 : Blo 1250443 2813723 := bstep (se 1 (by rfl) ⟨2110292, by rfl⟩ : syracuseStep 2813723 = 4220585) B4220585
theorem B2814569 : Blo 1250443 2814569 := bstep (se 2 (by rfl) ⟨1055463, by rfl⟩ : syracuseStep 2814569 = 2110927) B2110927
theorem B1876379 : Blo 1250443 1876379 := bstep (se 1 (by rfl) ⟨1407284, by rfl⟩ : syracuseStep 1876379 = 2814569) B2814569
theorem B7129255 : Blo 1250443 7129255 := bstep (se 1 (by rfl) ⟨5346941, by rfl⟩ : syracuseStep 7129255 = 10693883) B10693883
theorem B23130431 : Blo 1250443 23130431 := bstep (se 1 (by rfl) ⟨17347823, by rfl⟩ : syracuseStep 23130431 = 34695647) B34695647
theorem B1875815 : Blo 1250443 1875815 := bstep (se 1 (by rfl) ⟨1406861, by rfl⟩ : syracuseStep 1875815 = 2813723) B2813723
theorem B15420287 : Blo 1250443 15420287 := bstep (se 1 (by rfl) ⟨11565215, by rfl⟩ : syracuseStep 15420287 = 23130431) B23130431
theorem B9505673 : Blo 1250443 9505673 := bstep (se 2 (by rfl) ⟨3564627, by rfl⟩ : syracuseStep 9505673 = 7129255) B7129255
theorem B1250543 : Blo 1250443 1250543 := bstep (se 1 (by rfl) ⟨937907, by rfl⟩ : syracuseStep 1250543 = 1875815) B1875815
theorem B1250919 : Blo 1250443 1250919 := bstep (se 1 (by rfl) ⟨938189, by rfl⟩ : syracuseStep 1250919 = 1876379) B1876379
theorem B6337115 : Blo 1250443 6337115 := bstep (se 1 (by rfl) ⟨4752836, by rfl⟩ : syracuseStep 6337115 = 9505673) B9505673
theorem B10280191 : Blo 1250443 10280191 := bstep (se 1 (by rfl) ⟨7710143, by rfl⟩ : syracuseStep 10280191 = 15420287) B15420287
theorem B13706921 : Blo 1250443 13706921 := bstep (se 2 (by rfl) ⟨5140095, by rfl⟩ : syracuseStep 13706921 = 10280191) B10280191
theorem B4224743 : Blo 1250443 4224743 := bstep (se 1 (by rfl) ⟨3168557, by rfl⟩ : syracuseStep 4224743 = 6337115) B6337115
theorem B9137947 : Blo 1250443 9137947 := bstep (se 1 (by rfl) ⟨6853460, by rfl⟩ : syracuseStep 9137947 = 13706921) B13706921
theorem B2816495 : Blo 1250443 2816495 := bstep (se 1 (by rfl) ⟨2112371, by rfl⟩ : syracuseStep 2816495 = 4224743) B4224743
theorem B1877663 : Blo 1250443 1877663 := bstep (se 1 (by rfl) ⟨1408247, by rfl⟩ : syracuseStep 1877663 = 2816495) B2816495
theorem B12183929 : Blo 1250443 12183929 := bstep (se 2 (by rfl) ⟨4568973, by rfl⟩ : syracuseStep 12183929 = 9137947) B9137947
theorem B8122619 : Blo 1250443 8122619 := bstep (se 1 (by rfl) ⟨6091964, by rfl⟩ : syracuseStep 8122619 = 12183929) B12183929
theorem B1251775 : Blo 1250443 1251775 := bstep (se 1 (by rfl) ⟨938831, by rfl⟩ : syracuseStep 1251775 = 1877663) B1877663
theorem B21660317 : Blo 1250443 21660317 := bstep (se 3 (by rfl) ⟨4061309, by rfl⟩ : syracuseStep 21660317 = 8122619) B8122619
theorem B14440211 : Blo 1250443 14440211 := bstep (se 1 (by rfl) ⟨10830158, by rfl⟩ : syracuseStep 14440211 = 21660317) B21660317
theorem B9626807 : Blo 1250443 9626807 := bstep (se 1 (by rfl) ⟨7220105, by rfl⟩ : syracuseStep 9626807 = 14440211) B14440211
theorem B25671485 : Blo 1250443 25671485 := bstep (se 3 (by rfl) ⟨4813403, by rfl⟩ : syracuseStep 25671485 = 9626807) B9626807
theorem B17114323 : Blo 1250443 17114323 := bstep (se 1 (by rfl) ⟨12835742, by rfl⟩ : syracuseStep 17114323 = 25671485) B25671485
theorem B22819097 : Blo 1250443 22819097 := bstep (se 2 (by rfl) ⟨8557161, by rfl⟩ : syracuseStep 22819097 = 17114323) B17114323
theorem B15212731 : Blo 1250443 15212731 := bstep (se 1 (by rfl) ⟨11409548, by rfl⟩ : syracuseStep 15212731 = 22819097) B22819097
theorem B20283641 : Blo 1250443 20283641 := bstep (se 2 (by rfl) ⟨7606365, by rfl⟩ : syracuseStep 20283641 = 15212731) B15212731
theorem B13522427 : Blo 1250443 13522427 := bstep (se 1 (by rfl) ⟨10141820, by rfl⟩ : syracuseStep 13522427 = 20283641) B20283641
theorem B9014951 : Blo 1250443 9014951 := bstep (se 1 (by rfl) ⟨6761213, by rfl⟩ : syracuseStep 9014951 = 13522427) B13522427
theorem B6009967 : Blo 1250443 6009967 := bstep (se 1 (by rfl) ⟨4507475, by rfl⟩ : syracuseStep 6009967 = 9014951) B9014951
theorem B8013289 : Blo 1250443 8013289 := bstep (se 2 (by rfl) ⟨3004983, by rfl⟩ : syracuseStep 8013289 = 6009967) B6009967
theorem B10684385 : Blo 1250443 10684385 := bstep (se 2 (by rfl) ⟨4006644, by rfl⟩ : syracuseStep 10684385 = 8013289) B8013289
theorem B7122923 : Blo 1250443 7122923 := bstep (se 1 (by rfl) ⟨5342192, by rfl⟩ : syracuseStep 7122923 = 10684385) B10684385
theorem B4748615 : Blo 1250443 4748615 := bstep (se 1 (by rfl) ⟨3561461, by rfl⟩ : syracuseStep 4748615 = 7122923) B7122923
theorem B3165743 : Blo 1250443 3165743 := bstep (se 1 (by rfl) ⟨2374307, by rfl⟩ : syracuseStep 3165743 = 4748615) B4748615
theorem B2110495 : Blo 1250443 2110495 := bstep (se 1 (by rfl) ⟨1582871, by rfl⟩ : syracuseStep 2110495 = 3165743) B3165743
theorem B2813993 : Blo 1250443 2813993 := bstep (se 2 (by rfl) ⟨1055247, by rfl⟩ : syracuseStep 2813993 = 2110495) B2110495
theorem B1875995 : Blo 1250443 1875995 := bstep (se 1 (by rfl) ⟨1406996, by rfl⟩ : syracuseStep 1875995 = 2813993) B2813993
theorem B1250663 : Blo 1250443 1250663 := bstep (se 1 (by rfl) ⟨937997, by rfl⟩ : syracuseStep 1250663 = 1875995) B1875995

theorem C0 (j : ℕ) (h1 : 312610 ≤ j) (h2 : j ≤ 313110) : Blo 1250443 (4 * j + 3) := by
  interval_cases j
  · exact B1250443
  · exact B1250447
  · exact B1250451
  · exact B1250455
  · exact B1250459
  · exact B1250463
  · exact B1250467
  · exact B1250471
  · exact B1250475
  · exact B1250479
  · exact B1250483
  · exact B1250487
  · exact B1250491
  · exact B1250495
  · exact B1250499
  · exact B1250503
  · exact B1250507
  · exact B1250511
  · exact B1250515
  · exact B1250519
  · exact B1250523
  · exact B1250527
  · exact B1250531
  · exact B1250535
  · exact B1250539
  · exact B1250543
  · exact B1250547
  · exact B1250551
  · exact B1250555
  · exact B1250559
  · exact B1250563
  · exact B1250567
  · exact B1250571
  · exact B1250575
  · exact B1250579
  · exact B1250583
  · exact B1250587
  · exact B1250591
  · exact B1250595
  · exact B1250599
  · exact B1250603
  · exact B1250607
  · exact B1250611
  · exact B1250615
  · exact B1250619
  · exact B1250623
  · exact B1250627
  · exact B1250631
  · exact B1250635
  · exact B1250639
  · exact B1250643
  · exact B1250647
  · exact B1250651
  · exact B1250655
  · exact B1250659
  · exact B1250663
  · exact B1250667
  · exact B1250671
  · exact B1250675
  · exact B1250679
  · exact B1250683
  · exact B1250687
  · exact B1250691
  · exact B1250695
  · exact B1250699
  · exact B1250703
  · exact B1250707
  · exact B1250711
  · exact B1250715
  · exact B1250719
  · exact B1250723
  · exact B1250727
  · exact B1250731
  · exact B1250735
  · exact B1250739
  · exact B1250743
  · exact B1250747
  · exact B1250751
  · exact B1250755
  · exact B1250759
  · exact B1250763
  · exact B1250767
  · exact B1250771
  · exact B1250775
  · exact B1250779
  · exact B1250783
  · exact B1250787
  · exact B1250791
  · exact B1250795
  · exact B1250799
  · exact B1250803
  · exact B1250807
  · exact B1250811
  · exact B1250815
  · exact B1250819
  · exact B1250823
  · exact B1250827
  · exact B1250831
  · exact B1250835
  · exact B1250839
  · exact B1250843
  · exact B1250847
  · exact B1250851
  · exact B1250855
  · exact B1250859
  · exact B1250863
  · exact B1250867
  · exact B1250871
  · exact B1250875
  · exact B1250879
  · exact B1250883
  · exact B1250887
  · exact B1250891
  · exact B1250895
  · exact B1250899
  · exact B1250903
  · exact B1250907
  · exact B1250911
  · exact B1250915
  · exact B1250919
  · exact B1250923
  · exact B1250927
  · exact B1250931
  · exact B1250935
  · exact B1250939
  · exact B1250943
  · exact B1250947
  · exact B1250951
  · exact B1250955
  · exact B1250959
  · exact B1250963
  · exact B1250967
  · exact B1250971
  · exact B1250975
  · exact B1250979
  · exact B1250983
  · exact B1250987
  · exact B1250991
  · exact B1250995
  · exact B1250999
  · exact B1251003
  · exact B1251007
  · exact B1251011
  · exact B1251015
  · exact B1251019
  · exact B1251023
  · exact B1251027
  · exact B1251031
  · exact B1251035
  · exact B1251039
  · exact B1251043
  · exact B1251047
  · exact B1251051
  · exact B1251055
  · exact B1251059
  · exact B1251063
  · exact B1251067
  · exact B1251071
  · exact B1251075
  · exact B1251079
  · exact B1251083
  · exact B1251087
  · exact B1251091
  · exact B1251095
  · exact B1251099
  · exact B1251103
  · exact B1251107
  · exact B1251111
  · exact B1251115
  · exact B1251119
  · exact B1251123
  · exact B1251127
  · exact B1251131
  · exact B1251135
  · exact B1251139
  · exact B1251143
  · exact B1251147
  · exact B1251151
  · exact B1251155
  · exact B1251159
  · exact B1251163
  · exact B1251167
  · exact B1251171
  · exact B1251175
  · exact B1251179
  · exact B1251183
  · exact B1251187
  · exact B1251191
  · exact B1251195
  · exact B1251199
  · exact B1251203
  · exact B1251207
  · exact B1251211
  · exact B1251215
  · exact B1251219
  · exact B1251223
  · exact B1251227
  · exact B1251231
  · exact B1251235
  · exact B1251239
  · exact B1251243
  · exact B1251247
  · exact B1251251
  · exact B1251255
  · exact B1251259
  · exact B1251263
  · exact B1251267
  · exact B1251271
  · exact B1251275
  · exact B1251279
  · exact B1251283
  · exact B1251287
  · exact B1251291
  · exact B1251295
  · exact B1251299
  · exact B1251303
  · exact B1251307
  · exact B1251311
  · exact B1251315
  · exact B1251319
  · exact B1251323
  · exact B1251327
  · exact B1251331
  · exact B1251335
  · exact B1251339
  · exact B1251343
  · exact B1251347
  · exact B1251351
  · exact B1251355
  · exact B1251359
  · exact B1251363
  · exact B1251367
  · exact B1251371
  · exact B1251375
  · exact B1251379
  · exact B1251383
  · exact B1251387
  · exact B1251391
  · exact B1251395
  · exact B1251399
  · exact B1251403
  · exact B1251407
  · exact B1251411
  · exact B1251415
  · exact B1251419
  · exact B1251423
  · exact B1251427
  · exact B1251431
  · exact B1251435
  · exact B1251439
  · exact B1251443
  · exact B1251447
  · exact B1251451
  · exact B1251455
  · exact B1251459
  · exact B1251463
  · exact B1251467
  · exact B1251471
  · exact B1251475
  · exact B1251479
  · exact B1251483
  · exact B1251487
  · exact B1251491
  · exact B1251495
  · exact B1251499
  · exact B1251503
  · exact B1251507
  · exact B1251511
  · exact B1251515
  · exact B1251519
  · exact B1251523
  · exact B1251527
  · exact B1251531
  · exact B1251535
  · exact B1251539
  · exact B1251543
  · exact B1251547
  · exact B1251551
  · exact B1251555
  · exact B1251559
  · exact B1251563
  · exact B1251567
  · exact B1251571
  · exact B1251575
  · exact B1251579
  · exact B1251583
  · exact B1251587
  · exact B1251591
  · exact B1251595
  · exact B1251599
  · exact B1251603
  · exact B1251607
  · exact B1251611
  · exact B1251615
  · exact B1251619
  · exact B1251623
  · exact B1251627
  · exact B1251631
  · exact B1251635
  · exact B1251639
  · exact B1251643
  · exact B1251647
  · exact B1251651
  · exact B1251655
  · exact B1251659
  · exact B1251663
  · exact B1251667
  · exact B1251671
  · exact B1251675
  · exact B1251679
  · exact B1251683
  · exact B1251687
  · exact B1251691
  · exact B1251695
  · exact B1251699
  · exact B1251703
  · exact B1251707
  · exact B1251711
  · exact B1251715
  · exact B1251719
  · exact B1251723
  · exact B1251727
  · exact B1251731
  · exact B1251735
  · exact B1251739
  · exact B1251743
  · exact B1251747
  · exact B1251751
  · exact B1251755
  · exact B1251759
  · exact B1251763
  · exact B1251767
  · exact B1251771
  · exact B1251775
  · exact B1251779
  · exact B1251783
  · exact B1251787
  · exact B1251791
  · exact B1251795
  · exact B1251799
  · exact B1251803
  · exact B1251807
  · exact B1251811
  · exact B1251815
  · exact B1251819
  · exact B1251823
  · exact B1251827
  · exact B1251831
  · exact B1251835
  · exact B1251839
  · exact B1251843
  · exact B1251847
  · exact B1251851
  · exact B1251855
  · exact B1251859
  · exact B1251863
  · exact B1251867
  · exact B1251871
  · exact B1251875
  · exact B1251879
  · exact B1251883
  · exact B1251887
  · exact B1251891
  · exact B1251895
  · exact B1251899
  · exact B1251903
  · exact B1251907
  · exact B1251911
  · exact B1251915
  · exact B1251919
  · exact B1251923
  · exact B1251927
  · exact B1251931
  · exact B1251935
  · exact B1251939
  · exact B1251943
  · exact B1251947
  · exact B1251951
  · exact B1251955
  · exact B1251959
  · exact B1251963
  · exact B1251967
  · exact B1251971
  · exact B1251975
  · exact B1251979
  · exact B1251983
  · exact B1251987
  · exact B1251991
  · exact B1251995
  · exact B1251999
  · exact B1252003
  · exact B1252007
  · exact B1252011
  · exact B1252015
  · exact B1252019
  · exact B1252023
  · exact B1252027
  · exact B1252031
  · exact B1252035
  · exact B1252039
  · exact B1252043
  · exact B1252047
  · exact B1252051
  · exact B1252055
  · exact B1252059
  · exact B1252063
  · exact B1252067
  · exact B1252071
  · exact B1252075
  · exact B1252079
  · exact B1252083
  · exact B1252087
  · exact B1252091
  · exact B1252095
  · exact B1252099
  · exact B1252103
  · exact B1252107
  · exact B1252111
  · exact B1252115
  · exact B1252119
  · exact B1252123
  · exact B1252127
  · exact B1252131
  · exact B1252135
  · exact B1252139
  · exact B1252143
  · exact B1252147
  · exact B1252151
  · exact B1252155
  · exact B1252159
  · exact B1252163
  · exact B1252167
  · exact B1252171
  · exact B1252175
  · exact B1252179
  · exact B1252183
  · exact B1252187
  · exact B1252191
  · exact B1252195
  · exact B1252199
  · exact B1252203
  · exact B1252207
  · exact B1252211
  · exact B1252215
  · exact B1252219
  · exact B1252223
  · exact B1252227
  · exact B1252231
  · exact B1252235
  · exact B1252239
  · exact B1252243
  · exact B1252247
  · exact B1252251
  · exact B1252255
  · exact B1252259
  · exact B1252263
  · exact B1252267
  · exact B1252271
  · exact B1252275
  · exact B1252279
  · exact B1252283
  · exact B1252287
  · exact B1252291
  · exact B1252295
  · exact B1252299
  · exact B1252303
  · exact B1252307
  · exact B1252311
  · exact B1252315
  · exact B1252319
  · exact B1252323
  · exact B1252327
  · exact B1252331
  · exact B1252335
  · exact B1252339
  · exact B1252343
  · exact B1252347
  · exact B1252351
  · exact B1252355
  · exact B1252359
  · exact B1252363
  · exact B1252367
  · exact B1252371
  · exact B1252375
  · exact B1252379
  · exact B1252383
  · exact B1252387
  · exact B1252391
  · exact B1252395
  · exact B1252399
  · exact B1252403
  · exact B1252407
  · exact B1252411
  · exact B1252415
  · exact B1252419
  · exact B1252423
  · exact B1252427
  · exact B1252431
  · exact B1252435
  · exact B1252439
  · exact B1252443

theorem solution (m : ℕ) (hlo : 1250443 ≤ m) (hhi : m ≤ 1252443) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 312610 ≤ j := by omega
    have hj2 : j ≤ 313110 := by omega
    have hb : Blo 1250443 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
