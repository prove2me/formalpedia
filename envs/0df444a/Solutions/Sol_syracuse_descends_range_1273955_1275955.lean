-- Prove2me | solution 1 for syracuse_descends_range_1273955_1275955
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:29.902917+00:00
-- url     : https://prove2.me/submissions/b310f720-7c92-4831-a7e6-7d314ba89ff9

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


theorem B1433605 : Blo 1273955 1433605 := bbase (se 4 (by rfl) ⟨134400, by rfl⟩ : syracuseStep 1433605 = 268801) (by norm_num)
theorem B2867237 : Blo 1273955 2867237 := bbase (se 4 (by rfl) ⟨268803, by rfl⟩ : syracuseStep 2867237 = 537607) (by norm_num)
theorem B1433641 : Blo 1273955 1433641 := bbase (se 2 (by rfl) ⟨537615, by rfl⟩ : syracuseStep 1433641 = 1075231) (by norm_num)
theorem B5447749 : Blo 1273955 5447749 := bbase (se 4 (by rfl) ⟨510726, by rfl⟩ : syracuseStep 5447749 = 1021453) (by norm_num)
theorem B1433677 : Blo 1273955 1433677 := bbase (se 3 (by rfl) ⟨268814, by rfl⟩ : syracuseStep 1433677 = 537629) (by norm_num)
theorem B2867309 : Blo 1273955 2867309 := bbase (se 3 (by rfl) ⟨537620, by rfl⟩ : syracuseStep 2867309 = 1075241) (by norm_num)
theorem B1433713 : Blo 1273955 1433713 := bbase (se 2 (by rfl) ⟨537642, by rfl⟩ : syracuseStep 1433713 = 1075285) (by norm_num)
theorem B1613945 : Blo 1273955 1613945 := bbase (se 2 (by rfl) ⟨605229, by rfl⟩ : syracuseStep 1613945 = 1210459) (by norm_num)
theorem B3227789 : Blo 1273955 3227789 := bbase (se 3 (by rfl) ⟨605210, by rfl⟩ : syracuseStep 3227789 = 1210421) (by norm_num)
theorem B1532045 : Blo 1273955 1532045 := bbase (se 3 (by rfl) ⟨287258, by rfl⟩ : syracuseStep 1532045 = 574517) (by norm_num)
theorem B1433749 : Blo 1273955 1433749 := bbase (se 6 (by rfl) ⟨33603, by rfl⟩ : syracuseStep 1433749 = 67207) (by norm_num)
theorem B1614001 : Blo 1273955 1614001 := bbase (se 2 (by rfl) ⟨605250, by rfl⟩ : syracuseStep 1614001 = 1210501) (by norm_num)
theorem B2867381 : Blo 1273955 2867381 := bbase (se 5 (by rfl) ⟨134408, by rfl⟩ : syracuseStep 2867381 = 268817) (by norm_num)
theorem B4841653 : Blo 1273955 4841653 := bbase (se 5 (by rfl) ⟨226952, by rfl⟩ : syracuseStep 4841653 = 453905) (by norm_num)
theorem B1433785 : Blo 1273955 1433785 := bbase (se 2 (by rfl) ⟨537669, by rfl⟩ : syracuseStep 1433785 = 1075339) (by norm_num)
theorem B1433821 : Blo 1273955 1433821 := bbase (se 3 (by rfl) ⟨268841, by rfl⟩ : syracuseStep 1433821 = 537683) (by norm_num)
theorem B1310957 : Blo 1273955 1310957 := bbase (se 3 (by rfl) ⟨245804, by rfl⟩ : syracuseStep 1310957 = 491609) (by norm_num)
theorem B4301045 : Blo 1273955 4301045 := bbase (se 5 (by rfl) ⟨201611, by rfl⟩ : syracuseStep 4301045 = 403223) (by norm_num)
theorem B2867453 : Blo 1273955 2867453 := bbase (se 3 (by rfl) ⟨537647, by rfl⟩ : syracuseStep 2867453 = 1075295) (by norm_num)
theorem B1433857 : Blo 1273955 1433857 := bbase (se 2 (by rfl) ⟨537696, by rfl⟩ : syracuseStep 1433857 = 1075393) (by norm_num)
theorem B1614097 : Blo 1273955 1614097 := bbase (se 2 (by rfl) ⟨605286, by rfl⟩ : syracuseStep 1614097 = 1210573) (by norm_num)
theorem B7266581 : Blo 1273955 7266581 := bbase (se 6 (by rfl) ⟨170310, by rfl⟩ : syracuseStep 7266581 = 340621) (by norm_num)
theorem B1433893 : Blo 1273955 1433893 := bbase (se 4 (by rfl) ⟨134427, by rfl⟩ : syracuseStep 1433893 = 268855) (by norm_num)
theorem B2867525 : Blo 1273955 2867525 := bbase (se 4 (by rfl) ⟨268830, by rfl⟩ : syracuseStep 2867525 = 537661) (by norm_num)
theorem B1433929 : Blo 1273955 1433929 := bbase (se 2 (by rfl) ⟨537723, by rfl⟩ : syracuseStep 1433929 = 1075447) (by norm_num)
theorem B1532233 : Blo 1273955 1532233 := bbase (se 2 (by rfl) ⟨574587, by rfl⟩ : syracuseStep 1532233 = 1149175) (by norm_num)
theorem B1433965 : Blo 1273955 1433965 := bbase (se 3 (by rfl) ⟨268868, by rfl⟩ : syracuseStep 1433965 = 537737) (by norm_num)
theorem B2867597 : Blo 1273955 2867597 := bbase (se 3 (by rfl) ⟨537674, by rfl⟩ : syracuseStep 2867597 = 1075349) (by norm_num)
theorem B1434001 : Blo 1273955 1434001 := bbase (se 2 (by rfl) ⟨537750, by rfl⟩ : syracuseStep 1434001 = 1075501) (by norm_num)
theorem B7258517 : Blo 1273955 7258517 := bbase (se 6 (by rfl) ⟨170121, by rfl⟩ : syracuseStep 7258517 = 340243) (by norm_num)
theorem B1434037 : Blo 1273955 1434037 := bbase (se 5 (by rfl) ⟨67220, by rfl⟩ : syracuseStep 1434037 = 134441) (by norm_num)
theorem B1614269 : Blo 1273955 1614269 := bbase (se 3 (by rfl) ⟨302675, by rfl⟩ : syracuseStep 1614269 = 605351) (by norm_num)
theorem B2867669 : Blo 1273955 2867669 := bbase (se 7 (by rfl) ⟨33605, by rfl⟩ : syracuseStep 2867669 = 67211) (by norm_num)
theorem B1434073 : Blo 1273955 1434073 := bbase (se 2 (by rfl) ⟨537777, by rfl⟩ : syracuseStep 1434073 = 1075555) (by norm_num)
theorem B4841957 : Blo 1273955 4841957 := bbase (se 4 (by rfl) ⟨453933, by rfl⟩ : syracuseStep 4841957 = 907867) (by norm_num)
theorem B3228133 : Blo 1273955 3228133 := bbase (se 4 (by rfl) ⟨302637, by rfl⟩ : syracuseStep 3228133 = 605275) (by norm_num)
theorem B1614325 : Blo 1273955 1614325 := bbase (se 5 (by rfl) ⟨75671, by rfl⟩ : syracuseStep 1614325 = 151343) (by norm_num)
theorem B1434109 : Blo 1273955 1434109 := bbase (se 3 (by rfl) ⟨268895, by rfl⟩ : syracuseStep 1434109 = 537791) (by norm_num)
theorem B2867741 : Blo 1273955 2867741 := bbase (se 3 (by rfl) ⟨537701, by rfl⟩ : syracuseStep 2867741 = 1075403) (by norm_num)
theorem B1434145 : Blo 1273955 1434145 := bbase (se 2 (by rfl) ⟨537804, by rfl⟩ : syracuseStep 1434145 = 1075609) (by norm_num)
theorem B1532449 : Blo 1273955 1532449 := bbase (se 2 (by rfl) ⟨574668, by rfl⟩ : syracuseStep 1532449 = 1149337) (by norm_num)
theorem B3269173 : Blo 1273955 3269173 := bbase (se 5 (by rfl) ⟨153242, by rfl⟩ : syracuseStep 3269173 = 306485) (by norm_num)
theorem B6455861 : Blo 1273955 6455861 := bbase (se 5 (by rfl) ⟨302618, by rfl⟩ : syracuseStep 6455861 = 605237) (by norm_num)
theorem B1434181 : Blo 1273955 1434181 := bbase (se 4 (by rfl) ⟨134454, by rfl⟩ : syracuseStep 1434181 = 268909) (by norm_num)
theorem B3064397 : Blo 1273955 3064397 := bbase (se 3 (by rfl) ⟨574574, by rfl⟩ : syracuseStep 3064397 = 1149149) (by norm_num)
theorem B27927125 : Blo 1273955 27927125 := bbase (se 8 (by rfl) ⟨163635, by rfl⟩ : syracuseStep 27927125 = 327271) (by norm_num)
theorem B3228245 : Blo 1273955 3228245 := bbase (se 8 (by rfl) ⟨18915, by rfl⟩ : syracuseStep 3228245 = 37831) (by norm_num)
theorem B1614421 : Blo 1273955 1614421 := bbase (se 8 (by rfl) ⟨9459, by rfl⟩ : syracuseStep 1614421 = 18919) (by norm_num)
theorem B1360481 : Blo 1273955 1360481 := bbase (se 2 (by rfl) ⟨510180, by rfl⟩ : syracuseStep 1360481 = 1020361) (by norm_num)
theorem B2867813 : Blo 1273955 2867813 := bbase (se 4 (by rfl) ⟨268857, by rfl⟩ : syracuseStep 2867813 = 537715) (by norm_num)
theorem B1434217 : Blo 1273955 1434217 := bbase (se 2 (by rfl) ⟨537831, by rfl⟩ : syracuseStep 1434217 = 1075663) (by norm_num)
theorem B1434253 : Blo 1273955 1434253 := bbase (se 3 (by rfl) ⟨268922, by rfl⟩ : syracuseStep 1434253 = 537845) (by norm_num)
theorem B4301477 : Blo 1273955 4301477 := bbase (se 4 (by rfl) ⟨403263, by rfl⟩ : syracuseStep 4301477 = 806527) (by norm_num)
theorem B2867885 : Blo 1273955 2867885 := bbase (se 3 (by rfl) ⟨537728, by rfl⟩ : syracuseStep 2867885 = 1075457) (by norm_num)
theorem B1434289 : Blo 1273955 1434289 := bbase (se 2 (by rfl) ⟨537858, by rfl⟩ : syracuseStep 1434289 = 1075717) (by norm_num)
theorem B1434325 : Blo 1273955 1434325 := bbase (se 7 (by rfl) ⟨16808, by rfl⟩ : syracuseStep 1434325 = 33617) (by norm_num)
theorem B2867957 : Blo 1273955 2867957 := bbase (se 5 (by rfl) ⟨134435, by rfl⟩ : syracuseStep 2867957 = 268871) (by norm_num)
theorem B1434361 : Blo 1273955 1434361 := bbase (se 2 (by rfl) ⟨537885, by rfl⟩ : syracuseStep 1434361 = 1075771) (by norm_num)
theorem B1614593 : Blo 1273955 1614593 := bbase (se 2 (by rfl) ⟨605472, by rfl⟩ : syracuseStep 1614593 = 1210945) (by norm_num)
theorem B3228437 : Blo 1273955 3228437 := bbase (se 6 (by rfl) ⟨75666, by rfl⟩ : syracuseStep 3228437 = 151333) (by norm_num)
theorem B1434397 : Blo 1273955 1434397 := bbase (se 3 (by rfl) ⟨268949, by rfl⟩ : syracuseStep 1434397 = 537899) (by norm_num)
theorem B5595941 : Blo 1273955 5595941 := bbase (se 4 (by rfl) ⟨524619, by rfl⟩ : syracuseStep 5595941 = 1049239) (by norm_num)
theorem B5448485 : Blo 1273955 5448485 := bbase (se 4 (by rfl) ⟨510795, by rfl⟩ : syracuseStep 5448485 = 1021591) (by norm_num)
theorem B1614649 : Blo 1273955 1614649 := bbase (se 2 (by rfl) ⟨605493, by rfl⟩ : syracuseStep 1614649 = 1210987) (by norm_num)
theorem B2868029 : Blo 1273955 2868029 := bbase (se 3 (by rfl) ⟨537755, by rfl⟩ : syracuseStep 2868029 = 1075511) (by norm_num)
theorem B1434433 : Blo 1273955 1434433 := bbase (se 2 (by rfl) ⟨537912, by rfl⟩ : syracuseStep 1434433 = 1075825) (by norm_num)
theorem B1532737 : Blo 1273955 1532737 := bbase (se 2 (by rfl) ⟨574776, by rfl⟩ : syracuseStep 1532737 = 1149553) (by norm_num)
theorem B1434469 : Blo 1273955 1434469 := bbase (se 4 (by rfl) ⟨134481, by rfl⟩ : syracuseStep 1434469 = 268963) (by norm_num)
theorem B2868101 : Blo 1273955 2868101 := bbase (se 4 (by rfl) ⟨268884, by rfl⟩ : syracuseStep 2868101 = 537769) (by norm_num)
theorem B1434505 : Blo 1273955 1434505 := bbase (se 2 (by rfl) ⟨537939, by rfl⟩ : syracuseStep 1434505 = 1075879) (by norm_num)
theorem B18637717 : Blo 1273955 18637717 := bbase (se 6 (by rfl) ⟨436821, by rfl⟩ : syracuseStep 18637717 = 873643) (by norm_num)
theorem B1614745 : Blo 1273955 1614745 := bbase (se 2 (by rfl) ⟨605529, by rfl⟩ : syracuseStep 1614745 = 1211059) (by norm_num)
theorem B1434541 : Blo 1273955 1434541 := bbase (se 3 (by rfl) ⟨268976, by rfl⟩ : syracuseStep 1434541 = 537953) (by norm_num)
theorem B2868173 : Blo 1273955 2868173 := bbase (se 3 (by rfl) ⟨537782, by rfl⟩ : syracuseStep 2868173 = 1075565) (by norm_num)
theorem B1434577 : Blo 1273955 1434577 := bbase (se 2 (by rfl) ⟨537966, by rfl⟩ : syracuseStep 1434577 = 1075933) (by norm_num)
theorem B2040805 : Blo 1273955 2040805 := bbase (se 4 (by rfl) ⟨191325, by rfl⟩ : syracuseStep 2040805 = 382651) (by norm_num)
theorem B1434613 : Blo 1273955 1434613 := bbase (se 5 (by rfl) ⟨67247, by rfl⟩ : syracuseStep 1434613 = 134495) (by norm_num)
theorem B2868245 : Blo 1273955 2868245 := bbase (se 6 (by rfl) ⟨67224, by rfl⟩ : syracuseStep 2868245 = 134449) (by norm_num)
theorem B1434649 : Blo 1273955 1434649 := bbase (se 2 (by rfl) ⟨537993, by rfl⟩ : syracuseStep 1434649 = 1075987) (by norm_num)
theorem B1434685 : Blo 1273955 1434685 := bbase (se 3 (by rfl) ⟨269003, by rfl⟩ : syracuseStep 1434685 = 538007) (by norm_num)
theorem B4301909 : Blo 1273955 4301909 := bbase (se 8 (by rfl) ⟨25206, by rfl⟩ : syracuseStep 4301909 = 50413) (by norm_num)
theorem B2868317 : Blo 1273955 2868317 := bbase (se 3 (by rfl) ⟨537809, by rfl⟩ : syracuseStep 2868317 = 1075619) (by norm_num)
theorem B1434721 : Blo 1273955 1434721 := bbase (se 2 (by rfl) ⟨538020, by rfl⟩ : syracuseStep 1434721 = 1076041) (by norm_num)
theorem B3228781 : Blo 1273955 3228781 := bbase (se 3 (by rfl) ⟨605396, by rfl⟩ : syracuseStep 3228781 = 1210793) (by norm_num)
theorem B1434757 : Blo 1273955 1434757 := bbase (se 4 (by rfl) ⟨134508, by rfl⟩ : syracuseStep 1434757 = 269017) (by norm_num)
theorem B2868389 : Blo 1273955 2868389 := bbase (se 4 (by rfl) ⟨268911, by rfl⟩ : syracuseStep 2868389 = 537823) (by norm_num)
theorem B1434793 : Blo 1273955 1434793 := bbase (se 2 (by rfl) ⟨538047, by rfl⟩ : syracuseStep 1434793 = 1076095) (by norm_num)
theorem B3105973 : Blo 1273955 3105973 := bbase (se 5 (by rfl) ⟨145592, by rfl⟩ : syracuseStep 3105973 = 291185) (by norm_num)
theorem B1434829 : Blo 1273955 1434829 := bbase (se 3 (by rfl) ⟨269030, by rfl⟩ : syracuseStep 1434829 = 538061) (by norm_num)
theorem B3228893 : Blo 1273955 3228893 := bbase (se 3 (by rfl) ⟨605417, by rfl⟩ : syracuseStep 3228893 = 1210835) (by norm_num)
theorem B2868461 : Blo 1273955 2868461 := bbase (se 3 (by rfl) ⟨537836, by rfl⟩ : syracuseStep 2868461 = 1075673) (by norm_num)
theorem B1434865 : Blo 1273955 1434865 := bbase (se 2 (by rfl) ⟨538074, by rfl⟩ : syracuseStep 1434865 = 1076149) (by norm_num)
theorem B1434901 : Blo 1273955 1434901 := bbase (se 6 (by rfl) ⟨33630, by rfl⟩ : syracuseStep 1434901 = 67261) (by norm_num)
theorem B2868533 : Blo 1273955 2868533 := bbase (se 5 (by rfl) ⟨134462, by rfl⟩ : syracuseStep 2868533 = 268925) (by norm_num)
theorem B1434937 : Blo 1273955 1434937 := bbase (se 2 (by rfl) ⟨538101, by rfl⟩ : syracuseStep 1434937 = 1076203) (by norm_num)
theorem B1361233 : Blo 1273955 1361233 := bbase (se 2 (by rfl) ⟨510462, by rfl⟩ : syracuseStep 1361233 = 1020925) (by norm_num)
theorem B1434973 : Blo 1273955 1434973 := bbase (se 3 (by rfl) ⟨269057, by rfl⟩ : syracuseStep 1434973 = 538115) (by norm_num)
theorem B2868605 : Blo 1273955 2868605 := bbase (se 3 (by rfl) ⟨537863, by rfl⟩ : syracuseStep 2868605 = 1075727) (by norm_num)
theorem B1435009 : Blo 1273955 1435009 := bbase (se 2 (by rfl) ⟨538128, by rfl⟩ : syracuseStep 1435009 = 1076257) (by norm_num)
theorem B1361305 : Blo 1273955 1361305 := bbase (se 2 (by rfl) ⟨510489, by rfl⟩ : syracuseStep 1361305 = 1020979) (by norm_num)
theorem B3229085 : Blo 1273955 3229085 := bbase (se 3 (by rfl) ⟨605453, by rfl⟩ : syracuseStep 3229085 = 1210907) (by norm_num)
theorem B1435045 : Blo 1273955 1435045 := bbase (se 4 (by rfl) ⟨134535, by rfl⟩ : syracuseStep 1435045 = 269071) (by norm_num)
theorem B2868677 : Blo 1273955 2868677 := bbase (se 4 (by rfl) ⟨268938, by rfl⟩ : syracuseStep 2868677 = 537877) (by norm_num)
theorem B1435081 : Blo 1273955 1435081 := bbase (se 2 (by rfl) ⟨538155, by rfl⟩ : syracuseStep 1435081 = 1076311) (by norm_num)
theorem B1435117 : Blo 1273955 1435117 := bbase (se 3 (by rfl) ⟨269084, by rfl⟩ : syracuseStep 1435117 = 538169) (by norm_num)
theorem B4302341 : Blo 1273955 4302341 := bbase (se 4 (by rfl) ⟨403344, by rfl⟩ : syracuseStep 4302341 = 806689) (by norm_num)
theorem B2868749 : Blo 1273955 2868749 := bbase (se 3 (by rfl) ⟨537890, by rfl⟩ : syracuseStep 2868749 = 1075781) (by norm_num)
theorem B1435153 : Blo 1273955 1435153 := bbase (se 2 (by rfl) ⟨538182, by rfl⟩ : syracuseStep 1435153 = 1076365) (by norm_num)
theorem B1435189 : Blo 1273955 1435189 := bbase (se 5 (by rfl) ⟨67274, by rfl⟩ : syracuseStep 1435189 = 134549) (by norm_num)
theorem B2098757 : Blo 1273955 2098757 := bbase (se 4 (by rfl) ⟨196758, by rfl⟩ : syracuseStep 2098757 = 393517) (by norm_num)
theorem B1361485 : Blo 1273955 1361485 := bbase (se 3 (by rfl) ⟨255278, by rfl⟩ : syracuseStep 1361485 = 510557) (by norm_num)
theorem B2868821 : Blo 1273955 2868821 := bbase (se 8 (by rfl) ⟨16809, by rfl⟩ : syracuseStep 2868821 = 33619) (by norm_num)
theorem B1435225 : Blo 1273955 1435225 := bbase (se 2 (by rfl) ⟨538209, by rfl⟩ : syracuseStep 1435225 = 1076419) (by norm_num)
theorem B1435261 : Blo 1273955 1435261 := bbase (se 3 (by rfl) ⟨269111, by rfl⟩ : syracuseStep 1435261 = 538223) (by norm_num)
theorem B2868893 : Blo 1273955 2868893 := bbase (se 3 (by rfl) ⟨537917, by rfl⟩ : syracuseStep 2868893 = 1075835) (by norm_num)
theorem B1435297 : Blo 1273955 1435297 := bbase (se 2 (by rfl) ⟨538236, by rfl⟩ : syracuseStep 1435297 = 1076473) (by norm_num)
theorem B1435333 : Blo 1273955 1435333 := bbase (se 4 (by rfl) ⟨134562, by rfl⟩ : syracuseStep 1435333 = 269125) (by norm_num)
theorem B2721509 : Blo 1273955 2721509 := bbase (se 4 (by rfl) ⟨255141, by rfl⟩ : syracuseStep 2721509 = 510283) (by norm_num)
theorem B2868965 : Blo 1273955 2868965 := bbase (se 4 (by rfl) ⟨268965, by rfl⟩ : syracuseStep 2868965 = 537931) (by norm_num)
theorem B1435369 : Blo 1273955 1435369 := bbase (se 2 (by rfl) ⟨538263, by rfl⟩ : syracuseStep 1435369 = 1076527) (by norm_num)
theorem B3229429 : Blo 1273955 3229429 := bbase (se 5 (by rfl) ⟨151379, by rfl⟩ : syracuseStep 3229429 = 302759) (by norm_num)
theorem B1435405 : Blo 1273955 1435405 := bbase (se 3 (by rfl) ⟨269138, by rfl⟩ : syracuseStep 1435405 = 538277) (by norm_num)
theorem B2869037 : Blo 1273955 2869037 := bbase (se 3 (by rfl) ⟨537944, by rfl⟩ : syracuseStep 2869037 = 1075889) (by norm_num)
theorem B1435441 : Blo 1273955 1435441 := bbase (se 2 (by rfl) ⟨538290, by rfl⟩ : syracuseStep 1435441 = 1076581) (by norm_num)
theorem B6457157 : Blo 1273955 6457157 := bbase (se 4 (by rfl) ⟨605358, by rfl⟩ : syracuseStep 6457157 = 1210717) (by norm_num)
theorem B3229541 : Blo 1273955 3229541 := bbase (se 4 (by rfl) ⟨302769, by rfl⟩ : syracuseStep 3229541 = 605539) (by norm_num)
theorem B2869109 : Blo 1273955 2869109 := bbase (se 5 (by rfl) ⟨134489, by rfl⟩ : syracuseStep 2869109 = 268979) (by norm_num)
theorem B24831893 : Blo 1273955 24831893 := bbase (se 6 (by rfl) ⟨581997, by rfl⟩ : syracuseStep 24831893 = 1163995) (by norm_num)
theorem B3631013 : Blo 1273955 3631013 := bbase (se 4 (by rfl) ⟨340407, by rfl⟩ : syracuseStep 3631013 = 680815) (by norm_num)
theorem B4302773 : Blo 1273955 4302773 := bbase (se 5 (by rfl) ⟨201692, by rfl⟩ : syracuseStep 4302773 = 403385) (by norm_num)
theorem B2869181 : Blo 1273955 2869181 := bbase (se 3 (by rfl) ⟨537971, by rfl⟩ : syracuseStep 2869181 = 1075943) (by norm_num)
theorem B3729365 : Blo 1273955 3729365 := bbase (se 7 (by rfl) ⟨43703, by rfl⟩ : syracuseStep 3729365 = 87407) (by norm_num)
theorem B2869253 : Blo 1273955 2869253 := bbase (se 4 (by rfl) ⟨268992, by rfl⟩ : syracuseStep 2869253 = 537985) (by norm_num)
theorem B1361929 : Blo 1273955 1361929 := bbase (se 2 (by rfl) ⟨510723, by rfl⟩ : syracuseStep 1361929 = 1021447) (by norm_num)
theorem B3229733 : Blo 1273955 3229733 := bbase (se 4 (by rfl) ⟨302787, by rfl⟩ : syracuseStep 3229733 = 605575) (by norm_num)
theorem B2295877 : Blo 1273955 2295877 := bbase (se 4 (by rfl) ⟨215238, by rfl⟩ : syracuseStep 2295877 = 430477) (by norm_num)
theorem B2869325 : Blo 1273955 2869325 := bbase (se 3 (by rfl) ⟨537998, by rfl⟩ : syracuseStep 2869325 = 1075997) (by norm_num)
theorem B1362053 : Blo 1273955 1362053 := bbase (se 4 (by rfl) ⟨127692, by rfl⟩ : syracuseStep 1362053 = 255385) (by norm_num)
theorem B4909189 : Blo 1273955 4909189 := bbase (se 4 (by rfl) ⟨460236, by rfl⟩ : syracuseStep 4909189 = 920473) (by norm_num)
theorem B1910933 : Blo 1273955 1910933 := bbase (se 6 (by rfl) ⟨44787, by rfl⟩ : syracuseStep 1910933 = 89575) (by norm_num)
theorem B2869397 : Blo 1273955 2869397 := bbase (se 6 (by rfl) ⟨67251, by rfl⟩ : syracuseStep 2869397 = 134503) (by norm_num)
theorem B5441701 : Blo 1273955 5441701 := bbase (se 4 (by rfl) ⟨510159, by rfl⟩ : syracuseStep 5441701 = 1020319) (by norm_num)
theorem B1910957 : Blo 1273955 1910957 := bbase (se 3 (by rfl) ⟨358304, by rfl⟩ : syracuseStep 1910957 = 716609) (by norm_num)
theorem B1910981 : Blo 1273955 1910981 := bbase (se 4 (by rfl) ⟨179154, by rfl⟩ : syracuseStep 1910981 = 358309) (by norm_num)
theorem B1911005 : Blo 1273955 1911005 := bbase (se 3 (by rfl) ⟨358313, by rfl⟩ : syracuseStep 1911005 = 716627) (by norm_num)
theorem B2869469 : Blo 1273955 2869469 := bbase (se 3 (by rfl) ⟨538025, by rfl⟩ : syracuseStep 2869469 = 1076051) (by norm_num)
theorem B1911029 : Blo 1273955 1911029 := bbase (se 5 (by rfl) ⟨89579, by rfl⟩ : syracuseStep 1911029 = 179159) (by norm_num)
theorem B1911053 : Blo 1273955 1911053 := bbase (se 3 (by rfl) ⟨358322, by rfl⟩ : syracuseStep 1911053 = 716645) (by norm_num)
theorem B10897685 : Blo 1273955 10897685 := bbase (se 6 (by rfl) ⟨255414, by rfl⟩ : syracuseStep 10897685 = 510829) (by norm_num)
theorem B2582813 : Blo 1273955 2582813 := bbase (se 3 (by rfl) ⟨484277, by rfl⟩ : syracuseStep 2582813 = 968555) (by norm_num)
theorem B1911077 : Blo 1273955 1911077 := bbase (se 4 (by rfl) ⟨179163, by rfl⟩ : syracuseStep 1911077 = 358327) (by norm_num)
theorem B2869541 : Blo 1273955 2869541 := bbase (se 4 (by rfl) ⟨269019, by rfl⟩ : syracuseStep 2869541 = 538039) (by norm_num)
theorem B2418997 : Blo 1273955 2418997 := bbase (se 5 (by rfl) ⟨113390, by rfl⟩ : syracuseStep 2418997 = 226781) (by norm_num)
theorem B1911101 : Blo 1273955 1911101 := bbase (se 3 (by rfl) ⟨358331, by rfl⟩ : syracuseStep 1911101 = 716663) (by norm_num)
theorem B2042189 : Blo 1273955 2042189 := bbase (se 3 (by rfl) ⟨382910, by rfl⟩ : syracuseStep 2042189 = 765821) (by norm_num)
theorem B1911125 : Blo 1273955 1911125 := bbase (se 10 (by rfl) ⟨2799, by rfl⟩ : syracuseStep 1911125 = 5599) (by norm_num)
theorem B4303205 : Blo 1273955 4303205 := bbase (se 4 (by rfl) ⟨403425, by rfl⟩ : syracuseStep 4303205 = 806851) (by norm_num)
theorem B1911149 : Blo 1273955 1911149 := bbase (se 3 (by rfl) ⟨358340, by rfl⟩ : syracuseStep 1911149 = 716681) (by norm_num)
theorem B2869613 : Blo 1273955 2869613 := bbase (se 3 (by rfl) ⟨538052, by rfl⟩ : syracuseStep 2869613 = 1076105) (by norm_num)
theorem B1362305 : Blo 1273955 1362305 := bbase (se 2 (by rfl) ⟨510864, by rfl⟩ : syracuseStep 1362305 = 1021729) (by norm_num)
theorem B1911173 : Blo 1273955 1911173 := bbase (se 4 (by rfl) ⟨179172, by rfl⟩ : syracuseStep 1911173 = 358345) (by norm_num)
theorem B1911197 : Blo 1273955 1911197 := bbase (se 3 (by rfl) ⟨358349, by rfl⟩ : syracuseStep 1911197 = 716699) (by norm_num)
theorem B1911221 : Blo 1273955 1911221 := bbase (se 5 (by rfl) ⟨89588, by rfl⟩ : syracuseStep 1911221 = 179177) (by norm_num)
theorem B2869685 : Blo 1273955 2869685 := bbase (se 5 (by rfl) ⟨134516, by rfl⟩ : syracuseStep 2869685 = 269033) (by norm_num)
theorem B2419141 : Blo 1273955 2419141 := bbase (se 4 (by rfl) ⟨226794, by rfl⟩ : syracuseStep 2419141 = 453589) (by norm_num)
theorem B1911245 : Blo 1273955 1911245 := bbase (se 3 (by rfl) ⟨358358, by rfl⟩ : syracuseStep 1911245 = 716717) (by norm_num)
theorem B2722261 : Blo 1273955 2722261 := bbase (se 7 (by rfl) ⟨31901, by rfl⟩ : syracuseStep 2722261 = 63803) (by norm_num)
theorem B1911269 : Blo 1273955 1911269 := bbase (se 4 (by rfl) ⟨179181, by rfl⟩ : syracuseStep 1911269 = 358363) (by norm_num)
theorem B9685493 : Blo 1273955 9685493 := bbase (se 5 (by rfl) ⟨454007, by rfl⟩ : syracuseStep 9685493 = 908015) (by norm_num)
theorem B1911293 : Blo 1273955 1911293 := bbase (se 3 (by rfl) ⟨358367, by rfl⟩ : syracuseStep 1911293 = 716735) (by norm_num)
theorem B2869757 : Blo 1273955 2869757 := bbase (se 3 (by rfl) ⟨538079, by rfl⟩ : syracuseStep 2869757 = 1076159) (by norm_num)
theorem B2042381 : Blo 1273955 2042381 := bbase (se 3 (by rfl) ⟨382946, by rfl⟩ : syracuseStep 2042381 = 765893) (by norm_num)
theorem B1911317 : Blo 1273955 1911317 := bbase (se 6 (by rfl) ⟨44796, by rfl⟩ : syracuseStep 1911317 = 89593) (by norm_num)
theorem B4844069 : Blo 1273955 4844069 := bbase (se 4 (by rfl) ⟨454131, by rfl⟩ : syracuseStep 4844069 = 908263) (by norm_num)
theorem B1911341 : Blo 1273955 1911341 := bbase (se 3 (by rfl) ⟨358376, by rfl⟩ : syracuseStep 1911341 = 716753) (by norm_num)
theorem B1911365 : Blo 1273955 1911365 := bbase (se 4 (by rfl) ⟨179190, by rfl⟩ : syracuseStep 1911365 = 358381) (by norm_num)
theorem B2869829 : Blo 1273955 2869829 := bbase (se 4 (by rfl) ⟨269046, by rfl⟩ : syracuseStep 2869829 = 538093) (by norm_num)
theorem B1657433 : Blo 1273955 1657433 := bbase (se 2 (by rfl) ⟨621537, by rfl⟩ : syracuseStep 1657433 = 1243075) (by norm_num)
theorem B1911389 : Blo 1273955 1911389 := bbase (se 3 (by rfl) ⟨358385, by rfl⟩ : syracuseStep 1911389 = 716771) (by norm_num)
theorem B2722405 : Blo 1273955 2722405 := bbase (se 4 (by rfl) ⟨255225, by rfl⟩ : syracuseStep 2722405 = 510451) (by norm_num)
theorem B2419301 : Blo 1273955 2419301 := bbase (se 4 (by rfl) ⟨226809, by rfl⟩ : syracuseStep 2419301 = 453619) (by norm_num)
theorem B1722989 : Blo 1273955 1722989 := bbase (se 3 (by rfl) ⟨323060, by rfl⟩ : syracuseStep 1722989 = 646121) (by norm_num)
theorem B1911413 : Blo 1273955 1911413 := bbase (se 5 (by rfl) ⟨89597, by rfl⟩ : syracuseStep 1911413 = 179195) (by norm_num)
theorem B1911437 : Blo 1273955 1911437 := bbase (se 3 (by rfl) ⟨358394, by rfl⟩ : syracuseStep 1911437 = 716789) (by norm_num)
theorem B2869901 : Blo 1273955 2869901 := bbase (se 3 (by rfl) ⟨538106, by rfl⟩ : syracuseStep 2869901 = 1076213) (by norm_num)
theorem B1911461 : Blo 1273955 1911461 := bbase (se 4 (by rfl) ⟨179199, by rfl⟩ : syracuseStep 1911461 = 358399) (by norm_num)
theorem B1911485 : Blo 1273955 1911485 := bbase (se 3 (by rfl) ⟨358403, by rfl⟩ : syracuseStep 1911485 = 716807) (by norm_num)
theorem B2329277 : Blo 1273955 2329277 := bbase (se 3 (by rfl) ⟨436739, by rfl⟩ : syracuseStep 2329277 = 873479) (by norm_num)
theorem B1911509 : Blo 1273955 1911509 := bbase (se 7 (by rfl) ⟨22400, by rfl⟩ : syracuseStep 1911509 = 44801) (by norm_num)
theorem B2869973 : Blo 1273955 2869973 := bbase (se 7 (by rfl) ⟨33632, by rfl⟩ : syracuseStep 2869973 = 67265) (by norm_num)
theorem B1911533 : Blo 1273955 1911533 := bbase (se 3 (by rfl) ⟨358412, by rfl⟩ : syracuseStep 1911533 = 716825) (by norm_num)
theorem B2419445 : Blo 1273955 2419445 := bbase (se 5 (by rfl) ⟨113411, by rfl⟩ : syracuseStep 2419445 = 226823) (by norm_num)
theorem B1911557 : Blo 1273955 1911557 := bbase (se 4 (by rfl) ⟨179208, by rfl⟩ : syracuseStep 1911557 = 358417) (by norm_num)
theorem B4303637 : Blo 1273955 4303637 := bbase (se 6 (by rfl) ⟨100866, by rfl⟩ : syracuseStep 4303637 = 201733) (by norm_num)
theorem B1911581 : Blo 1273955 1911581 := bbase (se 3 (by rfl) ⟨358421, by rfl⟩ : syracuseStep 1911581 = 716843) (by norm_num)
theorem B2870045 : Blo 1273955 2870045 := bbase (se 3 (by rfl) ⟨538133, by rfl⟩ : syracuseStep 2870045 = 1076267) (by norm_num)
theorem B1911605 : Blo 1273955 1911605 := bbase (se 5 (by rfl) ⟨89606, by rfl⟩ : syracuseStep 1911605 = 179213) (by norm_num)
theorem B4844357 : Blo 1273955 4844357 := bbase (se 4 (by rfl) ⟨454158, by rfl⟩ : syracuseStep 4844357 = 908317) (by norm_num)
theorem B1911629 : Blo 1273955 1911629 := bbase (se 3 (by rfl) ⟨358430, by rfl⟩ : syracuseStep 1911629 = 716861) (by norm_num)
theorem B1911653 : Blo 1273955 1911653 := bbase (se 4 (by rfl) ⟨179217, by rfl⟩ : syracuseStep 1911653 = 358435) (by norm_num)
theorem B2870117 : Blo 1273955 2870117 := bbase (se 4 (by rfl) ⟨269073, by rfl⟩ : syracuseStep 2870117 = 538147) (by norm_num)
theorem B1911677 : Blo 1273955 1911677 := bbase (se 3 (by rfl) ⟨358439, by rfl⟩ : syracuseStep 1911677 = 716879) (by norm_num)
theorem B6130565 : Blo 1273955 6130565 := bbase (se 4 (by rfl) ⟨574740, by rfl⟩ : syracuseStep 6130565 = 1149481) (by norm_num)
theorem B9677717 : Blo 1273955 9677717 := bbase (se 6 (by rfl) ⟨226821, by rfl⟩ : syracuseStep 9677717 = 453643) (by norm_num)
theorem B1911701 : Blo 1273955 1911701 := bbase (se 6 (by rfl) ⟨44805, by rfl⟩ : syracuseStep 1911701 = 89611) (by norm_num)
theorem B1911725 : Blo 1273955 1911725 := bbase (se 3 (by rfl) ⟨358448, by rfl⟩ : syracuseStep 1911725 = 716897) (by norm_num)
theorem B2870189 : Blo 1273955 2870189 := bbase (se 3 (by rfl) ⟨538160, by rfl⟩ : syracuseStep 2870189 = 1076321) (by norm_num)
theorem B2296757 : Blo 1273955 2296757 := bbase (se 5 (by rfl) ⟨107660, by rfl⟩ : syracuseStep 2296757 = 215321) (by norm_num)
theorem B1911749 : Blo 1273955 1911749 := bbase (se 4 (by rfl) ⟨179226, by rfl⟩ : syracuseStep 1911749 = 358453) (by norm_num)
theorem B1911773 : Blo 1273955 1911773 := bbase (se 3 (by rfl) ⟨358457, by rfl⟩ : syracuseStep 1911773 = 716915) (by norm_num)
theorem B2722781 : Blo 1273955 2722781 := bbase (se 3 (by rfl) ⟨510521, by rfl⟩ : syracuseStep 2722781 = 1021043) (by norm_num)
theorem B1911797 : Blo 1273955 1911797 := bbase (se 5 (by rfl) ⟨89615, by rfl⟩ : syracuseStep 1911797 = 179231) (by norm_num)
theorem B2870261 : Blo 1273955 2870261 := bbase (se 5 (by rfl) ⟨134543, by rfl⟩ : syracuseStep 2870261 = 269087) (by norm_num)
theorem B1657849 : Blo 1273955 1657849 := bbase (se 2 (by rfl) ⟨621693, by rfl⟩ : syracuseStep 1657849 = 1243387) (by norm_num)
theorem B2296829 : Blo 1273955 2296829 := bbase (se 3 (by rfl) ⟨430655, by rfl⟩ : syracuseStep 2296829 = 861311) (by norm_num)
theorem B1911821 : Blo 1273955 1911821 := bbase (se 3 (by rfl) ⟨358466, by rfl⟩ : syracuseStep 1911821 = 716933) (by norm_num)
theorem B2419733 : Blo 1273955 2419733 := bbase (se 6 (by rfl) ⟨56712, by rfl⟩ : syracuseStep 2419733 = 113425) (by norm_num)
theorem B1911845 : Blo 1273955 1911845 := bbase (se 4 (by rfl) ⟨179235, by rfl⟩ : syracuseStep 1911845 = 358471) (by norm_num)
theorem B1911869 : Blo 1273955 1911869 := bbase (se 3 (by rfl) ⟨358475, by rfl⟩ : syracuseStep 1911869 = 716951) (by norm_num)
theorem B2870333 : Blo 1273955 2870333 := bbase (se 3 (by rfl) ⟨538187, by rfl⟩ : syracuseStep 2870333 = 1076375) (by norm_num)
theorem B3632197 : Blo 1273955 3632197 := bbase (se 4 (by rfl) ⟨340518, by rfl⟩ : syracuseStep 3632197 = 681037) (by norm_num)
theorem B1911893 : Blo 1273955 1911893 := bbase (se 8 (by rfl) ⟨11202, by rfl⟩ : syracuseStep 1911893 = 22405) (by norm_num)
theorem B6458453 : Blo 1273955 6458453 := bbase (se 8 (by rfl) ⟨37842, by rfl⟩ : syracuseStep 6458453 = 75685) (by norm_num)
theorem B1911917 : Blo 1273955 1911917 := bbase (se 3 (by rfl) ⟨358484, by rfl⟩ : syracuseStep 1911917 = 716969) (by norm_num)
theorem B1911941 : Blo 1273955 1911941 := bbase (se 4 (by rfl) ⟨179244, by rfl⟩ : syracuseStep 1911941 = 358489) (by norm_num)
theorem B2870405 : Blo 1273955 2870405 := bbase (se 4 (by rfl) ⟨269100, by rfl⟩ : syracuseStep 2870405 = 538201) (by norm_num)
theorem B2296973 : Blo 1273955 2296973 := bbase (se 3 (by rfl) ⟨430682, by rfl⟩ : syracuseStep 2296973 = 861365) (by norm_num)
theorem B1911965 : Blo 1273955 1911965 := bbase (se 3 (by rfl) ⟨358493, by rfl⟩ : syracuseStep 1911965 = 716987) (by norm_num)
theorem B2419885 : Blo 1273955 2419885 := bbase (se 3 (by rfl) ⟨453728, by rfl⟩ : syracuseStep 2419885 = 907457) (by norm_num)
theorem B1911989 : Blo 1273955 1911989 := bbase (se 5 (by rfl) ⟨89624, by rfl⟩ : syracuseStep 1911989 = 179249) (by norm_num)
theorem B4304069 : Blo 1273955 4304069 := bbase (se 4 (by rfl) ⟨403506, by rfl⟩ : syracuseStep 4304069 = 807013) (by norm_num)
theorem B1912013 : Blo 1273955 1912013 := bbase (se 3 (by rfl) ⟨358502, by rfl⟩ : syracuseStep 1912013 = 717005) (by norm_num)
theorem B2870477 : Blo 1273955 2870477 := bbase (se 3 (by rfl) ⟨538214, by rfl⟩ : syracuseStep 2870477 = 1076429) (by norm_num)
theorem B2297045 : Blo 1273955 2297045 := bbase (se 7 (by rfl) ⟨26918, by rfl⟩ : syracuseStep 2297045 = 53837) (by norm_num)
theorem B28331221 : Blo 1273955 28331221 := bbase (se 7 (by rfl) ⟨332006, by rfl⟩ : syracuseStep 28331221 = 664013) (by norm_num)
theorem B1912037 : Blo 1273955 1912037 := bbase (se 4 (by rfl) ⟨179253, by rfl⟩ : syracuseStep 1912037 = 358507) (by norm_num)
theorem B3632357 : Blo 1273955 3632357 := bbase (se 4 (by rfl) ⟨340533, by rfl⟩ : syracuseStep 3632357 = 681067) (by norm_num)
theorem B1912061 : Blo 1273955 1912061 := bbase (se 3 (by rfl) ⟨358511, by rfl⟩ : syracuseStep 1912061 = 717023) (by norm_num)
theorem B1912085 : Blo 1273955 1912085 := bbase (se 6 (by rfl) ⟨44814, by rfl⟩ : syracuseStep 1912085 = 89629) (by norm_num)
theorem B2870549 : Blo 1273955 2870549 := bbase (se 6 (by rfl) ⟨67278, by rfl⟩ : syracuseStep 2870549 = 134557) (by norm_num)
theorem B1912109 : Blo 1273955 1912109 := bbase (se 3 (by rfl) ⟨358520, by rfl⟩ : syracuseStep 1912109 = 717041) (by norm_num)
theorem B1912133 : Blo 1273955 1912133 := bbase (se 4 (by rfl) ⟨179262, by rfl⟩ : syracuseStep 1912133 = 358525) (by norm_num)
theorem B2723149 : Blo 1273955 2723149 := bbase (se 3 (by rfl) ⟨510590, by rfl⟩ : syracuseStep 2723149 = 1021181) (by norm_num)
theorem B1912157 : Blo 1273955 1912157 := bbase (se 3 (by rfl) ⟨358529, by rfl⟩ : syracuseStep 1912157 = 717059) (by norm_num)
theorem B2870621 : Blo 1273955 2870621 := bbase (se 3 (by rfl) ⟨538241, by rfl⟩ : syracuseStep 2870621 = 1076483) (by norm_num)
theorem B1912181 : Blo 1273955 1912181 := bbase (se 5 (by rfl) ⟨89633, by rfl⟩ : syracuseStep 1912181 = 179267) (by norm_num)
theorem B1912205 : Blo 1273955 1912205 := bbase (se 3 (by rfl) ⟨358538, by rfl⟩ : syracuseStep 1912205 = 717077) (by norm_num)
theorem B1723789 : Blo 1273955 1723789 := bbase (se 3 (by rfl) ⟨323210, by rfl⟩ : syracuseStep 1723789 = 646421) (by norm_num)
theorem B1912229 : Blo 1273955 1912229 := bbase (se 4 (by rfl) ⟨179271, by rfl⟩ : syracuseStep 1912229 = 358543) (by norm_num)
theorem B2870693 : Blo 1273955 2870693 := bbase (se 4 (by rfl) ⟨269127, by rfl⟩ : syracuseStep 2870693 = 538255) (by norm_num)
theorem B1912253 : Blo 1273955 1912253 := bbase (se 3 (by rfl) ⟨358547, by rfl⟩ : syracuseStep 1912253 = 717095) (by norm_num)
theorem B1912277 : Blo 1273955 1912277 := bbase (se 7 (by rfl) ⟨22409, by rfl⟩ : syracuseStep 1912277 = 44819) (by norm_num)
theorem B3632597 : Blo 1273955 3632597 := bbase (se 7 (by rfl) ⟨42569, by rfl⟩ : syracuseStep 3632597 = 85139) (by norm_num)
theorem B2420189 : Blo 1273955 2420189 := bbase (se 3 (by rfl) ⟨453785, by rfl⟩ : syracuseStep 2420189 = 907571) (by norm_num)
theorem B2149861 : Blo 1273955 2149861 := bbase (se 4 (by rfl) ⟨201549, by rfl⟩ : syracuseStep 2149861 = 403099) (by norm_num)
theorem B1912301 : Blo 1273955 1912301 := bbase (se 3 (by rfl) ⟨358556, by rfl⟩ : syracuseStep 1912301 = 717113) (by norm_num)
theorem B2870765 : Blo 1273955 2870765 := bbase (se 3 (by rfl) ⟨538268, by rfl⟩ : syracuseStep 2870765 = 1076537) (by norm_num)
theorem B1551857 : Blo 1273955 1551857 := bbase (se 2 (by rfl) ⟨581946, by rfl⟩ : syracuseStep 1551857 = 1163893) (by norm_num)
theorem B6450677 : Blo 1273955 6450677 := bbase (se 5 (by rfl) ⟨302375, by rfl⟩ : syracuseStep 6450677 = 604751) (by norm_num)
theorem B1912325 : Blo 1273955 1912325 := bbase (se 4 (by rfl) ⟨179280, by rfl⟩ : syracuseStep 1912325 = 358561) (by norm_num)
theorem B1912349 : Blo 1273955 1912349 := bbase (se 3 (by rfl) ⟨358565, by rfl⟩ : syracuseStep 1912349 = 717131) (by norm_num)
theorem B1912373 : Blo 1273955 1912373 := bbase (se 5 (by rfl) ⟨89642, by rfl⟩ : syracuseStep 1912373 = 179285) (by norm_num)
theorem B2870837 : Blo 1273955 2870837 := bbase (se 5 (by rfl) ⟨134570, by rfl⟩ : syracuseStep 2870837 = 269141) (by norm_num)
theorem B2149949 : Blo 1273955 2149949 := bbase (se 3 (by rfl) ⟨403115, by rfl⟩ : syracuseStep 2149949 = 806231) (by norm_num)
theorem B1912397 : Blo 1273955 1912397 := bbase (se 3 (by rfl) ⟨358574, by rfl⟩ : syracuseStep 1912397 = 717149) (by norm_num)
theorem B10333781 : Blo 1273955 10333781 := bbase (se 8 (by rfl) ⟨60549, by rfl⟩ : syracuseStep 10333781 = 121099) (by norm_num)
theorem B44174933 : Blo 1273955 44174933 := bbase (se 8 (by rfl) ⟨258837, by rfl⟩ : syracuseStep 44174933 = 517675) (by norm_num)
theorem B1912421 : Blo 1273955 1912421 := bbase (se 4 (by rfl) ⟨179289, by rfl⟩ : syracuseStep 1912421 = 358579) (by norm_num)
theorem B4304501 : Blo 1273955 4304501 := bbase (se 5 (by rfl) ⟨201773, by rfl⟩ : syracuseStep 4304501 = 403547) (by norm_num)
theorem B1912445 : Blo 1273955 1912445 := bbase (se 3 (by rfl) ⟨358583, by rfl⟩ : syracuseStep 1912445 = 717167) (by norm_num)
theorem B9186965 : Blo 1273955 9186965 := bbase (se 6 (by rfl) ⟨215319, by rfl⟩ : syracuseStep 9186965 = 430639) (by norm_num)
theorem B1912469 : Blo 1273955 1912469 := bbase (se 6 (by rfl) ⟨44823, by rfl⟩ : syracuseStep 1912469 = 89647) (by norm_num)
theorem B3632789 : Blo 1273955 3632789 := bbase (se 6 (by rfl) ⟨85143, by rfl⟩ : syracuseStep 3632789 = 170287) (by norm_num)
theorem B1912493 : Blo 1273955 1912493 := bbase (se 3 (by rfl) ⟨358592, by rfl⟩ : syracuseStep 1912493 = 717185) (by norm_num)
theorem B2150077 : Blo 1273955 2150077 := bbase (se 3 (by rfl) ⟨403139, by rfl⟩ : syracuseStep 2150077 = 806279) (by norm_num)
theorem B4419269 : Blo 1273955 4419269 := bbase (se 4 (by rfl) ⟨414306, by rfl⟩ : syracuseStep 4419269 = 828613) (by norm_num)
theorem B1912517 : Blo 1273955 1912517 := bbase (se 4 (by rfl) ⟨179298, by rfl⟩ : syracuseStep 1912517 = 358597) (by norm_num)
theorem B10333909 : Blo 1273955 10333909 := bbase (se 7 (by rfl) ⟨121100, by rfl⟩ : syracuseStep 10333909 = 242201) (by norm_num)
theorem B1912541 : Blo 1273955 1912541 := bbase (se 3 (by rfl) ⟨358601, by rfl⟩ : syracuseStep 1912541 = 717203) (by norm_num)
theorem B1912565 : Blo 1273955 1912565 := bbase (se 5 (by rfl) ⟨89651, by rfl⟩ : syracuseStep 1912565 = 179303) (by norm_num)
theorem B1838845 : Blo 1273955 1838845 := bbase (se 3 (by rfl) ⟨344783, by rfl⟩ : syracuseStep 1838845 = 689567) (by norm_num)
theorem B1912589 : Blo 1273955 1912589 := bbase (se 3 (by rfl) ⟨358610, by rfl⟩ : syracuseStep 1912589 = 717221) (by norm_num)
theorem B2150165 : Blo 1273955 2150165 := bbase (se 6 (by rfl) ⟨50394, by rfl⟩ : syracuseStep 2150165 = 100789) (by norm_num)
theorem B1912613 : Blo 1273955 1912613 := bbase (se 4 (by rfl) ⟨179307, by rfl⟩ : syracuseStep 1912613 = 358615) (by norm_num)
theorem B5812021 : Blo 1273955 5812021 := bbase (se 5 (by rfl) ⟨272438, by rfl⟩ : syracuseStep 5812021 = 544877) (by norm_num)
theorem B2043701 : Blo 1273955 2043701 := bbase (se 5 (by rfl) ⟨95798, by rfl⟩ : syracuseStep 2043701 = 191597) (by norm_num)
theorem B1912637 : Blo 1273955 1912637 := bbase (se 3 (by rfl) ⟨358619, by rfl⟩ : syracuseStep 1912637 = 717239) (by norm_num)
theorem B4140869 : Blo 1273955 4140869 := bbase (se 4 (by rfl) ⟨388206, by rfl⟩ : syracuseStep 4140869 = 776413) (by norm_num)
theorem B13782869 : Blo 1273955 13782869 := bbase (se 9 (by rfl) ⟨40379, by rfl⟩ : syracuseStep 13782869 = 80759) (by norm_num)
theorem B1912661 : Blo 1273955 1912661 := bbase (se 9 (by rfl) ⟨5603, by rfl⟩ : syracuseStep 1912661 = 11207) (by norm_num)
theorem B1912685 : Blo 1273955 1912685 := bbase (se 3 (by rfl) ⟨358628, by rfl⟩ : syracuseStep 1912685 = 717257) (by norm_num)
theorem B1912709 : Blo 1273955 1912709 := bbase (se 4 (by rfl) ⟨179316, by rfl⟩ : syracuseStep 1912709 = 358633) (by norm_num)
theorem B1814413 : Blo 1273955 1814413 := bbase (se 3 (by rfl) ⟨340202, by rfl⟩ : syracuseStep 1814413 = 680405) (by norm_num)
theorem B2150293 : Blo 1273955 2150293 := bbase (se 6 (by rfl) ⟨50397, by rfl⟩ : syracuseStep 2150293 = 100795) (by norm_num)
theorem B6123413 : Blo 1273955 6123413 := bbase (se 6 (by rfl) ⟨143517, by rfl⟩ : syracuseStep 6123413 = 287035) (by norm_num)
theorem B2043797 : Blo 1273955 2043797 := bbase (se 6 (by rfl) ⟨47901, by rfl⟩ : syracuseStep 2043797 = 95803) (by norm_num)
theorem B1912733 : Blo 1273955 1912733 := bbase (se 3 (by rfl) ⟨358637, by rfl⟩ : syracuseStep 1912733 = 717275) (by norm_num)
theorem B1912757 : Blo 1273955 1912757 := bbase (se 5 (by rfl) ⟨89660, by rfl⟩ : syracuseStep 1912757 = 179321) (by norm_num)
theorem B2043829 : Blo 1273955 2043829 := bbase (se 5 (by rfl) ⟨95804, by rfl⟩ : syracuseStep 2043829 = 191609) (by norm_num)
theorem B1912781 : Blo 1273955 1912781 := bbase (se 3 (by rfl) ⟨358646, by rfl⟩ : syracuseStep 1912781 = 717293) (by norm_num)
theorem B1912805 : Blo 1273955 1912805 := bbase (se 4 (by rfl) ⟨179325, by rfl⟩ : syracuseStep 1912805 = 358651) (by norm_num)
theorem B2150381 : Blo 1273955 2150381 := bbase (se 3 (by rfl) ⟨403196, by rfl⟩ : syracuseStep 2150381 = 806393) (by norm_num)
theorem B2297837 : Blo 1273955 2297837 := bbase (se 3 (by rfl) ⟨430844, by rfl⟩ : syracuseStep 2297837 = 861689) (by norm_num)
theorem B1912829 : Blo 1273955 1912829 := bbase (se 3 (by rfl) ⟨358655, by rfl⟩ : syracuseStep 1912829 = 717311) (by norm_num)
theorem B1912853 : Blo 1273955 1912853 := bbase (se 6 (by rfl) ⟨44832, by rfl⟩ : syracuseStep 1912853 = 89665) (by norm_num)
theorem B2584613 : Blo 1273955 2584613 := bbase (se 4 (by rfl) ⟨242307, by rfl⟩ : syracuseStep 2584613 = 484615) (by norm_num)
theorem B4304933 : Blo 1273955 4304933 := bbase (se 4 (by rfl) ⟨403587, by rfl⟩ : syracuseStep 4304933 = 807175) (by norm_num)
theorem B1912877 : Blo 1273955 1912877 := bbase (se 3 (by rfl) ⟨358664, by rfl⟩ : syracuseStep 1912877 = 717329) (by norm_num)
theorem B1634365 : Blo 1273955 1634365 := bbase (se 3 (by rfl) ⟨306443, by rfl⟩ : syracuseStep 1634365 = 612887) (by norm_num)
theorem B1912901 : Blo 1273955 1912901 := bbase (se 4 (by rfl) ⟨179334, by rfl⟩ : syracuseStep 1912901 = 358669) (by norm_num)
theorem B1912925 : Blo 1273955 1912925 := bbase (se 3 (by rfl) ⟨358673, by rfl⟩ : syracuseStep 1912925 = 717347) (by norm_num)
theorem B2150509 : Blo 1273955 2150509 := bbase (se 3 (by rfl) ⟨403220, by rfl⟩ : syracuseStep 2150509 = 806441) (by norm_num)
theorem B1912949 : Blo 1273955 1912949 := bbase (se 5 (by rfl) ⟨89669, by rfl⟩ : syracuseStep 1912949 = 179339) (by norm_num)
theorem B1912973 : Blo 1273955 1912973 := bbase (se 3 (by rfl) ⟨358682, by rfl⟩ : syracuseStep 1912973 = 717365) (by norm_num)
theorem B1912997 : Blo 1273955 1912997 := bbase (se 4 (by rfl) ⟨179343, by rfl⟩ : syracuseStep 1912997 = 358687) (by norm_num)
theorem B1913021 : Blo 1273955 1913021 := bbase (se 3 (by rfl) ⟨358691, by rfl⟩ : syracuseStep 1913021 = 717383) (by norm_num)
theorem B2150597 : Blo 1273955 2150597 := bbase (se 4 (by rfl) ⟨201618, by rfl⟩ : syracuseStep 2150597 = 403237) (by norm_num)
theorem B2420941 : Blo 1273955 2420941 := bbase (se 3 (by rfl) ⟨453926, by rfl⟩ : syracuseStep 2420941 = 907853) (by norm_num)
theorem B1913045 : Blo 1273955 1913045 := bbase (se 7 (by rfl) ⟨22418, by rfl⟩ : syracuseStep 1913045 = 44837) (by norm_num)
theorem B1913069 : Blo 1273955 1913069 := bbase (se 3 (by rfl) ⟨358700, by rfl⟩ : syracuseStep 1913069 = 717401) (by norm_num)
theorem B1913093 : Blo 1273955 1913093 := bbase (se 4 (by rfl) ⟨179352, by rfl⟩ : syracuseStep 1913093 = 358705) (by norm_num)
theorem B1937677 : Blo 1273955 1937677 := bbase (se 3 (by rfl) ⟨363314, by rfl⟩ : syracuseStep 1937677 = 726629) (by norm_num)
theorem B1913117 : Blo 1273955 1913117 := bbase (se 3 (by rfl) ⟨358709, by rfl⟩ : syracuseStep 1913117 = 717419) (by norm_num)
theorem B1913141 : Blo 1273955 1913141 := bbase (se 5 (by rfl) ⟨89678, by rfl⟩ : syracuseStep 1913141 = 179357) (by norm_num)
theorem B2150725 : Blo 1273955 2150725 := bbase (se 4 (by rfl) ⟨201630, by rfl⟩ : syracuseStep 2150725 = 403261) (by norm_num)
theorem B1913165 : Blo 1273955 1913165 := bbase (se 3 (by rfl) ⟨358718, by rfl⟩ : syracuseStep 1913165 = 717437) (by norm_num)
theorem B2421085 : Blo 1273955 2421085 := bbase (se 3 (by rfl) ⟨453953, by rfl⟩ : syracuseStep 2421085 = 907907) (by norm_num)
theorem B1913189 : Blo 1273955 1913189 := bbase (se 4 (by rfl) ⟨179361, by rfl⟩ : syracuseStep 1913189 = 358723) (by norm_num)
theorem B1913213 : Blo 1273955 1913213 := bbase (se 3 (by rfl) ⟨358727, by rfl⟩ : syracuseStep 1913213 = 717455) (by norm_num)
theorem B4837765 : Blo 1273955 4837765 := bbase (se 4 (by rfl) ⟨453540, by rfl⟩ : syracuseStep 4837765 = 907081) (by norm_num)
theorem B1913237 : Blo 1273955 1913237 := bbase (se 6 (by rfl) ⟨44841, by rfl⟩ : syracuseStep 1913237 = 89683) (by norm_num)
theorem B2150813 : Blo 1273955 2150813 := bbase (se 3 (by rfl) ⟨403277, by rfl⟩ : syracuseStep 2150813 = 806555) (by norm_num)
theorem B1913261 : Blo 1273955 1913261 := bbase (se 3 (by rfl) ⟨358736, by rfl⟩ : syracuseStep 1913261 = 717473) (by norm_num)
theorem B6631877 : Blo 1273955 6631877 := bbase (se 4 (by rfl) ⟨621738, by rfl⟩ : syracuseStep 6631877 = 1243477) (by norm_num)
theorem B1913285 : Blo 1273955 1913285 := bbase (se 4 (by rfl) ⟨179370, by rfl⟩ : syracuseStep 1913285 = 358741) (by norm_num)
theorem B4305365 : Blo 1273955 4305365 := bbase (se 7 (by rfl) ⟨50453, by rfl⟩ : syracuseStep 4305365 = 100907) (by norm_num)
theorem B1815005 : Blo 1273955 1815005 := bbase (se 3 (by rfl) ⟨340313, by rfl⟩ : syracuseStep 1815005 = 680627) (by norm_num)
theorem B1913309 : Blo 1273955 1913309 := bbase (se 3 (by rfl) ⟨358745, by rfl⟩ : syracuseStep 1913309 = 717491) (by norm_num)
theorem B1913333 : Blo 1273955 1913333 := bbase (se 5 (by rfl) ⟨89687, by rfl⟩ : syracuseStep 1913333 = 179375) (by norm_num)
theorem B2421245 : Blo 1273955 2421245 := bbase (se 3 (by rfl) ⟨453983, by rfl⟩ : syracuseStep 2421245 = 907967) (by norm_num)
theorem B1913357 : Blo 1273955 1913357 := bbase (se 3 (by rfl) ⟨358754, by rfl⟩ : syracuseStep 1913357 = 717509) (by norm_num)
theorem B10883605 : Blo 1273955 10883605 := bbase (se 6 (by rfl) ⟨255084, by rfl⟩ : syracuseStep 10883605 = 510169) (by norm_num)
theorem B2150941 : Blo 1273955 2150941 := bbase (se 3 (by rfl) ⟨403301, by rfl⟩ : syracuseStep 2150941 = 806603) (by norm_num)
theorem B1913381 : Blo 1273955 1913381 := bbase (se 4 (by rfl) ⟨179379, by rfl⟩ : syracuseStep 1913381 = 358759) (by norm_num)
theorem B1815085 : Blo 1273955 1815085 := bbase (se 3 (by rfl) ⟨340328, by rfl⟩ : syracuseStep 1815085 = 680657) (by norm_num)
theorem B1913405 : Blo 1273955 1913405 := bbase (se 3 (by rfl) ⟨358763, by rfl⟩ : syracuseStep 1913405 = 717527) (by norm_num)
theorem B1454657 : Blo 1273955 1454657 := bbase (se 2 (by rfl) ⟨545496, by rfl⟩ : syracuseStep 1454657 = 1090993) (by norm_num)
theorem B1913429 : Blo 1273955 1913429 := bbase (se 8 (by rfl) ⟨11211, by rfl⟩ : syracuseStep 1913429 = 22423) (by norm_num)
theorem B1913453 : Blo 1273955 1913453 := bbase (se 3 (by rfl) ⟨358772, by rfl⟩ : syracuseStep 1913453 = 717545) (by norm_num)
theorem B2151029 : Blo 1273955 2151029 := bbase (se 5 (by rfl) ⟨100829, by rfl⟩ : syracuseStep 2151029 = 201659) (by norm_num)
theorem B1913477 : Blo 1273955 1913477 := bbase (se 4 (by rfl) ⟨179388, by rfl⟩ : syracuseStep 1913477 = 358777) (by norm_num)
theorem B1380997 : Blo 1273955 1380997 := bbase (se 4 (by rfl) ⟨129468, by rfl⟩ : syracuseStep 1380997 = 258937) (by norm_num)
theorem B1839757 : Blo 1273955 1839757 := bbase (se 3 (by rfl) ⟨344954, by rfl⟩ : syracuseStep 1839757 = 689909) (by norm_num)
theorem B2421389 : Blo 1273955 2421389 := bbase (se 3 (by rfl) ⟨454010, by rfl⟩ : syracuseStep 2421389 = 908021) (by norm_num)
theorem B8163989 : Blo 1273955 8163989 := bbase (se 6 (by rfl) ⟨191343, by rfl⟩ : syracuseStep 8163989 = 382687) (by norm_num)
theorem B1913501 : Blo 1273955 1913501 := bbase (se 3 (by rfl) ⟨358781, by rfl⟩ : syracuseStep 1913501 = 717563) (by norm_num)
theorem B1815205 : Blo 1273955 1815205 := bbase (se 4 (by rfl) ⟨170175, by rfl⟩ : syracuseStep 1815205 = 340351) (by norm_num)
theorem B4838069 : Blo 1273955 4838069 := bbase (se 5 (by rfl) ⟨226784, by rfl⟩ : syracuseStep 4838069 = 453569) (by norm_num)
theorem B1913525 : Blo 1273955 1913525 := bbase (se 5 (by rfl) ⟨89696, by rfl⟩ : syracuseStep 1913525 = 179393) (by norm_num)
theorem B1913549 : Blo 1273955 1913549 := bbase (se 3 (by rfl) ⟨358790, by rfl⟩ : syracuseStep 1913549 = 717581) (by norm_num)
theorem B6206165 : Blo 1273955 6206165 := bbase (se 7 (by rfl) ⟨72728, by rfl⟩ : syracuseStep 6206165 = 145457) (by norm_num)
theorem B1913573 : Blo 1273955 1913573 := bbase (se 4 (by rfl) ⟨179397, by rfl⟩ : syracuseStep 1913573 = 358795) (by norm_num)
theorem B2151157 : Blo 1273955 2151157 := bbase (se 5 (by rfl) ⟨100835, by rfl⟩ : syracuseStep 2151157 = 201671) (by norm_num)
theorem B1913597 : Blo 1273955 1913597 := bbase (se 3 (by rfl) ⟨358799, by rfl⟩ : syracuseStep 1913597 = 717599) (by norm_num)
theorem B6451973 : Blo 1273955 6451973 := bbase (se 4 (by rfl) ⟨604872, by rfl⟩ : syracuseStep 6451973 = 1209745) (by norm_num)
theorem B1815301 : Blo 1273955 1815301 := bbase (se 4 (by rfl) ⟨170184, by rfl⟩ : syracuseStep 1815301 = 340369) (by norm_num)
theorem B1913621 : Blo 1273955 1913621 := bbase (se 6 (by rfl) ⟨44850, by rfl⟩ : syracuseStep 1913621 = 89701) (by norm_num)
theorem B2724653 : Blo 1273955 2724653 := bbase (se 3 (by rfl) ⟨510872, by rfl⟩ : syracuseStep 2724653 = 1021745) (by norm_num)
theorem B1913645 : Blo 1273955 1913645 := bbase (se 3 (by rfl) ⟨358808, by rfl⟩ : syracuseStep 1913645 = 717617) (by norm_num)
theorem B1913669 : Blo 1273955 1913669 := bbase (se 4 (by rfl) ⟨179406, by rfl⟩ : syracuseStep 1913669 = 358813) (by norm_num)
theorem B2151245 : Blo 1273955 2151245 := bbase (se 3 (by rfl) ⟨403358, by rfl⟩ : syracuseStep 2151245 = 806717) (by norm_num)
theorem B1913693 : Blo 1273955 1913693 := bbase (se 3 (by rfl) ⟨358817, by rfl⟩ : syracuseStep 1913693 = 717635) (by norm_num)
theorem B1913717 : Blo 1273955 1913717 := bbase (se 5 (by rfl) ⟨89705, by rfl⟩ : syracuseStep 1913717 = 179411) (by norm_num)
theorem B4305797 : Blo 1273955 4305797 := bbase (se 4 (by rfl) ⟨403668, by rfl⟩ : syracuseStep 4305797 = 807337) (by norm_num)
theorem B1913741 : Blo 1273955 1913741 := bbase (se 3 (by rfl) ⟨358826, by rfl⟩ : syracuseStep 1913741 = 717653) (by norm_num)
theorem B12252053 : Blo 1273955 12252053 := bbase (se 6 (by rfl) ⟨287157, by rfl⟩ : syracuseStep 12252053 = 574315) (by norm_num)
theorem B1913765 : Blo 1273955 1913765 := bbase (se 4 (by rfl) ⟨179415, by rfl⟩ : syracuseStep 1913765 = 358831) (by norm_num)
theorem B1455013 : Blo 1273955 1455013 := bbase (se 4 (by rfl) ⟨136407, by rfl⟩ : syracuseStep 1455013 = 272815) (by norm_num)
theorem B2421677 : Blo 1273955 2421677 := bbase (se 3 (by rfl) ⟨454064, by rfl⟩ : syracuseStep 2421677 = 908129) (by norm_num)
theorem B2724797 : Blo 1273955 2724797 := bbase (se 3 (by rfl) ⟨510899, by rfl⟩ : syracuseStep 2724797 = 1021799) (by norm_num)
theorem B1913789 : Blo 1273955 1913789 := bbase (se 3 (by rfl) ⟨358835, by rfl⟩ : syracuseStep 1913789 = 717671) (by norm_num)
theorem B2151373 : Blo 1273955 2151373 := bbase (se 3 (by rfl) ⟨403382, by rfl⟩ : syracuseStep 2151373 = 806765) (by norm_num)
theorem B50361301 : Blo 1273955 50361301 := bbase (se 7 (by rfl) ⟨590171, by rfl⟩ : syracuseStep 50361301 = 1180343) (by norm_num)
theorem B1913813 : Blo 1273955 1913813 := bbase (se 7 (by rfl) ⟨22427, by rfl⟩ : syracuseStep 1913813 = 44855) (by norm_num)
theorem B2618333 : Blo 1273955 2618333 := bbase (se 3 (by rfl) ⟨490937, by rfl⟩ : syracuseStep 2618333 = 981875) (by norm_num)
theorem B1913837 : Blo 1273955 1913837 := bbase (se 3 (by rfl) ⟨358844, by rfl⟩ : syracuseStep 1913837 = 717689) (by norm_num)
theorem B1913861 : Blo 1273955 1913861 := bbase (se 4 (by rfl) ⟨179424, by rfl⟩ : syracuseStep 1913861 = 358849) (by norm_num)
theorem B1913885 : Blo 1273955 1913885 := bbase (se 3 (by rfl) ⟨358853, by rfl⟩ : syracuseStep 1913885 = 717707) (by norm_num)
theorem B2151461 : Blo 1273955 2151461 := bbase (se 4 (by rfl) ⟨201699, by rfl⟩ : syracuseStep 2151461 = 403399) (by norm_num)
theorem B2069557 : Blo 1273955 2069557 := bbase (se 5 (by rfl) ⟨97010, by rfl⟩ : syracuseStep 2069557 = 194021) (by norm_num)
theorem B1913909 : Blo 1273955 1913909 := bbase (se 5 (by rfl) ⟨89714, by rfl⟩ : syracuseStep 1913909 = 179429) (by norm_num)
theorem B2421829 : Blo 1273955 2421829 := bbase (se 4 (by rfl) ⟨227046, by rfl⟩ : syracuseStep 2421829 = 454093) (by norm_num)
theorem B1913933 : Blo 1273955 1913933 := bbase (se 3 (by rfl) ⟨358862, by rfl⟩ : syracuseStep 1913933 = 717725) (by norm_num)
theorem B2151589 : Blo 1273955 2151589 := bbase (se 4 (by rfl) ⟨201711, by rfl⟩ : syracuseStep 2151589 = 403423) (by norm_num)
theorem B4592821 : Blo 1273955 4592821 := bbase (se 5 (by rfl) ⟨215288, by rfl⟩ : syracuseStep 4592821 = 430577) (by norm_num)
theorem B1815797 : Blo 1273955 1815797 := bbase (se 5 (by rfl) ⟨85115, by rfl⟩ : syracuseStep 1815797 = 170231) (by norm_num)
theorem B2585845 : Blo 1273955 2585845 := bbase (se 5 (by rfl) ⟨121211, by rfl⟩ : syracuseStep 2585845 = 242423) (by norm_num)
theorem B2151677 : Blo 1273955 2151677 := bbase (se 3 (by rfl) ⟨403439, by rfl⟩ : syracuseStep 2151677 = 806879) (by norm_num)
theorem B4306229 : Blo 1273955 4306229 := bbase (se 5 (by rfl) ⟨201854, by rfl⟩ : syracuseStep 4306229 = 403709) (by norm_num)
theorem B3224893 : Blo 1273955 3224893 := bbase (se 3 (by rfl) ⟨604667, by rfl⟩ : syracuseStep 3224893 = 1209335) (by norm_num)
theorem B2422133 : Blo 1273955 2422133 := bbase (se 5 (by rfl) ⟨113537, by rfl⟩ : syracuseStep 2422133 = 227075) (by norm_num)
theorem B2151805 : Blo 1273955 2151805 := bbase (se 3 (by rfl) ⟨403463, by rfl⟩ : syracuseStep 2151805 = 806927) (by norm_num)
theorem B3225005 : Blo 1273955 3225005 := bbase (se 3 (by rfl) ⟨604688, by rfl⟩ : syracuseStep 3225005 = 1209377) (by norm_num)
theorem B2151893 : Blo 1273955 2151893 := bbase (se 7 (by rfl) ⟨25217, by rfl⟩ : syracuseStep 2151893 = 50435) (by norm_num)
theorem B2152021 : Blo 1273955 2152021 := bbase (se 8 (by rfl) ⟨12609, by rfl⟩ : syracuseStep 2152021 = 25219) (by norm_num)
theorem B3225197 : Blo 1273955 3225197 := bbase (se 3 (by rfl) ⟨604724, by rfl⟩ : syracuseStep 3225197 = 1209449) (by norm_num)
theorem B2152109 : Blo 1273955 2152109 := bbase (se 3 (by rfl) ⟨403520, by rfl⟩ : syracuseStep 2152109 = 807041) (by norm_num)
theorem B5813957 : Blo 1273955 5813957 := bbase (se 4 (by rfl) ⟨545058, by rfl⟩ : syracuseStep 5813957 = 1090117) (by norm_num)
theorem B1816349 : Blo 1273955 1816349 := bbase (se 3 (by rfl) ⟨340565, by rfl⟩ : syracuseStep 1816349 = 681131) (by norm_num)
theorem B2152237 : Blo 1273955 2152237 := bbase (se 3 (by rfl) ⟨403544, by rfl⟩ : syracuseStep 2152237 = 807089) (by norm_num)
theorem B11032373 : Blo 1273955 11032373 := bbase (se 5 (by rfl) ⟨517142, by rfl⟩ : syracuseStep 11032373 = 1034285) (by norm_num)
theorem B2152325 : Blo 1273955 2152325 := bbase (se 4 (by rfl) ⟨201780, by rfl⟩ : syracuseStep 2152325 = 403561) (by norm_num)
theorem B3225541 : Blo 1273955 3225541 := bbase (se 4 (by rfl) ⟨302394, by rfl⟩ : syracuseStep 3225541 = 604789) (by norm_num)
theorem B2152453 : Blo 1273955 2152453 := bbase (se 4 (by rfl) ⟨201792, by rfl⟩ : syracuseStep 2152453 = 403585) (by norm_num)
theorem B6453269 : Blo 1273955 6453269 := bbase (se 6 (by rfl) ⟨151248, by rfl⟩ : syracuseStep 6453269 = 302497) (by norm_num)
theorem B3225653 : Blo 1273955 3225653 := bbase (se 5 (by rfl) ⟨151202, by rfl⟩ : syracuseStep 3225653 = 302405) (by norm_num)
theorem B2152541 : Blo 1273955 2152541 := bbase (se 3 (by rfl) ⟨403601, by rfl⟩ : syracuseStep 2152541 = 807203) (by norm_num)
theorem B14514389 : Blo 1273955 14514389 := bbase (se 7 (by rfl) ⟨170090, by rfl⟩ : syracuseStep 14514389 = 340181) (by norm_num)
theorem B2152669 : Blo 1273955 2152669 := bbase (se 3 (by rfl) ⟨403625, by rfl⟩ : syracuseStep 2152669 = 807251) (by norm_num)
theorem B3225845 : Blo 1273955 3225845 := bbase (se 5 (by rfl) ⟨151211, by rfl⟩ : syracuseStep 3225845 = 302423) (by norm_num)
theorem B3062053 : Blo 1273955 3062053 := bbase (se 4 (by rfl) ⟨287067, by rfl⟩ : syracuseStep 3062053 = 574135) (by norm_num)
theorem B2152757 : Blo 1273955 2152757 := bbase (se 5 (by rfl) ⟨100910, by rfl⟩ : syracuseStep 2152757 = 201821) (by norm_num)
theorem B6207877 : Blo 1273955 6207877 := bbase (se 4 (by rfl) ⟨581988, by rfl⟩ : syracuseStep 6207877 = 1163977) (by norm_num)
theorem B4086197 : Blo 1273955 4086197 := bbase (se 5 (by rfl) ⟨191540, by rfl⟩ : syracuseStep 4086197 = 383081) (by norm_num)
theorem B2152885 : Blo 1273955 2152885 := bbase (se 5 (by rfl) ⟨100916, by rfl⟩ : syracuseStep 2152885 = 201833) (by norm_num)
theorem B10885589 : Blo 1273955 10885589 := bbase (se 7 (by rfl) ⟨127565, by rfl⟩ : syracuseStep 10885589 = 255131) (by norm_num)
theorem B1292761 : Blo 1273955 1292761 := bbase (se 2 (by rfl) ⟨484785, by rfl⟩ : syracuseStep 1292761 = 969571) (by norm_num)
theorem B2152973 : Blo 1273955 2152973 := bbase (se 3 (by rfl) ⟨403682, by rfl⟩ : syracuseStep 2152973 = 807365) (by norm_num)
theorem B2759197 : Blo 1273955 2759197 := bbase (se 3 (by rfl) ⟨517349, by rfl⟩ : syracuseStep 2759197 = 1034699) (by norm_num)
theorem B3226189 : Blo 1273955 3226189 := bbase (se 3 (by rfl) ⟨604910, by rfl⟩ : syracuseStep 3226189 = 1209821) (by norm_num)
theorem B1612381 : Blo 1273955 1612381 := bbase (se 3 (by rfl) ⟨302321, by rfl⟩ : syracuseStep 1612381 = 604643) (by norm_num)
theorem B2906741 : Blo 1273955 2906741 := bbase (se 5 (by rfl) ⟨136253, by rfl⟩ : syracuseStep 2906741 = 272507) (by norm_num)
theorem B6543989 : Blo 1273955 6543989 := bbase (se 5 (by rfl) ⟨306749, by rfl⟩ : syracuseStep 6543989 = 613499) (by norm_num)
theorem B2153101 : Blo 1273955 2153101 := bbase (se 3 (by rfl) ⟨403706, by rfl⟩ : syracuseStep 2153101 = 807413) (by norm_num)
theorem B7756469 : Blo 1273955 7756469 := bbase (se 5 (by rfl) ⟨363584, by rfl⟩ : syracuseStep 7756469 = 727169) (by norm_num)
theorem B1612477 : Blo 1273955 1612477 := bbase (se 3 (by rfl) ⟨302339, by rfl⟩ : syracuseStep 1612477 = 604679) (by norm_num)
theorem B3226301 : Blo 1273955 3226301 := bbase (se 3 (by rfl) ⟨604931, by rfl⟩ : syracuseStep 3226301 = 1209863) (by norm_num)
theorem B4840181 : Blo 1273955 4840181 := bbase (se 5 (by rfl) ⟨226883, by rfl⟩ : syracuseStep 4840181 = 453767) (by norm_num)
theorem B1530661 : Blo 1273955 1530661 := bbase (se 4 (by rfl) ⟨143499, by rfl⟩ : syracuseStep 1530661 = 286999) (by norm_num)
theorem B1612649 : Blo 1273955 1612649 := bbase (se 2 (by rfl) ⟨604743, by rfl⟩ : syracuseStep 1612649 = 1209487) (by norm_num)
theorem B3226493 : Blo 1273955 3226493 := bbase (se 3 (by rfl) ⟨604967, by rfl⟩ : syracuseStep 3226493 = 1209935) (by norm_num)
theorem B1612705 : Blo 1273955 1612705 := bbase (se 2 (by rfl) ⟨604764, by rfl⟩ : syracuseStep 1612705 = 1209529) (by norm_num)
theorem B4299749 : Blo 1273955 4299749 := bbase (se 4 (by rfl) ⟨403101, by rfl⟩ : syracuseStep 4299749 = 806203) (by norm_num)
theorem B1612801 : Blo 1273955 1612801 := bbase (se 2 (by rfl) ⟨604800, by rfl⟩ : syracuseStep 1612801 = 1209601) (by norm_num)
theorem B4840469 : Blo 1273955 4840469 := bbase (se 6 (by rfl) ⟨113448, by rfl⟩ : syracuseStep 4840469 = 226897) (by norm_num)
theorem B5446709 : Blo 1273955 5446709 := bbase (se 5 (by rfl) ⟨255314, by rfl⟩ : syracuseStep 5446709 = 510629) (by norm_num)
theorem B3628165 : Blo 1273955 3628165 := bbase (se 4 (by rfl) ⟨340140, by rfl⟩ : syracuseStep 3628165 = 680281) (by norm_num)
theorem B16333973 : Blo 1273955 16333973 := bbase (se 6 (by rfl) ⟨382827, by rfl⟩ : syracuseStep 16333973 = 765655) (by norm_num)
theorem B4594853 : Blo 1273955 4594853 := bbase (se 4 (by rfl) ⟨430767, by rfl⟩ : syracuseStep 4594853 = 861535) (by norm_num)
theorem B1612973 : Blo 1273955 1612973 := bbase (se 3 (by rfl) ⟨302432, by rfl⟩ : syracuseStep 1612973 = 604865) (by norm_num)
theorem B3226837 : Blo 1273955 3226837 := bbase (se 7 (by rfl) ⟨37814, by rfl⟩ : syracuseStep 3226837 = 75629) (by norm_num)
theorem B1613029 : Blo 1273955 1613029 := bbase (se 4 (by rfl) ⟨151221, by rfl⟩ : syracuseStep 1613029 = 302443) (by norm_num)
theorem B2866445 : Blo 1273955 2866445 := bbase (se 3 (by rfl) ⟨537458, by rfl⟩ : syracuseStep 2866445 = 1074917) (by norm_num)
theorem B6454565 : Blo 1273955 6454565 := bbase (se 4 (by rfl) ⟨605115, by rfl⟩ : syracuseStep 6454565 = 1210231) (by norm_num)
theorem B4087093 : Blo 1273955 4087093 := bbase (se 5 (by rfl) ⟨191582, by rfl⟩ : syracuseStep 4087093 = 383165) (by norm_num)
theorem B1613125 : Blo 1273955 1613125 := bbase (se 4 (by rfl) ⟨151230, by rfl⟩ : syracuseStep 1613125 = 302461) (by norm_num)
theorem B3226949 : Blo 1273955 3226949 := bbase (se 4 (by rfl) ⟨302526, by rfl⟩ : syracuseStep 3226949 = 605053) (by norm_num)
theorem B2866517 : Blo 1273955 2866517 := bbase (se 11 (by rfl) ⟨2099, by rfl⟩ : syracuseStep 2866517 = 4199) (by norm_num)
theorem B13974869 : Blo 1273955 13974869 := bbase (se 11 (by rfl) ⟨10235, by rfl⟩ : syracuseStep 13974869 = 20471) (by norm_num)
theorem B5446997 : Blo 1273955 5446997 := bbase (se 11 (by rfl) ⟨3989, by rfl⟩ : syracuseStep 5446997 = 7979) (by norm_num)
theorem B6126949 : Blo 1273955 6126949 := bbase (se 4 (by rfl) ⟨574401, by rfl⟩ : syracuseStep 6126949 = 1148803) (by norm_num)
theorem B4300181 : Blo 1273955 4300181 := bbase (se 6 (by rfl) ⟨100785, by rfl⟩ : syracuseStep 4300181 = 201571) (by norm_num)
theorem B2866589 : Blo 1273955 2866589 := bbase (se 3 (by rfl) ⟨537485, by rfl⟩ : syracuseStep 2866589 = 1074971) (by norm_num)
theorem B1310137 : Blo 1273955 1310137 := bbase (se 2 (by rfl) ⟨491301, by rfl⟩ : syracuseStep 1310137 = 982603) (by norm_num)
theorem B2866661 : Blo 1273955 2866661 := bbase (se 4 (by rfl) ⟨268749, by rfl⟩ : syracuseStep 2866661 = 537499) (by norm_num)
theorem B1613297 : Blo 1273955 1613297 := bbase (se 2 (by rfl) ⟨604986, by rfl⟩ : syracuseStep 1613297 = 1209973) (by norm_num)
theorem B3227141 : Blo 1273955 3227141 := bbase (se 4 (by rfl) ⟨302544, by rfl⟩ : syracuseStep 3227141 = 605089) (by norm_num)
theorem B1613353 : Blo 1273955 1613353 := bbase (se 2 (by rfl) ⟨605007, by rfl⟩ : syracuseStep 1613353 = 1210015) (by norm_num)
theorem B2866733 : Blo 1273955 2866733 := bbase (se 3 (by rfl) ⟨537512, by rfl⟩ : syracuseStep 2866733 = 1075025) (by norm_num)
theorem B6889013 : Blo 1273955 6889013 := bbase (se 5 (by rfl) ⟨322922, by rfl⟩ : syracuseStep 6889013 = 645845) (by norm_num)
theorem B3448421 : Blo 1273955 3448421 := bbase (se 4 (by rfl) ⟨323289, by rfl⟩ : syracuseStep 3448421 = 646579) (by norm_num)
theorem B2866805 : Blo 1273955 2866805 := bbase (se 5 (by rfl) ⟨134381, by rfl⟩ : syracuseStep 2866805 = 268763) (by norm_num)
theorem B1433209 : Blo 1273955 1433209 := bbase (se 2 (by rfl) ⟨537453, by rfl⟩ : syracuseStep 1433209 = 1074907) (by norm_num)
theorem B1613449 : Blo 1273955 1613449 := bbase (se 2 (by rfl) ⟨605043, by rfl⟩ : syracuseStep 1613449 = 1210087) (by norm_num)
theorem B3063437 : Blo 1273955 3063437 := bbase (se 3 (by rfl) ⟨574394, by rfl⟩ : syracuseStep 3063437 = 1148789) (by norm_num)
theorem B1433245 : Blo 1273955 1433245 := bbase (se 3 (by rfl) ⟨268733, by rfl⟩ : syracuseStep 1433245 = 537467) (by norm_num)
theorem B2866877 : Blo 1273955 2866877 := bbase (se 3 (by rfl) ⟨537539, by rfl⟩ : syracuseStep 2866877 = 1075079) (by norm_num)
theorem B1433281 : Blo 1273955 1433281 := bbase (se 2 (by rfl) ⟨537480, by rfl⟩ : syracuseStep 1433281 = 1074961) (by norm_num)
theorem B4087493 : Blo 1273955 4087493 := bbase (se 4 (by rfl) ⟨383202, by rfl⟩ : syracuseStep 4087493 = 766405) (by norm_num)
theorem B1433317 : Blo 1273955 1433317 := bbase (se 4 (by rfl) ⟨134373, by rfl⟩ : syracuseStep 1433317 = 268747) (by norm_num)
theorem B2866949 : Blo 1273955 2866949 := bbase (se 4 (by rfl) ⟨268776, by rfl⟩ : syracuseStep 2866949 = 537553) (by norm_num)
theorem B1433353 : Blo 1273955 1433353 := bbase (se 2 (by rfl) ⟨537507, by rfl⟩ : syracuseStep 1433353 = 1075015) (by norm_num)
theorem B1433389 : Blo 1273955 1433389 := bbase (se 3 (by rfl) ⟨268760, by rfl⟩ : syracuseStep 1433389 = 537521) (by norm_num)
theorem B1613621 : Blo 1273955 1613621 := bbase (se 5 (by rfl) ⟨75638, by rfl⟩ : syracuseStep 1613621 = 151277) (by norm_num)
theorem B10485557 : Blo 1273955 10485557 := bbase (se 5 (by rfl) ⟨491510, by rfl⟩ : syracuseStep 10485557 = 983021) (by norm_num)
theorem B4300613 : Blo 1273955 4300613 := bbase (se 4 (by rfl) ⟨403182, by rfl⟩ : syracuseStep 4300613 = 806365) (by norm_num)
theorem B2867021 : Blo 1273955 2867021 := bbase (se 3 (by rfl) ⟨537566, by rfl⟩ : syracuseStep 2867021 = 1075133) (by norm_num)
theorem B3063629 : Blo 1273955 3063629 := bbase (se 3 (by rfl) ⟨574430, by rfl⟩ : syracuseStep 3063629 = 1148861) (by norm_num)
theorem B1433425 : Blo 1273955 1433425 := bbase (se 2 (by rfl) ⟨537534, by rfl⟩ : syracuseStep 1433425 = 1075069) (by norm_num)
theorem B3227485 : Blo 1273955 3227485 := bbase (se 3 (by rfl) ⟨605153, by rfl⟩ : syracuseStep 3227485 = 1210307) (by norm_num)
theorem B1613677 : Blo 1273955 1613677 := bbase (se 3 (by rfl) ⟨302564, by rfl⟩ : syracuseStep 1613677 = 605129) (by norm_num)
theorem B1433461 : Blo 1273955 1433461 := bbase (se 5 (by rfl) ⟨67193, by rfl⟩ : syracuseStep 1433461 = 134387) (by norm_num)
theorem B2867093 : Blo 1273955 2867093 := bbase (se 6 (by rfl) ⟨67197, by rfl⟩ : syracuseStep 2867093 = 134395) (by norm_num)
theorem B7364501 : Blo 1273955 7364501 := bbase (se 6 (by rfl) ⟨172605, by rfl⟩ : syracuseStep 7364501 = 345211) (by norm_num)
theorem B1433497 : Blo 1273955 1433497 := bbase (se 2 (by rfl) ⟨537561, by rfl⟩ : syracuseStep 1433497 = 1075123) (by norm_num)
theorem B1310629 : Blo 1273955 1310629 := bbase (se 4 (by rfl) ⟨122871, by rfl⟩ : syracuseStep 1310629 = 245743) (by norm_num)
theorem B1433533 : Blo 1273955 1433533 := bbase (se 3 (by rfl) ⟨268787, by rfl⟩ : syracuseStep 1433533 = 537575) (by norm_num)
theorem B1613773 : Blo 1273955 1613773 := bbase (se 3 (by rfl) ⟨302582, by rfl⟩ : syracuseStep 1613773 = 605165) (by norm_num)
theorem B3227597 : Blo 1273955 3227597 := bbase (se 3 (by rfl) ⟨605174, by rfl⟩ : syracuseStep 3227597 = 1210349) (by norm_num)
theorem B2867165 : Blo 1273955 2867165 := bbase (se 3 (by rfl) ⟨537593, by rfl⟩ : syracuseStep 2867165 = 1075187) (by norm_num)
theorem B1433569 : Blo 1273955 1433569 := bbase (se 2 (by rfl) ⟨537588, by rfl⟩ : syracuseStep 1433569 = 1075177) (by norm_num)
theorem B2179153 : Blo 1273955 2179153 := bstep (se 2 (by rfl) ⟨817182, by rfl⟩ : syracuseStep 2179153 = 1634365) B1634365
theorem B1433731 : Blo 1273955 1433731 := bstep (se 1 (by rfl) ⟨1075298, by rfl⟩ : syracuseStep 1433731 = 2150597) B2150597
theorem B2867345 : Blo 1273955 2867345 := bstep (se 2 (by rfl) ⟨1075254, by rfl⟩ : syracuseStep 2867345 = 2150509) B2150509
theorem B2867363 : Blo 1273955 2867363 := bstep (se 1 (by rfl) ⟨2150522, by rfl⟩ : syracuseStep 2867363 = 4301045) B4301045
theorem B6545585 : Blo 1273955 6545585 := bstep (se 2 (by rfl) ⟨2454594, by rfl⟩ : syracuseStep 6545585 = 4909189) B4909189
theorem B6455537 : Blo 1273955 6455537 := bstep (se 2 (by rfl) ⟨2420826, by rfl⟩ : syracuseStep 6455537 = 4841653) B4841653
theorem B3227921 : Blo 1273955 3227921 := bstep (se 2 (by rfl) ⟨1210470, by rfl⟩ : syracuseStep 3227921 = 2420941) B2420941
theorem B1433875 : Blo 1273955 1433875 := bstep (se 1 (by rfl) ⟨1075406, by rfl⟩ : syracuseStep 1433875 = 2150813) B2150813
theorem B3227971 : Blo 1273955 3227971 := bstep (se 1 (by rfl) ⟨2420978, by rfl⟩ : syracuseStep 3227971 = 4841957) B4841957
theorem B1614163 : Blo 1273955 1614163 := bstep (se 1 (by rfl) ⟨1210622, by rfl⟩ : syracuseStep 1614163 = 2421245) B2421245
theorem B1434019 : Blo 1273955 1434019 := bstep (se 1 (by rfl) ⟨1075514, by rfl⟩ : syracuseStep 1434019 = 2151029) B2151029
theorem B2867633 : Blo 1273955 2867633 := bstep (se 2 (by rfl) ⟨1075362, by rfl⟩ : syracuseStep 2867633 = 2150725) B2150725
theorem B1614259 : Blo 1273955 1614259 := bstep (se 1 (by rfl) ⟨1210694, by rfl⟩ : syracuseStep 1614259 = 2421389) B2421389
theorem B2867651 : Blo 1273955 2867651 := bstep (se 1 (by rfl) ⟨2150738, by rfl⟩ : syracuseStep 2867651 = 4301477) B4301477
theorem B4301261 : Blo 1273955 4301261 := bstep (se 3 (by rfl) ⟨806486, by rfl⟩ : syracuseStep 4301261 = 1612973) B1612973
theorem B3228113 : Blo 1273955 3228113 := bstep (se 2 (by rfl) ⟨1210542, by rfl⟩ : syracuseStep 3228113 = 2421085) B2421085
theorem B4137443 : Blo 1273955 4137443 := bstep (se 1 (by rfl) ⟨3103082, by rfl⟩ : syracuseStep 4137443 = 6206165) B6206165
theorem B4301315 : Blo 1273955 4301315 := bstep (se 1 (by rfl) ⟨3225986, by rfl⟩ : syracuseStep 4301315 = 6451973) B6451973
theorem B1434163 : Blo 1273955 1434163 := bstep (se 1 (by rfl) ⟨1075622, by rfl⟩ : syracuseStep 1434163 = 2151245) B2151245
theorem B8168035 : Blo 1273955 8168035 := bstep (se 1 (by rfl) ⟨6126026, by rfl⟩ : syracuseStep 8168035 = 12252053) B12252053
theorem B3629681 : Blo 1273955 3629681 := bstep (se 2 (by rfl) ⟨1361130, by rfl⟩ : syracuseStep 3629681 = 2722261) B2722261
theorem B4842125 : Blo 1273955 4842125 := bstep (se 3 (by rfl) ⟨907898, by rfl⟩ : syracuseStep 4842125 = 1815797) B1815797
theorem B1745555 : Blo 1273955 1745555 := bstep (se 1 (by rfl) ⟨1309166, by rfl⟩ : syracuseStep 1745555 = 2618333) B2618333
theorem B1434307 : Blo 1273955 1434307 := bstep (se 1 (by rfl) ⟨1075730, by rfl⟩ : syracuseStep 1434307 = 2151461) B2151461
theorem B3678929 : Blo 1273955 3678929 := bstep (se 2 (by rfl) ⟨1379598, by rfl⟩ : syracuseStep 3678929 = 2759197) B2759197
theorem B2867921 : Blo 1273955 2867921 := bstep (se 2 (by rfl) ⟨1075470, by rfl⟩ : syracuseStep 2867921 = 2150941) B2150941
theorem B2867939 : Blo 1273955 2867939 := bstep (se 1 (by rfl) ⟨2150954, by rfl⟩ : syracuseStep 2867939 = 4301909) B4301909
theorem B4358897 : Blo 1273955 4358897 := bstep (se 2 (by rfl) ⟨1634586, by rfl⟩ : syracuseStep 4358897 = 3269173) B3269173
theorem B4301585 : Blo 1273955 4301585 := bstep (se 2 (by rfl) ⟨1613094, by rfl⟩ : syracuseStep 4301585 = 3226189) B3226189
theorem B3629873 : Blo 1273955 3629873 := bstep (se 2 (by rfl) ⟨1361202, by rfl⟩ : syracuseStep 3629873 = 2722405) B2722405
theorem B32686901 : Blo 1273955 32686901 := bstep (se 5 (by rfl) ⟨1532198, by rfl⟩ : syracuseStep 32686901 = 3064397) B3064397
theorem B1434451 : Blo 1273955 1434451 := bstep (se 1 (by rfl) ⟨1075838, by rfl⟩ : syracuseStep 1434451 = 2151677) B2151677
theorem B1614755 : Blo 1273955 1614755 := bstep (se 1 (by rfl) ⟨1211066, by rfl⟩ : syracuseStep 1614755 = 2422133) B2422133
theorem B1434595 : Blo 1273955 1434595 := bstep (se 1 (by rfl) ⟨1075946, by rfl⟩ : syracuseStep 1434595 = 2151893) B2151893
theorem B2868209 : Blo 1273955 2868209 := bstep (se 2 (by rfl) ⟨1075578, by rfl⟩ : syracuseStep 2868209 = 2151157) B2151157
theorem B2868227 : Blo 1273955 2868227 := bstep (se 1 (by rfl) ⟨2151170, by rfl⟩ : syracuseStep 2868227 = 4302341) B4302341
theorem B2040881 : Blo 1273955 2040881 := bstep (se 2 (by rfl) ⟨765330, by rfl⟩ : syracuseStep 2040881 = 1530661) B1530661
theorem B1434739 : Blo 1273955 1434739 := bstep (se 1 (by rfl) ⟨1076054, by rfl⟩ : syracuseStep 1434739 = 2152109) B2152109
theorem B1434883 : Blo 1273955 1434883 := bstep (se 1 (by rfl) ⟨1076162, by rfl⟩ : syracuseStep 1434883 = 2152325) B2152325
theorem B2868497 : Blo 1273955 2868497 := bstep (se 2 (by rfl) ⟨1075686, by rfl⟩ : syracuseStep 2868497 = 2151373) B2151373
theorem B2868515 : Blo 1273955 2868515 := bstep (se 1 (by rfl) ⟨2151386, by rfl⟩ : syracuseStep 2868515 = 4302773) B4302773
theorem B4138285 : Blo 1273955 4138285 := bstep (se 3 (by rfl) ⟨775928, by rfl⟩ : syracuseStep 4138285 = 1551857) B1551857
theorem B4302125 : Blo 1273955 4302125 := bstep (se 3 (by rfl) ⟨806648, by rfl⟩ : syracuseStep 4302125 = 1613297) B1613297
theorem B2721073 : Blo 1273955 2721073 := bstep (se 2 (by rfl) ⟨1020402, by rfl⟩ : syracuseStep 2721073 = 2040805) B2040805
theorem B4302179 : Blo 1273955 4302179 := bstep (se 1 (by rfl) ⟨3226634, by rfl⟩ : syracuseStep 4302179 = 6453269) B6453269
theorem B1435027 : Blo 1273955 1435027 := bstep (se 1 (by rfl) ⟨1076270, by rfl⟩ : syracuseStep 1435027 = 2152541) B2152541
theorem B4842929 : Blo 1273955 4842929 := bstep (se 2 (by rfl) ⟨1816098, by rfl⟩ : syracuseStep 4842929 = 3632197) B3632197
theorem B3229105 : Blo 1273955 3229105 := bstep (se 2 (by rfl) ⟨1210914, by rfl⟩ : syracuseStep 3229105 = 2421829) B2421829
theorem B9676259 : Blo 1273955 9676259 := bstep (se 1 (by rfl) ⟨7257194, by rfl⟩ : syracuseStep 9676259 = 14514389) B14514389
theorem B5596685 : Blo 1273955 5596685 := bstep (se 3 (by rfl) ⟨1049378, by rfl⟩ : syracuseStep 5596685 = 2098757) B2098757
theorem B1435171 : Blo 1273955 1435171 := bstep (se 1 (by rfl) ⟨1076378, by rfl⟩ : syracuseStep 1435171 = 2152757) B2152757
theorem B2868785 : Blo 1273955 2868785 := bstep (se 2 (by rfl) ⟨1075794, by rfl⟩ : syracuseStep 2868785 = 2151589) B2151589
theorem B1361459 : Blo 1273955 1361459 := bstep (se 1 (by rfl) ⟨1021094, by rfl⟩ : syracuseStep 1361459 = 2042189) B2042189
theorem B2868803 : Blo 1273955 2868803 := bstep (se 1 (by rfl) ⟨2151602, by rfl⟩ : syracuseStep 2868803 = 4303205) B4303205
theorem B4302449 : Blo 1273955 4302449 := bstep (se 2 (by rfl) ⟨1613418, by rfl⟩ : syracuseStep 4302449 = 3226837) B3226837
theorem B37774961 : Blo 1273955 37774961 := bstep (se 2 (by rfl) ⟨14165610, by rfl⟩ : syracuseStep 37774961 = 28331221) B28331221
theorem B6456995 : Blo 1273955 6456995 := bstep (se 1 (by rfl) ⟨4842746, by rfl⟩ : syracuseStep 6456995 = 9685493) B9685493
theorem B1435315 : Blo 1273955 1435315 := bstep (se 1 (by rfl) ⟨1076486, by rfl⟩ : syracuseStep 1435315 = 2152973) B2152973
theorem B3229379 : Blo 1273955 3229379 := bstep (se 1 (by rfl) ⟨2422034, by rfl⟩ : syracuseStep 3229379 = 4844069) B4844069
theorem B5449457 : Blo 1273955 5449457 := bstep (se 2 (by rfl) ⟨2043546, by rfl⟩ : syracuseStep 5449457 = 4087093) B4087093
theorem B3630865 : Blo 1273955 3630865 := bstep (se 2 (by rfl) ⟨1361574, by rfl⟩ : syracuseStep 3630865 = 2723149) B2723149
theorem B5170979 : Blo 1273955 5170979 := bstep (se 1 (by rfl) ⟨3878234, by rfl⟩ : syracuseStep 5170979 = 7756469) B7756469
theorem B8169265 : Blo 1273955 8169265 := bstep (se 2 (by rfl) ⟨3063474, by rfl⟩ : syracuseStep 8169265 = 6126949) B6126949
theorem B6211405 : Blo 1273955 6211405 := bstep (se 3 (by rfl) ⟨1164638, by rfl⟩ : syracuseStep 6211405 = 2329277) B2329277
theorem B2869073 : Blo 1273955 2869073 := bstep (se 2 (by rfl) ⟨1075902, by rfl⟩ : syracuseStep 2869073 = 2151805) B2151805
theorem B2869091 : Blo 1273955 2869091 := bstep (se 1 (by rfl) ⟨2151818, by rfl⟩ : syracuseStep 2869091 = 4303637) B4303637
theorem B3229571 : Blo 1273955 3229571 := bstep (se 1 (by rfl) ⟨2422178, by rfl⟩ : syracuseStep 3229571 = 4844357) B4844357
theorem B3631139 : Blo 1273955 3631139 := bstep (se 1 (by rfl) ⟨2723354, by rfl⟩ : syracuseStep 3631139 = 5446709) B5446709
theorem B4843597 : Blo 1273955 4843597 := bstep (se 3 (by rfl) ⟨908174, by rfl⟩ : syracuseStep 4843597 = 1816349) B1816349
theorem B10889315 : Blo 1273955 10889315 := bstep (se 1 (by rfl) ⟨8166986, by rfl⟩ : syracuseStep 10889315 = 16333973) B16333973
theorem B2869361 : Blo 1273955 2869361 := bstep (se 2 (by rfl) ⟨1076010, by rfl⟩ : syracuseStep 2869361 = 2152021) B2152021
theorem B2869379 : Blo 1273955 2869379 := bstep (se 1 (by rfl) ⟨2152034, by rfl⟩ : syracuseStep 2869379 = 4304069) B4304069
theorem B7260293 : Blo 1273955 7260293 := bstep (se 4 (by rfl) ⟨680652, by rfl⟩ : syracuseStep 7260293 = 1361305) B1361305
theorem B29419661 : Blo 1273955 29419661 := bstep (se 3 (by rfl) ⟨5516186, by rfl⟩ : syracuseStep 29419661 = 11032373) B11032373
theorem B4302989 : Blo 1273955 4302989 := bstep (se 3 (by rfl) ⟨806810, by rfl⟩ : syracuseStep 4302989 = 1613621) B1613621
theorem B1910945 : Blo 1273955 1910945 := bstep (se 2 (by rfl) ⟨716604, by rfl⟩ : syracuseStep 1910945 = 1433209) B1433209
theorem B1910963 : Blo 1273955 1910963 := bstep (se 1 (by rfl) ⟨1433222, by rfl⟩ : syracuseStep 1910963 = 2866445) B2866445
theorem B4303043 : Blo 1273955 4303043 := bstep (se 1 (by rfl) ⟨3227282, by rfl⟩ : syracuseStep 4303043 = 6454565) B6454565
theorem B7760069 : Blo 1273955 7760069 := bstep (se 4 (by rfl) ⟨727506, by rfl⟩ : syracuseStep 7760069 = 1455013) B1455013
theorem B1910993 : Blo 1273955 1910993 := bstep (se 2 (by rfl) ⟨716622, by rfl⟩ : syracuseStep 1910993 = 1433245) B1433245
theorem B1911011 : Blo 1273955 1911011 := bstep (se 1 (by rfl) ⟨1433258, by rfl⟩ : syracuseStep 1911011 = 2866517) B2866517
theorem B9316579 : Blo 1273955 9316579 := bstep (se 1 (by rfl) ⟨6987434, by rfl⟩ : syracuseStep 9316579 = 13974869) B13974869
theorem B3631331 : Blo 1273955 3631331 := bstep (se 1 (by rfl) ⟨2723498, by rfl⟩ : syracuseStep 3631331 = 5446997) B5446997
theorem B1911041 : Blo 1273955 1911041 := bstep (se 2 (by rfl) ⟨716640, by rfl⟩ : syracuseStep 1911041 = 1433281) B1433281
theorem B1911059 : Blo 1273955 1911059 := bstep (se 1 (by rfl) ⟨1433294, by rfl⟩ : syracuseStep 1911059 = 2866589) B2866589
theorem B1911089 : Blo 1273955 1911089 := bstep (se 2 (by rfl) ⟨716658, by rfl⟩ : syracuseStep 1911089 = 1433317) B1433317
theorem B1911107 : Blo 1273955 1911107 := bstep (se 1 (by rfl) ⟨1433330, by rfl⟩ : syracuseStep 1911107 = 2866661) B2866661
theorem B2451793 : Blo 1273955 2451793 := bstep (se 2 (by rfl) ⟨919422, by rfl⟩ : syracuseStep 2451793 = 1838845) B1838845
theorem B1911137 : Blo 1273955 1911137 := bstep (se 2 (by rfl) ⟨716676, by rfl⟩ : syracuseStep 1911137 = 1433353) B1433353
theorem B1911155 : Blo 1273955 1911155 := bstep (se 1 (by rfl) ⟨1433366, by rfl⟩ : syracuseStep 1911155 = 2866733) B2866733
theorem B66218381 : Blo 1273955 66218381 := bstep (se 3 (by rfl) ⟨12415946, by rfl⟩ : syracuseStep 66218381 = 24831893) B24831893
theorem B5450125 : Blo 1273955 5450125 := bstep (se 3 (by rfl) ⟨1021898, by rfl⟩ : syracuseStep 5450125 = 2043797) B2043797
theorem B1911185 : Blo 1273955 1911185 := bstep (se 2 (by rfl) ⟨716694, by rfl⟩ : syracuseStep 1911185 = 1433389) B1433389
theorem B2869649 : Blo 1273955 2869649 := bstep (se 2 (by rfl) ⟨1076118, by rfl⟩ : syracuseStep 2869649 = 2152237) B2152237
theorem B1911203 : Blo 1273955 1911203 := bstep (se 1 (by rfl) ⟨1433402, by rfl⟩ : syracuseStep 1911203 = 2866805) B2866805
theorem B2869667 : Blo 1273955 2869667 := bstep (se 1 (by rfl) ⟨2152250, by rfl⟩ : syracuseStep 2869667 = 4304501) B4304501
theorem B2042291 : Blo 1273955 2042291 := bstep (se 1 (by rfl) ⟨1531718, by rfl⟩ : syracuseStep 2042291 = 3063437) B3063437
theorem B1911233 : Blo 1273955 1911233 := bstep (se 2 (by rfl) ⟨716712, by rfl⟩ : syracuseStep 1911233 = 1433425) B1433425
theorem B6457805 : Blo 1273955 6457805 := bstep (se 3 (by rfl) ⟨1210838, by rfl⟩ : syracuseStep 6457805 = 2421677) B2421677
theorem B4303313 : Blo 1273955 4303313 := bstep (se 2 (by rfl) ⟨1613742, by rfl⟩ : syracuseStep 4303313 = 3227485) B3227485
theorem B1911251 : Blo 1273955 1911251 := bstep (se 1 (by rfl) ⟨1433438, by rfl⟩ : syracuseStep 1911251 = 2866877) B2866877
theorem B1911281 : Blo 1273955 1911281 := bstep (se 2 (by rfl) ⟨716730, by rfl⟩ : syracuseStep 1911281 = 1433461) B1433461
theorem B1911299 : Blo 1273955 1911299 := bstep (se 1 (by rfl) ⟨1433474, by rfl⟩ : syracuseStep 1911299 = 2866949) B2866949
theorem B2419217 : Blo 1273955 2419217 := bstep (se 2 (by rfl) ⟨907206, by rfl⟩ : syracuseStep 2419217 = 1814413) B1814413
theorem B1911329 : Blo 1273955 1911329 := bstep (se 2 (by rfl) ⟨716748, by rfl⟩ : syracuseStep 1911329 = 1433497) B1433497
theorem B6990371 : Blo 1273955 6990371 := bstep (se 1 (by rfl) ⟨5242778, by rfl⟩ : syracuseStep 6990371 = 10485557) B10485557
theorem B1362467 : Blo 1273955 1362467 := bstep (se 1 (by rfl) ⟨1021850, by rfl⟩ : syracuseStep 1362467 = 2043701) B2043701
theorem B1747505 : Blo 1273955 1747505 := bstep (se 2 (by rfl) ⟨655314, by rfl⟩ : syracuseStep 1747505 = 1310629) B1310629
theorem B1911347 : Blo 1273955 1911347 := bstep (se 1 (by rfl) ⟨1433510, by rfl⟩ : syracuseStep 1911347 = 2867021) B2867021
theorem B2042419 : Blo 1273955 2042419 := bstep (se 1 (by rfl) ⟨1531814, by rfl⟩ : syracuseStep 2042419 = 3063629) B3063629
theorem B7260749 : Blo 1273955 7260749 := bstep (se 3 (by rfl) ⟨1361390, by rfl⟩ : syracuseStep 7260749 = 2722781) B2722781
theorem B1911377 : Blo 1273955 1911377 := bstep (se 2 (by rfl) ⟨716766, by rfl⟩ : syracuseStep 1911377 = 1433533) B1433533
theorem B1911395 : Blo 1273955 1911395 := bstep (se 1 (by rfl) ⟨1433546, by rfl⟩ : syracuseStep 1911395 = 2867093) B2867093
theorem B4082275 : Blo 1273955 4082275 := bstep (se 1 (by rfl) ⟨3061706, by rfl⟩ : syracuseStep 4082275 = 6123413) B6123413
theorem B4909667 : Blo 1273955 4909667 := bstep (se 1 (by rfl) ⟨3682250, by rfl⟩ : syracuseStep 4909667 = 7364501) B7364501
theorem B1911425 : Blo 1273955 1911425 := bstep (se 2 (by rfl) ⟨716784, by rfl⟩ : syracuseStep 1911425 = 1433569) B1433569
theorem B1911443 : Blo 1273955 1911443 := bstep (se 1 (by rfl) ⟨1433582, by rfl⟩ : syracuseStep 1911443 = 2867165) B2867165
theorem B1911473 : Blo 1273955 1911473 := bstep (se 2 (by rfl) ⟨716802, by rfl⟩ : syracuseStep 1911473 = 1433605) B1433605
theorem B2869937 : Blo 1273955 2869937 := bstep (se 2 (by rfl) ⟨1076226, by rfl⟩ : syracuseStep 2869937 = 2152453) B2152453
theorem B1911491 : Blo 1273955 1911491 := bstep (se 1 (by rfl) ⟨1433618, by rfl⟩ : syracuseStep 1911491 = 2867237) B2867237
theorem B1723075 : Blo 1273955 1723075 := bstep (se 1 (by rfl) ⟨1292306, by rfl⟩ : syracuseStep 1723075 = 2584613) B2584613
theorem B2869955 : Blo 1273955 2869955 := bstep (se 1 (by rfl) ⟨2152466, by rfl⟩ : syracuseStep 2869955 = 4304933) B4304933
theorem B1911521 : Blo 1273955 1911521 := bstep (se 2 (by rfl) ⟨716820, by rfl⟩ : syracuseStep 1911521 = 1433641) B1433641
theorem B1911539 : Blo 1273955 1911539 := bstep (se 1 (by rfl) ⟨1433654, by rfl⟩ : syracuseStep 1911539 = 2867309) B2867309
theorem B1911569 : Blo 1273955 1911569 := bstep (se 2 (by rfl) ⟨716838, by rfl⟩ : syracuseStep 1911569 = 1433677) B1433677
theorem B1911587 : Blo 1273955 1911587 := bstep (se 1 (by rfl) ⟨1433690, by rfl⟩ : syracuseStep 1911587 = 2867381) B2867381
theorem B1911617 : Blo 1273955 1911617 := bstep (se 2 (by rfl) ⟨716856, by rfl⟩ : syracuseStep 1911617 = 1433713) B1433713
theorem B1911635 : Blo 1273955 1911635 := bstep (se 1 (by rfl) ⟨1433726, by rfl⟩ : syracuseStep 1911635 = 2867453) B2867453
theorem B4844387 : Blo 1273955 4844387 := bstep (se 1 (by rfl) ⟨3633290, by rfl⟩ : syracuseStep 4844387 = 7266581) B7266581
theorem B1911665 : Blo 1273955 1911665 := bstep (se 2 (by rfl) ⟨716874, by rfl⟩ : syracuseStep 1911665 = 1433749) B1433749
theorem B1911683 : Blo 1273955 1911683 := bstep (se 1 (by rfl) ⟨1433762, by rfl⟩ : syracuseStep 1911683 = 2867525) B2867525
theorem B1911713 : Blo 1273955 1911713 := bstep (se 2 (by rfl) ⟨716892, by rfl⟩ : syracuseStep 1911713 = 1433785) B1433785
theorem B1911731 : Blo 1273955 1911731 := bstep (se 1 (by rfl) ⟨1433798, by rfl⟩ : syracuseStep 1911731 = 2867597) B2867597
theorem B11037637 : Blo 1273955 11037637 := bstep (se 4 (by rfl) ⟨1034778, by rfl⟩ : syracuseStep 11037637 = 2069557) B2069557
theorem B1911761 : Blo 1273955 1911761 := bstep (se 2 (by rfl) ⟨716910, by rfl⟩ : syracuseStep 1911761 = 1433821) B1433821
theorem B2870225 : Blo 1273955 2870225 := bstep (se 2 (by rfl) ⟨1076334, by rfl⟩ : syracuseStep 2870225 = 2152669) B2152669
theorem B1911779 : Blo 1273955 1911779 := bstep (se 1 (by rfl) ⟨1433834, by rfl⟩ : syracuseStep 1911779 = 2867669) B2867669
theorem B2870243 : Blo 1273955 2870243 := bstep (se 1 (by rfl) ⟨2152682, by rfl⟩ : syracuseStep 2870243 = 4305365) B4305365
theorem B4303853 : Blo 1273955 4303853 := bstep (se 3 (by rfl) ⟨806972, by rfl⟩ : syracuseStep 4303853 = 1613945) B1613945
theorem B1911809 : Blo 1273955 1911809 := bstep (se 2 (by rfl) ⟨716928, by rfl⟩ : syracuseStep 1911809 = 1433857) B1433857
theorem B3632141 : Blo 1273955 3632141 := bstep (se 3 (by rfl) ⟨681026, by rfl⟩ : syracuseStep 3632141 = 1362053) B1362053
theorem B2583569 : Blo 1273955 2583569 := bstep (se 2 (by rfl) ⟨968838, by rfl⟩ : syracuseStep 2583569 = 1937677) B1937677
theorem B1911827 : Blo 1273955 1911827 := bstep (se 1 (by rfl) ⟨1433870, by rfl⟩ : syracuseStep 1911827 = 2867741) B2867741
theorem B4303907 : Blo 1273955 4303907 := bstep (se 1 (by rfl) ⟨3227930, by rfl⟩ : syracuseStep 4303907 = 6455861) B6455861
theorem B4082737 : Blo 1273955 4082737 := bstep (se 2 (by rfl) ⟨1531026, by rfl⟩ : syracuseStep 4082737 = 3062053) B3062053
theorem B1911857 : Blo 1273955 1911857 := bstep (se 2 (by rfl) ⟨716946, by rfl⟩ : syracuseStep 1911857 = 1433893) B1433893
theorem B1911875 : Blo 1273955 1911875 := bstep (se 1 (by rfl) ⟨1433906, by rfl⟩ : syracuseStep 1911875 = 2867813) B2867813
theorem B1911905 : Blo 1273955 1911905 := bstep (se 2 (by rfl) ⟨716964, by rfl⟩ : syracuseStep 1911905 = 1433929) B1433929
theorem B2042977 : Blo 1273955 2042977 := bstep (se 2 (by rfl) ⟨766116, by rfl⟩ : syracuseStep 2042977 = 1532233) B1532233
theorem B5442659 : Blo 1273955 5442659 := bstep (se 1 (by rfl) ⟨4081994, by rfl⟩ : syracuseStep 5442659 = 8163989) B8163989
theorem B1911923 : Blo 1273955 1911923 := bstep (se 1 (by rfl) ⟨1433942, by rfl⟩ : syracuseStep 1911923 = 2867885) B2867885
theorem B1911953 : Blo 1273955 1911953 := bstep (se 2 (by rfl) ⟨716982, by rfl⟩ : syracuseStep 1911953 = 1433965) B1433965
theorem B1911971 : Blo 1273955 1911971 := bstep (se 1 (by rfl) ⟨1433978, by rfl⟩ : syracuseStep 1911971 = 2867957) B2867957
theorem B6450353 : Blo 1273955 6450353 := bstep (se 2 (by rfl) ⟨2418882, by rfl⟩ : syracuseStep 6450353 = 4837765) B4837765
theorem B8277169 : Blo 1273955 8277169 := bstep (se 2 (by rfl) ⟨3103938, by rfl⟩ : syracuseStep 8277169 = 6207877) B6207877
theorem B1912001 : Blo 1273955 1912001 := bstep (se 2 (by rfl) ⟨717000, by rfl⟩ : syracuseStep 1912001 = 1434001) B1434001
theorem B3730627 : Blo 1273955 3730627 := bstep (se 1 (by rfl) ⟨2797970, by rfl⟩ : syracuseStep 3730627 = 5595941) B5595941
theorem B3632323 : Blo 1273955 3632323 := bstep (se 1 (by rfl) ⟨2724242, by rfl⟩ : syracuseStep 3632323 = 5448485) B5448485
theorem B1912019 : Blo 1273955 1912019 := bstep (se 1 (by rfl) ⟨1434014, by rfl⟩ : syracuseStep 1912019 = 2868029) B2868029
theorem B1912049 : Blo 1273955 1912049 := bstep (se 2 (by rfl) ⟨717018, by rfl⟩ : syracuseStep 1912049 = 1434037) B1434037
theorem B2870513 : Blo 1273955 2870513 := bstep (se 2 (by rfl) ⟨1076442, by rfl⟩ : syracuseStep 2870513 = 2152885) B2152885
theorem B1912067 : Blo 1273955 1912067 := bstep (se 1 (by rfl) ⟨1434050, by rfl⟩ : syracuseStep 1912067 = 2868101) B2868101
theorem B2870531 : Blo 1273955 2870531 := bstep (se 1 (by rfl) ⟨2152898, by rfl⟩ : syracuseStep 2870531 = 4305797) B4305797
theorem B1912097 : Blo 1273955 1912097 := bstep (se 2 (by rfl) ⟨717036, by rfl⟩ : syracuseStep 1912097 = 1434073) B1434073
theorem B1723681 : Blo 1273955 1723681 := bstep (se 2 (by rfl) ⟨646380, by rfl⟩ : syracuseStep 1723681 = 1292761) B1292761
theorem B4304177 : Blo 1273955 4304177 := bstep (se 2 (by rfl) ⟨1614066, by rfl⟩ : syracuseStep 4304177 = 3228133) B3228133
theorem B1912115 : Blo 1273955 1912115 := bstep (se 1 (by rfl) ⟨1434086, by rfl⟩ : syracuseStep 1912115 = 2868173) B2868173
theorem B1912145 : Blo 1273955 1912145 := bstep (se 2 (by rfl) ⟨717054, by rfl⟩ : syracuseStep 1912145 = 1434109) B1434109
theorem B1912163 : Blo 1273955 1912163 := bstep (se 1 (by rfl) ⟨1434122, by rfl⟩ : syracuseStep 1912163 = 2868245) B2868245
theorem B14511473 : Blo 1273955 14511473 := bstep (se 2 (by rfl) ⟨5441802, by rfl⟩ : syracuseStep 14511473 = 10883605) B10883605
theorem B1912193 : Blo 1273955 1912193 := bstep (se 2 (by rfl) ⟨717072, by rfl⟩ : syracuseStep 1912193 = 1434145) B1434145
theorem B2420113 : Blo 1273955 2420113 := bstep (se 2 (by rfl) ⟨907542, by rfl⟩ : syracuseStep 2420113 = 1815085) B1815085
theorem B1912211 : Blo 1273955 1912211 := bstep (se 1 (by rfl) ⟨1434158, by rfl⟩ : syracuseStep 1912211 = 2868317) B2868317
theorem B1912241 : Blo 1273955 1912241 := bstep (se 2 (by rfl) ⟨717090, by rfl⟩ : syracuseStep 1912241 = 1434181) B1434181
theorem B1912259 : Blo 1273955 1912259 := bstep (se 1 (by rfl) ⟨1434194, by rfl⟩ : syracuseStep 1912259 = 2868389) B2868389
theorem B2149841 : Blo 1273955 2149841 := bstep (se 2 (by rfl) ⟨806190, by rfl⟩ : syracuseStep 2149841 = 1612381) B1612381
theorem B1912289 : Blo 1273955 1912289 := bstep (se 2 (by rfl) ⟨717108, by rfl⟩ : syracuseStep 1912289 = 1434217) B1434217
theorem B1912307 : Blo 1273955 1912307 := bstep (se 1 (by rfl) ⟨1434230, by rfl⟩ : syracuseStep 1912307 = 2868461) B2868461
theorem B2453009 : Blo 1273955 2453009 := bstep (se 2 (by rfl) ⟨919878, by rfl⟩ : syracuseStep 2453009 = 1839757) B1839757
theorem B1912337 : Blo 1273955 1912337 := bstep (se 2 (by rfl) ⟨717126, by rfl⟩ : syracuseStep 1912337 = 1434253) B1434253
theorem B2870801 : Blo 1273955 2870801 := bstep (se 2 (by rfl) ⟨1076550, by rfl⟩ : syracuseStep 2870801 = 2153101) B2153101
theorem B1912355 : Blo 1273955 1912355 := bstep (se 1 (by rfl) ⟨1434266, by rfl⟩ : syracuseStep 1912355 = 2868533) B2868533
theorem B2870819 : Blo 1273955 2870819 := bstep (se 1 (by rfl) ⟨2153114, by rfl⟩ : syracuseStep 2870819 = 4306229) B4306229
theorem B2420273 : Blo 1273955 2420273 := bstep (se 2 (by rfl) ⟨907602, by rfl⟩ : syracuseStep 2420273 = 1815205) B1815205
theorem B1912385 : Blo 1273955 1912385 := bstep (se 2 (by rfl) ⟨717144, by rfl⟩ : syracuseStep 1912385 = 1434289) B1434289
theorem B2149969 : Blo 1273955 2149969 := bstep (se 2 (by rfl) ⟨806238, by rfl⟩ : syracuseStep 2149969 = 1612477) B1612477
theorem B1912403 : Blo 1273955 1912403 := bstep (se 1 (by rfl) ⟨1434302, by rfl⟩ : syracuseStep 1912403 = 2868605) B2868605
theorem B1912433 : Blo 1273955 1912433 := bstep (se 2 (by rfl) ⟨717162, by rfl⟩ : syracuseStep 1912433 = 1434325) B1434325
theorem B2150003 : Blo 1273955 2150003 := bstep (se 1 (by rfl) ⟨1612502, by rfl⟩ : syracuseStep 2150003 = 3225005) B3225005
theorem B1912451 : Blo 1273955 1912451 := bstep (se 1 (by rfl) ⟨1434338, by rfl⟩ : syracuseStep 1912451 = 2868677) B2868677
theorem B1912481 : Blo 1273955 1912481 := bstep (se 2 (by rfl) ⟨717180, by rfl⟩ : syracuseStep 1912481 = 1434361) B1434361
theorem B3632813 : Blo 1273955 3632813 := bstep (se 3 (by rfl) ⟨681152, by rfl⟩ : syracuseStep 3632813 = 1362305) B1362305
theorem B1912499 : Blo 1273955 1912499 := bstep (se 1 (by rfl) ⟨1434374, by rfl⟩ : syracuseStep 1912499 = 2868749) B2868749
theorem B1912529 : Blo 1273955 1912529 := bstep (se 2 (by rfl) ⟨717198, by rfl⟩ : syracuseStep 1912529 = 1434397) B1434397
theorem B1912547 : Blo 1273955 1912547 := bstep (se 1 (by rfl) ⟨1434410, by rfl⟩ : syracuseStep 1912547 = 2868821) B2868821
theorem B2150131 : Blo 1273955 2150131 := bstep (se 1 (by rfl) ⟨1612598, by rfl⟩ : syracuseStep 2150131 = 3225197) B3225197
theorem B1912577 : Blo 1273955 1912577 := bstep (se 2 (by rfl) ⟨717216, by rfl⟩ : syracuseStep 1912577 = 1434433) B1434433
theorem B2043649 : Blo 1273955 2043649 := bstep (se 2 (by rfl) ⟨766368, by rfl⟩ : syracuseStep 2043649 = 1532737) B1532737
theorem B1912595 : Blo 1273955 1912595 := bstep (se 1 (by rfl) ⟨1434446, by rfl⟩ : syracuseStep 1912595 = 2868893) B2868893
theorem B1912625 : Blo 1273955 1912625 := bstep (se 2 (by rfl) ⟨717234, by rfl⟩ : syracuseStep 1912625 = 1434469) B1434469
theorem B1814339 : Blo 1273955 1814339 := bstep (se 1 (by rfl) ⟨1360754, by rfl⟩ : syracuseStep 1814339 = 2721509) B2721509
theorem B1912643 : Blo 1273955 1912643 := bstep (se 1 (by rfl) ⟨1434482, by rfl⟩ : syracuseStep 1912643 = 2868965) B2868965
theorem B4304717 : Blo 1273955 4304717 := bstep (se 3 (by rfl) ⟨807134, by rfl⟩ : syracuseStep 4304717 = 1614269) B1614269
theorem B1912673 : Blo 1273955 1912673 := bstep (se 2 (by rfl) ⟨717252, by rfl⟩ : syracuseStep 1912673 = 1434505) B1434505
theorem B24850289 : Blo 1273955 24850289 := bstep (se 2 (by rfl) ⟨9318858, by rfl⟩ : syracuseStep 24850289 = 18637717) B18637717
theorem B1912691 : Blo 1273955 1912691 := bstep (se 1 (by rfl) ⟨1434518, by rfl⟩ : syracuseStep 1912691 = 2869037) B2869037
theorem B2150273 : Blo 1273955 2150273 := bstep (se 2 (by rfl) ⟨806352, by rfl⟩ : syracuseStep 2150273 = 1612705) B1612705
theorem B4304771 : Blo 1273955 4304771 := bstep (se 1 (by rfl) ⟨3228578, by rfl⟩ : syracuseStep 4304771 = 6457157) B6457157
theorem B1912721 : Blo 1273955 1912721 := bstep (se 2 (by rfl) ⟨717270, by rfl⟩ : syracuseStep 1912721 = 1434541) B1434541
theorem B1912739 : Blo 1273955 1912739 := bstep (se 1 (by rfl) ⟨1434554, by rfl⟩ : syracuseStep 1912739 = 2869109) B2869109
theorem B1912769 : Blo 1273955 1912769 := bstep (se 2 (by rfl) ⟨717288, by rfl⟩ : syracuseStep 1912769 = 1434577) B1434577
theorem B2420675 : Blo 1273955 2420675 := bstep (se 1 (by rfl) ⟨1815506, by rfl⟩ : syracuseStep 2420675 = 3631013) B3631013
theorem B1912787 : Blo 1273955 1912787 := bstep (se 1 (by rfl) ⟨1434590, by rfl⟩ : syracuseStep 1912787 = 2869181) B2869181
theorem B2486243 : Blo 1273955 2486243 := bstep (se 1 (by rfl) ⟨1864682, by rfl⟩ : syracuseStep 2486243 = 3729365) B3729365
theorem B1912817 : Blo 1273955 1912817 := bstep (se 2 (by rfl) ⟨717306, by rfl⟩ : syracuseStep 1912817 = 1434613) B1434613
theorem B2150401 : Blo 1273955 2150401 := bstep (se 2 (by rfl) ⟨806400, by rfl⟩ : syracuseStep 2150401 = 1612801) B1612801
theorem B1912835 : Blo 1273955 1912835 := bstep (se 1 (by rfl) ⟨1434626, by rfl⟩ : syracuseStep 1912835 = 2869253) B2869253
theorem B1912865 : Blo 1273955 1912865 := bstep (se 2 (by rfl) ⟨717324, by rfl⟩ : syracuseStep 1912865 = 1434649) B1434649
theorem B2150435 : Blo 1273955 2150435 := bstep (se 1 (by rfl) ⟨1612826, by rfl⟩ : syracuseStep 2150435 = 3225653) B3225653
theorem B1912883 : Blo 1273955 1912883 := bstep (se 1 (by rfl) ⟨1434662, by rfl⟩ : syracuseStep 1912883 = 2869325) B2869325
theorem B1912913 : Blo 1273955 1912913 := bstep (se 2 (by rfl) ⟨717342, by rfl⟩ : syracuseStep 1912913 = 1434685) B1434685
theorem B1273955 : Blo 1273955 1273955 := bstep (se 1 (by rfl) ⟨955466, by rfl⟩ : syracuseStep 1273955 = 1910933) B1910933
theorem B1912931 : Blo 1273955 1912931 := bstep (se 1 (by rfl) ⟨1434698, by rfl⟩ : syracuseStep 1912931 = 2869397) B2869397
theorem B1273971 : Blo 1273955 1273971 := bstep (se 1 (by rfl) ⟨955478, by rfl⟩ : syracuseStep 1273971 = 1910957) B1910957
theorem B1912961 : Blo 1273955 1912961 := bstep (se 2 (by rfl) ⟨717360, by rfl⟩ : syracuseStep 1912961 = 1434721) B1434721
theorem B1273987 : Blo 1273955 1273987 := bstep (se 1 (by rfl) ⟨955490, by rfl⟩ : syracuseStep 1273987 = 1910981) B1910981
theorem B4305041 : Blo 1273955 4305041 := bstep (se 2 (by rfl) ⟨1614390, by rfl⟩ : syracuseStep 4305041 = 3228781) B3228781
theorem B1274003 : Blo 1273955 1274003 := bstep (se 1 (by rfl) ⟨955502, by rfl⟩ : syracuseStep 1274003 = 1911005) B1911005
theorem B1912979 : Blo 1273955 1912979 := bstep (se 1 (by rfl) ⟨1434734, by rfl⟩ : syracuseStep 1912979 = 2869469) B2869469
theorem B1274019 : Blo 1273955 1274019 := bstep (se 1 (by rfl) ⟨955514, by rfl⟩ : syracuseStep 1274019 = 1911029) B1911029
theorem B2150563 : Blo 1273955 2150563 := bstep (se 1 (by rfl) ⟨1612922, by rfl⟩ : syracuseStep 2150563 = 3225845) B3225845
theorem B3879085 : Blo 1273955 3879085 := bstep (se 3 (by rfl) ⟨727328, by rfl⟩ : syracuseStep 3879085 = 1454657) B1454657
theorem B4837553 : Blo 1273955 4837553 := bstep (se 2 (by rfl) ⟨1814082, by rfl⟩ : syracuseStep 4837553 = 3628165) B3628165
theorem B1913009 : Blo 1273955 1913009 := bstep (se 2 (by rfl) ⟨717378, by rfl⟩ : syracuseStep 1913009 = 1434757) B1434757
theorem B1274035 : Blo 1273955 1274035 := bstep (se 1 (by rfl) ⟨955526, by rfl⟩ : syracuseStep 1274035 = 1911053) B1911053
theorem B1274051 : Blo 1273955 1274051 := bstep (se 1 (by rfl) ⟨955538, by rfl⟩ : syracuseStep 1274051 = 1911077) B1911077
theorem B1913027 : Blo 1273955 1913027 := bstep (se 1 (by rfl) ⟨1434770, by rfl⟩ : syracuseStep 1913027 = 2869541) B2869541
theorem B1274067 : Blo 1273955 1274067 := bstep (se 1 (by rfl) ⟨955550, by rfl⟩ : syracuseStep 1274067 = 1911101) B1911101
theorem B1913057 : Blo 1273955 1913057 := bstep (se 2 (by rfl) ⟨717396, by rfl⟩ : syracuseStep 1913057 = 1434793) B1434793
theorem B1274083 : Blo 1273955 1274083 := bstep (se 1 (by rfl) ⟨955562, by rfl⟩ : syracuseStep 1274083 = 1911125) B1911125
theorem B4419821 : Blo 1273955 4419821 := bstep (se 3 (by rfl) ⟨828716, by rfl⟩ : syracuseStep 4419821 = 1657433) B1657433
theorem B6123761 : Blo 1273955 6123761 := bstep (se 2 (by rfl) ⟨2296410, by rfl⟩ : syracuseStep 6123761 = 4592821) B4592821
theorem B4141297 : Blo 1273955 4141297 := bstep (se 2 (by rfl) ⟨1552986, by rfl⟩ : syracuseStep 4141297 = 3105973) B3105973
theorem B1274099 : Blo 1273955 1274099 := bstep (se 1 (by rfl) ⟨955574, by rfl⟩ : syracuseStep 1274099 = 1911149) B1911149
theorem B1913075 : Blo 1273955 1913075 := bstep (se 1 (by rfl) ⟨1434806, by rfl⟩ : syracuseStep 1913075 = 2869613) B2869613
theorem B1274115 : Blo 1273955 1274115 := bstep (se 1 (by rfl) ⟨955586, by rfl⟩ : syracuseStep 1274115 = 1911173) B1911173
theorem B1913105 : Blo 1273955 1913105 := bstep (se 2 (by rfl) ⟨717414, by rfl⟩ : syracuseStep 1913105 = 1434829) B1434829
theorem B1274131 : Blo 1273955 1274131 := bstep (se 1 (by rfl) ⟨955598, by rfl⟩ : syracuseStep 1274131 = 1911197) B1911197
theorem B1274147 : Blo 1273955 1274147 := bstep (se 1 (by rfl) ⟨955610, by rfl⟩ : syracuseStep 1274147 = 1911221) B1911221
theorem B1913123 : Blo 1273955 1913123 := bstep (se 1 (by rfl) ⟨1434842, by rfl⟩ : syracuseStep 1913123 = 2869685) B2869685
theorem B2724131 : Blo 1273955 2724131 := bstep (se 1 (by rfl) ⟨2043098, by rfl⟩ : syracuseStep 2724131 = 4086197) B4086197
theorem B2150705 : Blo 1273955 2150705 := bstep (se 2 (by rfl) ⟨806514, by rfl⟩ : syracuseStep 2150705 = 1613029) B1613029
theorem B1274163 : Blo 1273955 1274163 := bstep (se 1 (by rfl) ⟨955622, by rfl⟩ : syracuseStep 1274163 = 1911245) B1911245
theorem B1913153 : Blo 1273955 1913153 := bstep (se 2 (by rfl) ⟨717432, by rfl⟩ : syracuseStep 1913153 = 1434865) B1434865
theorem B1274179 : Blo 1273955 1274179 := bstep (se 1 (by rfl) ⟨955634, by rfl⟩ : syracuseStep 1274179 = 1911269) B1911269
theorem B1274195 : Blo 1273955 1274195 := bstep (se 1 (by rfl) ⟨955646, by rfl⟩ : syracuseStep 1274195 = 1911293) B1911293
theorem B1913171 : Blo 1273955 1913171 := bstep (se 1 (by rfl) ⟨1434878, by rfl⟩ : syracuseStep 1913171 = 2869757) B2869757
theorem B1274211 : Blo 1273955 1274211 := bstep (se 1 (by rfl) ⟨955658, by rfl⟩ : syracuseStep 1274211 = 1911317) B1911317
theorem B1913201 : Blo 1273955 1913201 := bstep (se 2 (by rfl) ⟨717450, by rfl⟩ : syracuseStep 1913201 = 1434901) B1434901
theorem B1274227 : Blo 1273955 1274227 := bstep (se 1 (by rfl) ⟨955670, by rfl⟩ : syracuseStep 1274227 = 1911341) B1911341
theorem B1274243 : Blo 1273955 1274243 := bstep (se 1 (by rfl) ⟨955682, by rfl⟩ : syracuseStep 1274243 = 1911365) B1911365
theorem B1913219 : Blo 1273955 1913219 := bstep (se 1 (by rfl) ⟨1434914, by rfl⟩ : syracuseStep 1913219 = 2869829) B2869829
theorem B9687437 : Blo 1273955 9687437 := bstep (se 3 (by rfl) ⟨1816394, by rfl⟩ : syracuseStep 9687437 = 3632789) B3632789
theorem B1274259 : Blo 1273955 1274259 := bstep (se 1 (by rfl) ⟨955694, by rfl⟩ : syracuseStep 1274259 = 1911389) B1911389
theorem B1913249 : Blo 1273955 1913249 := bstep (se 2 (by rfl) ⟨717468, by rfl⟩ : syracuseStep 1913249 = 1434937) B1434937
theorem B1274275 : Blo 1273955 1274275 := bstep (se 1 (by rfl) ⟨955706, by rfl⟩ : syracuseStep 1274275 = 1911413) B1911413
theorem B1937827 : Blo 1273955 1937827 := bstep (se 1 (by rfl) ⟨1453370, by rfl⟩ : syracuseStep 1937827 = 2906741) B2906741
theorem B4362659 : Blo 1273955 4362659 := bstep (se 1 (by rfl) ⟨3271994, by rfl⟩ : syracuseStep 4362659 = 6543989) B6543989
theorem B2150833 : Blo 1273955 2150833 := bstep (se 2 (by rfl) ⟨806562, by rfl⟩ : syracuseStep 2150833 = 1613125) B1613125
theorem B1274291 : Blo 1273955 1274291 := bstep (se 1 (by rfl) ⟨955718, by rfl⟩ : syracuseStep 1274291 = 1911437) B1911437
theorem B1913267 : Blo 1273955 1913267 := bstep (se 1 (by rfl) ⟨1434950, by rfl⟩ : syracuseStep 1913267 = 2869901) B2869901
theorem B1814977 : Blo 1273955 1814977 := bstep (se 2 (by rfl) ⟨680616, by rfl⟩ : syracuseStep 1814977 = 1361233) B1361233
theorem B1274307 : Blo 1273955 1274307 := bstep (se 1 (by rfl) ⟨955730, by rfl⟩ : syracuseStep 1274307 = 1911461) B1911461
theorem B1913297 : Blo 1273955 1913297 := bstep (se 2 (by rfl) ⟨717486, by rfl⟩ : syracuseStep 1913297 = 1434973) B1434973
theorem B1274323 : Blo 1273955 1274323 := bstep (se 1 (by rfl) ⟨955742, by rfl⟩ : syracuseStep 1274323 = 1911485) B1911485
theorem B2150867 : Blo 1273955 2150867 := bstep (se 1 (by rfl) ⟨1613150, by rfl⟩ : syracuseStep 2150867 = 3226301) B3226301
theorem B1274339 : Blo 1273955 1274339 := bstep (se 1 (by rfl) ⟨955754, by rfl⟩ : syracuseStep 1274339 = 1911509) B1911509
theorem B1913315 : Blo 1273955 1913315 := bstep (se 1 (by rfl) ⟨1434986, by rfl⟩ : syracuseStep 1913315 = 2869973) B2869973
theorem B1274355 : Blo 1273955 1274355 := bstep (se 1 (by rfl) ⟨955766, by rfl⟩ : syracuseStep 1274355 = 1911533) B1911533
theorem B1913345 : Blo 1273955 1913345 := bstep (se 2 (by rfl) ⟨717504, by rfl⟩ : syracuseStep 1913345 = 1435009) B1435009
theorem B1274371 : Blo 1273955 1274371 := bstep (se 1 (by rfl) ⟨955778, by rfl⟩ : syracuseStep 1274371 = 1911557) B1911557
theorem B15503885 : Blo 1273955 15503885 := bstep (se 3 (by rfl) ⟨2906978, by rfl⟩ : syracuseStep 15503885 = 5813957) B5813957
theorem B2298385 : Blo 1273955 2298385 := bstep (se 2 (by rfl) ⟨861894, by rfl⟩ : syracuseStep 2298385 = 1723789) B1723789
theorem B1274387 : Blo 1273955 1274387 := bstep (se 1 (by rfl) ⟨955790, by rfl⟩ : syracuseStep 1274387 = 1911581) B1911581
theorem B1913363 : Blo 1273955 1913363 := bstep (se 1 (by rfl) ⟨1435022, by rfl⟩ : syracuseStep 1913363 = 2870045) B2870045
theorem B1274403 : Blo 1273955 1274403 := bstep (se 1 (by rfl) ⟨955802, by rfl⟩ : syracuseStep 1274403 = 1911605) B1911605
theorem B1913393 : Blo 1273955 1913393 := bstep (se 2 (by rfl) ⟨717522, by rfl⟩ : syracuseStep 1913393 = 1435045) B1435045
theorem B1274419 : Blo 1273955 1274419 := bstep (se 1 (by rfl) ⟨955814, by rfl⟩ : syracuseStep 1274419 = 1911629) B1911629
theorem B1274435 : Blo 1273955 1274435 := bstep (se 1 (by rfl) ⟨955826, by rfl⟩ : syracuseStep 1274435 = 1911653) B1911653
theorem B1913411 : Blo 1273955 1913411 := bstep (se 1 (by rfl) ⟨1435058, by rfl⟩ : syracuseStep 1913411 = 2870117) B2870117
theorem B1274451 : Blo 1273955 1274451 := bstep (se 1 (by rfl) ⟨955838, by rfl⟩ : syracuseStep 1274451 = 1911677) B1911677
theorem B2150995 : Blo 1273955 2150995 := bstep (se 1 (by rfl) ⟨1613246, by rfl⟩ : syracuseStep 2150995 = 3226493) B3226493
theorem B1913441 : Blo 1273955 1913441 := bstep (se 2 (by rfl) ⟨717540, by rfl⟩ : syracuseStep 1913441 = 1435081) B1435081
theorem B6451811 : Blo 1273955 6451811 := bstep (se 1 (by rfl) ⟨4838858, by rfl⟩ : syracuseStep 6451811 = 9677717) B9677717
theorem B1274467 : Blo 1273955 1274467 := bstep (se 1 (by rfl) ⟨955850, by rfl⟩ : syracuseStep 1274467 = 1911701) B1911701
theorem B1274483 : Blo 1273955 1274483 := bstep (se 1 (by rfl) ⟨955862, by rfl⟩ : syracuseStep 1274483 = 1911725) B1911725
theorem B1913459 : Blo 1273955 1913459 := bstep (se 1 (by rfl) ⟨1435094, by rfl⟩ : syracuseStep 1913459 = 2870189) B2870189
theorem B1274499 : Blo 1273955 1274499 := bstep (se 1 (by rfl) ⟨955874, by rfl⟩ : syracuseStep 1274499 = 1911749) B1911749
theorem B1913489 : Blo 1273955 1913489 := bstep (se 2 (by rfl) ⟨717558, by rfl⟩ : syracuseStep 1913489 = 1435117) B1435117
theorem B1274515 : Blo 1273955 1274515 := bstep (se 1 (by rfl) ⟨955886, by rfl⟩ : syracuseStep 1274515 = 1911773) B1911773
theorem B1274531 : Blo 1273955 1274531 := bstep (se 1 (by rfl) ⟨955898, by rfl⟩ : syracuseStep 1274531 = 1911797) B1911797
theorem B1913507 : Blo 1273955 1913507 := bstep (se 1 (by rfl) ⟨1435130, by rfl⟩ : syracuseStep 1913507 = 2870261) B2870261
theorem B4305581 : Blo 1273955 4305581 := bstep (se 3 (by rfl) ⟨807296, by rfl⟩ : syracuseStep 4305581 = 1614593) B1614593
theorem B1274547 : Blo 1273955 1274547 := bstep (se 1 (by rfl) ⟨955910, by rfl⟩ : syracuseStep 1274547 = 1911821) B1911821
theorem B1913537 : Blo 1273955 1913537 := bstep (se 2 (by rfl) ⟨717576, by rfl⟩ : syracuseStep 1913537 = 1435153) B1435153
theorem B1274563 : Blo 1273955 1274563 := bstep (se 1 (by rfl) ⟨955922, by rfl⟩ : syracuseStep 1274563 = 1911845) B1911845
theorem B1274579 : Blo 1273955 1274579 := bstep (se 1 (by rfl) ⟨955934, by rfl⟩ : syracuseStep 1274579 = 1911869) B1911869
theorem B1913555 : Blo 1273955 1913555 := bstep (se 1 (by rfl) ⟨1435166, by rfl⟩ : syracuseStep 1913555 = 2870333) B2870333
theorem B2151137 : Blo 1273955 2151137 := bstep (se 2 (by rfl) ⟨806676, by rfl⟩ : syracuseStep 2151137 = 1613353) B1613353
theorem B1274595 : Blo 1273955 1274595 := bstep (se 1 (by rfl) ⟨955946, by rfl⟩ : syracuseStep 1274595 = 1911893) B1911893
theorem B4305635 : Blo 1273955 4305635 := bstep (se 1 (by rfl) ⟨3229226, by rfl⟩ : syracuseStep 4305635 = 6458453) B6458453
theorem B1913585 : Blo 1273955 1913585 := bstep (se 2 (by rfl) ⟨717594, by rfl⟩ : syracuseStep 1913585 = 1435189) B1435189
theorem B1274611 : Blo 1273955 1274611 := bstep (se 1 (by rfl) ⟨955958, by rfl⟩ : syracuseStep 1274611 = 1911917) B1911917
theorem B1274627 : Blo 1273955 1274627 := bstep (se 1 (by rfl) ⟨955970, by rfl⟩ : syracuseStep 1274627 = 1911941) B1911941
theorem B1913603 : Blo 1273955 1913603 := bstep (se 1 (by rfl) ⟨1435202, by rfl⟩ : syracuseStep 1913603 = 2870405) B2870405
theorem B1815313 : Blo 1273955 1815313 := bstep (se 2 (by rfl) ⟨680742, by rfl⟩ : syracuseStep 1815313 = 1361485) B1361485
theorem B1274643 : Blo 1273955 1274643 := bstep (se 1 (by rfl) ⟨955982, by rfl⟩ : syracuseStep 1274643 = 1911965) B1911965
theorem B1913633 : Blo 1273955 1913633 := bstep (se 2 (by rfl) ⟨717612, by rfl⟩ : syracuseStep 1913633 = 1435225) B1435225
theorem B1274659 : Blo 1273955 1274659 := bstep (se 1 (by rfl) ⟨955994, by rfl⟩ : syracuseStep 1274659 = 1911989) B1911989
theorem B1274675 : Blo 1273955 1274675 := bstep (se 1 (by rfl) ⟨956006, by rfl⟩ : syracuseStep 1274675 = 1912013) B1912013
theorem B1913651 : Blo 1273955 1913651 := bstep (se 1 (by rfl) ⟨1435238, by rfl⟩ : syracuseStep 1913651 = 2870477) B2870477
theorem B1274691 : Blo 1273955 1274691 := bstep (se 1 (by rfl) ⟨956018, by rfl⟩ : syracuseStep 1274691 = 1912037) B1912037
theorem B2421571 : Blo 1273955 2421571 := bstep (se 1 (by rfl) ⟨1816178, by rfl⟩ : syracuseStep 2421571 = 3632357) B3632357
theorem B1913681 : Blo 1273955 1913681 := bstep (se 2 (by rfl) ⟨717630, by rfl⟩ : syracuseStep 1913681 = 1435261) B1435261
theorem B1274707 : Blo 1273955 1274707 := bstep (se 1 (by rfl) ⟨956030, by rfl⟩ : syracuseStep 1274707 = 1912061) B1912061
theorem B2151265 : Blo 1273955 2151265 := bstep (se 2 (by rfl) ⟨806724, by rfl⟩ : syracuseStep 2151265 = 1613449) B1613449
theorem B1274723 : Blo 1273955 1274723 := bstep (se 1 (by rfl) ⟨956042, by rfl⟩ : syracuseStep 1274723 = 1912085) B1912085
theorem B1913699 : Blo 1273955 1913699 := bstep (se 1 (by rfl) ⟨1435274, by rfl⟩ : syracuseStep 1913699 = 2870549) B2870549
theorem B1274739 : Blo 1273955 1274739 := bstep (se 1 (by rfl) ⟨956054, by rfl⟩ : syracuseStep 1274739 = 1912109) B1912109
theorem B1913729 : Blo 1273955 1913729 := bstep (se 2 (by rfl) ⟨717648, by rfl⟩ : syracuseStep 1913729 = 1435297) B1435297
theorem B1274755 : Blo 1273955 1274755 := bstep (se 1 (by rfl) ⟨956066, by rfl⟩ : syracuseStep 1274755 = 1912133) B1912133
theorem B2151299 : Blo 1273955 2151299 := bstep (se 1 (by rfl) ⟨1613474, by rfl⟩ : syracuseStep 2151299 = 3226949) B3226949
theorem B1274771 : Blo 1273955 1274771 := bstep (se 1 (by rfl) ⟨956078, by rfl⟩ : syracuseStep 1274771 = 1912157) B1912157
theorem B1913747 : Blo 1273955 1913747 := bstep (se 1 (by rfl) ⟨1435310, by rfl⟩ : syracuseStep 1913747 = 2870621) B2870621
theorem B1274787 : Blo 1273955 1274787 := bstep (se 1 (by rfl) ⟨956090, by rfl⟩ : syracuseStep 1274787 = 1912181) B1912181
theorem B1913777 : Blo 1273955 1913777 := bstep (se 2 (by rfl) ⟨717666, by rfl⟩ : syracuseStep 1913777 = 1435333) B1435333
theorem B1274803 : Blo 1273955 1274803 := bstep (se 1 (by rfl) ⟨956102, by rfl⟩ : syracuseStep 1274803 = 1912205) B1912205
theorem B1274819 : Blo 1273955 1274819 := bstep (se 1 (by rfl) ⟨956114, by rfl⟩ : syracuseStep 1274819 = 1912229) B1912229
theorem B1913795 : Blo 1273955 1913795 := bstep (se 1 (by rfl) ⟨1435346, by rfl⟩ : syracuseStep 1913795 = 2870693) B2870693
theorem B1274835 : Blo 1273955 1274835 := bstep (se 1 (by rfl) ⟨956126, by rfl⟩ : syracuseStep 1274835 = 1912253) B1912253
theorem B1913825 : Blo 1273955 1913825 := bstep (se 2 (by rfl) ⟨717684, by rfl⟩ : syracuseStep 1913825 = 1435369) B1435369
theorem B1274851 : Blo 1273955 1274851 := bstep (se 1 (by rfl) ⟨956138, by rfl⟩ : syracuseStep 1274851 = 1912277) B1912277
theorem B2421731 : Blo 1273955 2421731 := bstep (se 1 (by rfl) ⟨1816298, by rfl⟩ : syracuseStep 2421731 = 3632597) B3632597
theorem B4305905 : Blo 1273955 4305905 := bstep (se 2 (by rfl) ⟨1614714, by rfl⟩ : syracuseStep 4305905 = 3229429) B3229429
theorem B1274867 : Blo 1273955 1274867 := bstep (se 1 (by rfl) ⟨956150, by rfl⟩ : syracuseStep 1274867 = 1912301) B1912301
theorem B1913843 : Blo 1273955 1913843 := bstep (se 1 (by rfl) ⟨1435382, by rfl⟩ : syracuseStep 1913843 = 2870765) B2870765
theorem B1274883 : Blo 1273955 1274883 := bstep (se 1 (by rfl) ⟨956162, by rfl⟩ : syracuseStep 1274883 = 1912325) B1912325
theorem B2151427 : Blo 1273955 2151427 := bstep (se 1 (by rfl) ⟨1613570, by rfl⟩ : syracuseStep 2151427 = 3227141) B3227141
theorem B1913873 : Blo 1273955 1913873 := bstep (se 2 (by rfl) ⟨717702, by rfl⟩ : syracuseStep 1913873 = 1435405) B1435405
theorem B1274899 : Blo 1273955 1274899 := bstep (se 1 (by rfl) ⟨956174, by rfl⟩ : syracuseStep 1274899 = 1912349) B1912349
theorem B4592675 : Blo 1273955 4592675 := bstep (se 1 (by rfl) ⟨3444506, by rfl⟩ : syracuseStep 4592675 = 6889013) B6889013
theorem B1274915 : Blo 1273955 1274915 := bstep (se 1 (by rfl) ⟨956186, by rfl⟩ : syracuseStep 1274915 = 1912373) B1912373
theorem B1913891 : Blo 1273955 1913891 := bstep (se 1 (by rfl) ⟨1435418, by rfl⟩ : syracuseStep 1913891 = 2870837) B2870837
theorem B1274931 : Blo 1273955 1274931 := bstep (se 1 (by rfl) ⟨956198, by rfl⟩ : syracuseStep 1274931 = 1912397) B1912397
theorem B1913921 : Blo 1273955 1913921 := bstep (se 2 (by rfl) ⟨717720, by rfl⟩ : syracuseStep 1913921 = 1435441) B1435441
theorem B1274947 : Blo 1273955 1274947 := bstep (se 1 (by rfl) ⟨956210, by rfl⟩ : syracuseStep 1274947 = 1912421) B1912421
theorem B2298947 : Blo 1273955 2298947 := bstep (se 1 (by rfl) ⟨1724210, by rfl⟩ : syracuseStep 2298947 = 3448421) B3448421
theorem B1274963 : Blo 1273955 1274963 := bstep (se 1 (by rfl) ⟨956222, by rfl⟩ : syracuseStep 1274963 = 1912445) B1912445
theorem B6124643 : Blo 1273955 6124643 := bstep (se 1 (by rfl) ⟨4593482, by rfl⟩ : syracuseStep 6124643 = 9186965) B9186965
theorem B1274979 : Blo 1273955 1274979 := bstep (se 1 (by rfl) ⟨956234, by rfl⟩ : syracuseStep 1274979 = 1912469) B1912469
theorem B1274995 : Blo 1273955 1274995 := bstep (se 1 (by rfl) ⟨956246, by rfl⟩ : syracuseStep 1274995 = 1912493) B1912493
theorem B2946179 : Blo 1273955 2946179 := bstep (se 1 (by rfl) ⟨2209634, by rfl⟩ : syracuseStep 2946179 = 4419269) B4419269
theorem B1275011 : Blo 1273955 1275011 := bstep (se 1 (by rfl) ⟨956258, by rfl⟩ : syracuseStep 1275011 = 1912517) B1912517
theorem B2724995 : Blo 1273955 2724995 := bstep (se 1 (by rfl) ⟨2043746, by rfl⟩ : syracuseStep 2724995 = 4087493) B4087493
theorem B2151569 : Blo 1273955 2151569 := bstep (se 2 (by rfl) ⟨806838, by rfl⟩ : syracuseStep 2151569 = 1613677) B1613677
theorem B1275027 : Blo 1273955 1275027 := bstep (se 1 (by rfl) ⟨956270, by rfl⟩ : syracuseStep 1275027 = 1912541) B1912541
theorem B1275043 : Blo 1273955 1275043 := bstep (se 1 (by rfl) ⟨956282, by rfl⟩ : syracuseStep 1275043 = 1912565) B1912565
theorem B1275059 : Blo 1273955 1275059 := bstep (se 1 (by rfl) ⟨956294, by rfl⟩ : syracuseStep 1275059 = 1912589) B1912589
theorem B1275075 : Blo 1273955 1275075 := bstep (se 1 (by rfl) ⟨956306, by rfl⟩ : syracuseStep 1275075 = 1912613) B1912613
theorem B1275091 : Blo 1273955 1275091 := bstep (se 1 (by rfl) ⟨956318, by rfl⟩ : syracuseStep 1275091 = 1912637) B1912637
theorem B9188579 : Blo 1273955 9188579 := bstep (se 1 (by rfl) ⟨6891434, by rfl⟩ : syracuseStep 9188579 = 13782869) B13782869
theorem B1275107 : Blo 1273955 1275107 := bstep (se 1 (by rfl) ⟨956330, by rfl⟩ : syracuseStep 1275107 = 1912661) B1912661
theorem B2725105 : Blo 1273955 2725105 := bstep (se 2 (by rfl) ⟨1021914, by rfl⟩ : syracuseStep 2725105 = 2043829) B2043829
theorem B1275123 : Blo 1273955 1275123 := bstep (se 1 (by rfl) ⟨956342, by rfl⟩ : syracuseStep 1275123 = 1912685) B1912685
theorem B1275139 : Blo 1273955 1275139 := bstep (se 1 (by rfl) ⟨956354, by rfl⟩ : syracuseStep 1275139 = 1912709) B1912709
theorem B2151697 : Blo 1273955 2151697 := bstep (se 2 (by rfl) ⟨806886, by rfl⟩ : syracuseStep 2151697 = 1613773) B1613773
theorem B1275155 : Blo 1273955 1275155 := bstep (se 1 (by rfl) ⟨956366, by rfl⟩ : syracuseStep 1275155 = 1912733) B1912733
theorem B1275171 : Blo 1273955 1275171 := bstep (se 1 (by rfl) ⟨956378, by rfl⟩ : syracuseStep 1275171 = 1912757) B1912757
theorem B2151731 : Blo 1273955 2151731 := bstep (se 1 (by rfl) ⟨1613798, by rfl⟩ : syracuseStep 2151731 = 3227597) B3227597
theorem B1275187 : Blo 1273955 1275187 := bstep (se 1 (by rfl) ⟨956390, by rfl⟩ : syracuseStep 1275187 = 1912781) B1912781
theorem B1275203 : Blo 1273955 1275203 := bstep (se 1 (by rfl) ⟨956402, by rfl⟩ : syracuseStep 1275203 = 1912805) B1912805
theorem B1275219 : Blo 1273955 1275219 := bstep (se 1 (by rfl) ⟨956414, by rfl⟩ : syracuseStep 1275219 = 1912829) B1912829
theorem B1815905 : Blo 1273955 1815905 := bstep (se 2 (by rfl) ⟨680964, by rfl⟩ : syracuseStep 1815905 = 1361929) B1361929
theorem B1275235 : Blo 1273955 1275235 := bstep (se 1 (by rfl) ⟨956426, by rfl⟩ : syracuseStep 1275235 = 1912853) B1912853
theorem B1275251 : Blo 1273955 1275251 := bstep (se 1 (by rfl) ⟨956438, by rfl⟩ : syracuseStep 1275251 = 1912877) B1912877
theorem B1275267 : Blo 1273955 1275267 := bstep (se 1 (by rfl) ⟨956450, by rfl⟩ : syracuseStep 1275267 = 1912901) B1912901
theorem B6452621 : Blo 1273955 6452621 := bstep (se 3 (by rfl) ⟨1209866, by rfl⟩ : syracuseStep 6452621 = 2419733) B2419733
theorem B1275283 : Blo 1273955 1275283 := bstep (se 1 (by rfl) ⟨956462, by rfl⟩ : syracuseStep 1275283 = 1912925) B1912925
theorem B1275299 : Blo 1273955 1275299 := bstep (se 1 (by rfl) ⟨956474, by rfl⟩ : syracuseStep 1275299 = 1912949) B1912949
theorem B3061169 : Blo 1273955 3061169 := bstep (se 2 (by rfl) ⟨1147938, by rfl⟩ : syracuseStep 3061169 = 2295877) B2295877
theorem B7263665 : Blo 1273955 7263665 := bstep (se 2 (by rfl) ⟨2723874, by rfl⟩ : syracuseStep 7263665 = 5447749) B5447749
theorem B2151859 : Blo 1273955 2151859 := bstep (se 1 (by rfl) ⟨1613894, by rfl⟩ : syracuseStep 2151859 = 3227789) B3227789
theorem B1275315 : Blo 1273955 1275315 := bstep (se 1 (by rfl) ⟨956486, by rfl⟩ : syracuseStep 1275315 = 1912973) B1912973
theorem B1275331 : Blo 1273955 1275331 := bstep (se 1 (by rfl) ⟨956498, by rfl⟩ : syracuseStep 1275331 = 1912997) B1912997
theorem B1275347 : Blo 1273955 1275347 := bstep (se 1 (by rfl) ⟨956510, by rfl⟩ : syracuseStep 1275347 = 1913021) B1913021
theorem B1275363 : Blo 1273955 1275363 := bstep (se 1 (by rfl) ⟨956522, by rfl⟩ : syracuseStep 1275363 = 1913045) B1913045
theorem B1275379 : Blo 1273955 1275379 := bstep (se 1 (by rfl) ⟨956534, by rfl⟩ : syracuseStep 1275379 = 1913069) B1913069
theorem B1275395 : Blo 1273955 1275395 := bstep (se 1 (by rfl) ⟨956546, by rfl⟩ : syracuseStep 1275395 = 1913093) B1913093
theorem B8173061 : Blo 1273955 8173061 := bstep (se 4 (by rfl) ⟨766224, by rfl⟩ : syracuseStep 8173061 = 1532449) B1532449
theorem B1275411 : Blo 1273955 1275411 := bstep (se 1 (by rfl) ⟨956558, by rfl⟩ : syracuseStep 1275411 = 1913117) B1913117
theorem B1275427 : Blo 1273955 1275427 := bstep (se 1 (by rfl) ⟨956570, by rfl⟩ : syracuseStep 1275427 = 1913141) B1913141
theorem B7255601 : Blo 1273955 7255601 := bstep (se 2 (by rfl) ⟨2720850, by rfl⟩ : syracuseStep 7255601 = 5441701) B5441701
theorem B1275443 : Blo 1273955 1275443 := bstep (se 1 (by rfl) ⟨956582, by rfl⟩ : syracuseStep 1275443 = 1913165) B1913165
theorem B2152001 : Blo 1273955 2152001 := bstep (se 2 (by rfl) ⟨807000, by rfl⟩ : syracuseStep 2152001 = 1614001) B1614001
theorem B1275459 : Blo 1273955 1275459 := bstep (se 1 (by rfl) ⟨956594, by rfl⟩ : syracuseStep 1275459 = 1913189) B1913189
theorem B1275475 : Blo 1273955 1275475 := bstep (se 1 (by rfl) ⟨956606, by rfl⟩ : syracuseStep 1275475 = 1913213) B1913213
theorem B4839011 : Blo 1273955 4839011 := bstep (se 1 (by rfl) ⟨3629258, by rfl⟩ : syracuseStep 4839011 = 7258517) B7258517
theorem B1275491 : Blo 1273955 1275491 := bstep (se 1 (by rfl) ⟨956618, by rfl⟩ : syracuseStep 1275491 = 1913237) B1913237
theorem B1275507 : Blo 1273955 1275507 := bstep (se 1 (by rfl) ⟨956630, by rfl⟩ : syracuseStep 1275507 = 1913261) B1913261
theorem B4421251 : Blo 1273955 4421251 := bstep (se 1 (by rfl) ⟨3315938, by rfl⟩ : syracuseStep 4421251 = 6631877) B6631877
theorem B1275523 : Blo 1273955 1275523 := bstep (se 1 (by rfl) ⟨956642, by rfl⟩ : syracuseStep 1275523 = 1913285) B1913285
theorem B1275539 : Blo 1273955 1275539 := bstep (se 1 (by rfl) ⟨956654, by rfl⟩ : syracuseStep 1275539 = 1913309) B1913309
theorem B1275555 : Blo 1273955 1275555 := bstep (se 1 (by rfl) ⟨956666, by rfl⟩ : syracuseStep 1275555 = 1913333) B1913333
theorem B1275571 : Blo 1273955 1275571 := bstep (se 1 (by rfl) ⟨956678, by rfl⟩ : syracuseStep 1275571 = 1913357) B1913357
theorem B2152129 : Blo 1273955 2152129 := bstep (se 2 (by rfl) ⟨807048, by rfl⟩ : syracuseStep 2152129 = 1614097) B1614097
theorem B1275587 : Blo 1273955 1275587 := bstep (se 1 (by rfl) ⟨956690, by rfl⟩ : syracuseStep 1275587 = 1913381) B1913381
theorem B4085453 : Blo 1273955 4085453 := bstep (se 3 (by rfl) ⟨766022, by rfl⟩ : syracuseStep 4085453 = 1532045) B1532045
theorem B1275603 : Blo 1273955 1275603 := bstep (se 1 (by rfl) ⟨956702, by rfl⟩ : syracuseStep 1275603 = 1913405) B1913405
theorem B18618083 : Blo 1273955 18618083 := bstep (se 1 (by rfl) ⟨13963562, by rfl⟩ : syracuseStep 18618083 = 27927125) B27927125
theorem B2152163 : Blo 1273955 2152163 := bstep (se 1 (by rfl) ⟨1614122, by rfl⟩ : syracuseStep 2152163 = 3228245) B3228245
theorem B1275619 : Blo 1273955 1275619 := bstep (se 1 (by rfl) ⟨956714, by rfl⟩ : syracuseStep 1275619 = 1913429) B1913429
theorem B3225329 : Blo 1273955 3225329 := bstep (se 2 (by rfl) ⟨1209498, by rfl⟩ : syracuseStep 3225329 = 2418997) B2418997
theorem B1275635 : Blo 1273955 1275635 := bstep (se 1 (by rfl) ⟨956726, by rfl⟩ : syracuseStep 1275635 = 1913453) B1913453
theorem B1275651 : Blo 1273955 1275651 := bstep (se 1 (by rfl) ⟨956738, by rfl⟩ : syracuseStep 1275651 = 1913477) B1913477
theorem B12252941 : Blo 1273955 12252941 := bstep (se 3 (by rfl) ⟨2297426, by rfl⟩ : syracuseStep 12252941 = 4594853) B4594853
theorem B1275667 : Blo 1273955 1275667 := bstep (se 1 (by rfl) ⟨956750, by rfl⟩ : syracuseStep 1275667 = 1913501) B1913501
theorem B3225379 : Blo 1273955 3225379 := bstep (se 1 (by rfl) ⟨2419034, by rfl⟩ : syracuseStep 3225379 = 4838069) B4838069
theorem B1275683 : Blo 1273955 1275683 := bstep (se 1 (by rfl) ⟨956762, by rfl⟩ : syracuseStep 1275683 = 1913525) B1913525
theorem B1275699 : Blo 1273955 1275699 := bstep (se 1 (by rfl) ⟨956774, by rfl⟩ : syracuseStep 1275699 = 1913549) B1913549
theorem B1275715 : Blo 1273955 1275715 := bstep (se 1 (by rfl) ⟨956786, by rfl⟩ : syracuseStep 1275715 = 1913573) B1913573
theorem B1275731 : Blo 1273955 1275731 := bstep (se 1 (by rfl) ⟨956798, by rfl⟩ : syracuseStep 1275731 = 1913597) B1913597
theorem B2152291 : Blo 1273955 2152291 := bstep (se 1 (by rfl) ⟨1614218, by rfl⟩ : syracuseStep 2152291 = 3228437) B3228437
theorem B1275747 : Blo 1273955 1275747 := bstep (se 1 (by rfl) ⟨956810, by rfl⟩ : syracuseStep 1275747 = 1913621) B1913621
theorem B1816435 : Blo 1273955 1816435 := bstep (se 1 (by rfl) ⟨1362326, by rfl⟩ : syracuseStep 1816435 = 2724653) B2724653
theorem B1275763 : Blo 1273955 1275763 := bstep (se 1 (by rfl) ⟨956822, by rfl⟩ : syracuseStep 1275763 = 1913645) B1913645
theorem B1275779 : Blo 1273955 1275779 := bstep (se 1 (by rfl) ⟨956834, by rfl⟩ : syracuseStep 1275779 = 1913669) B1913669
theorem B6125453 : Blo 1273955 6125453 := bstep (se 3 (by rfl) ⟨1148522, by rfl⟩ : syracuseStep 6125453 = 2297045) B2297045
theorem B1275795 : Blo 1273955 1275795 := bstep (se 1 (by rfl) ⟨956846, by rfl⟩ : syracuseStep 1275795 = 1913693) B1913693
theorem B1275811 : Blo 1273955 1275811 := bstep (se 1 (by rfl) ⟨956858, by rfl⟩ : syracuseStep 1275811 = 1913717) B1913717
theorem B3225521 : Blo 1273955 3225521 := bstep (se 2 (by rfl) ⟨1209570, by rfl⟩ : syracuseStep 3225521 = 2419141) B2419141
theorem B1275827 : Blo 1273955 1275827 := bstep (se 1 (by rfl) ⟨956870, by rfl⟩ : syracuseStep 1275827 = 1913741) B1913741
theorem B1275843 : Blo 1273955 1275843 := bstep (se 1 (by rfl) ⟨956882, by rfl⟩ : syracuseStep 1275843 = 1913765) B1913765
theorem B1275859 : Blo 1273955 1275859 := bstep (se 1 (by rfl) ⟨956894, by rfl⟩ : syracuseStep 1275859 = 1913789) B1913789
theorem B1275875 : Blo 1273955 1275875 := bstep (se 1 (by rfl) ⟨956906, by rfl⟩ : syracuseStep 1275875 = 1913813) B1913813
theorem B2152433 : Blo 1273955 2152433 := bstep (se 2 (by rfl) ⟨807162, by rfl⟩ : syracuseStep 2152433 = 1614325) B1614325
theorem B1275891 : Blo 1273955 1275891 := bstep (se 1 (by rfl) ⟨956918, by rfl⟩ : syracuseStep 1275891 = 1913837) B1913837
theorem B1275907 : Blo 1273955 1275907 := bstep (se 1 (by rfl) ⟨956930, by rfl⟩ : syracuseStep 1275907 = 1913861) B1913861
theorem B1275923 : Blo 1273955 1275923 := bstep (se 1 (by rfl) ⟨956942, by rfl⟩ : syracuseStep 1275923 = 1913885) B1913885
theorem B1275939 : Blo 1273955 1275939 := bstep (se 1 (by rfl) ⟨956954, by rfl⟩ : syracuseStep 1275939 = 1913909) B1913909
theorem B1275955 : Blo 1273955 1275955 := bstep (se 1 (by rfl) ⟨956966, by rfl⟩ : syracuseStep 1275955 = 1913933) B1913933
theorem B6887501 : Blo 1273955 6887501 := bstep (se 3 (by rfl) ⟨1291406, by rfl⟩ : syracuseStep 6887501 = 2582813) B2582813
theorem B2152561 : Blo 1273955 2152561 := bstep (se 2 (by rfl) ⟨807210, by rfl⟩ : syracuseStep 2152561 = 1614421) B1614421
theorem B2152595 : Blo 1273955 2152595 := bstep (se 1 (by rfl) ⟨1614446, by rfl⟩ : syracuseStep 2152595 = 3228893) B3228893
theorem B1841329 : Blo 1273955 1841329 := bstep (se 2 (by rfl) ⟨690498, by rfl⟩ : syracuseStep 1841329 = 1380997) B1380997
theorem B2152723 : Blo 1273955 2152723 := bstep (se 1 (by rfl) ⟨1614542, by rfl⟩ : syracuseStep 2152723 = 3229085) B3229085
theorem B2152865 : Blo 1273955 2152865 := bstep (se 2 (by rfl) ⟨807324, by rfl⟩ : syracuseStep 2152865 = 1614649) B1614649
theorem B2152993 : Blo 1273955 2152993 := bstep (se 2 (by rfl) ⟨807372, by rfl⟩ : syracuseStep 2152993 = 1614745) B1614745
theorem B2153027 : Blo 1273955 2153027 := bstep (se 1 (by rfl) ⟨1614770, by rfl⟩ : syracuseStep 2153027 = 3229541) B3229541
theorem B4840013 : Blo 1273955 4840013 := bstep (se 3 (by rfl) ⟨907502, by rfl⟩ : syracuseStep 4840013 = 1815005) B1815005
theorem B67148401 : Blo 1273955 67148401 := bstep (se 2 (by rfl) ⟨25180650, by rfl⟩ : syracuseStep 67148401 = 50361301) B50361301
theorem B2210465 : Blo 1273955 2210465 := bstep (se 2 (by rfl) ⟨828924, by rfl⟩ : syracuseStep 2210465 = 1657849) B1657849
theorem B2153155 : Blo 1273955 2153155 := bstep (se 1 (by rfl) ⟨1614866, by rfl⟩ : syracuseStep 2153155 = 3229733) B3229733
theorem B9681605 : Blo 1273955 9681605 := bstep (se 4 (by rfl) ⟨907650, by rfl⟩ : syracuseStep 9681605 = 1815301) B1815301
theorem B5446349 : Blo 1273955 5446349 := bstep (se 3 (by rfl) ⟨1021190, by rfl⟩ : syracuseStep 5446349 = 2042381) B2042381
theorem B7265123 : Blo 1273955 7265123 := bstep (se 1 (by rfl) ⟨5448842, by rfl⟩ : syracuseStep 7265123 = 10897685) B10897685
theorem B3226513 : Blo 1273955 3226513 := bstep (se 2 (by rfl) ⟨1209942, by rfl⟩ : syracuseStep 3226513 = 2419885) B2419885
theorem B3627949 : Blo 1273955 3627949 := bstep (se 3 (by rfl) ⟨680240, by rfl⟩ : syracuseStep 3627949 = 1360481) B1360481
theorem B4594637 : Blo 1273955 4594637 := bstep (se 3 (by rfl) ⟨861494, by rfl⟩ : syracuseStep 4594637 = 1722989) B1722989
theorem B7257059 : Blo 1273955 7257059 := bstep (se 1 (by rfl) ⟨5442794, by rfl⟩ : syracuseStep 7257059 = 10885589) B10885589
theorem B3447793 : Blo 1273955 3447793 := bstep (se 2 (by rfl) ⟨1292922, by rfl⟩ : syracuseStep 3447793 = 2585845) B2585845
theorem B1612867 : Blo 1273955 1612867 := bstep (se 1 (by rfl) ⟨1209650, by rfl⟩ : syracuseStep 1612867 = 2419301) B2419301
theorem B4299857 : Blo 1273955 4299857 := bstep (se 2 (by rfl) ⟨1612446, by rfl⟩ : syracuseStep 4299857 = 3224893) B3224893
theorem B1612963 : Blo 1273955 1612963 := bstep (se 1 (by rfl) ⟨1209722, by rfl⟩ : syracuseStep 1612963 = 2419445) B2419445
theorem B3226787 : Blo 1273955 3226787 := bstep (se 1 (by rfl) ⟨2420090, by rfl⟩ : syracuseStep 3226787 = 4840181) B4840181
theorem B55934165 : Blo 1273955 55934165 := bstep (se 7 (by rfl) ⟨655478, by rfl⟩ : syracuseStep 55934165 = 1310957) B1310957
theorem B4087043 : Blo 1273955 4087043 := bstep (se 1 (by rfl) ⟨3065282, by rfl⟩ : syracuseStep 4087043 = 6130565) B6130565
theorem B1531171 : Blo 1273955 1531171 := bstep (se 1 (by rfl) ⟨1148378, by rfl⟩ : syracuseStep 1531171 = 2296757) B2296757
theorem B2866481 : Blo 1273955 2866481 := bstep (se 2 (by rfl) ⟨1074930, by rfl⟩ : syracuseStep 2866481 = 2149861) B2149861
theorem B2866499 : Blo 1273955 2866499 := bstep (se 1 (by rfl) ⟨2149874, by rfl⟩ : syracuseStep 2866499 = 4299749) B4299749
theorem B1531219 : Blo 1273955 1531219 := bstep (se 1 (by rfl) ⟨1148414, by rfl⟩ : syracuseStep 1531219 = 2296829) B2296829
theorem B3226979 : Blo 1273955 3226979 := bstep (se 1 (by rfl) ⟨2420234, by rfl⟩ : syracuseStep 3226979 = 4840469) B4840469
theorem B1531315 : Blo 1273955 1531315 := bstep (se 1 (by rfl) ⟨1148486, by rfl⟩ : syracuseStep 1531315 = 2296973) B2296973
theorem B11042317 : Blo 1273955 11042317 := bstep (se 3 (by rfl) ⟨2070434, by rfl⟩ : syracuseStep 11042317 = 4140869) B4140869
theorem B2866769 : Blo 1273955 2866769 := bstep (se 2 (by rfl) ⟨1075038, by rfl⟩ : syracuseStep 2866769 = 2150077) B2150077
theorem B2866787 : Blo 1273955 2866787 := bstep (se 1 (by rfl) ⟨2150090, by rfl⟩ : syracuseStep 2866787 = 4300181) B4300181
theorem B4300397 : Blo 1273955 4300397 := bstep (se 3 (by rfl) ⟨806324, by rfl⟩ : syracuseStep 4300397 = 1612649) B1612649
theorem B13778545 : Blo 1273955 13778545 := bstep (se 2 (by rfl) ⟨5166954, by rfl⟩ : syracuseStep 13778545 = 10333909) B10333909
theorem B6987397 : Blo 1273955 6987397 := bstep (se 4 (by rfl) ⟨655068, by rfl⟩ : syracuseStep 6987397 = 1310137) B1310137
theorem B1613459 : Blo 1273955 1613459 := bstep (se 1 (by rfl) ⟨1210094, by rfl⟩ : syracuseStep 1613459 = 2420189) B2420189
theorem B4300451 : Blo 1273955 4300451 := bstep (se 1 (by rfl) ⟨3225338, by rfl⟩ : syracuseStep 4300451 = 6450677) B6450677
theorem B1433299 : Blo 1273955 1433299 := bstep (se 1 (by rfl) ⟨1074974, by rfl⟩ : syracuseStep 1433299 = 2149949) B2149949
theorem B6889187 : Blo 1273955 6889187 := bstep (se 1 (by rfl) ⟨5166890, by rfl⟩ : syracuseStep 6889187 = 10333781) B10333781
theorem B29449955 : Blo 1273955 29449955 := bstep (se 1 (by rfl) ⟨22087466, by rfl⟩ : syracuseStep 29449955 = 44174933) B44174933
theorem B7749361 : Blo 1273955 7749361 := bstep (se 2 (by rfl) ⟨2906010, by rfl⟩ : syracuseStep 7749361 = 5812021) B5812021
theorem B7266125 : Blo 1273955 7266125 := bstep (se 3 (by rfl) ⟨1362398, by rfl⟩ : syracuseStep 7266125 = 2724797) B2724797
theorem B1433443 : Blo 1273955 1433443 := bstep (se 1 (by rfl) ⟨1075082, by rfl⟩ : syracuseStep 1433443 = 2150165) B2150165
theorem B2867057 : Blo 1273955 2867057 := bstep (se 2 (by rfl) ⟨1075146, by rfl⟩ : syracuseStep 2867057 = 2150293) B2150293
theorem B2867075 : Blo 1273955 2867075 := bstep (se 1 (by rfl) ⟨2150306, by rfl⟩ : syracuseStep 2867075 = 4300613) B4300613
theorem B4300721 : Blo 1273955 4300721 := bstep (se 2 (by rfl) ⟨1612770, by rfl⟩ : syracuseStep 4300721 = 3225541) B3225541
theorem B1433587 : Blo 1273955 1433587 := bstep (se 1 (by rfl) ⟨1075190, by rfl⟩ : syracuseStep 1433587 = 2150381) B2150381
theorem B1531891 : Blo 1273955 1531891 := bstep (se 1 (by rfl) ⟨1148918, by rfl⟩ : syracuseStep 1531891 = 2297837) B2297837
theorem B2867201 : Blo 1273955 2867201 := bstep (se 2 (by rfl) ⟨1075200, by rfl⟩ : syracuseStep 2867201 = 2150401) B2150401
theorem B1433623 : Blo 1273955 1433623 := bstep (se 1 (by rfl) ⟨1075217, by rfl⟩ : syracuseStep 1433623 = 2150435) B2150435
theorem B26165429 : Blo 1273955 26165429 := bstep (se 5 (by rfl) ⟨1226504, by rfl⟩ : syracuseStep 26165429 = 2453009) B2453009
theorem B1433803 : Blo 1273955 1433803 := bstep (se 1 (by rfl) ⟨1075352, by rfl⟩ : syracuseStep 1433803 = 2150705) B2150705
theorem B2867417 : Blo 1273955 2867417 := bstep (se 2 (by rfl) ⟨1075281, by rfl⟩ : syracuseStep 2867417 = 2150563) B2150563
theorem B2908439 : Blo 1273955 2908439 := bstep (se 1 (by rfl) ⟨2181329, by rfl⟩ : syracuseStep 2908439 = 4362659) B4362659
theorem B2867507 : Blo 1273955 2867507 := bstep (se 1 (by rfl) ⟨2150630, by rfl⟩ : syracuseStep 2867507 = 4301261) B4301261
theorem B1433911 : Blo 1273955 1433911 := bstep (se 1 (by rfl) ⟨1075433, by rfl⟩ : syracuseStep 1433911 = 2150867) B2150867
theorem B2867543 : Blo 1273955 2867543 := bstep (se 1 (by rfl) ⟨2150657, by rfl⟩ : syracuseStep 2867543 = 4301315) B4301315
theorem B4301207 : Blo 1273955 4301207 := bstep (se 1 (by rfl) ⟨3225905, by rfl⟩ : syracuseStep 4301207 = 6451811) B6451811
theorem B3228083 : Blo 1273955 3228083 := bstep (se 1 (by rfl) ⟨2421062, by rfl⟩ : syracuseStep 3228083 = 4842125) B4842125
theorem B3269057 : Blo 1273955 3269057 := bstep (se 2 (by rfl) ⟨1225896, by rfl⟩ : syracuseStep 3269057 = 2451793) B2451793
theorem B1434091 : Blo 1273955 1434091 := bstep (se 1 (by rfl) ⟨1075568, by rfl⟩ : syracuseStep 1434091 = 2151137) B2151137
theorem B2867723 : Blo 1273955 2867723 := bstep (se 1 (by rfl) ⟨2150792, by rfl⟩ : syracuseStep 2867723 = 4301585) B4301585
theorem B7266833 : Blo 1273955 7266833 := bstep (se 2 (by rfl) ⟨2725062, by rfl⟩ : syracuseStep 7266833 = 5450125) B5450125
theorem B21791267 : Blo 1273955 21791267 := bstep (se 1 (by rfl) ⟨16343450, by rfl⟩ : syracuseStep 21791267 = 32686901) B32686901
theorem B2867777 : Blo 1273955 2867777 := bstep (se 2 (by rfl) ⟨1075416, by rfl⟩ : syracuseStep 2867777 = 2150833) B2150833
theorem B1434199 : Blo 1273955 1434199 := bstep (se 1 (by rfl) ⟨1075649, by rfl⟩ : syracuseStep 1434199 = 2151299) B2151299
theorem B9683549 : Blo 1273955 9683549 := bstep (se 3 (by rfl) ⟨1815665, by rfl⟩ : syracuseStep 9683549 = 3631331) B3631331
theorem B1614487 : Blo 1273955 1614487 := bstep (se 1 (by rfl) ⟨1210865, by rfl⟩ : syracuseStep 1614487 = 2421731) B2421731
theorem B1434379 : Blo 1273955 1434379 := bstep (se 1 (by rfl) ⟨1075784, by rfl⟩ : syracuseStep 1434379 = 2151569) B2151569
theorem B2867993 : Blo 1273955 2867993 := bstep (se 2 (by rfl) ⟨1075497, by rfl⟩ : syracuseStep 2867993 = 2150995) B2150995
theorem B89531201 : Blo 1273955 89531201 := bstep (se 2 (by rfl) ⟨33574200, by rfl⟩ : syracuseStep 89531201 = 67148401) B67148401
theorem B2868083 : Blo 1273955 2868083 := bstep (se 1 (by rfl) ⟨2151062, by rfl⟩ : syracuseStep 2868083 = 4302125) B4302125
theorem B1434487 : Blo 1273955 1434487 := bstep (se 1 (by rfl) ⟨1075865, by rfl⟩ : syracuseStep 1434487 = 2151731) B2151731
theorem B2868119 : Blo 1273955 2868119 := bstep (se 1 (by rfl) ⟨2151089, by rfl⟩ : syracuseStep 2868119 = 4302179) B4302179
theorem B4842413 : Blo 1273955 4842413 := bstep (se 3 (by rfl) ⟨907952, by rfl⟩ : syracuseStep 4842413 = 1815905) B1815905
theorem B4301747 : Blo 1273955 4301747 := bstep (se 1 (by rfl) ⟨3226310, by rfl⟩ : syracuseStep 4301747 = 6452621) B6452621
theorem B2040779 : Blo 1273955 2040779 := bstep (se 1 (by rfl) ⟨1530584, by rfl⟩ : syracuseStep 2040779 = 3061169) B3061169
theorem B4842443 : Blo 1273955 4842443 := bstep (se 1 (by rfl) ⟨3631832, by rfl⟩ : syracuseStep 4842443 = 7263665) B7263665
theorem B3228619 : Blo 1273955 3228619 := bstep (se 1 (by rfl) ⟨2421464, by rfl⟩ : syracuseStep 3228619 = 4842929) B4842929
theorem B5448707 : Blo 1273955 5448707 := bstep (se 1 (by rfl) ⟨4086530, by rfl⟩ : syracuseStep 5448707 = 8173061) B8173061
theorem B1434667 : Blo 1273955 1434667 := bstep (se 1 (by rfl) ⟨1076000, by rfl⟩ : syracuseStep 1434667 = 2152001) B2152001
theorem B2868299 : Blo 1273955 2868299 := bstep (se 1 (by rfl) ⟨2151224, by rfl⟩ : syracuseStep 2868299 = 4302449) B4302449
theorem B25183307 : Blo 1273955 25183307 := bstep (se 1 (by rfl) ⟨18887480, by rfl⟩ : syracuseStep 25183307 = 37774961) B37774961
theorem B3228761 : Blo 1273955 3228761 := bstep (se 2 (by rfl) ⟨1210785, by rfl⟩ : syracuseStep 3228761 = 2421571) B2421571
theorem B2868353 : Blo 1273955 2868353 := bstep (se 2 (by rfl) ⟨1075632, by rfl⟩ : syracuseStep 2868353 = 2151265) B2151265
theorem B12412055 : Blo 1273955 12412055 := bstep (se 1 (by rfl) ⟨9309041, by rfl⟩ : syracuseStep 12412055 = 18618083) B18618083
theorem B1434775 : Blo 1273955 1434775 := bstep (se 1 (by rfl) ⟨1076081, by rfl⟩ : syracuseStep 1434775 = 2152163) B2152163
theorem B8168627 : Blo 1273955 8168627 := bstep (se 1 (by rfl) ⟨6126470, by rfl⟩ : syracuseStep 8168627 = 12252941) B12252941
theorem B4302017 : Blo 1273955 4302017 := bstep (se 2 (by rfl) ⟨1613256, by rfl⟩ : syracuseStep 4302017 = 3226513) B3226513
theorem B41329925 : Blo 1273955 41329925 := bstep (se 4 (by rfl) ⟨3874680, by rfl⟩ : syracuseStep 41329925 = 7749361) B7749361
theorem B22086917 : Blo 1273955 22086917 := bstep (se 4 (by rfl) ⟨2070648, by rfl⟩ : syracuseStep 22086917 = 4141297) B4141297
theorem B4597057 : Blo 1273955 4597057 := bstep (se 2 (by rfl) ⟨1723896, by rfl⟩ : syracuseStep 4597057 = 3447793) B3447793
theorem B1434955 : Blo 1273955 1434955 := bstep (se 1 (by rfl) ⟨1076216, by rfl⟩ : syracuseStep 1434955 = 2152433) B2152433
theorem B2868569 : Blo 1273955 2868569 := bstep (se 2 (by rfl) ⟨1075713, by rfl⟩ : syracuseStep 2868569 = 2151427) B2151427
theorem B7259543 : Blo 1273955 7259543 := bstep (se 1 (by rfl) ⟨5444657, by rfl⟩ : syracuseStep 7259543 = 10889315) B10889315
theorem B19613107 : Blo 1273955 19613107 := bstep (se 1 (by rfl) ⟨14709830, by rfl⟩ : syracuseStep 19613107 = 29419661) B29419661
theorem B2868659 : Blo 1273955 2868659 := bstep (se 1 (by rfl) ⟨2151494, by rfl⟩ : syracuseStep 2868659 = 4302989) B4302989
theorem B1435063 : Blo 1273955 1435063 := bstep (se 1 (by rfl) ⟨1076297, by rfl⟩ : syracuseStep 1435063 = 2152595) B2152595
theorem B2868695 : Blo 1273955 2868695 := bstep (se 1 (by rfl) ⟨2151521, by rfl⟩ : syracuseStep 2868695 = 4303043) B4303043
theorem B3630557 : Blo 1273955 3630557 := bstep (se 3 (by rfl) ⟨680729, by rfl⟩ : syracuseStep 3630557 = 1361459) B1361459
theorem B11036225 : Blo 1273955 11036225 := bstep (se 2 (by rfl) ⟨4138584, by rfl⟩ : syracuseStep 11036225 = 8277169) B8277169
theorem B4843097 : Blo 1273955 4843097 := bstep (se 2 (by rfl) ⟨1816161, by rfl⟩ : syracuseStep 4843097 = 3632323) B3632323
theorem B13092445 : Blo 1273955 13092445 := bstep (se 3 (by rfl) ⟨2454833, by rfl⟩ : syracuseStep 13092445 = 4909667) B4909667
theorem B1435243 : Blo 1273955 1435243 := bstep (se 1 (by rfl) ⟨1076432, by rfl⟩ : syracuseStep 1435243 = 2152865) B2152865
theorem B2868875 : Blo 1273955 2868875 := bstep (se 1 (by rfl) ⟨2151656, by rfl⟩ : syracuseStep 2868875 = 4303313) B4303313
theorem B2868929 : Blo 1273955 2868929 := bstep (se 2 (by rfl) ⟨1075848, by rfl⟩ : syracuseStep 2868929 = 2151697) B2151697
theorem B1435351 : Blo 1273955 1435351 := bstep (se 1 (by rfl) ⟨1076513, by rfl⟩ : syracuseStep 1435351 = 2153027) B2153027
theorem B2041561 : Blo 1273955 2041561 := bstep (se 2 (by rfl) ⟨765585, by rfl⟩ : syracuseStep 2041561 = 1531171) B1531171
theorem B4302557 : Blo 1273955 4302557 := bstep (se 3 (by rfl) ⟨806729, by rfl⟩ : syracuseStep 4302557 = 1613459) B1613459
theorem B2041625 : Blo 1273955 2041625 := bstep (se 2 (by rfl) ⟨765609, by rfl⟩ : syracuseStep 2041625 = 1531219) B1531219
theorem B3630899 : Blo 1273955 3630899 := bstep (se 1 (by rfl) ⟨2723174, by rfl⟩ : syracuseStep 3630899 = 5446349) B5446349
theorem B4843415 : Blo 1273955 4843415 := bstep (se 1 (by rfl) ⟨3632561, by rfl⟩ : syracuseStep 4843415 = 7265123) B7265123
theorem B3229591 : Blo 1273955 3229591 := bstep (se 1 (by rfl) ⟨2422193, by rfl⟩ : syracuseStep 3229591 = 4844387) B4844387
theorem B2041753 : Blo 1273955 2041753 := bstep (se 2 (by rfl) ⟨765657, by rfl⟩ : syracuseStep 2041753 = 1531315) B1531315
theorem B2869145 : Blo 1273955 2869145 := bstep (se 2 (by rfl) ⟨1075929, by rfl⟩ : syracuseStep 2869145 = 2151859) B2151859
theorem B2869235 : Blo 1273955 2869235 := bstep (se 1 (by rfl) ⟨2151926, by rfl⟩ : syracuseStep 2869235 = 4303853) B4303853
theorem B1722379 : Blo 1273955 1722379 := bstep (se 1 (by rfl) ⟨1291784, by rfl⟩ : syracuseStep 1722379 = 2583569) B2583569
theorem B14723089 : Blo 1273955 14723089 := bstep (se 2 (by rfl) ⟨5521158, by rfl⟩ : syracuseStep 14723089 = 11042317) B11042317
theorem B2869271 : Blo 1273955 2869271 := bstep (se 1 (by rfl) ⟨2151953, by rfl⟩ : syracuseStep 2869271 = 4303907) B4303907
theorem B13789277 : Blo 1273955 13789277 := bstep (se 3 (by rfl) ⟨2585489, by rfl⟩ : syracuseStep 13789277 = 5170979) B5170979
theorem B9316529 : Blo 1273955 9316529 := bstep (se 2 (by rfl) ⟨3493698, by rfl⟩ : syracuseStep 9316529 = 6987397) B6987397
theorem B1910987 : Blo 1273955 1910987 := bstep (se 1 (by rfl) ⟨1433240, by rfl⟩ : syracuseStep 1910987 = 2866481) B2866481
theorem B2869451 : Blo 1273955 2869451 := bstep (se 1 (by rfl) ⟨2152088, by rfl⟩ : syracuseStep 2869451 = 4304177) B4304177
theorem B1910999 : Blo 1273955 1910999 := bstep (se 1 (by rfl) ⟨1433249, by rfl⟩ : syracuseStep 1910999 = 2866499) B2866499
theorem B2869505 : Blo 1273955 2869505 := bstep (se 2 (by rfl) ⟨1076064, by rfl⟩ : syracuseStep 2869505 = 2152129) B2152129
theorem B1911065 : Blo 1273955 1911065 := bstep (se 2 (by rfl) ⟨716649, by rfl⟩ : syracuseStep 1911065 = 1433299) B1433299
theorem B1911179 : Blo 1273955 1911179 := bstep (se 1 (by rfl) ⟨1433384, by rfl⟩ : syracuseStep 1911179 = 2866769) B2866769
theorem B1911191 : Blo 1273955 1911191 := bstep (se 1 (by rfl) ⟨1433393, by rfl⟩ : syracuseStep 1911191 = 2866787) B2866787
theorem B1911257 : Blo 1273955 1911257 := bstep (se 2 (by rfl) ⟨716721, by rfl⟩ : syracuseStep 1911257 = 1433443) B1433443
theorem B2869721 : Blo 1273955 2869721 := bstep (se 2 (by rfl) ⟨1076145, by rfl⟩ : syracuseStep 2869721 = 2152291) B2152291
theorem B2869811 : Blo 1273955 2869811 := bstep (se 1 (by rfl) ⟨2152358, by rfl⟩ : syracuseStep 2869811 = 4304717) B4304717
theorem B4844083 : Blo 1273955 4844083 := bstep (se 1 (by rfl) ⟨3633062, by rfl⟩ : syracuseStep 4844083 = 7266125) B7266125
theorem B1911371 : Blo 1273955 1911371 := bstep (se 1 (by rfl) ⟨1433528, by rfl⟩ : syracuseStep 1911371 = 2867057) B2867057
theorem B16566859 : Blo 1273955 16566859 := bstep (se 1 (by rfl) ⟨12425144, by rfl⟩ : syracuseStep 16566859 = 24850289) B24850289
theorem B1911383 : Blo 1273955 1911383 := bstep (se 1 (by rfl) ⟨1433537, by rfl⟩ : syracuseStep 1911383 = 2867075) B2867075
theorem B2869847 : Blo 1273955 2869847 := bstep (se 1 (by rfl) ⟨2152385, by rfl⟩ : syracuseStep 2869847 = 4304771) B4304771
theorem B8170085 : Blo 1273955 8170085 := bstep (se 4 (by rfl) ⟨765945, by rfl⟩ : syracuseStep 8170085 = 1531891) B1531891
theorem B1657495 : Blo 1273955 1657495 := bstep (se 1 (by rfl) ⟨1243121, by rfl⟩ : syracuseStep 1657495 = 2486243) B2486243
theorem B1911449 : Blo 1273955 1911449 := bstep (se 2 (by rfl) ⟨716793, by rfl⟩ : syracuseStep 1911449 = 1433587) B1433587
theorem B12258053 : Blo 1273955 12258053 := bstep (se 4 (by rfl) ⟨1149192, by rfl⟩ : syracuseStep 12258053 = 2298385) B2298385
theorem B1911563 : Blo 1273955 1911563 := bstep (se 1 (by rfl) ⟨1433672, by rfl⟩ : syracuseStep 1911563 = 2867345) B2867345
theorem B2870027 : Blo 1273955 2870027 := bstep (se 1 (by rfl) ⟨2152520, by rfl⟩ : syracuseStep 2870027 = 4305041) B4305041
theorem B6458129 : Blo 1273955 6458129 := bstep (se 2 (by rfl) ⟨2421798, by rfl⟩ : syracuseStep 6458129 = 4843597) B4843597
theorem B1911575 : Blo 1273955 1911575 := bstep (se 1 (by rfl) ⟨1433681, by rfl⟩ : syracuseStep 1911575 = 2867363) B2867363
theorem B2870081 : Blo 1273955 2870081 := bstep (se 2 (by rfl) ⟨1076280, by rfl⟩ : syracuseStep 2870081 = 2152561) B2152561
theorem B4082507 : Blo 1273955 4082507 := bstep (se 1 (by rfl) ⟨3061880, by rfl⟩ : syracuseStep 4082507 = 6123761) B6123761
theorem B4303691 : Blo 1273955 4303691 := bstep (se 1 (by rfl) ⟨3227768, by rfl⟩ : syracuseStep 4303691 = 6455537) B6455537
theorem B1911641 : Blo 1273955 1911641 := bstep (se 2 (by rfl) ⟨716865, by rfl⟩ : syracuseStep 1911641 = 1433731) B1433731
theorem B5172113 : Blo 1273955 5172113 := bstep (se 2 (by rfl) ⟨1939542, by rfl⟩ : syracuseStep 5172113 = 3879085) B3879085
theorem B6458291 : Blo 1273955 6458291 := bstep (se 1 (by rfl) ⟨4843718, by rfl⟩ : syracuseStep 6458291 = 9687437) B9687437
theorem B1911755 : Blo 1273955 1911755 := bstep (se 1 (by rfl) ⟨1433816, by rfl⟩ : syracuseStep 1911755 = 2867633) B2867633
theorem B1911767 : Blo 1273955 1911767 := bstep (se 1 (by rfl) ⟨1433825, by rfl⟩ : syracuseStep 1911767 = 2867651) B2867651
theorem B12422105 : Blo 1273955 12422105 := bstep (se 2 (by rfl) ⟨4658289, by rfl⟩ : syracuseStep 12422105 = 9316579) B9316579
theorem B1911833 : Blo 1273955 1911833 := bstep (se 2 (by rfl) ⟨716937, by rfl⟩ : syracuseStep 1911833 = 1433875) B1433875
theorem B2870297 : Blo 1273955 2870297 := bstep (se 2 (by rfl) ⟨1076361, by rfl⟩ : syracuseStep 2870297 = 2152723) B2152723
theorem B2419787 : Blo 1273955 2419787 := bstep (se 1 (by rfl) ⟨1814840, by rfl⟩ : syracuseStep 2419787 = 3629681) B3629681
theorem B4303961 : Blo 1273955 4303961 := bstep (se 2 (by rfl) ⟨1613985, by rfl⟩ : syracuseStep 4303961 = 3227971) B3227971
theorem B2870387 : Blo 1273955 2870387 := bstep (se 1 (by rfl) ⟨2152790, by rfl⟩ : syracuseStep 2870387 = 4305581) B4305581
theorem B2452619 : Blo 1273955 2452619 := bstep (se 1 (by rfl) ⟨1839464, by rfl⟩ : syracuseStep 2452619 = 3678929) B3678929
theorem B1911947 : Blo 1273955 1911947 := bstep (se 1 (by rfl) ⟨1433960, by rfl⟩ : syracuseStep 1911947 = 2867921) B2867921
theorem B1911959 : Blo 1273955 1911959 := bstep (se 1 (by rfl) ⟨1433969, by rfl⟩ : syracuseStep 1911959 = 2867939) B2867939
theorem B2870423 : Blo 1273955 2870423 := bstep (se 1 (by rfl) ⟨2152817, by rfl⟩ : syracuseStep 2870423 = 4305635) B4305635
theorem B21769397 : Blo 1273955 21769397 := bstep (se 5 (by rfl) ⟨1020440, by rfl⟩ : syracuseStep 21769397 = 2040881) B2040881
theorem B2583769 : Blo 1273955 2583769 := bstep (se 2 (by rfl) ⟨968913, by rfl⟩ : syracuseStep 2583769 = 1937827) B1937827
theorem B1912025 : Blo 1273955 1912025 := bstep (se 2 (by rfl) ⟨717009, by rfl⟩ : syracuseStep 1912025 = 1434019) B1434019
theorem B2419969 : Blo 1273955 2419969 := bstep (se 2 (by rfl) ⟨907488, by rfl⟩ : syracuseStep 2419969 = 1814977) B1814977
theorem B1912139 : Blo 1273955 1912139 := bstep (se 1 (by rfl) ⟨1434104, by rfl⟩ : syracuseStep 1912139 = 2868209) B2868209
theorem B2870603 : Blo 1273955 2870603 := bstep (se 1 (by rfl) ⟨2152952, by rfl⟩ : syracuseStep 2870603 = 4305905) B4305905
theorem B1912151 : Blo 1273955 1912151 := bstep (se 1 (by rfl) ⟨1434113, by rfl⟩ : syracuseStep 1912151 = 2868227) B2868227
theorem B24522101 : Blo 1273955 24522101 := bstep (se 5 (by rfl) ⟨1149473, by rfl⟩ : syracuseStep 24522101 = 2298947) B2298947
theorem B2870657 : Blo 1273955 2870657 := bstep (se 2 (by rfl) ⟨1076496, by rfl⟩ : syracuseStep 2870657 = 2152993) B2152993
theorem B4083095 : Blo 1273955 4083095 := bstep (se 1 (by rfl) ⟨3062321, by rfl⟩ : syracuseStep 4083095 = 6124643) B6124643
theorem B1912217 : Blo 1273955 1912217 := bstep (se 2 (by rfl) ⟨717081, by rfl⟩ : syracuseStep 1912217 = 1434163) B1434163
theorem B2723225 : Blo 1273955 2723225 := bstep (se 2 (by rfl) ⟨1021209, by rfl⟩ : syracuseStep 2723225 = 2042419) B2042419
theorem B5443033 : Blo 1273955 5443033 := bstep (se 2 (by rfl) ⟨2041137, by rfl⟩ : syracuseStep 5443033 = 4082275) B4082275
theorem B10890713 : Blo 1273955 10890713 := bstep (se 2 (by rfl) ⟨4084017, by rfl⟩ : syracuseStep 10890713 = 8168035) B8168035
theorem B1912331 : Blo 1273955 1912331 := bstep (se 1 (by rfl) ⟨1434248, by rfl⟩ : syracuseStep 1912331 = 2868497) B2868497
theorem B1912343 : Blo 1273955 1912343 := bstep (se 1 (by rfl) ⟨1434257, by rfl⟩ : syracuseStep 1912343 = 2868515) B2868515
theorem B1912409 : Blo 1273955 1912409 := bstep (se 2 (by rfl) ⟨717153, by rfl⟩ : syracuseStep 1912409 = 1434307) B1434307
theorem B2870873 : Blo 1273955 2870873 := bstep (se 2 (by rfl) ⟨1076577, by rfl⟩ : syracuseStep 2870873 = 2153155) B2153155
theorem B6450839 : Blo 1273955 6450839 := bstep (se 1 (by rfl) ⟨4838129, by rfl⟩ : syracuseStep 6450839 = 9676259) B9676259
theorem B3731123 : Blo 1273955 3731123 := bstep (se 1 (by rfl) ⟨2798342, by rfl⟩ : syracuseStep 3731123 = 5596685) B5596685
theorem B2420417 : Blo 1273955 2420417 := bstep (se 2 (by rfl) ⟨907656, by rfl⟩ : syracuseStep 2420417 = 1815313) B1815313
theorem B4837067 : Blo 1273955 4837067 := bstep (se 1 (by rfl) ⟨3627800, by rfl⟩ : syracuseStep 4837067 = 7255601) B7255601
theorem B1912523 : Blo 1273955 1912523 := bstep (se 1 (by rfl) ⟨1434392, by rfl⟩ : syracuseStep 1912523 = 2868785) B2868785
theorem B1912535 : Blo 1273955 1912535 := bstep (se 1 (by rfl) ⟨1434401, by rfl⟩ : syracuseStep 1912535 = 2868803) B2868803
theorem B4304663 : Blo 1273955 4304663 := bstep (se 1 (by rfl) ⟨3228497, by rfl⟩ : syracuseStep 4304663 = 6456995) B6456995
theorem B1912601 : Blo 1273955 1912601 := bstep (se 2 (by rfl) ⟨717225, by rfl⟩ : syracuseStep 1912601 = 1434451) B1434451
theorem B2723635 : Blo 1273955 2723635 := bstep (se 1 (by rfl) ⟨2042726, by rfl⟩ : syracuseStep 2723635 = 4085453) B4085453
theorem B2150219 : Blo 1273955 2150219 := bstep (se 1 (by rfl) ⟨1612664, by rfl⟩ : syracuseStep 2150219 = 3225329) B3225329
theorem B1912715 : Blo 1273955 1912715 := bstep (se 1 (by rfl) ⟨1434536, by rfl⟩ : syracuseStep 1912715 = 2869073) B2869073
theorem B4837265 : Blo 1273955 4837265 := bstep (se 2 (by rfl) ⟨1813974, by rfl⟩ : syracuseStep 4837265 = 3627949) B3627949
theorem B1912727 : Blo 1273955 1912727 := bstep (se 1 (by rfl) ⟨1434545, by rfl⟩ : syracuseStep 1912727 = 2869091) B2869091
theorem B4083635 : Blo 1273955 4083635 := bstep (se 1 (by rfl) ⟨3062726, by rfl⟩ : syracuseStep 4083635 = 6125453) B6125453
theorem B2150347 : Blo 1273955 2150347 := bstep (se 1 (by rfl) ⟨1612760, by rfl⟩ : syracuseStep 2150347 = 3225521) B3225521
theorem B1912793 : Blo 1273955 1912793 := bstep (se 2 (by rfl) ⟨717297, by rfl⟩ : syracuseStep 1912793 = 1434595) B1434595
theorem B10899461 : Blo 1273955 10899461 := bstep (se 4 (by rfl) ⟨1021824, by rfl⟩ : syracuseStep 10899461 = 2043649) B2043649
theorem B2420759 : Blo 1273955 2420759 := bstep (se 1 (by rfl) ⟨1815569, by rfl⟩ : syracuseStep 2420759 = 3631139) B3631139
theorem B4591667 : Blo 1273955 4591667 := bstep (se 1 (by rfl) ⟨3443750, by rfl⟩ : syracuseStep 4591667 = 6887501) B6887501
theorem B5443649 : Blo 1273955 5443649 := bstep (se 2 (by rfl) ⟨2041368, by rfl⟩ : syracuseStep 5443649 = 4082737) B4082737
theorem B1912907 : Blo 1273955 1912907 := bstep (se 1 (by rfl) ⟨1434680, by rfl⟩ : syracuseStep 1912907 = 2869361) B2869361
theorem B1912919 : Blo 1273955 1912919 := bstep (se 1 (by rfl) ⟨1434689, by rfl⟩ : syracuseStep 1912919 = 2869379) B2869379
theorem B2150489 : Blo 1273955 2150489 := bstep (se 2 (by rfl) ⟨806433, by rfl⟩ : syracuseStep 2150489 = 1612867) B1612867
theorem B3633245 : Blo 1273955 3633245 := bstep (se 3 (by rfl) ⟨681233, by rfl⟩ : syracuseStep 3633245 = 1362467) B1362467
theorem B1273963 : Blo 1273955 1273963 := bstep (se 1 (by rfl) ⟨955472, by rfl⟩ : syracuseStep 1273963 = 1910945) B1910945
theorem B1273975 : Blo 1273955 1273975 := bstep (se 1 (by rfl) ⟨955481, by rfl⟩ : syracuseStep 1273975 = 1910963) B1910963
theorem B2723969 : Blo 1273955 2723969 := bstep (se 2 (by rfl) ⟨1021488, by rfl⟩ : syracuseStep 2723969 = 2042977) B2042977
theorem B5173379 : Blo 1273955 5173379 := bstep (se 1 (by rfl) ⟨3880034, by rfl⟩ : syracuseStep 5173379 = 7760069) B7760069
theorem B1273995 : Blo 1273955 1273995 := bstep (se 1 (by rfl) ⟨955496, by rfl⟩ : syracuseStep 1273995 = 1910993) B1910993
theorem B1274007 : Blo 1273955 1274007 := bstep (se 1 (by rfl) ⟨955505, by rfl⟩ : syracuseStep 1274007 = 1911011) B1911011
theorem B1912985 : Blo 1273955 1912985 := bstep (se 2 (by rfl) ⟨717369, by rfl⟩ : syracuseStep 1912985 = 1434739) B1434739
theorem B1274027 : Blo 1273955 1274027 := bstep (se 1 (by rfl) ⟨955520, by rfl⟩ : syracuseStep 1274027 = 1911041) B1911041
theorem B1274039 : Blo 1273955 1274039 := bstep (se 1 (by rfl) ⟨955529, by rfl⟩ : syracuseStep 1274039 = 1911059) B1911059
theorem B1274059 : Blo 1273955 1274059 := bstep (se 1 (by rfl) ⟨955544, by rfl⟩ : syracuseStep 1274059 = 1911089) B1911089
theorem B1274071 : Blo 1273955 1274071 := bstep (se 1 (by rfl) ⟨955553, by rfl⟩ : syracuseStep 1274071 = 1911107) B1911107
theorem B2150617 : Blo 1273955 2150617 := bstep (se 2 (by rfl) ⟨806481, by rfl⟩ : syracuseStep 2150617 = 1612963) B1612963
theorem B1274091 : Blo 1273955 1274091 := bstep (se 1 (by rfl) ⟨955568, by rfl⟩ : syracuseStep 1274091 = 1911137) B1911137
theorem B1274103 : Blo 1273955 1274103 := bstep (se 1 (by rfl) ⟨955577, by rfl⟩ : syracuseStep 1274103 = 1911155) B1911155
theorem B1274123 : Blo 1273955 1274123 := bstep (se 1 (by rfl) ⟨955592, by rfl⟩ : syracuseStep 1274123 = 1911185) B1911185
theorem B1913099 : Blo 1273955 1913099 := bstep (se 1 (by rfl) ⟨1434824, by rfl⟩ : syracuseStep 1913099 = 2869649) B2869649
theorem B1274135 : Blo 1273955 1274135 := bstep (se 1 (by rfl) ⟨955601, by rfl⟩ : syracuseStep 1274135 = 1911203) B1911203
theorem B1913111 : Blo 1273955 1913111 := bstep (se 1 (by rfl) ⟨1434833, by rfl⟩ : syracuseStep 1913111 = 2869667) B2869667
theorem B1274155 : Blo 1273955 1274155 := bstep (se 1 (by rfl) ⟨955616, by rfl⟩ : syracuseStep 1274155 = 1911233) B1911233
theorem B4305203 : Blo 1273955 4305203 := bstep (se 1 (by rfl) ⟨3228902, by rfl⟩ : syracuseStep 4305203 = 6457805) B6457805
theorem B1274167 : Blo 1273955 1274167 := bstep (se 1 (by rfl) ⟨955625, by rfl⟩ : syracuseStep 1274167 = 1911251) B1911251
theorem B3633473 : Blo 1273955 3633473 := bstep (se 2 (by rfl) ⟨1362552, by rfl⟩ : syracuseStep 3633473 = 2725105) B2725105
theorem B1274187 : Blo 1273955 1274187 := bstep (se 1 (by rfl) ⟨955640, by rfl⟩ : syracuseStep 1274187 = 1911281) B1911281
theorem B1274199 : Blo 1273955 1274199 := bstep (se 1 (by rfl) ⟨955649, by rfl⟩ : syracuseStep 1274199 = 1911299) B1911299
theorem B1913177 : Blo 1273955 1913177 := bstep (se 2 (by rfl) ⟨717441, by rfl⟩ : syracuseStep 1913177 = 1434883) B1434883
theorem B1274219 : Blo 1273955 1274219 := bstep (se 1 (by rfl) ⟨955664, by rfl⟩ : syracuseStep 1274219 = 1911329) B1911329
theorem B1274231 : Blo 1273955 1274231 := bstep (se 1 (by rfl) ⟨955673, by rfl⟩ : syracuseStep 1274231 = 1911347) B1911347
theorem B2298241 : Blo 1273955 2298241 := bstep (se 2 (by rfl) ⟨861840, by rfl⟩ : syracuseStep 2298241 = 1723681) B1723681
theorem B1274251 : Blo 1273955 1274251 := bstep (se 1 (by rfl) ⟨955688, by rfl⟩ : syracuseStep 1274251 = 1911377) B1911377
theorem B5517713 : Blo 1273955 5517713 := bstep (se 2 (by rfl) ⟨2069142, by rfl⟩ : syracuseStep 5517713 = 4138285) B4138285
theorem B1274263 : Blo 1273955 1274263 := bstep (se 1 (by rfl) ⟨955697, by rfl⟩ : syracuseStep 1274263 = 1911395) B1911395
theorem B1274283 : Blo 1273955 1274283 := bstep (se 1 (by rfl) ⟨955712, by rfl⟩ : syracuseStep 1274283 = 1911425) B1911425
theorem B1274295 : Blo 1273955 1274295 := bstep (se 1 (by rfl) ⟨955721, by rfl⟩ : syracuseStep 1274295 = 1911443) B1911443
theorem B1274315 : Blo 1273955 1274315 := bstep (se 1 (by rfl) ⟨955736, by rfl⟩ : syracuseStep 1274315 = 1911473) B1911473
theorem B1913291 : Blo 1273955 1913291 := bstep (se 1 (by rfl) ⟨1434968, by rfl⟩ : syracuseStep 1913291 = 2869937) B2869937
theorem B1274327 : Blo 1273955 1274327 := bstep (se 1 (by rfl) ⟨955745, by rfl⟩ : syracuseStep 1274327 = 1911491) B1911491
theorem B1913303 : Blo 1273955 1913303 := bstep (se 1 (by rfl) ⟨1434977, by rfl⟩ : syracuseStep 1913303 = 2869955) B2869955
theorem B1274347 : Blo 1273955 1274347 := bstep (se 1 (by rfl) ⟨955760, by rfl⟩ : syracuseStep 1274347 = 1911521) B1911521
theorem B1274359 : Blo 1273955 1274359 := bstep (se 1 (by rfl) ⟨955769, by rfl⟩ : syracuseStep 1274359 = 1911539) B1911539
theorem B1274379 : Blo 1273955 1274379 := bstep (se 1 (by rfl) ⟨955784, by rfl⟩ : syracuseStep 1274379 = 1911569) B1911569
theorem B1274391 : Blo 1273955 1274391 := bstep (se 1 (by rfl) ⟨955793, by rfl⟩ : syracuseStep 1274391 = 1911587) B1911587
theorem B1913369 : Blo 1273955 1913369 := bstep (se 2 (by rfl) ⟨717513, by rfl⟩ : syracuseStep 1913369 = 1435027) B1435027
theorem B1274411 : Blo 1273955 1274411 := bstep (se 1 (by rfl) ⟨955808, by rfl⟩ : syracuseStep 1274411 = 1911617) B1911617
theorem B1274423 : Blo 1273955 1274423 := bstep (se 1 (by rfl) ⟨955817, by rfl⟩ : syracuseStep 1274423 = 1911635) B1911635
theorem B4305473 : Blo 1273955 4305473 := bstep (se 2 (by rfl) ⟨1614552, by rfl⟩ : syracuseStep 4305473 = 3229105) B3229105
theorem B1274443 : Blo 1273955 1274443 := bstep (se 1 (by rfl) ⟨955832, by rfl⟩ : syracuseStep 1274443 = 1911665) B1911665
theorem B1274455 : Blo 1273955 1274455 := bstep (se 1 (by rfl) ⟨955841, by rfl⟩ : syracuseStep 1274455 = 1911683) B1911683
theorem B1274475 : Blo 1273955 1274475 := bstep (se 1 (by rfl) ⟨955856, by rfl⟩ : syracuseStep 1274475 = 1911713) B1911713
theorem B1274487 : Blo 1273955 1274487 := bstep (se 1 (by rfl) ⟨955865, by rfl⟩ : syracuseStep 1274487 = 1911731) B1911731
theorem B1274507 : Blo 1273955 1274507 := bstep (se 1 (by rfl) ⟨955880, by rfl⟩ : syracuseStep 1274507 = 1911761) B1911761
theorem B1913483 : Blo 1273955 1913483 := bstep (se 1 (by rfl) ⟨1435112, by rfl⟩ : syracuseStep 1913483 = 2870225) B2870225
theorem B4838039 : Blo 1273955 4838039 := bstep (se 1 (by rfl) ⟨3628529, by rfl⟩ : syracuseStep 4838039 = 7257059) B7257059
theorem B1274519 : Blo 1273955 1274519 := bstep (se 1 (by rfl) ⟨955889, by rfl⟩ : syracuseStep 1274519 = 1911779) B1911779
theorem B1913495 : Blo 1273955 1913495 := bstep (se 1 (by rfl) ⟨1435121, by rfl⟩ : syracuseStep 1913495 = 2870243) B2870243
theorem B1274539 : Blo 1273955 1274539 := bstep (se 1 (by rfl) ⟨955904, by rfl⟩ : syracuseStep 1274539 = 1911809) B1911809
theorem B2421427 : Blo 1273955 2421427 := bstep (se 1 (by rfl) ⟨1816070, by rfl⟩ : syracuseStep 2421427 = 3632141) B3632141
theorem B1274551 : Blo 1273955 1274551 := bstep (se 1 (by rfl) ⟨955913, by rfl⟩ : syracuseStep 1274551 = 1911827) B1911827
theorem B1274571 : Blo 1273955 1274571 := bstep (se 1 (by rfl) ⟨955928, by rfl⟩ : syracuseStep 1274571 = 1911857) B1911857
theorem B1274583 : Blo 1273955 1274583 := bstep (se 1 (by rfl) ⟨955937, by rfl⟩ : syracuseStep 1274583 = 1911875) B1911875
theorem B1913561 : Blo 1273955 1913561 := bstep (se 2 (by rfl) ⟨717585, by rfl⟩ : syracuseStep 1913561 = 1435171) B1435171
theorem B1274603 : Blo 1273955 1274603 := bstep (se 1 (by rfl) ⟨955952, by rfl⟩ : syracuseStep 1274603 = 1911905) B1911905
theorem B1274615 : Blo 1273955 1274615 := bstep (se 1 (by rfl) ⟨955961, by rfl⟩ : syracuseStep 1274615 = 1911923) B1911923
theorem B1274635 : Blo 1273955 1274635 := bstep (se 1 (by rfl) ⟨955976, by rfl⟩ : syracuseStep 1274635 = 1911953) B1911953
theorem B1274647 : Blo 1273955 1274647 := bstep (se 1 (by rfl) ⟨955985, by rfl⟩ : syracuseStep 1274647 = 1911971) B1911971
theorem B2151191 : Blo 1273955 2151191 := bstep (se 1 (by rfl) ⟨1613393, by rfl⟩ : syracuseStep 2151191 = 3226787) B3226787
theorem B1274667 : Blo 1273955 1274667 := bstep (se 1 (by rfl) ⟨956000, by rfl⟩ : syracuseStep 1274667 = 1912001) B1912001
theorem B9679661 : Blo 1273955 9679661 := bstep (se 3 (by rfl) ⟨1814936, by rfl⟩ : syracuseStep 9679661 = 3629873) B3629873
theorem B1274679 : Blo 1273955 1274679 := bstep (se 1 (by rfl) ⟨956009, by rfl⟩ : syracuseStep 1274679 = 1912019) B1912019
theorem B18371393 : Blo 1273955 18371393 := bstep (se 2 (by rfl) ⟨6889272, by rfl⟩ : syracuseStep 18371393 = 13778545) B13778545
theorem B1274699 : Blo 1273955 1274699 := bstep (se 1 (by rfl) ⟨956024, by rfl⟩ : syracuseStep 1274699 = 1912049) B1912049
theorem B1913675 : Blo 1273955 1913675 := bstep (se 1 (by rfl) ⟨1435256, by rfl⟩ : syracuseStep 1913675 = 2870513) B2870513
theorem B1274711 : Blo 1273955 1274711 := bstep (se 1 (by rfl) ⟨956033, by rfl⟩ : syracuseStep 1274711 = 1912067) B1912067
theorem B2724695 : Blo 1273955 2724695 := bstep (se 1 (by rfl) ⟨2043521, by rfl⟩ : syracuseStep 2724695 = 4087043) B4087043
theorem B5895001 : Blo 1273955 5895001 := bstep (se 2 (by rfl) ⟨2210625, by rfl⟩ : syracuseStep 5895001 = 4421251) B4421251
theorem B1913687 : Blo 1273955 1913687 := bstep (se 1 (by rfl) ⟨1435265, by rfl⟩ : syracuseStep 1913687 = 2870531) B2870531
theorem B4838237 : Blo 1273955 4838237 := bstep (se 3 (by rfl) ⟨907169, by rfl⟩ : syracuseStep 4838237 = 1814339) B1814339
theorem B1274731 : Blo 1273955 1274731 := bstep (se 1 (by rfl) ⟨956048, by rfl⟩ : syracuseStep 1274731 = 1912097) B1912097
theorem B1274743 : Blo 1273955 1274743 := bstep (se 1 (by rfl) ⟨956057, by rfl⟩ : syracuseStep 1274743 = 1912115) B1912115
theorem B1274763 : Blo 1273955 1274763 := bstep (se 1 (by rfl) ⟨956072, by rfl⟩ : syracuseStep 1274763 = 1912145) B1912145
theorem B1274775 : Blo 1273955 1274775 := bstep (se 1 (by rfl) ⟨956081, by rfl⟩ : syracuseStep 1274775 = 1912163) B1912163
theorem B2151319 : Blo 1273955 2151319 := bstep (se 1 (by rfl) ⟨1613489, by rfl⟩ : syracuseStep 2151319 = 3226979) B3226979
theorem B1913753 : Blo 1273955 1913753 := bstep (se 2 (by rfl) ⟨717657, by rfl⟩ : syracuseStep 1913753 = 1435315) B1435315
theorem B1274795 : Blo 1273955 1274795 := bstep (se 1 (by rfl) ⟨956096, by rfl⟩ : syracuseStep 1274795 = 1912193) B1912193
theorem B1274807 : Blo 1273955 1274807 := bstep (se 1 (by rfl) ⟨956105, by rfl⟩ : syracuseStep 1274807 = 1912211) B1912211
theorem B1274827 : Blo 1273955 1274827 := bstep (se 1 (by rfl) ⟨956120, by rfl⟩ : syracuseStep 1274827 = 1912241) B1912241
theorem B1274839 : Blo 1273955 1274839 := bstep (se 1 (by rfl) ⟨956129, by rfl⟩ : syracuseStep 1274839 = 1912259) B1912259
theorem B1274859 : Blo 1273955 1274859 := bstep (se 1 (by rfl) ⟨956144, by rfl⟩ : syracuseStep 1274859 = 1912289) B1912289
theorem B1274871 : Blo 1273955 1274871 := bstep (se 1 (by rfl) ⟨956153, by rfl⟩ : syracuseStep 1274871 = 1912307) B1912307
theorem B1274891 : Blo 1273955 1274891 := bstep (se 1 (by rfl) ⟨956168, by rfl⟩ : syracuseStep 1274891 = 1912337) B1912337
theorem B1913867 : Blo 1273955 1913867 := bstep (se 1 (by rfl) ⟨1435400, by rfl⟩ : syracuseStep 1913867 = 2870801) B2870801
theorem B1274903 : Blo 1273955 1274903 := bstep (se 1 (by rfl) ⟨956177, by rfl⟩ : syracuseStep 1274903 = 1912355) B1912355
theorem B1913879 : Blo 1273955 1913879 := bstep (se 1 (by rfl) ⟨1435409, by rfl⟩ : syracuseStep 1913879 = 2870819) B2870819
theorem B1274923 : Blo 1273955 1274923 := bstep (se 1 (by rfl) ⟨956192, by rfl⟩ : syracuseStep 1274923 = 1912385) B1912385
theorem B1274935 : Blo 1273955 1274935 := bstep (se 1 (by rfl) ⟨956201, by rfl⟩ : syracuseStep 1274935 = 1912403) B1912403
theorem B10892353 : Blo 1273955 10892353 := bstep (se 2 (by rfl) ⟨4084632, by rfl⟩ : syracuseStep 10892353 = 8169265) B8169265
theorem B1274955 : Blo 1273955 1274955 := bstep (se 1 (by rfl) ⟨956216, by rfl⟩ : syracuseStep 1274955 = 1912433) B1912433
theorem B1274967 : Blo 1273955 1274967 := bstep (se 1 (by rfl) ⟨956225, by rfl⟩ : syracuseStep 1274967 = 1912451) B1912451
theorem B4306013 : Blo 1273955 4306013 := bstep (se 3 (by rfl) ⟨807377, by rfl⟩ : syracuseStep 4306013 = 1614755) B1614755
theorem B1274987 : Blo 1273955 1274987 := bstep (se 1 (by rfl) ⟨956240, by rfl⟩ : syracuseStep 1274987 = 1912481) B1912481
theorem B2421875 : Blo 1273955 2421875 := bstep (se 1 (by rfl) ⟨1816406, by rfl⟩ : syracuseStep 2421875 = 3632813) B3632813
theorem B1274999 : Blo 1273955 1274999 := bstep (se 1 (by rfl) ⟨956249, by rfl⟩ : syracuseStep 1274999 = 1912499) B1912499
theorem B1275019 : Blo 1273955 1275019 := bstep (se 1 (by rfl) ⟨956264, by rfl⟩ : syracuseStep 1275019 = 1912529) B1912529
theorem B4592791 : Blo 1273955 4592791 := bstep (se 1 (by rfl) ⟨3444593, by rfl⟩ : syracuseStep 4592791 = 6889187) B6889187
theorem B1275031 : Blo 1273955 1275031 := bstep (se 1 (by rfl) ⟨956273, by rfl⟩ : syracuseStep 1275031 = 1912547) B1912547
theorem B19633303 : Blo 1273955 19633303 := bstep (se 1 (by rfl) ⟨14724977, by rfl⟩ : syracuseStep 19633303 = 29449955) B29449955
theorem B2421913 : Blo 1273955 2421913 := bstep (se 2 (by rfl) ⟨908217, by rfl⟩ : syracuseStep 2421913 = 1816435) B1816435
theorem B1275051 : Blo 1273955 1275051 := bstep (se 1 (by rfl) ⟨956288, by rfl⟩ : syracuseStep 1275051 = 1912577) B1912577
theorem B1275063 : Blo 1273955 1275063 := bstep (se 1 (by rfl) ⟨956297, by rfl⟩ : syracuseStep 1275063 = 1912595) B1912595
theorem B1275083 : Blo 1273955 1275083 := bstep (se 1 (by rfl) ⟨956312, by rfl⟩ : syracuseStep 1275083 = 1912625) B1912625
theorem B1275095 : Blo 1273955 1275095 := bstep (se 1 (by rfl) ⟨956321, by rfl⟩ : syracuseStep 1275095 = 1912643) B1912643
theorem B1275115 : Blo 1273955 1275115 := bstep (se 1 (by rfl) ⟨956336, by rfl⟩ : syracuseStep 1275115 = 1912673) B1912673
theorem B1275127 : Blo 1273955 1275127 := bstep (se 1 (by rfl) ⟨956345, by rfl⟩ : syracuseStep 1275127 = 1912691) B1912691
theorem B1275147 : Blo 1273955 1275147 := bstep (se 1 (by rfl) ⟨956360, by rfl⟩ : syracuseStep 1275147 = 1912721) B1912721
theorem B1275159 : Blo 1273955 1275159 := bstep (se 1 (by rfl) ⟨956369, by rfl⟩ : syracuseStep 1275159 = 1912739) B1912739
theorem B1275179 : Blo 1273955 1275179 := bstep (se 1 (by rfl) ⟨956384, by rfl⟩ : syracuseStep 1275179 = 1912769) B1912769
theorem B1275191 : Blo 1273955 1275191 := bstep (se 1 (by rfl) ⟨956393, by rfl⟩ : syracuseStep 1275191 = 1912787) B1912787
theorem B1275211 : Blo 1273955 1275211 := bstep (se 1 (by rfl) ⟨956408, by rfl⟩ : syracuseStep 1275211 = 1912817) B1912817
theorem B1275223 : Blo 1273955 1275223 := bstep (se 1 (by rfl) ⟨956417, by rfl⟩ : syracuseStep 1275223 = 1912835) B1912835
theorem B1275243 : Blo 1273955 1275243 := bstep (se 1 (by rfl) ⟨956432, by rfl⟩ : syracuseStep 1275243 = 1912865) B1912865
theorem B1275255 : Blo 1273955 1275255 := bstep (se 1 (by rfl) ⟨956441, by rfl⟩ : syracuseStep 1275255 = 1912883) B1912883
theorem B1275275 : Blo 1273955 1275275 := bstep (se 1 (by rfl) ⟨956456, by rfl⟩ : syracuseStep 1275275 = 1912913) B1912913
theorem B1275287 : Blo 1273955 1275287 := bstep (se 1 (by rfl) ⟨956465, by rfl⟩ : syracuseStep 1275287 = 1912931) B1912931
theorem B1275307 : Blo 1273955 1275307 := bstep (se 1 (by rfl) ⟨956480, by rfl⟩ : syracuseStep 1275307 = 1912961) B1912961
theorem B1275319 : Blo 1273955 1275319 := bstep (se 1 (by rfl) ⟨956489, by rfl⟩ : syracuseStep 1275319 = 1912979) B1912979
theorem B2905537 : Blo 1273955 2905537 := bstep (se 2 (by rfl) ⟨1089576, by rfl⟩ : syracuseStep 2905537 = 2179153) B2179153
theorem B3225035 : Blo 1273955 3225035 := bstep (se 1 (by rfl) ⟨2418776, by rfl⟩ : syracuseStep 3225035 = 4837553) B4837553
theorem B1275339 : Blo 1273955 1275339 := bstep (se 1 (by rfl) ⟨956504, by rfl⟩ : syracuseStep 1275339 = 1913009) B1913009
theorem B4363723 : Blo 1273955 4363723 := bstep (se 1 (by rfl) ⟨3272792, by rfl⟩ : syracuseStep 4363723 = 6545585) B6545585
theorem B1275351 : Blo 1273955 1275351 := bstep (se 1 (by rfl) ⟨956513, by rfl⟩ : syracuseStep 1275351 = 1913027) B1913027
theorem B1275371 : Blo 1273955 1275371 := bstep (se 1 (by rfl) ⟨956528, by rfl⟩ : syracuseStep 1275371 = 1913057) B1913057
theorem B2946547 : Blo 1273955 2946547 := bstep (se 1 (by rfl) ⟨2209910, by rfl⟩ : syracuseStep 2946547 = 4419821) B4419821
theorem B1275383 : Blo 1273955 1275383 := bstep (se 1 (by rfl) ⟨956537, by rfl⟩ : syracuseStep 1275383 = 1913075) B1913075
theorem B2151947 : Blo 1273955 2151947 := bstep (se 1 (by rfl) ⟨1613960, by rfl⟩ : syracuseStep 2151947 = 3227921) B3227921
theorem B1275403 : Blo 1273955 1275403 := bstep (se 1 (by rfl) ⟨956552, by rfl⟩ : syracuseStep 1275403 = 1913105) B1913105
theorem B1275415 : Blo 1273955 1275415 := bstep (se 1 (by rfl) ⟨956561, by rfl⟩ : syracuseStep 1275415 = 1913123) B1913123
theorem B1275435 : Blo 1273955 1275435 := bstep (se 1 (by rfl) ⟨956576, by rfl⟩ : syracuseStep 1275435 = 1913153) B1913153
theorem B1275447 : Blo 1273955 1275447 := bstep (se 1 (by rfl) ⟨956585, by rfl⟩ : syracuseStep 1275447 = 1913171) B1913171
theorem B2455105 : Blo 1273955 2455105 := bstep (se 2 (by rfl) ⟨920664, by rfl⟩ : syracuseStep 2455105 = 1841329) B1841329
theorem B1275467 : Blo 1273955 1275467 := bstep (se 1 (by rfl) ⟨956600, by rfl⟩ : syracuseStep 1275467 = 1913201) B1913201
theorem B1275479 : Blo 1273955 1275479 := bstep (se 1 (by rfl) ⟨956609, by rfl⟩ : syracuseStep 1275479 = 1913219) B1913219
theorem B1275499 : Blo 1273955 1275499 := bstep (se 1 (by rfl) ⟨956624, by rfl⟩ : syracuseStep 1275499 = 1913249) B1913249
theorem B1275511 : Blo 1273955 1275511 := bstep (se 1 (by rfl) ⟨956633, by rfl⟩ : syracuseStep 1275511 = 1913267) B1913267
theorem B2152075 : Blo 1273955 2152075 := bstep (se 1 (by rfl) ⟨1614056, by rfl⟩ : syracuseStep 2152075 = 3228113) B3228113
theorem B1275531 : Blo 1273955 1275531 := bstep (se 1 (by rfl) ⟨956648, by rfl⟩ : syracuseStep 1275531 = 1913297) B1913297
theorem B2758295 : Blo 1273955 2758295 := bstep (se 1 (by rfl) ⟨2068721, by rfl⟩ : syracuseStep 2758295 = 4137443) B4137443
theorem B1275543 : Blo 1273955 1275543 := bstep (se 1 (by rfl) ⟨956657, by rfl⟩ : syracuseStep 1275543 = 1913315) B1913315
theorem B1275563 : Blo 1273955 1275563 := bstep (se 1 (by rfl) ⟨956672, by rfl⟩ : syracuseStep 1275563 = 1913345) B1913345
theorem B10335923 : Blo 1273955 10335923 := bstep (se 1 (by rfl) ⟨7751942, by rfl⟩ : syracuseStep 10335923 = 15503885) B15503885
theorem B1275575 : Blo 1273955 1275575 := bstep (se 1 (by rfl) ⟨956681, by rfl⟩ : syracuseStep 1275575 = 1913363) B1913363
theorem B1275595 : Blo 1273955 1275595 := bstep (se 1 (by rfl) ⟨956696, by rfl⟩ : syracuseStep 1275595 = 1913393) B1913393
theorem B1275607 : Blo 1273955 1275607 := bstep (se 1 (by rfl) ⟨956705, by rfl⟩ : syracuseStep 1275607 = 1913411) B1913411
theorem B1275627 : Blo 1273955 1275627 := bstep (se 1 (by rfl) ⟨956720, by rfl⟩ : syracuseStep 1275627 = 1913441) B1913441
theorem B1275639 : Blo 1273955 1275639 := bstep (se 1 (by rfl) ⟨956729, by rfl⟩ : syracuseStep 1275639 = 1913459) B1913459
theorem B1275659 : Blo 1273955 1275659 := bstep (se 1 (by rfl) ⟨956744, by rfl⟩ : syracuseStep 1275659 = 1913489) B1913489
theorem B1275671 : Blo 1273955 1275671 := bstep (se 1 (by rfl) ⟨956753, by rfl⟩ : syracuseStep 1275671 = 1913507) B1913507
theorem B2152217 : Blo 1273955 2152217 := bstep (se 2 (by rfl) ⟨807081, by rfl⟩ : syracuseStep 2152217 = 1614163) B1614163
theorem B1275691 : Blo 1273955 1275691 := bstep (se 1 (by rfl) ⟨956768, by rfl⟩ : syracuseStep 1275691 = 1913537) B1913537
theorem B1275703 : Blo 1273955 1275703 := bstep (se 1 (by rfl) ⟨956777, by rfl⟩ : syracuseStep 1275703 = 1913555) B1913555
theorem B2905931 : Blo 1273955 2905931 := bstep (se 1 (by rfl) ⟨2179448, by rfl⟩ : syracuseStep 2905931 = 4358897) B4358897
theorem B1275723 : Blo 1273955 1275723 := bstep (se 1 (by rfl) ⟨956792, by rfl⟩ : syracuseStep 1275723 = 1913585) B1913585
theorem B1275735 : Blo 1273955 1275735 := bstep (se 1 (by rfl) ⟨956801, by rfl⟩ : syracuseStep 1275735 = 1913603) B1913603
theorem B1275755 : Blo 1273955 1275755 := bstep (se 1 (by rfl) ⟨956816, by rfl⟩ : syracuseStep 1275755 = 1913633) B1913633
theorem B1275767 : Blo 1273955 1275767 := bstep (se 1 (by rfl) ⟨956825, by rfl⟩ : syracuseStep 1275767 = 1913651) B1913651
theorem B1275787 : Blo 1273955 1275787 := bstep (se 1 (by rfl) ⟨956840, by rfl⟩ : syracuseStep 1275787 = 1913681) B1913681
theorem B149157773 : Blo 1273955 149157773 := bstep (se 3 (by rfl) ⟨27967082, by rfl⟩ : syracuseStep 149157773 = 55934165) B55934165
theorem B1275799 : Blo 1273955 1275799 := bstep (se 1 (by rfl) ⟨956849, by rfl⟩ : syracuseStep 1275799 = 1913699) B1913699
theorem B2152345 : Blo 1273955 2152345 := bstep (se 2 (by rfl) ⟨807129, by rfl⟩ : syracuseStep 2152345 = 1614259) B1614259
theorem B1275819 : Blo 1273955 1275819 := bstep (se 1 (by rfl) ⟨956864, by rfl⟩ : syracuseStep 1275819 = 1913729) B1913729
theorem B1275831 : Blo 1273955 1275831 := bstep (se 1 (by rfl) ⟨956873, by rfl⟩ : syracuseStep 1275831 = 1913747) B1913747
theorem B1275851 : Blo 1273955 1275851 := bstep (se 1 (by rfl) ⟨956888, by rfl⟩ : syracuseStep 1275851 = 1913777) B1913777
theorem B1275863 : Blo 1273955 1275863 := bstep (se 1 (by rfl) ⟨956897, by rfl⟩ : syracuseStep 1275863 = 1913795) B1913795
theorem B1275883 : Blo 1273955 1275883 := bstep (se 1 (by rfl) ⟨956912, by rfl⟩ : syracuseStep 1275883 = 1913825) B1913825
theorem B1275895 : Blo 1273955 1275895 := bstep (se 1 (by rfl) ⟨956921, by rfl⟩ : syracuseStep 1275895 = 1913843) B1913843
theorem B1275915 : Blo 1273955 1275915 := bstep (se 1 (by rfl) ⟨956936, by rfl⟩ : syracuseStep 1275915 = 1913873) B1913873
theorem B3061783 : Blo 1273955 3061783 := bstep (se 1 (by rfl) ⟨2296337, by rfl⟩ : syracuseStep 3061783 = 4592675) B4592675
theorem B1275927 : Blo 1273955 1275927 := bstep (se 1 (by rfl) ⟨956945, by rfl⟩ : syracuseStep 1275927 = 1913891) B1913891
theorem B1275947 : Blo 1273955 1275947 := bstep (se 1 (by rfl) ⟨956960, by rfl⟩ : syracuseStep 1275947 = 1913921) B1913921
theorem B1964119 : Blo 1273955 1964119 := bstep (se 1 (by rfl) ⟨1473089, by rfl⟩ : syracuseStep 1964119 = 2946179) B2946179
theorem B1816663 : Blo 1273955 1816663 := bstep (se 1 (by rfl) ⟨1362497, by rfl⟩ : syracuseStep 1816663 = 2724995) B2724995
theorem B7264349 : Blo 1273955 7264349 := bstep (se 3 (by rfl) ⟨1362065, by rfl⟩ : syracuseStep 7264349 = 2724131) B2724131
theorem B6125719 : Blo 1273955 6125719 := bstep (se 1 (by rfl) ⟨4594289, by rfl⟩ : syracuseStep 6125719 = 9188579) B9188579
theorem B9189733 : Blo 1273955 9189733 := bstep (se 4 (by rfl) ⟨861537, by rfl⟩ : syracuseStep 9189733 = 1723075) B1723075
theorem B19896677 : Blo 1273955 19896677 := bstep (se 4 (by rfl) ⟨1865313, by rfl⟩ : syracuseStep 19896677 = 3730627) B3730627
theorem B3226007 : Blo 1273955 3226007 := bstep (se 1 (by rfl) ⟨2419505, by rfl⟩ : syracuseStep 3226007 = 4839011) B4839011
theorem B2152919 : Blo 1273955 2152919 := bstep (se 1 (by rfl) ⟨1614689, by rfl⟩ : syracuseStep 2152919 = 3229379) B3229379
theorem B5446109 : Blo 1273955 5446109 := bstep (se 3 (by rfl) ⟨1021145, by rfl⟩ : syracuseStep 5446109 = 2042291) B2042291
theorem B2153047 : Blo 1273955 2153047 := bstep (se 1 (by rfl) ⟨1614785, by rfl⟩ : syracuseStep 2153047 = 3229571) B3229571
theorem B4840195 : Blo 1273955 4840195 := bstep (se 1 (by rfl) ⟨3630146, by rfl⟩ : syracuseStep 4840195 = 7260293) B7260293
theorem B4660013 : Blo 1273955 4660013 := bstep (se 3 (by rfl) ⟨873752, by rfl⟩ : syracuseStep 4660013 = 1747505) B1747505
theorem B18619253 : Blo 1273955 18619253 := bstep (se 5 (by rfl) ⟨872777, by rfl⟩ : syracuseStep 18619253 = 1745555) B1745555
theorem B44145587 : Blo 1273955 44145587 := bstep (se 1 (by rfl) ⟨33109190, by rfl⟩ : syracuseStep 44145587 = 66218381) B66218381
theorem B1612811 : Blo 1273955 1612811 := bstep (se 1 (by rfl) ⟨1209608, by rfl⟩ : syracuseStep 1612811 = 2419217) B2419217
theorem B4660247 : Blo 1273955 4660247 := bstep (se 1 (by rfl) ⟨3495185, by rfl⟩ : syracuseStep 4660247 = 6990371) B6990371
theorem B3226675 : Blo 1273955 3226675 := bstep (se 1 (by rfl) ⟨2420006, by rfl⟩ : syracuseStep 3226675 = 4840013) B4840013
theorem B4840499 : Blo 1273955 4840499 := bstep (se 1 (by rfl) ⟨3630374, by rfl⟩ : syracuseStep 4840499 = 7260749) B7260749
theorem B3628097 : Blo 1273955 3628097 := bstep (se 2 (by rfl) ⟨1360536, by rfl⟩ : syracuseStep 3628097 = 2721073) B2721073
theorem B1473643 : Blo 1273955 1473643 := bstep (se 1 (by rfl) ⟨1105232, by rfl⟩ : syracuseStep 1473643 = 2210465) B2210465
theorem B6454403 : Blo 1273955 6454403 := bstep (se 1 (by rfl) ⟨4840802, by rfl⟩ : syracuseStep 6454403 = 9681605) B9681605
theorem B3226817 : Blo 1273955 3226817 := bstep (se 2 (by rfl) ⟨1210056, by rfl⟩ : syracuseStep 3226817 = 2420113) B2420113
theorem B14531885 : Blo 1273955 14531885 := bstep (se 3 (by rfl) ⟨2724728, by rfl⟩ : syracuseStep 14531885 = 5449457) B5449457
theorem B3063091 : Blo 1273955 3063091 := bstep (se 1 (by rfl) ⟨2297318, by rfl⟩ : syracuseStep 3063091 = 4594637) B4594637
theorem B2866571 : Blo 1273955 2866571 := bstep (se 1 (by rfl) ⟨2149928, by rfl⟩ : syracuseStep 2866571 = 4299857) B4299857
theorem B3628439 : Blo 1273955 3628439 := bstep (se 1 (by rfl) ⟨2721329, by rfl⟩ : syracuseStep 3628439 = 5442659) B5442659
theorem B2866625 : Blo 1273955 2866625 := bstep (se 2 (by rfl) ⟨1074984, by rfl⟩ : syracuseStep 2866625 = 2149969) B2149969
theorem B4300235 : Blo 1273955 4300235 := bstep (se 1 (by rfl) ⟨3225176, by rfl⟩ : syracuseStep 4300235 = 6450353) B6450353
theorem B9674315 : Blo 1273955 9674315 := bstep (se 1 (by rfl) ⟨7255736, by rfl⟩ : syracuseStep 9674315 = 14511473) B14511473
theorem B1433227 : Blo 1273955 1433227 := bstep (se 1 (by rfl) ⟨1074920, by rfl⟩ : syracuseStep 1433227 = 2149841) B2149841
theorem B2866841 : Blo 1273955 2866841 := bstep (se 2 (by rfl) ⟨1075065, by rfl⟩ : syracuseStep 2866841 = 2150131) B2150131
theorem B4841153 : Blo 1273955 4841153 := bstep (se 2 (by rfl) ⟨1815432, by rfl⟩ : syracuseStep 4841153 = 3630865) B3630865
theorem B58867397 : Blo 1273955 58867397 := bstep (se 4 (by rfl) ⟨5518818, by rfl⟩ : syracuseStep 58867397 = 11037637) B11037637
theorem B1613515 : Blo 1273955 1613515 := bstep (se 1 (by rfl) ⟨1210136, by rfl⟩ : syracuseStep 1613515 = 2420273) B2420273
theorem B4300505 : Blo 1273955 4300505 := bstep (se 2 (by rfl) ⟨1612689, by rfl⟩ : syracuseStep 4300505 = 3225379) B3225379
theorem B2866931 : Blo 1273955 2866931 := bstep (se 1 (by rfl) ⟨2150198, by rfl⟩ : syracuseStep 2866931 = 4300397) B4300397
theorem B1433335 : Blo 1273955 1433335 := bstep (se 1 (by rfl) ⟨1075001, by rfl⟩ : syracuseStep 1433335 = 2150003) B2150003
theorem B8281873 : Blo 1273955 8281873 := bstep (se 2 (by rfl) ⟨3105702, by rfl⟩ : syracuseStep 8281873 = 6211405) B6211405
theorem B2866967 : Blo 1273955 2866967 := bstep (se 1 (by rfl) ⟨2150225, by rfl⟩ : syracuseStep 2866967 = 4300451) B4300451
theorem B1433515 : Blo 1273955 1433515 := bstep (se 1 (by rfl) ⟨1075136, by rfl⟩ : syracuseStep 1433515 = 2150273) B2150273
theorem B2867147 : Blo 1273955 2867147 := bstep (se 1 (by rfl) ⟨2150360, by rfl⟩ : syracuseStep 2867147 = 4300721) B4300721
theorem B1613783 : Blo 1273955 1613783 := bstep (se 1 (by rfl) ⟨1210337, by rfl⟩ : syracuseStep 1613783 = 2420675) B2420675
theorem B7266307 : Blo 1273955 7266307 := bstep (se 1 (by rfl) ⟨5449730, by rfl⟩ : syracuseStep 7266307 = 10899461) B10899461
theorem B1613839 : Blo 1273955 1613839 := bstep (se 1 (by rfl) ⟨1210379, by rfl⟩ : syracuseStep 1613839 = 2420759) B2420759
theorem B4300829 : Blo 1273955 4300829 := bstep (se 3 (by rfl) ⟨806405, by rfl⟩ : syracuseStep 4300829 = 1612811) B1612811
theorem B3629099 : Blo 1273955 3629099 := bstep (se 1 (by rfl) ⟨2721824, by rfl⟩ : syracuseStep 3629099 = 5443649) B5443649
theorem B1433659 : Blo 1273955 1433659 := bstep (se 1 (by rfl) ⟨1075244, by rfl⟩ : syracuseStep 1433659 = 2150489) B2150489
theorem B3448919 : Blo 1273955 3448919 := bstep (se 1 (by rfl) ⟨2586689, by rfl⟩ : syracuseStep 3448919 = 5173379) B5173379
theorem B8167625 : Blo 1273955 8167625 := bstep (se 2 (by rfl) ⟨3062859, by rfl⟩ : syracuseStep 8167625 = 6125719) B6125719
theorem B3678475 : Blo 1273955 3678475 := bstep (se 1 (by rfl) ⟨2758856, by rfl⟩ : syracuseStep 3678475 = 5517713) B5517713
theorem B2867471 : Blo 1273955 2867471 := bstep (se 1 (by rfl) ⟨2150603, by rfl⟩ : syracuseStep 2867471 = 4301207) B4301207
theorem B2867489 : Blo 1273955 2867489 := bstep (se 2 (by rfl) ⟨1075308, by rfl⟩ : syracuseStep 2867489 = 2150617) B2150617
theorem B6455699 : Blo 1273955 6455699 := bstep (se 1 (by rfl) ⟨4841774, by rfl⟩ : syracuseStep 6455699 = 9683549) B9683549
theorem B3064321 : Blo 1273955 3064321 := bstep (se 2 (by rfl) ⟨1149120, by rfl⟩ : syracuseStep 3064321 = 2298241) B2298241
theorem B1434127 : Blo 1273955 1434127 := bstep (se 1 (by rfl) ⟨1075595, by rfl⟩ : syracuseStep 1434127 = 2151191) B2151191
theorem B12247595 : Blo 1273955 12247595 := bstep (se 1 (by rfl) ⟨9185696, by rfl⟩ : syracuseStep 12247595 = 18371393) B18371393
theorem B3228275 : Blo 1273955 3228275 := bstep (se 1 (by rfl) ⟨2421206, by rfl⟩ : syracuseStep 3228275 = 4842413) B4842413
theorem B2867831 : Blo 1273955 2867831 := bstep (se 1 (by rfl) ⟨2150873, by rfl⟩ : syracuseStep 2867831 = 4301747) B4301747
theorem B1360519 : Blo 1273955 1360519 := bstep (se 1 (by rfl) ⟨1020389, by rfl⟩ : syracuseStep 1360519 = 2040779) B2040779
theorem B3228295 : Blo 1273955 3228295 := bstep (se 1 (by rfl) ⟨2421221, by rfl⟩ : syracuseStep 3228295 = 4842443) B4842443
theorem B1614583 : Blo 1273955 1614583 := bstep (se 1 (by rfl) ⟨1210937, by rfl⟩ : syracuseStep 1614583 = 2421875) B2421875
theorem B8274703 : Blo 1273955 8274703 := bstep (se 1 (by rfl) ⟨6206027, by rfl⟩ : syracuseStep 8274703 = 12412055) B12412055
theorem B2868011 : Blo 1273955 2868011 := bstep (se 1 (by rfl) ⟨2151008, by rfl⟩ : syracuseStep 2868011 = 4302017) B4302017
theorem B3228569 : Blo 1273955 3228569 := bstep (se 2 (by rfl) ⟨1210713, by rfl⟩ : syracuseStep 3228569 = 2421427) B2421427
theorem B1434631 : Blo 1273955 1434631 := bstep (se 1 (by rfl) ⟨1075973, by rfl⟩ : syracuseStep 1434631 = 2151947) B2151947
theorem B7357483 : Blo 1273955 7357483 := bstep (se 1 (by rfl) ⟨5518112, by rfl⟩ : syracuseStep 7357483 = 11036225) B11036225
theorem B3228731 : Blo 1273955 3228731 := bstep (se 1 (by rfl) ⟨2421548, by rfl⟩ : syracuseStep 3228731 = 4843097) B4843097
theorem B10888253 : Blo 1273955 10888253 := bstep (se 3 (by rfl) ⟨2041547, by rfl⟩ : syracuseStep 10888253 = 4083095) B4083095
theorem B6890615 : Blo 1273955 6890615 := bstep (se 1 (by rfl) ⟨5167961, by rfl⟩ : syracuseStep 6890615 = 10335923) B10335923
theorem B2868371 : Blo 1273955 2868371 := bstep (se 1 (by rfl) ⟨2151278, by rfl⟩ : syracuseStep 2868371 = 4302557) B4302557
theorem B8717485 : Blo 1273955 8717485 := bstep (se 3 (by rfl) ⟨1634528, by rfl⟩ : syracuseStep 8717485 = 3269057) B3269057
theorem B1434811 : Blo 1273955 1434811 := bstep (se 1 (by rfl) ⟨1076108, by rfl⟩ : syracuseStep 1434811 = 2152217) B2152217
theorem B2868425 : Blo 1273955 2868425 := bstep (se 2 (by rfl) ⟨1075659, by rfl⟩ : syracuseStep 2868425 = 2151319) B2151319
theorem B3228943 : Blo 1273955 3228943 := bstep (se 1 (by rfl) ⟨2421707, by rfl⟩ : syracuseStep 3228943 = 4843415) B4843415
theorem B9192851 : Blo 1273955 9192851 := bstep (se 1 (by rfl) ⟨6894638, by rfl⟩ : syracuseStep 9192851 = 13789277) B13789277
theorem B4842899 : Blo 1273955 4842899 := bstep (se 1 (by rfl) ⟨3632174, by rfl⟩ : syracuseStep 4842899 = 7264349) B7264349
theorem B4302233 : Blo 1273955 4302233 := bstep (se 2 (by rfl) ⟨1613337, by rfl⟩ : syracuseStep 4302233 = 3226675) B3226675
theorem B6211019 : Blo 1273955 6211019 := bstep (se 1 (by rfl) ⟨4658264, by rfl⟩ : syracuseStep 6211019 = 9316529) B9316529
theorem B3229217 : Blo 1273955 3229217 := bstep (se 2 (by rfl) ⟨1210956, by rfl⟩ : syracuseStep 3229217 = 2421913) B2421913
theorem B13264451 : Blo 1273955 13264451 := bstep (se 1 (by rfl) ⟨9948338, by rfl⟩ : syracuseStep 13264451 = 19896677) B19896677
theorem B14526053 : Blo 1273955 14526053 := bstep (se 4 (by rfl) ⟨1361817, by rfl⟩ : syracuseStep 14526053 = 2723635) B2723635
theorem B1435279 : Blo 1273955 1435279 := bstep (se 1 (by rfl) ⟨1076459, by rfl⟩ : syracuseStep 1435279 = 2152919) B2152919
theorem B3630739 : Blo 1273955 3630739 := bstep (se 1 (by rfl) ⟨2723054, by rfl⟩ : syracuseStep 3630739 = 5446109) B5446109
theorem B2721671 : Blo 1273955 2721671 := bstep (se 1 (by rfl) ⟨2041253, by rfl⟩ : syracuseStep 2721671 = 4082507) B4082507
theorem B2869127 : Blo 1273955 2869127 := bstep (se 1 (by rfl) ⟨2151845, by rfl⟩ : syracuseStep 2869127 = 4303691) B4303691
theorem B26150809 : Blo 1273955 26150809 := bstep (se 2 (by rfl) ⟨9806553, by rfl⟩ : syracuseStep 26150809 = 19613107) B19613107
theorem B12412835 : Blo 1273955 12412835 := bstep (se 1 (by rfl) ⟨9309626, by rfl⟩ : syracuseStep 12412835 = 18619253) B18619253
theorem B3106831 : Blo 1273955 3106831 := bstep (se 1 (by rfl) ⟨2330123, by rfl⟩ : syracuseStep 3106831 = 4660247) B4660247
theorem B2418731 : Blo 1273955 2418731 := bstep (se 1 (by rfl) ⟨1814048, by rfl⟩ : syracuseStep 2418731 = 3628097) B3628097
theorem B2869307 : Blo 1273955 2869307 := bstep (se 1 (by rfl) ⟨2151980, by rfl⟩ : syracuseStep 2869307 = 4303961) B4303961
theorem B4302935 : Blo 1273955 4302935 := bstep (se 1 (by rfl) ⟨3227201, by rfl⟩ : syracuseStep 4302935 = 6454403) B6454403
theorem B238749869 : Blo 1273955 238749869 := bstep (se 3 (by rfl) ⟨44765600, by rfl⟩ : syracuseStep 238749869 = 89531201) B89531201
theorem B1910969 : Blo 1273955 1910969 := bstep (se 2 (by rfl) ⟨716613, by rfl⟩ : syracuseStep 1910969 = 1433227) B1433227
theorem B2869433 : Blo 1273955 2869433 := bstep (se 2 (by rfl) ⟨1076037, by rfl⟩ : syracuseStep 2869433 = 2152075) B2152075
theorem B1911047 : Blo 1273955 1911047 := bstep (se 1 (by rfl) ⟨1433285, by rfl⟩ : syracuseStep 1911047 = 2866571) B2866571
theorem B2418959 : Blo 1273955 2418959 := bstep (se 1 (by rfl) ⟨1814219, by rfl⟩ : syracuseStep 2418959 = 3628439) B3628439
theorem B2722081 : Blo 1273955 2722081 := bstep (se 2 (by rfl) ⟨1020780, by rfl⟩ : syracuseStep 2722081 = 2041561) B2041561
theorem B1911083 : Blo 1273955 1911083 := bstep (se 1 (by rfl) ⟨1433312, by rfl⟩ : syracuseStep 1911083 = 2866625) B2866625
theorem B7260475 : Blo 1273955 7260475 := bstep (se 1 (by rfl) ⟨5445356, by rfl⟩ : syracuseStep 7260475 = 10890713) B10890713
theorem B1911113 : Blo 1273955 1911113 := bstep (se 2 (by rfl) ⟨716667, by rfl⟩ : syracuseStep 1911113 = 1433335) B1433335
theorem B6449543 : Blo 1273955 6449543 := bstep (se 1 (by rfl) ⟨4837157, by rfl⟩ : syracuseStep 6449543 = 9674315) B9674315
theorem B1911227 : Blo 1273955 1911227 := bstep (se 1 (by rfl) ⟨1433420, by rfl⟩ : syracuseStep 1911227 = 2866841) B2866841
theorem B1911287 : Blo 1273955 1911287 := bstep (se 1 (by rfl) ⟨1433465, by rfl⟩ : syracuseStep 1911287 = 2866931) B2866931
theorem B1911311 : Blo 1273955 1911311 := bstep (se 1 (by rfl) ⟨1433483, by rfl⟩ : syracuseStep 1911311 = 2866967) B2866967
theorem B2869775 : Blo 1273955 2869775 := bstep (se 1 (by rfl) ⟨2152331, by rfl⟩ : syracuseStep 2869775 = 4304663) B4304663
theorem B2722337 : Blo 1273955 2722337 := bstep (se 2 (by rfl) ⟨1020876, by rfl⟩ : syracuseStep 2722337 = 2041753) B2041753
theorem B2869793 : Blo 1273955 2869793 := bstep (se 2 (by rfl) ⟨1076172, by rfl⟩ : syracuseStep 2869793 = 2152345) B2152345
theorem B1911353 : Blo 1273955 1911353 := bstep (se 2 (by rfl) ⟨716757, by rfl⟩ : syracuseStep 1911353 = 1433515) B1433515
theorem B4303421 : Blo 1273955 4303421 := bstep (se 3 (by rfl) ⟨806891, by rfl⟩ : syracuseStep 4303421 = 1613783) B1613783
theorem B15714917 : Blo 1273955 15714917 := bstep (se 4 (by rfl) ⟨1473273, by rfl⟩ : syracuseStep 15714917 = 2946547) B2946547
theorem B2722423 : Blo 1273955 2722423 := bstep (se 1 (by rfl) ⟨2041817, by rfl⟩ : syracuseStep 2722423 = 4083635) B4083635
theorem B1911431 : Blo 1273955 1911431 := bstep (se 1 (by rfl) ⟨1433573, by rfl⟩ : syracuseStep 1911431 = 2867147) B2867147
theorem B1911467 : Blo 1273955 1911467 := bstep (se 1 (by rfl) ⟨1433600, by rfl⟩ : syracuseStep 1911467 = 2867201) B2867201
theorem B2296505 : Blo 1273955 2296505 := bstep (se 2 (by rfl) ⟨861189, by rfl⟩ : syracuseStep 2296505 = 1722379) B1722379
theorem B1911497 : Blo 1273955 1911497 := bstep (se 2 (by rfl) ⟨716811, by rfl⟩ : syracuseStep 1911497 = 1433623) B1433623
theorem B78523141 : Blo 1273955 78523141 := bstep (se 4 (by rfl) ⟨7361544, by rfl⟩ : syracuseStep 78523141 = 14723089) B14723089
theorem B17443619 : Blo 1273955 17443619 := bstep (se 1 (by rfl) ⟨13082714, by rfl⟩ : syracuseStep 17443619 = 26165429) B26165429
theorem B16329509 : Blo 1273955 16329509 := bstep (se 4 (by rfl) ⟨1530891, by rfl⟩ : syracuseStep 16329509 = 3061783) B3061783
theorem B1911611 : Blo 1273955 1911611 := bstep (se 1 (by rfl) ⟨1433708, by rfl⟩ : syracuseStep 1911611 = 2867417) B2867417
theorem B1911671 : Blo 1273955 1911671 := bstep (se 1 (by rfl) ⟨1433753, by rfl⟩ : syracuseStep 1911671 = 2867507) B2867507
theorem B2870135 : Blo 1273955 2870135 := bstep (se 1 (by rfl) ⟨2152601, by rfl⟩ : syracuseStep 2870135 = 4305203) B4305203
theorem B1911695 : Blo 1273955 1911695 := bstep (se 1 (by rfl) ⟨1433771, by rfl⟩ : syracuseStep 1911695 = 2867543) B2867543
theorem B1911737 : Blo 1273955 1911737 := bstep (se 2 (by rfl) ⟨716901, by rfl⟩ : syracuseStep 1911737 = 1433803) B1433803
theorem B1911815 : Blo 1273955 1911815 := bstep (se 1 (by rfl) ⟨1433861, by rfl⟩ : syracuseStep 1911815 = 2867723) B2867723
theorem B4844555 : Blo 1273955 4844555 := bstep (se 1 (by rfl) ⟨3633416, by rfl⟩ : syracuseStep 4844555 = 7266833) B7266833
theorem B14527511 : Blo 1273955 14527511 := bstep (se 1 (by rfl) ⟨10895633, by rfl⟩ : syracuseStep 14527511 = 21791267) B21791267
theorem B1911851 : Blo 1273955 1911851 := bstep (se 1 (by rfl) ⟨1433888, by rfl⟩ : syracuseStep 1911851 = 2867777) B2867777
theorem B2870315 : Blo 1273955 2870315 := bstep (se 1 (by rfl) ⟨2152736, by rfl⟩ : syracuseStep 2870315 = 4305473) B4305473
theorem B1911881 : Blo 1273955 1911881 := bstep (se 2 (by rfl) ⟨716955, by rfl⟩ : syracuseStep 1911881 = 1433911) B1433911
theorem B1911995 : Blo 1273955 1911995 := bstep (se 1 (by rfl) ⟨1433996, by rfl⟩ : syracuseStep 1911995 = 2867993) B2867993
theorem B7859429 : Blo 1273955 7859429 := bstep (se 4 (by rfl) ⟨736821, by rfl⟩ : syracuseStep 7859429 = 1473643) B1473643
theorem B1912055 : Blo 1273955 1912055 := bstep (se 1 (by rfl) ⟨1434041, by rfl⟩ : syracuseStep 1912055 = 2868083) B2868083
theorem B1912079 : Blo 1273955 1912079 := bstep (se 1 (by rfl) ⟨1434059, by rfl⟩ : syracuseStep 1912079 = 2868119) B2868119
theorem B1912121 : Blo 1273955 1912121 := bstep (se 2 (by rfl) ⟨717045, by rfl⟩ : syracuseStep 1912121 = 1434091) B1434091
theorem B3632471 : Blo 1273955 3632471 := bstep (se 1 (by rfl) ⟨2724353, by rfl⟩ : syracuseStep 3632471 = 5448707) B5448707
theorem B1912199 : Blo 1273955 1912199 := bstep (se 1 (by rfl) ⟨1434149, by rfl⟩ : syracuseStep 1912199 = 2868299) B2868299
theorem B16788871 : Blo 1273955 16788871 := bstep (se 1 (by rfl) ⟨12591653, by rfl⟩ : syracuseStep 16788871 = 25183307) B25183307
theorem B2870675 : Blo 1273955 2870675 := bstep (se 1 (by rfl) ⟨2153006, by rfl⟩ : syracuseStep 2870675 = 4306013) B4306013
theorem B6458777 : Blo 1273955 6458777 := bstep (se 2 (by rfl) ⟨2422041, by rfl⟩ : syracuseStep 6458777 = 4844083) B4844083
theorem B1912235 : Blo 1273955 1912235 := bstep (se 1 (by rfl) ⟨1434176, by rfl⟩ : syracuseStep 1912235 = 2868353) B2868353
theorem B22089145 : Blo 1273955 22089145 := bstep (se 2 (by rfl) ⟨8283429, by rfl⟩ : syracuseStep 22089145 = 16566859) B16566859
theorem B1912265 : Blo 1273955 1912265 := bstep (se 2 (by rfl) ⟨717099, by rfl⟩ : syracuseStep 1912265 = 1434199) B1434199
theorem B2870729 : Blo 1273955 2870729 := bstep (se 2 (by rfl) ⟨1076523, by rfl⟩ : syracuseStep 2870729 = 2153047) B2153047
theorem B27553283 : Blo 1273955 27553283 := bstep (se 1 (by rfl) ⟨20664962, by rfl⟩ : syracuseStep 27553283 = 41329925) B41329925
theorem B14724611 : Blo 1273955 14724611 := bstep (se 1 (by rfl) ⟨11043458, by rfl⟩ : syracuseStep 14724611 = 22086917) B22086917
theorem B1912379 : Blo 1273955 1912379 := bstep (se 1 (by rfl) ⟨1434284, by rfl⟩ : syracuseStep 1912379 = 2868569) B2868569
theorem B1912439 : Blo 1273955 1912439 := bstep (se 1 (by rfl) ⟨1434329, by rfl⟩ : syracuseStep 1912439 = 2868659) B2868659
theorem B2150023 : Blo 1273955 2150023 := bstep (se 1 (by rfl) ⟨1612517, by rfl⟩ : syracuseStep 2150023 = 3225035) B3225035
theorem B1912463 : Blo 1273955 1912463 := bstep (se 1 (by rfl) ⟨1434347, by rfl⟩ : syracuseStep 1912463 = 2868695) B2868695
theorem B2420371 : Blo 1273955 2420371 := bstep (se 1 (by rfl) ⟨1815278, by rfl⟩ : syracuseStep 2420371 = 3630557) B3630557
theorem B1912505 : Blo 1273955 1912505 := bstep (se 2 (by rfl) ⟨717189, by rfl⟩ : syracuseStep 1912505 = 1434379) B1434379
theorem B7261933 : Blo 1273955 7261933 := bstep (se 3 (by rfl) ⟨1361612, by rfl⟩ : syracuseStep 7261933 = 2723225) B2723225
theorem B1912583 : Blo 1273955 1912583 := bstep (se 1 (by rfl) ⟨1434437, by rfl⟩ : syracuseStep 1912583 = 2868875) B2868875
theorem B1838863 : Blo 1273955 1838863 := bstep (se 1 (by rfl) ⟨1379147, by rfl⟩ : syracuseStep 1838863 = 2758295) B2758295
theorem B1912619 : Blo 1273955 1912619 := bstep (se 1 (by rfl) ⟨1434464, by rfl⟩ : syracuseStep 1912619 = 2868929) B2868929
theorem B1912649 : Blo 1273955 1912649 := bstep (se 2 (by rfl) ⟨717243, by rfl⟩ : syracuseStep 1912649 = 1434487) B1434487
theorem B2420599 : Blo 1273955 2420599 := bstep (se 1 (by rfl) ⟨1815449, by rfl⟩ : syracuseStep 2420599 = 3630899) B3630899
theorem B1937287 : Blo 1273955 1937287 := bstep (se 1 (by rfl) ⟨1452965, by rfl⟩ : syracuseStep 1937287 = 2905931) B2905931
theorem B99438515 : Blo 1273955 99438515 := bstep (se 1 (by rfl) ⟨74578886, by rfl⟩ : syracuseStep 99438515 = 149157773) B149157773
theorem B4304825 : Blo 1273955 4304825 := bstep (se 2 (by rfl) ⟨1614309, by rfl⟩ : syracuseStep 4304825 = 3228619) B3228619
theorem B1912763 : Blo 1273955 1912763 := bstep (se 1 (by rfl) ⟨1434572, by rfl⟩ : syracuseStep 1912763 = 2869145) B2869145
theorem B1912823 : Blo 1273955 1912823 := bstep (se 1 (by rfl) ⟨1434617, by rfl⟩ : syracuseStep 1912823 = 2869235) B2869235
theorem B1912847 : Blo 1273955 1912847 := bstep (se 1 (by rfl) ⟨1434635, by rfl⟩ : syracuseStep 1912847 = 2869271) B2869271
theorem B1912889 : Blo 1273955 1912889 := bstep (se 2 (by rfl) ⟨717333, by rfl⟩ : syracuseStep 1912889 = 1434667) B1434667
theorem B1273991 : Blo 1273955 1273991 := bstep (se 1 (by rfl) ⟨955493, by rfl⟩ : syracuseStep 1273991 = 1910987) B1910987
theorem B1912967 : Blo 1273955 1912967 := bstep (se 1 (by rfl) ⟨1434725, by rfl⟩ : syracuseStep 1912967 = 2869451) B2869451
theorem B1273999 : Blo 1273955 1273999 := bstep (se 1 (by rfl) ⟨955499, by rfl⟩ : syracuseStep 1273999 = 1910999) B1910999
theorem B1913003 : Blo 1273955 1913003 := bstep (se 1 (by rfl) ⟨1434752, by rfl⟩ : syracuseStep 1913003 = 2869505) B2869505
theorem B1274043 : Blo 1273955 1274043 := bstep (se 1 (by rfl) ⟨955532, by rfl⟩ : syracuseStep 1274043 = 1911065) B1911065
theorem B6123721 : Blo 1273955 6123721 := bstep (se 2 (by rfl) ⟨2296395, by rfl⟩ : syracuseStep 6123721 = 4592791) B4592791
theorem B26177737 : Blo 1273955 26177737 := bstep (se 2 (by rfl) ⟨9816651, by rfl⟩ : syracuseStep 26177737 = 19633303) B19633303
theorem B1913033 : Blo 1273955 1913033 := bstep (se 2 (by rfl) ⟨717387, by rfl⟩ : syracuseStep 1913033 = 1434775) B1434775
theorem B1274119 : Blo 1273955 1274119 := bstep (se 1 (by rfl) ⟨955589, by rfl⟩ : syracuseStep 1274119 = 1911179) B1911179
theorem B21786893 : Blo 1273955 21786893 := bstep (se 3 (by rfl) ⟨4085042, by rfl⟩ : syracuseStep 21786893 = 8170085) B8170085
theorem B1274127 : Blo 1273955 1274127 := bstep (se 1 (by rfl) ⟨955595, by rfl⟩ : syracuseStep 1274127 = 1911191) B1911191
theorem B2150671 : Blo 1273955 2150671 := bstep (se 1 (by rfl) ⟨1613003, by rfl⟩ : syracuseStep 2150671 = 3226007) B3226007
theorem B3445025 : Blo 1273955 3445025 := bstep (se 2 (by rfl) ⟨1291884, by rfl⟩ : syracuseStep 3445025 = 2583769) B2583769
theorem B1274171 : Blo 1273955 1274171 := bstep (se 1 (by rfl) ⟨955628, by rfl⟩ : syracuseStep 1274171 = 1911257) B1911257
theorem B1913147 : Blo 1273955 1913147 := bstep (se 1 (by rfl) ⟨1434860, by rfl⟩ : syracuseStep 1913147 = 2869721) B2869721
theorem B1913207 : Blo 1273955 1913207 := bstep (se 1 (by rfl) ⟨1434905, by rfl⟩ : syracuseStep 1913207 = 2869811) B2869811
theorem B1274247 : Blo 1273955 1274247 := bstep (se 1 (by rfl) ⟨955685, by rfl⟩ : syracuseStep 1274247 = 1911371) B1911371
theorem B1274255 : Blo 1273955 1274255 := bstep (se 1 (by rfl) ⟨955691, by rfl⟩ : syracuseStep 1274255 = 1911383) B1911383
theorem B1913231 : Blo 1273955 1913231 := bstep (se 1 (by rfl) ⟨1434923, by rfl⟩ : syracuseStep 1913231 = 2869847) B2869847
theorem B4084121 : Blo 1273955 4084121 := bstep (se 2 (by rfl) ⟨1531545, by rfl⟩ : syracuseStep 4084121 = 3063091) B3063091
theorem B1913273 : Blo 1273955 1913273 := bstep (se 2 (by rfl) ⟨717477, by rfl⟩ : syracuseStep 1913273 = 1434955) B1434955
theorem B1274299 : Blo 1273955 1274299 := bstep (se 1 (by rfl) ⟨955724, by rfl⟩ : syracuseStep 1274299 = 1911449) B1911449
theorem B8172035 : Blo 1273955 8172035 := bstep (se 1 (by rfl) ⟨6129026, by rfl⟩ : syracuseStep 8172035 = 12258053) B12258053
theorem B1274375 : Blo 1273955 1274375 := bstep (se 1 (by rfl) ⟨955781, by rfl⟩ : syracuseStep 1274375 = 1911563) B1911563
theorem B1913351 : Blo 1273955 1913351 := bstep (se 1 (by rfl) ⟨1435013, by rfl⟩ : syracuseStep 1913351 = 2870027) B2870027
theorem B4305419 : Blo 1273955 4305419 := bstep (se 1 (by rfl) ⟨3229064, by rfl⟩ : syracuseStep 4305419 = 6458129) B6458129
theorem B1274383 : Blo 1273955 1274383 := bstep (se 1 (by rfl) ⟨955787, by rfl⟩ : syracuseStep 1274383 = 1911575) B1911575
theorem B1913387 : Blo 1273955 1913387 := bstep (se 1 (by rfl) ⟨1435040, by rfl⟩ : syracuseStep 1913387 = 2870081) B2870081
theorem B1274427 : Blo 1273955 1274427 := bstep (se 1 (by rfl) ⟨955820, by rfl⟩ : syracuseStep 1274427 = 1911641) B1911641
theorem B1913417 : Blo 1273955 1913417 := bstep (se 2 (by rfl) ⟨717531, by rfl⟩ : syracuseStep 1913417 = 1435063) B1435063
theorem B29430391 : Blo 1273955 29430391 := bstep (se 1 (by rfl) ⟨22072793, by rfl⟩ : syracuseStep 29430391 = 44145587) B44145587
theorem B4305527 : Blo 1273955 4305527 := bstep (se 1 (by rfl) ⟨3229145, by rfl⟩ : syracuseStep 4305527 = 6458291) B6458291
theorem B1274503 : Blo 1273955 1274503 := bstep (se 1 (by rfl) ⟨955877, by rfl⟩ : syracuseStep 1274503 = 1911755) B1911755
theorem B1274511 : Blo 1273955 1274511 := bstep (se 1 (by rfl) ⟨955883, by rfl⟩ : syracuseStep 1274511 = 1911767) B1911767
theorem B1274555 : Blo 1273955 1274555 := bstep (se 1 (by rfl) ⟨955916, by rfl⟩ : syracuseStep 1274555 = 1911833) B1911833
theorem B1913531 : Blo 1273955 1913531 := bstep (se 1 (by rfl) ⟨1435148, by rfl⟩ : syracuseStep 1913531 = 2870297) B2870297
theorem B5444333 : Blo 1273955 5444333 := bstep (se 3 (by rfl) ⟨1020812, by rfl⟩ : syracuseStep 5444333 = 2041625) B2041625
theorem B1913591 : Blo 1273955 1913591 := bstep (se 1 (by rfl) ⟨1435193, by rfl⟩ : syracuseStep 1913591 = 2870387) B2870387
theorem B3273473 : Blo 1273955 3273473 := bstep (se 2 (by rfl) ⟨1227552, by rfl⟩ : syracuseStep 3273473 = 2455105) B2455105
theorem B1635079 : Blo 1273955 1635079 := bstep (se 1 (by rfl) ⟨1226309, by rfl⟩ : syracuseStep 1635079 = 2452619) B2452619
theorem B1274631 : Blo 1273955 1274631 := bstep (se 1 (by rfl) ⟨955973, by rfl⟩ : syracuseStep 1274631 = 1911947) B1911947
theorem B1274639 : Blo 1273955 1274639 := bstep (se 1 (by rfl) ⟨955979, by rfl⟩ : syracuseStep 1274639 = 1911959) B1911959
theorem B1913615 : Blo 1273955 1913615 := bstep (se 1 (by rfl) ⟨1435211, by rfl⟩ : syracuseStep 1913615 = 2870423) B2870423
theorem B14512931 : Blo 1273955 14512931 := bstep (se 1 (by rfl) ⟨10884698, by rfl⟩ : syracuseStep 14512931 = 21769397) B21769397
theorem B2151211 : Blo 1273955 2151211 := bstep (se 1 (by rfl) ⟨1613408, by rfl⟩ : syracuseStep 2151211 = 3226817) B3226817
theorem B1913657 : Blo 1273955 1913657 := bstep (se 2 (by rfl) ⟨717621, by rfl⟩ : syracuseStep 1913657 = 1435243) B1435243
theorem B1274683 : Blo 1273955 1274683 := bstep (se 1 (by rfl) ⟨956012, by rfl⟩ : syracuseStep 1274683 = 1912025) B1912025
theorem B9687923 : Blo 1273955 9687923 := bstep (se 1 (by rfl) ⟨7265942, by rfl⟩ : syracuseStep 9687923 = 14531885) B14531885
theorem B1274759 : Blo 1273955 1274759 := bstep (se 1 (by rfl) ⟨956069, by rfl⟩ : syracuseStep 1274759 = 1912139) B1912139
theorem B1913735 : Blo 1273955 1913735 := bstep (se 1 (by rfl) ⟨1435301, by rfl⟩ : syracuseStep 1913735 = 2870603) B2870603
theorem B1274767 : Blo 1273955 1274767 := bstep (se 1 (by rfl) ⟨956075, by rfl⟩ : syracuseStep 1274767 = 1912151) B1912151
theorem B16348067 : Blo 1273955 16348067 := bstep (se 1 (by rfl) ⟨12261050, by rfl⟩ : syracuseStep 16348067 = 24522101) B24522101
theorem B1913771 : Blo 1273955 1913771 := bstep (se 1 (by rfl) ⟨1435328, by rfl⟩ : syracuseStep 1913771 = 2870657) B2870657
theorem B2151353 : Blo 1273955 2151353 := bstep (se 2 (by rfl) ⟨806757, by rfl⟩ : syracuseStep 2151353 = 1613515) B1613515
theorem B1274811 : Blo 1273955 1274811 := bstep (se 1 (by rfl) ⟨956108, by rfl⟩ : syracuseStep 1274811 = 1912217) B1912217
theorem B1913801 : Blo 1273955 1913801 := bstep (se 2 (by rfl) ⟨717675, by rfl⟩ : syracuseStep 1913801 = 1435351) B1435351
theorem B1274887 : Blo 1273955 1274887 := bstep (se 1 (by rfl) ⟨956165, by rfl⟩ : syracuseStep 1274887 = 1912331) B1912331
theorem B1274895 : Blo 1273955 1274895 := bstep (se 1 (by rfl) ⟨956171, by rfl⟩ : syracuseStep 1274895 = 1912343) B1912343
theorem B13792301 : Blo 1273955 13792301 := bstep (se 3 (by rfl) ⟨2586056, by rfl⟩ : syracuseStep 13792301 = 5172113) B5172113
theorem B1274939 : Blo 1273955 1274939 := bstep (se 1 (by rfl) ⟨956204, by rfl⟩ : syracuseStep 1274939 = 1912409) B1912409
theorem B1913915 : Blo 1273955 1913915 := bstep (se 1 (by rfl) ⟨1435436, by rfl⟩ : syracuseStep 1913915 = 2870873) B2870873
theorem B2487415 : Blo 1273955 2487415 := bstep (se 1 (by rfl) ⟨1865561, by rfl⟩ : syracuseStep 2487415 = 3731123) B3731123
theorem B39244931 : Blo 1273955 39244931 := bstep (se 1 (by rfl) ⟨29433698, by rfl⟩ : syracuseStep 39244931 = 58867397) B58867397
theorem B3224711 : Blo 1273955 3224711 := bstep (se 1 (by rfl) ⟨2418533, by rfl⟩ : syracuseStep 3224711 = 4837067) B4837067
theorem B1275015 : Blo 1273955 1275015 := bstep (se 1 (by rfl) ⟨956261, by rfl⟩ : syracuseStep 1275015 = 1912523) B1912523
theorem B1275023 : Blo 1273955 1275023 := bstep (se 1 (by rfl) ⟨956267, by rfl⟩ : syracuseStep 1275023 = 1912535) B1912535
theorem B1275067 : Blo 1273955 1275067 := bstep (se 1 (by rfl) ⟨956300, by rfl⟩ : syracuseStep 1275067 = 1912601) B1912601
theorem B4306121 : Blo 1273955 4306121 := bstep (se 2 (by rfl) ⟨1614795, by rfl⟩ : syracuseStep 4306121 = 3229591) B3229591
theorem B1275143 : Blo 1273955 1275143 := bstep (se 1 (by rfl) ⟨956357, by rfl⟩ : syracuseStep 1275143 = 1912715) B1912715
theorem B3224843 : Blo 1273955 3224843 := bstep (se 1 (by rfl) ⟨2418632, by rfl⟩ : syracuseStep 3224843 = 4837265) B4837265
theorem B1275151 : Blo 1273955 1275151 := bstep (se 1 (by rfl) ⟨956363, by rfl⟩ : syracuseStep 1275151 = 1912727) B1912727
theorem B1275195 : Blo 1273955 1275195 := bstep (se 1 (by rfl) ⟨956396, by rfl⟩ : syracuseStep 1275195 = 1912793) B1912793
theorem B1275271 : Blo 1273955 1275271 := bstep (se 1 (by rfl) ⟨956453, by rfl⟩ : syracuseStep 1275271 = 1912907) B1912907
theorem B1275279 : Blo 1273955 1275279 := bstep (se 1 (by rfl) ⟨956459, by rfl⟩ : syracuseStep 1275279 = 1912919) B1912919
theorem B2422163 : Blo 1273955 2422163 := bstep (se 1 (by rfl) ⟨1816622, by rfl⟩ : syracuseStep 2422163 = 3633245) B3633245
theorem B1275323 : Blo 1273955 1275323 := bstep (se 1 (by rfl) ⟨956492, by rfl⟩ : syracuseStep 1275323 = 1912985) B1912985
theorem B2618825 : Blo 1273955 2618825 := bstep (se 2 (by rfl) ⟨982059, by rfl⟩ : syracuseStep 2618825 = 1964119) B1964119
theorem B2422217 : Blo 1273955 2422217 := bstep (se 2 (by rfl) ⟨908331, by rfl⟩ : syracuseStep 2422217 = 1816663) B1816663
theorem B12244445 : Blo 1273955 12244445 := bstep (se 3 (by rfl) ⟨2295833, by rfl⟩ : syracuseStep 12244445 = 4591667) B4591667
theorem B1275399 : Blo 1273955 1275399 := bstep (se 1 (by rfl) ⟨956549, by rfl⟩ : syracuseStep 1275399 = 1913099) B1913099
theorem B1938959 : Blo 1273955 1938959 := bstep (se 1 (by rfl) ⟨1454219, by rfl⟩ : syracuseStep 1938959 = 2908439) B2908439
theorem B1275407 : Blo 1273955 1275407 := bstep (se 1 (by rfl) ⟨956555, by rfl⟩ : syracuseStep 1275407 = 1913111) B1913111
theorem B2422315 : Blo 1273955 2422315 := bstep (se 1 (by rfl) ⟨1816736, by rfl⟩ : syracuseStep 2422315 = 3633473) B3633473
theorem B1275451 : Blo 1273955 1275451 := bstep (se 1 (by rfl) ⟨956588, by rfl⟩ : syracuseStep 1275451 = 1913177) B1913177
theorem B2152055 : Blo 1273955 2152055 := bstep (se 1 (by rfl) ⟨1614041, by rfl⟩ : syracuseStep 2152055 = 3228083) B3228083
theorem B1275527 : Blo 1273955 1275527 := bstep (se 1 (by rfl) ⟨956645, by rfl⟩ : syracuseStep 1275527 = 1913291) B1913291
theorem B1275535 : Blo 1273955 1275535 := bstep (se 1 (by rfl) ⟨956651, by rfl⟩ : syracuseStep 1275535 = 1913303) B1913303
theorem B7263917 : Blo 1273955 7263917 := bstep (se 3 (by rfl) ⟨1361984, by rfl⟩ : syracuseStep 7263917 = 2723969) B2723969
theorem B1275579 : Blo 1273955 1275579 := bstep (se 1 (by rfl) ⟨956684, by rfl⟩ : syracuseStep 1275579 = 1913369) B1913369
theorem B1275655 : Blo 1273955 1275655 := bstep (se 1 (by rfl) ⟨956741, by rfl⟩ : syracuseStep 1275655 = 1913483) B1913483
theorem B3225359 : Blo 1273955 3225359 := bstep (se 1 (by rfl) ⟨2419019, by rfl⟩ : syracuseStep 3225359 = 4838039) B4838039
theorem B1275663 : Blo 1273955 1275663 := bstep (se 1 (by rfl) ⟨956747, by rfl⟩ : syracuseStep 1275663 = 1913495) B1913495
theorem B12252977 : Blo 1273955 12252977 := bstep (se 2 (by rfl) ⟨4594866, by rfl⟩ : syracuseStep 12252977 = 9189733) B9189733
theorem B1275707 : Blo 1273955 1275707 := bstep (se 1 (by rfl) ⟨956780, by rfl⟩ : syracuseStep 1275707 = 1913561) B1913561
theorem B6453107 : Blo 1273955 6453107 := bstep (se 1 (by rfl) ⟨4839830, by rfl⟩ : syracuseStep 6453107 = 9679661) B9679661
theorem B1275783 : Blo 1273955 1275783 := bstep (se 1 (by rfl) ⟨956837, by rfl⟩ : syracuseStep 1275783 = 1913675) B1913675
theorem B1816463 : Blo 1273955 1816463 := bstep (se 1 (by rfl) ⟨1362347, by rfl⟩ : syracuseStep 1816463 = 2724695) B2724695
theorem B1275791 : Blo 1273955 1275791 := bstep (se 1 (by rfl) ⟨956843, by rfl⟩ : syracuseStep 1275791 = 1913687) B1913687
theorem B3225491 : Blo 1273955 3225491 := bstep (se 1 (by rfl) ⟨2419118, by rfl⟩ : syracuseStep 3225491 = 4838237) B4838237
theorem B1275835 : Blo 1273955 1275835 := bstep (se 1 (by rfl) ⟨956876, by rfl⟩ : syracuseStep 1275835 = 1913753) B1913753
theorem B1275911 : Blo 1273955 1275911 := bstep (se 1 (by rfl) ⟨956933, by rfl⟩ : syracuseStep 1275911 = 1913867) B1913867
theorem B1275919 : Blo 1273955 1275919 := bstep (se 1 (by rfl) ⟨956939, by rfl⟩ : syracuseStep 1275919 = 1913879) B1913879
theorem B2152507 : Blo 1273955 2152507 := bstep (se 1 (by rfl) ⟨1614380, by rfl⟩ : syracuseStep 2152507 = 3228761) B3228761
theorem B5445751 : Blo 1273955 5445751 := bstep (se 1 (by rfl) ⟨4084313, by rfl⟩ : syracuseStep 5445751 = 8168627) B8168627
theorem B2209993 : Blo 1273955 2209993 := bstep (se 2 (by rfl) ⟨828747, by rfl⟩ : syracuseStep 2209993 = 1657495) B1657495
theorem B2152649 : Blo 1273955 2152649 := bstep (se 2 (by rfl) ⟨807243, by rfl⟩ : syracuseStep 2152649 = 1614487) B1614487
theorem B4839695 : Blo 1273955 4839695 := bstep (se 1 (by rfl) ⟨3629771, by rfl⟩ : syracuseStep 4839695 = 7259543) B7259543
theorem B6453593 : Blo 1273955 6453593 := bstep (se 2 (by rfl) ⟨2420097, by rfl⟩ : syracuseStep 6453593 = 4840195) B4840195
theorem B14523137 : Blo 1273955 14523137 := bstep (se 2 (by rfl) ⟨5446176, by rfl⟩ : syracuseStep 14523137 = 10892353) B10892353
theorem B3226625 : Blo 1273955 3226625 := bstep (se 2 (by rfl) ⟨1209984, by rfl⟩ : syracuseStep 3226625 = 2419969) B2419969
theorem B24517637 : Blo 1273955 24517637 := bstep (se 4 (by rfl) ⟨2298528, by rfl⟩ : syracuseStep 24517637 = 4597057) B4597057
theorem B31440005 : Blo 1273955 31440005 := bstep (se 4 (by rfl) ⟨2947500, by rfl⟩ : syracuseStep 31440005 = 5895001) B5895001
theorem B3874049 : Blo 1273955 3874049 := bstep (se 2 (by rfl) ⟨1452768, by rfl⟩ : syracuseStep 3874049 = 2905537) B2905537
theorem B7257377 : Blo 1273955 7257377 := bstep (se 2 (by rfl) ⟨2721516, by rfl⟩ : syracuseStep 7257377 = 5443033) B5443033
theorem B8281403 : Blo 1273955 8281403 := bstep (se 1 (by rfl) ⟨6211052, by rfl⟩ : syracuseStep 8281403 = 12422105) B12422105
theorem B3226999 : Blo 1273955 3226999 := bstep (se 1 (by rfl) ⟨2420249, by rfl⟩ : syracuseStep 3226999 = 4840499) B4840499
theorem B1613191 : Blo 1273955 1613191 := bstep (se 1 (by rfl) ⟨1209893, by rfl⟩ : syracuseStep 1613191 = 2419787) B2419787
theorem B12426701 : Blo 1273955 12426701 := bstep (se 3 (by rfl) ⟨2330006, by rfl⟩ : syracuseStep 12426701 = 4660013) B4660013
theorem B17456593 : Blo 1273955 17456593 := bstep (se 2 (by rfl) ⟨6546222, by rfl⟩ : syracuseStep 17456593 = 13092445) B13092445
theorem B2866823 : Blo 1273955 2866823 := bstep (se 1 (by rfl) ⟨2150117, by rfl⟩ : syracuseStep 2866823 = 4300235) B4300235
theorem B11042497 : Blo 1273955 11042497 := bstep (se 2 (by rfl) ⟨4140936, by rfl⟩ : syracuseStep 11042497 = 8281873) B8281873
theorem B23273189 : Blo 1273955 23273189 := bstep (se 4 (by rfl) ⟨2181861, by rfl⟩ : syracuseStep 23273189 = 4363723) B4363723
theorem B4300559 : Blo 1273955 4300559 := bstep (se 1 (by rfl) ⟨3225419, by rfl⟩ : syracuseStep 4300559 = 6450839) B6450839
theorem B1613611 : Blo 1273955 1613611 := bstep (se 1 (by rfl) ⟨1210208, by rfl⟩ : syracuseStep 1613611 = 2420417) B2420417
theorem B3227435 : Blo 1273955 3227435 := bstep (se 1 (by rfl) ⟨2420576, by rfl⟩ : syracuseStep 3227435 = 4841153) B4841153
theorem B2867003 : Blo 1273955 2867003 := bstep (se 1 (by rfl) ⟨2150252, by rfl⟩ : syracuseStep 2867003 = 4300505) B4300505
theorem B1433479 : Blo 1273955 1433479 := bstep (se 1 (by rfl) ⟨1075109, by rfl⟩ : syracuseStep 1433479 = 2150219) B2150219
theorem B2867129 : Blo 1273955 2867129 := bstep (se 2 (by rfl) ⟨1075173, by rfl⟩ : syracuseStep 2867129 = 2150347) B2150347
theorem B2867219 : Blo 1273955 2867219 := bstep (se 1 (by rfl) ⟨2150414, by rfl⟩ : syracuseStep 2867219 = 4300829) B4300829
theorem B14524595 : Blo 1273955 14524595 := bstep (se 1 (by rfl) ⟨10893446, by rfl⟩ : syracuseStep 14524595 = 21786893) B21786893
theorem B5448023 : Blo 1273955 5448023 := bstep (se 1 (by rfl) ⟨4086017, by rfl⟩ : syracuseStep 5448023 = 8172035) B8172035
theorem B2867561 : Blo 1273955 2867561 := bstep (se 2 (by rfl) ⟨1075335, by rfl⟩ : syracuseStep 2867561 = 2150671) B2150671
theorem B3629441 : Blo 1273955 3629441 := bstep (se 2 (by rfl) ⟨1361040, by rfl⟩ : syracuseStep 3629441 = 2722081) B2722081
theorem B3629555 : Blo 1273955 3629555 := bstep (se 1 (by rfl) ⟨2722166, by rfl⟩ : syracuseStep 3629555 = 5444333) B5444333
theorem B9675287 : Blo 1273955 9675287 := bstep (se 1 (by rfl) ⟨7256465, by rfl⟩ : syracuseStep 9675287 = 14512931) B14512931
theorem B1434235 : Blo 1273955 1434235 := bstep (se 1 (by rfl) ⟨1075676, by rfl⟩ : syracuseStep 1434235 = 2151353) B2151353
theorem B7258835 : Blo 1273955 7258835 := bstep (se 1 (by rfl) ⟨5444126, by rfl⟩ : syracuseStep 7258835 = 10888253) B10888253
theorem B39240521 : Blo 1273955 39240521 := bstep (se 2 (by rfl) ⟨14715195, by rfl⟩ : syracuseStep 39240521 = 29430391) B29430391
theorem B3629897 : Blo 1273955 3629897 := bstep (se 2 (by rfl) ⟨1361211, by rfl⟩ : syracuseStep 3629897 = 2722423) B2722423
theorem B6128567 : Blo 1273955 6128567 := bstep (se 1 (by rfl) ⟨4596425, by rfl⟩ : syracuseStep 6128567 = 9192851) B9192851
theorem B3228599 : Blo 1273955 3228599 := bstep (se 1 (by rfl) ⟨2421449, by rfl⟩ : syracuseStep 3228599 = 4842899) B4842899
theorem B2868155 : Blo 1273955 2868155 := bstep (se 1 (by rfl) ⟨2151116, by rfl⟩ : syracuseStep 2868155 = 4302233) B4302233
theorem B1614811 : Blo 1273955 1614811 := bstep (se 1 (by rfl) ⟨1211108, by rfl⟩ : syracuseStep 1614811 = 2422217) B2422217
theorem B2180105 : Blo 1273955 2180105 := bstep (se 2 (by rfl) ⟨817539, by rfl⟩ : syracuseStep 2180105 = 1635079) B1635079
theorem B2868281 : Blo 1273955 2868281 := bstep (se 2 (by rfl) ⟨1075605, by rfl⟩ : syracuseStep 2868281 = 2151211) B2151211
theorem B9684035 : Blo 1273955 9684035 := bstep (se 1 (by rfl) ⟨7263026, by rfl⟩ : syracuseStep 9684035 = 14526053) B14526053
theorem B1434703 : Blo 1273955 1434703 := bstep (se 1 (by rfl) ⟨1076027, by rfl⟩ : syracuseStep 1434703 = 2152055) B2152055
theorem B4842611 : Blo 1273955 4842611 := bstep (se 1 (by rfl) ⟨3631958, by rfl⟩ : syracuseStep 4842611 = 7263917) B7263917
theorem B8168651 : Blo 1273955 8168651 := bstep (se 1 (by rfl) ⟨6126488, by rfl⟩ : syracuseStep 8168651 = 12252977) B12252977
theorem B33137869 : Blo 1273955 33137869 := bstep (se 3 (by rfl) ⟨6213350, by rfl⟩ : syracuseStep 33137869 = 12426701) B12426701
theorem B4302071 : Blo 1273955 4302071 := bstep (se 1 (by rfl) ⟨3226553, by rfl⟩ : syracuseStep 4302071 = 6453107) B6453107
theorem B8275223 : Blo 1273955 8275223 := bstep (se 1 (by rfl) ⟨6206417, by rfl⟩ : syracuseStep 8275223 = 12412835) B12412835
theorem B2868623 : Blo 1273955 2868623 := bstep (se 1 (by rfl) ⟨2151467, by rfl⟩ : syracuseStep 2868623 = 4302935) B4302935
theorem B1435099 : Blo 1273955 1435099 := bstep (se 1 (by rfl) ⟨1076324, by rfl⟩ : syracuseStep 1435099 = 2152649) B2152649
theorem B4302395 : Blo 1273955 4302395 := bstep (se 1 (by rfl) ⟨3226796, by rfl⟩ : syracuseStep 4302395 = 6453593) B6453593
theorem B2868947 : Blo 1273955 2868947 := bstep (se 1 (by rfl) ⟨2151710, by rfl⟩ : syracuseStep 2868947 = 4303421) B4303421
theorem B4302665 : Blo 1273955 4302665 := bstep (se 2 (by rfl) ⟨1613499, by rfl⟩ : syracuseStep 4302665 = 3226999) B3226999
theorem B29452193 : Blo 1273955 29452193 := bstep (se 2 (by rfl) ⟨11044572, by rfl⟩ : syracuseStep 29452193 = 22089145) B22089145
theorem B23275457 : Blo 1273955 23275457 := bstep (se 2 (by rfl) ⟨8728296, by rfl⟩ : syracuseStep 23275457 = 17456593) B17456593
theorem B16345091 : Blo 1273955 16345091 := bstep (se 1 (by rfl) ⟨12258818, by rfl⟩ : syracuseStep 16345091 = 24517637) B24517637
theorem B3229703 : Blo 1273955 3229703 := bstep (se 1 (by rfl) ⟨2422277, by rfl⟩ : syracuseStep 3229703 = 4844555) B4844555
theorem B9685007 : Blo 1273955 9685007 := bstep (se 1 (by rfl) ⟨7263755, by rfl⟩ : syracuseStep 9685007 = 14527511) B14527511
theorem B3229753 : Blo 1273955 3229753 := bstep (se 2 (by rfl) ⟨1211157, by rfl⟩ : syracuseStep 3229753 = 2422315) B2422315
theorem B2582699 : Blo 1273955 2582699 := bstep (se 1 (by rfl) ⟨1937024, by rfl⟩ : syracuseStep 2582699 = 3874049) B3874049
theorem B14723329 : Blo 1273955 14723329 := bstep (se 2 (by rfl) ⟨5521248, by rfl⟩ : syracuseStep 14723329 = 11042497) B11042497
theorem B18368855 : Blo 1273955 18368855 := bstep (se 1 (by rfl) ⟨13776641, by rfl⟩ : syracuseStep 18368855 = 27553283) B27553283
theorem B9816407 : Blo 1273955 9816407 := bstep (se 1 (by rfl) ⟨7362305, by rfl⟩ : syracuseStep 9816407 = 14724611) B14724611
theorem B2451817 : Blo 1273955 2451817 := bstep (se 2 (by rfl) ⟨919431, by rfl⟩ : syracuseStep 2451817 = 1838863) B1838863
theorem B4843901 : Blo 1273955 4843901 := bstep (se 3 (by rfl) ⟨908231, by rfl⟩ : syracuseStep 4843901 = 1816463) B1816463
theorem B1911215 : Blo 1273955 1911215 := bstep (se 1 (by rfl) ⟨1433411, by rfl⟩ : syracuseStep 1911215 = 2866823) B2866823
theorem B2583049 : Blo 1273955 2583049 := bstep (se 2 (by rfl) ⟨968643, by rfl⟩ : syracuseStep 2583049 = 1937287) B1937287
theorem B1911305 : Blo 1273955 1911305 := bstep (se 2 (by rfl) ⟨716739, by rfl⟩ : syracuseStep 1911305 = 1433479) B1433479
theorem B34867745 : Blo 1273955 34867745 := bstep (se 2 (by rfl) ⟨13075404, by rfl⟩ : syracuseStep 34867745 = 26150809) B26150809
theorem B1911335 : Blo 1273955 1911335 := bstep (se 1 (by rfl) ⟨1433501, by rfl⟩ : syracuseStep 1911335 = 2867003) B2867003
theorem B66292343 : Blo 1273955 66292343 := bstep (se 1 (by rfl) ⟨49719257, by rfl⟩ : syracuseStep 66292343 = 99438515) B99438515
theorem B1911419 : Blo 1273955 1911419 := bstep (se 1 (by rfl) ⟨1433564, by rfl⟩ : syracuseStep 1911419 = 2867129) B2867129
theorem B2869883 : Blo 1273955 2869883 := bstep (se 1 (by rfl) ⟨2152412, by rfl⟩ : syracuseStep 2869883 = 4304825) B4304825
theorem B2419399 : Blo 1273955 2419399 := bstep (se 1 (by rfl) ⟨1814549, by rfl⟩ : syracuseStep 2419399 = 3629099) B3629099
theorem B1911545 : Blo 1273955 1911545 := bstep (se 2 (by rfl) ⟨716829, by rfl⟩ : syracuseStep 1911545 = 1433659) B1433659
theorem B2870009 : Blo 1273955 2870009 := bstep (se 2 (by rfl) ⟨1076253, by rfl⟩ : syracuseStep 2870009 = 2152507) B2152507
theorem B7261001 : Blo 1273955 7261001 := bstep (se 2 (by rfl) ⟨2722875, by rfl⟩ : syracuseStep 7261001 = 5445751) B5445751
theorem B1911647 : Blo 1273955 1911647 := bstep (se 1 (by rfl) ⟨1433735, by rfl⟩ : syracuseStep 1911647 = 2867471) B2867471
theorem B1911659 : Blo 1273955 1911659 := bstep (se 1 (by rfl) ⟨1433744, by rfl⟩ : syracuseStep 1911659 = 2867489) B2867489
theorem B4303799 : Blo 1273955 4303799 := bstep (se 1 (by rfl) ⟨3227849, by rfl⟩ : syracuseStep 4303799 = 6455699) B6455699
theorem B2722747 : Blo 1273955 2722747 := bstep (se 1 (by rfl) ⟨2042060, by rfl⟩ : syracuseStep 2722747 = 4084121) B4084121
theorem B2870279 : Blo 1273955 2870279 := bstep (se 1 (by rfl) ⟨2152709, by rfl⟩ : syracuseStep 2870279 = 4305419) B4305419
theorem B1911887 : Blo 1273955 1911887 := bstep (se 1 (by rfl) ⟨1433915, by rfl⟩ : syracuseStep 1911887 = 2867831) B2867831
theorem B2870351 : Blo 1273955 2870351 := bstep (se 1 (by rfl) ⟨2152763, by rfl⟩ : syracuseStep 2870351 = 4305527) B4305527
theorem B2182315 : Blo 1273955 2182315 := bstep (se 1 (by rfl) ⟨1636736, by rfl⟩ : syracuseStep 2182315 = 3273473) B3273473
theorem B1912007 : Blo 1273955 1912007 := bstep (se 1 (by rfl) ⟨1434005, by rfl⟩ : syracuseStep 1912007 = 2868011) B2868011
theorem B6458615 : Blo 1273955 6458615 := bstep (se 1 (by rfl) ⟨4843961, by rfl⟩ : syracuseStep 6458615 = 9687923) B9687923
theorem B10898711 : Blo 1273955 10898711 := bstep (se 1 (by rfl) ⟨8174033, by rfl⟩ : syracuseStep 10898711 = 16348067) B16348067
theorem B1912169 : Blo 1273955 1912169 := bstep (se 2 (by rfl) ⟨717063, by rfl⟩ : syracuseStep 1912169 = 1434127) B1434127
theorem B9194867 : Blo 1273955 9194867 := bstep (se 1 (by rfl) ⟨6896150, by rfl⟩ : syracuseStep 9194867 = 13792301) B13792301
theorem B9186733 : Blo 1273955 9186733 := bstep (se 3 (by rfl) ⟨1722512, by rfl⟩ : syracuseStep 9186733 = 3445025) B3445025
theorem B2149807 : Blo 1273955 2149807 := bstep (se 1 (by rfl) ⟨1612355, by rfl⟩ : syracuseStep 2149807 = 3224711) B3224711
theorem B1912247 : Blo 1273955 1912247 := bstep (se 1 (by rfl) ⟨1434185, by rfl⟩ : syracuseStep 1912247 = 2868371) B2868371
theorem B1912283 : Blo 1273955 1912283 := bstep (se 1 (by rfl) ⟨1434212, by rfl⟩ : syracuseStep 1912283 = 2868425) B2868425
theorem B2870747 : Blo 1273955 2870747 := bstep (se 1 (by rfl) ⟨2153060, by rfl⟩ : syracuseStep 2870747 = 4306121) B4306121
theorem B2149895 : Blo 1273955 2149895 := bstep (se 1 (by rfl) ⟨1612421, by rfl⟩ : syracuseStep 2149895 = 3224843) B3224843
theorem B4304393 : Blo 1273955 4304393 := bstep (se 2 (by rfl) ⟨1614147, by rfl⟩ : syracuseStep 4304393 = 3228295) B3228295
theorem B4140679 : Blo 1273955 4140679 := bstep (se 1 (by rfl) ⟨3105509, by rfl⟩ : syracuseStep 4140679 = 6211019) B6211019
theorem B8162963 : Blo 1273955 8162963 := bstep (se 1 (by rfl) ⟨6122222, by rfl⟩ : syracuseStep 8162963 = 12244445) B12244445
theorem B104697521 : Blo 1273955 104697521 := bstep (se 2 (by rfl) ⟨39261570, by rfl⟩ : syracuseStep 104697521 = 78523141) B78523141
theorem B8842967 : Blo 1273955 8842967 := bstep (se 1 (by rfl) ⟨6632225, by rfl⟩ : syracuseStep 8842967 = 13264451) B13264451
theorem B6459101 : Blo 1273955 6459101 := bstep (se 3 (by rfl) ⟨1211081, by rfl⟩ : syracuseStep 6459101 = 2422163) B2422163
theorem B2150239 : Blo 1273955 2150239 := bstep (se 1 (by rfl) ⟨1612679, by rfl⟩ : syracuseStep 2150239 = 3225359) B3225359
theorem B6983533 : Blo 1273955 6983533 := bstep (se 3 (by rfl) ⟨1309412, by rfl⟩ : syracuseStep 6983533 = 2618825) B2618825
theorem B1814447 : Blo 1273955 1814447 := bstep (se 1 (by rfl) ⟨1360835, by rfl⟩ : syracuseStep 1814447 = 2721671) B2721671
theorem B1912751 : Blo 1273955 1912751 := bstep (se 1 (by rfl) ⟨1434563, by rfl⟩ : syracuseStep 1912751 = 2869127) B2869127
theorem B2150327 : Blo 1273955 2150327 := bstep (se 1 (by rfl) ⟨1612745, by rfl⟩ : syracuseStep 2150327 = 3225491) B3225491
theorem B1912841 : Blo 1273955 1912841 := bstep (se 2 (by rfl) ⟨717315, by rfl⟩ : syracuseStep 1912841 = 1434631) B1434631
theorem B1912871 : Blo 1273955 1912871 := bstep (se 1 (by rfl) ⟨1434653, by rfl⟩ : syracuseStep 1912871 = 2869307) B2869307
theorem B9809977 : Blo 1273955 9809977 := bstep (se 2 (by rfl) ⟨3678741, by rfl⟩ : syracuseStep 9809977 = 7357483) B7357483
theorem B159166579 : Blo 1273955 159166579 := bstep (se 1 (by rfl) ⟨119374934, by rfl⟩ : syracuseStep 159166579 = 238749869) B238749869
theorem B1273979 : Blo 1273955 1273979 := bstep (se 1 (by rfl) ⟨955484, by rfl⟩ : syracuseStep 1273979 = 1910969) B1910969
theorem B1912955 : Blo 1273955 1912955 := bstep (se 1 (by rfl) ⟨1434716, by rfl⟩ : syracuseStep 1912955 = 2869433) B2869433
theorem B1274031 : Blo 1273955 1274031 := bstep (se 1 (by rfl) ⟨955523, by rfl⟩ : syracuseStep 1274031 = 1911047) B1911047
theorem B1274055 : Blo 1273955 1274055 := bstep (se 1 (by rfl) ⟨955541, by rfl⟩ : syracuseStep 1274055 = 1911083) B1911083
theorem B1274075 : Blo 1273955 1274075 := bstep (se 1 (by rfl) ⟨955556, by rfl⟩ : syracuseStep 1274075 = 1911113) B1911113
theorem B1913081 : Blo 1273955 1913081 := bstep (se 2 (by rfl) ⟨717405, by rfl⟩ : syracuseStep 1913081 = 1434811) B1434811
theorem B1274151 : Blo 1273955 1274151 := bstep (se 1 (by rfl) ⟨955613, by rfl⟩ : syracuseStep 1274151 = 1911227) B1911227
theorem B1274191 : Blo 1273955 1274191 := bstep (se 1 (by rfl) ⟨955643, by rfl⟩ : syracuseStep 1274191 = 1911287) B1911287
theorem B1274207 : Blo 1273955 1274207 := bstep (se 1 (by rfl) ⟨955655, by rfl⟩ : syracuseStep 1274207 = 1911311) B1911311
theorem B1913183 : Blo 1273955 1913183 := bstep (se 1 (by rfl) ⟨1434887, by rfl⟩ : syracuseStep 1913183 = 2869775) B2869775
theorem B4305257 : Blo 1273955 4305257 := bstep (se 2 (by rfl) ⟨1614471, by rfl⟩ : syracuseStep 4305257 = 3228943) B3228943
theorem B1814891 : Blo 1273955 1814891 := bstep (se 1 (by rfl) ⟨1361168, by rfl⟩ : syracuseStep 1814891 = 2722337) B2722337
theorem B1913195 : Blo 1273955 1913195 := bstep (se 1 (by rfl) ⟨1434896, by rfl⟩ : syracuseStep 1913195 = 2869793) B2869793
theorem B1274235 : Blo 1273955 1274235 := bstep (se 1 (by rfl) ⟨955676, by rfl⟩ : syracuseStep 1274235 = 1911353) B1911353
theorem B1274287 : Blo 1273955 1274287 := bstep (se 1 (by rfl) ⟨955715, by rfl⟩ : syracuseStep 1274287 = 1911431) B1911431
theorem B1274311 : Blo 1273955 1274311 := bstep (se 1 (by rfl) ⟨955733, by rfl⟩ : syracuseStep 1274311 = 1911467) B1911467
theorem B1274331 : Blo 1273955 1274331 := bstep (se 1 (by rfl) ⟨955748, by rfl⟩ : syracuseStep 1274331 = 1911497) B1911497
theorem B2150921 : Blo 1273955 2150921 := bstep (se 2 (by rfl) ⟨806595, by rfl⟩ : syracuseStep 2150921 = 1613191) B1613191
theorem B22385161 : Blo 1273955 22385161 := bstep (se 2 (by rfl) ⟨8394435, by rfl⟩ : syracuseStep 22385161 = 16788871) B16788871
theorem B11629079 : Blo 1273955 11629079 := bstep (se 1 (by rfl) ⟨8721809, by rfl⟩ : syracuseStep 11629079 = 17443619) B17443619
theorem B1274407 : Blo 1273955 1274407 := bstep (se 1 (by rfl) ⟨955805, by rfl⟩ : syracuseStep 1274407 = 1911611) B1911611
theorem B1274447 : Blo 1273955 1274447 := bstep (se 1 (by rfl) ⟨955835, by rfl⟩ : syracuseStep 1274447 = 1911671) B1911671
theorem B1913423 : Blo 1273955 1913423 := bstep (se 1 (by rfl) ⟨1435067, by rfl⟩ : syracuseStep 1913423 = 2870135) B2870135
theorem B1274463 : Blo 1273955 1274463 := bstep (se 1 (by rfl) ⟨955847, by rfl⟩ : syracuseStep 1274463 = 1911695) B1911695
theorem B1274491 : Blo 1273955 1274491 := bstep (se 1 (by rfl) ⟨955868, by rfl⟩ : syracuseStep 1274491 = 1911737) B1911737
theorem B2151083 : Blo 1273955 2151083 := bstep (se 1 (by rfl) ⟨1613312, by rfl⟩ : syracuseStep 2151083 = 3226625) B3226625
theorem B1274543 : Blo 1273955 1274543 := bstep (se 1 (by rfl) ⟨955907, by rfl⟩ : syracuseStep 1274543 = 1911815) B1911815
theorem B1274567 : Blo 1273955 1274567 := bstep (se 1 (by rfl) ⟨955925, by rfl⟩ : syracuseStep 1274567 = 1911851) B1911851
theorem B1913543 : Blo 1273955 1913543 := bstep (se 1 (by rfl) ⟨1435157, by rfl⟩ : syracuseStep 1913543 = 2870315) B2870315
theorem B1274587 : Blo 1273955 1274587 := bstep (se 1 (by rfl) ⟨955940, by rfl⟩ : syracuseStep 1274587 = 1911881) B1911881
theorem B20960003 : Blo 1273955 20960003 := bstep (se 1 (by rfl) ⟨15720002, by rfl⟩ : syracuseStep 20960003 = 31440005) B31440005
theorem B1274663 : Blo 1273955 1274663 := bstep (se 1 (by rfl) ⟨955997, by rfl⟩ : syracuseStep 1274663 = 1911995) B1911995
theorem B5239619 : Blo 1273955 5239619 := bstep (se 1 (by rfl) ⟨3929714, by rfl⟩ : syracuseStep 5239619 = 7859429) B7859429
theorem B1274703 : Blo 1273955 1274703 := bstep (se 1 (by rfl) ⟨956027, by rfl⟩ : syracuseStep 1274703 = 1912055) B1912055
theorem B1274719 : Blo 1273955 1274719 := bstep (se 1 (by rfl) ⟨956039, by rfl⟩ : syracuseStep 1274719 = 1912079) B1912079
theorem B1913705 : Blo 1273955 1913705 := bstep (se 2 (by rfl) ⟨717639, by rfl⟩ : syracuseStep 1913705 = 1435279) B1435279
theorem B4838251 : Blo 1273955 4838251 := bstep (se 1 (by rfl) ⟨3628688, by rfl⟩ : syracuseStep 4838251 = 7257377) B7257377
theorem B1274747 : Blo 1273955 1274747 := bstep (se 1 (by rfl) ⟨956060, by rfl⟩ : syracuseStep 1274747 = 1912121) B1912121
theorem B2421647 : Blo 1273955 2421647 := bstep (se 1 (by rfl) ⟨1816235, by rfl⟩ : syracuseStep 2421647 = 3632471) B3632471
theorem B1274799 : Blo 1273955 1274799 := bstep (se 1 (by rfl) ⟨956099, by rfl⟩ : syracuseStep 1274799 = 1912199) B1912199
theorem B1913783 : Blo 1273955 1913783 := bstep (se 1 (by rfl) ⟨1435337, by rfl⟩ : syracuseStep 1913783 = 2870675) B2870675
theorem B4305851 : Blo 1273955 4305851 := bstep (se 1 (by rfl) ⟨3229388, by rfl⟩ : syracuseStep 4305851 = 6458777) B6458777
theorem B1274823 : Blo 1273955 1274823 := bstep (se 1 (by rfl) ⟨956117, by rfl⟩ : syracuseStep 1274823 = 1912235) B1912235
theorem B1274843 : Blo 1273955 1274843 := bstep (se 1 (by rfl) ⟨956132, by rfl⟩ : syracuseStep 1274843 = 1912265) B1912265
theorem B1913819 : Blo 1273955 1913819 := bstep (se 1 (by rfl) ⟨1435364, by rfl⟩ : syracuseStep 1913819 = 2870729) B2870729
theorem B1274919 : Blo 1273955 1274919 := bstep (se 1 (by rfl) ⟨956189, by rfl⟩ : syracuseStep 1274919 = 1912379) B1912379
theorem B2151481 : Blo 1273955 2151481 := bstep (se 2 (by rfl) ⟨806805, by rfl⟩ : syracuseStep 2151481 = 1613611) B1613611
theorem B1274959 : Blo 1273955 1274959 := bstep (se 1 (by rfl) ⟨956219, by rfl⟩ : syracuseStep 1274959 = 1912439) B1912439
theorem B1274975 : Blo 1273955 1274975 := bstep (se 1 (by rfl) ⟨956231, by rfl⟩ : syracuseStep 1274975 = 1912463) B1912463
theorem B1275003 : Blo 1273955 1275003 := bstep (se 1 (by rfl) ⟨956252, by rfl⟩ : syracuseStep 1275003 = 1912505) B1912505
theorem B1275055 : Blo 1273955 1275055 := bstep (se 1 (by rfl) ⟨956291, by rfl⟩ : syracuseStep 1275055 = 1912583) B1912583
theorem B2151623 : Blo 1273955 2151623 := bstep (se 1 (by rfl) ⟨1613717, by rfl⟩ : syracuseStep 2151623 = 3227435) B3227435
theorem B1275079 : Blo 1273955 1275079 := bstep (se 1 (by rfl) ⟨956309, by rfl⟩ : syracuseStep 1275079 = 1912619) B1912619
theorem B1275099 : Blo 1273955 1275099 := bstep (se 1 (by rfl) ⟨956324, by rfl⟩ : syracuseStep 1275099 = 1912649) B1912649
theorem B1275175 : Blo 1273955 1275175 := bstep (se 1 (by rfl) ⟨956381, by rfl⟩ : syracuseStep 1275175 = 1912763) B1912763
theorem B1275215 : Blo 1273955 1275215 := bstep (se 1 (by rfl) ⟨956411, by rfl⟩ : syracuseStep 1275215 = 1912823) B1912823
theorem B9688409 : Blo 1273955 9688409 := bstep (se 2 (by rfl) ⟨3633153, by rfl⟩ : syracuseStep 9688409 = 7266307) B7266307
theorem B1275231 : Blo 1273955 1275231 := bstep (se 1 (by rfl) ⟨956423, by rfl⟩ : syracuseStep 1275231 = 1912847) B1912847
theorem B2151785 : Blo 1273955 2151785 := bstep (se 2 (by rfl) ⟨806919, by rfl⟩ : syracuseStep 2151785 = 1613839) B1613839
theorem B4142441 : Blo 1273955 4142441 := bstep (se 2 (by rfl) ⟨1553415, by rfl⟩ : syracuseStep 4142441 = 3106831) B3106831
theorem B1275259 : Blo 1273955 1275259 := bstep (se 1 (by rfl) ⟨956444, by rfl⟩ : syracuseStep 1275259 = 1912889) B1912889
theorem B2299279 : Blo 1273955 2299279 := bstep (se 1 (by rfl) ⟨1724459, by rfl⟩ : syracuseStep 2299279 = 3448919) B3448919
theorem B1275311 : Blo 1273955 1275311 := bstep (se 1 (by rfl) ⟨956483, by rfl⟩ : syracuseStep 1275311 = 1912967) B1912967
theorem B1275335 : Blo 1273955 1275335 := bstep (se 1 (by rfl) ⟨956501, by rfl⟩ : syracuseStep 1275335 = 1913003) B1913003
theorem B5445083 : Blo 1273955 5445083 := bstep (se 1 (by rfl) ⟨4083812, by rfl⟩ : syracuseStep 5445083 = 8167625) B8167625
theorem B1275355 : Blo 1273955 1275355 := bstep (se 1 (by rfl) ⟨956516, by rfl⟩ : syracuseStep 1275355 = 1913033) B1913033
theorem B1275431 : Blo 1273955 1275431 := bstep (se 1 (by rfl) ⟨956573, by rfl⟩ : syracuseStep 1275431 = 1913147) B1913147
theorem B1275471 : Blo 1273955 1275471 := bstep (se 1 (by rfl) ⟨956603, by rfl⟩ : syracuseStep 1275471 = 1913207) B1913207
theorem B1275487 : Blo 1273955 1275487 := bstep (se 1 (by rfl) ⟨956615, by rfl⟩ : syracuseStep 1275487 = 1913231) B1913231
theorem B8164961 : Blo 1273955 8164961 := bstep (se 2 (by rfl) ⟨3061860, by rfl⟩ : syracuseStep 8164961 = 6123721) B6123721
theorem B34903649 : Blo 1273955 34903649 := bstep (se 2 (by rfl) ⟨13088868, by rfl⟩ : syracuseStep 34903649 = 26177737) B26177737
theorem B1275515 : Blo 1273955 1275515 := bstep (se 1 (by rfl) ⟨956636, by rfl⟩ : syracuseStep 1275515 = 1913273) B1913273
theorem B1275567 : Blo 1273955 1275567 := bstep (se 1 (by rfl) ⟨956675, by rfl⟩ : syracuseStep 1275567 = 1913351) B1913351
theorem B4904633 : Blo 1273955 4904633 := bstep (se 2 (by rfl) ⟨1839237, by rfl⟩ : syracuseStep 4904633 = 3678475) B3678475
theorem B8165063 : Blo 1273955 8165063 := bstep (se 1 (by rfl) ⟨6123797, by rfl⟩ : syracuseStep 8165063 = 12247595) B12247595
theorem B1275591 : Blo 1273955 1275591 := bstep (se 1 (by rfl) ⟨956693, by rfl⟩ : syracuseStep 1275591 = 1913387) B1913387
theorem B1275611 : Blo 1273955 1275611 := bstep (se 1 (by rfl) ⟨956708, by rfl⟩ : syracuseStep 1275611 = 1913417) B1913417
theorem B2152183 : Blo 1273955 2152183 := bstep (se 1 (by rfl) ⟨1614137, by rfl⟩ : syracuseStep 2152183 = 3228275) B3228275
theorem B9680633 : Blo 1273955 9680633 := bstep (se 2 (by rfl) ⟨3630237, by rfl⟩ : syracuseStep 9680633 = 7260475) B7260475
theorem B1275687 : Blo 1273955 1275687 := bstep (se 1 (by rfl) ⟨956765, by rfl⟩ : syracuseStep 1275687 = 1913531) B1913531
theorem B1275727 : Blo 1273955 1275727 := bstep (se 1 (by rfl) ⟨956795, by rfl⟩ : syracuseStep 1275727 = 1913591) B1913591
theorem B1275743 : Blo 1273955 1275743 := bstep (se 1 (by rfl) ⟨956807, by rfl⟩ : syracuseStep 1275743 = 1913615) B1913615
theorem B1275771 : Blo 1273955 1275771 := bstep (se 1 (by rfl) ⟨956828, by rfl⟩ : syracuseStep 1275771 = 1913657) B1913657
theorem B1275823 : Blo 1273955 1275823 := bstep (se 1 (by rfl) ⟨956867, by rfl⟩ : syracuseStep 1275823 = 1913735) B1913735
theorem B2152379 : Blo 1273955 2152379 := bstep (se 1 (by rfl) ⟨1614284, by rfl⟩ : syracuseStep 2152379 = 3228569) B3228569
theorem B1275847 : Blo 1273955 1275847 := bstep (se 1 (by rfl) ⟨956885, by rfl⟩ : syracuseStep 1275847 = 1913771) B1913771
theorem B1275867 : Blo 1273955 1275867 := bstep (se 1 (by rfl) ⟨956900, by rfl⟩ : syracuseStep 1275867 = 1913801) B1913801
theorem B4085761 : Blo 1273955 4085761 := bstep (se 2 (by rfl) ⟨1532160, by rfl⟩ : syracuseStep 4085761 = 3064321) B3064321
theorem B7256101 : Blo 1273955 7256101 := bstep (se 4 (by rfl) ⟨680259, by rfl⟩ : syracuseStep 7256101 = 1360519) B1360519
theorem B2152487 : Blo 1273955 2152487 := bstep (se 1 (by rfl) ⟨1614365, by rfl⟩ : syracuseStep 2152487 = 3228731) B3228731
theorem B1275943 : Blo 1273955 1275943 := bstep (se 1 (by rfl) ⟨956957, by rfl⟩ : syracuseStep 1275943 = 1913915) B1913915
theorem B4593743 : Blo 1273955 4593743 := bstep (se 1 (by rfl) ⟨3445307, by rfl⟩ : syracuseStep 4593743 = 6890615) B6890615
theorem B26163287 : Blo 1273955 26163287 := bstep (se 1 (by rfl) ⟨19622465, by rfl⟩ : syracuseStep 26163287 = 39244931) B39244931
theorem B2152777 : Blo 1273955 2152777 := bstep (se 2 (by rfl) ⟨807291, by rfl⟩ : syracuseStep 2152777 = 1614583) B1614583
theorem B1292639 : Blo 1273955 1292639 := bstep (se 1 (by rfl) ⟨969479, by rfl⟩ : syracuseStep 1292639 = 1938959) B1938959
theorem B11032937 : Blo 1273955 11032937 := bstep (se 2 (by rfl) ⟨4137351, by rfl⟩ : syracuseStep 11032937 = 8274703) B8274703
theorem B2152811 : Blo 1273955 2152811 := bstep (se 1 (by rfl) ⟨1614608, by rfl⟩ : syracuseStep 2152811 = 3229217) B3229217
theorem B11786629 : Blo 1273955 11786629 := bstep (se 4 (by rfl) ⟨1104996, by rfl⟩ : syracuseStep 11786629 = 2209993) B2209993
theorem B1612487 : Blo 1273955 1612487 := bstep (se 1 (by rfl) ⟨1209365, by rfl⟩ : syracuseStep 1612487 = 2418731) B2418731
theorem B3316553 : Blo 1273955 3316553 := bstep (se 2 (by rfl) ⟨1243707, by rfl⟩ : syracuseStep 3316553 = 2487415) B2487415
theorem B1612639 : Blo 1273955 1612639 := bstep (se 1 (by rfl) ⟨1209479, by rfl⟩ : syracuseStep 1612639 = 2418959) B2418959
theorem B3226463 : Blo 1273955 3226463 := bstep (se 1 (by rfl) ⟨2419847, by rfl⟩ : syracuseStep 3226463 = 4839695) B4839695
theorem B11623313 : Blo 1273955 11623313 := bstep (se 2 (by rfl) ⟨4358742, by rfl⟩ : syracuseStep 11623313 = 8717485) B8717485
theorem B4299695 : Blo 1273955 4299695 := bstep (se 1 (by rfl) ⟨3224771, by rfl⟩ : syracuseStep 4299695 = 6449543) B6449543
theorem B10476611 : Blo 1273955 10476611 := bstep (se 1 (by rfl) ⟨7857458, by rfl⟩ : syracuseStep 10476611 = 15714917) B15714917
theorem B1531003 : Blo 1273955 1531003 := bstep (se 1 (by rfl) ⟨1148252, by rfl⟩ : syracuseStep 1531003 = 2296505) B2296505
theorem B9682091 : Blo 1273955 9682091 := bstep (se 1 (by rfl) ⟨7261568, by rfl⟩ : syracuseStep 9682091 = 14523137) B14523137
theorem B10886339 : Blo 1273955 10886339 := bstep (se 1 (by rfl) ⟨8164754, by rfl⟩ : syracuseStep 10886339 = 16329509) B16329509
theorem B2866697 : Blo 1273955 2866697 := bstep (se 2 (by rfl) ⟨1075011, by rfl⟩ : syracuseStep 2866697 = 2150023) B2150023
theorem B3227161 : Blo 1273955 3227161 := bstep (se 2 (by rfl) ⟨1210185, by rfl⟩ : syracuseStep 3227161 = 2420371) B2420371
theorem B4840985 : Blo 1273955 4840985 := bstep (se 2 (by rfl) ⟨1815369, by rfl⟩ : syracuseStep 4840985 = 3630739) B3630739
theorem B5520935 : Blo 1273955 5520935 := bstep (se 1 (by rfl) ⟨4140701, by rfl⟩ : syracuseStep 5520935 = 8281403) B8281403
theorem B9682577 : Blo 1273955 9682577 := bstep (se 2 (by rfl) ⟨3630966, by rfl⟩ : syracuseStep 9682577 = 7261933) B7261933
theorem B15515459 : Blo 1273955 15515459 := bstep (se 1 (by rfl) ⟨11636594, by rfl⟩ : syracuseStep 15515459 = 23273189) B23273189
theorem B3227465 : Blo 1273955 3227465 := bstep (se 2 (by rfl) ⟨1210299, by rfl⟩ : syracuseStep 3227465 = 2420599) B2420599
theorem B2867039 : Blo 1273955 2867039 := bstep (se 1 (by rfl) ⟨2150279, by rfl⟩ : syracuseStep 2867039 = 4300559) B4300559
theorem B5447681 : Blo 1273955 5447681 := bstep (se 2 (by rfl) ⟨2042880, by rfl⟩ : syracuseStep 5447681 = 4085761) B4085761
theorem B9674801 : Blo 1273955 9674801 := bstep (se 2 (by rfl) ⟨3628050, by rfl⟩ : syracuseStep 9674801 = 7256101) B7256101
theorem B9683063 : Blo 1273955 9683063 := bstep (se 1 (by rfl) ⟨7262297, by rfl⟩ : syracuseStep 9683063 = 14524595) B14524595
theorem B212222105 : Blo 1273955 212222105 := bstep (se 2 (by rfl) ⟨79583289, by rfl⟩ : syracuseStep 212222105 = 159166579) B159166579
theorem B1433947 : Blo 1273955 1433947 := bstep (se 1 (by rfl) ⟨1075460, by rfl⟩ : syracuseStep 1433947 = 2150921) B2150921
theorem B1434055 : Blo 1273955 1434055 := bstep (se 1 (by rfl) ⟨1075541, by rfl⟩ : syracuseStep 1434055 = 2151083) B2151083
theorem B3269089 : Blo 1273955 3269089 := bstep (se 2 (by rfl) ⟨1225908, by rfl⟩ : syracuseStep 3269089 = 2451817) B2451817
theorem B1614431 : Blo 1273955 1614431 := bstep (se 1 (by rfl) ⟨1210823, by rfl⟩ : syracuseStep 1614431 = 2421647) B2421647
theorem B6456023 : Blo 1273955 6456023 := bstep (se 1 (by rfl) ⟨4842017, by rfl⟩ : syracuseStep 6456023 = 9684035) B9684035
theorem B3228407 : Blo 1273955 3228407 := bstep (se 1 (by rfl) ⟨2421305, by rfl⟩ : syracuseStep 3228407 = 4842611) B4842611
theorem B1434415 : Blo 1273955 1434415 := bstep (se 1 (by rfl) ⟨1075811, by rfl⟩ : syracuseStep 1434415 = 2151623) B2151623
theorem B2868047 : Blo 1273955 2868047 := bstep (se 1 (by rfl) ⟨2151035, by rfl⟩ : syracuseStep 2868047 = 4302071) B4302071
theorem B1434523 : Blo 1273955 1434523 := bstep (se 1 (by rfl) ⟨1075892, by rfl⟩ : syracuseStep 1434523 = 2151785) B2151785
theorem B2761627 : Blo 1273955 2761627 := bstep (se 1 (by rfl) ⟨2071220, by rfl⟩ : syracuseStep 2761627 = 4142441) B4142441
theorem B2868263 : Blo 1273955 2868263 := bstep (se 1 (by rfl) ⟨2151197, by rfl⟩ : syracuseStep 2868263 = 4302395) B4302395
theorem B3269755 : Blo 1273955 3269755 := bstep (se 1 (by rfl) ⟨2452316, by rfl⟩ : syracuseStep 3269755 = 4904633) B4904633
theorem B2868443 : Blo 1273955 2868443 := bstep (se 1 (by rfl) ⟨2151332, by rfl⟩ : syracuseStep 2868443 = 4302665) B4302665
theorem B3630329 : Blo 1273955 3630329 := bstep (se 2 (by rfl) ⟨1361373, by rfl⟩ : syracuseStep 3630329 = 2722747) B2722747
theorem B1434919 : Blo 1273955 1434919 := bstep (se 1 (by rfl) ⟨1076189, by rfl⟩ : syracuseStep 1434919 = 2152379) B2152379
theorem B15516971 : Blo 1273955 15516971 := bstep (se 1 (by rfl) ⟨11637728, by rfl⟩ : syracuseStep 15516971 = 23275457) B23275457
theorem B10896727 : Blo 1273955 10896727 := bstep (se 1 (by rfl) ⟨8172545, by rfl⟩ : syracuseStep 10896727 = 16345091) B16345091
theorem B6456671 : Blo 1273955 6456671 := bstep (se 1 (by rfl) ⟨4842503, by rfl⟩ : syracuseStep 6456671 = 9685007) B9685007
theorem B1434991 : Blo 1273955 1434991 := bstep (se 1 (by rfl) ⟨1076243, by rfl⟩ : syracuseStep 1434991 = 2152487) B2152487
theorem B17442191 : Blo 1273955 17442191 := bstep (se 1 (by rfl) ⟨13081643, by rfl⟩ : syracuseStep 17442191 = 26163287) B26163287
theorem B2868641 : Blo 1273955 2868641 := bstep (se 2 (by rfl) ⟨1075740, by rfl⟩ : syracuseStep 2868641 = 2151481) B2151481
theorem B2041337 : Blo 1273955 2041337 := bstep (se 2 (by rfl) ⟨765501, by rfl⟩ : syracuseStep 2041337 = 1531003) B1531003
theorem B2909753 : Blo 1273955 2909753 := bstep (se 2 (by rfl) ⟨1091157, by rfl⟩ : syracuseStep 2909753 = 2182315) B2182315
theorem B1435207 : Blo 1273955 1435207 := bstep (se 1 (by rfl) ⟨1076405, by rfl⟩ : syracuseStep 1435207 = 2152811) B2152811
theorem B3229267 : Blo 1273955 3229267 := bstep (se 1 (by rfl) ⟨2421950, by rfl⟩ : syracuseStep 3229267 = 4843901) B4843901
theorem B3065705 : Blo 1273955 3065705 := bstep (se 2 (by rfl) ⟨1149639, by rfl⟩ : syracuseStep 3065705 = 2299279) B2299279
theorem B12248977 : Blo 1273955 12248977 := bstep (se 2 (by rfl) ⟨4593366, by rfl⟩ : syracuseStep 12248977 = 9186733) B9186733
theorem B2869199 : Blo 1273955 2869199 := bstep (se 1 (by rfl) ⟨2151899, by rfl⟩ : syracuseStep 2869199 = 4303799) B4303799
theorem B4302881 : Blo 1273955 4302881 := bstep (se 2 (by rfl) ⟨1613580, by rfl⟩ : syracuseStep 4302881 = 3227161) B3227161
theorem B6129911 : Blo 1273955 6129911 := bstep (se 1 (by rfl) ⟨4597433, by rfl⟩ : syracuseStep 6129911 = 9194867) B9194867
theorem B2869577 : Blo 1273955 2869577 := bstep (se 2 (by rfl) ⟨1076091, by rfl⟩ : syracuseStep 2869577 = 2152183) B2152183
theorem B1911131 : Blo 1273955 1911131 := bstep (se 1 (by rfl) ⟨1433348, by rfl⟩ : syracuseStep 1911131 = 2866697) B2866697
theorem B2869595 : Blo 1273955 2869595 := bstep (se 1 (by rfl) ⟨2152196, by rfl⟩ : syracuseStep 2869595 = 4304393) B4304393
theorem B3680623 : Blo 1273955 3680623 := bstep (se 1 (by rfl) ⟨2760467, by rfl⟩ : syracuseStep 3680623 = 5520935) B5520935
theorem B5441975 : Blo 1273955 5441975 := bstep (se 1 (by rfl) ⟨4081481, by rfl⟩ : syracuseStep 5441975 = 8162963) B8162963
theorem B69798347 : Blo 1273955 69798347 := bstep (se 1 (by rfl) ⟨52348760, by rfl⟩ : syracuseStep 69798347 = 104697521) B104697521
theorem B1911359 : Blo 1273955 1911359 := bstep (se 1 (by rfl) ⟨1433519, by rfl⟩ : syracuseStep 1911359 = 2867039) B2867039
theorem B1911479 : Blo 1273955 1911479 := bstep (se 1 (by rfl) ⟨1433609, by rfl⟩ : syracuseStep 1911479 = 2867219) B2867219
theorem B3632015 : Blo 1273955 3632015 := bstep (se 1 (by rfl) ⟨2724011, by rfl⟩ : syracuseStep 3632015 = 5448023) B5448023
theorem B1911707 : Blo 1273955 1911707 := bstep (se 1 (by rfl) ⟨1433780, by rfl⟩ : syracuseStep 1911707 = 2867561) B2867561
theorem B2870171 : Blo 1273955 2870171 := bstep (se 1 (by rfl) ⟨2152628, by rfl⟩ : syracuseStep 2870171 = 4305257) B4305257
theorem B2419627 : Blo 1273955 2419627 := bstep (se 1 (by rfl) ⟨1814720, by rfl⟩ : syracuseStep 2419627 = 3629441) B3629441
theorem B2419703 : Blo 1273955 2419703 := bstep (se 1 (by rfl) ⟨1814777, by rfl⟩ : syracuseStep 2419703 = 3629555) B3629555
theorem B19631105 : Blo 1273955 19631105 := bstep (se 2 (by rfl) ⟨7361664, by rfl⟩ : syracuseStep 19631105 = 14723329) B14723329
theorem B6450191 : Blo 1273955 6450191 := bstep (se 1 (by rfl) ⟨4837643, by rfl⟩ : syracuseStep 6450191 = 9675287) B9675287
theorem B7752719 : Blo 1273955 7752719 := bstep (se 1 (by rfl) ⟨5814539, by rfl⟩ : syracuseStep 7752719 = 11629079) B11629079
theorem B2870369 : Blo 1273955 2870369 := bstep (se 2 (by rfl) ⟨1076388, by rfl⟩ : syracuseStep 2870369 = 2152777) B2152777
theorem B15715505 : Blo 1273955 15715505 := bstep (se 2 (by rfl) ⟨5893314, by rfl⟩ : syracuseStep 15715505 = 11786629) B11786629
theorem B3493079 : Blo 1273955 3493079 := bstep (se 1 (by rfl) ⟨2619809, by rfl⟩ : syracuseStep 3493079 = 5239619) B5239619
theorem B26160347 : Blo 1273955 26160347 := bstep (se 1 (by rfl) ⟨19620260, by rfl⟩ : syracuseStep 26160347 = 39240521) B39240521
theorem B2419931 : Blo 1273955 2419931 := bstep (se 1 (by rfl) ⟨1814948, by rfl⟩ : syracuseStep 2419931 = 3629897) B3629897
theorem B1912103 : Blo 1273955 1912103 := bstep (se 1 (by rfl) ⟨1434077, by rfl⟩ : syracuseStep 1912103 = 2868155) B2868155
theorem B2870567 : Blo 1273955 2870567 := bstep (se 1 (by rfl) ⟨2152925, by rfl⟩ : syracuseStep 2870567 = 4305851) B4305851
theorem B1453403 : Blo 1273955 1453403 := bstep (se 1 (by rfl) ⟨1090052, by rfl⟩ : syracuseStep 1453403 = 2180105) B2180105
theorem B3444065 : Blo 1273955 3444065 := bstep (se 2 (by rfl) ⟨1291524, by rfl⟩ : syracuseStep 3444065 = 2583049) B2583049
theorem B1912187 : Blo 1273955 1912187 := bstep (se 1 (by rfl) ⟨1434140, by rfl⟩ : syracuseStep 1912187 = 2868281) B2868281
theorem B1912313 : Blo 1273955 1912313 := bstep (se 2 (by rfl) ⟨717117, by rfl⟩ : syracuseStep 1912313 = 1434235) B1434235
theorem B5516815 : Blo 1273955 5516815 := bstep (se 1 (by rfl) ⟨4137611, by rfl⟩ : syracuseStep 5516815 = 8275223) B8275223
theorem B6458939 : Blo 1273955 6458939 := bstep (se 1 (by rfl) ⟨4844204, by rfl⟩ : syracuseStep 6458939 = 9688409) B9688409
theorem B1912415 : Blo 1273955 1912415 := bstep (se 1 (by rfl) ⟨1434311, by rfl⟩ : syracuseStep 1912415 = 2868623) B2868623
theorem B5443307 : Blo 1273955 5443307 := bstep (se 1 (by rfl) ⟨4082480, by rfl⟩ : syracuseStep 5443307 = 8164961) B8164961
theorem B2150185 : Blo 1273955 2150185 := bstep (se 2 (by rfl) ⟨806319, by rfl⟩ : syracuseStep 2150185 = 1612639) B1612639
theorem B5443375 : Blo 1273955 5443375 := bstep (se 1 (by rfl) ⟨4082531, by rfl⟩ : syracuseStep 5443375 = 8165063) B8165063
theorem B6451001 : Blo 1273955 6451001 := bstep (se 2 (by rfl) ⟨2419125, by rfl⟩ : syracuseStep 6451001 = 4838251) B4838251
theorem B1912631 : Blo 1273955 1912631 := bstep (se 1 (by rfl) ⟨1434473, by rfl⟩ : syracuseStep 1912631 = 2868947) B2868947
theorem B14520221 : Blo 1273955 14520221 := bstep (se 3 (by rfl) ⟨2722541, by rfl⟩ : syracuseStep 14520221 = 5445083) B5445083
theorem B1912937 : Blo 1273955 1912937 := bstep (se 2 (by rfl) ⟨717351, by rfl⟩ : syracuseStep 1912937 = 1434703) B1434703
theorem B44183825 : Blo 1273955 44183825 := bstep (se 2 (by rfl) ⟨16568934, by rfl⟩ : syracuseStep 44183825 = 33137869) B33137869
theorem B1274143 : Blo 1273955 1274143 := bstep (se 1 (by rfl) ⟨955607, by rfl⟩ : syracuseStep 1274143 = 1911215) B1911215
theorem B1274203 : Blo 1273955 1274203 := bstep (se 1 (by rfl) ⟨955652, by rfl⟩ : syracuseStep 1274203 = 1911305) B1911305
theorem B23245163 : Blo 1273955 23245163 := bstep (se 1 (by rfl) ⟨17433872, by rfl⟩ : syracuseStep 23245163 = 34867745) B34867745
theorem B1274223 : Blo 1273955 1274223 := bstep (se 1 (by rfl) ⟨955667, by rfl⟩ : syracuseStep 1274223 = 1911335) B1911335
theorem B1274279 : Blo 1273955 1274279 := bstep (se 1 (by rfl) ⟨955709, by rfl⟩ : syracuseStep 1274279 = 1911419) B1911419
theorem B1913255 : Blo 1273955 1913255 := bstep (se 1 (by rfl) ⟨1434941, by rfl⟩ : syracuseStep 1913255 = 2869883) B2869883
theorem B1274363 : Blo 1273955 1274363 := bstep (se 1 (by rfl) ⟨955772, by rfl⟩ : syracuseStep 1274363 = 1911545) B1911545
theorem B1913339 : Blo 1273955 1913339 := bstep (se 1 (by rfl) ⟨1435004, by rfl⟩ : syracuseStep 1913339 = 2870009) B2870009
theorem B1274431 : Blo 1273955 1274431 := bstep (se 1 (by rfl) ⟨955823, by rfl⟩ : syracuseStep 1274431 = 1911647) B1911647
theorem B2150975 : Blo 1273955 2150975 := bstep (se 1 (by rfl) ⟨1613231, by rfl⟩ : syracuseStep 2150975 = 3226463) B3226463
theorem B1274439 : Blo 1273955 1274439 := bstep (se 1 (by rfl) ⟨955829, by rfl⟩ : syracuseStep 1274439 = 1911659) B1911659
theorem B1913465 : Blo 1273955 1913465 := bstep (se 2 (by rfl) ⟨717549, by rfl⟩ : syracuseStep 1913465 = 1435099) B1435099
theorem B1913519 : Blo 1273955 1913519 := bstep (se 1 (by rfl) ⟨1435139, by rfl⟩ : syracuseStep 1913519 = 2870279) B2870279
theorem B6984407 : Blo 1273955 6984407 := bstep (se 1 (by rfl) ⟨5238305, by rfl⟩ : syracuseStep 6984407 = 10476611) B10476611
theorem B1274591 : Blo 1273955 1274591 := bstep (se 1 (by rfl) ⟨955943, by rfl⟩ : syracuseStep 1274591 = 1911887) B1911887
theorem B1913567 : Blo 1273955 1913567 := bstep (se 1 (by rfl) ⟨1435175, by rfl⟩ : syracuseStep 1913567 = 2870351) B2870351
theorem B1274671 : Blo 1273955 1274671 := bstep (se 1 (by rfl) ⟨956003, by rfl⟩ : syracuseStep 1274671 = 1912007) B1912007
theorem B4305743 : Blo 1273955 4305743 := bstep (se 1 (by rfl) ⟨3229307, by rfl⟩ : syracuseStep 4305743 = 6458615) B6458615
theorem B1274779 : Blo 1273955 1274779 := bstep (se 1 (by rfl) ⟨956084, by rfl⟩ : syracuseStep 1274779 = 1912169) B1912169
theorem B1274831 : Blo 1273955 1274831 := bstep (se 1 (by rfl) ⟨956123, by rfl⟩ : syracuseStep 1274831 = 1912247) B1912247
theorem B1274855 : Blo 1273955 1274855 := bstep (se 1 (by rfl) ⟨956141, by rfl⟩ : syracuseStep 1274855 = 1912283) B1912283
theorem B1913831 : Blo 1273955 1913831 := bstep (se 1 (by rfl) ⟨1435373, by rfl⟩ : syracuseStep 1913831 = 2870747) B2870747
theorem B4838525 : Blo 1273955 4838525 := bstep (se 3 (by rfl) ⟨907223, by rfl⟩ : syracuseStep 4838525 = 1814447) B1814447
theorem B5895311 : Blo 1273955 5895311 := bstep (se 1 (by rfl) ⟨4421483, by rfl⟩ : syracuseStep 5895311 = 8842967) B8842967
theorem B9311377 : Blo 1273955 9311377 := bstep (se 2 (by rfl) ⟨3491766, by rfl⟩ : syracuseStep 9311377 = 6983533) B6983533
theorem B4306067 : Blo 1273955 4306067 := bstep (se 1 (by rfl) ⟨3229550, by rfl⟩ : syracuseStep 4306067 = 6459101) B6459101
theorem B10343639 : Blo 1273955 10343639 := bstep (se 1 (by rfl) ⟨7757729, by rfl⟩ : syracuseStep 10343639 = 15515459) B15515459
theorem B2151643 : Blo 1273955 2151643 := bstep (se 1 (by rfl) ⟨1613732, by rfl⟩ : syracuseStep 2151643 = 3227465) B3227465
theorem B1275167 : Blo 1273955 1275167 := bstep (se 1 (by rfl) ⟨956375, by rfl⟩ : syracuseStep 1275167 = 1912751) B1912751
theorem B1275227 : Blo 1273955 1275227 := bstep (se 1 (by rfl) ⟨956420, by rfl⟩ : syracuseStep 1275227 = 1912841) B1912841
theorem B1275247 : Blo 1273955 1275247 := bstep (se 1 (by rfl) ⟨956435, by rfl⟩ : syracuseStep 1275247 = 1912871) B1912871
theorem B119387525 : Blo 1273955 119387525 := bstep (se 4 (by rfl) ⟨11192580, by rfl⟩ : syracuseStep 119387525 = 22385161) B22385161
theorem B13079969 : Blo 1273955 13079969 := bstep (se 2 (by rfl) ⟨4904988, by rfl⟩ : syracuseStep 13079969 = 9809977) B9809977
theorem B4306337 : Blo 1273955 4306337 := bstep (se 2 (by rfl) ⟨1614876, by rfl⟩ : syracuseStep 4306337 = 3229753) B3229753
theorem B1275303 : Blo 1273955 1275303 := bstep (se 1 (by rfl) ⟨956477, by rfl⟩ : syracuseStep 1275303 = 1912955) B1912955
theorem B1275387 : Blo 1273955 1275387 := bstep (se 1 (by rfl) ⟨956540, by rfl⟩ : syracuseStep 1275387 = 1913081) B1913081
theorem B1275455 : Blo 1273955 1275455 := bstep (se 1 (by rfl) ⟨956591, by rfl⟩ : syracuseStep 1275455 = 1913183) B1913183
theorem B1275463 : Blo 1273955 1275463 := bstep (se 1 (by rfl) ⟨956597, by rfl⟩ : syracuseStep 1275463 = 1913195) B1913195
theorem B1275615 : Blo 1273955 1275615 := bstep (se 1 (by rfl) ⟨956711, by rfl⟩ : syracuseStep 1275615 = 1913423) B1913423
theorem B6887197 : Blo 1273955 6887197 := bstep (se 3 (by rfl) ⟨1291349, by rfl⟩ : syracuseStep 6887197 = 2582699) B2582699
theorem B1275695 : Blo 1273955 1275695 := bstep (se 1 (by rfl) ⟨956771, by rfl⟩ : syracuseStep 1275695 = 1913543) B1913543
theorem B4839223 : Blo 1273955 4839223 := bstep (se 1 (by rfl) ⟨3629417, by rfl⟩ : syracuseStep 4839223 = 7258835) B7258835
theorem B1275803 : Blo 1273955 1275803 := bstep (se 1 (by rfl) ⟨956852, by rfl⟩ : syracuseStep 1275803 = 1913705) B1913705
theorem B4085711 : Blo 1273955 4085711 := bstep (se 1 (by rfl) ⟨3064283, by rfl⟩ : syracuseStep 4085711 = 6128567) B6128567
theorem B2152399 : Blo 1273955 2152399 := bstep (se 1 (by rfl) ⟨1614299, by rfl⟩ : syracuseStep 2152399 = 3228599) B3228599
theorem B1275855 : Blo 1273955 1275855 := bstep (se 1 (by rfl) ⟨956891, by rfl⟩ : syracuseStep 1275855 = 1913783) B1913783
theorem B1275879 : Blo 1273955 1275879 := bstep (se 1 (by rfl) ⟨956909, by rfl⟩ : syracuseStep 1275879 = 1913819) B1913819
theorem B5445767 : Blo 1273955 5445767 := bstep (se 1 (by rfl) ⟨4084325, by rfl⟩ : syracuseStep 5445767 = 8168651) B8168651
theorem B3447037 : Blo 1273955 3447037 := bstep (se 3 (by rfl) ⟨646319, by rfl⟩ : syracuseStep 3447037 = 1292639) B1292639
theorem B3225865 : Blo 1273955 3225865 := bstep (se 2 (by rfl) ⟨1209699, by rfl⟩ : syracuseStep 3225865 = 2419399) B2419399
theorem B4839709 : Blo 1273955 4839709 := bstep (se 3 (by rfl) ⟨907445, by rfl⟩ : syracuseStep 4839709 = 1814891) B1814891
theorem B6453755 : Blo 1273955 6453755 := bstep (se 1 (by rfl) ⟨4840316, by rfl⟩ : syracuseStep 6453755 = 9680633) B9680633
theorem B19634795 : Blo 1273955 19634795 := bstep (se 1 (by rfl) ⟨14726096, by rfl⟩ : syracuseStep 19634795 = 29452193) B29452193
theorem B2153081 : Blo 1273955 2153081 := bstep (se 2 (by rfl) ⟨807405, by rfl⟩ : syracuseStep 2153081 = 1614811) B1614811
theorem B2153135 : Blo 1273955 2153135 := bstep (se 1 (by rfl) ⟨1614851, by rfl⟩ : syracuseStep 2153135 = 3229703) B3229703
theorem B3062495 : Blo 1273955 3062495 := bstep (se 1 (by rfl) ⟨2296871, by rfl⟩ : syracuseStep 3062495 = 4593743) B4593743
theorem B12245903 : Blo 1273955 12245903 := bstep (se 1 (by rfl) ⟨9184427, by rfl⟩ : syracuseStep 12245903 = 18368855) B18368855
theorem B6544271 : Blo 1273955 6544271 := bstep (se 1 (by rfl) ⟨4908203, by rfl⟩ : syracuseStep 6544271 = 9816407) B9816407
theorem B7355291 : Blo 1273955 7355291 := bstep (se 1 (by rfl) ⟨5516468, by rfl⟩ : syracuseStep 7355291 = 11032937) B11032937
theorem B93076397 : Blo 1273955 93076397 := bstep (se 3 (by rfl) ⟨17451824, by rfl⟩ : syracuseStep 93076397 = 34903649) B34903649
theorem B44194895 : Blo 1273955 44194895 := bstep (se 1 (by rfl) ⟨33146171, by rfl⟩ : syracuseStep 44194895 = 66292343) B66292343
theorem B4299965 : Blo 1273955 4299965 := bstep (se 3 (by rfl) ⟨806243, by rfl⟩ : syracuseStep 4299965 = 1612487) B1612487
theorem B4840667 : Blo 1273955 4840667 := bstep (se 1 (by rfl) ⟨3630500, by rfl⟩ : syracuseStep 4840667 = 7261001) B7261001
theorem B2211035 : Blo 1273955 2211035 := bstep (se 1 (by rfl) ⟨1658276, by rfl⟩ : syracuseStep 2211035 = 3316553) B3316553
theorem B2866409 : Blo 1273955 2866409 := bstep (se 2 (by rfl) ⟨1074903, by rfl⟩ : syracuseStep 2866409 = 2149807) B2149807
theorem B7748875 : Blo 1273955 7748875 := bstep (se 1 (by rfl) ⟨5811656, by rfl⟩ : syracuseStep 7748875 = 11623313) B11623313
theorem B2866463 : Blo 1273955 2866463 := bstep (se 1 (by rfl) ⟨2149847, by rfl⟩ : syracuseStep 2866463 = 4299695) B4299695
theorem B55893341 : Blo 1273955 55893341 := bstep (se 3 (by rfl) ⟨10480001, by rfl⟩ : syracuseStep 55893341 = 20960003) B20960003
theorem B6454727 : Blo 1273955 6454727 := bstep (se 1 (by rfl) ⟨4841045, by rfl⟩ : syracuseStep 6454727 = 9682091) B9682091
theorem B7257559 : Blo 1273955 7257559 := bstep (se 1 (by rfl) ⟨5443169, by rfl⟩ : syracuseStep 7257559 = 10886339) B10886339
theorem B5520905 : Blo 1273955 5520905 := bstep (se 2 (by rfl) ⟨2070339, by rfl⟩ : syracuseStep 5520905 = 4140679) B4140679
theorem B7265807 : Blo 1273955 7265807 := bstep (se 1 (by rfl) ⟨5449355, by rfl⟩ : syracuseStep 7265807 = 10898711) B10898711
theorem B1433263 : Blo 1273955 1433263 := bstep (se 1 (by rfl) ⟨1074947, by rfl⟩ : syracuseStep 1433263 = 2149895) B2149895
theorem B3227323 : Blo 1273955 3227323 := bstep (se 1 (by rfl) ⟨2420492, by rfl⟩ : syracuseStep 3227323 = 4840985) B4840985
theorem B6455051 : Blo 1273955 6455051 := bstep (se 1 (by rfl) ⟨4841288, by rfl⟩ : syracuseStep 6455051 = 9682577) B9682577
theorem B2866985 : Blo 1273955 2866985 := bstep (se 2 (by rfl) ⟨1075119, by rfl⟩ : syracuseStep 2866985 = 2150239) B2150239
theorem B1433551 : Blo 1273955 1433551 := bstep (se 1 (by rfl) ⟨1075163, by rfl⟩ : syracuseStep 1433551 = 2150327) B2150327
theorem B6455375 : Blo 1273955 6455375 := bstep (se 1 (by rfl) ⟨4841531, by rfl⟩ : syracuseStep 6455375 = 9683063) B9683063
theorem B4596049 : Blo 1273955 4596049 := bstep (se 2 (by rfl) ⟨1723518, by rfl⟩ : syracuseStep 4596049 = 3447037) B3447037
theorem B4301153 : Blo 1273955 4301153 := bstep (se 2 (by rfl) ⟨1612932, by rfl⟩ : syracuseStep 4301153 = 3225865) B3225865
theorem B1433983 : Blo 1273955 1433983 := bstep (se 1 (by rfl) ⟨1075487, by rfl⟩ : syracuseStep 1433983 = 2150975) B2150975
theorem B27583037 : Blo 1273955 27583037 := bstep (se 3 (by rfl) ⟨5171819, by rfl⟩ : syracuseStep 27583037 = 10343639) B10343639
theorem B3875741 : Blo 1273955 3875741 := bstep (se 3 (by rfl) ⟨726701, by rfl⟩ : syracuseStep 3875741 = 1453403) B1453403
theorem B1360891 : Blo 1273955 1360891 := bstep (se 1 (by rfl) ⟨1020668, by rfl⟩ : syracuseStep 1360891 = 2041337) B2041337
theorem B2868587 : Blo 1273955 2868587 := bstep (se 1 (by rfl) ⟨2151440, by rfl⟩ : syracuseStep 2868587 = 4302881) B4302881
theorem B3630511 : Blo 1273955 3630511 := bstep (se 1 (by rfl) ⟨2722883, by rfl⟩ : syracuseStep 3630511 = 5445767) B5445767
theorem B62883317 : Blo 1273955 62883317 := bstep (se 5 (by rfl) ⟨2947655, by rfl⟩ : syracuseStep 62883317 = 5895311) B5895311
theorem B4359673 : Blo 1273955 4359673 := bstep (se 2 (by rfl) ⟨1634877, by rfl⟩ : syracuseStep 4359673 = 3269755) B3269755
theorem B2868857 : Blo 1273955 2868857 := bstep (se 2 (by rfl) ⟨1075821, by rfl⟩ : syracuseStep 2868857 = 2151643) B2151643
theorem B46532231 : Blo 1273955 46532231 := bstep (se 1 (by rfl) ⟨34899173, by rfl⟩ : syracuseStep 46532231 = 69798347) B69798347
theorem B4302503 : Blo 1273955 4302503 := bstep (se 1 (by rfl) ⟨3226877, by rfl⟩ : syracuseStep 4302503 = 6453755) B6453755
theorem B10331833 : Blo 1273955 10331833 := bstep (se 2 (by rfl) ⟨3874437, by rfl⟩ : syracuseStep 10331833 = 7748875) B7748875
theorem B1435387 : Blo 1273955 1435387 := bstep (se 1 (by rfl) ⟨1076540, by rfl⟩ : syracuseStep 1435387 = 2153081) B2153081
theorem B1435423 : Blo 1273955 1435423 := bstep (se 1 (by rfl) ⟨1076567, by rfl⟩ : syracuseStep 1435423 = 2153135) B2153135
theorem B19629989 : Blo 1273955 19629989 := bstep (se 4 (by rfl) ⟨1840311, by rfl⟩ : syracuseStep 19629989 = 3680623) B3680623
theorem B9676745 : Blo 1273955 9676745 := bstep (se 2 (by rfl) ⟨3628779, by rfl⟩ : syracuseStep 9676745 = 7257559) B7257559
theorem B1910939 : Blo 1273955 1910939 := bstep (se 1 (by rfl) ⟨1433204, by rfl⟩ : syracuseStep 1910939 = 2866409) B2866409
theorem B1910975 : Blo 1273955 1910975 := bstep (se 1 (by rfl) ⟨1433231, by rfl⟩ : syracuseStep 1910975 = 2866463) B2866463
theorem B1911017 : Blo 1273955 1911017 := bstep (se 2 (by rfl) ⟨716631, by rfl⟩ : syracuseStep 1911017 = 1433263) B1433263
theorem B2296043 : Blo 1273955 2296043 := bstep (se 1 (by rfl) ⟨1722032, by rfl⟩ : syracuseStep 2296043 = 3444065) B3444065
theorem B37259509 : Blo 1273955 37259509 := bstep (se 5 (by rfl) ⟨1746539, by rfl⟩ : syracuseStep 37259509 = 3493079) B3493079
theorem B4303097 : Blo 1273955 4303097 := bstep (se 2 (by rfl) ⟨1613661, by rfl⟩ : syracuseStep 4303097 = 3227323) B3227323
theorem B4303151 : Blo 1273955 4303151 := bstep (se 1 (by rfl) ⟨3227363, by rfl⟩ : syracuseStep 4303151 = 6454727) B6454727
theorem B3680603 : Blo 1273955 3680603 := bstep (se 1 (by rfl) ⟨2760452, by rfl⟩ : syracuseStep 3680603 = 5520905) B5520905
theorem B4843871 : Blo 1273955 4843871 := bstep (se 1 (by rfl) ⟨3632903, by rfl⟩ : syracuseStep 4843871 = 7265807) B7265807
theorem B17451389 : Blo 1273955 17451389 := bstep (se 3 (by rfl) ⟨3272135, by rfl⟩ : syracuseStep 17451389 = 6544271) B6544271
theorem B19614109 : Blo 1273955 19614109 := bstep (se 3 (by rfl) ⟨3677645, by rfl⟩ : syracuseStep 19614109 = 7355291) B7355291
theorem B17435141 : Blo 1273955 17435141 := bstep (se 4 (by rfl) ⟨1634544, by rfl⟩ : syracuseStep 17435141 = 3269089) B3269089
theorem B4303367 : Blo 1273955 4303367 := bstep (se 1 (by rfl) ⟨3227525, by rfl⟩ : syracuseStep 4303367 = 6455051) B6455051
theorem B1911323 : Blo 1273955 1911323 := bstep (se 1 (by rfl) ⟨1433492, by rfl⟩ : syracuseStep 1911323 = 2866985) B2866985
theorem B1911401 : Blo 1273955 1911401 := bstep (se 2 (by rfl) ⟨716775, by rfl⟩ : syracuseStep 1911401 = 1433551) B1433551
theorem B2869865 : Blo 1273955 2869865 := bstep (se 2 (by rfl) ⟨1076199, by rfl⟩ : syracuseStep 2869865 = 2152399) B2152399
theorem B3631787 : Blo 1273955 3631787 := bstep (se 1 (by rfl) ⟨2723840, by rfl⟩ : syracuseStep 3631787 = 5447681) B5447681
theorem B6449867 : Blo 1273955 6449867 := bstep (se 1 (by rfl) ⟨4837400, by rfl⟩ : syracuseStep 6449867 = 9674801) B9674801
theorem B1911929 : Blo 1273955 1911929 := bstep (se 2 (by rfl) ⟨716973, by rfl⟩ : syracuseStep 1911929 = 1433947) B1433947
theorem B4304015 : Blo 1273955 4304015 := bstep (se 1 (by rfl) ⟨3228011, by rfl⟩ : syracuseStep 4304015 = 6456023) B6456023
theorem B1912031 : Blo 1273955 1912031 := bstep (se 1 (by rfl) ⟨1434023, by rfl⟩ : syracuseStep 1912031 = 2868047) B2868047
theorem B2870495 : Blo 1273955 2870495 := bstep (se 1 (by rfl) ⟨2152871, by rfl⟩ : syracuseStep 2870495 = 4305743) B4305743
theorem B1912073 : Blo 1273955 1912073 := bstep (se 2 (by rfl) ⟨717027, by rfl⟩ : syracuseStep 1912073 = 1434055) B1434055
theorem B1912175 : Blo 1273955 1912175 := bstep (se 1 (by rfl) ⟨1434131, by rfl⟩ : syracuseStep 1912175 = 2868263) B2868263
theorem B2870711 : Blo 1273955 2870711 := bstep (se 1 (by rfl) ⟨2153033, by rfl⟩ : syracuseStep 2870711 = 4306067) B4306067
theorem B1912295 : Blo 1273955 1912295 := bstep (se 1 (by rfl) ⟨1434221, by rfl⟩ : syracuseStep 1912295 = 2868443) B2868443
theorem B2420219 : Blo 1273955 2420219 := bstep (se 1 (by rfl) ⟨1815164, by rfl⟩ : syracuseStep 2420219 = 3630329) B3630329
theorem B4304447 : Blo 1273955 4304447 := bstep (se 1 (by rfl) ⟨3228335, by rfl⟩ : syracuseStep 4304447 = 6456671) B6456671
theorem B11628127 : Blo 1273955 11628127 := bstep (se 1 (by rfl) ⟨8721095, by rfl⟩ : syracuseStep 11628127 = 17442191) B17442191
theorem B8719979 : Blo 1273955 8719979 := bstep (se 1 (by rfl) ⟨6539984, by rfl⟩ : syracuseStep 8719979 = 13079969) B13079969
theorem B1912427 : Blo 1273955 1912427 := bstep (se 1 (by rfl) ⟨1434320, by rfl⟩ : syracuseStep 1912427 = 2868641) B2868641
theorem B2870891 : Blo 1273955 2870891 := bstep (se 1 (by rfl) ⟨2153168, by rfl⟩ : syracuseStep 2870891 = 4306337) B4306337
theorem B1912553 : Blo 1273955 1912553 := bstep (se 2 (by rfl) ⟨717207, by rfl⟩ : syracuseStep 1912553 = 1434415) B1434415
theorem B1912697 : Blo 1273955 1912697 := bstep (se 2 (by rfl) ⟨717261, by rfl⟩ : syracuseStep 1912697 = 1434523) B1434523
theorem B3682169 : Blo 1273955 3682169 := bstep (se 2 (by rfl) ⟨1380813, by rfl⟩ : syracuseStep 3682169 = 2761627) B2761627
theorem B2043803 : Blo 1273955 2043803 := bstep (se 1 (by rfl) ⟨1532852, by rfl⟩ : syracuseStep 2043803 = 3065705) B3065705
theorem B1912799 : Blo 1273955 1912799 := bstep (se 1 (by rfl) ⟨1434599, by rfl⟩ : syracuseStep 1912799 = 2869199) B2869199
theorem B2723807 : Blo 1273955 2723807 := bstep (se 1 (by rfl) ⟨2042855, by rfl⟩ : syracuseStep 2723807 = 4085711) B4085711
theorem B1273466933 : Blo 1273955 1273466933 := bstep (se 5 (by rfl) ⟨59693762, by rfl⟩ : syracuseStep 1273466933 = 119387525) B119387525
theorem B12415169 : Blo 1273955 12415169 := bstep (se 2 (by rfl) ⟨4655688, by rfl⟩ : syracuseStep 12415169 = 9311377) B9311377
theorem B1913051 : Blo 1273955 1913051 := bstep (se 1 (by rfl) ⟨1434788, by rfl⟩ : syracuseStep 1913051 = 2869577) B2869577
theorem B1274087 : Blo 1273955 1274087 := bstep (se 1 (by rfl) ⟨955565, by rfl⟩ : syracuseStep 1274087 = 1911131) B1911131
theorem B1913063 : Blo 1273955 1913063 := bstep (se 1 (by rfl) ⟨1434797, by rfl⟩ : syracuseStep 1913063 = 2869595) B2869595
theorem B4305149 : Blo 1273955 4305149 := bstep (se 3 (by rfl) ⟨807215, by rfl⟩ : syracuseStep 4305149 = 1614431) B1614431
theorem B1274239 : Blo 1273955 1274239 := bstep (se 1 (by rfl) ⟨955679, by rfl⟩ : syracuseStep 1274239 = 1911359) B1911359
theorem B1913225 : Blo 1273955 1913225 := bstep (se 2 (by rfl) ⟨717459, by rfl⟩ : syracuseStep 1913225 = 1434919) B1434919
theorem B14528969 : Blo 1273955 14528969 := bstep (se 2 (by rfl) ⟨5448363, by rfl⟩ : syracuseStep 14528969 = 10896727) B10896727
theorem B1274319 : Blo 1273955 1274319 := bstep (se 1 (by rfl) ⟨955739, by rfl⟩ : syracuseStep 1274319 = 1911479) B1911479
theorem B1913321 : Blo 1273955 1913321 := bstep (se 2 (by rfl) ⟨717495, by rfl⟩ : syracuseStep 1913321 = 1434991) B1434991
theorem B18625085 : Blo 1273955 18625085 := bstep (se 3 (by rfl) ⟨3492203, by rfl⟩ : syracuseStep 18625085 = 6984407) B6984407
theorem B8163935 : Blo 1273955 8163935 := bstep (se 1 (by rfl) ⟨6122951, by rfl⟩ : syracuseStep 8163935 = 12245903) B12245903
theorem B2421343 : Blo 1273955 2421343 := bstep (se 1 (by rfl) ⟨1816007, by rfl⟩ : syracuseStep 2421343 = 3632015) B3632015
theorem B1274471 : Blo 1273955 1274471 := bstep (se 1 (by rfl) ⟨955853, by rfl⟩ : syracuseStep 1274471 = 1911707) B1911707
theorem B1913447 : Blo 1273955 1913447 := bstep (se 1 (by rfl) ⟨1435085, by rfl⟩ : syracuseStep 1913447 = 2870171) B2870171
theorem B62050931 : Blo 1273955 62050931 := bstep (se 1 (by rfl) ⟨46538198, by rfl⟩ : syracuseStep 62050931 = 93076397) B93076397
theorem B13087403 : Blo 1273955 13087403 := bstep (se 1 (by rfl) ⟨9815552, by rfl⟩ : syracuseStep 13087403 = 19631105) B19631105
theorem B29463263 : Blo 1273955 29463263 := bstep (se 1 (by rfl) ⟨22097447, by rfl⟩ : syracuseStep 29463263 = 44194895) B44194895
theorem B1913579 : Blo 1273955 1913579 := bstep (se 1 (by rfl) ⟨1435184, by rfl⟩ : syracuseStep 1913579 = 2870369) B2870369
theorem B1913609 : Blo 1273955 1913609 := bstep (se 2 (by rfl) ⟨717603, by rfl⟩ : syracuseStep 1913609 = 1435207) B1435207
theorem B4305689 : Blo 1273955 4305689 := bstep (se 2 (by rfl) ⟨1614633, by rfl⟩ : syracuseStep 4305689 = 3229267) B3229267
theorem B1274735 : Blo 1273955 1274735 := bstep (se 1 (by rfl) ⟨956051, by rfl⟩ : syracuseStep 1274735 = 1912103) B1912103
theorem B1913711 : Blo 1273955 1913711 := bstep (se 1 (by rfl) ⟨1435283, by rfl⟩ : syracuseStep 1913711 = 2870567) B2870567
theorem B37262227 : Blo 1273955 37262227 := bstep (se 1 (by rfl) ⟨27946670, by rfl⟩ : syracuseStep 37262227 = 55893341) B55893341
theorem B1274791 : Blo 1273955 1274791 := bstep (se 1 (by rfl) ⟨956093, by rfl⟩ : syracuseStep 1274791 = 1912187) B1912187
theorem B1274875 : Blo 1273955 1274875 := bstep (se 1 (by rfl) ⟨956156, by rfl⟩ : syracuseStep 1274875 = 1912313) B1912313
theorem B4305959 : Blo 1273955 4305959 := bstep (se 1 (by rfl) ⟨3229469, by rfl⟩ : syracuseStep 4305959 = 6458939) B6458939
theorem B1274943 : Blo 1273955 1274943 := bstep (se 1 (by rfl) ⟨956207, by rfl⟩ : syracuseStep 1274943 = 1912415) B1912415
theorem B6452297 : Blo 1273955 6452297 := bstep (se 2 (by rfl) ⟨2419611, by rfl⟩ : syracuseStep 6452297 = 4839223) B4839223
theorem B16331969 : Blo 1273955 16331969 := bstep (se 2 (by rfl) ⟨6124488, by rfl⟩ : syracuseStep 16331969 = 12248977) B12248977
theorem B1275087 : Blo 1273955 1275087 := bstep (se 1 (by rfl) ⟨956315, by rfl⟩ : syracuseStep 1275087 = 1912631) B1912631
theorem B9680147 : Blo 1273955 9680147 := bstep (se 1 (by rfl) ⟨7260110, by rfl⟩ : syracuseStep 9680147 = 14520221) B14520221
theorem B20673917 : Blo 1273955 20673917 := bstep (se 3 (by rfl) ⟨3876359, by rfl⟩ : syracuseStep 20673917 = 7752719) B7752719
theorem B1275291 : Blo 1273955 1275291 := bstep (se 1 (by rfl) ⟨956468, by rfl⟩ : syracuseStep 1275291 = 1912937) B1912937
theorem B141481403 : Blo 1273955 141481403 := bstep (se 1 (by rfl) ⟨106111052, by rfl⟩ : syracuseStep 141481403 = 212222105) B212222105
theorem B29455883 : Blo 1273955 29455883 := bstep (se 1 (by rfl) ⟨22091912, by rfl⟩ : syracuseStep 29455883 = 44183825) B44183825
theorem B15496775 : Blo 1273955 15496775 := bstep (se 1 (by rfl) ⟨11622581, by rfl⟩ : syracuseStep 15496775 = 23245163) B23245163
theorem B1275503 : Blo 1273955 1275503 := bstep (se 1 (by rfl) ⟨956627, by rfl⟩ : syracuseStep 1275503 = 1913255) B1913255
theorem B1275559 : Blo 1273955 1275559 := bstep (se 1 (by rfl) ⟨956669, by rfl⟩ : syracuseStep 1275559 = 1913339) B1913339
theorem B6452945 : Blo 1273955 6452945 := bstep (se 2 (by rfl) ⟨2419854, by rfl⟩ : syracuseStep 6452945 = 4839709) B4839709
theorem B1275643 : Blo 1273955 1275643 := bstep (se 1 (by rfl) ⟨956732, by rfl⟩ : syracuseStep 1275643 = 1913465) B1913465
theorem B1275679 : Blo 1273955 1275679 := bstep (se 1 (by rfl) ⟨956759, by rfl⟩ : syracuseStep 1275679 = 1913519) B1913519
theorem B41908013 : Blo 1273955 41908013 := bstep (se 3 (by rfl) ⟨7857752, by rfl⟩ : syracuseStep 41908013 = 15715505) B15715505
theorem B1275711 : Blo 1273955 1275711 := bstep (se 1 (by rfl) ⟨956783, by rfl⟩ : syracuseStep 1275711 = 1913567) B1913567
theorem B2152271 : Blo 1273955 2152271 := bstep (se 1 (by rfl) ⟨1614203, by rfl⟩ : syracuseStep 2152271 = 3228407) B3228407
theorem B5896093 : Blo 1273955 5896093 := bstep (se 3 (by rfl) ⟨1105517, by rfl⟩ : syracuseStep 5896093 = 2211035) B2211035
theorem B1275887 : Blo 1273955 1275887 := bstep (se 1 (by rfl) ⟨956915, by rfl⟩ : syracuseStep 1275887 = 1913831) B1913831
theorem B3225683 : Blo 1273955 3225683 := bstep (se 1 (by rfl) ⟨2419262, by rfl⟩ : syracuseStep 3225683 = 4838525) B4838525
theorem B10344647 : Blo 1273955 10344647 := bstep (se 1 (by rfl) ⟨7758485, by rfl⟩ : syracuseStep 10344647 = 15516971) B15516971
theorem B1939835 : Blo 1273955 1939835 := bstep (se 1 (by rfl) ⟨1454876, by rfl⟩ : syracuseStep 1939835 = 2909753) B2909753
theorem B3226169 : Blo 1273955 3226169 := bstep (se 2 (by rfl) ⟨1209813, by rfl⟩ : syracuseStep 3226169 = 2419627) B2419627
theorem B4086607 : Blo 1273955 4086607 := bstep (se 1 (by rfl) ⟨3064955, by rfl⟩ : syracuseStep 4086607 = 6129911) B6129911
theorem B3627983 : Blo 1273955 3627983 := bstep (se 1 (by rfl) ⟨2720987, by rfl⟩ : syracuseStep 3627983 = 5441975) B5441975
theorem B13089863 : Blo 1273955 13089863 := bstep (se 1 (by rfl) ⟨9817397, by rfl⟩ : syracuseStep 13089863 = 19634795) B19634795
theorem B8166653 : Blo 1273955 8166653 := bstep (se 3 (by rfl) ⟨1531247, by rfl⟩ : syracuseStep 8166653 = 3062495) B3062495
theorem B1613135 : Blo 1273955 1613135 := bstep (se 1 (by rfl) ⟨1209851, by rfl⟩ : syracuseStep 1613135 = 2419703) B2419703
theorem B4300127 : Blo 1273955 4300127 := bstep (se 1 (by rfl) ⟨3225095, by rfl⟩ : syracuseStep 4300127 = 6450191) B6450191
theorem B7355753 : Blo 1273955 7355753 := bstep (se 2 (by rfl) ⟨2758407, by rfl⟩ : syracuseStep 7355753 = 5516815) B5516815
theorem B2866643 : Blo 1273955 2866643 := bstep (se 1 (by rfl) ⟨2149982, by rfl⟩ : syracuseStep 2866643 = 4299965) B4299965
theorem B17440231 : Blo 1273955 17440231 := bstep (se 1 (by rfl) ⟨13080173, by rfl⟩ : syracuseStep 17440231 = 26160347) B26160347
theorem B1613287 : Blo 1273955 1613287 := bstep (se 1 (by rfl) ⟨1209965, by rfl⟩ : syracuseStep 1613287 = 2419931) B2419931
theorem B3227111 : Blo 1273955 3227111 := bstep (se 1 (by rfl) ⟨2420333, by rfl⟩ : syracuseStep 3227111 = 4840667) B4840667
theorem B9182929 : Blo 1273955 9182929 := bstep (se 2 (by rfl) ⟨3443598, by rfl⟩ : syracuseStep 9182929 = 6887197) B6887197
theorem B2866913 : Blo 1273955 2866913 := bstep (se 2 (by rfl) ⟨1075092, by rfl⟩ : syracuseStep 2866913 = 2150185) B2150185
theorem B7257833 : Blo 1273955 7257833 := bstep (se 2 (by rfl) ⟨2721687, by rfl⟩ : syracuseStep 7257833 = 5443375) B5443375
theorem B3628871 : Blo 1273955 3628871 := bstep (se 1 (by rfl) ⟨2721653, by rfl⟩ : syracuseStep 3628871 = 5443307) B5443307
theorem B4300667 : Blo 1273955 4300667 := bstep (se 1 (by rfl) ⟨3225500, by rfl⟩ : syracuseStep 4300667 = 6451001) B6451001
theorem B848977955 : Blo 1273955 848977955 := bstep (se 1 (by rfl) ⟨636733466, by rfl⟩ : syracuseStep 848977955 = 1273466933) B1273466933
theorem B2867435 : Blo 1273955 2867435 := bstep (se 1 (by rfl) ⟨2150576, by rfl⟩ : syracuseStep 2867435 = 4301153) B4301153
theorem B6128065 : Blo 1273955 6128065 := bstep (se 2 (by rfl) ⟨2298024, by rfl⟩ : syracuseStep 6128065 = 4596049) B4596049
theorem B8724935 : Blo 1273955 8724935 := bstep (se 1 (by rfl) ⟨6543701, by rfl⟩ : syracuseStep 8724935 = 13087403) B13087403
theorem B4301531 : Blo 1273955 4301531 := bstep (se 1 (by rfl) ⟨3226148, by rfl⟩ : syracuseStep 4301531 = 6452297) B6452297
theorem B3228457 : Blo 1273955 3228457 := bstep (se 2 (by rfl) ⟨1210671, by rfl⟩ : syracuseStep 3228457 = 2421343) B2421343
theorem B10887979 : Blo 1273955 10887979 := bstep (se 1 (by rfl) ⟨8165984, by rfl⟩ : syracuseStep 10887979 = 16331969) B16331969
theorem B4301693 : Blo 1273955 4301693 := bstep (se 3 (by rfl) ⟨806567, by rfl⟩ : syracuseStep 4301693 = 1613135) B1613135
theorem B19637255 : Blo 1273955 19637255 := bstep (se 1 (by rfl) ⟨14727941, by rfl⟩ : syracuseStep 19637255 = 29455883) B29455883
theorem B10331183 : Blo 1273955 10331183 := bstep (se 1 (by rfl) ⟨7748387, by rfl⟩ : syracuseStep 10331183 = 15496775) B15496775
theorem B5448809 : Blo 1273955 5448809 := bstep (se 2 (by rfl) ⟨2043303, by rfl⟩ : syracuseStep 5448809 = 4086607) B4086607
theorem B2868335 : Blo 1273955 2868335 := bstep (se 1 (by rfl) ⟨2151251, by rfl⟩ : syracuseStep 2868335 = 4302503) B4302503
theorem B4301963 : Blo 1273955 4301963 := bstep (se 1 (by rfl) ⟨3226472, by rfl⟩ : syracuseStep 4301963 = 6452945) B6452945
theorem B1434847 : Blo 1273955 1434847 := bstep (se 1 (by rfl) ⟨1076135, by rfl⟩ : syracuseStep 1434847 = 2152271) B2152271
theorem B2868731 : Blo 1273955 2868731 := bstep (se 1 (by rfl) ⟨2151548, by rfl⟩ : syracuseStep 2868731 = 4303097) B4303097
theorem B2868767 : Blo 1273955 2868767 := bstep (se 1 (by rfl) ⟨2151575, by rfl⟩ : syracuseStep 2868767 = 4303151) B4303151
theorem B3229247 : Blo 1273955 3229247 := bstep (se 1 (by rfl) ⟨2421935, by rfl⟩ : syracuseStep 3229247 = 4843871) B4843871
theorem B2868911 : Blo 1273955 2868911 := bstep (se 1 (by rfl) ⟨2151683, by rfl⟩ : syracuseStep 2868911 = 4303367) B4303367
theorem B2418655 : Blo 1273955 2418655 := bstep (se 1 (by rfl) ⟨1813991, by rfl⟩ : syracuseStep 2418655 = 3627983) B3627983
theorem B8726575 : Blo 1273955 8726575 := bstep (se 1 (by rfl) ⟨6544931, by rfl⟩ : syracuseStep 8726575 = 13089863) B13089863
theorem B2869343 : Blo 1273955 2869343 := bstep (se 1 (by rfl) ⟨2152007, by rfl⟩ : syracuseStep 2869343 = 4304015) B4304015
theorem B1911095 : Blo 1273955 1911095 := bstep (se 1 (by rfl) ⟨1433321, by rfl⟩ : syracuseStep 1911095 = 2866643) B2866643
theorem B2869631 : Blo 1273955 2869631 := bstep (se 1 (by rfl) ⟨2152223, by rfl⟩ : syracuseStep 2869631 = 4304447) B4304447
theorem B5450141 : Blo 1273955 5450141 := bstep (se 3 (by rfl) ⟨1021901, by rfl⟩ : syracuseStep 5450141 = 2043803) B2043803
theorem B1911275 : Blo 1273955 1911275 := bstep (se 1 (by rfl) ⟨1433456, by rfl⟩ : syracuseStep 1911275 = 2866913) B2866913
theorem B2419247 : Blo 1273955 2419247 := bstep (se 1 (by rfl) ⟨1814435, by rfl⟩ : syracuseStep 2419247 = 3628871) B3628871
theorem B4303583 : Blo 1273955 4303583 := bstep (se 1 (by rfl) ⟨3227687, by rfl⟩ : syracuseStep 4303583 = 6455375) B6455375
theorem B8276779 : Blo 1273955 8276779 := bstep (se 1 (by rfl) ⟨6207584, by rfl⟩ : syracuseStep 8276779 = 12415169) B12415169
theorem B2870099 : Blo 1273955 2870099 := bstep (se 1 (by rfl) ⟨2152574, by rfl⟩ : syracuseStep 2870099 = 4305149) B4305149
theorem B9685979 : Blo 1273955 9685979 := bstep (se 1 (by rfl) ⟨7264484, by rfl⟩ : syracuseStep 9685979 = 14528969) B14528969
theorem B49679345 : Blo 1273955 49679345 := bstep (se 2 (by rfl) ⟨18629754, by rfl⟩ : syracuseStep 49679345 = 37259509) B37259509
theorem B5442623 : Blo 1273955 5442623 := bstep (se 1 (by rfl) ⟨4081967, by rfl⟩ : syracuseStep 5442623 = 8163935) B8163935
theorem B62016677 : Blo 1273955 62016677 := bstep (se 4 (by rfl) ⟨5814063, by rfl⟩ : syracuseStep 62016677 = 11628127) B11628127
theorem B1911977 : Blo 1273955 1911977 := bstep (se 2 (by rfl) ⟨716991, by rfl⟩ : syracuseStep 1911977 = 1433983) B1433983
theorem B2870459 : Blo 1273955 2870459 := bstep (se 1 (by rfl) ⟨2152844, by rfl⟩ : syracuseStep 2870459 = 4305689) B4305689
theorem B26152145 : Blo 1273955 26152145 := bstep (se 2 (by rfl) ⟨9807054, by rfl⟩ : syracuseStep 26152145 = 19614109) B19614109
theorem B2583827 : Blo 1273955 2583827 := bstep (se 1 (by rfl) ⟨1937870, by rfl⟩ : syracuseStep 2583827 = 3875741) B3875741
theorem B2870639 : Blo 1273955 2870639 := bstep (se 1 (by rfl) ⟨2152979, by rfl⟩ : syracuseStep 2870639 = 4305959) B4305959
theorem B1912391 : Blo 1273955 1912391 := bstep (se 1 (by rfl) ⟨1434293, by rfl⟩ : syracuseStep 1912391 = 2868587) B2868587
theorem B13782611 : Blo 1273955 13782611 := bstep (se 1 (by rfl) ⟨10336958, by rfl⟩ : syracuseStep 13782611 = 20673917) B20673917
theorem B5172893 : Blo 1273955 5172893 := bstep (se 3 (by rfl) ⟨969917, by rfl⟩ : syracuseStep 5172893 = 1939835) B1939835
theorem B41922211 : Blo 1273955 41922211 := bstep (se 1 (by rfl) ⟨31441658, by rfl⟩ : syracuseStep 41922211 = 62883317) B62883317
theorem B1912571 : Blo 1273955 1912571 := bstep (se 1 (by rfl) ⟨1434428, by rfl⟩ : syracuseStep 1912571 = 2868857) B2868857
theorem B27938675 : Blo 1273955 27938675 := bstep (se 1 (by rfl) ⟨20954006, by rfl⟩ : syracuseStep 27938675 = 41908013) B41908013
theorem B13086659 : Blo 1273955 13086659 := bstep (se 1 (by rfl) ⟨9814994, by rfl⟩ : syracuseStep 13086659 = 19629989) B19629989
theorem B6451163 : Blo 1273955 6451163 := bstep (se 1 (by rfl) ⟨4838372, by rfl⟩ : syracuseStep 6451163 = 9676745) B9676745
theorem B2150455 : Blo 1273955 2150455 := bstep (se 1 (by rfl) ⟨1612841, by rfl⟩ : syracuseStep 2150455 = 3225683) B3225683
theorem B1273959 : Blo 1273955 1273959 := bstep (se 1 (by rfl) ⟨955469, by rfl⟩ : syracuseStep 1273959 = 1910939) B1910939
theorem B1273983 : Blo 1273955 1273983 := bstep (se 1 (by rfl) ⟨955487, by rfl⟩ : syracuseStep 1273983 = 1910975) B1910975
theorem B1274011 : Blo 1273955 1274011 := bstep (se 1 (by rfl) ⟨955508, by rfl⟩ : syracuseStep 1274011 = 1911017) B1911017
theorem B2453735 : Blo 1273955 2453735 := bstep (se 1 (by rfl) ⟨1840301, by rfl⟩ : syracuseStep 2453735 = 3680603) B3680603
theorem B23253277 : Blo 1273955 23253277 := bstep (se 3 (by rfl) ⟨4359989, by rfl⟩ : syracuseStep 23253277 = 8719979) B8719979
theorem B1274215 : Blo 1273955 1274215 := bstep (se 1 (by rfl) ⟨955661, by rfl⟩ : syracuseStep 1274215 = 1911323) B1911323
theorem B2150779 : Blo 1273955 2150779 := bstep (se 1 (by rfl) ⟨1613084, by rfl⟩ : syracuseStep 2150779 = 3226169) B3226169
theorem B1274267 : Blo 1273955 1274267 := bstep (se 1 (by rfl) ⟨955700, by rfl⟩ : syracuseStep 1274267 = 1911401) B1911401
theorem B1913243 : Blo 1273955 1913243 := bstep (se 1 (by rfl) ⟨1434932, by rfl⟩ : syracuseStep 1913243 = 2869865) B2869865
theorem B2421191 : Blo 1273955 2421191 := bstep (se 1 (by rfl) ⟨1815893, by rfl⟩ : syracuseStep 2421191 = 3631787) B3631787
theorem B23253641 : Blo 1273955 23253641 := bstep (se 2 (by rfl) ⟨8720115, by rfl⟩ : syracuseStep 23253641 = 17440231) B17440231
theorem B2151049 : Blo 1273955 2151049 := bstep (se 2 (by rfl) ⟨806643, by rfl⟩ : syracuseStep 2151049 = 1613287) B1613287
theorem B5812897 : Blo 1273955 5812897 := bstep (se 2 (by rfl) ⟨2179836, by rfl⟩ : syracuseStep 5812897 = 4359673) B4359673
theorem B1274619 : Blo 1273955 1274619 := bstep (se 1 (by rfl) ⟨955964, by rfl⟩ : syracuseStep 1274619 = 1911929) B1911929
theorem B1274687 : Blo 1273955 1274687 := bstep (se 1 (by rfl) ⟨956015, by rfl⟩ : syracuseStep 1274687 = 1912031) B1912031
theorem B1913663 : Blo 1273955 1913663 := bstep (se 1 (by rfl) ⟨1435247, by rfl⟩ : syracuseStep 1913663 = 2870495) B2870495
theorem B5444435 : Blo 1273955 5444435 := bstep (se 1 (by rfl) ⟨4083326, by rfl⟩ : syracuseStep 5444435 = 8166653) B8166653
theorem B1274715 : Blo 1273955 1274715 := bstep (se 1 (by rfl) ⟨956036, by rfl⟩ : syracuseStep 1274715 = 1912073) B1912073
theorem B4903835 : Blo 1273955 4903835 := bstep (se 1 (by rfl) ⟨3677876, by rfl⟩ : syracuseStep 4903835 = 7355753) B7355753
theorem B1274783 : Blo 1273955 1274783 := bstep (se 1 (by rfl) ⟨956087, by rfl⟩ : syracuseStep 1274783 = 1912175) B1912175
theorem B13775777 : Blo 1273955 13775777 := bstep (se 2 (by rfl) ⟨5165916, by rfl⟩ : syracuseStep 13775777 = 10331833) B10331833
theorem B12243905 : Blo 1273955 12243905 := bstep (se 2 (by rfl) ⟨4591464, by rfl⟩ : syracuseStep 12243905 = 9182929) B9182929
theorem B1913807 : Blo 1273955 1913807 := bstep (se 1 (by rfl) ⟨1435355, by rfl⟩ : syracuseStep 1913807 = 2870711) B2870711
theorem B1274863 : Blo 1273955 1274863 := bstep (se 1 (by rfl) ⟨956147, by rfl⟩ : syracuseStep 1274863 = 1912295) B1912295
theorem B2151407 : Blo 1273955 2151407 := bstep (se 1 (by rfl) ⟨1613555, by rfl⟩ : syracuseStep 2151407 = 3227111) B3227111
theorem B1913849 : Blo 1273955 1913849 := bstep (se 2 (by rfl) ⟨717693, by rfl⟩ : syracuseStep 1913849 = 1435387) B1435387
theorem B1913897 : Blo 1273955 1913897 := bstep (se 2 (by rfl) ⟨717711, by rfl⟩ : syracuseStep 1913897 = 1435423) B1435423
theorem B1274951 : Blo 1273955 1274951 := bstep (se 1 (by rfl) ⟨956213, by rfl⟩ : syracuseStep 1274951 = 1912427) B1912427
theorem B1913927 : Blo 1273955 1913927 := bstep (se 1 (by rfl) ⟨1435445, by rfl⟩ : syracuseStep 1913927 = 2870891) B2870891
theorem B4838555 : Blo 1273955 4838555 := bstep (se 1 (by rfl) ⟨3628916, by rfl⟩ : syracuseStep 4838555 = 7257833) B7257833
theorem B1275035 : Blo 1273955 1275035 := bstep (se 1 (by rfl) ⟨956276, by rfl⟩ : syracuseStep 1275035 = 1912553) B1912553
theorem B7861457 : Blo 1273955 7861457 := bstep (se 2 (by rfl) ⟨2948046, by rfl⟩ : syracuseStep 7861457 = 5896093) B5896093
theorem B1275131 : Blo 1273955 1275131 := bstep (se 1 (by rfl) ⟨956348, by rfl⟩ : syracuseStep 1275131 = 1912697) B1912697
theorem B2454779 : Blo 1273955 2454779 := bstep (se 1 (by rfl) ⟨1841084, by rfl⟩ : syracuseStep 2454779 = 3682169) B3682169
theorem B1275199 : Blo 1273955 1275199 := bstep (se 1 (by rfl) ⟨956399, by rfl⟩ : syracuseStep 1275199 = 1912799) B1912799
theorem B1815871 : Blo 1273955 1815871 := bstep (se 1 (by rfl) ⟨1361903, by rfl⟩ : syracuseStep 1815871 = 2723807) B2723807
theorem B1275367 : Blo 1273955 1275367 := bstep (se 1 (by rfl) ⟨956525, by rfl⟩ : syracuseStep 1275367 = 1913051) B1913051
theorem B1275375 : Blo 1273955 1275375 := bstep (se 1 (by rfl) ⟨956531, by rfl⟩ : syracuseStep 1275375 = 1913063) B1913063
theorem B1275483 : Blo 1273955 1275483 := bstep (se 1 (by rfl) ⟨956612, by rfl⟩ : syracuseStep 1275483 = 1913225) B1913225
theorem B1275547 : Blo 1273955 1275547 := bstep (se 1 (by rfl) ⟨956660, by rfl⟩ : syracuseStep 1275547 = 1913321) B1913321
theorem B12416723 : Blo 1273955 12416723 := bstep (se 1 (by rfl) ⟨9312542, by rfl⟩ : syracuseStep 12416723 = 18625085) B18625085
theorem B18388691 : Blo 1273955 18388691 := bstep (se 1 (by rfl) ⟨13791518, by rfl⟩ : syracuseStep 18388691 = 27583037) B27583037
theorem B1275631 : Blo 1273955 1275631 := bstep (se 1 (by rfl) ⟨956723, by rfl⟩ : syracuseStep 1275631 = 1913447) B1913447
theorem B41367287 : Blo 1273955 41367287 := bstep (se 1 (by rfl) ⟨31025465, by rfl⟩ : syracuseStep 41367287 = 62050931) B62050931
theorem B19642175 : Blo 1273955 19642175 := bstep (se 1 (by rfl) ⟨14731631, by rfl⟩ : syracuseStep 19642175 = 29463263) B29463263
theorem B1275719 : Blo 1273955 1275719 := bstep (se 1 (by rfl) ⟨956789, by rfl⟩ : syracuseStep 1275719 = 1913579) B1913579
theorem B1275739 : Blo 1273955 1275739 := bstep (se 1 (by rfl) ⟨956804, by rfl⟩ : syracuseStep 1275739 = 1913609) B1913609
theorem B1275807 : Blo 1273955 1275807 := bstep (se 1 (by rfl) ⟨956855, by rfl⟩ : syracuseStep 1275807 = 1913711) B1913711
theorem B6453431 : Blo 1273955 6453431 := bstep (se 1 (by rfl) ⟨4840073, by rfl⟩ : syracuseStep 6453431 = 9680147) B9680147
theorem B94320935 : Blo 1273955 94320935 := bstep (se 1 (by rfl) ⟨70740701, by rfl⟩ : syracuseStep 94320935 = 141481403) B141481403
theorem B46537037 : Blo 1273955 46537037 := bstep (se 3 (by rfl) ⟨8725694, by rfl⟩ : syracuseStep 46537037 = 17451389) B17451389
theorem B31021487 : Blo 1273955 31021487 := bstep (se 1 (by rfl) ⟨23266115, by rfl⟩ : syracuseStep 31021487 = 46532231) B46532231
theorem B49682969 : Blo 1273955 49682969 := bstep (se 2 (by rfl) ⟨18631113, by rfl⟩ : syracuseStep 49682969 = 37262227) B37262227
theorem B6453917 : Blo 1273955 6453917 := bstep (se 3 (by rfl) ⟨1210109, by rfl⟩ : syracuseStep 6453917 = 2420219) B2420219
theorem B6896431 : Blo 1273955 6896431 := bstep (se 1 (by rfl) ⟨5172323, by rfl⟩ : syracuseStep 6896431 = 10344647) B10344647
theorem B1530695 : Blo 1273955 1530695 := bstep (se 1 (by rfl) ⟨1148021, by rfl⟩ : syracuseStep 1530695 = 2296043) B2296043
theorem B11623427 : Blo 1273955 11623427 := bstep (se 1 (by rfl) ⟨8717570, by rfl⟩ : syracuseStep 11623427 = 17435141) B17435141
theorem B4299911 : Blo 1273955 4299911 := bstep (se 1 (by rfl) ⟨3224933, by rfl⟩ : syracuseStep 4299911 = 6449867) B6449867
theorem B4840681 : Blo 1273955 4840681 := bstep (se 2 (by rfl) ⟨1815255, by rfl⟩ : syracuseStep 4840681 = 3630511) B3630511
theorem B2866751 : Blo 1273955 2866751 := bstep (se 1 (by rfl) ⟨2150063, by rfl⟩ : syracuseStep 2866751 = 4300127) B4300127
theorem B2867111 : Blo 1273955 2867111 := bstep (se 1 (by rfl) ⟨2150333, by rfl⟩ : syracuseStep 2867111 = 4300667) B4300667
theorem B7258085 : Blo 1273955 7258085 := bstep (se 4 (by rfl) ⟨680445, by rfl⟩ : syracuseStep 7258085 = 1360891) B1360891
theorem B565985303 : Blo 1273955 565985303 := bstep (se 1 (by rfl) ⟨424488977, by rfl⟩ : syracuseStep 565985303 = 848977955) B848977955
theorem B2867273 : Blo 1273955 2867273 := bstep (se 2 (by rfl) ⟨1075227, by rfl⟩ : syracuseStep 2867273 = 2150455) B2150455
theorem B27549821 : Blo 1273955 27549821 := bstep (se 3 (by rfl) ⟨5165591, by rfl⟩ : syracuseStep 27549821 = 10331183) B10331183
theorem B5816623 : Blo 1273955 5816623 := bstep (se 1 (by rfl) ⟨4362467, by rfl⟩ : syracuseStep 5816623 = 8724935) B8724935
theorem B2867687 : Blo 1273955 2867687 := bstep (se 1 (by rfl) ⟨2150765, by rfl⟩ : syracuseStep 2867687 = 4301531) B4301531
theorem B2867705 : Blo 1273955 2867705 := bstep (se 2 (by rfl) ⟨1075389, by rfl⟩ : syracuseStep 2867705 = 2150779) B2150779
theorem B3629623 : Blo 1273955 3629623 := bstep (se 1 (by rfl) ⟨2722217, by rfl⟩ : syracuseStep 3629623 = 5444435) B5444435
theorem B2867795 : Blo 1273955 2867795 := bstep (se 1 (by rfl) ⟨2150846, by rfl⟩ : syracuseStep 2867795 = 4301693) B4301693
theorem B9183851 : Blo 1273955 9183851 := bstep (se 1 (by rfl) ⟨6887888, by rfl⟩ : syracuseStep 9183851 = 13775777) B13775777
theorem B6546077 : Blo 1273955 6546077 := bstep (se 3 (by rfl) ⟨1227389, by rfl⟩ : syracuseStep 6546077 = 2454779) B2454779
theorem B1434271 : Blo 1273955 1434271 := bstep (se 1 (by rfl) ⟨1075703, by rfl⟩ : syracuseStep 1434271 = 2151407) B2151407
theorem B13091503 : Blo 1273955 13091503 := bstep (se 1 (by rfl) ⟨9818627, by rfl⟩ : syracuseStep 13091503 = 19637255) B19637255
theorem B2867975 : Blo 1273955 2867975 := bstep (se 1 (by rfl) ⟨2150981, by rfl⟩ : syracuseStep 2867975 = 4301963) B4301963
theorem B2868065 : Blo 1273955 2868065 := bstep (se 2 (by rfl) ⟨1075524, by rfl⟩ : syracuseStep 2868065 = 2151049) B2151049
theorem B7750529 : Blo 1273955 7750529 := bstep (se 2 (by rfl) ⟨2906448, by rfl⟩ : syracuseStep 7750529 = 5812897) B5812897
theorem B11035705 : Blo 1273955 11035705 := bstep (se 2 (by rfl) ⟨4138389, by rfl⟩ : syracuseStep 11035705 = 8276779) B8276779
theorem B14517305 : Blo 1273955 14517305 := bstep (se 2 (by rfl) ⟨5443989, by rfl⟩ : syracuseStep 14517305 = 10887979) B10887979
theorem B6456509 : Blo 1273955 6456509 := bstep (se 3 (by rfl) ⟨1210595, by rfl⟩ : syracuseStep 6456509 = 2421191) B2421191
theorem B4302287 : Blo 1273955 4302287 := bstep (se 1 (by rfl) ⟨3226715, by rfl⟩ : syracuseStep 4302287 = 6453431) B6453431
theorem B31024691 : Blo 1273955 31024691 := bstep (se 1 (by rfl) ⟨23268518, by rfl⟩ : syracuseStep 31024691 = 46537037) B46537037
theorem B33121979 : Blo 1273955 33121979 := bstep (se 1 (by rfl) ⟨24841484, by rfl⟩ : syracuseStep 33121979 = 49682969) B49682969
theorem B4302611 : Blo 1273955 4302611 := bstep (se 1 (by rfl) ⟨3226958, by rfl⟩ : syracuseStep 4302611 = 6453917) B6453917
theorem B2869055 : Blo 1273955 2869055 := bstep (se 1 (by rfl) ⟨2151791, by rfl⟩ : syracuseStep 2869055 = 4303583) B4303583
theorem B6457319 : Blo 1273955 6457319 := bstep (se 1 (by rfl) ⟨4842989, by rfl⟩ : syracuseStep 6457319 = 9685979) B9685979
theorem B17434763 : Blo 1273955 17434763 := bstep (se 1 (by rfl) ⟨13076072, by rfl⟩ : syracuseStep 17434763 = 26152145) B26152145
theorem B1722551 : Blo 1273955 1722551 := bstep (se 1 (by rfl) ⟨1291913, by rfl⟩ : syracuseStep 1722551 = 2583827) B2583827
theorem B4081853 : Blo 1273955 4081853 := bstep (se 3 (by rfl) ⟨765347, by rfl⟩ : syracuseStep 4081853 = 1530695) B1530695
theorem B55896281 : Blo 1273955 55896281 := bstep (se 2 (by rfl) ⟨20961105, by rfl⟩ : syracuseStep 55896281 = 41922211) B41922211
theorem B1911167 : Blo 1273955 1911167 := bstep (se 1 (by rfl) ⟨1433375, by rfl⟩ : syracuseStep 1911167 = 2866751) B2866751
theorem B13076893 : Blo 1273955 13076893 := bstep (se 3 (by rfl) ⟨2451917, by rfl⟩ : syracuseStep 13076893 = 4903835) B4903835
theorem B1911407 : Blo 1273955 1911407 := bstep (se 1 (by rfl) ⟨1433555, by rfl⟩ : syracuseStep 1911407 = 2867111) B2867111
theorem B11635433 : Blo 1273955 11635433 := bstep (se 2 (by rfl) ⟨4363287, by rfl⟩ : syracuseStep 11635433 = 8726575) B8726575
theorem B1911623 : Blo 1273955 1911623 := bstep (se 1 (by rfl) ⟨1433717, by rfl⟩ : syracuseStep 1911623 = 2867435) B2867435
theorem B15502427 : Blo 1273955 15502427 := bstep (se 1 (by rfl) ⟨11626820, by rfl⟩ : syracuseStep 15502427 = 23253641) B23253641
theorem B8170753 : Blo 1273955 8170753 := bstep (se 2 (by rfl) ⟨3064032, by rfl⟩ : syracuseStep 8170753 = 6128065) B6128065
theorem B8162603 : Blo 1273955 8162603 := bstep (se 1 (by rfl) ⟨6121952, by rfl⟩ : syracuseStep 8162603 = 12243905) B12243905
theorem B3632539 : Blo 1273955 3632539 := bstep (se 1 (by rfl) ⟨2724404, by rfl⟩ : syracuseStep 3632539 = 5448809) B5448809
theorem B1912223 : Blo 1273955 1912223 := bstep (se 1 (by rfl) ⟨1434167, by rfl⟩ : syracuseStep 1912223 = 2868335) B2868335
theorem B1912487 : Blo 1273955 1912487 := bstep (se 1 (by rfl) ⟨1434365, by rfl⟩ : syracuseStep 1912487 = 2868731) B2868731
theorem B1912511 : Blo 1273955 1912511 := bstep (se 1 (by rfl) ⟨1434383, by rfl⟩ : syracuseStep 1912511 = 2868767) B2868767
theorem B4304609 : Blo 1273955 4304609 := bstep (se 2 (by rfl) ⟨1614228, by rfl⟩ : syracuseStep 4304609 = 3228457) B3228457
theorem B1912607 : Blo 1273955 1912607 := bstep (se 1 (by rfl) ⟨1434455, by rfl⟩ : syracuseStep 1912607 = 2868911) B2868911
theorem B8277815 : Blo 1273955 8277815 := bstep (se 1 (by rfl) ⟨6208361, by rfl⟩ : syracuseStep 8277815 = 12416723) B12416723
theorem B12259127 : Blo 1273955 12259127 := bstep (se 1 (by rfl) ⟨9194345, by rfl⟩ : syracuseStep 12259127 = 18388691) B18388691
theorem B27578191 : Blo 1273955 27578191 := bstep (se 1 (by rfl) ⟨20683643, by rfl⟩ : syracuseStep 27578191 = 41367287) B41367287
theorem B13094783 : Blo 1273955 13094783 := bstep (se 1 (by rfl) ⟨9821087, by rfl⟩ : syracuseStep 13094783 = 19642175) B19642175
theorem B1912895 : Blo 1273955 1912895 := bstep (se 1 (by rfl) ⟨1434671, by rfl⟩ : syracuseStep 1912895 = 2869343) B2869343
theorem B6451325 : Blo 1273955 6451325 := bstep (se 3 (by rfl) ⟨1209623, by rfl⟩ : syracuseStep 6451325 = 2419247) B2419247
theorem B1274063 : Blo 1273955 1274063 := bstep (se 1 (by rfl) ⟨955547, by rfl⟩ : syracuseStep 1274063 = 1911095) B1911095
theorem B1913087 : Blo 1273955 1913087 := bstep (se 1 (by rfl) ⟨1434815, by rfl⟩ : syracuseStep 1913087 = 2869631) B2869631
theorem B3633427 : Blo 1273955 3633427 := bstep (se 1 (by rfl) ⟨2725070, by rfl⟩ : syracuseStep 3633427 = 5450141) B5450141
theorem B20680991 : Blo 1273955 20680991 := bstep (se 1 (by rfl) ⟨15510743, by rfl⟩ : syracuseStep 20680991 = 31021487) B31021487
theorem B1913129 : Blo 1273955 1913129 := bstep (se 2 (by rfl) ⟨717423, by rfl⟩ : syracuseStep 1913129 = 1434847) B1434847
theorem B1274183 : Blo 1273955 1274183 := bstep (se 1 (by rfl) ⟨955637, by rfl⟩ : syracuseStep 1274183 = 1911275) B1911275
theorem B2421161 : Blo 1273955 2421161 := bstep (se 2 (by rfl) ⟨907935, by rfl⟩ : syracuseStep 2421161 = 1815871) B1815871
theorem B1913399 : Blo 1273955 1913399 := bstep (se 1 (by rfl) ⟨1435049, by rfl⟩ : syracuseStep 1913399 = 2870099) B2870099
theorem B1274651 : Blo 1273955 1274651 := bstep (se 1 (by rfl) ⟨955988, by rfl⟩ : syracuseStep 1274651 = 1911977) B1911977
theorem B1913639 : Blo 1273955 1913639 := bstep (se 1 (by rfl) ⟨1435229, by rfl⟩ : syracuseStep 1913639 = 2870459) B2870459
theorem B1913759 : Blo 1273955 1913759 := bstep (se 1 (by rfl) ⟨1435319, by rfl⟩ : syracuseStep 1913759 = 2870639) B2870639
theorem B1274927 : Blo 1273955 1274927 := bstep (se 1 (by rfl) ⟨956195, by rfl⟩ : syracuseStep 1274927 = 1912391) B1912391
theorem B9188407 : Blo 1273955 9188407 := bstep (se 1 (by rfl) ⟨6891305, by rfl⟩ : syracuseStep 9188407 = 13782611) B13782611
theorem B1275047 : Blo 1273955 1275047 := bstep (se 1 (by rfl) ⟨956285, by rfl⟩ : syracuseStep 1275047 = 1912571) B1912571
theorem B18625783 : Blo 1273955 18625783 := bstep (se 1 (by rfl) ⟨13969337, by rfl⟩ : syracuseStep 18625783 = 27938675) B27938675
theorem B3224873 : Blo 1273955 3224873 := bstep (se 2 (by rfl) ⟨1209327, by rfl⟩ : syracuseStep 3224873 = 2418655) B2418655
theorem B4838723 : Blo 1273955 4838723 := bstep (se 1 (by rfl) ⟨3629042, by rfl⟩ : syracuseStep 4838723 = 7258085) B7258085
theorem B1635823 : Blo 1273955 1635823 := bstep (se 1 (by rfl) ⟨1226867, by rfl⟩ : syracuseStep 1635823 = 2453735) B2453735
theorem B1275495 : Blo 1273955 1275495 := bstep (se 1 (by rfl) ⟨956621, by rfl⟩ : syracuseStep 1275495 = 1913243) B1913243
theorem B31004369 : Blo 1273955 31004369 := bstep (se 2 (by rfl) ⟨11626638, by rfl⟩ : syracuseStep 31004369 = 23253277) B23253277
theorem B1275775 : Blo 1273955 1275775 := bstep (se 1 (by rfl) ⟨956831, by rfl⟩ : syracuseStep 1275775 = 1913663) B1913663
theorem B1275871 : Blo 1273955 1275871 := bstep (se 1 (by rfl) ⟨956903, by rfl⟩ : syracuseStep 1275871 = 1913807) B1913807
theorem B1275899 : Blo 1273955 1275899 := bstep (se 1 (by rfl) ⟨956924, by rfl⟩ : syracuseStep 1275899 = 1913849) B1913849
theorem B1275931 : Blo 1273955 1275931 := bstep (se 1 (by rfl) ⟨956948, by rfl⟩ : syracuseStep 1275931 = 1913897) B1913897
theorem B1275951 : Blo 1273955 1275951 := bstep (se 1 (by rfl) ⟨956963, by rfl⟩ : syracuseStep 1275951 = 1913927) B1913927
theorem B3225703 : Blo 1273955 3225703 := bstep (se 1 (by rfl) ⟨2419277, by rfl⟩ : syracuseStep 3225703 = 4838555) B4838555
theorem B5240971 : Blo 1273955 5240971 := bstep (se 1 (by rfl) ⟨3930728, by rfl⟩ : syracuseStep 5240971 = 7861457) B7861457
theorem B2152831 : Blo 1273955 2152831 := bstep (se 1 (by rfl) ⟨1614623, by rfl⟩ : syracuseStep 2152831 = 3229247) B3229247
theorem B62880623 : Blo 1273955 62880623 := bstep (se 1 (by rfl) ⟨47160467, by rfl⟩ : syracuseStep 62880623 = 94320935) B94320935
theorem B36780965 : Blo 1273955 36780965 := bstep (se 4 (by rfl) ⟨3448215, by rfl⟩ : syracuseStep 36780965 = 6896431) B6896431
theorem B6454241 : Blo 1273955 6454241 := bstep (se 2 (by rfl) ⟨2420340, by rfl⟩ : syracuseStep 6454241 = 4840681) B4840681
theorem B33119563 : Blo 1273955 33119563 := bstep (se 1 (by rfl) ⟨24839672, by rfl⟩ : syracuseStep 33119563 = 49679345) B49679345
theorem B7748951 : Blo 1273955 7748951 := bstep (se 1 (by rfl) ⟨5811713, by rfl⟩ : syracuseStep 7748951 = 11623427) B11623427
theorem B3628415 : Blo 1273955 3628415 := bstep (se 1 (by rfl) ⟨2721311, by rfl⟩ : syracuseStep 3628415 = 5442623) B5442623
theorem B2866607 : Blo 1273955 2866607 := bstep (se 1 (by rfl) ⟨2149955, by rfl⟩ : syracuseStep 2866607 = 4299911) B4299911
theorem B41344451 : Blo 1273955 41344451 := bstep (se 1 (by rfl) ⟨31008338, by rfl⟩ : syracuseStep 41344451 = 62016677) B62016677
theorem B3448595 : Blo 1273955 3448595 := bstep (se 1 (by rfl) ⟨2586446, by rfl⟩ : syracuseStep 3448595 = 5172893) B5172893
theorem B8724439 : Blo 1273955 8724439 := bstep (se 1 (by rfl) ⟨6543329, by rfl⟩ : syracuseStep 8724439 = 13086659) B13086659
theorem B4300775 : Blo 1273955 4300775 := bstep (se 1 (by rfl) ⟨3225581, by rfl⟩ : syracuseStep 4300775 = 6451163) B6451163
theorem B377323535 : Blo 1273955 377323535 := bstep (se 1 (by rfl) ⟨282992651, by rfl⟩ : syracuseStep 377323535 = 565985303) B565985303
theorem B18366547 : Blo 1273955 18366547 := bstep (se 1 (by rfl) ⟨13774910, by rfl⟩ : syracuseStep 18366547 = 27549821) B27549821
theorem B4300883 : Blo 1273955 4300883 := bstep (se 1 (by rfl) ⟨3225662, by rfl⟩ : syracuseStep 4300883 = 6451325) B6451325
theorem B4300937 : Blo 1273955 4300937 := bstep (se 2 (by rfl) ⟨1612851, by rfl⟩ : syracuseStep 4300937 = 3225703) B3225703
theorem B6987961 : Blo 1273955 6987961 := bstep (se 2 (by rfl) ⟨2620485, by rfl⟩ : syracuseStep 6987961 = 5240971) B5240971
theorem B13787327 : Blo 1273955 13787327 := bstep (se 1 (by rfl) ⟨10340495, by rfl⟩ : syracuseStep 13787327 = 20680991) B20680991
theorem B1614107 : Blo 1273955 1614107 := bstep (se 1 (by rfl) ⟨1210580, by rfl⟩ : syracuseStep 1614107 = 2421161) B2421161
theorem B2868191 : Blo 1273955 2868191 := bstep (se 1 (by rfl) ⟨2151143, by rfl⟩ : syracuseStep 2868191 = 4302287) B4302287
theorem B9675773 : Blo 1273955 9675773 := bstep (se 3 (by rfl) ⟨1814207, by rfl⟩ : syracuseStep 9675773 = 3628415) B3628415
theorem B20669579 : Blo 1273955 20669579 := bstep (se 1 (by rfl) ⟨15502184, by rfl⟩ : syracuseStep 20669579 = 31004369) B31004369
theorem B2868407 : Blo 1273955 2868407 := bstep (se 1 (by rfl) ⟨2151305, by rfl⟩ : syracuseStep 2868407 = 4302611) B4302611
theorem B14714273 : Blo 1273955 14714273 := bstep (se 2 (by rfl) ⟨5517852, by rfl⟩ : syracuseStep 14714273 = 11035705) B11035705
theorem B4843385 : Blo 1273955 4843385 := bstep (se 2 (by rfl) ⟨1816269, by rfl⟩ : syracuseStep 4843385 = 3632539) B3632539
theorem B41920415 : Blo 1273955 41920415 := bstep (se 1 (by rfl) ⟨31440311, by rfl⟩ : syracuseStep 41920415 = 62880623) B62880623
theorem B24520643 : Blo 1273955 24520643 := bstep (se 1 (by rfl) ⟨18390482, by rfl⟩ : syracuseStep 24520643 = 36780965) B36780965
theorem B2181097 : Blo 1273955 2181097 := bstep (se 2 (by rfl) ⟨817911, by rfl⟩ : syracuseStep 2181097 = 1635823) B1635823
theorem B4302827 : Blo 1273955 4302827 := bstep (se 1 (by rfl) ⟨3227120, by rfl⟩ : syracuseStep 4302827 = 6454241) B6454241
theorem B5441735 : Blo 1273955 5441735 := bstep (se 1 (by rfl) ⟨4081301, by rfl⟩ : syracuseStep 5441735 = 8162603) B8162603
theorem B1911071 : Blo 1273955 1911071 := bstep (se 1 (by rfl) ⟨1433303, by rfl⟩ : syracuseStep 1911071 = 2866607) B2866607
theorem B2869739 : Blo 1273955 2869739 := bstep (se 1 (by rfl) ⟨2152304, by rfl⟩ : syracuseStep 2869739 = 4304609) B4304609
theorem B1911515 : Blo 1273955 1911515 := bstep (se 1 (by rfl) ⟨1433636, by rfl⟩ : syracuseStep 1911515 = 2867273) B2867273
theorem B1911791 : Blo 1273955 1911791 := bstep (se 1 (by rfl) ⟨1433843, by rfl⟩ : syracuseStep 1911791 = 2867687) B2867687
theorem B1911803 : Blo 1273955 1911803 := bstep (se 1 (by rfl) ⟨1433852, by rfl⟩ : syracuseStep 1911803 = 2867705) B2867705
theorem B4844569 : Blo 1273955 4844569 := bstep (se 2 (by rfl) ⟨1816713, by rfl⟩ : syracuseStep 4844569 = 3633427) B3633427
theorem B1911863 : Blo 1273955 1911863 := bstep (se 1 (by rfl) ⟨1433897, by rfl⟩ : syracuseStep 1911863 = 2867795) B2867795
theorem B6122567 : Blo 1273955 6122567 := bstep (se 1 (by rfl) ⟨4591925, by rfl⟩ : syracuseStep 6122567 = 9183851) B9183851
theorem B2870441 : Blo 1273955 2870441 := bstep (se 2 (by rfl) ⟨1076415, by rfl⟩ : syracuseStep 2870441 = 2152831) B2152831
theorem B1911983 : Blo 1273955 1911983 := bstep (se 1 (by rfl) ⟨1433987, by rfl⟩ : syracuseStep 1911983 = 2867975) B2867975
theorem B17435857 : Blo 1273955 17435857 := bstep (se 2 (by rfl) ⟨6538446, by rfl⟩ : syracuseStep 17435857 = 13076893) B13076893
theorem B1912043 : Blo 1273955 1912043 := bstep (se 1 (by rfl) ⟨1434032, by rfl⟩ : syracuseStep 1912043 = 2868065) B2868065
theorem B9678203 : Blo 1273955 9678203 := bstep (se 1 (by rfl) ⟨7258652, by rfl⟩ : syracuseStep 9678203 = 14517305) B14517305
theorem B4304339 : Blo 1273955 4304339 := bstep (se 1 (by rfl) ⟨3228254, by rfl⟩ : syracuseStep 4304339 = 6456509) B6456509
theorem B2149915 : Blo 1273955 2149915 := bstep (se 1 (by rfl) ⟨1612436, by rfl⟩ : syracuseStep 2149915 = 3224873) B3224873
theorem B1912361 : Blo 1273955 1912361 := bstep (se 2 (by rfl) ⟨717135, by rfl⟩ : syracuseStep 1912361 = 1434271) B1434271
theorem B20663869 : Blo 1273955 20663869 := bstep (se 3 (by rfl) ⟨3874475, by rfl⟩ : syracuseStep 20663869 = 7748951) B7748951
theorem B22081319 : Blo 1273955 22081319 := bstep (se 1 (by rfl) ⟨16560989, by rfl⟩ : syracuseStep 22081319 = 33121979) B33121979
theorem B1912703 : Blo 1273955 1912703 := bstep (se 1 (by rfl) ⟨1434527, by rfl⟩ : syracuseStep 1912703 = 2869055) B2869055
theorem B4304879 : Blo 1273955 4304879 := bstep (se 1 (by rfl) ⟨3228659, by rfl⟩ : syracuseStep 4304879 = 6457319) B6457319
theorem B12251209 : Blo 1273955 12251209 := bstep (se 2 (by rfl) ⟨4594203, by rfl⟩ : syracuseStep 12251209 = 9188407) B9188407
theorem B1274111 : Blo 1273955 1274111 := bstep (se 1 (by rfl) ⟨955583, by rfl⟩ : syracuseStep 1274111 = 1911167) B1911167
theorem B24834377 : Blo 1273955 24834377 := bstep (se 2 (by rfl) ⟨9312891, by rfl⟩ : syracuseStep 24834377 = 18625783) B18625783
theorem B1274271 : Blo 1273955 1274271 := bstep (se 1 (by rfl) ⟨955703, by rfl⟩ : syracuseStep 1274271 = 1911407) B1911407
theorem B44159417 : Blo 1273955 44159417 := bstep (se 2 (by rfl) ⟨16559781, by rfl⟩ : syracuseStep 44159417 = 33119563) B33119563
theorem B1274415 : Blo 1273955 1274415 := bstep (se 1 (by rfl) ⟨955811, by rfl⟩ : syracuseStep 1274415 = 1911623) B1911623
theorem B9196253 : Blo 1273955 9196253 := bstep (se 3 (by rfl) ⟨1724297, by rfl⟩ : syracuseStep 9196253 = 3448595) B3448595
theorem B10334951 : Blo 1273955 10334951 := bstep (se 1 (by rfl) ⟨7751213, by rfl⟩ : syracuseStep 10334951 = 15502427) B15502427
theorem B1274815 : Blo 1273955 1274815 := bstep (se 1 (by rfl) ⟨956111, by rfl⟩ : syracuseStep 1274815 = 1912223) B1912223
theorem B27562967 : Blo 1273955 27562967 := bstep (se 1 (by rfl) ⟨20672225, by rfl⟩ : syracuseStep 27562967 = 41344451) B41344451
theorem B36770921 : Blo 1273955 36770921 := bstep (se 2 (by rfl) ⟨13789095, by rfl⟩ : syracuseStep 36770921 = 27578191) B27578191
theorem B1274991 : Blo 1273955 1274991 := bstep (se 1 (by rfl) ⟨956243, by rfl⟩ : syracuseStep 1274991 = 1912487) B1912487
theorem B1275007 : Blo 1273955 1275007 := bstep (se 1 (by rfl) ⟨956255, by rfl⟩ : syracuseStep 1275007 = 1912511) B1912511
theorem B1275071 : Blo 1273955 1275071 := bstep (se 1 (by rfl) ⟨956303, by rfl⟩ : syracuseStep 1275071 = 1912607) B1912607
theorem B5518543 : Blo 1273955 5518543 := bstep (se 1 (by rfl) ⟨4138907, by rfl⟩ : syracuseStep 5518543 = 8277815) B8277815
theorem B8172751 : Blo 1273955 8172751 := bstep (se 1 (by rfl) ⟨6129563, by rfl⟩ : syracuseStep 8172751 = 12259127) B12259127
theorem B8729855 : Blo 1273955 8729855 := bstep (se 1 (by rfl) ⟨6547391, by rfl⟩ : syracuseStep 8729855 = 13094783) B13094783
theorem B1275263 : Blo 1273955 1275263 := bstep (se 1 (by rfl) ⟨956447, by rfl⟩ : syracuseStep 1275263 = 1912895) B1912895
theorem B1275391 : Blo 1273955 1275391 := bstep (se 1 (by rfl) ⟨956543, by rfl⟩ : syracuseStep 1275391 = 1913087) B1913087
theorem B1275419 : Blo 1273955 1275419 := bstep (se 1 (by rfl) ⟨956564, by rfl⟩ : syracuseStep 1275419 = 1913129) B1913129
theorem B1275599 : Blo 1273955 1275599 := bstep (se 1 (by rfl) ⟨956699, by rfl⟩ : syracuseStep 1275599 = 1913399) B1913399
theorem B7755497 : Blo 1273955 7755497 := bstep (se 2 (by rfl) ⟨2908311, by rfl⟩ : syracuseStep 7755497 = 5816623) B5816623
theorem B4364051 : Blo 1273955 4364051 := bstep (se 1 (by rfl) ⟨3273038, by rfl⟩ : syracuseStep 4364051 = 6546077) B6546077
theorem B10884941 : Blo 1273955 10884941 := bstep (se 3 (by rfl) ⟨2040926, by rfl⟩ : syracuseStep 10884941 = 4081853) B4081853
theorem B1275759 : Blo 1273955 1275759 := bstep (se 1 (by rfl) ⟨956819, by rfl⟩ : syracuseStep 1275759 = 1913639) B1913639
theorem B5167019 : Blo 1273955 5167019 := bstep (se 1 (by rfl) ⟨3875264, by rfl⟩ : syracuseStep 5167019 = 7750529) B7750529
theorem B1275839 : Blo 1273955 1275839 := bstep (se 1 (by rfl) ⟨956879, by rfl⟩ : syracuseStep 1275839 = 1913759) B1913759
theorem B4839497 : Blo 1273955 4839497 := bstep (se 2 (by rfl) ⟨1814811, by rfl⟩ : syracuseStep 4839497 = 3629623) B3629623
theorem B3225815 : Blo 1273955 3225815 := bstep (se 1 (by rfl) ⟨2419361, by rfl⟩ : syracuseStep 3225815 = 4838723) B4838723
theorem B17455337 : Blo 1273955 17455337 := bstep (se 2 (by rfl) ⟨6545751, by rfl⟩ : syracuseStep 17455337 = 13091503) B13091503
theorem B20683127 : Blo 1273955 20683127 := bstep (se 1 (by rfl) ⟨15512345, by rfl⟩ : syracuseStep 20683127 = 31024691) B31024691
theorem B11623175 : Blo 1273955 11623175 := bstep (se 1 (by rfl) ⟨8717381, by rfl⟩ : syracuseStep 11623175 = 17434763) B17434763
theorem B37264187 : Blo 1273955 37264187 := bstep (se 1 (by rfl) ⟨27948140, by rfl⟩ : syracuseStep 37264187 = 55896281) B55896281
theorem B10894337 : Blo 1273955 10894337 := bstep (se 2 (by rfl) ⟨4085376, by rfl⟩ : syracuseStep 10894337 = 8170753) B8170753
theorem B7756955 : Blo 1273955 7756955 := bstep (se 1 (by rfl) ⟨5817716, by rfl⟩ : syracuseStep 7756955 = 11635433) B11635433
theorem B18373877 : Blo 1273955 18373877 := bstep (se 5 (by rfl) ⟨861275, by rfl⟩ : syracuseStep 18373877 = 1722551) B1722551
theorem B11632585 : Blo 1273955 11632585 := bstep (se 2 (by rfl) ⟨4362219, by rfl⟩ : syracuseStep 11632585 = 8724439) B8724439
theorem B2867183 : Blo 1273955 2867183 := bstep (se 1 (by rfl) ⟨2150387, by rfl⟩ : syracuseStep 2867183 = 4300775) B4300775
theorem B2867255 : Blo 1273955 2867255 := bstep (se 1 (by rfl) ⟨2150441, by rfl⟩ : syracuseStep 2867255 = 4300883) B4300883
theorem B2867291 : Blo 1273955 2867291 := bstep (se 1 (by rfl) ⟨2150468, by rfl⟩ : syracuseStep 2867291 = 4300937) B4300937
theorem B16334945 : Blo 1273955 16334945 := bstep (se 2 (by rfl) ⟨6125604, by rfl⟩ : syracuseStep 16334945 = 12251209) B12251209
theorem B9191551 : Blo 1273955 9191551 := bstep (se 1 (by rfl) ⟨6893663, by rfl⟩ : syracuseStep 9191551 = 13787327) B13787327
theorem B16326845 : Blo 1273955 16326845 := bstep (se 3 (by rfl) ⟨3061283, by rfl⟩ : syracuseStep 16326845 = 6122567) B6122567
theorem B16556251 : Blo 1273955 16556251 := bstep (se 1 (by rfl) ⟨12417188, by rfl⟩ : syracuseStep 16556251 = 24834377) B24834377
theorem B6889967 : Blo 1273955 6889967 := bstep (se 1 (by rfl) ⟨5167475, by rfl⟩ : syracuseStep 6889967 = 10334951) B10334951
theorem B18375311 : Blo 1273955 18375311 := bstep (se 1 (by rfl) ⟨13781483, by rfl⟩ : syracuseStep 18375311 = 27562967) B27562967
theorem B13779719 : Blo 1273955 13779719 := bstep (se 1 (by rfl) ⟨10334789, by rfl⟩ : syracuseStep 13779719 = 20669579) B20669579
theorem B5170331 : Blo 1273955 5170331 := bstep (se 1 (by rfl) ⟨3877748, by rfl⟩ : syracuseStep 5170331 = 7755497) B7755497
theorem B3228923 : Blo 1273955 3228923 := bstep (se 1 (by rfl) ⟨2421692, by rfl⟩ : syracuseStep 3228923 = 4843385) B4843385
theorem B2868551 : Blo 1273955 2868551 := bstep (se 1 (by rfl) ⟨2151413, by rfl⟩ : syracuseStep 2868551 = 4302827) B4302827
theorem B13788751 : Blo 1273955 13788751 := bstep (se 1 (by rfl) ⟨10341563, by rfl⟩ : syracuseStep 13788751 = 20683127) B20683127
theorem B7358057 : Blo 1273955 7358057 := bstep (se 2 (by rfl) ⟨2759271, by rfl⟩ : syracuseStep 7358057 = 5518543) B5518543
theorem B10897001 : Blo 1273955 10897001 := bstep (se 2 (by rfl) ⟨4086375, by rfl⟩ : syracuseStep 10897001 = 8172751) B8172751
theorem B27551825 : Blo 1273955 27551825 := bstep (se 2 (by rfl) ⟨10331934, by rfl⟩ : syracuseStep 27551825 = 20663869) B20663869
theorem B5171303 : Blo 1273955 5171303 := bstep (se 1 (by rfl) ⟨3878477, by rfl⟩ : syracuseStep 5171303 = 7756955) B7756955
theorem B12249251 : Blo 1273955 12249251 := bstep (se 1 (by rfl) ⟨9186938, by rfl⟩ : syracuseStep 12249251 = 18373877) B18373877
theorem B2869559 : Blo 1273955 2869559 := bstep (se 1 (by rfl) ⟨2152169, by rfl⟩ : syracuseStep 2869559 = 4304339) B4304339
theorem B15510113 : Blo 1273955 15510113 := bstep (se 2 (by rfl) ⟨5816292, by rfl⟩ : syracuseStep 15510113 = 11632585) B11632585
theorem B1911455 : Blo 1273955 1911455 := bstep (se 1 (by rfl) ⟨1433591, by rfl⟩ : syracuseStep 1911455 = 2867183) B2867183
theorem B2869919 : Blo 1273955 2869919 := bstep (se 1 (by rfl) ⟨2152439, by rfl⟩ : syracuseStep 2869919 = 4304879) B4304879
theorem B24488729 : Blo 1273955 24488729 := bstep (se 2 (by rfl) ⟨9183273, by rfl⟩ : syracuseStep 24488729 = 18366547) B18366547
theorem B9317281 : Blo 1273955 9317281 := bstep (se 2 (by rfl) ⟨3493980, by rfl⟩ : syracuseStep 9317281 = 6987961) B6987961
theorem B6130835 : Blo 1273955 6130835 := bstep (se 1 (by rfl) ⟨4598126, by rfl⟩ : syracuseStep 6130835 = 9196253) B9196253
theorem B1912127 : Blo 1273955 1912127 := bstep (se 1 (by rfl) ⟨1434095, by rfl⟩ : syracuseStep 1912127 = 2868191) B2868191
theorem B6450515 : Blo 1273955 6450515 := bstep (se 1 (by rfl) ⟨4837886, by rfl⟩ : syracuseStep 6450515 = 9675773) B9675773
theorem B24513947 : Blo 1273955 24513947 := bstep (se 1 (by rfl) ⟨18385460, by rfl⟩ : syracuseStep 24513947 = 36770921) B36770921
theorem B4304285 : Blo 1273955 4304285 := bstep (se 3 (by rfl) ⟨807053, by rfl⟩ : syracuseStep 4304285 = 1614107) B1614107
theorem B1912271 : Blo 1273955 1912271 := bstep (se 1 (by rfl) ⟨1434203, by rfl⟩ : syracuseStep 1912271 = 2868407) B2868407
theorem B5819903 : Blo 1273955 5819903 := bstep (se 1 (by rfl) ⟨4364927, by rfl⟩ : syracuseStep 5819903 = 8729855) B8729855
theorem B9809515 : Blo 1273955 9809515 := bstep (se 1 (by rfl) ⟨7357136, by rfl⟩ : syracuseStep 9809515 = 14714273) B14714273
theorem B27946943 : Blo 1273955 27946943 := bstep (se 1 (by rfl) ⟨20960207, by rfl⟩ : syracuseStep 27946943 = 41920415) B41920415
theorem B3444679 : Blo 1273955 3444679 := bstep (se 1 (by rfl) ⟨2583509, by rfl⟩ : syracuseStep 3444679 = 5167019) B5167019
theorem B16347095 : Blo 1273955 16347095 := bstep (se 1 (by rfl) ⟨12260321, by rfl⟩ : syracuseStep 16347095 = 24520643) B24520643
theorem B6459425 : Blo 1273955 6459425 := bstep (se 2 (by rfl) ⟨2422284, by rfl⟩ : syracuseStep 6459425 = 4844569) B4844569
theorem B2150543 : Blo 1273955 2150543 := bstep (se 1 (by rfl) ⟨1612907, by rfl⟩ : syracuseStep 2150543 = 3225815) B3225815
theorem B11636891 : Blo 1273955 11636891 := bstep (se 1 (by rfl) ⟨8727668, by rfl⟩ : syracuseStep 11636891 = 17455337) B17455337
theorem B1274047 : Blo 1273955 1274047 := bstep (se 1 (by rfl) ⟨955535, by rfl⟩ : syracuseStep 1274047 = 1911071) B1911071
theorem B1913159 : Blo 1273955 1913159 := bstep (se 1 (by rfl) ⟨1434869, by rfl⟩ : syracuseStep 1913159 = 2869739) B2869739
theorem B1274343 : Blo 1273955 1274343 := bstep (se 1 (by rfl) ⟨955757, by rfl⟩ : syracuseStep 1274343 = 1911515) B1911515
theorem B24842791 : Blo 1273955 24842791 := bstep (se 1 (by rfl) ⟨18632093, by rfl⟩ : syracuseStep 24842791 = 37264187) B37264187
theorem B1274527 : Blo 1273955 1274527 := bstep (se 1 (by rfl) ⟨955895, by rfl⟩ : syracuseStep 1274527 = 1911791) B1911791
theorem B1274535 : Blo 1273955 1274535 := bstep (se 1 (by rfl) ⟨955901, by rfl⟩ : syracuseStep 1274535 = 1911803) B1911803
theorem B7262891 : Blo 1273955 7262891 := bstep (se 1 (by rfl) ⟨5447168, by rfl⟩ : syracuseStep 7262891 = 10894337) B10894337
theorem B1274575 : Blo 1273955 1274575 := bstep (se 1 (by rfl) ⟨955931, by rfl⟩ : syracuseStep 1274575 = 1911863) B1911863
theorem B11637469 : Blo 1273955 11637469 := bstep (se 3 (by rfl) ⟨2182025, by rfl⟩ : syracuseStep 11637469 = 4364051) B4364051
theorem B1913627 : Blo 1273955 1913627 := bstep (se 1 (by rfl) ⟨1435220, by rfl⟩ : syracuseStep 1913627 = 2870441) B2870441
theorem B1274655 : Blo 1273955 1274655 := bstep (se 1 (by rfl) ⟨955991, by rfl⟩ : syracuseStep 1274655 = 1911983) B1911983
theorem B1274695 : Blo 1273955 1274695 := bstep (se 1 (by rfl) ⟨956021, by rfl⟩ : syracuseStep 1274695 = 1912043) B1912043
theorem B6452135 : Blo 1273955 6452135 := bstep (se 1 (by rfl) ⟨4839101, by rfl⟩ : syracuseStep 6452135 = 9678203) B9678203
theorem B1274907 : Blo 1273955 1274907 := bstep (se 1 (by rfl) ⟨956180, by rfl⟩ : syracuseStep 1274907 = 1912361) B1912361
theorem B1275135 : Blo 1273955 1275135 := bstep (se 1 (by rfl) ⟨956351, by rfl⟩ : syracuseStep 1275135 = 1912703) B1912703
theorem B251549023 : Blo 1273955 251549023 := bstep (se 1 (by rfl) ⟨188661767, by rfl⟩ : syracuseStep 251549023 = 377323535) B377323535
theorem B29439611 : Blo 1273955 29439611 := bstep (se 1 (by rfl) ⟨22079708, by rfl⟩ : syracuseStep 29439611 = 44159417) B44159417
theorem B7256627 : Blo 1273955 7256627 := bstep (se 1 (by rfl) ⟨5442470, by rfl⟩ : syracuseStep 7256627 = 10884941) B10884941
theorem B3226331 : Blo 1273955 3226331 := bstep (se 1 (by rfl) ⟨2419748, by rfl⟩ : syracuseStep 3226331 = 4839497) B4839497
theorem B3627823 : Blo 1273955 3627823 := bstep (se 1 (by rfl) ⟨2720867, by rfl⟩ : syracuseStep 3627823 = 5441735) B5441735
theorem B23247809 : Blo 1273955 23247809 := bstep (se 2 (by rfl) ⟨8717928, by rfl⟩ : syracuseStep 23247809 = 17435857) B17435857
theorem B7748783 : Blo 1273955 7748783 := bstep (se 1 (by rfl) ⟨5811587, by rfl⟩ : syracuseStep 7748783 = 11623175) B11623175
theorem B2866553 : Blo 1273955 2866553 := bstep (se 2 (by rfl) ⟨1074957, by rfl⟩ : syracuseStep 2866553 = 2149915) B2149915
theorem B14720879 : Blo 1273955 14720879 := bstep (se 1 (by rfl) ⟨11040659, by rfl⟩ : syracuseStep 14720879 = 22081319) B22081319
theorem B11632517 : Blo 1273955 11632517 := bstep (se 4 (by rfl) ⟨1090548, by rfl⟩ : syracuseStep 11632517 = 2181097) B2181097
theorem B1433695 : Blo 1273955 1433695 := bstep (se 1 (by rfl) ⟨1075271, by rfl⟩ : syracuseStep 1433695 = 2150543) B2150543
theorem B7757927 : Blo 1273955 7757927 := bstep (se 1 (by rfl) ⟨5818445, by rfl⟩ : syracuseStep 7757927 = 11636891) B11636891
theorem B12255401 : Blo 1273955 12255401 := bstep (se 2 (by rfl) ⟨4595775, by rfl⟩ : syracuseStep 12255401 = 9191551) B9191551
theorem B4841927 : Blo 1273955 4841927 := bstep (se 1 (by rfl) ⟨3631445, by rfl⟩ : syracuseStep 4841927 = 7262891) B7262891
theorem B4301423 : Blo 1273955 4301423 := bstep (se 1 (by rfl) ⟨3226067, by rfl⟩ : syracuseStep 4301423 = 6452135) B6452135
theorem B15516625 : Blo 1273955 15516625 := bstep (se 2 (by rfl) ⟨5818734, by rfl⟩ : syracuseStep 15516625 = 11637469) B11637469
theorem B18367883 : Blo 1273955 18367883 := bstep (se 1 (by rfl) ⟨13775912, by rfl⟩ : syracuseStep 18367883 = 27551825) B27551825
theorem B10340075 : Blo 1273955 10340075 := bstep (se 1 (by rfl) ⟨7755056, by rfl⟩ : syracuseStep 10340075 = 15510113) B15510113
theorem B335398697 : Blo 1273955 335398697 := bstep (se 2 (by rfl) ⟨125774511, by rfl⟩ : syracuseStep 335398697 = 251549023) B251549023
theorem B18385001 : Blo 1273955 18385001 := bstep (se 2 (by rfl) ⟨6894375, by rfl⟩ : syracuseStep 18385001 = 13788751) B13788751
theorem B1911035 : Blo 1273955 1911035 := bstep (se 1 (by rfl) ⟨1433276, by rfl⟩ : syracuseStep 1911035 = 2866553) B2866553
theorem B2869523 : Blo 1273955 2869523 := bstep (se 1 (by rfl) ⟨2152142, by rfl⟩ : syracuseStep 2869523 = 4304285) B4304285
theorem B18631295 : Blo 1273955 18631295 := bstep (se 1 (by rfl) ⟨13973471, by rfl⟩ : syracuseStep 18631295 = 27946943) B27946943
theorem B10898063 : Blo 1273955 10898063 := bstep (se 1 (by rfl) ⟨8173547, by rfl⟩ : syracuseStep 10898063 = 16347095) B16347095
theorem B1911503 : Blo 1273955 1911503 := bstep (se 1 (by rfl) ⟨1433627, by rfl⟩ : syracuseStep 1911503 = 2867255) B2867255
theorem B1911527 : Blo 1273955 1911527 := bstep (se 1 (by rfl) ⟨1433645, by rfl⟩ : syracuseStep 1911527 = 2867291) B2867291
theorem B10889963 : Blo 1273955 10889963 := bstep (se 1 (by rfl) ⟨8167472, by rfl⟩ : syracuseStep 10889963 = 16334945) B16334945
theorem B12250207 : Blo 1273955 12250207 := bstep (se 1 (by rfl) ⟨9187655, by rfl⟩ : syracuseStep 12250207 = 18375311) B18375311
theorem B9186479 : Blo 1273955 9186479 := bstep (se 1 (by rfl) ⟨6889859, by rfl⟩ : syracuseStep 9186479 = 13779719) B13779719
theorem B52317413 : Blo 1273955 52317413 := bstep (se 4 (by rfl) ⟨4904757, by rfl⟩ : syracuseStep 52317413 = 9809515) B9809515
theorem B1912367 : Blo 1273955 1912367 := bstep (se 1 (by rfl) ⟨1434275, by rfl⟩ : syracuseStep 1912367 = 2868551) B2868551
theorem B4837097 : Blo 1273955 4837097 := bstep (se 2 (by rfl) ⟨1813911, by rfl⟩ : syracuseStep 4837097 = 3627823) B3627823
theorem B12423041 : Blo 1273955 12423041 := bstep (se 2 (by rfl) ⟨4658640, by rfl⟩ : syracuseStep 12423041 = 9317281) B9317281
theorem B1913039 : Blo 1273955 1913039 := bstep (se 1 (by rfl) ⟨1434779, by rfl⟩ : syracuseStep 1913039 = 2869559) B2869559
theorem B4837751 : Blo 1273955 4837751 := bstep (se 1 (by rfl) ⟨3628313, by rfl⟩ : syracuseStep 4837751 = 7256627) B7256627
theorem B1274303 : Blo 1273955 1274303 := bstep (se 1 (by rfl) ⟨955727, by rfl⟩ : syracuseStep 1274303 = 1911455) B1911455
theorem B1913279 : Blo 1273955 1913279 := bstep (se 1 (by rfl) ⟨1434959, by rfl⟩ : syracuseStep 1913279 = 2869919) B2869919
theorem B2150887 : Blo 1273955 2150887 := bstep (se 1 (by rfl) ⟨1613165, by rfl⟩ : syracuseStep 2150887 = 3226331) B3226331
theorem B5165855 : Blo 1273955 5165855 := bstep (se 1 (by rfl) ⟨3874391, by rfl⟩ : syracuseStep 5165855 = 7748783) B7748783
theorem B1274751 : Blo 1273955 1274751 := bstep (se 1 (by rfl) ⟨956063, by rfl⟩ : syracuseStep 1274751 = 1912127) B1912127
theorem B1274847 : Blo 1273955 1274847 := bstep (se 1 (by rfl) ⟨956135, by rfl⟩ : syracuseStep 1274847 = 1912271) B1912271
theorem B3879935 : Blo 1273955 3879935 := bstep (se 1 (by rfl) ⟨2909951, by rfl⟩ : syracuseStep 3879935 = 5819903) B5819903
theorem B7755011 : Blo 1273955 7755011 := bstep (se 1 (by rfl) ⟨5816258, by rfl⟩ : syracuseStep 7755011 = 11632517) B11632517
theorem B4592905 : Blo 1273955 4592905 := bstep (se 2 (by rfl) ⟨1722339, by rfl⟩ : syracuseStep 4592905 = 3444679) B3444679
theorem B4306283 : Blo 1273955 4306283 := bstep (se 1 (by rfl) ⟨3229712, by rfl⟩ : syracuseStep 4306283 = 6459425) B6459425
theorem B10884563 : Blo 1273955 10884563 := bstep (se 1 (by rfl) ⟨8163422, by rfl⟩ : syracuseStep 10884563 = 16326845) B16326845
theorem B132494885 : Blo 1273955 132494885 := bstep (se 4 (by rfl) ⟨12421395, by rfl⟩ : syracuseStep 132494885 = 24842791) B24842791
theorem B1275439 : Blo 1273955 1275439 := bstep (se 1 (by rfl) ⟨956579, by rfl⟩ : syracuseStep 1275439 = 1913159) B1913159
theorem B22075001 : Blo 1273955 22075001 := bstep (se 2 (by rfl) ⟨8278125, by rfl⟩ : syracuseStep 22075001 = 16556251) B16556251
theorem B4593311 : Blo 1273955 4593311 := bstep (se 1 (by rfl) ⟨3444983, by rfl⟩ : syracuseStep 4593311 = 6889967) B6889967
theorem B1275751 : Blo 1273955 1275751 := bstep (se 1 (by rfl) ⟨956813, by rfl⟩ : syracuseStep 1275751 = 1913627) B1913627
theorem B3446887 : Blo 1273955 3446887 := bstep (se 1 (by rfl) ⟨2585165, by rfl⟩ : syracuseStep 3446887 = 5170331) B5170331
theorem B2152615 : Blo 1273955 2152615 := bstep (se 1 (by rfl) ⟨1614461, by rfl⟩ : syracuseStep 2152615 = 3228923) B3228923
theorem B4905371 : Blo 1273955 4905371 := bstep (se 1 (by rfl) ⟨3679028, by rfl⟩ : syracuseStep 4905371 = 7358057) B7358057
theorem B7264667 : Blo 1273955 7264667 := bstep (se 1 (by rfl) ⟨5448500, by rfl⟩ : syracuseStep 7264667 = 10897001) B10897001
theorem B19626407 : Blo 1273955 19626407 := bstep (se 1 (by rfl) ⟨14719805, by rfl⟩ : syracuseStep 19626407 = 29439611) B29439611
theorem B3447535 : Blo 1273955 3447535 := bstep (se 1 (by rfl) ⟨2585651, by rfl⟩ : syracuseStep 3447535 = 5171303) B5171303
theorem B8166167 : Blo 1273955 8166167 := bstep (se 1 (by rfl) ⟨6124625, by rfl⟩ : syracuseStep 8166167 = 12249251) B12249251
theorem B16325819 : Blo 1273955 16325819 := bstep (se 1 (by rfl) ⟨12244364, by rfl⟩ : syracuseStep 16325819 = 24488729) B24488729
theorem B15498539 : Blo 1273955 15498539 := bstep (se 1 (by rfl) ⟨11623904, by rfl⟩ : syracuseStep 15498539 = 23247809) B23247809
theorem B4087223 : Blo 1273955 4087223 := bstep (se 1 (by rfl) ⟨3065417, by rfl⟩ : syracuseStep 4087223 = 6130835) B6130835
theorem B4300343 : Blo 1273955 4300343 := bstep (se 1 (by rfl) ⟨3225257, by rfl⟩ : syracuseStep 4300343 = 6450515) B6450515
theorem B16342631 : Blo 1273955 16342631 := bstep (se 1 (by rfl) ⟨12256973, by rfl⟩ : syracuseStep 16342631 = 24513947) B24513947
theorem B9813919 : Blo 1273955 9813919 := bstep (se 1 (by rfl) ⟨7360439, by rfl⟩ : syracuseStep 9813919 = 14720879) B14720879
theorem B4595849 : Blo 1273955 4595849 := bstep (se 2 (by rfl) ⟨1723443, by rfl⟩ : syracuseStep 4595849 = 3446887) B3446887
theorem B3227951 : Blo 1273955 3227951 := bstep (se 1 (by rfl) ⟨2420963, by rfl⟩ : syracuseStep 3227951 = 4841927) B4841927
theorem B2867615 : Blo 1273955 2867615 := bstep (se 1 (by rfl) ⟨2150711, by rfl⟩ : syracuseStep 2867615 = 4301423) B4301423
theorem B2867849 : Blo 1273955 2867849 := bstep (se 2 (by rfl) ⟨1075443, by rfl⟩ : syracuseStep 2867849 = 2150887) B2150887
theorem B5170007 : Blo 1273955 5170007 := bstep (se 1 (by rfl) ⟨3877505, by rfl⟩ : syracuseStep 5170007 = 7755011) B7755011
theorem B4596713 : Blo 1273955 4596713 := bstep (se 2 (by rfl) ⟨1723767, by rfl⟩ : syracuseStep 4596713 = 3447535) B3447535
theorem B24495493 : Blo 1273955 24495493 := bstep (se 4 (by rfl) ⟨2296452, by rfl⟩ : syracuseStep 24495493 = 4592905) B4592905
theorem B12256667 : Blo 1273955 12256667 := bstep (se 1 (by rfl) ⟨9192500, by rfl⟩ : syracuseStep 12256667 = 18385001) B18385001
theorem B4843111 : Blo 1273955 4843111 := bstep (se 1 (by rfl) ⟨3632333, by rfl⟩ : syracuseStep 4843111 = 7264667) B7264667
theorem B13084271 : Blo 1273955 13084271 := bstep (se 1 (by rfl) ⟨9813203, by rfl⟩ : syracuseStep 13084271 = 19626407) B19626407
theorem B12420863 : Blo 1273955 12420863 := bstep (se 1 (by rfl) ⟨9315647, by rfl⟩ : syracuseStep 12420863 = 18631295) B18631295
theorem B7259975 : Blo 1273955 7259975 := bstep (se 1 (by rfl) ⟨5444981, by rfl⟩ : syracuseStep 7259975 = 10889963) B10889963
theorem B10332359 : Blo 1273955 10332359 := bstep (se 1 (by rfl) ⟨7749269, by rfl⟩ : syracuseStep 10332359 = 15498539) B15498539
theorem B13085225 : Blo 1273955 13085225 := bstep (se 2 (by rfl) ⟨4906959, by rfl⟩ : syracuseStep 13085225 = 9813919) B9813919
theorem B5171951 : Blo 1273955 5171951 := bstep (se 1 (by rfl) ⟨3878963, by rfl⟩ : syracuseStep 5171951 = 7757927) B7757927
theorem B8170267 : Blo 1273955 8170267 := bstep (se 1 (by rfl) ⟨6127700, by rfl⟩ : syracuseStep 8170267 = 12255401) B12255401
theorem B1911593 : Blo 1273955 1911593 := bstep (se 2 (by rfl) ⟨716847, by rfl⟩ : syracuseStep 1911593 = 1433695) B1433695
theorem B2870153 : Blo 1273955 2870153 := bstep (se 2 (by rfl) ⟨1076307, by rfl⟩ : syracuseStep 2870153 = 2152615) B2152615
theorem B3443903 : Blo 1273955 3443903 := bstep (se 1 (by rfl) ⟨2582927, by rfl⟩ : syracuseStep 3443903 = 5165855) B5165855
theorem B2870855 : Blo 1273955 2870855 := bstep (se 1 (by rfl) ⟨2153141, by rfl⟩ : syracuseStep 2870855 = 4306283) B4306283
theorem B88329923 : Blo 1273955 88329923 := bstep (se 1 (by rfl) ⟨66247442, by rfl⟩ : syracuseStep 88329923 = 132494885) B132494885
theorem B14716667 : Blo 1273955 14716667 := bstep (se 1 (by rfl) ⟨11037500, by rfl⟩ : syracuseStep 14716667 = 22075001) B22075001
theorem B6893383 : Blo 1273955 6893383 := bstep (se 1 (by rfl) ⟨5170037, by rfl⟩ : syracuseStep 6893383 = 10340075) B10340075
theorem B20688833 : Blo 1273955 20688833 := bstep (se 2 (by rfl) ⟨7758312, by rfl⟩ : syracuseStep 20688833 = 15516625) B15516625
theorem B1274023 : Blo 1273955 1274023 := bstep (se 1 (by rfl) ⟨955517, by rfl⟩ : syracuseStep 1274023 = 1911035) B1911035
theorem B1913015 : Blo 1273955 1913015 := bstep (se 1 (by rfl) ⟨1434761, by rfl⟩ : syracuseStep 1913015 = 2869523) B2869523
theorem B1274335 : Blo 1273955 1274335 := bstep (se 1 (by rfl) ⟨955751, by rfl⟩ : syracuseStep 1274335 = 1911503) B1911503
theorem B1274351 : Blo 1273955 1274351 := bstep (se 1 (by rfl) ⟨955763, by rfl⟩ : syracuseStep 1274351 = 1911527) B1911527
theorem B5444111 : Blo 1273955 5444111 := bstep (se 1 (by rfl) ⟨4083083, by rfl⟩ : syracuseStep 5444111 = 8166167) B8166167
theorem B6124319 : Blo 1273955 6124319 := bstep (se 1 (by rfl) ⟨4593239, by rfl⟩ : syracuseStep 6124319 = 9186479) B9186479
theorem B10883879 : Blo 1273955 10883879 := bstep (se 1 (by rfl) ⟨8162909, by rfl⟩ : syracuseStep 10883879 = 16325819) B16325819
theorem B34878275 : Blo 1273955 34878275 := bstep (se 1 (by rfl) ⟨26158706, by rfl⟩ : syracuseStep 34878275 = 52317413) B52317413
theorem B2724815 : Blo 1273955 2724815 := bstep (se 1 (by rfl) ⟨2043611, by rfl⟩ : syracuseStep 2724815 = 4087223) B4087223
theorem B1274911 : Blo 1273955 1274911 := bstep (se 1 (by rfl) ⟨956183, by rfl⟩ : syracuseStep 1274911 = 1912367) B1912367
theorem B3224731 : Blo 1273955 3224731 := bstep (se 1 (by rfl) ⟨2418548, by rfl⟩ : syracuseStep 3224731 = 4837097) B4837097
theorem B1275359 : Blo 1273955 1275359 := bstep (se 1 (by rfl) ⟨956519, by rfl⟩ : syracuseStep 1275359 = 1913039) B1913039
theorem B3225167 : Blo 1273955 3225167 := bstep (se 1 (by rfl) ⟨2418875, by rfl⟩ : syracuseStep 3225167 = 4837751) B4837751
theorem B1275519 : Blo 1273955 1275519 := bstep (se 1 (by rfl) ⟨956639, by rfl⟩ : syracuseStep 1275519 = 1913279) B1913279
theorem B2586623 : Blo 1273955 2586623 := bstep (se 1 (by rfl) ⟨1939967, by rfl⟩ : syracuseStep 2586623 = 3879935) B3879935
theorem B12245255 : Blo 1273955 12245255 := bstep (se 1 (by rfl) ⟨9183941, by rfl⟩ : syracuseStep 12245255 = 18367883) B18367883
theorem B7256375 : Blo 1273955 7256375 := bstep (se 1 (by rfl) ⟨5442281, by rfl⟩ : syracuseStep 7256375 = 10884563) B10884563
theorem B13080989 : Blo 1273955 13080989 := bstep (se 3 (by rfl) ⟨2452685, by rfl⟩ : syracuseStep 13080989 = 4905371) B4905371
theorem B3062207 : Blo 1273955 3062207 := bstep (se 1 (by rfl) ⟨2296655, by rfl⟩ : syracuseStep 3062207 = 4593311) B4593311
theorem B223599131 : Blo 1273955 223599131 := bstep (se 1 (by rfl) ⟨167699348, by rfl⟩ : syracuseStep 223599131 = 335398697) B335398697
theorem B16333609 : Blo 1273955 16333609 := bstep (se 2 (by rfl) ⟨6125103, by rfl⟩ : syracuseStep 16333609 = 12250207) B12250207
theorem B7265375 : Blo 1273955 7265375 := bstep (se 1 (by rfl) ⟨5449031, by rfl⟩ : syracuseStep 7265375 = 10898063) B10898063
theorem B2866895 : Blo 1273955 2866895 := bstep (se 1 (by rfl) ⟨2150171, by rfl⟩ : syracuseStep 2866895 = 4300343) B4300343
theorem B10895087 : Blo 1273955 10895087 := bstep (se 1 (by rfl) ⟨8171315, by rfl⟩ : syracuseStep 10895087 = 16342631) B16342631
theorem B8282027 : Blo 1273955 8282027 := bstep (se 1 (by rfl) ⟨6211520, by rfl⟩ : syracuseStep 8282027 = 12423041) B12423041
theorem B3063899 : Blo 1273955 3063899 := bstep (se 1 (by rfl) ⟨2297924, by rfl⟩ : syracuseStep 3063899 = 4595849) B4595849
theorem B3629407 : Blo 1273955 3629407 := bstep (se 1 (by rfl) ⟨2722055, by rfl⟩ : syracuseStep 3629407 = 5444111) B5444111
theorem B3064475 : Blo 1273955 3064475 := bstep (se 1 (by rfl) ⟨2298356, by rfl⟩ : syracuseStep 3064475 = 4596713) B4596713
theorem B2041471 : Blo 1273955 2041471 := bstep (se 1 (by rfl) ⟨1531103, by rfl⟩ : syracuseStep 2041471 = 3062207) B3062207
theorem B4843583 : Blo 1273955 4843583 := bstep (se 1 (by rfl) ⟨3632687, by rfl⟩ : syracuseStep 4843583 = 7265375) B7265375
theorem B2295935 : Blo 1273955 2295935 := bstep (se 1 (by rfl) ⟨1721951, by rfl⟩ : syracuseStep 2295935 = 3443903) B3443903
theorem B6457481 : Blo 1273955 6457481 := bstep (se 2 (by rfl) ⟨2421555, by rfl⟩ : syracuseStep 6457481 = 4843111) B4843111
theorem B58886615 : Blo 1273955 58886615 := bstep (se 1 (by rfl) ⟨44164961, by rfl⟩ : syracuseStep 58886615 = 88329923) B88329923
theorem B1911263 : Blo 1273955 1911263 := bstep (se 1 (by rfl) ⟨1433447, by rfl⟩ : syracuseStep 1911263 = 2866895) B2866895
theorem B1911743 : Blo 1273955 1911743 := bstep (se 1 (by rfl) ⟨1433807, by rfl⟩ : syracuseStep 1911743 = 2867615) B2867615
theorem B1911899 : Blo 1273955 1911899 := bstep (se 1 (by rfl) ⟨1433924, by rfl⟩ : syracuseStep 1911899 = 2867849) B2867849
theorem B4082879 : Blo 1273955 4082879 := bstep (se 1 (by rfl) ⟨3062159, by rfl⟩ : syracuseStep 4082879 = 6124319) B6124319
theorem B23252183 : Blo 1273955 23252183 := bstep (se 1 (by rfl) ⟨17439137, by rfl⟩ : syracuseStep 23252183 = 34878275) B34878275
theorem B8171111 : Blo 1273955 8171111 := bstep (se 1 (by rfl) ⟨6128333, by rfl⟩ : syracuseStep 8171111 = 12256667) B12256667
theorem B2150111 : Blo 1273955 2150111 := bstep (se 1 (by rfl) ⟨1612583, by rfl⟩ : syracuseStep 2150111 = 3225167) B3225167
theorem B21778145 : Blo 1273955 21778145 := bstep (se 2 (by rfl) ⟨8166804, by rfl⟩ : syracuseStep 21778145 = 16333609) B16333609
theorem B8163503 : Blo 1273955 8163503 := bstep (se 1 (by rfl) ⟨6122627, by rfl⟩ : syracuseStep 8163503 = 12245255) B12245255
theorem B4837583 : Blo 1273955 4837583 := bstep (se 1 (by rfl) ⟨3628187, by rfl⟩ : syracuseStep 4837583 = 7256375) B7256375
theorem B8720659 : Blo 1273955 8720659 := bstep (se 1 (by rfl) ⟨6540494, by rfl⟩ : syracuseStep 8720659 = 13080989) B13080989
theorem B149066087 : Blo 1273955 149066087 := bstep (se 1 (by rfl) ⟨111799565, by rfl⟩ : syracuseStep 149066087 = 223599131) B223599131
theorem B1274395 : Blo 1273955 1274395 := bstep (se 1 (by rfl) ⟨955796, by rfl⟩ : syracuseStep 1274395 = 1911593) B1911593
theorem B1913435 : Blo 1273955 1913435 := bstep (se 1 (by rfl) ⟨1435076, by rfl⟩ : syracuseStep 1913435 = 2870153) B2870153
theorem B39244445 : Blo 1273955 39244445 := bstep (se 3 (by rfl) ⟨7358333, by rfl⟩ : syracuseStep 39244445 = 14716667) B14716667
theorem B1913903 : Blo 1273955 1913903 := bstep (se 1 (by rfl) ⟨1435427, by rfl⟩ : syracuseStep 1913903 = 2870855) B2870855
theorem B7263391 : Blo 1273955 7263391 := bstep (se 1 (by rfl) ⟨5447543, by rfl⟩ : syracuseStep 7263391 = 10895087) B10895087
theorem B13792555 : Blo 1273955 13792555 := bstep (se 1 (by rfl) ⟨10344416, by rfl⟩ : syracuseStep 13792555 = 20688833) B20688833
theorem B1275343 : Blo 1273955 1275343 := bstep (se 1 (by rfl) ⟨956507, by rfl⟩ : syracuseStep 1275343 = 1913015) B1913015
theorem B2151967 : Blo 1273955 2151967 := bstep (se 1 (by rfl) ⟨1613975, by rfl⟩ : syracuseStep 2151967 = 3227951) B3227951
theorem B7255919 : Blo 1273955 7255919 := bstep (se 1 (by rfl) ⟨5441939, by rfl⟩ : syracuseStep 7255919 = 10883879) B10883879
theorem B3446671 : Blo 1273955 3446671 := bstep (se 1 (by rfl) ⟨2585003, by rfl⟩ : syracuseStep 3446671 = 5170007) B5170007
theorem B1816543 : Blo 1273955 1816543 := bstep (se 1 (by rfl) ⟨1362407, by rfl⟩ : syracuseStep 1816543 = 2724815) B2724815
theorem B10893689 : Blo 1273955 10893689 := bstep (se 2 (by rfl) ⟨4085133, by rfl⟩ : syracuseStep 10893689 = 8170267) B8170267
theorem B8722847 : Blo 1273955 8722847 := bstep (se 1 (by rfl) ⟨6542135, by rfl⟩ : syracuseStep 8722847 = 13084271) B13084271
theorem B8280575 : Blo 1273955 8280575 := bstep (se 1 (by rfl) ⟨6210431, by rfl⟩ : syracuseStep 8280575 = 12420863) B12420863
theorem B4839983 : Blo 1273955 4839983 := bstep (se 1 (by rfl) ⟨3629987, by rfl⟩ : syracuseStep 4839983 = 7259975) B7259975
theorem B6888239 : Blo 1273955 6888239 := bstep (se 1 (by rfl) ⟨5166179, by rfl⟩ : syracuseStep 6888239 = 10332359) B10332359
theorem B4299641 : Blo 1273955 4299641 := bstep (se 2 (by rfl) ⟨1612365, by rfl⟩ : syracuseStep 4299641 = 3224731) B3224731
theorem B8723483 : Blo 1273955 8723483 := bstep (se 1 (by rfl) ⟨6542612, by rfl⟩ : syracuseStep 8723483 = 13085225) B13085225
theorem B3447967 : Blo 1273955 3447967 := bstep (se 1 (by rfl) ⟨2585975, by rfl⟩ : syracuseStep 3447967 = 5171951) B5171951
theorem B32660657 : Blo 1273955 32660657 := bstep (se 2 (by rfl) ⟨12247746, by rfl⟩ : syracuseStep 32660657 = 24495493) B24495493
theorem B9191177 : Blo 1273955 9191177 := bstep (se 2 (by rfl) ⟨3446691, by rfl⟩ : syracuseStep 9191177 = 6893383) B6893383
theorem B22085405 : Blo 1273955 22085405 := bstep (se 3 (by rfl) ⟨4141013, by rfl⟩ : syracuseStep 22085405 = 8282027) B8282027
theorem B27590645 : Blo 1273955 27590645 := bstep (se 5 (by rfl) ⟨1293311, by rfl⟩ : syracuseStep 27590645 = 2586623) B2586623
theorem B397509565 : Blo 1273955 397509565 := bstep (se 3 (by rfl) ⟨74533043, by rfl⟩ : syracuseStep 397509565 = 149066087) B149066087
theorem B3229055 : Blo 1273955 3229055 := bstep (se 1 (by rfl) ⟨2421791, by rfl⟩ : syracuseStep 3229055 = 4843583) B4843583
theorem B9684521 : Blo 1273955 9684521 := bstep (se 2 (by rfl) ⟨3631695, by rfl⟩ : syracuseStep 9684521 = 7263391) B7263391
theorem B4597289 : Blo 1273955 4597289 := bstep (se 2 (by rfl) ⟨1723983, by rfl⟩ : syracuseStep 4597289 = 3447967) B3447967
theorem B2869289 : Blo 1273955 2869289 := bstep (se 2 (by rfl) ⟨1075983, by rfl⟩ : syracuseStep 2869289 = 2151967) B2151967
theorem B2721919 : Blo 1273955 2721919 := bstep (se 1 (by rfl) ⟨2041439, by rfl⟩ : syracuseStep 2721919 = 4082879) B4082879
theorem B15501455 : Blo 1273955 15501455 := bstep (se 1 (by rfl) ⟨11626091, by rfl⟩ : syracuseStep 15501455 = 23252183) B23252183
theorem B2721961 : Blo 1273955 2721961 := bstep (se 2 (by rfl) ⟨1020735, by rfl⟩ : syracuseStep 2721961 = 2041471) B2041471
theorem B14518763 : Blo 1273955 14518763 := bstep (se 1 (by rfl) ⟨10889072, by rfl⟩ : syracuseStep 14518763 = 21778145) B21778145
theorem B14723603 : Blo 1273955 14723603 := bstep (se 1 (by rfl) ⟨11042702, by rfl⟩ : syracuseStep 14723603 = 22085405) B22085405
theorem B73575053 : Blo 1273955 73575053 := bstep (se 3 (by rfl) ⟨13795322, by rfl⟩ : syracuseStep 73575053 = 27590645) B27590645
theorem B2042599 : Blo 1273955 2042599 := bstep (se 1 (by rfl) ⟨1531949, by rfl⟩ : syracuseStep 2042599 = 3063899) B3063899
theorem B5442335 : Blo 1273955 5442335 := bstep (se 1 (by rfl) ⟨4081751, by rfl⟩ : syracuseStep 5442335 = 8163503) B8163503
theorem B11627545 : Blo 1273955 11627545 := bstep (se 2 (by rfl) ⟨4360329, by rfl⟩ : syracuseStep 11627545 = 8720659) B8720659
theorem B2042983 : Blo 1273955 2042983 := bstep (se 1 (by rfl) ⟨1532237, by rfl⟩ : syracuseStep 2042983 = 3064475) B3064475
theorem B23260925 : Blo 1273955 23260925 := bstep (se 3 (by rfl) ⟨4361423, by rfl⟩ : syracuseStep 23260925 = 8722847) B8722847
theorem B4837279 : Blo 1273955 4837279 := bstep (se 1 (by rfl) ⟨3627959, by rfl⟩ : syracuseStep 4837279 = 7255919) B7255919
theorem B4304987 : Blo 1273955 4304987 := bstep (se 1 (by rfl) ⟨3228740, by rfl⟩ : syracuseStep 4304987 = 6457481) B6457481
theorem B7262459 : Blo 1273955 7262459 := bstep (se 1 (by rfl) ⟨5446844, by rfl⟩ : syracuseStep 7262459 = 10893689) B10893689
theorem B1274175 : Blo 1273955 1274175 := bstep (se 1 (by rfl) ⟨955631, by rfl⟩ : syracuseStep 1274175 = 1911263) B1911263
theorem B4592159 : Blo 1273955 4592159 := bstep (se 1 (by rfl) ⟨3444119, by rfl⟩ : syracuseStep 4592159 = 6888239) B6888239
theorem B1274495 : Blo 1273955 1274495 := bstep (se 1 (by rfl) ⟨955871, by rfl⟩ : syracuseStep 1274495 = 1911743) B1911743
theorem B1274599 : Blo 1273955 1274599 := bstep (se 1 (by rfl) ⟨955949, by rfl⟩ : syracuseStep 1274599 = 1911899) B1911899
theorem B2422057 : Blo 1273955 2422057 := bstep (se 2 (by rfl) ⟨908271, by rfl⟩ : syracuseStep 2422057 = 1816543) B1816543
theorem B3225055 : Blo 1273955 3225055 := bstep (se 1 (by rfl) ⟨2418791, by rfl⟩ : syracuseStep 3225055 = 4837583) B4837583
theorem B1275623 : Blo 1273955 1275623 := bstep (se 1 (by rfl) ⟨956717, by rfl⟩ : syracuseStep 1275623 = 1913435) B1913435
theorem B26162963 : Blo 1273955 26162963 := bstep (se 1 (by rfl) ⟨19622222, by rfl⟩ : syracuseStep 26162963 = 39244445) B39244445
theorem B4839209 : Blo 1273955 4839209 := bstep (se 2 (by rfl) ⟨1814703, by rfl⟩ : syracuseStep 4839209 = 3629407) B3629407
theorem B1275935 : Blo 1273955 1275935 := bstep (se 1 (by rfl) ⟨956951, by rfl⟩ : syracuseStep 1275935 = 1913903) B1913903
theorem B157030973 : Blo 1273955 157030973 := bstep (se 3 (by rfl) ⟨29443307, by rfl⟩ : syracuseStep 157030973 = 58886615) B58886615
theorem B1530623 : Blo 1273955 1530623 := bstep (se 1 (by rfl) ⟨1147967, by rfl⟩ : syracuseStep 1530623 = 2295935) B2295935
theorem B5520383 : Blo 1273955 5520383 := bstep (se 1 (by rfl) ⟨4140287, by rfl⟩ : syracuseStep 5520383 = 8280575) B8280575
theorem B3226655 : Blo 1273955 3226655 := bstep (se 1 (by rfl) ⟨2419991, by rfl⟩ : syracuseStep 3226655 = 4839983) B4839983
theorem B18390073 : Blo 1273955 18390073 := bstep (se 2 (by rfl) ⟨6896277, by rfl⟩ : syracuseStep 18390073 = 13792555) B13792555
theorem B2866427 : Blo 1273955 2866427 := bstep (se 1 (by rfl) ⟨2149820, by rfl⟩ : syracuseStep 2866427 = 4299641) B4299641
theorem B5815655 : Blo 1273955 5815655 := bstep (se 1 (by rfl) ⟨4361741, by rfl⟩ : syracuseStep 5815655 = 8723483) B8723483
theorem B21773771 : Blo 1273955 21773771 := bstep (se 1 (by rfl) ⟨16330328, by rfl⟩ : syracuseStep 21773771 = 32660657) B32660657
theorem B5447407 : Blo 1273955 5447407 := bstep (se 1 (by rfl) ⟨4085555, by rfl⟩ : syracuseStep 5447407 = 8171111) B8171111
theorem B1433407 : Blo 1273955 1433407 := bstep (se 1 (by rfl) ⟨1075055, by rfl⟩ : syracuseStep 1433407 = 2150111) B2150111
theorem B6127451 : Blo 1273955 6127451 := bstep (se 1 (by rfl) ⟨4595588, by rfl⟩ : syracuseStep 6127451 = 9191177) B9191177
theorem B4595561 : Blo 1273955 4595561 := bstep (se 2 (by rfl) ⟨1723335, by rfl⟩ : syracuseStep 4595561 = 3446671) B3446671
theorem B4841639 : Blo 1273955 4841639 := bstep (se 1 (by rfl) ⟨3631229, by rfl⟩ : syracuseStep 4841639 = 7262459) B7262459
theorem B3629225 : Blo 1273955 3629225 := bstep (se 2 (by rfl) ⟨1360959, by rfl⟩ : syracuseStep 3629225 = 2721919) B2721919
theorem B3629281 : Blo 1273955 3629281 := bstep (se 2 (by rfl) ⟨1360980, by rfl⟩ : syracuseStep 3629281 = 2721961) B2721961
theorem B6456347 : Blo 1273955 6456347 := bstep (se 1 (by rfl) ⟨4842260, by rfl⟩ : syracuseStep 6456347 = 9684521) B9684521
theorem B3064859 : Blo 1273955 3064859 := bstep (se 1 (by rfl) ⟨2298644, by rfl⟩ : syracuseStep 3064859 = 4597289) B4597289
theorem B17441975 : Blo 1273955 17441975 := bstep (se 1 (by rfl) ⟨13081481, by rfl⟩ : syracuseStep 17441975 = 26162963) B26162963
theorem B24520097 : Blo 1273955 24520097 := bstep (se 2 (by rfl) ⟨9195036, by rfl⟩ : syracuseStep 24520097 = 18390073) B18390073
theorem B9815735 : Blo 1273955 9815735 := bstep (se 1 (by rfl) ⟨7361801, by rfl⟩ : syracuseStep 9815735 = 14723603) B14723603
theorem B104687315 : Blo 1273955 104687315 := bstep (se 1 (by rfl) ⟨78515486, by rfl⟩ : syracuseStep 104687315 = 157030973) B157030973
theorem B3229409 : Blo 1273955 3229409 := bstep (se 2 (by rfl) ⟨1211028, by rfl⟩ : syracuseStep 3229409 = 2422057) B2422057
theorem B4081661 : Blo 1273955 4081661 := bstep (se 3 (by rfl) ⟨765311, by rfl⟩ : syracuseStep 4081661 = 1530623) B1530623
theorem B3680255 : Blo 1273955 3680255 := bstep (se 1 (by rfl) ⟨2760191, by rfl⟩ : syracuseStep 3680255 = 5520383) B5520383
theorem B1910951 : Blo 1273955 1910951 := bstep (se 1 (by rfl) ⟨1433213, by rfl⟩ : syracuseStep 1910951 = 2866427) B2866427
theorem B3877103 : Blo 1273955 3877103 := bstep (se 1 (by rfl) ⟨2907827, by rfl⟩ : syracuseStep 3877103 = 5815655) B5815655
theorem B1911209 : Blo 1273955 1911209 := bstep (se 2 (by rfl) ⟨716703, by rfl⟩ : syracuseStep 1911209 = 1433407) B1433407
theorem B6449705 : Blo 1273955 6449705 := bstep (se 2 (by rfl) ⟨2418639, by rfl⟩ : syracuseStep 6449705 = 4837279) B4837279
theorem B2869991 : Blo 1273955 2869991 := bstep (se 1 (by rfl) ⟨2152493, by rfl⟩ : syracuseStep 2869991 = 4304987) B4304987
theorem B2723465 : Blo 1273955 2723465 := bstep (se 2 (by rfl) ⟨1021299, by rfl⟩ : syracuseStep 2723465 = 2042599) B2042599
theorem B1912859 : Blo 1273955 1912859 := bstep (se 1 (by rfl) ⟨1434644, by rfl⟩ : syracuseStep 1912859 = 2869289) B2869289
theorem B15503393 : Blo 1273955 15503393 := bstep (se 2 (by rfl) ⟨5813772, by rfl⟩ : syracuseStep 15503393 = 11627545) B11627545
theorem B10334303 : Blo 1273955 10334303 := bstep (se 1 (by rfl) ⟨7750727, by rfl⟩ : syracuseStep 10334303 = 15501455) B15501455
theorem B2723977 : Blo 1273955 2723977 := bstep (se 2 (by rfl) ⟨1021491, by rfl⟩ : syracuseStep 2723977 = 2042983) B2042983
theorem B9679175 : Blo 1273955 9679175 := bstep (se 1 (by rfl) ⟨7259381, by rfl⟩ : syracuseStep 9679175 = 14518763) B14518763
theorem B49050035 : Blo 1273955 49050035 := bstep (se 1 (by rfl) ⟨36787526, by rfl⟩ : syracuseStep 49050035 = 73575053) B73575053
theorem B2151103 : Blo 1273955 2151103 := bstep (se 1 (by rfl) ⟨1613327, by rfl⟩ : syracuseStep 2151103 = 3226655) B3226655
theorem B7263209 : Blo 1273955 7263209 := bstep (se 2 (by rfl) ⟨2723703, by rfl⟩ : syracuseStep 7263209 = 5447407) B5447407
theorem B4084967 : Blo 1273955 4084967 := bstep (se 1 (by rfl) ⟨3063725, by rfl⟩ : syracuseStep 4084967 = 6127451) B6127451
theorem B3061439 : Blo 1273955 3061439 := bstep (se 1 (by rfl) ⟨2296079, by rfl⟩ : syracuseStep 3061439 = 4592159) B4592159
theorem B2152703 : Blo 1273955 2152703 := bstep (se 1 (by rfl) ⟨1614527, by rfl⟩ : syracuseStep 2152703 = 3229055) B3229055
theorem B3226139 : Blo 1273955 3226139 := bstep (se 1 (by rfl) ⟨2419604, by rfl⟩ : syracuseStep 3226139 = 4839209) B4839209
theorem B530012753 : Blo 1273955 530012753 := bstep (se 2 (by rfl) ⟨198754782, by rfl⟩ : syracuseStep 530012753 = 397509565) B397509565
theorem B3628223 : Blo 1273955 3628223 := bstep (se 1 (by rfl) ⟨2721167, by rfl⟩ : syracuseStep 3628223 = 5442335) B5442335
theorem B4300073 : Blo 1273955 4300073 := bstep (se 2 (by rfl) ⟨1612527, by rfl⟩ : syracuseStep 4300073 = 3225055) B3225055
theorem B14515847 : Blo 1273955 14515847 := bstep (se 1 (by rfl) ⟨10886885, by rfl⟩ : syracuseStep 14515847 = 21773771) B21773771
theorem B15507283 : Blo 1273955 15507283 := bstep (se 1 (by rfl) ⟨11630462, by rfl⟩ : syracuseStep 15507283 = 23260925) B23260925
theorem B3063707 : Blo 1273955 3063707 := bstep (se 1 (by rfl) ⟨2297780, by rfl⟩ : syracuseStep 3063707 = 4595561) B4595561
theorem B6889535 : Blo 1273955 6889535 := bstep (se 1 (by rfl) ⟨5167151, by rfl⟩ : syracuseStep 6889535 = 10334303) B10334303
theorem B3227759 : Blo 1273955 3227759 := bstep (se 1 (by rfl) ⟨2420819, by rfl⟩ : syracuseStep 3227759 = 4841639) B4841639
theorem B10338941 : Blo 1273955 10338941 := bstep (se 3 (by rfl) ⟨1938551, by rfl⟩ : syracuseStep 10338941 = 3877103) B3877103
theorem B4842139 : Blo 1273955 4842139 := bstep (se 1 (by rfl) ⟨3631604, by rfl⟩ : syracuseStep 4842139 = 7263209) B7263209
theorem B2868137 : Blo 1273955 2868137 := bstep (se 2 (by rfl) ⟨1075551, by rfl⟩ : syracuseStep 2868137 = 2151103) B2151103
theorem B2040959 : Blo 1273955 2040959 := bstep (se 1 (by rfl) ⟨1530719, by rfl⟩ : syracuseStep 2040959 = 3061439) B3061439
theorem B2721107 : Blo 1273955 2721107 := bstep (se 1 (by rfl) ⟨2040830, by rfl⟩ : syracuseStep 2721107 = 4081661) B4081661
theorem B1435135 : Blo 1273955 1435135 := bstep (se 1 (by rfl) ⟨1076351, by rfl⟩ : syracuseStep 1435135 = 2152703) B2152703
theorem B2418815 : Blo 1273955 2418815 := bstep (se 1 (by rfl) ⟨1814111, by rfl⟩ : syracuseStep 2418815 = 3628223) B3628223
theorem B9677231 : Blo 1273955 9677231 := bstep (se 1 (by rfl) ⟨7257923, by rfl⟩ : syracuseStep 9677231 = 14515847) B14515847
theorem B2042471 : Blo 1273955 2042471 := bstep (se 1 (by rfl) ⟨1531853, by rfl⟩ : syracuseStep 2042471 = 3063707) B3063707
theorem B2419483 : Blo 1273955 2419483 := bstep (se 1 (by rfl) ⟨1814612, by rfl⟩ : syracuseStep 2419483 = 3629225) B3629225
theorem B3631969 : Blo 1273955 3631969 := bstep (se 2 (by rfl) ⟨1361988, by rfl⟩ : syracuseStep 3631969 = 2723977) B2723977
theorem B4304231 : Blo 1273955 4304231 := bstep (se 1 (by rfl) ⟨3228173, by rfl⟩ : syracuseStep 4304231 = 6456347) B6456347
theorem B2043239 : Blo 1273955 2043239 := bstep (se 1 (by rfl) ⟨1532429, by rfl⟩ : syracuseStep 2043239 = 3064859) B3064859
theorem B11627983 : Blo 1273955 11627983 := bstep (se 1 (by rfl) ⟨8720987, by rfl⟩ : syracuseStep 11627983 = 17441975) B17441975
theorem B2723311 : Blo 1273955 2723311 := bstep (se 1 (by rfl) ⟨2042483, by rfl⟩ : syracuseStep 2723311 = 4084967) B4084967
theorem B16346731 : Blo 1273955 16346731 := bstep (se 1 (by rfl) ⟨12260048, by rfl⟩ : syracuseStep 16346731 = 24520097) B24520097
theorem B69791543 : Blo 1273955 69791543 := bstep (se 1 (by rfl) ⟨52343657, by rfl⟩ : syracuseStep 69791543 = 104687315) B104687315
theorem B2453503 : Blo 1273955 2453503 := bstep (se 1 (by rfl) ⟨1840127, by rfl⟩ : syracuseStep 2453503 = 3680255) B3680255
theorem B1273967 : Blo 1273955 1273967 := bstep (se 1 (by rfl) ⟨955475, by rfl⟩ : syracuseStep 1273967 = 1910951) B1910951
theorem B1274139 : Blo 1273955 1274139 := bstep (se 1 (by rfl) ⟨955604, by rfl⟩ : syracuseStep 1274139 = 1911209) B1911209
theorem B2150759 : Blo 1273955 2150759 := bstep (se 1 (by rfl) ⟨1613069, by rfl⟩ : syracuseStep 2150759 = 3226139) B3226139
theorem B353341835 : Blo 1273955 353341835 := bstep (se 1 (by rfl) ⟨265006376, by rfl⟩ : syracuseStep 353341835 = 530012753) B530012753
theorem B1913327 : Blo 1273955 1913327 := bstep (se 1 (by rfl) ⟨1434995, by rfl⟩ : syracuseStep 1913327 = 2869991) B2869991
theorem B1815643 : Blo 1273955 1815643 := bstep (se 1 (by rfl) ⟨1361732, by rfl⟩ : syracuseStep 1815643 = 2723465) B2723465
theorem B1275239 : Blo 1273955 1275239 := bstep (se 1 (by rfl) ⟨956429, by rfl⟩ : syracuseStep 1275239 = 1912859) B1912859
theorem B10335595 : Blo 1273955 10335595 := bstep (se 1 (by rfl) ⟨7751696, by rfl⟩ : syracuseStep 10335595 = 15503393) B15503393
theorem B6452783 : Blo 1273955 6452783 := bstep (se 1 (by rfl) ⟨4839587, by rfl⟩ : syracuseStep 6452783 = 9679175) B9679175
theorem B32700023 : Blo 1273955 32700023 := bstep (se 1 (by rfl) ⟨24525017, by rfl⟩ : syracuseStep 32700023 = 49050035) B49050035
theorem B4839041 : Blo 1273955 4839041 := bstep (se 2 (by rfl) ⟨1814640, by rfl⟩ : syracuseStep 4839041 = 3629281) B3629281
theorem B6543823 : Blo 1273955 6543823 := bstep (se 1 (by rfl) ⟨4907867, by rfl⟩ : syracuseStep 6543823 = 9815735) B9815735
theorem B2152939 : Blo 1273955 2152939 := bstep (se 1 (by rfl) ⟨1614704, by rfl⟩ : syracuseStep 2152939 = 3229409) B3229409
theorem B4299803 : Blo 1273955 4299803 := bstep (se 1 (by rfl) ⟨3224852, by rfl⟩ : syracuseStep 4299803 = 6449705) B6449705
theorem B2866715 : Blo 1273955 2866715 := bstep (se 1 (by rfl) ⟨2150036, by rfl⟩ : syracuseStep 2866715 = 4300073) B4300073
theorem B20676377 : Blo 1273955 20676377 := bstep (se 2 (by rfl) ⟨7753641, by rfl⟩ : syracuseStep 20676377 = 15507283) B15507283
theorem B1433839 : Blo 1273955 1433839 := bstep (se 1 (by rfl) ⟨1075379, by rfl⟩ : syracuseStep 1433839 = 2150759) B2150759
theorem B235561223 : Blo 1273955 235561223 := bstep (se 1 (by rfl) ⟨176670917, by rfl⟩ : syracuseStep 235561223 = 353341835) B353341835
theorem B8725097 : Blo 1273955 8725097 := bstep (se 2 (by rfl) ⟨3271911, by rfl⟩ : syracuseStep 8725097 = 6543823) B6543823
theorem B1360639 : Blo 1273955 1360639 := bstep (se 1 (by rfl) ⟨1020479, by rfl⟩ : syracuseStep 1360639 = 2040959) B2040959
theorem B6456185 : Blo 1273955 6456185 := bstep (se 2 (by rfl) ⟨2421069, by rfl⟩ : syracuseStep 6456185 = 4842139) B4842139
theorem B5448637 : Blo 1273955 5448637 := bstep (se 3 (by rfl) ⟨1021619, by rfl⟩ : syracuseStep 5448637 = 2043239) B2043239
theorem B4301855 : Blo 1273955 4301855 := bstep (se 1 (by rfl) ⟨3226391, by rfl⟩ : syracuseStep 4301855 = 6452783) B6452783
theorem B21800015 : Blo 1273955 21800015 := bstep (se 1 (by rfl) ⟨16350011, by rfl⟩ : syracuseStep 21800015 = 32700023) B32700023
theorem B4842625 : Blo 1273955 4842625 := bstep (se 2 (by rfl) ⟨1815984, by rfl⟩ : syracuseStep 4842625 = 3631969) B3631969
theorem B1361647 : Blo 1273955 1361647 := bstep (se 1 (by rfl) ⟨1021235, by rfl⟩ : syracuseStep 1361647 = 2042471) B2042471
theorem B13780793 : Blo 1273955 13780793 := bstep (se 2 (by rfl) ⟨5167797, by rfl⟩ : syracuseStep 13780793 = 10335595) B10335595
theorem B3631081 : Blo 1273955 3631081 := bstep (se 2 (by rfl) ⟨1361655, by rfl⟩ : syracuseStep 3631081 = 2723311) B2723311
theorem B2869487 : Blo 1273955 2869487 := bstep (se 1 (by rfl) ⟨2152115, by rfl⟩ : syracuseStep 2869487 = 4304231) B4304231
theorem B1911143 : Blo 1273955 1911143 := bstep (se 1 (by rfl) ⟨1433357, by rfl⟩ : syracuseStep 1911143 = 2866715) B2866715
theorem B3271337 : Blo 1273955 3271337 := bstep (se 2 (by rfl) ⟨1226751, by rfl⟩ : syracuseStep 3271337 = 2453503) B2453503
theorem B6892627 : Blo 1273955 6892627 := bstep (se 1 (by rfl) ⟨5169470, by rfl⟩ : syracuseStep 6892627 = 10338941) B10338941
theorem B1912091 : Blo 1273955 1912091 := bstep (se 1 (by rfl) ⟨1434068, by rfl⟩ : syracuseStep 1912091 = 2868137) B2868137
theorem B2870585 : Blo 1273955 2870585 := bstep (se 2 (by rfl) ⟨1076469, by rfl⟩ : syracuseStep 2870585 = 2152939) B2152939
theorem B1814071 : Blo 1273955 1814071 := bstep (se 1 (by rfl) ⟨1360553, by rfl⟩ : syracuseStep 1814071 = 2721107) B2721107
theorem B2420857 : Blo 1273955 2420857 := bstep (se 2 (by rfl) ⟨907821, by rfl⟩ : syracuseStep 2420857 = 1815643) B1815643
theorem B6451487 : Blo 1273955 6451487 := bstep (se 1 (by rfl) ⟨4838615, by rfl⟩ : syracuseStep 6451487 = 9677231) B9677231
theorem B15503977 : Blo 1273955 15503977 := bstep (se 2 (by rfl) ⟨5813991, by rfl⟩ : syracuseStep 15503977 = 11627983) B11627983
theorem B1913513 : Blo 1273955 1913513 := bstep (se 2 (by rfl) ⟨717567, by rfl⟩ : syracuseStep 1913513 = 1435135) B1435135
theorem B21795641 : Blo 1273955 21795641 := bstep (se 2 (by rfl) ⟨8173365, by rfl⟩ : syracuseStep 21795641 = 16346731) B16346731
theorem B13784251 : Blo 1273955 13784251 := bstep (se 1 (by rfl) ⟨10338188, by rfl⟩ : syracuseStep 13784251 = 20676377) B20676377
theorem B46527695 : Blo 1273955 46527695 := bstep (se 1 (by rfl) ⟨34895771, by rfl⟩ : syracuseStep 46527695 = 69791543) B69791543
theorem B4593023 : Blo 1273955 4593023 := bstep (se 1 (by rfl) ⟨3444767, by rfl⟩ : syracuseStep 4593023 = 6889535) B6889535
theorem B2151839 : Blo 1273955 2151839 := bstep (se 1 (by rfl) ⟨1613879, by rfl⟩ : syracuseStep 2151839 = 3227759) B3227759
theorem B1275551 : Blo 1273955 1275551 := bstep (se 1 (by rfl) ⟨956663, by rfl⟩ : syracuseStep 1275551 = 1913327) B1913327
theorem B3225977 : Blo 1273955 3225977 := bstep (se 2 (by rfl) ⟨1209741, by rfl⟩ : syracuseStep 3225977 = 2419483) B2419483
theorem B3226027 : Blo 1273955 3226027 := bstep (se 1 (by rfl) ⟨2419520, by rfl⟩ : syracuseStep 3226027 = 4839041) B4839041
theorem B1612543 : Blo 1273955 1612543 := bstep (se 1 (by rfl) ⟨1209407, by rfl⟩ : syracuseStep 1612543 = 2418815) B2418815
theorem B2866535 : Blo 1273955 2866535 := bstep (se 1 (by rfl) ⟨2149901, by rfl⟩ : syracuseStep 2866535 = 4299803) B4299803
theorem B3227809 : Blo 1273955 3227809 := bstep (se 2 (by rfl) ⟨1210428, by rfl⟩ : syracuseStep 3227809 = 2420857) B2420857
theorem B4300991 : Blo 1273955 4300991 := bstep (se 1 (by rfl) ⟨3225743, by rfl⟩ : syracuseStep 4300991 = 6451487) B6451487
theorem B4301369 : Blo 1273955 4301369 := bstep (se 2 (by rfl) ⟨1613013, by rfl⟩ : syracuseStep 4301369 = 3226027) B3226027
theorem B628163261 : Blo 1273955 628163261 := bstep (se 3 (by rfl) ⟨117780611, by rfl⟩ : syracuseStep 628163261 = 235561223) B235561223
theorem B2867903 : Blo 1273955 2867903 := bstep (se 1 (by rfl) ⟨2150927, by rfl⟩ : syracuseStep 2867903 = 4301855) B4301855
theorem B14533343 : Blo 1273955 14533343 := bstep (se 1 (by rfl) ⟨10900007, by rfl⟩ : syracuseStep 14533343 = 21800015) B21800015
theorem B1434559 : Blo 1273955 1434559 := bstep (se 1 (by rfl) ⟨1075919, by rfl⟩ : syracuseStep 1434559 = 2151839) B2151839
theorem B6456833 : Blo 1273955 6456833 := bstep (se 2 (by rfl) ⟨2421312, by rfl⟩ : syracuseStep 6456833 = 4842625) B4842625
theorem B23266925 : Blo 1273955 23266925 := bstep (se 3 (by rfl) ⟨4362548, by rfl⟩ : syracuseStep 23266925 = 8725097) B8725097
theorem B2180891 : Blo 1273955 2180891 := bstep (se 1 (by rfl) ⟨1635668, by rfl⟩ : syracuseStep 2180891 = 3271337) B3271337
theorem B2418761 : Blo 1273955 2418761 := bstep (se 2 (by rfl) ⟨907035, by rfl⟩ : syracuseStep 2418761 = 1814071) B1814071
theorem B1911023 : Blo 1273955 1911023 := bstep (se 1 (by rfl) ⟨1433267, by rfl⟩ : syracuseStep 1911023 = 2866535) B2866535
theorem B1911785 : Blo 1273955 1911785 := bstep (se 2 (by rfl) ⟨716919, by rfl⟩ : syracuseStep 1911785 = 1433839) B1433839
theorem B4304123 : Blo 1273955 4304123 := bstep (se 1 (by rfl) ⟨3228092, by rfl⟩ : syracuseStep 4304123 = 6456185) B6456185
theorem B31018463 : Blo 1273955 31018463 := bstep (se 1 (by rfl) ⟨23263847, by rfl⟩ : syracuseStep 31018463 = 46527695) B46527695
theorem B20671969 : Blo 1273955 20671969 := bstep (se 2 (by rfl) ⟨7751988, by rfl⟩ : syracuseStep 20671969 = 15503977) B15503977
theorem B2150057 : Blo 1273955 2150057 := bstep (se 2 (by rfl) ⟨806271, by rfl⟩ : syracuseStep 2150057 = 1612543) B1612543
theorem B1814185 : Blo 1273955 1814185 := bstep (se 2 (by rfl) ⟨680319, by rfl⟩ : syracuseStep 1814185 = 1360639) B1360639
theorem B9187195 : Blo 1273955 9187195 := bstep (se 1 (by rfl) ⟨6890396, by rfl⟩ : syracuseStep 9187195 = 13780793) B13780793
theorem B1912991 : Blo 1273955 1912991 := bstep (se 1 (by rfl) ⟨1434743, by rfl⟩ : syracuseStep 1912991 = 2869487) B2869487
theorem B1274095 : Blo 1273955 1274095 := bstep (se 1 (by rfl) ⟨955571, by rfl⟩ : syracuseStep 1274095 = 1911143) B1911143
theorem B18379001 : Blo 1273955 18379001 := bstep (se 2 (by rfl) ⟨6892125, by rfl⟩ : syracuseStep 18379001 = 13784251) B13784251
theorem B2150651 : Blo 1273955 2150651 := bstep (se 1 (by rfl) ⟨1612988, by rfl⟩ : syracuseStep 2150651 = 3225977) B3225977
theorem B1274727 : Blo 1273955 1274727 := bstep (se 1 (by rfl) ⟨956045, by rfl⟩ : syracuseStep 1274727 = 1912091) B1912091
theorem B1913723 : Blo 1273955 1913723 := bstep (se 1 (by rfl) ⟨1435292, by rfl⟩ : syracuseStep 1913723 = 2870585) B2870585
theorem B1815529 : Blo 1273955 1815529 := bstep (se 2 (by rfl) ⟨680823, by rfl⟩ : syracuseStep 1815529 = 1361647) B1361647
theorem B1275675 : Blo 1273955 1275675 := bstep (se 1 (by rfl) ⟨956756, by rfl⟩ : syracuseStep 1275675 = 1913513) B1913513
theorem B14530427 : Blo 1273955 14530427 := bstep (se 1 (by rfl) ⟨10897820, by rfl⟩ : syracuseStep 14530427 = 21795641) B21795641
theorem B3062015 : Blo 1273955 3062015 := bstep (se 1 (by rfl) ⟨2296511, by rfl⟩ : syracuseStep 3062015 = 4593023) B4593023
theorem B7264849 : Blo 1273955 7264849 := bstep (se 2 (by rfl) ⟨2724318, by rfl⟩ : syracuseStep 7264849 = 5448637) B5448637
theorem B9190169 : Blo 1273955 9190169 := bstep (se 2 (by rfl) ⟨3446313, by rfl⟩ : syracuseStep 9190169 = 6892627) B6892627
theorem B4841441 : Blo 1273955 4841441 := bstep (se 2 (by rfl) ⟨1815540, by rfl⟩ : syracuseStep 4841441 = 3631081) B3631081
theorem B2867327 : Blo 1273955 2867327 := bstep (se 1 (by rfl) ⟨2150495, by rfl⟩ : syracuseStep 2867327 = 4300991) B4300991
theorem B1433767 : Blo 1273955 1433767 := bstep (se 1 (by rfl) ⟨1075325, by rfl⟩ : syracuseStep 1433767 = 2150651) B2150651
theorem B2867579 : Blo 1273955 2867579 := bstep (se 1 (by rfl) ⟨2150684, by rfl⟩ : syracuseStep 2867579 = 4301369) B4301369
theorem B418775507 : Blo 1273955 418775507 := bstep (se 1 (by rfl) ⟨314081630, by rfl⟩ : syracuseStep 418775507 = 628163261) B628163261
theorem B2041343 : Blo 1273955 2041343 := bstep (se 1 (by rfl) ⟨1531007, by rfl⟩ : syracuseStep 2041343 = 3062015) B3062015
theorem B2869415 : Blo 1273955 2869415 := bstep (se 1 (by rfl) ⟨2152061, by rfl⟩ : syracuseStep 2869415 = 4304123) B4304123
theorem B2418913 : Blo 1273955 2418913 := bstep (se 2 (by rfl) ⟨907092, by rfl⟩ : syracuseStep 2418913 = 1814185) B1814185
theorem B20678975 : Blo 1273955 20678975 := bstep (se 1 (by rfl) ⟨15509231, by rfl⟩ : syracuseStep 20678975 = 31018463) B31018463
theorem B12249593 : Blo 1273955 12249593 := bstep (se 2 (by rfl) ⟨4593597, by rfl⟩ : syracuseStep 12249593 = 9187195) B9187195
theorem B6450029 : Blo 1273955 6450029 := bstep (se 3 (by rfl) ⟨1209380, by rfl⟩ : syracuseStep 6450029 = 2418761) B2418761
theorem B4303745 : Blo 1273955 4303745 := bstep (se 2 (by rfl) ⟨1613904, by rfl⟩ : syracuseStep 4303745 = 3227809) B3227809
theorem B1911935 : Blo 1273955 1911935 := bstep (se 1 (by rfl) ⟨1433951, by rfl⟩ : syracuseStep 1911935 = 2867903) B2867903
theorem B9686465 : Blo 1273955 9686465 := bstep (se 2 (by rfl) ⟨3632424, by rfl⟩ : syracuseStep 9686465 = 7264849) B7264849
theorem B4304555 : Blo 1273955 4304555 := bstep (se 1 (by rfl) ⟨3228416, by rfl⟩ : syracuseStep 4304555 = 6456833) B6456833
theorem B15511283 : Blo 1273955 15511283 := bstep (se 1 (by rfl) ⟨11633462, by rfl⟩ : syracuseStep 15511283 = 23266925) B23266925
theorem B9686951 : Blo 1273955 9686951 := bstep (se 1 (by rfl) ⟨7265213, by rfl⟩ : syracuseStep 9686951 = 14530427) B14530427
theorem B1912745 : Blo 1273955 1912745 := bstep (se 2 (by rfl) ⟨717279, by rfl⟩ : syracuseStep 1912745 = 1434559) B1434559
theorem B2420705 : Blo 1273955 2420705 := bstep (se 2 (by rfl) ⟨907764, by rfl⟩ : syracuseStep 2420705 = 1815529) B1815529
theorem B1274015 : Blo 1273955 1274015 := bstep (se 1 (by rfl) ⟨955511, by rfl⟩ : syracuseStep 1274015 = 1911023) B1911023
theorem B27562625 : Blo 1273955 27562625 := bstep (se 2 (by rfl) ⟨10335984, by rfl⟩ : syracuseStep 27562625 = 20671969) B20671969
theorem B1274523 : Blo 1273955 1274523 := bstep (se 1 (by rfl) ⟨955892, by rfl⟩ : syracuseStep 1274523 = 1911785) B1911785
theorem B1275327 : Blo 1273955 1275327 := bstep (se 1 (by rfl) ⟨956495, by rfl⟩ : syracuseStep 1275327 = 1912991) B1912991
theorem B9688895 : Blo 1273955 9688895 := bstep (se 1 (by rfl) ⟨7266671, by rfl⟩ : syracuseStep 9688895 = 14533343) B14533343
theorem B1275815 : Blo 1273955 1275815 := bstep (se 1 (by rfl) ⟨956861, by rfl⟩ : syracuseStep 1275815 = 1913723) B1913723
theorem B49010669 : Blo 1273955 49010669 := bstep (se 3 (by rfl) ⟨9189500, by rfl⟩ : syracuseStep 49010669 = 18379001) B18379001
theorem B6126779 : Blo 1273955 6126779 := bstep (se 1 (by rfl) ⟨4595084, by rfl⟩ : syracuseStep 6126779 = 9190169) B9190169
theorem B5815709 : Blo 1273955 5815709 := bstep (se 3 (by rfl) ⟨1090445, by rfl⟩ : syracuseStep 5815709 = 2180891) B2180891
theorem B1433371 : Blo 1273955 1433371 := bstep (se 1 (by rfl) ⟨1075028, by rfl⟩ : syracuseStep 1433371 = 2150057) B2150057
theorem B3227627 : Blo 1273955 3227627 := bstep (se 1 (by rfl) ⟨2420720, by rfl⟩ : syracuseStep 3227627 = 4841441) B4841441
theorem B279183671 : Blo 1273955 279183671 := bstep (se 1 (by rfl) ⟨209387753, by rfl⟩ : syracuseStep 279183671 = 418775507) B418775507
theorem B18375083 : Blo 1273955 18375083 := bstep (se 1 (by rfl) ⟨13781312, by rfl⟩ : syracuseStep 18375083 = 27562625) B27562625
theorem B1360895 : Blo 1273955 1360895 := bstep (se 1 (by rfl) ⟨1020671, by rfl⟩ : syracuseStep 1360895 = 2041343) B2041343
theorem B2869163 : Blo 1273955 2869163 := bstep (se 1 (by rfl) ⟨2151872, by rfl⟩ : syracuseStep 2869163 = 4303745) B4303745
theorem B3877139 : Blo 1273955 3877139 := bstep (se 1 (by rfl) ⟨2907854, by rfl⟩ : syracuseStep 3877139 = 5815709) B5815709
theorem B6457643 : Blo 1273955 6457643 := bstep (se 1 (by rfl) ⟨4843232, by rfl⟩ : syracuseStep 6457643 = 9686465) B9686465
theorem B1911161 : Blo 1273955 1911161 := bstep (se 2 (by rfl) ⟨716685, by rfl⟩ : syracuseStep 1911161 = 1433371) B1433371
theorem B2869703 : Blo 1273955 2869703 := bstep (se 1 (by rfl) ⟨2152277, by rfl⟩ : syracuseStep 2869703 = 4304555) B4304555
theorem B10340855 : Blo 1273955 10340855 := bstep (se 1 (by rfl) ⟨7755641, by rfl⟩ : syracuseStep 10340855 = 15511283) B15511283
theorem B6457967 : Blo 1273955 6457967 := bstep (se 1 (by rfl) ⟨4843475, by rfl⟩ : syracuseStep 6457967 = 9686951) B9686951
theorem B1911551 : Blo 1273955 1911551 := bstep (se 1 (by rfl) ⟨1433663, by rfl⟩ : syracuseStep 1911551 = 2867327) B2867327
theorem B1911689 : Blo 1273955 1911689 := bstep (se 2 (by rfl) ⟨716883, by rfl⟩ : syracuseStep 1911689 = 1433767) B1433767
theorem B1911719 : Blo 1273955 1911719 := bstep (se 1 (by rfl) ⟨1433789, by rfl⟩ : syracuseStep 1911719 = 2867579) B2867579
theorem B6459263 : Blo 1273955 6459263 := bstep (se 1 (by rfl) ⟨4844447, by rfl⟩ : syracuseStep 6459263 = 9688895) B9688895
theorem B32673779 : Blo 1273955 32673779 := bstep (se 1 (by rfl) ⟨24505334, by rfl⟩ : syracuseStep 32673779 = 49010669) B49010669
theorem B1912943 : Blo 1273955 1912943 := bstep (se 1 (by rfl) ⟨1434707, by rfl⟩ : syracuseStep 1912943 = 2869415) B2869415
theorem B1274623 : Blo 1273955 1274623 := bstep (se 1 (by rfl) ⟨955967, by rfl⟩ : syracuseStep 1274623 = 1911935) B1911935
theorem B4084519 : Blo 1273955 4084519 := bstep (se 1 (by rfl) ⟨3063389, by rfl⟩ : syracuseStep 4084519 = 6126779) B6126779
theorem B1275163 : Blo 1273955 1275163 := bstep (se 1 (by rfl) ⟨956372, by rfl⟩ : syracuseStep 1275163 = 1912745) B1912745
theorem B2151751 : Blo 1273955 2151751 := bstep (se 1 (by rfl) ⟨1613813, by rfl⟩ : syracuseStep 2151751 = 3227627) B3227627
theorem B3225217 : Blo 1273955 3225217 := bstep (se 2 (by rfl) ⟨1209456, by rfl⟩ : syracuseStep 3225217 = 2418913) B2418913
theorem B13785983 : Blo 1273955 13785983 := bstep (se 1 (by rfl) ⟨10339487, by rfl⟩ : syracuseStep 13785983 = 20678975) B20678975
theorem B8166395 : Blo 1273955 8166395 := bstep (se 1 (by rfl) ⟨6124796, by rfl⟩ : syracuseStep 8166395 = 12249593) B12249593
theorem B4300019 : Blo 1273955 4300019 := bstep (se 1 (by rfl) ⟨3225014, by rfl⟩ : syracuseStep 4300019 = 6450029) B6450029
theorem B6455213 : Blo 1273955 6455213 := bstep (se 3 (by rfl) ⟨1210352, by rfl⟩ : syracuseStep 6455213 = 2420705) B2420705
theorem B186122447 : Blo 1273955 186122447 := bstep (se 1 (by rfl) ⟨139591835, by rfl⟩ : syracuseStep 186122447 = 279183671) B279183671
theorem B2869001 : Blo 1273955 2869001 := bstep (se 2 (by rfl) ⟨1075875, by rfl⟩ : syracuseStep 2869001 = 2151751) B2151751
theorem B4303475 : Blo 1273955 4303475 := bstep (se 1 (by rfl) ⟨3227606, by rfl⟩ : syracuseStep 4303475 = 6455213) B6455213
theorem B12250055 : Blo 1273955 12250055 := bstep (se 1 (by rfl) ⟨9187541, by rfl⟩ : syracuseStep 12250055 = 18375083) B18375083
theorem B1912775 : Blo 1273955 1912775 := bstep (se 1 (by rfl) ⟨1434581, by rfl⟩ : syracuseStep 1912775 = 2869163) B2869163
theorem B2584759 : Blo 1273955 2584759 := bstep (se 1 (by rfl) ⟨1938569, by rfl⟩ : syracuseStep 2584759 = 3877139) B3877139
theorem B4305095 : Blo 1273955 4305095 := bstep (se 1 (by rfl) ⟨3228821, by rfl⟩ : syracuseStep 4305095 = 6457643) B6457643
theorem B1274107 : Blo 1273955 1274107 := bstep (se 1 (by rfl) ⟨955580, by rfl⟩ : syracuseStep 1274107 = 1911161) B1911161
theorem B1913135 : Blo 1273955 1913135 := bstep (se 1 (by rfl) ⟨1434851, by rfl⟩ : syracuseStep 1913135 = 2869703) B2869703
theorem B6893903 : Blo 1273955 6893903 := bstep (se 1 (by rfl) ⟨5170427, by rfl⟩ : syracuseStep 6893903 = 10340855) B10340855
theorem B4305311 : Blo 1273955 4305311 := bstep (se 1 (by rfl) ⟨3228983, by rfl⟩ : syracuseStep 4305311 = 6457967) B6457967
theorem B1274367 : Blo 1273955 1274367 := bstep (se 1 (by rfl) ⟨955775, by rfl⟩ : syracuseStep 1274367 = 1911551) B1911551
theorem B1274459 : Blo 1273955 1274459 := bstep (se 1 (by rfl) ⟨955844, by rfl⟩ : syracuseStep 1274459 = 1911689) B1911689
theorem B1274479 : Blo 1273955 1274479 := bstep (se 1 (by rfl) ⟨955859, by rfl⟩ : syracuseStep 1274479 = 1911719) B1911719
theorem B5444263 : Blo 1273955 5444263 := bstep (se 1 (by rfl) ⟨4083197, by rfl⟩ : syracuseStep 5444263 = 8166395) B8166395
theorem B4306175 : Blo 1273955 4306175 := bstep (se 1 (by rfl) ⟨3229631, by rfl⟩ : syracuseStep 4306175 = 6459263) B6459263
theorem B1275295 : Blo 1273955 1275295 := bstep (se 1 (by rfl) ⟨956471, by rfl⟩ : syracuseStep 1275295 = 1912943) B1912943
theorem B5446025 : Blo 1273955 5446025 := bstep (se 2 (by rfl) ⟨2042259, by rfl⟩ : syracuseStep 5446025 = 4084519) B4084519
theorem B9190655 : Blo 1273955 9190655 := bstep (se 1 (by rfl) ⟨6892991, by rfl⟩ : syracuseStep 9190655 = 13785983) B13785983
theorem B2866679 : Blo 1273955 2866679 := bstep (se 1 (by rfl) ⟨2150009, by rfl⟩ : syracuseStep 2866679 = 4300019) B4300019
theorem B4300289 : Blo 1273955 4300289 := bstep (se 2 (by rfl) ⟨1612608, by rfl⟩ : syracuseStep 4300289 = 3225217) B3225217
theorem B21782519 : Blo 1273955 21782519 := bstep (se 1 (by rfl) ⟨16336889, by rfl⟩ : syracuseStep 21782519 = 32673779) B32673779
theorem B3629053 : Blo 1273955 3629053 := bstep (se 3 (by rfl) ⟨680447, by rfl⟩ : syracuseStep 3629053 = 1360895) B1360895
theorem B4595935 : Blo 1273955 4595935 := bstep (se 1 (by rfl) ⟨3446951, by rfl⟩ : syracuseStep 4595935 = 6893903) B6893903
theorem B7259017 : Blo 1273955 7259017 := bstep (se 2 (by rfl) ⟨2722131, by rfl⟩ : syracuseStep 7259017 = 5444263) B5444263
theorem B3630683 : Blo 1273955 3630683 := bstep (se 1 (by rfl) ⟨2723012, by rfl⟩ : syracuseStep 3630683 = 5446025) B5446025
theorem B2868983 : Blo 1273955 2868983 := bstep (se 1 (by rfl) ⟨2151737, by rfl⟩ : syracuseStep 2868983 = 4303475) B4303475
theorem B1911119 : Blo 1273955 1911119 := bstep (se 1 (by rfl) ⟨1433339, by rfl⟩ : syracuseStep 1911119 = 2866679) B2866679
theorem B2870063 : Blo 1273955 2870063 := bstep (se 1 (by rfl) ⟨2152547, by rfl⟩ : syracuseStep 2870063 = 4305095) B4305095
theorem B2870207 : Blo 1273955 2870207 := bstep (se 1 (by rfl) ⟨2152655, by rfl⟩ : syracuseStep 2870207 = 4305311) B4305311
theorem B2870783 : Blo 1273955 2870783 := bstep (se 1 (by rfl) ⟨2153087, by rfl⟩ : syracuseStep 2870783 = 4306175) B4306175
theorem B1912667 : Blo 1273955 1912667 := bstep (se 1 (by rfl) ⟨1434500, by rfl⟩ : syracuseStep 1912667 = 2869001) B2869001
theorem B1275183 : Blo 1273955 1275183 := bstep (se 1 (by rfl) ⟨956387, by rfl⟩ : syracuseStep 1275183 = 1912775) B1912775
theorem B14521679 : Blo 1273955 14521679 := bstep (se 1 (by rfl) ⟨10891259, by rfl⟩ : syracuseStep 14521679 = 21782519) B21782519
theorem B4838737 : Blo 1273955 4838737 := bstep (se 2 (by rfl) ⟨1814526, by rfl⟩ : syracuseStep 4838737 = 3629053) B3629053
theorem B124081631 : Blo 1273955 124081631 := bstep (se 1 (by rfl) ⟨93061223, by rfl⟩ : syracuseStep 124081631 = 186122447) B186122447
theorem B1275423 : Blo 1273955 1275423 := bstep (se 1 (by rfl) ⟨956567, by rfl⟩ : syracuseStep 1275423 = 1913135) B1913135
theorem B3446345 : Blo 1273955 3446345 := bstep (se 2 (by rfl) ⟨1292379, by rfl⟩ : syracuseStep 3446345 = 2584759) B2584759
theorem B8166703 : Blo 1273955 8166703 := bstep (se 1 (by rfl) ⟨6125027, by rfl⟩ : syracuseStep 8166703 = 12250055) B12250055
theorem B6127103 : Blo 1273955 6127103 := bstep (se 1 (by rfl) ⟨4595327, by rfl⟩ : syracuseStep 6127103 = 9190655) B9190655
theorem B2866859 : Blo 1273955 2866859 := bstep (se 1 (by rfl) ⟨2150144, by rfl⟩ : syracuseStep 2866859 = 4300289) B4300289
theorem B6127913 : Blo 1273955 6127913 := bstep (se 2 (by rfl) ⟨2297967, by rfl⟩ : syracuseStep 6127913 = 4595935) B4595935
theorem B10888937 : Blo 1273955 10888937 := bstep (se 2 (by rfl) ⟨4083351, by rfl⟩ : syracuseStep 10888937 = 8166703) B8166703
theorem B1911239 : Blo 1273955 1911239 := bstep (se 1 (by rfl) ⟨1433429, by rfl⟩ : syracuseStep 1911239 = 2866859) B2866859
theorem B2420455 : Blo 1273955 2420455 := bstep (se 1 (by rfl) ⟨1815341, by rfl⟩ : syracuseStep 2420455 = 3630683) B3630683
theorem B1912655 : Blo 1273955 1912655 := bstep (se 1 (by rfl) ⟨1434491, by rfl⟩ : syracuseStep 1912655 = 2868983) B2868983
theorem B9678689 : Blo 1273955 9678689 := bstep (se 2 (by rfl) ⟨3629508, by rfl⟩ : syracuseStep 9678689 = 7259017) B7259017
theorem B16338941 : Blo 1273955 16338941 := bstep (se 3 (by rfl) ⟨3063551, by rfl⟩ : syracuseStep 16338941 = 6127103) B6127103
theorem B1274079 : Blo 1273955 1274079 := bstep (se 1 (by rfl) ⟨955559, by rfl⟩ : syracuseStep 1274079 = 1911119) B1911119
theorem B6451649 : Blo 1273955 6451649 := bstep (se 2 (by rfl) ⟨2419368, by rfl⟩ : syracuseStep 6451649 = 4838737) B4838737
theorem B1913375 : Blo 1273955 1913375 := bstep (se 1 (by rfl) ⟨1435031, by rfl⟩ : syracuseStep 1913375 = 2870063) B2870063
theorem B1913471 : Blo 1273955 1913471 := bstep (se 1 (by rfl) ⟨1435103, by rfl⟩ : syracuseStep 1913471 = 2870207) B2870207
theorem B1913855 : Blo 1273955 1913855 := bstep (se 1 (by rfl) ⟨1435391, by rfl⟩ : syracuseStep 1913855 = 2870783) B2870783
theorem B1275111 : Blo 1273955 1275111 := bstep (se 1 (by rfl) ⟨956333, by rfl⟩ : syracuseStep 1275111 = 1912667) B1912667
theorem B9681119 : Blo 1273955 9681119 := bstep (se 1 (by rfl) ⟨7260839, by rfl⟩ : syracuseStep 9681119 = 14521679) B14521679
theorem B82721087 : Blo 1273955 82721087 := bstep (se 1 (by rfl) ⟨62040815, by rfl⟩ : syracuseStep 82721087 = 124081631) B124081631
theorem B9190253 : Blo 1273955 9190253 := bstep (se 3 (by rfl) ⟨1723172, by rfl⟩ : syracuseStep 9190253 = 3446345) B3446345
theorem B4301099 : Blo 1273955 4301099 := bstep (se 1 (by rfl) ⟨3225824, by rfl⟩ : syracuseStep 4301099 = 6451649) B6451649
theorem B7259291 : Blo 1273955 7259291 := bstep (se 1 (by rfl) ⟨5444468, by rfl⟩ : syracuseStep 7259291 = 10888937) B10888937
theorem B1274159 : Blo 1273955 1274159 := bstep (se 1 (by rfl) ⟨955619, by rfl⟩ : syracuseStep 1274159 = 1911239) B1911239
theorem B1275103 : Blo 1273955 1275103 := bstep (se 1 (by rfl) ⟨956327, by rfl⟩ : syracuseStep 1275103 = 1912655) B1912655
theorem B6452459 : Blo 1273955 6452459 := bstep (se 1 (by rfl) ⟨4839344, by rfl⟩ : syracuseStep 6452459 = 9678689) B9678689
theorem B10892627 : Blo 1273955 10892627 := bstep (se 1 (by rfl) ⟨8169470, by rfl⟩ : syracuseStep 10892627 = 16338941) B16338941
theorem B4085275 : Blo 1273955 4085275 := bstep (se 1 (by rfl) ⟨3063956, by rfl⟩ : syracuseStep 4085275 = 6127913) B6127913
theorem B1275583 : Blo 1273955 1275583 := bstep (se 1 (by rfl) ⟨956687, by rfl⟩ : syracuseStep 1275583 = 1913375) B1913375
theorem B1275647 : Blo 1273955 1275647 := bstep (se 1 (by rfl) ⟨956735, by rfl⟩ : syracuseStep 1275647 = 1913471) B1913471
theorem B1275903 : Blo 1273955 1275903 := bstep (se 1 (by rfl) ⟨956927, by rfl⟩ : syracuseStep 1275903 = 1913855) B1913855
theorem B6454079 : Blo 1273955 6454079 := bstep (se 1 (by rfl) ⟨4840559, by rfl⟩ : syracuseStep 6454079 = 9681119) B9681119
theorem B55147391 : Blo 1273955 55147391 := bstep (se 1 (by rfl) ⟨41360543, by rfl⟩ : syracuseStep 55147391 = 82721087) B82721087
theorem B6126835 : Blo 1273955 6126835 := bstep (se 1 (by rfl) ⟨4595126, by rfl⟩ : syracuseStep 6126835 = 9190253) B9190253
theorem B3227273 : Blo 1273955 3227273 := bstep (se 2 (by rfl) ⟨1210227, by rfl⟩ : syracuseStep 3227273 = 2420455) B2420455
theorem B2867399 : Blo 1273955 2867399 := bstep (se 1 (by rfl) ⟨2150549, by rfl⟩ : syracuseStep 2867399 = 4301099) B4301099
theorem B4301639 : Blo 1273955 4301639 := bstep (se 1 (by rfl) ⟨3226229, by rfl⟩ : syracuseStep 4301639 = 6452459) B6452459
theorem B8169113 : Blo 1273955 8169113 := bstep (se 2 (by rfl) ⟨3063417, by rfl⟩ : syracuseStep 8169113 = 6126835) B6126835
theorem B4302719 : Blo 1273955 4302719 := bstep (se 1 (by rfl) ⟨3227039, by rfl⟩ : syracuseStep 4302719 = 6454079) B6454079
theorem B7261751 : Blo 1273955 7261751 := bstep (se 1 (by rfl) ⟨5446313, by rfl⟩ : syracuseStep 7261751 = 10892627) B10892627
theorem B2151515 : Blo 1273955 2151515 := bstep (se 1 (by rfl) ⟨1613636, by rfl⟩ : syracuseStep 2151515 = 3227273) B3227273
theorem B4839527 : Blo 1273955 4839527 := bstep (se 1 (by rfl) ⟨3629645, by rfl⟩ : syracuseStep 4839527 = 7259291) B7259291
theorem B36764927 : Blo 1273955 36764927 := bstep (se 1 (by rfl) ⟨27573695, by rfl⟩ : syracuseStep 36764927 = 55147391) B55147391
theorem B5447033 : Blo 1273955 5447033 := bstep (se 2 (by rfl) ⟨2042637, by rfl⟩ : syracuseStep 5447033 = 4085275) B4085275
theorem B2867759 : Blo 1273955 2867759 := bstep (se 1 (by rfl) ⟨2150819, by rfl⟩ : syracuseStep 2867759 = 4301639) B4301639
theorem B1434343 : Blo 1273955 1434343 := bstep (se 1 (by rfl) ⟨1075757, by rfl⟩ : syracuseStep 1434343 = 2151515) B2151515
theorem B2868479 : Blo 1273955 2868479 := bstep (se 1 (by rfl) ⟨2151359, by rfl⟩ : syracuseStep 2868479 = 4302719) B4302719
theorem B3631355 : Blo 1273955 3631355 := bstep (se 1 (by rfl) ⟨2723516, by rfl⟩ : syracuseStep 3631355 = 5447033) B5447033
theorem B1911599 : Blo 1273955 1911599 := bstep (se 1 (by rfl) ⟨1433699, by rfl⟩ : syracuseStep 1911599 = 2867399) B2867399
theorem B5446075 : Blo 1273955 5446075 := bstep (se 1 (by rfl) ⟨4084556, by rfl⟩ : syracuseStep 5446075 = 8169113) B8169113
theorem B3226351 : Blo 1273955 3226351 := bstep (se 1 (by rfl) ⟨2419763, by rfl⟩ : syracuseStep 3226351 = 4839527) B4839527
theorem B24509951 : Blo 1273955 24509951 := bstep (se 1 (by rfl) ⟨18382463, by rfl⟩ : syracuseStep 24509951 = 36764927) B36764927
theorem B4841167 : Blo 1273955 4841167 := bstep (se 1 (by rfl) ⟨3630875, by rfl⟩ : syracuseStep 4841167 = 7261751) B7261751
theorem B4301801 : Blo 1273955 4301801 := bstep (se 2 (by rfl) ⟨1613175, by rfl⟩ : syracuseStep 4301801 = 3226351) B3226351
theorem B1911839 : Blo 1273955 1911839 := bstep (se 1 (by rfl) ⟨1433879, by rfl⟩ : syracuseStep 1911839 = 2867759) B2867759
theorem B7261433 : Blo 1273955 7261433 := bstep (se 2 (by rfl) ⟨2723037, by rfl⟩ : syracuseStep 7261433 = 5446075) B5446075
theorem B1912319 : Blo 1273955 1912319 := bstep (se 1 (by rfl) ⟨1434239, by rfl⟩ : syracuseStep 1912319 = 2868479) B2868479
theorem B1912457 : Blo 1273955 1912457 := bstep (se 2 (by rfl) ⟨717171, by rfl⟩ : syracuseStep 1912457 = 1434343) B1434343
theorem B2420903 : Blo 1273955 2420903 := bstep (se 1 (by rfl) ⟨1815677, by rfl⟩ : syracuseStep 2420903 = 3631355) B3631355
theorem B1274399 : Blo 1273955 1274399 := bstep (se 1 (by rfl) ⟨955799, by rfl⟩ : syracuseStep 1274399 = 1911599) B1911599
theorem B16339967 : Blo 1273955 16339967 := bstep (se 1 (by rfl) ⟨12254975, by rfl⟩ : syracuseStep 16339967 = 24509951) B24509951
theorem B6454889 : Blo 1273955 6454889 := bstep (se 2 (by rfl) ⟨2420583, by rfl⟩ : syracuseStep 6454889 = 4841167) B4841167
theorem B1613935 : Blo 1273955 1613935 := bstep (se 1 (by rfl) ⟨1210451, by rfl⟩ : syracuseStep 1613935 = 2420903) B2420903
theorem B2867867 : Blo 1273955 2867867 := bstep (se 1 (by rfl) ⟨2150900, by rfl⟩ : syracuseStep 2867867 = 4301801) B4301801
theorem B4303259 : Blo 1273955 4303259 := bstep (se 1 (by rfl) ⟨3227444, by rfl⟩ : syracuseStep 4303259 = 6454889) B6454889
theorem B1274559 : Blo 1273955 1274559 := bstep (se 1 (by rfl) ⟨955919, by rfl⟩ : syracuseStep 1274559 = 1911839) B1911839
theorem B1274879 : Blo 1273955 1274879 := bstep (se 1 (by rfl) ⟨956159, by rfl⟩ : syracuseStep 1274879 = 1912319) B1912319
theorem B1274971 : Blo 1273955 1274971 := bstep (se 1 (by rfl) ⟨956228, by rfl⟩ : syracuseStep 1274971 = 1912457) B1912457
theorem B10893311 : Blo 1273955 10893311 := bstep (se 1 (by rfl) ⟨8169983, by rfl⟩ : syracuseStep 10893311 = 16339967) B16339967
theorem B4840955 : Blo 1273955 4840955 := bstep (se 1 (by rfl) ⟨3630716, by rfl⟩ : syracuseStep 4840955 = 7261433) B7261433
theorem B2868839 : Blo 1273955 2868839 := bstep (se 1 (by rfl) ⟨2151629, by rfl⟩ : syracuseStep 2868839 = 4303259) B4303259
theorem B1911911 : Blo 1273955 1911911 := bstep (se 1 (by rfl) ⟨1433933, by rfl⟩ : syracuseStep 1911911 = 2867867) B2867867
theorem B7262207 : Blo 1273955 7262207 := bstep (se 1 (by rfl) ⟨5446655, by rfl⟩ : syracuseStep 7262207 = 10893311) B10893311
theorem B2151913 : Blo 1273955 2151913 := bstep (se 2 (by rfl) ⟨806967, by rfl⟩ : syracuseStep 2151913 = 1613935) B1613935
theorem B3227303 : Blo 1273955 3227303 := bstep (se 1 (by rfl) ⟨2420477, by rfl⟩ : syracuseStep 3227303 = 4840955) B4840955
theorem B2869217 : Blo 1273955 2869217 := bstep (se 2 (by rfl) ⟨1075956, by rfl⟩ : syracuseStep 2869217 = 2151913) B2151913
theorem B1912559 : Blo 1273955 1912559 := bstep (se 1 (by rfl) ⟨1434419, by rfl⟩ : syracuseStep 1912559 = 2868839) B2868839
theorem B4841471 : Blo 1273955 4841471 := bstep (se 1 (by rfl) ⟨3631103, by rfl⟩ : syracuseStep 4841471 = 7262207) B7262207
theorem B1274607 : Blo 1273955 1274607 := bstep (se 1 (by rfl) ⟨955955, by rfl⟩ : syracuseStep 1274607 = 1911911) B1911911
theorem B2151535 : Blo 1273955 2151535 := bstep (se 1 (by rfl) ⟨1613651, by rfl⟩ : syracuseStep 2151535 = 3227303) B3227303
theorem B2868713 : Blo 1273955 2868713 := bstep (se 2 (by rfl) ⟨1075767, by rfl⟩ : syracuseStep 2868713 = 2151535) B2151535
theorem B1912811 : Blo 1273955 1912811 := bstep (se 1 (by rfl) ⟨1434608, by rfl⟩ : syracuseStep 1912811 = 2869217) B2869217
theorem B1275039 : Blo 1273955 1275039 := bstep (se 1 (by rfl) ⟨956279, by rfl⟩ : syracuseStep 1275039 = 1912559) B1912559
theorem B3227647 : Blo 1273955 3227647 := bstep (se 1 (by rfl) ⟨2420735, by rfl⟩ : syracuseStep 3227647 = 4841471) B4841471
theorem B4303529 : Blo 1273955 4303529 := bstep (se 2 (by rfl) ⟨1613823, by rfl⟩ : syracuseStep 4303529 = 3227647) B3227647
theorem B1912475 : Blo 1273955 1912475 := bstep (se 1 (by rfl) ⟨1434356, by rfl⟩ : syracuseStep 1912475 = 2868713) B2868713
theorem B1275207 : Blo 1273955 1275207 := bstep (se 1 (by rfl) ⟨956405, by rfl⟩ : syracuseStep 1275207 = 1912811) B1912811
theorem B2869019 : Blo 1273955 2869019 := bstep (se 1 (by rfl) ⟨2151764, by rfl⟩ : syracuseStep 2869019 = 4303529) B4303529
theorem B1274983 : Blo 1273955 1274983 := bstep (se 1 (by rfl) ⟨956237, by rfl⟩ : syracuseStep 1274983 = 1912475) B1912475
theorem B1912679 : Blo 1273955 1912679 := bstep (se 1 (by rfl) ⟨1434509, by rfl⟩ : syracuseStep 1912679 = 2869019) B2869019
theorem B1275119 : Blo 1273955 1275119 := bstep (se 1 (by rfl) ⟨956339, by rfl⟩ : syracuseStep 1275119 = 1912679) B1912679

theorem C0 (j : ℕ) (h1 : 318488 ≤ j) (h2 : j ≤ 318988) : Blo 1273955 (4 * j + 3) := by
  interval_cases j
  · exact B1273955
  · exact B1273959
  · exact B1273963
  · exact B1273967
  · exact B1273971
  · exact B1273975
  · exact B1273979
  · exact B1273983
  · exact B1273987
  · exact B1273991
  · exact B1273995
  · exact B1273999
  · exact B1274003
  · exact B1274007
  · exact B1274011
  · exact B1274015
  · exact B1274019
  · exact B1274023
  · exact B1274027
  · exact B1274031
  · exact B1274035
  · exact B1274039
  · exact B1274043
  · exact B1274047
  · exact B1274051
  · exact B1274055
  · exact B1274059
  · exact B1274063
  · exact B1274067
  · exact B1274071
  · exact B1274075
  · exact B1274079
  · exact B1274083
  · exact B1274087
  · exact B1274091
  · exact B1274095
  · exact B1274099
  · exact B1274103
  · exact B1274107
  · exact B1274111
  · exact B1274115
  · exact B1274119
  · exact B1274123
  · exact B1274127
  · exact B1274131
  · exact B1274135
  · exact B1274139
  · exact B1274143
  · exact B1274147
  · exact B1274151
  · exact B1274155
  · exact B1274159
  · exact B1274163
  · exact B1274167
  · exact B1274171
  · exact B1274175
  · exact B1274179
  · exact B1274183
  · exact B1274187
  · exact B1274191
  · exact B1274195
  · exact B1274199
  · exact B1274203
  · exact B1274207
  · exact B1274211
  · exact B1274215
  · exact B1274219
  · exact B1274223
  · exact B1274227
  · exact B1274231
  · exact B1274235
  · exact B1274239
  · exact B1274243
  · exact B1274247
  · exact B1274251
  · exact B1274255
  · exact B1274259
  · exact B1274263
  · exact B1274267
  · exact B1274271
  · exact B1274275
  · exact B1274279
  · exact B1274283
  · exact B1274287
  · exact B1274291
  · exact B1274295
  · exact B1274299
  · exact B1274303
  · exact B1274307
  · exact B1274311
  · exact B1274315
  · exact B1274319
  · exact B1274323
  · exact B1274327
  · exact B1274331
  · exact B1274335
  · exact B1274339
  · exact B1274343
  · exact B1274347
  · exact B1274351
  · exact B1274355
  · exact B1274359
  · exact B1274363
  · exact B1274367
  · exact B1274371
  · exact B1274375
  · exact B1274379
  · exact B1274383
  · exact B1274387
  · exact B1274391
  · exact B1274395
  · exact B1274399
  · exact B1274403
  · exact B1274407
  · exact B1274411
  · exact B1274415
  · exact B1274419
  · exact B1274423
  · exact B1274427
  · exact B1274431
  · exact B1274435
  · exact B1274439
  · exact B1274443
  · exact B1274447
  · exact B1274451
  · exact B1274455
  · exact B1274459
  · exact B1274463
  · exact B1274467
  · exact B1274471
  · exact B1274475
  · exact B1274479
  · exact B1274483
  · exact B1274487
  · exact B1274491
  · exact B1274495
  · exact B1274499
  · exact B1274503
  · exact B1274507
  · exact B1274511
  · exact B1274515
  · exact B1274519
  · exact B1274523
  · exact B1274527
  · exact B1274531
  · exact B1274535
  · exact B1274539
  · exact B1274543
  · exact B1274547
  · exact B1274551
  · exact B1274555
  · exact B1274559
  · exact B1274563
  · exact B1274567
  · exact B1274571
  · exact B1274575
  · exact B1274579
  · exact B1274583
  · exact B1274587
  · exact B1274591
  · exact B1274595
  · exact B1274599
  · exact B1274603
  · exact B1274607
  · exact B1274611
  · exact B1274615
  · exact B1274619
  · exact B1274623
  · exact B1274627
  · exact B1274631
  · exact B1274635
  · exact B1274639
  · exact B1274643
  · exact B1274647
  · exact B1274651
  · exact B1274655
  · exact B1274659
  · exact B1274663
  · exact B1274667
  · exact B1274671
  · exact B1274675
  · exact B1274679
  · exact B1274683
  · exact B1274687
  · exact B1274691
  · exact B1274695
  · exact B1274699
  · exact B1274703
  · exact B1274707
  · exact B1274711
  · exact B1274715
  · exact B1274719
  · exact B1274723
  · exact B1274727
  · exact B1274731
  · exact B1274735
  · exact B1274739
  · exact B1274743
  · exact B1274747
  · exact B1274751
  · exact B1274755
  · exact B1274759
  · exact B1274763
  · exact B1274767
  · exact B1274771
  · exact B1274775
  · exact B1274779
  · exact B1274783
  · exact B1274787
  · exact B1274791
  · exact B1274795
  · exact B1274799
  · exact B1274803
  · exact B1274807
  · exact B1274811
  · exact B1274815
  · exact B1274819
  · exact B1274823
  · exact B1274827
  · exact B1274831
  · exact B1274835
  · exact B1274839
  · exact B1274843
  · exact B1274847
  · exact B1274851
  · exact B1274855
  · exact B1274859
  · exact B1274863
  · exact B1274867
  · exact B1274871
  · exact B1274875
  · exact B1274879
  · exact B1274883
  · exact B1274887
  · exact B1274891
  · exact B1274895
  · exact B1274899
  · exact B1274903
  · exact B1274907
  · exact B1274911
  · exact B1274915
  · exact B1274919
  · exact B1274923
  · exact B1274927
  · exact B1274931
  · exact B1274935
  · exact B1274939
  · exact B1274943
  · exact B1274947
  · exact B1274951
  · exact B1274955
  · exact B1274959
  · exact B1274963
  · exact B1274967
  · exact B1274971
  · exact B1274975
  · exact B1274979
  · exact B1274983
  · exact B1274987
  · exact B1274991
  · exact B1274995
  · exact B1274999
  · exact B1275003
  · exact B1275007
  · exact B1275011
  · exact B1275015
  · exact B1275019
  · exact B1275023
  · exact B1275027
  · exact B1275031
  · exact B1275035
  · exact B1275039
  · exact B1275043
  · exact B1275047
  · exact B1275051
  · exact B1275055
  · exact B1275059
  · exact B1275063
  · exact B1275067
  · exact B1275071
  · exact B1275075
  · exact B1275079
  · exact B1275083
  · exact B1275087
  · exact B1275091
  · exact B1275095
  · exact B1275099
  · exact B1275103
  · exact B1275107
  · exact B1275111
  · exact B1275115
  · exact B1275119
  · exact B1275123
  · exact B1275127
  · exact B1275131
  · exact B1275135
  · exact B1275139
  · exact B1275143
  · exact B1275147
  · exact B1275151
  · exact B1275155
  · exact B1275159
  · exact B1275163
  · exact B1275167
  · exact B1275171
  · exact B1275175
  · exact B1275179
  · exact B1275183
  · exact B1275187
  · exact B1275191
  · exact B1275195
  · exact B1275199
  · exact B1275203
  · exact B1275207
  · exact B1275211
  · exact B1275215
  · exact B1275219
  · exact B1275223
  · exact B1275227
  · exact B1275231
  · exact B1275235
  · exact B1275239
  · exact B1275243
  · exact B1275247
  · exact B1275251
  · exact B1275255
  · exact B1275259
  · exact B1275263
  · exact B1275267
  · exact B1275271
  · exact B1275275
  · exact B1275279
  · exact B1275283
  · exact B1275287
  · exact B1275291
  · exact B1275295
  · exact B1275299
  · exact B1275303
  · exact B1275307
  · exact B1275311
  · exact B1275315
  · exact B1275319
  · exact B1275323
  · exact B1275327
  · exact B1275331
  · exact B1275335
  · exact B1275339
  · exact B1275343
  · exact B1275347
  · exact B1275351
  · exact B1275355
  · exact B1275359
  · exact B1275363
  · exact B1275367
  · exact B1275371
  · exact B1275375
  · exact B1275379
  · exact B1275383
  · exact B1275387
  · exact B1275391
  · exact B1275395
  · exact B1275399
  · exact B1275403
  · exact B1275407
  · exact B1275411
  · exact B1275415
  · exact B1275419
  · exact B1275423
  · exact B1275427
  · exact B1275431
  · exact B1275435
  · exact B1275439
  · exact B1275443
  · exact B1275447
  · exact B1275451
  · exact B1275455
  · exact B1275459
  · exact B1275463
  · exact B1275467
  · exact B1275471
  · exact B1275475
  · exact B1275479
  · exact B1275483
  · exact B1275487
  · exact B1275491
  · exact B1275495
  · exact B1275499
  · exact B1275503
  · exact B1275507
  · exact B1275511
  · exact B1275515
  · exact B1275519
  · exact B1275523
  · exact B1275527
  · exact B1275531
  · exact B1275535
  · exact B1275539
  · exact B1275543
  · exact B1275547
  · exact B1275551
  · exact B1275555
  · exact B1275559
  · exact B1275563
  · exact B1275567
  · exact B1275571
  · exact B1275575
  · exact B1275579
  · exact B1275583
  · exact B1275587
  · exact B1275591
  · exact B1275595
  · exact B1275599
  · exact B1275603
  · exact B1275607
  · exact B1275611
  · exact B1275615
  · exact B1275619
  · exact B1275623
  · exact B1275627
  · exact B1275631
  · exact B1275635
  · exact B1275639
  · exact B1275643
  · exact B1275647
  · exact B1275651
  · exact B1275655
  · exact B1275659
  · exact B1275663
  · exact B1275667
  · exact B1275671
  · exact B1275675
  · exact B1275679
  · exact B1275683
  · exact B1275687
  · exact B1275691
  · exact B1275695
  · exact B1275699
  · exact B1275703
  · exact B1275707
  · exact B1275711
  · exact B1275715
  · exact B1275719
  · exact B1275723
  · exact B1275727
  · exact B1275731
  · exact B1275735
  · exact B1275739
  · exact B1275743
  · exact B1275747
  · exact B1275751
  · exact B1275755
  · exact B1275759
  · exact B1275763
  · exact B1275767
  · exact B1275771
  · exact B1275775
  · exact B1275779
  · exact B1275783
  · exact B1275787
  · exact B1275791
  · exact B1275795
  · exact B1275799
  · exact B1275803
  · exact B1275807
  · exact B1275811
  · exact B1275815
  · exact B1275819
  · exact B1275823
  · exact B1275827
  · exact B1275831
  · exact B1275835
  · exact B1275839
  · exact B1275843
  · exact B1275847
  · exact B1275851
  · exact B1275855
  · exact B1275859
  · exact B1275863
  · exact B1275867
  · exact B1275871
  · exact B1275875
  · exact B1275879
  · exact B1275883
  · exact B1275887
  · exact B1275891
  · exact B1275895
  · exact B1275899
  · exact B1275903
  · exact B1275907
  · exact B1275911
  · exact B1275915
  · exact B1275919
  · exact B1275923
  · exact B1275927
  · exact B1275931
  · exact B1275935
  · exact B1275939
  · exact B1275943
  · exact B1275947
  · exact B1275951
  · exact B1275955

theorem solution (m : ℕ) (hlo : 1273955 ≤ m) (hhi : m ≤ 1275955) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 318488 ≤ j := by omega
    have hj2 : j ≤ 318988 := by omega
    have hb : Blo 1273955 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
