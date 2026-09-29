-- Prove2me | solution 1 for syracuse_descends_range_642303_646303
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:45.401589+00:00
-- url     : https://prove2.me/submissions/20c64230-4a5b-47eb-9807-01bc02d4ec5b

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


theorem B1572941 : Blo 642303 1572941 := bbase (se 3 (by rfl) ⟨294926, by rfl⟩ : syracuseStep 1572941 = 589853) (by norm_num)
theorem B2752613 : Blo 642303 2752613 := bbase (se 4 (by rfl) ⟨258057, by rfl⟩ : syracuseStep 2752613 = 516115) (by norm_num)
theorem B917669 : Blo 642303 917669 := bbase (se 4 (by rfl) ⟨86031, by rfl⟩ : syracuseStep 917669 = 172063) (by norm_num)
theorem B688333 : Blo 642303 688333 := bbase (se 3 (by rfl) ⟨129062, by rfl⟩ : syracuseStep 688333 = 258125) (by norm_num)
theorem B688457 : Blo 642303 688457 := bbase (se 2 (by rfl) ⟨258171, by rfl⟩ : syracuseStep 688457 = 516343) (by norm_num)
theorem B885109 : Blo 642303 885109 := bbase (se 5 (by rfl) ⟨41489, by rfl⟩ : syracuseStep 885109 = 82979) (by norm_num)
theorem B688709 : Blo 642303 688709 := bbase (se 4 (by rfl) ⟨64566, by rfl⟩ : syracuseStep 688709 = 129133) (by norm_num)
theorem B1114717 : Blo 642303 1114717 := bbase (se 3 (by rfl) ⟨209009, by rfl⟩ : syracuseStep 1114717 = 418019) (by norm_num)
theorem B918221 : Blo 642303 918221 := bbase (se 3 (by rfl) ⟨172166, by rfl⟩ : syracuseStep 918221 = 344333) (by norm_num)
theorem B2753365 : Blo 642303 2753365 := bbase (se 9 (by rfl) ⟨8066, by rfl⟩ : syracuseStep 2753365 = 16133) (by norm_num)
theorem B17662805 : Blo 642303 17662805 := bbase (se 9 (by rfl) ⟨51746, by rfl⟩ : syracuseStep 17662805 = 103493) (by norm_num)
theorem B10617749 : Blo 642303 10617749 := bbase (se 6 (by rfl) ⟨248853, by rfl⟩ : syracuseStep 10617749 = 497707) (by norm_num)
theorem B1770389 : Blo 642303 1770389 := bbase (se 6 (by rfl) ⟨41493, by rfl⟩ : syracuseStep 1770389 = 82987) (by norm_num)
theorem B1835941 : Blo 642303 1835941 := bbase (se 4 (by rfl) ⟨172119, by rfl⟩ : syracuseStep 1835941 = 344239) (by norm_num)
theorem B6783925 : Blo 642303 6783925 := bbase (se 5 (by rfl) ⟨317996, by rfl⟩ : syracuseStep 6783925 = 635993) (by norm_num)
theorem B689153 : Blo 642303 689153 := bbase (se 2 (by rfl) ⟨258432, by rfl⟩ : syracuseStep 689153 = 516865) (by norm_num)
theorem B1836101 : Blo 642303 1836101 := bbase (se 4 (by rfl) ⟨172134, by rfl⟩ : syracuseStep 1836101 = 344269) (by norm_num)
theorem B1377461 : Blo 642303 1377461 := bbase (se 5 (by rfl) ⟨64568, by rfl⟩ : syracuseStep 1377461 = 129137) (by norm_num)
theorem B2786501 : Blo 642303 2786501 := bbase (se 4 (by rfl) ⟨261234, by rfl⟩ : syracuseStep 2786501 = 522469) (by norm_num)
theorem B689401 : Blo 642303 689401 := bbase (se 2 (by rfl) ⟨258525, by rfl⟩ : syracuseStep 689401 = 517051) (by norm_num)
theorem B1836341 : Blo 642303 1836341 := bbase (se 5 (by rfl) ⟨86078, by rfl⟩ : syracuseStep 1836341 = 172157) (by norm_num)
theorem B1377605 : Blo 642303 1377605 := bbase (se 4 (by rfl) ⟨129150, by rfl⟩ : syracuseStep 1377605 = 258301) (by norm_num)
theorem B918973 : Blo 642303 918973 := bbase (se 3 (by rfl) ⟨172307, by rfl⟩ : syracuseStep 918973 = 344615) (by norm_num)
theorem B1836533 : Blo 642303 1836533 := bbase (se 5 (by rfl) ⟨86087, by rfl⟩ : syracuseStep 1836533 = 172175) (by norm_num)
theorem B2754101 : Blo 642303 2754101 := bbase (se 5 (by rfl) ⟨129098, by rfl⟩ : syracuseStep 2754101 = 258197) (by norm_num)
theorem B722605 : Blo 642303 722605 := bbase (se 3 (by rfl) ⟨135488, by rfl⟩ : syracuseStep 722605 = 270977) (by norm_num)
theorem B1377965 : Blo 642303 1377965 := bbase (se 3 (by rfl) ⟨258368, by rfl⟩ : syracuseStep 1377965 = 516737) (by norm_num)
theorem B689845 : Blo 642303 689845 := bbase (se 5 (by rfl) ⟨32336, by rfl⟩ : syracuseStep 689845 = 64673) (by norm_num)
theorem B722641 : Blo 642303 722641 := bbase (se 2 (by rfl) ⟨270990, by rfl⟩ : syracuseStep 722641 = 541981) (by norm_num)
theorem B11175637 : Blo 642303 11175637 := bbase (se 7 (by rfl) ⟨130964, by rfl⟩ : syracuseStep 11175637 = 261929) (by norm_num)
theorem B689905 : Blo 642303 689905 := bbase (se 2 (by rfl) ⟨258714, by rfl⟩ : syracuseStep 689905 = 517429) (by norm_num)
theorem B722677 : Blo 642303 722677 := bbase (se 5 (by rfl) ⟨33875, by rfl⟩ : syracuseStep 722677 = 67751) (by norm_num)
theorem B722713 : Blo 642303 722713 := bbase (se 2 (by rfl) ⟨271017, by rfl⟩ : syracuseStep 722713 = 542035) (by norm_num)
theorem B722749 : Blo 642303 722749 := bbase (se 3 (by rfl) ⟨135515, by rfl⟩ : syracuseStep 722749 = 271031) (by norm_num)
theorem B722785 : Blo 642303 722785 := bbase (se 2 (by rfl) ⟨271044, by rfl⟩ : syracuseStep 722785 = 542089) (by norm_num)
theorem B722821 : Blo 642303 722821 := bbase (se 4 (by rfl) ⟨67764, by rfl⟩ : syracuseStep 722821 = 135529) (by norm_num)
theorem B722857 : Blo 642303 722857 := bbase (se 2 (by rfl) ⟨271071, by rfl⟩ : syracuseStep 722857 = 542143) (by norm_num)
theorem B722893 : Blo 642303 722893 := bbase (se 3 (by rfl) ⟨135542, by rfl⟩ : syracuseStep 722893 = 271085) (by norm_num)
theorem B722929 : Blo 642303 722929 := bbase (se 2 (by rfl) ⟨271098, by rfl⟩ : syracuseStep 722929 = 542197) (by norm_num)
theorem B722965 : Blo 642303 722965 := bbase (se 6 (by rfl) ⟨16944, by rfl⟩ : syracuseStep 722965 = 33889) (by norm_num)
theorem B723001 : Blo 642303 723001 := bbase (se 2 (by rfl) ⟨271125, by rfl⟩ : syracuseStep 723001 = 542251) (by norm_num)
theorem B723037 : Blo 642303 723037 := bbase (se 3 (by rfl) ⟨135569, by rfl⟩ : syracuseStep 723037 = 271139) (by norm_num)
theorem B723073 : Blo 642303 723073 := bbase (se 2 (by rfl) ⟨271152, by rfl⟩ : syracuseStep 723073 = 542305) (by norm_num)
theorem B723109 : Blo 642303 723109 := bbase (se 4 (by rfl) ⟨67791, by rfl⟩ : syracuseStep 723109 = 135583) (by norm_num)
theorem B723145 : Blo 642303 723145 := bbase (se 2 (by rfl) ⟨271179, by rfl⟩ : syracuseStep 723145 = 542359) (by norm_num)
theorem B919765 : Blo 642303 919765 := bbase (se 7 (by rfl) ⟨10778, by rfl⟩ : syracuseStep 919765 = 21557) (by norm_num)
theorem B723181 : Blo 642303 723181 := bbase (se 3 (by rfl) ⟨135596, by rfl⟩ : syracuseStep 723181 = 271193) (by norm_num)
theorem B723217 : Blo 642303 723217 := bbase (se 2 (by rfl) ⟨271206, by rfl⟩ : syracuseStep 723217 = 542413) (by norm_num)
theorem B723253 : Blo 642303 723253 := bbase (se 5 (by rfl) ⟨33902, by rfl⟩ : syracuseStep 723253 = 67805) (by norm_num)
theorem B723289 : Blo 642303 723289 := bbase (se 2 (by rfl) ⟨271233, by rfl⟩ : syracuseStep 723289 = 542467) (by norm_num)
theorem B723325 : Blo 642303 723325 := bbase (se 3 (by rfl) ⟨135623, by rfl⟩ : syracuseStep 723325 = 271247) (by norm_num)
theorem B723361 : Blo 642303 723361 := bbase (se 2 (by rfl) ⟨271260, by rfl⟩ : syracuseStep 723361 = 542521) (by norm_num)
theorem B723397 : Blo 642303 723397 := bbase (se 4 (by rfl) ⟨67818, by rfl⟩ : syracuseStep 723397 = 135637) (by norm_num)
theorem B1837525 : Blo 642303 1837525 := bbase (se 7 (by rfl) ⟨21533, by rfl⟩ : syracuseStep 1837525 = 43067) (by norm_num)
theorem B723433 : Blo 642303 723433 := bbase (se 2 (by rfl) ⟨271287, by rfl⟩ : syracuseStep 723433 = 542575) (by norm_num)
theorem B1083901 : Blo 642303 1083901 := bbase (se 3 (by rfl) ⟨203231, by rfl⟩ : syracuseStep 1083901 = 406463) (by norm_num)
theorem B723469 : Blo 642303 723469 := bbase (se 3 (by rfl) ⟨135650, by rfl⟩ : syracuseStep 723469 = 271301) (by norm_num)
theorem B1378853 : Blo 642303 1378853 := bbase (se 4 (by rfl) ⟨129267, by rfl⟩ : syracuseStep 1378853 = 258535) (by norm_num)
theorem B920101 : Blo 642303 920101 := bbase (se 4 (by rfl) ⟨86259, by rfl⟩ : syracuseStep 920101 = 172519) (by norm_num)
theorem B723505 : Blo 642303 723505 := bbase (se 2 (by rfl) ⟨271314, by rfl⟩ : syracuseStep 723505 = 542629) (by norm_num)
theorem B1083989 : Blo 642303 1083989 := bbase (se 8 (by rfl) ⟨6351, by rfl⟩ : syracuseStep 1083989 = 12703) (by norm_num)
theorem B723541 : Blo 642303 723541 := bbase (se 8 (by rfl) ⟨4239, by rfl⟩ : syracuseStep 723541 = 8479) (by norm_num)
theorem B723577 : Blo 642303 723577 := bbase (se 2 (by rfl) ⟨271341, by rfl⟩ : syracuseStep 723577 = 542683) (by norm_num)
theorem B723613 : Blo 642303 723613 := bbase (se 3 (by rfl) ⟨135677, by rfl⟩ : syracuseStep 723613 = 271355) (by norm_num)
theorem B2067125 : Blo 642303 2067125 := bbase (se 5 (by rfl) ⟨96896, by rfl⟩ : syracuseStep 2067125 = 193793) (by norm_num)
theorem B723649 : Blo 642303 723649 := bbase (se 2 (by rfl) ⟨271368, by rfl⟩ : syracuseStep 723649 = 542737) (by norm_num)
theorem B1084117 : Blo 642303 1084117 := bbase (se 7 (by rfl) ⟨12704, by rfl⟩ : syracuseStep 1084117 = 25409) (by norm_num)
theorem B723685 : Blo 642303 723685 := bbase (se 4 (by rfl) ⟨67845, by rfl⟩ : syracuseStep 723685 = 135691) (by norm_num)
theorem B723721 : Blo 642303 723721 := bbase (se 2 (by rfl) ⟨271395, by rfl⟩ : syracuseStep 723721 = 542791) (by norm_num)
theorem B1379101 : Blo 642303 1379101 := bbase (se 3 (by rfl) ⟨258581, by rfl⟩ : syracuseStep 1379101 = 517163) (by norm_num)
theorem B1084205 : Blo 642303 1084205 := bbase (se 3 (by rfl) ⟨203288, by rfl⟩ : syracuseStep 1084205 = 406577) (by norm_num)
theorem B723757 : Blo 642303 723757 := bbase (se 3 (by rfl) ⟨135704, by rfl⟩ : syracuseStep 723757 = 271409) (by norm_num)
theorem B723793 : Blo 642303 723793 := bbase (se 2 (by rfl) ⟨271422, by rfl⟩ : syracuseStep 723793 = 542845) (by norm_num)
theorem B723829 : Blo 642303 723829 := bbase (se 5 (by rfl) ⟨33929, by rfl⟩ : syracuseStep 723829 = 67859) (by norm_num)
theorem B723865 : Blo 642303 723865 := bbase (se 2 (by rfl) ⟨271449, by rfl⟩ : syracuseStep 723865 = 542899) (by norm_num)
theorem B1084333 : Blo 642303 1084333 := bbase (se 3 (by rfl) ⟨203312, by rfl⟩ : syracuseStep 1084333 = 406625) (by norm_num)
theorem B723901 : Blo 642303 723901 := bbase (se 3 (by rfl) ⟨135731, by rfl⟩ : syracuseStep 723901 = 271463) (by norm_num)
theorem B723937 : Blo 642303 723937 := bbase (se 2 (by rfl) ⟨271476, by rfl⟩ : syracuseStep 723937 = 542953) (by norm_num)
theorem B1084421 : Blo 642303 1084421 := bbase (se 4 (by rfl) ⟨101664, by rfl⟩ : syracuseStep 1084421 = 203329) (by norm_num)
theorem B723973 : Blo 642303 723973 := bbase (se 4 (by rfl) ⟨67872, by rfl⟩ : syracuseStep 723973 = 135745) (by norm_num)
theorem B724009 : Blo 642303 724009 := bbase (se 2 (by rfl) ⟨271503, by rfl⟩ : syracuseStep 724009 = 543007) (by norm_num)
theorem B724045 : Blo 642303 724045 := bbase (se 3 (by rfl) ⟨135758, by rfl⟩ : syracuseStep 724045 = 271517) (by norm_num)
theorem B724081 : Blo 642303 724081 := bbase (se 2 (by rfl) ⟨271530, by rfl⟩ : syracuseStep 724081 = 543061) (by norm_num)
theorem B1084549 : Blo 642303 1084549 := bbase (se 4 (by rfl) ⟨101676, by rfl⟩ : syracuseStep 1084549 = 203353) (by norm_num)
theorem B724117 : Blo 642303 724117 := bbase (se 6 (by rfl) ⟨16971, by rfl⟩ : syracuseStep 724117 = 33943) (by norm_num)
theorem B724153 : Blo 642303 724153 := bbase (se 2 (by rfl) ⟨271557, by rfl⟩ : syracuseStep 724153 = 543115) (by norm_num)
theorem B1084637 : Blo 642303 1084637 := bbase (se 3 (by rfl) ⟨203369, by rfl⟩ : syracuseStep 1084637 = 406739) (by norm_num)
theorem B724189 : Blo 642303 724189 := bbase (se 3 (by rfl) ⟨135785, by rfl⟩ : syracuseStep 724189 = 271571) (by norm_num)
theorem B724225 : Blo 642303 724225 := bbase (se 2 (by rfl) ⟨271584, by rfl⟩ : syracuseStep 724225 = 543169) (by norm_num)
theorem B1543445 : Blo 642303 1543445 := bbase (se 6 (by rfl) ⟨36174, by rfl⟩ : syracuseStep 1543445 = 72349) (by norm_num)
theorem B1379605 : Blo 642303 1379605 := bbase (se 6 (by rfl) ⟨32334, by rfl⟩ : syracuseStep 1379605 = 64669) (by norm_num)
theorem B724261 : Blo 642303 724261 := bbase (se 4 (by rfl) ⟨67899, by rfl⟩ : syracuseStep 724261 = 135799) (by norm_num)
theorem B724297 : Blo 642303 724297 := bbase (se 2 (by rfl) ⟨271611, by rfl⟩ : syracuseStep 724297 = 543223) (by norm_num)
theorem B1084765 : Blo 642303 1084765 := bbase (se 3 (by rfl) ⟨203393, by rfl⟩ : syracuseStep 1084765 = 406787) (by norm_num)
theorem B724333 : Blo 642303 724333 := bbase (se 3 (by rfl) ⟨135812, by rfl⟩ : syracuseStep 724333 = 271625) (by norm_num)
theorem B1445237 : Blo 642303 1445237 := bbase (se 5 (by rfl) ⟨67745, by rfl⟩ : syracuseStep 1445237 = 135491) (by norm_num)
theorem B724369 : Blo 642303 724369 := bbase (se 2 (by rfl) ⟨271638, by rfl⟩ : syracuseStep 724369 = 543277) (by norm_num)
theorem B1084853 : Blo 642303 1084853 := bbase (se 5 (by rfl) ⟨50852, by rfl⟩ : syracuseStep 1084853 = 101705) (by norm_num)
theorem B724405 : Blo 642303 724405 := bbase (se 5 (by rfl) ⟨33956, by rfl⟩ : syracuseStep 724405 = 67913) (by norm_num)
theorem B1445309 : Blo 642303 1445309 := bbase (se 3 (by rfl) ⟨270995, by rfl⟩ : syracuseStep 1445309 = 541991) (by norm_num)
theorem B724441 : Blo 642303 724441 := bbase (se 2 (by rfl) ⟨271665, by rfl⟩ : syracuseStep 724441 = 543331) (by norm_num)
theorem B724477 : Blo 642303 724477 := bbase (se 3 (by rfl) ⟨135839, by rfl⟩ : syracuseStep 724477 = 271679) (by norm_num)
theorem B1445381 : Blo 642303 1445381 := bbase (se 4 (by rfl) ⟨135504, by rfl⟩ : syracuseStep 1445381 = 271009) (by norm_num)
theorem B724513 : Blo 642303 724513 := bbase (se 2 (by rfl) ⟨271692, by rfl⟩ : syracuseStep 724513 = 543385) (by norm_num)
theorem B1838629 : Blo 642303 1838629 := bbase (se 4 (by rfl) ⟨172371, by rfl⟩ : syracuseStep 1838629 = 344743) (by norm_num)
theorem B1084981 : Blo 642303 1084981 := bbase (se 5 (by rfl) ⟨50858, by rfl⟩ : syracuseStep 1084981 = 101717) (by norm_num)
theorem B724549 : Blo 642303 724549 := bbase (se 4 (by rfl) ⟨67926, by rfl⟩ : syracuseStep 724549 = 135853) (by norm_num)
theorem B2068037 : Blo 642303 2068037 := bbase (se 4 (by rfl) ⟨193878, by rfl⟩ : syracuseStep 2068037 = 387757) (by norm_num)
theorem B1445453 : Blo 642303 1445453 := bbase (se 3 (by rfl) ⟨271022, by rfl⟩ : syracuseStep 1445453 = 542045) (by norm_num)
theorem B724585 : Blo 642303 724585 := bbase (se 2 (by rfl) ⟨271719, by rfl⟩ : syracuseStep 724585 = 543439) (by norm_num)
theorem B1085069 : Blo 642303 1085069 := bbase (se 3 (by rfl) ⟨203450, by rfl⟩ : syracuseStep 1085069 = 406901) (by norm_num)
theorem B724621 : Blo 642303 724621 := bbase (se 3 (by rfl) ⟨135866, by rfl⟩ : syracuseStep 724621 = 271733) (by norm_num)
theorem B1445525 : Blo 642303 1445525 := bbase (se 6 (by rfl) ⟨33879, by rfl⟩ : syracuseStep 1445525 = 67759) (by norm_num)
theorem B724657 : Blo 642303 724657 := bbase (se 2 (by rfl) ⟨271746, by rfl⟩ : syracuseStep 724657 = 543493) (by norm_num)
theorem B724693 : Blo 642303 724693 := bbase (se 7 (by rfl) ⟨8492, by rfl⟩ : syracuseStep 724693 = 16985) (by norm_num)
theorem B1445597 : Blo 642303 1445597 := bbase (se 3 (by rfl) ⟨271049, by rfl⟩ : syracuseStep 1445597 = 542099) (by norm_num)
theorem B724729 : Blo 642303 724729 := bbase (se 2 (by rfl) ⟨271773, by rfl⟩ : syracuseStep 724729 = 543547) (by norm_num)
theorem B1085197 : Blo 642303 1085197 := bbase (se 3 (by rfl) ⟨203474, by rfl⟩ : syracuseStep 1085197 = 406949) (by norm_num)
theorem B724765 : Blo 642303 724765 := bbase (se 3 (by rfl) ⟨135893, by rfl⟩ : syracuseStep 724765 = 271787) (by norm_num)
theorem B1445669 : Blo 642303 1445669 := bbase (se 4 (by rfl) ⟨135531, by rfl⟩ : syracuseStep 1445669 = 271063) (by norm_num)
theorem B5508917 : Blo 642303 5508917 := bbase (se 5 (by rfl) ⟨258230, by rfl⟩ : syracuseStep 5508917 = 516461) (by norm_num)
theorem B724801 : Blo 642303 724801 := bbase (se 2 (by rfl) ⟨271800, by rfl⟩ : syracuseStep 724801 = 543601) (by norm_num)
theorem B1740613 : Blo 642303 1740613 := bbase (se 4 (by rfl) ⟨163182, by rfl⟩ : syracuseStep 1740613 = 326365) (by norm_num)
theorem B1085285 : Blo 642303 1085285 := bbase (se 4 (by rfl) ⟨101745, by rfl⟩ : syracuseStep 1085285 = 203491) (by norm_num)
theorem B724837 : Blo 642303 724837 := bbase (se 4 (by rfl) ⟨67953, by rfl⟩ : syracuseStep 724837 = 135907) (by norm_num)
theorem B1445741 : Blo 642303 1445741 := bbase (se 3 (by rfl) ⟨271076, by rfl⟩ : syracuseStep 1445741 = 542153) (by norm_num)
theorem B724873 : Blo 642303 724873 := bbase (se 2 (by rfl) ⟨271827, by rfl⟩ : syracuseStep 724873 = 543655) (by norm_num)
theorem B724909 : Blo 642303 724909 := bbase (se 3 (by rfl) ⟨135920, by rfl⟩ : syracuseStep 724909 = 271841) (by norm_num)
theorem B1445813 : Blo 642303 1445813 := bbase (se 5 (by rfl) ⟨67772, by rfl⟩ : syracuseStep 1445813 = 135545) (by norm_num)
theorem B724945 : Blo 642303 724945 := bbase (se 2 (by rfl) ⟨271854, by rfl⟩ : syracuseStep 724945 = 543709) (by norm_num)
theorem B3674069 : Blo 642303 3674069 := bbase (se 7 (by rfl) ⟨43055, by rfl⟩ : syracuseStep 3674069 = 86111) (by norm_num)
theorem B1085413 : Blo 642303 1085413 := bbase (se 4 (by rfl) ⟨101757, by rfl⟩ : syracuseStep 1085413 = 203515) (by norm_num)
theorem B724981 : Blo 642303 724981 := bbase (se 5 (by rfl) ⟨33983, by rfl⟩ : syracuseStep 724981 = 67967) (by norm_num)
theorem B1445885 : Blo 642303 1445885 := bbase (se 3 (by rfl) ⟨271103, by rfl⟩ : syracuseStep 1445885 = 542207) (by norm_num)
theorem B3313685 : Blo 642303 3313685 := bbase (se 6 (by rfl) ⟨77664, by rfl⟩ : syracuseStep 3313685 = 155329) (by norm_num)
theorem B725017 : Blo 642303 725017 := bbase (se 2 (by rfl) ⟨271881, by rfl⟩ : syracuseStep 725017 = 543763) (by norm_num)
theorem B1085501 : Blo 642303 1085501 := bbase (se 3 (by rfl) ⟨203531, by rfl⟩ : syracuseStep 1085501 = 407063) (by norm_num)
theorem B725053 : Blo 642303 725053 := bbase (se 3 (by rfl) ⟨135947, by rfl⟩ : syracuseStep 725053 = 271895) (by norm_num)
theorem B1445957 : Blo 642303 1445957 := bbase (se 4 (by rfl) ⟨135558, by rfl⟩ : syracuseStep 1445957 = 271117) (by norm_num)
theorem B725089 : Blo 642303 725089 := bbase (se 2 (by rfl) ⟨271908, by rfl⟩ : syracuseStep 725089 = 543817) (by norm_num)
theorem B2199653 : Blo 642303 2199653 := bbase (se 4 (by rfl) ⟨206217, by rfl⟩ : syracuseStep 2199653 = 412435) (by norm_num)
theorem B725125 : Blo 642303 725125 := bbase (se 4 (by rfl) ⟨67980, by rfl⟩ : syracuseStep 725125 = 135961) (by norm_num)
theorem B1446029 : Blo 642303 1446029 := bbase (se 3 (by rfl) ⟨271130, by rfl⟩ : syracuseStep 1446029 = 542261) (by norm_num)
theorem B725161 : Blo 642303 725161 := bbase (se 2 (by rfl) ⟨271935, by rfl⟩ : syracuseStep 725161 = 543871) (by norm_num)
theorem B1085629 : Blo 642303 1085629 := bbase (se 3 (by rfl) ⟨203555, by rfl⟩ : syracuseStep 1085629 = 407111) (by norm_num)
theorem B725197 : Blo 642303 725197 := bbase (se 3 (by rfl) ⟨135974, by rfl⟩ : syracuseStep 725197 = 271949) (by norm_num)
theorem B1446101 : Blo 642303 1446101 := bbase (se 7 (by rfl) ⟨16946, by rfl⟩ : syracuseStep 1446101 = 33893) (by norm_num)
theorem B725233 : Blo 642303 725233 := bbase (se 2 (by rfl) ⟨271962, by rfl⟩ : syracuseStep 725233 = 543925) (by norm_num)
theorem B1085717 : Blo 642303 1085717 := bbase (se 6 (by rfl) ⟨25446, by rfl⟩ : syracuseStep 1085717 = 50893) (by norm_num)
theorem B725269 : Blo 642303 725269 := bbase (se 6 (by rfl) ⟨16998, by rfl⟩ : syracuseStep 725269 = 33997) (by norm_num)
theorem B1446173 : Blo 642303 1446173 := bbase (se 3 (by rfl) ⟨271157, by rfl⟩ : syracuseStep 1446173 = 542315) (by norm_num)
theorem B725305 : Blo 642303 725305 := bbase (se 2 (by rfl) ⟨271989, by rfl⟩ : syracuseStep 725305 = 543979) (by norm_num)
theorem B725341 : Blo 642303 725341 := bbase (se 3 (by rfl) ⟨136001, by rfl⟩ : syracuseStep 725341 = 272003) (by norm_num)
theorem B1446245 : Blo 642303 1446245 := bbase (se 4 (by rfl) ⟨135585, by rfl⟩ : syracuseStep 1446245 = 271171) (by norm_num)
theorem B725377 : Blo 642303 725377 := bbase (se 2 (by rfl) ⟨272016, by rfl⟩ : syracuseStep 725377 = 544033) (by norm_num)
theorem B1085845 : Blo 642303 1085845 := bbase (se 6 (by rfl) ⟨25449, by rfl⟩ : syracuseStep 1085845 = 50899) (by norm_num)
theorem B725413 : Blo 642303 725413 := bbase (se 4 (by rfl) ⟨68007, by rfl⟩ : syracuseStep 725413 = 136015) (by norm_num)
theorem B1446317 : Blo 642303 1446317 := bbase (se 3 (by rfl) ⟨271184, by rfl⟩ : syracuseStep 1446317 = 542369) (by norm_num)
theorem B725449 : Blo 642303 725449 := bbase (se 2 (by rfl) ⟨272043, by rfl⟩ : syracuseStep 725449 = 544087) (by norm_num)
theorem B1085933 : Blo 642303 1085933 := bbase (se 3 (by rfl) ⟨203612, by rfl⟩ : syracuseStep 1085933 = 407225) (by norm_num)
theorem B725485 : Blo 642303 725485 := bbase (se 3 (by rfl) ⟨136028, by rfl⟩ : syracuseStep 725485 = 272057) (by norm_num)
theorem B1446389 : Blo 642303 1446389 := bbase (se 5 (by rfl) ⟨67799, by rfl⟩ : syracuseStep 1446389 = 135599) (by norm_num)
theorem B2789893 : Blo 642303 2789893 := bbase (se 4 (by rfl) ⟨261552, by rfl⟩ : syracuseStep 2789893 = 523105) (by norm_num)
theorem B725521 : Blo 642303 725521 := bbase (se 2 (by rfl) ⟨272070, by rfl⟩ : syracuseStep 725521 = 544141) (by norm_num)
theorem B725557 : Blo 642303 725557 := bbase (se 5 (by rfl) ⟨34010, by rfl⟩ : syracuseStep 725557 = 68021) (by norm_num)
theorem B1446461 : Blo 642303 1446461 := bbase (se 3 (by rfl) ⟨271211, by rfl⟩ : syracuseStep 1446461 = 542423) (by norm_num)
theorem B725593 : Blo 642303 725593 := bbase (se 2 (by rfl) ⟨272097, by rfl⟩ : syracuseStep 725593 = 544195) (by norm_num)
theorem B1086061 : Blo 642303 1086061 := bbase (se 3 (by rfl) ⟨203636, by rfl⟩ : syracuseStep 1086061 = 407273) (by norm_num)
theorem B725629 : Blo 642303 725629 := bbase (se 3 (by rfl) ⟨136055, by rfl⟩ : syracuseStep 725629 = 272111) (by norm_num)
theorem B1446533 : Blo 642303 1446533 := bbase (se 4 (by rfl) ⟨135612, by rfl⟩ : syracuseStep 1446533 = 271225) (by norm_num)
theorem B725665 : Blo 642303 725665 := bbase (se 2 (by rfl) ⟨272124, by rfl⟩ : syracuseStep 725665 = 544249) (by norm_num)
theorem B1086149 : Blo 642303 1086149 := bbase (se 4 (by rfl) ⟨101826, by rfl⟩ : syracuseStep 1086149 = 203653) (by norm_num)
theorem B725701 : Blo 642303 725701 := bbase (se 4 (by rfl) ⟨68034, by rfl⟩ : syracuseStep 725701 = 136069) (by norm_num)
theorem B1446605 : Blo 642303 1446605 := bbase (se 3 (by rfl) ⟨271238, by rfl⟩ : syracuseStep 1446605 = 542477) (by norm_num)
theorem B725737 : Blo 642303 725737 := bbase (se 2 (by rfl) ⟨272151, by rfl⟩ : syracuseStep 725737 = 544303) (by norm_num)
theorem B725773 : Blo 642303 725773 := bbase (se 3 (by rfl) ⟨136082, by rfl⟩ : syracuseStep 725773 = 272165) (by norm_num)
theorem B1446677 : Blo 642303 1446677 := bbase (se 6 (by rfl) ⟨33906, by rfl⟩ : syracuseStep 1446677 = 67813) (by norm_num)
theorem B2757397 : Blo 642303 2757397 := bbase (se 6 (by rfl) ⟨64626, by rfl⟩ : syracuseStep 2757397 = 129253) (by norm_num)
theorem B725809 : Blo 642303 725809 := bbase (se 2 (by rfl) ⟨272178, by rfl⟩ : syracuseStep 725809 = 544357) (by norm_num)
theorem B1086277 : Blo 642303 1086277 := bbase (se 4 (by rfl) ⟨101838, by rfl⟩ : syracuseStep 1086277 = 203677) (by norm_num)
theorem B725845 : Blo 642303 725845 := bbase (se 9 (by rfl) ⟨2126, by rfl⟩ : syracuseStep 725845 = 4253) (by norm_num)
theorem B1446749 : Blo 642303 1446749 := bbase (se 3 (by rfl) ⟨271265, by rfl⟩ : syracuseStep 1446749 = 542531) (by norm_num)
theorem B725881 : Blo 642303 725881 := bbase (se 2 (by rfl) ⟨272205, by rfl⟩ : syracuseStep 725881 = 544411) (by norm_num)
theorem B2069381 : Blo 642303 2069381 := bbase (se 4 (by rfl) ⟨194004, by rfl⟩ : syracuseStep 2069381 = 388009) (by norm_num)
theorem B824213 : Blo 642303 824213 := bbase (se 6 (by rfl) ⟨19317, by rfl⟩ : syracuseStep 824213 = 38635) (by norm_num)
theorem B1086365 : Blo 642303 1086365 := bbase (se 3 (by rfl) ⟨203693, by rfl⟩ : syracuseStep 1086365 = 407387) (by norm_num)
theorem B725917 : Blo 642303 725917 := bbase (se 3 (by rfl) ⟨136109, by rfl⟩ : syracuseStep 725917 = 272219) (by norm_num)
theorem B1446821 : Blo 642303 1446821 := bbase (se 4 (by rfl) ⟨135639, by rfl⟩ : syracuseStep 1446821 = 271279) (by norm_num)
theorem B725953 : Blo 642303 725953 := bbase (se 2 (by rfl) ⟨272232, by rfl⟩ : syracuseStep 725953 = 544465) (by norm_num)
theorem B725989 : Blo 642303 725989 := bbase (se 4 (by rfl) ⟨68061, by rfl⟩ : syracuseStep 725989 = 136123) (by norm_num)
theorem B1446893 : Blo 642303 1446893 := bbase (se 3 (by rfl) ⟨271292, by rfl⟩ : syracuseStep 1446893 = 542585) (by norm_num)
theorem B1840133 : Blo 642303 1840133 := bbase (se 4 (by rfl) ⟨172512, by rfl⟩ : syracuseStep 1840133 = 345025) (by norm_num)
theorem B726025 : Blo 642303 726025 := bbase (se 2 (by rfl) ⟨272259, by rfl⟩ : syracuseStep 726025 = 544519) (by norm_num)
theorem B2167829 : Blo 642303 2167829 := bbase (se 6 (by rfl) ⟨50808, by rfl⟩ : syracuseStep 2167829 = 101617) (by norm_num)
theorem B1086493 : Blo 642303 1086493 := bbase (se 3 (by rfl) ⟨203717, by rfl⟩ : syracuseStep 1086493 = 407435) (by norm_num)
theorem B726061 : Blo 642303 726061 := bbase (se 3 (by rfl) ⟨136136, by rfl⟩ : syracuseStep 726061 = 272273) (by norm_num)
theorem B1446965 : Blo 642303 1446965 := bbase (se 5 (by rfl) ⟨67826, by rfl⟩ : syracuseStep 1446965 = 135653) (by norm_num)
theorem B726097 : Blo 642303 726097 := bbase (se 2 (by rfl) ⟨272286, by rfl⟩ : syracuseStep 726097 = 544573) (by norm_num)
theorem B1086581 : Blo 642303 1086581 := bbase (se 5 (by rfl) ⟨50933, by rfl⟩ : syracuseStep 1086581 = 101867) (by norm_num)
theorem B3675253 : Blo 642303 3675253 := bbase (se 5 (by rfl) ⟨172277, by rfl⟩ : syracuseStep 3675253 = 344555) (by norm_num)
theorem B726133 : Blo 642303 726133 := bbase (se 5 (by rfl) ⟨34037, by rfl⟩ : syracuseStep 726133 = 68075) (by norm_num)
theorem B1447037 : Blo 642303 1447037 := bbase (se 3 (by rfl) ⟨271319, by rfl⟩ : syracuseStep 1447037 = 542639) (by norm_num)
theorem B4887701 : Blo 642303 4887701 := bbase (se 6 (by rfl) ⟨114555, by rfl⟩ : syracuseStep 4887701 = 229111) (by norm_num)
theorem B726169 : Blo 642303 726169 := bbase (se 2 (by rfl) ⟨272313, by rfl⟩ : syracuseStep 726169 = 544627) (by norm_num)
theorem B726205 : Blo 642303 726205 := bbase (se 3 (by rfl) ⟨136163, by rfl⟩ : syracuseStep 726205 = 272327) (by norm_num)
theorem B1447109 : Blo 642303 1447109 := bbase (se 4 (by rfl) ⟨135666, by rfl⟩ : syracuseStep 1447109 = 271333) (by norm_num)
theorem B824537 : Blo 642303 824537 := bbase (se 2 (by rfl) ⟨309201, by rfl⟩ : syracuseStep 824537 = 618403) (by norm_num)
theorem B726241 : Blo 642303 726241 := bbase (se 2 (by rfl) ⟨272340, by rfl⟩ : syracuseStep 726241 = 544681) (by norm_num)
theorem B1086709 : Blo 642303 1086709 := bbase (se 5 (by rfl) ⟨50939, by rfl⟩ : syracuseStep 1086709 = 101879) (by norm_num)
theorem B726277 : Blo 642303 726277 := bbase (se 4 (by rfl) ⟨68088, by rfl⟩ : syracuseStep 726277 = 136177) (by norm_num)
theorem B1447181 : Blo 642303 1447181 := bbase (se 3 (by rfl) ⟨271346, by rfl⟩ : syracuseStep 1447181 = 542693) (by norm_num)
theorem B726313 : Blo 642303 726313 := bbase (se 2 (by rfl) ⟨272367, by rfl⟩ : syracuseStep 726313 = 544735) (by norm_num)
theorem B1086797 : Blo 642303 1086797 := bbase (se 3 (by rfl) ⟨203774, by rfl⟩ : syracuseStep 1086797 = 407549) (by norm_num)
theorem B726349 : Blo 642303 726349 := bbase (se 3 (by rfl) ⟨136190, by rfl⟩ : syracuseStep 726349 = 272381) (by norm_num)
theorem B1447253 : Blo 642303 1447253 := bbase (se 14 (by rfl) ⟨132, by rfl⟩ : syracuseStep 1447253 = 265) (by norm_num)
theorem B726385 : Blo 642303 726385 := bbase (se 2 (by rfl) ⟨272394, by rfl⟩ : syracuseStep 726385 = 544789) (by norm_num)
theorem B726421 : Blo 642303 726421 := bbase (se 6 (by rfl) ⟨17025, by rfl⟩ : syracuseStep 726421 = 34051) (by norm_num)
theorem B1447325 : Blo 642303 1447325 := bbase (se 3 (by rfl) ⟨271373, by rfl⟩ : syracuseStep 1447325 = 542747) (by norm_num)
theorem B726457 : Blo 642303 726457 := bbase (se 2 (by rfl) ⟨272421, by rfl⟩ : syracuseStep 726457 = 544843) (by norm_num)
theorem B2168261 : Blo 642303 2168261 := bbase (se 4 (by rfl) ⟨203274, by rfl⟩ : syracuseStep 2168261 = 406549) (by norm_num)
theorem B1086925 : Blo 642303 1086925 := bbase (se 3 (by rfl) ⟨203798, by rfl⟩ : syracuseStep 1086925 = 407597) (by norm_num)
theorem B726493 : Blo 642303 726493 := bbase (se 3 (by rfl) ⟨136217, by rfl⟩ : syracuseStep 726493 = 272435) (by norm_num)
theorem B1447397 : Blo 642303 1447397 := bbase (se 4 (by rfl) ⟨135693, by rfl⟩ : syracuseStep 1447397 = 271387) (by norm_num)
theorem B726529 : Blo 642303 726529 := bbase (se 2 (by rfl) ⟨272448, by rfl⟩ : syracuseStep 726529 = 544897) (by norm_num)
theorem B1087013 : Blo 642303 1087013 := bbase (se 4 (by rfl) ⟨101907, by rfl⟩ : syracuseStep 1087013 = 203815) (by norm_num)
theorem B726565 : Blo 642303 726565 := bbase (se 4 (by rfl) ⟨68115, by rfl⟩ : syracuseStep 726565 = 136231) (by norm_num)
theorem B1447469 : Blo 642303 1447469 := bbase (se 3 (by rfl) ⟨271400, by rfl⟩ : syracuseStep 1447469 = 542801) (by norm_num)
theorem B726601 : Blo 642303 726601 := bbase (se 2 (by rfl) ⟨272475, by rfl⟩ : syracuseStep 726601 = 544951) (by norm_num)
theorem B661069 : Blo 642303 661069 := bbase (se 3 (by rfl) ⟨123950, by rfl⟩ : syracuseStep 661069 = 247901) (by norm_num)
theorem B1119853 : Blo 642303 1119853 := bbase (se 3 (by rfl) ⟨209972, by rfl⟩ : syracuseStep 1119853 = 419945) (by norm_num)
theorem B726637 : Blo 642303 726637 := bbase (se 3 (by rfl) ⟨136244, by rfl⟩ : syracuseStep 726637 = 272489) (by norm_num)
theorem B1447541 : Blo 642303 1447541 := bbase (se 5 (by rfl) ⟨67853, by rfl⟩ : syracuseStep 1447541 = 135707) (by norm_num)
theorem B726673 : Blo 642303 726673 := bbase (se 2 (by rfl) ⟨272502, by rfl⟩ : syracuseStep 726673 = 545005) (by norm_num)
theorem B1742485 : Blo 642303 1742485 := bbase (se 6 (by rfl) ⟨40839, by rfl⟩ : syracuseStep 1742485 = 81679) (by norm_num)
theorem B1087141 : Blo 642303 1087141 := bbase (se 4 (by rfl) ⟨101919, by rfl⟩ : syracuseStep 1087141 = 203839) (by norm_num)
theorem B726709 : Blo 642303 726709 := bbase (se 5 (by rfl) ⟨34064, by rfl⟩ : syracuseStep 726709 = 68129) (by norm_num)
theorem B1447613 : Blo 642303 1447613 := bbase (se 3 (by rfl) ⟨271427, by rfl⟩ : syracuseStep 1447613 = 542855) (by norm_num)
theorem B726745 : Blo 642303 726745 := bbase (se 2 (by rfl) ⟨272529, by rfl⟩ : syracuseStep 726745 = 545059) (by norm_num)
theorem B1087229 : Blo 642303 1087229 := bbase (se 3 (by rfl) ⟨203855, by rfl⟩ : syracuseStep 1087229 = 407711) (by norm_num)
theorem B726781 : Blo 642303 726781 := bbase (se 3 (by rfl) ⟨136271, by rfl⟩ : syracuseStep 726781 = 272543) (by norm_num)
theorem B1447685 : Blo 642303 1447685 := bbase (se 4 (by rfl) ⟨135720, by rfl⟩ : syracuseStep 1447685 = 271441) (by norm_num)
theorem B726817 : Blo 642303 726817 := bbase (se 2 (by rfl) ⟨272556, by rfl⟩ : syracuseStep 726817 = 545113) (by norm_num)
theorem B726853 : Blo 642303 726853 := bbase (se 4 (by rfl) ⟨68142, by rfl⟩ : syracuseStep 726853 = 136285) (by norm_num)
theorem B1447757 : Blo 642303 1447757 := bbase (se 3 (by rfl) ⟨271454, by rfl⟩ : syracuseStep 1447757 = 542909) (by norm_num)
theorem B726889 : Blo 642303 726889 := bbase (se 2 (by rfl) ⟨272583, by rfl⟩ : syracuseStep 726889 = 545167) (by norm_num)
theorem B2168693 : Blo 642303 2168693 := bbase (se 5 (by rfl) ⟨101657, by rfl⟩ : syracuseStep 2168693 = 203315) (by norm_num)
theorem B1087357 : Blo 642303 1087357 := bbase (se 3 (by rfl) ⟨203879, by rfl⟩ : syracuseStep 1087357 = 407759) (by norm_num)
theorem B726925 : Blo 642303 726925 := bbase (se 3 (by rfl) ⟨136298, by rfl⟩ : syracuseStep 726925 = 272597) (by norm_num)
theorem B1447829 : Blo 642303 1447829 := bbase (se 6 (by rfl) ⟨33933, by rfl⟩ : syracuseStep 1447829 = 67867) (by norm_num)
theorem B726961 : Blo 642303 726961 := bbase (se 2 (by rfl) ⟨272610, by rfl⟩ : syracuseStep 726961 = 545221) (by norm_num)
theorem B1087445 : Blo 642303 1087445 := bbase (se 7 (by rfl) ⟨12743, by rfl⟩ : syracuseStep 1087445 = 25487) (by norm_num)
theorem B726997 : Blo 642303 726997 := bbase (se 7 (by rfl) ⟨8519, by rfl⟩ : syracuseStep 726997 = 17039) (by norm_num)
theorem B1447901 : Blo 642303 1447901 := bbase (se 3 (by rfl) ⟨271481, by rfl⟩ : syracuseStep 1447901 = 542963) (by norm_num)
theorem B727033 : Blo 642303 727033 := bbase (se 2 (by rfl) ⟨272637, by rfl⟩ : syracuseStep 727033 = 545275) (by norm_num)
theorem B727069 : Blo 642303 727069 := bbase (se 3 (by rfl) ⟨136325, by rfl⟩ : syracuseStep 727069 = 272651) (by norm_num)
theorem B1447973 : Blo 642303 1447973 := bbase (se 4 (by rfl) ⟨135747, by rfl⟩ : syracuseStep 1447973 = 271495) (by norm_num)
theorem B1087573 : Blo 642303 1087573 := bbase (se 8 (by rfl) ⟨6372, by rfl⟩ : syracuseStep 1087573 = 12745) (by norm_num)
theorem B1448045 : Blo 642303 1448045 := bbase (se 3 (by rfl) ⟨271508, by rfl⟩ : syracuseStep 1448045 = 543017) (by norm_num)
theorem B1087661 : Blo 642303 1087661 := bbase (se 3 (by rfl) ⟨203936, by rfl⟩ : syracuseStep 1087661 = 407873) (by norm_num)
theorem B1448117 : Blo 642303 1448117 := bbase (se 5 (by rfl) ⟨67880, by rfl⟩ : syracuseStep 1448117 = 135761) (by norm_num)
theorem B1448189 : Blo 642303 1448189 := bbase (se 3 (by rfl) ⟨271535, by rfl⟩ : syracuseStep 1448189 = 543071) (by norm_num)
theorem B2169125 : Blo 642303 2169125 := bbase (se 4 (by rfl) ⟨203355, by rfl⟩ : syracuseStep 2169125 = 406711) (by norm_num)
theorem B1087789 : Blo 642303 1087789 := bbase (se 3 (by rfl) ⟨203960, by rfl⟩ : syracuseStep 1087789 = 407921) (by norm_num)
theorem B1448261 : Blo 642303 1448261 := bbase (se 4 (by rfl) ⟨135774, by rfl⟩ : syracuseStep 1448261 = 271549) (by norm_num)
theorem B3086677 : Blo 642303 3086677 := bbase (se 10 (by rfl) ⟨4521, by rfl⟩ : syracuseStep 3086677 = 9043) (by norm_num)
theorem B1087877 : Blo 642303 1087877 := bbase (se 4 (by rfl) ⟨101988, by rfl⟩ : syracuseStep 1087877 = 203977) (by norm_num)
theorem B1448333 : Blo 642303 1448333 := bbase (se 3 (by rfl) ⟨271562, by rfl⟩ : syracuseStep 1448333 = 543125) (by norm_num)
theorem B1448405 : Blo 642303 1448405 := bbase (se 7 (by rfl) ⟨16973, by rfl⟩ : syracuseStep 1448405 = 33947) (by norm_num)
theorem B1088005 : Blo 642303 1088005 := bbase (se 4 (by rfl) ⟨102000, by rfl⟩ : syracuseStep 1088005 = 204001) (by norm_num)
theorem B1448477 : Blo 642303 1448477 := bbase (se 3 (by rfl) ⟨271589, by rfl⟩ : syracuseStep 1448477 = 543179) (by norm_num)
theorem B1088093 : Blo 642303 1088093 := bbase (se 3 (by rfl) ⟨204017, by rfl⟩ : syracuseStep 1088093 = 408035) (by norm_num)
theorem B1448549 : Blo 642303 1448549 := bbase (se 4 (by rfl) ⟨135801, by rfl⟩ : syracuseStep 1448549 = 271603) (by norm_num)
theorem B1448621 : Blo 642303 1448621 := bbase (se 3 (by rfl) ⟨271616, by rfl⟩ : syracuseStep 1448621 = 543233) (by norm_num)
theorem B2169557 : Blo 642303 2169557 := bbase (se 7 (by rfl) ⟨25424, by rfl⟩ : syracuseStep 2169557 = 50849) (by norm_num)
theorem B1088221 : Blo 642303 1088221 := bbase (se 3 (by rfl) ⟨204041, by rfl⟩ : syracuseStep 1088221 = 408083) (by norm_num)
theorem B1448693 : Blo 642303 1448693 := bbase (se 5 (by rfl) ⟨67907, by rfl⟩ : syracuseStep 1448693 = 135815) (by norm_num)
theorem B1547029 : Blo 642303 1547029 := bbase (se 6 (by rfl) ⟨36258, by rfl⟩ : syracuseStep 1547029 = 72517) (by norm_num)
theorem B1088309 : Blo 642303 1088309 := bbase (se 5 (by rfl) ⟨51014, by rfl⟩ : syracuseStep 1088309 = 102029) (by norm_num)
theorem B1448765 : Blo 642303 1448765 := bbase (se 3 (by rfl) ⟨271643, by rfl⟩ : syracuseStep 1448765 = 543287) (by norm_num)
theorem B1448837 : Blo 642303 1448837 := bbase (se 4 (by rfl) ⟨135828, by rfl⟩ : syracuseStep 1448837 = 271657) (by norm_num)
theorem B1088437 : Blo 642303 1088437 := bbase (se 5 (by rfl) ⟨51020, by rfl⟩ : syracuseStep 1088437 = 102041) (by norm_num)
theorem B1448909 : Blo 642303 1448909 := bbase (se 3 (by rfl) ⟨271670, by rfl⟩ : syracuseStep 1448909 = 543341) (by norm_num)
theorem B1219549 : Blo 642303 1219549 := bbase (se 3 (by rfl) ⟨228665, by rfl⟩ : syracuseStep 1219549 = 457331) (by norm_num)
theorem B1088525 : Blo 642303 1088525 := bbase (se 3 (by rfl) ⟨204098, by rfl⟩ : syracuseStep 1088525 = 408197) (by norm_num)
theorem B1448981 : Blo 642303 1448981 := bbase (se 6 (by rfl) ⟨33960, by rfl⟩ : syracuseStep 1448981 = 67921) (by norm_num)
theorem B3677237 : Blo 642303 3677237 := bbase (se 5 (by rfl) ⟨172370, by rfl⟩ : syracuseStep 3677237 = 344741) (by norm_num)
theorem B1449053 : Blo 642303 1449053 := bbase (se 3 (by rfl) ⟨271697, by rfl⟩ : syracuseStep 1449053 = 543395) (by norm_num)
theorem B1219693 : Blo 642303 1219693 := bbase (se 3 (by rfl) ⟨228692, by rfl⟩ : syracuseStep 1219693 = 457385) (by norm_num)
theorem B2169989 : Blo 642303 2169989 := bbase (se 4 (by rfl) ⟨203436, by rfl⟩ : syracuseStep 2169989 = 406873) (by norm_num)
theorem B1088653 : Blo 642303 1088653 := bbase (se 3 (by rfl) ⟨204122, by rfl⟩ : syracuseStep 1088653 = 408245) (by norm_num)
theorem B1449125 : Blo 642303 1449125 := bbase (se 4 (by rfl) ⟨135855, by rfl⟩ : syracuseStep 1449125 = 271711) (by norm_num)
theorem B1088741 : Blo 642303 1088741 := bbase (se 4 (by rfl) ⟨102069, by rfl⟩ : syracuseStep 1088741 = 204139) (by norm_num)
theorem B1449197 : Blo 642303 1449197 := bbase (se 3 (by rfl) ⟨271724, by rfl⟩ : syracuseStep 1449197 = 543449) (by norm_num)
theorem B1219853 : Blo 642303 1219853 := bbase (se 3 (by rfl) ⟨228722, by rfl⟩ : syracuseStep 1219853 = 457445) (by norm_num)
theorem B1449269 : Blo 642303 1449269 := bbase (se 5 (by rfl) ⟨67934, by rfl⟩ : syracuseStep 1449269 = 135869) (by norm_num)
theorem B1088869 : Blo 642303 1088869 := bbase (se 4 (by rfl) ⟨102081, by rfl⟩ : syracuseStep 1088869 = 204163) (by norm_num)
theorem B1449341 : Blo 642303 1449341 := bbase (se 3 (by rfl) ⟨271751, by rfl⟩ : syracuseStep 1449341 = 543503) (by norm_num)
theorem B1219997 : Blo 642303 1219997 := bbase (se 3 (by rfl) ⟨228749, by rfl⟩ : syracuseStep 1219997 = 457499) (by norm_num)
theorem B1547693 : Blo 642303 1547693 := bbase (se 3 (by rfl) ⟨290192, by rfl⟩ : syracuseStep 1547693 = 580385) (by norm_num)
theorem B1088957 : Blo 642303 1088957 := bbase (se 3 (by rfl) ⟨204179, by rfl⟩ : syracuseStep 1088957 = 408359) (by norm_num)
theorem B1449413 : Blo 642303 1449413 := bbase (se 4 (by rfl) ⟨135882, by rfl⟩ : syracuseStep 1449413 = 271765) (by norm_num)
theorem B1449485 : Blo 642303 1449485 := bbase (se 3 (by rfl) ⟨271778, by rfl⟩ : syracuseStep 1449485 = 543557) (by norm_num)
theorem B2170421 : Blo 642303 2170421 := bbase (se 5 (by rfl) ⟨101738, by rfl⟩ : syracuseStep 2170421 = 203477) (by norm_num)
theorem B1089085 : Blo 642303 1089085 := bbase (se 3 (by rfl) ⟨204203, by rfl⟩ : syracuseStep 1089085 = 408407) (by norm_num)
theorem B1449557 : Blo 642303 1449557 := bbase (se 8 (by rfl) ⟨8493, by rfl⟩ : syracuseStep 1449557 = 16987) (by norm_num)
theorem B1089173 : Blo 642303 1089173 := bbase (se 6 (by rfl) ⟨25527, by rfl⟩ : syracuseStep 1089173 = 51055) (by norm_num)
theorem B1449629 : Blo 642303 1449629 := bbase (se 3 (by rfl) ⟨271805, by rfl⟩ : syracuseStep 1449629 = 543611) (by norm_num)
theorem B1220285 : Blo 642303 1220285 := bbase (se 3 (by rfl) ⟨228803, by rfl⟩ : syracuseStep 1220285 = 457607) (by norm_num)
theorem B2760389 : Blo 642303 2760389 := bbase (se 4 (by rfl) ⟨258786, by rfl⟩ : syracuseStep 2760389 = 517573) (by norm_num)
theorem B1547981 : Blo 642303 1547981 := bbase (se 3 (by rfl) ⟨290246, by rfl⟩ : syracuseStep 1547981 = 580493) (by norm_num)
theorem B1449701 : Blo 642303 1449701 := bbase (se 4 (by rfl) ⟨135909, by rfl⟩ : syracuseStep 1449701 = 271819) (by norm_num)
theorem B1089301 : Blo 642303 1089301 := bbase (se 6 (by rfl) ⟨25530, by rfl⟩ : syracuseStep 1089301 = 51061) (by norm_num)
theorem B1449773 : Blo 642303 1449773 := bbase (se 3 (by rfl) ⟨271832, by rfl⟩ : syracuseStep 1449773 = 543665) (by norm_num)
theorem B1220437 : Blo 642303 1220437 := bbase (se 9 (by rfl) ⟨3575, by rfl⟩ : syracuseStep 1220437 = 7151) (by norm_num)
theorem B1089389 : Blo 642303 1089389 := bbase (se 3 (by rfl) ⟨204260, by rfl⟩ : syracuseStep 1089389 = 408521) (by norm_num)
theorem B1449845 : Blo 642303 1449845 := bbase (se 5 (by rfl) ⟨67961, by rfl⟩ : syracuseStep 1449845 = 135923) (by norm_num)
theorem B3252149 : Blo 642303 3252149 := bbase (se 5 (by rfl) ⟨152444, by rfl⟩ : syracuseStep 3252149 = 304889) (by norm_num)
theorem B1449917 : Blo 642303 1449917 := bbase (se 3 (by rfl) ⟨271859, by rfl⟩ : syracuseStep 1449917 = 543719) (by norm_num)
theorem B2170853 : Blo 642303 2170853 := bbase (se 4 (by rfl) ⟨203517, by rfl⟩ : syracuseStep 2170853 = 407035) (by norm_num)
theorem B1089517 : Blo 642303 1089517 := bbase (se 3 (by rfl) ⟨204284, by rfl⟩ : syracuseStep 1089517 = 408569) (by norm_num)
theorem B1449989 : Blo 642303 1449989 := bbase (se 4 (by rfl) ⟨135936, by rfl⟩ : syracuseStep 1449989 = 271873) (by norm_num)
theorem B1089605 : Blo 642303 1089605 := bbase (se 4 (by rfl) ⟨102150, by rfl⟩ : syracuseStep 1089605 = 204301) (by norm_num)
theorem B1450061 : Blo 642303 1450061 := bbase (se 3 (by rfl) ⟨271886, by rfl⟩ : syracuseStep 1450061 = 543773) (by norm_num)
theorem B1220741 : Blo 642303 1220741 := bbase (se 4 (by rfl) ⟨114444, by rfl⟩ : syracuseStep 1220741 = 228889) (by norm_num)
theorem B1450133 : Blo 642303 1450133 := bbase (se 6 (by rfl) ⟨33987, by rfl⟩ : syracuseStep 1450133 = 67975) (by norm_num)
theorem B1089733 : Blo 642303 1089733 := bbase (se 4 (by rfl) ⟨102162, by rfl⟩ : syracuseStep 1089733 = 204325) (by norm_num)
theorem B1450205 : Blo 642303 1450205 := bbase (se 3 (by rfl) ⟨271913, by rfl⟩ : syracuseStep 1450205 = 543827) (by norm_num)
theorem B1089821 : Blo 642303 1089821 := bbase (se 3 (by rfl) ⟨204341, by rfl⟩ : syracuseStep 1089821 = 408683) (by norm_num)
theorem B1450277 : Blo 642303 1450277 := bbase (se 4 (by rfl) ⟨135963, by rfl⟩ : syracuseStep 1450277 = 271927) (by norm_num)
theorem B1450349 : Blo 642303 1450349 := bbase (se 3 (by rfl) ⟨271940, by rfl⟩ : syracuseStep 1450349 = 543881) (by norm_num)
theorem B2171285 : Blo 642303 2171285 := bbase (se 6 (by rfl) ⟨50889, by rfl⟩ : syracuseStep 2171285 = 101779) (by norm_num)
theorem B1089949 : Blo 642303 1089949 := bbase (se 3 (by rfl) ⟨204365, by rfl⟩ : syracuseStep 1089949 = 408731) (by norm_num)
theorem B1450421 : Blo 642303 1450421 := bbase (se 5 (by rfl) ⟨67988, by rfl⟩ : syracuseStep 1450421 = 135977) (by norm_num)
theorem B1090037 : Blo 642303 1090037 := bbase (se 5 (by rfl) ⟨51095, by rfl⟩ : syracuseStep 1090037 = 102191) (by norm_num)
theorem B1450493 : Blo 642303 1450493 := bbase (se 3 (by rfl) ⟨271967, by rfl⟩ : syracuseStep 1450493 = 543935) (by norm_num)
theorem B1450565 : Blo 642303 1450565 := bbase (se 4 (by rfl) ⟨135990, by rfl⟩ : syracuseStep 1450565 = 271981) (by norm_num)
theorem B1090165 : Blo 642303 1090165 := bbase (se 5 (by rfl) ⟨51101, by rfl⟩ : syracuseStep 1090165 = 102203) (by norm_num)
theorem B1450637 : Blo 642303 1450637 := bbase (se 3 (by rfl) ⟨271994, by rfl⟩ : syracuseStep 1450637 = 543989) (by norm_num)
theorem B1057429 : Blo 642303 1057429 := bbase (se 6 (by rfl) ⟨24783, by rfl⟩ : syracuseStep 1057429 = 49567) (by norm_num)
theorem B1090253 : Blo 642303 1090253 := bbase (se 3 (by rfl) ⟨204422, by rfl⟩ : syracuseStep 1090253 = 408845) (by norm_num)
theorem B1450709 : Blo 642303 1450709 := bbase (se 7 (by rfl) ⟨17000, by rfl⟩ : syracuseStep 1450709 = 34001) (by norm_num)
theorem B1450781 : Blo 642303 1450781 := bbase (se 3 (by rfl) ⟨272021, by rfl⟩ : syracuseStep 1450781 = 544043) (by norm_num)
theorem B2171717 : Blo 642303 2171717 := bbase (se 4 (by rfl) ⟨203598, by rfl⟩ : syracuseStep 2171717 = 407197) (by norm_num)
theorem B1090381 : Blo 642303 1090381 := bbase (se 3 (by rfl) ⟨204446, by rfl⟩ : syracuseStep 1090381 = 408893) (by norm_num)
theorem B1450853 : Blo 642303 1450853 := bbase (se 4 (by rfl) ⟨136017, by rfl⟩ : syracuseStep 1450853 = 272035) (by norm_num)
theorem B1221493 : Blo 642303 1221493 := bbase (se 5 (by rfl) ⟨57257, by rfl⟩ : syracuseStep 1221493 = 114515) (by norm_num)
theorem B1090469 : Blo 642303 1090469 := bbase (se 4 (by rfl) ⟨102231, by rfl⟩ : syracuseStep 1090469 = 204463) (by norm_num)
theorem B1450925 : Blo 642303 1450925 := bbase (se 3 (by rfl) ⟨272048, by rfl⟩ : syracuseStep 1450925 = 544097) (by norm_num)
theorem B4137941 : Blo 642303 4137941 := bbase (se 7 (by rfl) ⟨48491, by rfl⟩ : syracuseStep 4137941 = 96983) (by norm_num)
theorem B1450997 : Blo 642303 1450997 := bbase (se 5 (by rfl) ⟨68015, by rfl⟩ : syracuseStep 1450997 = 136031) (by norm_num)
theorem B1221637 : Blo 642303 1221637 := bbase (se 4 (by rfl) ⟨114528, by rfl⟩ : syracuseStep 1221637 = 229057) (by norm_num)
theorem B1090597 : Blo 642303 1090597 := bbase (se 4 (by rfl) ⟨102243, by rfl⟩ : syracuseStep 1090597 = 204487) (by norm_num)
theorem B1451069 : Blo 642303 1451069 := bbase (se 3 (by rfl) ⟨272075, by rfl⟩ : syracuseStep 1451069 = 544151) (by norm_num)
theorem B5022805 : Blo 642303 5022805 := bbase (se 8 (by rfl) ⟨29430, by rfl⟩ : syracuseStep 5022805 = 58861) (by norm_num)
theorem B6202453 : Blo 642303 6202453 := bbase (se 8 (by rfl) ⟨36342, by rfl⟩ : syracuseStep 6202453 = 72685) (by norm_num)
theorem B1451141 : Blo 642303 1451141 := bbase (se 4 (by rfl) ⟨136044, by rfl⟩ : syracuseStep 1451141 = 272089) (by norm_num)
theorem B1221797 : Blo 642303 1221797 := bbase (se 4 (by rfl) ⟨114543, by rfl⟩ : syracuseStep 1221797 = 229087) (by norm_num)
theorem B3253445 : Blo 642303 3253445 := bbase (se 4 (by rfl) ⟨305010, by rfl⟩ : syracuseStep 3253445 = 610021) (by norm_num)
theorem B1451213 : Blo 642303 1451213 := bbase (se 3 (by rfl) ⟨272102, by rfl⟩ : syracuseStep 1451213 = 544205) (by norm_num)
theorem B3679445 : Blo 642303 3679445 := bbase (se 7 (by rfl) ⟨43118, by rfl⟩ : syracuseStep 3679445 = 86237) (by norm_num)
theorem B2172149 : Blo 642303 2172149 := bbase (se 5 (by rfl) ⟨101819, by rfl⟩ : syracuseStep 2172149 = 203639) (by norm_num)
theorem B1451285 : Blo 642303 1451285 := bbase (se 6 (by rfl) ⟨34014, by rfl⟩ : syracuseStep 1451285 = 68029) (by norm_num)
theorem B1221941 : Blo 642303 1221941 := bbase (se 5 (by rfl) ⟨57278, by rfl⟩ : syracuseStep 1221941 = 114557) (by norm_num)
theorem B1451357 : Blo 642303 1451357 := bbase (se 3 (by rfl) ⟨272129, by rfl⟩ : syracuseStep 1451357 = 544259) (by norm_num)
theorem B1451429 : Blo 642303 1451429 := bbase (se 4 (by rfl) ⟨136071, by rfl⟩ : syracuseStep 1451429 = 272143) (by norm_num)
theorem B1451501 : Blo 642303 1451501 := bbase (se 3 (by rfl) ⟨272156, by rfl⟩ : syracuseStep 1451501 = 544313) (by norm_num)
theorem B1648181 : Blo 642303 1648181 := bbase (se 5 (by rfl) ⟨77258, by rfl⟩ : syracuseStep 1648181 = 154517) (by norm_num)
theorem B1451573 : Blo 642303 1451573 := bbase (se 5 (by rfl) ⟨68042, by rfl⟩ : syracuseStep 1451573 = 136085) (by norm_num)
theorem B1222229 : Blo 642303 1222229 := bbase (se 8 (by rfl) ⟨7161, by rfl⟩ : syracuseStep 1222229 = 14323) (by norm_num)
theorem B1746517 : Blo 642303 1746517 := bbase (se 8 (by rfl) ⟨10233, by rfl⟩ : syracuseStep 1746517 = 20467) (by norm_num)
theorem B1451645 : Blo 642303 1451645 := bbase (se 3 (by rfl) ⟨272183, by rfl⟩ : syracuseStep 1451645 = 544367) (by norm_num)
theorem B2172581 : Blo 642303 2172581 := bbase (se 4 (by rfl) ⟨203679, by rfl⟩ : syracuseStep 2172581 = 407359) (by norm_num)
theorem B1451717 : Blo 642303 1451717 := bbase (se 4 (by rfl) ⟨136098, by rfl⟩ : syracuseStep 1451717 = 272197) (by norm_num)
theorem B1550029 : Blo 642303 1550029 := bbase (se 3 (by rfl) ⟨290630, by rfl⟩ : syracuseStep 1550029 = 581261) (by norm_num)
theorem B1222381 : Blo 642303 1222381 := bbase (se 3 (by rfl) ⟨229196, by rfl⟩ : syracuseStep 1222381 = 458393) (by norm_num)
theorem B1451789 : Blo 642303 1451789 := bbase (se 3 (by rfl) ⟨272210, by rfl⟩ : syracuseStep 1451789 = 544421) (by norm_num)
theorem B1451861 : Blo 642303 1451861 := bbase (se 9 (by rfl) ⟨4253, by rfl⟩ : syracuseStep 1451861 = 8507) (by norm_num)
theorem B1451933 : Blo 642303 1451933 := bbase (se 3 (by rfl) ⟨272237, by rfl⟩ : syracuseStep 1451933 = 544475) (by norm_num)
theorem B1452005 : Blo 642303 1452005 := bbase (se 4 (by rfl) ⟨136125, by rfl⟩ : syracuseStep 1452005 = 272251) (by norm_num)
theorem B1222685 : Blo 642303 1222685 := bbase (se 3 (by rfl) ⟨229253, by rfl⟩ : syracuseStep 1222685 = 458507) (by norm_num)
theorem B1452077 : Blo 642303 1452077 := bbase (se 3 (by rfl) ⟨272264, by rfl⟩ : syracuseStep 1452077 = 544529) (by norm_num)
theorem B2173013 : Blo 642303 2173013 := bbase (se 8 (by rfl) ⟨12732, by rfl⟩ : syracuseStep 2173013 = 25465) (by norm_num)
theorem B1452149 : Blo 642303 1452149 := bbase (se 5 (by rfl) ⟨68069, by rfl⟩ : syracuseStep 1452149 = 136139) (by norm_num)
theorem B3090581 : Blo 642303 3090581 := bbase (se 6 (by rfl) ⟨72435, by rfl⟩ : syracuseStep 3090581 = 144871) (by norm_num)
theorem B3582133 : Blo 642303 3582133 := bbase (se 5 (by rfl) ⟨167912, by rfl⟩ : syracuseStep 3582133 = 335825) (by norm_num)
theorem B1452221 : Blo 642303 1452221 := bbase (se 3 (by rfl) ⟨272291, by rfl⟩ : syracuseStep 1452221 = 544583) (by norm_num)
theorem B1452293 : Blo 642303 1452293 := bbase (se 4 (by rfl) ⟨136152, by rfl⟩ : syracuseStep 1452293 = 272305) (by norm_num)
theorem B1452365 : Blo 642303 1452365 := bbase (se 3 (by rfl) ⟨272318, by rfl⟩ : syracuseStep 1452365 = 544637) (by norm_num)
theorem B44607829 : Blo 642303 44607829 := bbase (se 10 (by rfl) ⟨65343, by rfl⟩ : syracuseStep 44607829 = 130687) (by norm_num)
theorem B1452437 : Blo 642303 1452437 := bbase (se 6 (by rfl) ⟨34041, by rfl⟩ : syracuseStep 1452437 = 68083) (by norm_num)
theorem B3254741 : Blo 642303 3254741 := bbase (se 7 (by rfl) ⟨38141, by rfl⟩ : syracuseStep 3254741 = 76283) (by norm_num)
theorem B1452509 : Blo 642303 1452509 := bbase (se 3 (by rfl) ⟨272345, by rfl⟩ : syracuseStep 1452509 = 544691) (by norm_num)
theorem B2173445 : Blo 642303 2173445 := bbase (se 4 (by rfl) ⟨203760, by rfl⟩ : syracuseStep 2173445 = 407521) (by norm_num)
theorem B1649165 : Blo 642303 1649165 := bbase (se 3 (by rfl) ⟨309218, by rfl⟩ : syracuseStep 1649165 = 618437) (by norm_num)
theorem B1452581 : Blo 642303 1452581 := bbase (se 4 (by rfl) ⟨136179, by rfl⟩ : syracuseStep 1452581 = 272359) (by norm_num)
theorem B1452653 : Blo 642303 1452653 := bbase (se 3 (by rfl) ⟨272372, by rfl⟩ : syracuseStep 1452653 = 544745) (by norm_num)
theorem B3353237 : Blo 642303 3353237 := bbase (se 6 (by rfl) ⟨78591, by rfl⟩ : syracuseStep 3353237 = 157183) (by norm_num)
theorem B1452725 : Blo 642303 1452725 := bbase (se 5 (by rfl) ⟨68096, by rfl⟩ : syracuseStep 1452725 = 136193) (by norm_num)
theorem B1452797 : Blo 642303 1452797 := bbase (se 3 (by rfl) ⟨272399, by rfl⟩ : syracuseStep 1452797 = 544799) (by norm_num)
theorem B1223437 : Blo 642303 1223437 := bbase (se 3 (by rfl) ⟨229394, by rfl⟩ : syracuseStep 1223437 = 458789) (by norm_num)
theorem B1452869 : Blo 642303 1452869 := bbase (se 4 (by rfl) ⟨136206, by rfl⟩ : syracuseStep 1452869 = 272413) (by norm_num)
theorem B1321829 : Blo 642303 1321829 := bbase (se 4 (by rfl) ⟨123921, by rfl⟩ : syracuseStep 1321829 = 247843) (by norm_num)
theorem B1452941 : Blo 642303 1452941 := bbase (se 3 (by rfl) ⟨272426, by rfl⟩ : syracuseStep 1452941 = 544853) (by norm_num)
theorem B1223581 : Blo 642303 1223581 := bbase (se 3 (by rfl) ⟨229421, by rfl⟩ : syracuseStep 1223581 = 458843) (by norm_num)
theorem B2173877 : Blo 642303 2173877 := bbase (se 5 (by rfl) ⟨101900, by rfl⟩ : syracuseStep 2173877 = 203801) (by norm_num)
theorem B1453013 : Blo 642303 1453013 := bbase (se 7 (by rfl) ⟨17027, by rfl⟩ : syracuseStep 1453013 = 34055) (by norm_num)
theorem B1453085 : Blo 642303 1453085 := bbase (se 3 (by rfl) ⟨272453, by rfl⟩ : syracuseStep 1453085 = 544907) (by norm_num)
theorem B1223741 : Blo 642303 1223741 := bbase (se 3 (by rfl) ⟨229451, by rfl⟩ : syracuseStep 1223741 = 458903) (by norm_num)
theorem B1453157 : Blo 642303 1453157 := bbase (se 4 (by rfl) ⟨136233, by rfl⟩ : syracuseStep 1453157 = 272467) (by norm_num)
theorem B1453229 : Blo 642303 1453229 := bbase (se 3 (by rfl) ⟨272480, by rfl⟩ : syracuseStep 1453229 = 544961) (by norm_num)
theorem B1223885 : Blo 642303 1223885 := bbase (se 3 (by rfl) ⟨229478, by rfl⟩ : syracuseStep 1223885 = 458957) (by norm_num)
theorem B1453301 : Blo 642303 1453301 := bbase (se 5 (by rfl) ⟨68123, by rfl⟩ : syracuseStep 1453301 = 136247) (by norm_num)
theorem B1453373 : Blo 642303 1453373 := bbase (se 3 (by rfl) ⟨272507, by rfl⟩ : syracuseStep 1453373 = 545015) (by norm_num)
theorem B2174309 : Blo 642303 2174309 := bbase (se 4 (by rfl) ⟨203841, by rfl⟩ : syracuseStep 2174309 = 407683) (by norm_num)
theorem B1453445 : Blo 642303 1453445 := bbase (se 4 (by rfl) ⟨136260, by rfl⟩ : syracuseStep 1453445 = 272521) (by norm_num)
theorem B1453517 : Blo 642303 1453517 := bbase (se 3 (by rfl) ⟨272534, by rfl⟩ : syracuseStep 1453517 = 545069) (by norm_num)
theorem B1224173 : Blo 642303 1224173 := bbase (se 3 (by rfl) ⟨229532, by rfl⟩ : syracuseStep 1224173 = 459065) (by norm_num)
theorem B1453589 : Blo 642303 1453589 := bbase (se 6 (by rfl) ⟨34068, by rfl⟩ : syracuseStep 1453589 = 68137) (by norm_num)
theorem B1453661 : Blo 642303 1453661 := bbase (se 3 (by rfl) ⟨272561, by rfl⟩ : syracuseStep 1453661 = 545123) (by norm_num)
theorem B1224325 : Blo 642303 1224325 := bbase (se 4 (by rfl) ⟨114780, by rfl⟩ : syracuseStep 1224325 = 229561) (by norm_num)
theorem B1453733 : Blo 642303 1453733 := bbase (se 4 (by rfl) ⟨136287, by rfl⟩ : syracuseStep 1453733 = 272575) (by norm_num)
theorem B5516981 : Blo 642303 5516981 := bbase (se 5 (by rfl) ⟨258608, by rfl⟩ : syracuseStep 5516981 = 517217) (by norm_num)
theorem B3256037 : Blo 642303 3256037 := bbase (se 4 (by rfl) ⟨305253, by rfl⟩ : syracuseStep 3256037 = 610507) (by norm_num)
theorem B1453805 : Blo 642303 1453805 := bbase (se 3 (by rfl) ⟨272588, by rfl⟩ : syracuseStep 1453805 = 545177) (by norm_num)
theorem B1191677 : Blo 642303 1191677 := bbase (se 3 (by rfl) ⟨223439, by rfl⟩ : syracuseStep 1191677 = 446879) (by norm_num)
theorem B2174741 : Blo 642303 2174741 := bbase (se 6 (by rfl) ⟨50970, by rfl⟩ : syracuseStep 2174741 = 101941) (by norm_num)
theorem B1453877 : Blo 642303 1453877 := bbase (se 5 (by rfl) ⟨68150, by rfl⟩ : syracuseStep 1453877 = 136301) (by norm_num)
theorem B1453949 : Blo 642303 1453949 := bbase (se 3 (by rfl) ⟨272615, by rfl⟩ : syracuseStep 1453949 = 545231) (by norm_num)
theorem B1224629 : Blo 642303 1224629 := bbase (se 5 (by rfl) ⟨57404, by rfl⟩ : syracuseStep 1224629 = 114809) (by norm_num)
theorem B3583925 : Blo 642303 3583925 := bbase (se 5 (by rfl) ⟨167996, by rfl⟩ : syracuseStep 3583925 = 335993) (by norm_num)
theorem B1454021 : Blo 642303 1454021 := bbase (se 4 (by rfl) ⟨136314, by rfl⟩ : syracuseStep 1454021 = 272629) (by norm_num)
theorem B1454093 : Blo 642303 1454093 := bbase (se 3 (by rfl) ⟨272642, by rfl⟩ : syracuseStep 1454093 = 545285) (by norm_num)
theorem B1552421 : Blo 642303 1552421 := bbase (se 4 (by rfl) ⟨145539, by rfl⟩ : syracuseStep 1552421 = 291079) (by norm_num)
theorem B1159213 : Blo 642303 1159213 := bbase (se 3 (by rfl) ⟨217352, by rfl⟩ : syracuseStep 1159213 = 434705) (by norm_num)
theorem B1454165 : Blo 642303 1454165 := bbase (se 8 (by rfl) ⟨8520, by rfl⟩ : syracuseStep 1454165 = 17041) (by norm_num)
theorem B1552565 : Blo 642303 1552565 := bbase (se 5 (by rfl) ⟨72776, by rfl⟩ : syracuseStep 1552565 = 145553) (by norm_num)
theorem B2175173 : Blo 642303 2175173 := bbase (se 4 (by rfl) ⟨203922, by rfl⟩ : syracuseStep 2175173 = 407845) (by norm_num)
theorem B1159429 : Blo 642303 1159429 := bbase (se 4 (by rfl) ⟨108696, by rfl⟩ : syracuseStep 1159429 = 217393) (by norm_num)
theorem B2175605 : Blo 642303 2175605 := bbase (se 5 (by rfl) ⟨101981, by rfl⟩ : syracuseStep 2175605 = 203963) (by norm_num)
theorem B1225381 : Blo 642303 1225381 := bbase (se 4 (by rfl) ⟨114879, by rfl⟩ : syracuseStep 1225381 = 229759) (by norm_num)
theorem B4895477 : Blo 642303 4895477 := bbase (se 5 (by rfl) ⟨229475, by rfl⟩ : syracuseStep 4895477 = 458951) (by norm_num)
theorem B1225525 : Blo 642303 1225525 := bbase (se 5 (by rfl) ⟨57446, by rfl⟩ : syracuseStep 1225525 = 114893) (by norm_num)
theorem B734017 : Blo 642303 734017 := bbase (se 2 (by rfl) ⟨275256, by rfl⟩ : syracuseStep 734017 = 550513) (by norm_num)
theorem B963461 : Blo 642303 963461 := bbase (se 4 (by rfl) ⟨90324, by rfl⟩ : syracuseStep 963461 = 180649) (by norm_num)
theorem B734089 : Blo 642303 734089 := bbase (se 2 (by rfl) ⟨275283, by rfl⟩ : syracuseStep 734089 = 550567) (by norm_num)
theorem B963485 : Blo 642303 963485 := bbase (se 3 (by rfl) ⟨180653, by rfl⟩ : syracuseStep 963485 = 361307) (by norm_num)
theorem B963509 : Blo 642303 963509 := bbase (se 5 (by rfl) ⟨45164, by rfl⟩ : syracuseStep 963509 = 90329) (by norm_num)
theorem B963533 : Blo 642303 963533 := bbase (se 3 (by rfl) ⟨180662, by rfl⟩ : syracuseStep 963533 = 361325) (by norm_num)
theorem B3093461 : Blo 642303 3093461 := bbase (se 7 (by rfl) ⟨36251, by rfl⟩ : syracuseStep 3093461 = 72503) (by norm_num)
theorem B1225685 : Blo 642303 1225685 := bbase (se 7 (by rfl) ⟨14363, by rfl⟩ : syracuseStep 1225685 = 28727) (by norm_num)
theorem B963557 : Blo 642303 963557 := bbase (se 4 (by rfl) ⟨90333, by rfl⟩ : syracuseStep 963557 = 180667) (by norm_num)
theorem B3257333 : Blo 642303 3257333 := bbase (se 5 (by rfl) ⟨152687, by rfl⟩ : syracuseStep 3257333 = 305375) (by norm_num)
theorem B963581 : Blo 642303 963581 := bbase (se 3 (by rfl) ⟨180671, by rfl⟩ : syracuseStep 963581 = 361343) (by norm_num)
theorem B963605 : Blo 642303 963605 := bbase (se 6 (by rfl) ⟨22584, by rfl⟩ : syracuseStep 963605 = 45169) (by norm_num)
theorem B2176037 : Blo 642303 2176037 := bbase (se 4 (by rfl) ⟨204003, by rfl⟩ : syracuseStep 2176037 = 408007) (by norm_num)
theorem B963629 : Blo 642303 963629 := bbase (se 3 (by rfl) ⟨180680, by rfl⟩ : syracuseStep 963629 = 361361) (by norm_num)
theorem B1029181 : Blo 642303 1029181 := bbase (se 3 (by rfl) ⟨192971, by rfl⟩ : syracuseStep 1029181 = 385943) (by norm_num)
theorem B963653 : Blo 642303 963653 := bbase (se 4 (by rfl) ⟨90342, by rfl⟩ : syracuseStep 963653 = 180685) (by norm_num)
theorem B963677 : Blo 642303 963677 := bbase (se 3 (by rfl) ⟨180689, by rfl⟩ : syracuseStep 963677 = 361379) (by norm_num)
theorem B1225829 : Blo 642303 1225829 := bbase (se 4 (by rfl) ⟨114921, by rfl⟩ : syracuseStep 1225829 = 229843) (by norm_num)
theorem B963701 : Blo 642303 963701 := bbase (se 5 (by rfl) ⟨45173, by rfl⟩ : syracuseStep 963701 = 90347) (by norm_num)
theorem B963725 : Blo 642303 963725 := bbase (se 3 (by rfl) ⟨180698, by rfl⟩ : syracuseStep 963725 = 361397) (by norm_num)
theorem B963749 : Blo 642303 963749 := bbase (se 4 (by rfl) ⟨90351, by rfl⟩ : syracuseStep 963749 = 180703) (by norm_num)
theorem B963773 : Blo 642303 963773 := bbase (se 3 (by rfl) ⟨180707, by rfl⟩ : syracuseStep 963773 = 361415) (by norm_num)
theorem B963797 : Blo 642303 963797 := bbase (se 7 (by rfl) ⟨11294, by rfl⟩ : syracuseStep 963797 = 22589) (by norm_num)
theorem B963821 : Blo 642303 963821 := bbase (se 3 (by rfl) ⟨180716, by rfl⟩ : syracuseStep 963821 = 361433) (by norm_num)
theorem B963845 : Blo 642303 963845 := bbase (se 4 (by rfl) ⟨90360, by rfl⟩ : syracuseStep 963845 = 180721) (by norm_num)
theorem B963869 : Blo 642303 963869 := bbase (se 3 (by rfl) ⟨180725, by rfl⟩ : syracuseStep 963869 = 361451) (by norm_num)
theorem B963893 : Blo 642303 963893 := bbase (se 5 (by rfl) ⟨45182, by rfl⟩ : syracuseStep 963893 = 90365) (by norm_num)
theorem B1029437 : Blo 642303 1029437 := bbase (se 3 (by rfl) ⟨193019, by rfl⟩ : syracuseStep 1029437 = 386039) (by norm_num)
theorem B963917 : Blo 642303 963917 := bbase (se 3 (by rfl) ⟨180734, by rfl⟩ : syracuseStep 963917 = 361469) (by norm_num)
theorem B963941 : Blo 642303 963941 := bbase (se 4 (by rfl) ⟨90369, by rfl⟩ : syracuseStep 963941 = 180739) (by norm_num)
theorem B963965 : Blo 642303 963965 := bbase (se 3 (by rfl) ⟨180743, by rfl⟩ : syracuseStep 963965 = 361487) (by norm_num)
theorem B1226117 : Blo 642303 1226117 := bbase (se 4 (by rfl) ⟨114948, by rfl⟩ : syracuseStep 1226117 = 229897) (by norm_num)
theorem B963989 : Blo 642303 963989 := bbase (se 6 (by rfl) ⟨22593, by rfl⟩ : syracuseStep 963989 = 45187) (by norm_num)
theorem B964013 : Blo 642303 964013 := bbase (se 3 (by rfl) ⟨180752, by rfl⟩ : syracuseStep 964013 = 361505) (by norm_num)
theorem B3716533 : Blo 642303 3716533 := bbase (se 5 (by rfl) ⟨174212, by rfl⟩ : syracuseStep 3716533 = 348425) (by norm_num)
theorem B964037 : Blo 642303 964037 := bbase (se 4 (by rfl) ⟨90378, by rfl⟩ : syracuseStep 964037 = 180757) (by norm_num)
theorem B2176469 : Blo 642303 2176469 := bbase (se 7 (by rfl) ⟨25505, by rfl⟩ : syracuseStep 2176469 = 51011) (by norm_num)
theorem B964061 : Blo 642303 964061 := bbase (se 3 (by rfl) ⟨180761, by rfl⟩ : syracuseStep 964061 = 361523) (by norm_num)
theorem B964085 : Blo 642303 964085 := bbase (se 5 (by rfl) ⟨45191, by rfl⟩ : syracuseStep 964085 = 90383) (by norm_num)
theorem B1029629 : Blo 642303 1029629 := bbase (se 3 (by rfl) ⟨193055, by rfl⟩ : syracuseStep 1029629 = 386111) (by norm_num)
theorem B964109 : Blo 642303 964109 := bbase (se 3 (by rfl) ⟨180770, by rfl⟩ : syracuseStep 964109 = 361541) (by norm_num)
theorem B1226269 : Blo 642303 1226269 := bbase (se 3 (by rfl) ⟨229925, by rfl⟩ : syracuseStep 1226269 = 459851) (by norm_num)
theorem B964133 : Blo 642303 964133 := bbase (se 4 (by rfl) ⟨90387, by rfl⟩ : syracuseStep 964133 = 180775) (by norm_num)
theorem B964157 : Blo 642303 964157 := bbase (se 3 (by rfl) ⟨180779, by rfl⟩ : syracuseStep 964157 = 361559) (by norm_num)
theorem B1652285 : Blo 642303 1652285 := bbase (se 3 (by rfl) ⟨309803, by rfl⟩ : syracuseStep 1652285 = 619607) (by norm_num)
theorem B964181 : Blo 642303 964181 := bbase (se 8 (by rfl) ⟨5649, by rfl⟩ : syracuseStep 964181 = 11299) (by norm_num)
theorem B964205 : Blo 642303 964205 := bbase (se 3 (by rfl) ⟨180788, by rfl⟩ : syracuseStep 964205 = 361577) (by norm_num)
theorem B964229 : Blo 642303 964229 := bbase (se 4 (by rfl) ⟨90396, by rfl⟩ : syracuseStep 964229 = 180793) (by norm_num)
theorem B964253 : Blo 642303 964253 := bbase (se 3 (by rfl) ⟨180797, by rfl⟩ : syracuseStep 964253 = 361595) (by norm_num)
theorem B964277 : Blo 642303 964277 := bbase (se 5 (by rfl) ⟨45200, by rfl⟩ : syracuseStep 964277 = 90401) (by norm_num)
theorem B1160885 : Blo 642303 1160885 := bbase (se 5 (by rfl) ⟨54416, by rfl⟩ : syracuseStep 1160885 = 108833) (by norm_num)
theorem B964301 : Blo 642303 964301 := bbase (se 3 (by rfl) ⟨180806, by rfl⟩ : syracuseStep 964301 = 361613) (by norm_num)
theorem B2438869 : Blo 642303 2438869 := bbase (se 7 (by rfl) ⟨28580, by rfl⟩ : syracuseStep 2438869 = 57161) (by norm_num)
theorem B734933 : Blo 642303 734933 := bbase (se 7 (by rfl) ⟨8612, by rfl⟩ : syracuseStep 734933 = 17225) (by norm_num)
theorem B964325 : Blo 642303 964325 := bbase (se 4 (by rfl) ⟨90405, by rfl⟩ : syracuseStep 964325 = 180811) (by norm_num)
theorem B964349 : Blo 642303 964349 := bbase (se 3 (by rfl) ⟨180815, by rfl⟩ : syracuseStep 964349 = 361631) (by norm_num)
theorem B964373 : Blo 642303 964373 := bbase (se 6 (by rfl) ⟨22602, by rfl⟩ : syracuseStep 964373 = 45205) (by norm_num)
theorem B964397 : Blo 642303 964397 := bbase (se 3 (by rfl) ⟨180824, by rfl⟩ : syracuseStep 964397 = 361649) (by norm_num)
theorem B964421 : Blo 642303 964421 := bbase (se 4 (by rfl) ⟨90414, by rfl⟩ : syracuseStep 964421 = 180829) (by norm_num)
theorem B1161029 : Blo 642303 1161029 := bbase (se 4 (by rfl) ⟨108846, by rfl⟩ : syracuseStep 1161029 = 217693) (by norm_num)
theorem B1226573 : Blo 642303 1226573 := bbase (se 3 (by rfl) ⟨229982, by rfl⟩ : syracuseStep 1226573 = 459965) (by norm_num)
theorem B964445 : Blo 642303 964445 := bbase (se 3 (by rfl) ⟨180833, by rfl⟩ : syracuseStep 964445 = 361667) (by norm_num)
theorem B964469 : Blo 642303 964469 := bbase (se 5 (by rfl) ⟨45209, by rfl⟩ : syracuseStep 964469 = 90419) (by norm_num)
theorem B2176901 : Blo 642303 2176901 := bbase (se 4 (by rfl) ⟨204084, by rfl⟩ : syracuseStep 2176901 = 408169) (by norm_num)
theorem B964493 : Blo 642303 964493 := bbase (se 3 (by rfl) ⟨180842, by rfl⟩ : syracuseStep 964493 = 361685) (by norm_num)
theorem B1161101 : Blo 642303 1161101 := bbase (se 3 (by rfl) ⟨217706, by rfl⟩ : syracuseStep 1161101 = 435413) (by norm_num)
theorem B964517 : Blo 642303 964517 := bbase (se 4 (by rfl) ⟨90423, by rfl⟩ : syracuseStep 964517 = 180847) (by norm_num)
theorem B964541 : Blo 642303 964541 := bbase (se 3 (by rfl) ⟨180851, by rfl⟩ : syracuseStep 964541 = 361703) (by norm_num)
theorem B964565 : Blo 642303 964565 := bbase (se 7 (by rfl) ⟨11303, by rfl⟩ : syracuseStep 964565 = 22607) (by norm_num)
theorem B964589 : Blo 642303 964589 := bbase (se 3 (by rfl) ⟨180860, by rfl⟩ : syracuseStep 964589 = 361721) (by norm_num)
theorem B2439173 : Blo 642303 2439173 := bbase (se 4 (by rfl) ⟨228672, by rfl⟩ : syracuseStep 2439173 = 457345) (by norm_num)
theorem B964613 : Blo 642303 964613 := bbase (se 4 (by rfl) ⟨90432, by rfl⟩ : syracuseStep 964613 = 180865) (by norm_num)
theorem B964637 : Blo 642303 964637 := bbase (se 3 (by rfl) ⟨180869, by rfl⟩ : syracuseStep 964637 = 361739) (by norm_num)
theorem B964661 : Blo 642303 964661 := bbase (se 5 (by rfl) ⟨45218, by rfl⟩ : syracuseStep 964661 = 90437) (by norm_num)
theorem B964685 : Blo 642303 964685 := bbase (se 3 (by rfl) ⟨180878, by rfl⟩ : syracuseStep 964685 = 361757) (by norm_num)
theorem B964709 : Blo 642303 964709 := bbase (se 4 (by rfl) ⟨90441, by rfl⟩ : syracuseStep 964709 = 180883) (by norm_num)
theorem B964733 : Blo 642303 964733 := bbase (se 3 (by rfl) ⟨180887, by rfl⟩ : syracuseStep 964733 = 361775) (by norm_num)
theorem B964757 : Blo 642303 964757 := bbase (se 6 (by rfl) ⟨22611, by rfl⟩ : syracuseStep 964757 = 45223) (by norm_num)
theorem B964781 : Blo 642303 964781 := bbase (se 3 (by rfl) ⟨180896, by rfl⟩ : syracuseStep 964781 = 361793) (by norm_num)
theorem B964805 : Blo 642303 964805 := bbase (se 4 (by rfl) ⟨90450, by rfl⟩ : syracuseStep 964805 = 180901) (by norm_num)
theorem B964829 : Blo 642303 964829 := bbase (se 3 (by rfl) ⟨180905, by rfl⟩ : syracuseStep 964829 = 361811) (by norm_num)
theorem B964853 : Blo 642303 964853 := bbase (se 5 (by rfl) ⟨45227, by rfl⟩ : syracuseStep 964853 = 90455) (by norm_num)
theorem B3258629 : Blo 642303 3258629 := bbase (se 4 (by rfl) ⟨305496, by rfl⟩ : syracuseStep 3258629 = 610993) (by norm_num)
theorem B964877 : Blo 642303 964877 := bbase (se 3 (by rfl) ⟨180914, by rfl⟩ : syracuseStep 964877 = 361829) (by norm_num)
theorem B735517 : Blo 642303 735517 := bbase (se 3 (by rfl) ⟨137909, by rfl⟩ : syracuseStep 735517 = 275819) (by norm_num)
theorem B964901 : Blo 642303 964901 := bbase (se 4 (by rfl) ⟨90459, by rfl⟩ : syracuseStep 964901 = 180919) (by norm_num)
theorem B2177333 : Blo 642303 2177333 := bbase (se 5 (by rfl) ⟨102062, by rfl⟩ : syracuseStep 2177333 = 204125) (by norm_num)
theorem B964925 : Blo 642303 964925 := bbase (se 3 (by rfl) ⟨180923, by rfl⟩ : syracuseStep 964925 = 361847) (by norm_num)
theorem B964949 : Blo 642303 964949 := bbase (se 10 (by rfl) ⟨1413, by rfl⟩ : syracuseStep 964949 = 2827) (by norm_num)
theorem B964973 : Blo 642303 964973 := bbase (se 3 (by rfl) ⟨180932, by rfl⟩ : syracuseStep 964973 = 361865) (by norm_num)
theorem B964997 : Blo 642303 964997 := bbase (se 4 (by rfl) ⟨90468, by rfl⟩ : syracuseStep 964997 = 180937) (by norm_num)
theorem B1161605 : Blo 642303 1161605 := bbase (se 4 (by rfl) ⟨108900, by rfl⟩ : syracuseStep 1161605 = 217801) (by norm_num)
theorem B965021 : Blo 642303 965021 := bbase (se 3 (by rfl) ⟨180941, by rfl⟩ : syracuseStep 965021 = 361883) (by norm_num)
theorem B1030565 : Blo 642303 1030565 := bbase (se 4 (by rfl) ⟨96615, by rfl⟩ : syracuseStep 1030565 = 193231) (by norm_num)
theorem B965045 : Blo 642303 965045 := bbase (se 5 (by rfl) ⟨45236, by rfl⟩ : syracuseStep 965045 = 90473) (by norm_num)
theorem B965069 : Blo 642303 965069 := bbase (se 3 (by rfl) ⟨180950, by rfl⟩ : syracuseStep 965069 = 361901) (by norm_num)
theorem B965093 : Blo 642303 965093 := bbase (se 4 (by rfl) ⟨90477, by rfl⟩ : syracuseStep 965093 = 180955) (by norm_num)
theorem B965117 : Blo 642303 965117 := bbase (se 3 (by rfl) ⟨180959, by rfl⟩ : syracuseStep 965117 = 361919) (by norm_num)
theorem B965141 : Blo 642303 965141 := bbase (se 6 (by rfl) ⟨22620, by rfl⟩ : syracuseStep 965141 = 45241) (by norm_num)
theorem B965165 : Blo 642303 965165 := bbase (se 3 (by rfl) ⟨180968, by rfl⟩ : syracuseStep 965165 = 361937) (by norm_num)
theorem B965189 : Blo 642303 965189 := bbase (se 4 (by rfl) ⟨90486, by rfl⟩ : syracuseStep 965189 = 180973) (by norm_num)
theorem B965213 : Blo 642303 965213 := bbase (se 3 (by rfl) ⟨180977, by rfl⟩ : syracuseStep 965213 = 361955) (by norm_num)
theorem B965237 : Blo 642303 965237 := bbase (se 5 (by rfl) ⟨45245, by rfl⟩ : syracuseStep 965237 = 90491) (by norm_num)
theorem B3357317 : Blo 642303 3357317 := bbase (se 4 (by rfl) ⟨314748, by rfl⟩ : syracuseStep 3357317 = 629497) (by norm_num)
theorem B965261 : Blo 642303 965261 := bbase (se 3 (by rfl) ⟨180986, by rfl⟩ : syracuseStep 965261 = 361973) (by norm_num)
theorem B965285 : Blo 642303 965285 := bbase (se 4 (by rfl) ⟨90495, by rfl⟩ : syracuseStep 965285 = 180991) (by norm_num)
theorem B1325749 : Blo 642303 1325749 := bbase (se 5 (by rfl) ⟨62144, by rfl⟩ : syracuseStep 1325749 = 124289) (by norm_num)
theorem B965309 : Blo 642303 965309 := bbase (se 3 (by rfl) ⟨180995, by rfl⟩ : syracuseStep 965309 = 361991) (by norm_num)
theorem B965333 : Blo 642303 965333 := bbase (se 7 (by rfl) ⟨11312, by rfl⟩ : syracuseStep 965333 = 22625) (by norm_num)
theorem B2177765 : Blo 642303 2177765 := bbase (se 4 (by rfl) ⟨204165, by rfl⟩ : syracuseStep 2177765 = 408331) (by norm_num)
theorem B965357 : Blo 642303 965357 := bbase (se 3 (by rfl) ⟨181004, by rfl⟩ : syracuseStep 965357 = 362009) (by norm_num)
theorem B1325821 : Blo 642303 1325821 := bbase (se 3 (by rfl) ⟨248591, by rfl⟩ : syracuseStep 1325821 = 497183) (by norm_num)
theorem B965381 : Blo 642303 965381 := bbase (se 4 (by rfl) ⟨90504, by rfl⟩ : syracuseStep 965381 = 181009) (by norm_num)
theorem B965405 : Blo 642303 965405 := bbase (se 3 (by rfl) ⟨181013, by rfl⟩ : syracuseStep 965405 = 362027) (by norm_num)
theorem B1030949 : Blo 642303 1030949 := bbase (se 4 (by rfl) ⟨96651, by rfl⟩ : syracuseStep 1030949 = 193303) (by norm_num)
theorem B6175541 : Blo 642303 6175541 := bbase (se 5 (by rfl) ⟨289478, by rfl⟩ : syracuseStep 6175541 = 578957) (by norm_num)
theorem B965429 : Blo 642303 965429 := bbase (se 5 (by rfl) ⟨45254, by rfl⟩ : syracuseStep 965429 = 90509) (by norm_num)
theorem B965453 : Blo 642303 965453 := bbase (se 3 (by rfl) ⟨181022, by rfl⟩ : syracuseStep 965453 = 362045) (by norm_num)
theorem B965477 : Blo 642303 965477 := bbase (se 4 (by rfl) ⟨90513, by rfl⟩ : syracuseStep 965477 = 181027) (by norm_num)
theorem B965501 : Blo 642303 965501 := bbase (se 3 (by rfl) ⟨181031, by rfl⟩ : syracuseStep 965501 = 362063) (by norm_num)
theorem B965525 : Blo 642303 965525 := bbase (se 6 (by rfl) ⟨22629, by rfl⟩ : syracuseStep 965525 = 45259) (by norm_num)
theorem B1031077 : Blo 642303 1031077 := bbase (se 4 (by rfl) ⟨96663, by rfl⟩ : syracuseStep 1031077 = 193327) (by norm_num)
theorem B965549 : Blo 642303 965549 := bbase (se 3 (by rfl) ⟨181040, by rfl⟩ : syracuseStep 965549 = 362081) (by norm_num)
theorem B965573 : Blo 642303 965573 := bbase (se 4 (by rfl) ⟨90522, by rfl⟩ : syracuseStep 965573 = 181045) (by norm_num)
theorem B965597 : Blo 642303 965597 := bbase (se 3 (by rfl) ⟨181049, by rfl⟩ : syracuseStep 965597 = 362099) (by norm_num)
theorem B965621 : Blo 642303 965621 := bbase (se 5 (by rfl) ⟨45263, by rfl⟩ : syracuseStep 965621 = 90527) (by norm_num)
theorem B965645 : Blo 642303 965645 := bbase (se 3 (by rfl) ⟨181058, by rfl⟩ : syracuseStep 965645 = 362117) (by norm_num)
theorem B965669 : Blo 642303 965669 := bbase (se 4 (by rfl) ⟨90531, by rfl⟩ : syracuseStep 965669 = 181063) (by norm_num)
theorem B1653805 : Blo 642303 1653805 := bbase (se 3 (by rfl) ⟨310088, by rfl⟩ : syracuseStep 1653805 = 620177) (by norm_num)
theorem B965693 : Blo 642303 965693 := bbase (se 3 (by rfl) ⟨181067, by rfl⟩ : syracuseStep 965693 = 362135) (by norm_num)
theorem B965717 : Blo 642303 965717 := bbase (se 8 (by rfl) ⟨5658, by rfl⟩ : syracuseStep 965717 = 11317) (by norm_num)
theorem B3095653 : Blo 642303 3095653 := bbase (se 4 (by rfl) ⟨290217, by rfl⟩ : syracuseStep 3095653 = 580435) (by norm_num)
theorem B965741 : Blo 642303 965741 := bbase (se 3 (by rfl) ⟨181076, by rfl⟩ : syracuseStep 965741 = 362153) (by norm_num)
theorem B965765 : Blo 642303 965765 := bbase (se 4 (by rfl) ⟨90540, by rfl⟩ : syracuseStep 965765 = 181081) (by norm_num)
theorem B736393 : Blo 642303 736393 := bbase (se 2 (by rfl) ⟨276147, by rfl⟩ : syracuseStep 736393 = 552295) (by norm_num)
theorem B2178197 : Blo 642303 2178197 := bbase (se 6 (by rfl) ⟨51051, by rfl⟩ : syracuseStep 2178197 = 102103) (by norm_num)
theorem B965789 : Blo 642303 965789 := bbase (se 3 (by rfl) ⟨181085, by rfl⟩ : syracuseStep 965789 = 362171) (by norm_num)
theorem B965813 : Blo 642303 965813 := bbase (se 5 (by rfl) ⟨45272, by rfl⟩ : syracuseStep 965813 = 90545) (by norm_num)
theorem B965837 : Blo 642303 965837 := bbase (se 3 (by rfl) ⟨181094, by rfl⟩ : syracuseStep 965837 = 362189) (by norm_num)
theorem B965861 : Blo 642303 965861 := bbase (se 4 (by rfl) ⟨90549, by rfl⟩ : syracuseStep 965861 = 181099) (by norm_num)
theorem B6208757 : Blo 642303 6208757 := bbase (se 5 (by rfl) ⟨291035, by rfl⟩ : syracuseStep 6208757 = 582071) (by norm_num)
theorem B965885 : Blo 642303 965885 := bbase (se 3 (by rfl) ⟨181103, by rfl⟩ : syracuseStep 965885 = 362207) (by norm_num)
theorem B965909 : Blo 642303 965909 := bbase (se 6 (by rfl) ⟨22638, by rfl⟩ : syracuseStep 965909 = 45277) (by norm_num)
theorem B965933 : Blo 642303 965933 := bbase (se 3 (by rfl) ⟨181112, by rfl⟩ : syracuseStep 965933 = 362225) (by norm_num)
theorem B965957 : Blo 642303 965957 := bbase (se 4 (by rfl) ⟨90558, by rfl⟩ : syracuseStep 965957 = 181117) (by norm_num)
theorem B965981 : Blo 642303 965981 := bbase (se 3 (by rfl) ⟨181121, by rfl⟩ : syracuseStep 965981 = 362243) (by norm_num)
theorem B966005 : Blo 642303 966005 := bbase (se 5 (by rfl) ⟨45281, by rfl⟩ : syracuseStep 966005 = 90563) (by norm_num)
theorem B966029 : Blo 642303 966029 := bbase (se 3 (by rfl) ⟨181130, by rfl⟩ : syracuseStep 966029 = 362261) (by norm_num)
theorem B966053 : Blo 642303 966053 := bbase (se 4 (by rfl) ⟨90567, by rfl⟩ : syracuseStep 966053 = 181135) (by norm_num)
theorem B966077 : Blo 642303 966077 := bbase (se 3 (by rfl) ⟨181139, by rfl⟩ : syracuseStep 966077 = 362279) (by norm_num)
theorem B966101 : Blo 642303 966101 := bbase (se 7 (by rfl) ⟨11321, by rfl⟩ : syracuseStep 966101 = 22643) (by norm_num)
theorem B966125 : Blo 642303 966125 := bbase (se 3 (by rfl) ⟨181148, by rfl⟩ : syracuseStep 966125 = 362297) (by norm_num)
theorem B966149 : Blo 642303 966149 := bbase (se 4 (by rfl) ⟨90576, by rfl⟩ : syracuseStep 966149 = 181153) (by norm_num)
theorem B3259925 : Blo 642303 3259925 := bbase (se 6 (by rfl) ⟨76404, by rfl⟩ : syracuseStep 3259925 = 152809) (by norm_num)
theorem B966173 : Blo 642303 966173 := bbase (se 3 (by rfl) ⟨181157, by rfl⟩ : syracuseStep 966173 = 362315) (by norm_num)
theorem B966197 : Blo 642303 966197 := bbase (se 5 (by rfl) ⟨45290, by rfl⟩ : syracuseStep 966197 = 90581) (by norm_num)
theorem B2178629 : Blo 642303 2178629 := bbase (se 4 (by rfl) ⟨204246, by rfl⟩ : syracuseStep 2178629 = 408493) (by norm_num)
theorem B966221 : Blo 642303 966221 := bbase (se 3 (by rfl) ⟨181166, by rfl⟩ : syracuseStep 966221 = 362333) (by norm_num)
theorem B966245 : Blo 642303 966245 := bbase (se 4 (by rfl) ⟨90585, by rfl⟩ : syracuseStep 966245 = 181171) (by norm_num)
theorem B966269 : Blo 642303 966269 := bbase (se 3 (by rfl) ⟨181175, by rfl⟩ : syracuseStep 966269 = 362351) (by norm_num)
theorem B966293 : Blo 642303 966293 := bbase (se 6 (by rfl) ⟨22647, by rfl⟩ : syracuseStep 966293 = 45295) (by norm_num)
theorem B966317 : Blo 642303 966317 := bbase (se 3 (by rfl) ⟨181184, by rfl⟩ : syracuseStep 966317 = 362369) (by norm_num)
theorem B736949 : Blo 642303 736949 := bbase (se 5 (by rfl) ⟨34544, by rfl⟩ : syracuseStep 736949 = 69089) (by norm_num)
theorem B966341 : Blo 642303 966341 := bbase (se 4 (by rfl) ⟨90594, by rfl⟩ : syracuseStep 966341 = 181189) (by norm_num)
theorem B966365 : Blo 642303 966365 := bbase (se 3 (by rfl) ⟨181193, by rfl⟩ : syracuseStep 966365 = 362387) (by norm_num)
theorem B966389 : Blo 642303 966389 := bbase (se 5 (by rfl) ⟨45299, by rfl⟩ : syracuseStep 966389 = 90599) (by norm_num)
theorem B966413 : Blo 642303 966413 := bbase (se 3 (by rfl) ⟨181202, by rfl⟩ : syracuseStep 966413 = 362405) (by norm_num)
theorem B966437 : Blo 642303 966437 := bbase (se 4 (by rfl) ⟨90603, by rfl⟩ : syracuseStep 966437 = 181207) (by norm_num)
theorem B966461 : Blo 642303 966461 := bbase (se 3 (by rfl) ⟨181211, by rfl⟩ : syracuseStep 966461 = 362423) (by norm_num)
theorem B966485 : Blo 642303 966485 := bbase (se 9 (by rfl) ⟨2831, by rfl⟩ : syracuseStep 966485 = 5663) (by norm_num)
theorem B966509 : Blo 642303 966509 := bbase (se 3 (by rfl) ⟨181220, by rfl⟩ : syracuseStep 966509 = 362441) (by norm_num)
theorem B966533 : Blo 642303 966533 := bbase (se 4 (by rfl) ⟨90612, by rfl⟩ : syracuseStep 966533 = 181225) (by norm_num)
theorem B1032077 : Blo 642303 1032077 := bbase (se 3 (by rfl) ⟨193514, by rfl⟩ : syracuseStep 1032077 = 387029) (by norm_num)
theorem B966557 : Blo 642303 966557 := bbase (se 3 (by rfl) ⟨181229, by rfl⟩ : syracuseStep 966557 = 362459) (by norm_num)
theorem B966581 : Blo 642303 966581 := bbase (se 5 (by rfl) ⟨45308, by rfl⟩ : syracuseStep 966581 = 90617) (by norm_num)
theorem B966605 : Blo 642303 966605 := bbase (se 3 (by rfl) ⟨181238, by rfl⟩ : syracuseStep 966605 = 362477) (by norm_num)
theorem B966629 : Blo 642303 966629 := bbase (se 4 (by rfl) ⟨90621, by rfl⟩ : syracuseStep 966629 = 181243) (by norm_num)
theorem B2179061 : Blo 642303 2179061 := bbase (se 5 (by rfl) ⟨102143, by rfl⟩ : syracuseStep 2179061 = 204287) (by norm_num)
theorem B966653 : Blo 642303 966653 := bbase (se 3 (by rfl) ⟨181247, by rfl⟩ : syracuseStep 966653 = 362495) (by norm_num)
theorem B1032205 : Blo 642303 1032205 := bbase (se 3 (by rfl) ⟨193538, by rfl⟩ : syracuseStep 1032205 = 387077) (by norm_num)
theorem B966677 : Blo 642303 966677 := bbase (se 6 (by rfl) ⟨22656, by rfl⟩ : syracuseStep 966677 = 45313) (by norm_num)
theorem B966701 : Blo 642303 966701 := bbase (se 3 (by rfl) ⟨181256, by rfl⟩ : syracuseStep 966701 = 362513) (by norm_num)
theorem B2441285 : Blo 642303 2441285 := bbase (se 4 (by rfl) ⟨228870, by rfl⟩ : syracuseStep 2441285 = 457741) (by norm_num)
theorem B966725 : Blo 642303 966725 := bbase (se 4 (by rfl) ⟨90630, by rfl⟩ : syracuseStep 966725 = 181261) (by norm_num)
theorem B966749 : Blo 642303 966749 := bbase (se 3 (by rfl) ⟨181265, by rfl⟩ : syracuseStep 966749 = 362531) (by norm_num)
theorem B966773 : Blo 642303 966773 := bbase (se 5 (by rfl) ⟨45317, by rfl⟩ : syracuseStep 966773 = 90635) (by norm_num)
theorem B966797 : Blo 642303 966797 := bbase (se 3 (by rfl) ⟨181274, by rfl⟩ : syracuseStep 966797 = 362549) (by norm_num)
theorem B868501 : Blo 642303 868501 := bbase (se 6 (by rfl) ⟨20355, by rfl⟩ : syracuseStep 868501 = 40711) (by norm_num)
theorem B966821 : Blo 642303 966821 := bbase (se 4 (by rfl) ⟨90639, by rfl⟩ : syracuseStep 966821 = 181279) (by norm_num)
theorem B966845 : Blo 642303 966845 := bbase (se 3 (by rfl) ⟨181283, by rfl⟩ : syracuseStep 966845 = 362567) (by norm_num)
theorem B966869 : Blo 642303 966869 := bbase (se 7 (by rfl) ⟨11330, by rfl⟩ : syracuseStep 966869 = 22661) (by norm_num)
theorem B1327333 : Blo 642303 1327333 := bbase (se 4 (by rfl) ⟨124437, by rfl⟩ : syracuseStep 1327333 = 248875) (by norm_num)
theorem B966893 : Blo 642303 966893 := bbase (se 3 (by rfl) ⟨181292, by rfl⟩ : syracuseStep 966893 = 362585) (by norm_num)
theorem B966917 : Blo 642303 966917 := bbase (se 4 (by rfl) ⟨90648, by rfl⟩ : syracuseStep 966917 = 181297) (by norm_num)
theorem B966941 : Blo 642303 966941 := bbase (se 3 (by rfl) ⟨181301, by rfl⟩ : syracuseStep 966941 = 362603) (by norm_num)
theorem B966965 : Blo 642303 966965 := bbase (se 5 (by rfl) ⟨45326, by rfl⟩ : syracuseStep 966965 = 90653) (by norm_num)
theorem B966989 : Blo 642303 966989 := bbase (se 3 (by rfl) ⟨181310, by rfl⟩ : syracuseStep 966989 = 362621) (by norm_num)
theorem B2441573 : Blo 642303 2441573 := bbase (se 4 (by rfl) ⟨228897, by rfl⟩ : syracuseStep 2441573 = 457795) (by norm_num)
theorem B967013 : Blo 642303 967013 := bbase (se 4 (by rfl) ⟨90657, by rfl⟩ : syracuseStep 967013 = 181315) (by norm_num)
theorem B967037 : Blo 642303 967037 := bbase (se 3 (by rfl) ⟨181319, by rfl⟩ : syracuseStep 967037 = 362639) (by norm_num)
theorem B1032589 : Blo 642303 1032589 := bbase (se 3 (by rfl) ⟨193610, by rfl⟩ : syracuseStep 1032589 = 387221) (by norm_num)
theorem B967061 : Blo 642303 967061 := bbase (se 6 (by rfl) ⟨22665, by rfl⟩ : syracuseStep 967061 = 45331) (by norm_num)
theorem B2179493 : Blo 642303 2179493 := bbase (se 4 (by rfl) ⟨204327, by rfl⟩ : syracuseStep 2179493 = 408655) (by norm_num)
theorem B967085 : Blo 642303 967085 := bbase (se 3 (by rfl) ⟨181328, by rfl⟩ : syracuseStep 967085 = 362657) (by norm_num)
theorem B967109 : Blo 642303 967109 := bbase (se 4 (by rfl) ⟨90666, by rfl⟩ : syracuseStep 967109 = 181333) (by norm_num)
theorem B967133 : Blo 642303 967133 := bbase (se 3 (by rfl) ⟨181337, by rfl⟩ : syracuseStep 967133 = 362675) (by norm_num)
theorem B967157 : Blo 642303 967157 := bbase (se 5 (by rfl) ⟨45335, by rfl⟩ : syracuseStep 967157 = 90671) (by norm_num)
theorem B967181 : Blo 642303 967181 := bbase (se 3 (by rfl) ⟨181346, by rfl⟩ : syracuseStep 967181 = 362693) (by norm_num)
theorem B967205 : Blo 642303 967205 := bbase (se 4 (by rfl) ⟨90675, by rfl⟩ : syracuseStep 967205 = 181351) (by norm_num)
theorem B967229 : Blo 642303 967229 := bbase (se 3 (by rfl) ⟨181355, by rfl⟩ : syracuseStep 967229 = 362711) (by norm_num)
theorem B967253 : Blo 642303 967253 := bbase (se 8 (by rfl) ⟨5667, by rfl⟩ : syracuseStep 967253 = 11335) (by norm_num)
theorem B967277 : Blo 642303 967277 := bbase (se 3 (by rfl) ⟨181364, by rfl⟩ : syracuseStep 967277 = 362729) (by norm_num)
theorem B967301 : Blo 642303 967301 := bbase (se 4 (by rfl) ⟨90684, by rfl⟩ : syracuseStep 967301 = 181369) (by norm_num)
theorem B1032845 : Blo 642303 1032845 := bbase (se 3 (by rfl) ⟨193658, by rfl⟩ : syracuseStep 1032845 = 387317) (by norm_num)
theorem B3981973 : Blo 642303 3981973 := bbase (se 6 (by rfl) ⟨93327, by rfl⟩ : syracuseStep 3981973 = 186655) (by norm_num)
theorem B836249 : Blo 642303 836249 := bbase (se 2 (by rfl) ⟨313593, by rfl⟩ : syracuseStep 836249 = 627187) (by norm_num)
theorem B967325 : Blo 642303 967325 := bbase (se 3 (by rfl) ⟨181373, by rfl⟩ : syracuseStep 967325 = 362747) (by norm_num)
theorem B967349 : Blo 642303 967349 := bbase (se 5 (by rfl) ⟨45344, by rfl⟩ : syracuseStep 967349 = 90689) (by norm_num)
theorem B967373 : Blo 642303 967373 := bbase (se 3 (by rfl) ⟨181382, by rfl⟩ : syracuseStep 967373 = 362765) (by norm_num)
theorem B967397 : Blo 642303 967397 := bbase (se 4 (by rfl) ⟨90693, by rfl⟩ : syracuseStep 967397 = 181387) (by norm_num)
theorem B967421 : Blo 642303 967421 := bbase (se 3 (by rfl) ⟨181391, by rfl⟩ : syracuseStep 967421 = 362783) (by norm_num)
theorem B967445 : Blo 642303 967445 := bbase (se 6 (by rfl) ⟨22674, by rfl⟩ : syracuseStep 967445 = 45349) (by norm_num)
theorem B3261221 : Blo 642303 3261221 := bbase (se 4 (by rfl) ⟨305739, by rfl⟩ : syracuseStep 3261221 = 611479) (by norm_num)
theorem B967469 : Blo 642303 967469 := bbase (se 3 (by rfl) ⟨181400, by rfl⟩ : syracuseStep 967469 = 362801) (by norm_num)
theorem B3490613 : Blo 642303 3490613 := bbase (se 5 (by rfl) ⟨163622, by rfl⟩ : syracuseStep 3490613 = 327245) (by norm_num)
theorem B967493 : Blo 642303 967493 := bbase (se 4 (by rfl) ⟨90702, by rfl⟩ : syracuseStep 967493 = 181405) (by norm_num)
theorem B2179925 : Blo 642303 2179925 := bbase (se 9 (by rfl) ⟨6386, by rfl⟩ : syracuseStep 2179925 = 12773) (by norm_num)
theorem B967517 : Blo 642303 967517 := bbase (se 3 (by rfl) ⟨181409, by rfl⟩ : syracuseStep 967517 = 362819) (by norm_num)
theorem B967541 : Blo 642303 967541 := bbase (se 5 (by rfl) ⟨45353, by rfl⟩ : syracuseStep 967541 = 90707) (by norm_num)
theorem B967565 : Blo 642303 967565 := bbase (se 3 (by rfl) ⟨181418, by rfl⟩ : syracuseStep 967565 = 362837) (by norm_num)
theorem B967589 : Blo 642303 967589 := bbase (se 4 (by rfl) ⟨90711, by rfl⟩ : syracuseStep 967589 = 181423) (by norm_num)
theorem B1098677 : Blo 642303 1098677 := bbase (se 5 (by rfl) ⟨51500, by rfl⟩ : syracuseStep 1098677 = 103001) (by norm_num)
theorem B967613 : Blo 642303 967613 := bbase (se 3 (by rfl) ⟨181427, by rfl⟩ : syracuseStep 967613 = 362855) (by norm_num)
theorem B967637 : Blo 642303 967637 := bbase (se 7 (by rfl) ⟨11339, by rfl⟩ : syracuseStep 967637 = 22679) (by norm_num)
theorem B967661 : Blo 642303 967661 := bbase (se 3 (by rfl) ⟨181436, by rfl⟩ : syracuseStep 967661 = 362873) (by norm_num)
theorem B967685 : Blo 642303 967685 := bbase (se 4 (by rfl) ⟨90720, by rfl⟩ : syracuseStep 967685 = 181441) (by norm_num)
theorem B967709 : Blo 642303 967709 := bbase (se 3 (by rfl) ⟨181445, by rfl⟩ : syracuseStep 967709 = 362891) (by norm_num)
theorem B967733 : Blo 642303 967733 := bbase (se 5 (by rfl) ⟨45362, by rfl⟩ : syracuseStep 967733 = 90725) (by norm_num)
theorem B967757 : Blo 642303 967757 := bbase (se 3 (by rfl) ⟨181454, by rfl⟩ : syracuseStep 967757 = 362909) (by norm_num)
theorem B967781 : Blo 642303 967781 := bbase (se 4 (by rfl) ⟨90729, by rfl⟩ : syracuseStep 967781 = 181459) (by norm_num)
theorem B967805 : Blo 642303 967805 := bbase (se 3 (by rfl) ⟨181463, by rfl⟩ : syracuseStep 967805 = 362927) (by norm_num)
theorem B967829 : Blo 642303 967829 := bbase (se 6 (by rfl) ⟨22683, by rfl⟩ : syracuseStep 967829 = 45367) (by norm_num)
theorem B967853 : Blo 642303 967853 := bbase (se 3 (by rfl) ⟨181472, by rfl⟩ : syracuseStep 967853 = 362945) (by norm_num)
theorem B967877 : Blo 642303 967877 := bbase (se 4 (by rfl) ⟨90738, by rfl⟩ : syracuseStep 967877 = 181477) (by norm_num)
theorem B967901 : Blo 642303 967901 := bbase (se 3 (by rfl) ⟨181481, by rfl⟩ : syracuseStep 967901 = 362963) (by norm_num)
theorem B967925 : Blo 642303 967925 := bbase (se 5 (by rfl) ⟨45371, by rfl⟩ : syracuseStep 967925 = 90743) (by norm_num)
theorem B2180357 : Blo 642303 2180357 := bbase (se 4 (by rfl) ⟨204408, by rfl⟩ : syracuseStep 2180357 = 408817) (by norm_num)
theorem B967949 : Blo 642303 967949 := bbase (se 3 (by rfl) ⟨181490, by rfl⟩ : syracuseStep 967949 = 362981) (by norm_num)
theorem B967973 : Blo 642303 967973 := bbase (se 4 (by rfl) ⟨90747, by rfl⟩ : syracuseStep 967973 = 181495) (by norm_num)
theorem B967997 : Blo 642303 967997 := bbase (se 3 (by rfl) ⟨181499, by rfl⟩ : syracuseStep 967997 = 362999) (by norm_num)
theorem B968021 : Blo 642303 968021 := bbase (se 12 (by rfl) ⟨354, by rfl⟩ : syracuseStep 968021 = 709) (by norm_num)
theorem B968045 : Blo 642303 968045 := bbase (se 3 (by rfl) ⟨181508, by rfl⟩ : syracuseStep 968045 = 363017) (by norm_num)
theorem B1164661 : Blo 642303 1164661 := bbase (se 5 (by rfl) ⟨54593, by rfl⟩ : syracuseStep 1164661 = 109187) (by norm_num)
theorem B968069 : Blo 642303 968069 := bbase (se 4 (by rfl) ⟨90756, by rfl⟩ : syracuseStep 968069 = 181513) (by norm_num)
theorem B968093 : Blo 642303 968093 := bbase (se 3 (by rfl) ⟨181517, by rfl⟩ : syracuseStep 968093 = 363035) (by norm_num)
theorem B968117 : Blo 642303 968117 := bbase (se 5 (by rfl) ⟨45380, by rfl⟩ : syracuseStep 968117 = 90761) (by norm_num)
theorem B968141 : Blo 642303 968141 := bbase (se 3 (by rfl) ⟨181526, by rfl⟩ : syracuseStep 968141 = 363053) (by norm_num)
theorem B968165 : Blo 642303 968165 := bbase (se 4 (by rfl) ⟨90765, by rfl⟩ : syracuseStep 968165 = 181531) (by norm_num)
theorem B1033717 : Blo 642303 1033717 := bbase (se 5 (by rfl) ⟨48455, by rfl⟩ : syracuseStep 1033717 = 96911) (by norm_num)
theorem B968189 : Blo 642303 968189 := bbase (se 3 (by rfl) ⟨181535, by rfl⟩ : syracuseStep 968189 = 363071) (by norm_num)
theorem B2442757 : Blo 642303 2442757 := bbase (se 4 (by rfl) ⟨229008, by rfl⟩ : syracuseStep 2442757 = 458017) (by norm_num)
theorem B968213 : Blo 642303 968213 := bbase (se 6 (by rfl) ⟨22692, by rfl⟩ : syracuseStep 968213 = 45385) (by norm_num)
theorem B968237 : Blo 642303 968237 := bbase (se 3 (by rfl) ⟨181544, by rfl⟩ : syracuseStep 968237 = 363089) (by norm_num)
theorem B1099333 : Blo 642303 1099333 := bbase (se 4 (by rfl) ⟨103062, by rfl⟩ : syracuseStep 1099333 = 206125) (by norm_num)
theorem B968261 : Blo 642303 968261 := bbase (se 4 (by rfl) ⟨90774, by rfl⟩ : syracuseStep 968261 = 181549) (by norm_num)
theorem B1033813 : Blo 642303 1033813 := bbase (se 8 (by rfl) ⟨6057, by rfl⟩ : syracuseStep 1033813 = 12115) (by norm_num)
theorem B968285 : Blo 642303 968285 := bbase (se 3 (by rfl) ⟨181553, by rfl⟩ : syracuseStep 968285 = 363107) (by norm_num)
theorem B968309 : Blo 642303 968309 := bbase (se 5 (by rfl) ⟨45389, by rfl⟩ : syracuseStep 968309 = 90779) (by norm_num)
theorem B968333 : Blo 642303 968333 := bbase (se 3 (by rfl) ⟨181562, by rfl⟩ : syracuseStep 968333 = 363125) (by norm_num)
theorem B968357 : Blo 642303 968357 := bbase (se 4 (by rfl) ⟨90783, by rfl⟩ : syracuseStep 968357 = 181567) (by norm_num)
theorem B2180789 : Blo 642303 2180789 := bbase (se 5 (by rfl) ⟨102224, by rfl⟩ : syracuseStep 2180789 = 204449) (by norm_num)
theorem B968381 : Blo 642303 968381 := bbase (se 3 (by rfl) ⟨181571, by rfl⟩ : syracuseStep 968381 = 363143) (by norm_num)
theorem B968405 : Blo 642303 968405 := bbase (se 7 (by rfl) ⟨11348, by rfl⟩ : syracuseStep 968405 = 22697) (by norm_num)
theorem B968429 : Blo 642303 968429 := bbase (se 3 (by rfl) ⟨181580, by rfl⟩ : syracuseStep 968429 = 363161) (by norm_num)
theorem B1033973 : Blo 642303 1033973 := bbase (se 5 (by rfl) ⟨48467, by rfl⟩ : syracuseStep 1033973 = 96935) (by norm_num)
theorem B968453 : Blo 642303 968453 := bbase (se 4 (by rfl) ⟨90792, by rfl⟩ : syracuseStep 968453 = 181585) (by norm_num)
theorem B968477 : Blo 642303 968477 := bbase (se 3 (by rfl) ⟨181589, by rfl⟩ : syracuseStep 968477 = 363179) (by norm_num)
theorem B2443061 : Blo 642303 2443061 := bbase (se 5 (by rfl) ⟨114518, by rfl⟩ : syracuseStep 2443061 = 229037) (by norm_num)
theorem B968501 : Blo 642303 968501 := bbase (se 5 (by rfl) ⟨45398, by rfl⟩ : syracuseStep 968501 = 90797) (by norm_num)
theorem B2475845 : Blo 642303 2475845 := bbase (se 4 (by rfl) ⟨232110, by rfl⟩ : syracuseStep 2475845 = 464221) (by norm_num)
theorem B968525 : Blo 642303 968525 := bbase (se 3 (by rfl) ⟨181598, by rfl⟩ : syracuseStep 968525 = 363197) (by norm_num)
theorem B968549 : Blo 642303 968549 := bbase (se 4 (by rfl) ⟨90801, by rfl⟩ : syracuseStep 968549 = 181603) (by norm_num)
theorem B968573 : Blo 642303 968573 := bbase (se 3 (by rfl) ⟨181607, by rfl⟩ : syracuseStep 968573 = 363215) (by norm_num)
theorem B771977 : Blo 642303 771977 := bbase (se 2 (by rfl) ⟨289491, by rfl⟩ : syracuseStep 771977 = 578983) (by norm_num)
theorem B968597 : Blo 642303 968597 := bbase (se 6 (by rfl) ⟨22701, by rfl⟩ : syracuseStep 968597 = 45403) (by norm_num)
theorem B968621 : Blo 642303 968621 := bbase (se 3 (by rfl) ⟨181616, by rfl⟩ : syracuseStep 968621 = 363233) (by norm_num)
theorem B968645 : Blo 642303 968645 := bbase (se 4 (by rfl) ⟨90810, by rfl⟩ : syracuseStep 968645 = 181621) (by norm_num)
theorem B968669 : Blo 642303 968669 := bbase (se 3 (by rfl) ⟨181625, by rfl⟩ : syracuseStep 968669 = 363251) (by norm_num)
theorem B968693 : Blo 642303 968693 := bbase (se 5 (by rfl) ⟨45407, by rfl⟩ : syracuseStep 968693 = 90815) (by norm_num)
theorem B968717 : Blo 642303 968717 := bbase (se 3 (by rfl) ⟨181634, by rfl⟩ : syracuseStep 968717 = 363269) (by norm_num)
theorem B968741 : Blo 642303 968741 := bbase (se 4 (by rfl) ⟨90819, by rfl⟩ : syracuseStep 968741 = 181639) (by norm_num)
theorem B3262517 : Blo 642303 3262517 := bbase (se 5 (by rfl) ⟨152930, by rfl⟩ : syracuseStep 3262517 = 305861) (by norm_num)
theorem B968765 : Blo 642303 968765 := bbase (se 3 (by rfl) ⟨181643, by rfl⟩ : syracuseStep 968765 = 363287) (by norm_num)
theorem B968789 : Blo 642303 968789 := bbase (se 8 (by rfl) ⟨5676, by rfl⟩ : syracuseStep 968789 = 11353) (by norm_num)
theorem B2181221 : Blo 642303 2181221 := bbase (se 4 (by rfl) ⟨204489, by rfl⟩ : syracuseStep 2181221 = 408979) (by norm_num)
theorem B968813 : Blo 642303 968813 := bbase (se 3 (by rfl) ⟨181652, by rfl⟩ : syracuseStep 968813 = 363305) (by norm_num)
theorem B968837 : Blo 642303 968837 := bbase (se 4 (by rfl) ⟨90828, by rfl⟩ : syracuseStep 968837 = 181657) (by norm_num)
theorem B4638869 : Blo 642303 4638869 := bbase (se 6 (by rfl) ⟨108723, by rfl⟩ : syracuseStep 4638869 = 217447) (by norm_num)
theorem B968861 : Blo 642303 968861 := bbase (se 3 (by rfl) ⟨181661, by rfl⟩ : syracuseStep 968861 = 363323) (by norm_num)
theorem B968885 : Blo 642303 968885 := bbase (se 5 (by rfl) ⟨45416, by rfl⟩ : syracuseStep 968885 = 90833) (by norm_num)
theorem B968909 : Blo 642303 968909 := bbase (se 3 (by rfl) ⟨181670, by rfl⟩ : syracuseStep 968909 = 363341) (by norm_num)
theorem B968933 : Blo 642303 968933 := bbase (se 4 (by rfl) ⟨90837, by rfl⟩ : syracuseStep 968933 = 181675) (by norm_num)
theorem B870637 : Blo 642303 870637 := bbase (se 3 (by rfl) ⟨163244, by rfl⟩ : syracuseStep 870637 = 326489) (by norm_num)
theorem B968957 : Blo 642303 968957 := bbase (se 3 (by rfl) ⟨181679, by rfl⟩ : syracuseStep 968957 = 363359) (by norm_num)
theorem B968981 : Blo 642303 968981 := bbase (se 6 (by rfl) ⟨22710, by rfl⟩ : syracuseStep 968981 = 45421) (by norm_num)
theorem B969005 : Blo 642303 969005 := bbase (se 3 (by rfl) ⟨181688, by rfl⟩ : syracuseStep 969005 = 363377) (by norm_num)
theorem B969029 : Blo 642303 969029 := bbase (se 4 (by rfl) ⟨90846, by rfl⟩ : syracuseStep 969029 = 181693) (by norm_num)
theorem B969053 : Blo 642303 969053 := bbase (se 3 (by rfl) ⟨181697, by rfl⟩ : syracuseStep 969053 = 363395) (by norm_num)
theorem B772453 : Blo 642303 772453 := bbase (se 4 (by rfl) ⟨72417, by rfl⟩ : syracuseStep 772453 = 144835) (by norm_num)
theorem B969077 : Blo 642303 969077 := bbase (se 5 (by rfl) ⟨45425, by rfl⟩ : syracuseStep 969077 = 90851) (by norm_num)
theorem B772481 : Blo 642303 772481 := bbase (se 2 (by rfl) ⟨289680, by rfl⟩ : syracuseStep 772481 = 579361) (by norm_num)
theorem B969101 : Blo 642303 969101 := bbase (se 3 (by rfl) ⟨181706, by rfl⟩ : syracuseStep 969101 = 363413) (by norm_num)
theorem B2935205 : Blo 642303 2935205 := bbase (se 4 (by rfl) ⟨275175, by rfl⟩ : syracuseStep 2935205 = 550351) (by norm_num)
theorem B969125 : Blo 642303 969125 := bbase (se 4 (by rfl) ⟨90855, by rfl⟩ : syracuseStep 969125 = 181711) (by norm_num)
theorem B969149 : Blo 642303 969149 := bbase (se 3 (by rfl) ⟨181715, by rfl⟩ : syracuseStep 969149 = 363431) (by norm_num)
theorem B969173 : Blo 642303 969173 := bbase (se 7 (by rfl) ⟨11357, by rfl⟩ : syracuseStep 969173 = 22715) (by norm_num)
theorem B969197 : Blo 642303 969197 := bbase (se 3 (by rfl) ⟨181724, by rfl⟩ : syracuseStep 969197 = 363449) (by norm_num)
theorem B707069 : Blo 642303 707069 := bbase (se 3 (by rfl) ⟨132575, by rfl⟩ : syracuseStep 707069 = 265151) (by norm_num)
theorem B969221 : Blo 642303 969221 := bbase (se 4 (by rfl) ⟨90864, by rfl⟩ : syracuseStep 969221 = 181729) (by norm_num)
theorem B969245 : Blo 642303 969245 := bbase (se 3 (by rfl) ⟨181733, by rfl⟩ : syracuseStep 969245 = 363467) (by norm_num)
theorem B969269 : Blo 642303 969269 := bbase (se 5 (by rfl) ⟨45434, by rfl⟩ : syracuseStep 969269 = 90869) (by norm_num)
theorem B772669 : Blo 642303 772669 := bbase (se 3 (by rfl) ⟨144875, by rfl⟩ : syracuseStep 772669 = 289751) (by norm_num)
theorem B969293 : Blo 642303 969293 := bbase (se 3 (by rfl) ⟨181742, by rfl⟩ : syracuseStep 969293 = 363485) (by norm_num)
theorem B969317 : Blo 642303 969317 := bbase (se 4 (by rfl) ⟨90873, by rfl⟩ : syracuseStep 969317 = 181747) (by norm_num)
theorem B969341 : Blo 642303 969341 := bbase (se 3 (by rfl) ⟨181751, by rfl⟩ : syracuseStep 969341 = 363503) (by norm_num)
theorem B969365 : Blo 642303 969365 := bbase (se 6 (by rfl) ⟨22719, by rfl⟩ : syracuseStep 969365 = 45439) (by norm_num)
theorem B969389 : Blo 642303 969389 := bbase (se 3 (by rfl) ⟨181760, by rfl⟩ : syracuseStep 969389 = 363521) (by norm_num)
theorem B772789 : Blo 642303 772789 := bbase (se 5 (by rfl) ⟨36224, by rfl⟩ : syracuseStep 772789 = 72449) (by norm_num)
theorem B1100477 : Blo 642303 1100477 := bbase (se 3 (by rfl) ⟨206339, by rfl⟩ : syracuseStep 1100477 = 412679) (by norm_num)
theorem B969413 : Blo 642303 969413 := bbase (se 4 (by rfl) ⟨90882, by rfl⟩ : syracuseStep 969413 = 181765) (by norm_num)
theorem B871117 : Blo 642303 871117 := bbase (se 3 (by rfl) ⟨163334, by rfl⟩ : syracuseStep 871117 = 326669) (by norm_num)
theorem B969437 : Blo 642303 969437 := bbase (se 3 (by rfl) ⟨181769, by rfl⟩ : syracuseStep 969437 = 363539) (by norm_num)
theorem B1035101 : Blo 642303 1035101 := bbase (se 3 (by rfl) ⟨194081, by rfl⟩ : syracuseStep 1035101 = 388163) (by norm_num)
theorem B3099653 : Blo 642303 3099653 := bbase (se 4 (by rfl) ⟨290592, by rfl⟩ : syracuseStep 3099653 = 581185) (by norm_num)
theorem B2608357 : Blo 642303 2608357 := bbase (se 4 (by rfl) ⟨244533, by rfl⟩ : syracuseStep 2608357 = 489067) (by norm_num)
theorem B3263813 : Blo 642303 3263813 := bbase (se 4 (by rfl) ⟨305982, by rfl⟩ : syracuseStep 3263813 = 611965) (by norm_num)
theorem B11750741 : Blo 642303 11750741 := bbase (se 11 (by rfl) ⟨8606, by rfl⟩ : syracuseStep 11750741 = 17213) (by norm_num)
theorem B1625933 : Blo 642303 1625933 := bbase (se 3 (by rfl) ⟨304862, by rfl⟩ : syracuseStep 1625933 = 609725) (by norm_num)
theorem B2445173 : Blo 642303 2445173 := bbase (se 5 (by rfl) ⟨114617, by rfl⟩ : syracuseStep 2445173 = 229235) (by norm_num)
theorem B2543605 : Blo 642303 2543605 := bbase (se 5 (by rfl) ⟨119231, by rfl⟩ : syracuseStep 2543605 = 238463) (by norm_num)
theorem B8278037 : Blo 642303 8278037 := bbase (se 6 (by rfl) ⟨194016, by rfl⟩ : syracuseStep 8278037 = 388033) (by norm_num)
theorem B872501 : Blo 642303 872501 := bbase (se 5 (by rfl) ⟨40898, by rfl⟩ : syracuseStep 872501 = 81797) (by norm_num)
theorem B2445461 : Blo 642303 2445461 := bbase (se 6 (by rfl) ⟨57315, by rfl⟩ : syracuseStep 2445461 = 114631) (by norm_num)
theorem B3723413 : Blo 642303 3723413 := bbase (se 6 (by rfl) ⟨87267, by rfl⟩ : syracuseStep 3723413 = 174535) (by norm_num)
theorem B1626277 : Blo 642303 1626277 := bbase (se 4 (by rfl) ⟨152463, by rfl⟩ : syracuseStep 1626277 = 304927) (by norm_num)
theorem B774365 : Blo 642303 774365 := bbase (se 3 (by rfl) ⟨145193, by rfl⟩ : syracuseStep 774365 = 290387) (by norm_num)
theorem B4903157 : Blo 642303 4903157 := bbase (se 5 (by rfl) ⟨229835, by rfl⟩ : syracuseStep 4903157 = 459671) (by norm_num)
theorem B1626389 : Blo 642303 1626389 := bbase (se 6 (by rfl) ⟨38118, by rfl⟩ : syracuseStep 1626389 = 76237) (by norm_num)
theorem B4903253 : Blo 642303 4903253 := bbase (se 10 (by rfl) ⟨7182, by rfl⟩ : syracuseStep 4903253 = 14365) (by norm_num)
theorem B1626581 : Blo 642303 1626581 := bbase (se 7 (by rfl) ⟨19061, by rfl⟩ : syracuseStep 1626581 = 38123) (by norm_num)
theorem B3265109 : Blo 642303 3265109 := bbase (se 8 (by rfl) ⟨19131, by rfl⟩ : syracuseStep 3265109 = 38263) (by norm_num)
theorem B1954469 : Blo 642303 1954469 := bbase (se 4 (by rfl) ⟨183231, by rfl⟩ : syracuseStep 1954469 = 366463) (by norm_num)
theorem B840449 : Blo 642303 840449 := bbase (se 2 (by rfl) ⟨315168, by rfl⟩ : syracuseStep 840449 = 630337) (by norm_num)
theorem B1626925 : Blo 642303 1626925 := bbase (se 3 (by rfl) ⟨305048, by rfl⟩ : syracuseStep 1626925 = 610097) (by norm_num)
theorem B775057 : Blo 642303 775057 := bbase (se 2 (by rfl) ⟨290646, by rfl⟩ : syracuseStep 775057 = 581293) (by norm_num)
theorem B1627037 : Blo 642303 1627037 := bbase (se 3 (by rfl) ⟨305069, by rfl⟩ : syracuseStep 1627037 = 610139) (by norm_num)
theorem B775153 : Blo 642303 775153 := bbase (se 2 (by rfl) ⟨290682, by rfl⟩ : syracuseStep 775153 = 581365) (by norm_num)
theorem B1102837 : Blo 642303 1102837 := bbase (se 5 (by rfl) ⟨51695, by rfl⟩ : syracuseStep 1102837 = 103391) (by norm_num)
theorem B8246357 : Blo 642303 8246357 := bbase (se 8 (by rfl) ⟨48318, by rfl⟩ : syracuseStep 8246357 = 96637) (by norm_num)
theorem B1627229 : Blo 642303 1627229 := bbase (se 3 (by rfl) ⟨305105, by rfl⟩ : syracuseStep 1627229 = 610211) (by norm_num)
theorem B2446645 : Blo 642303 2446645 := bbase (se 5 (by rfl) ⟨114686, by rfl⟩ : syracuseStep 2446645 = 229373) (by norm_num)
theorem B1627573 : Blo 642303 1627573 := bbase (se 5 (by rfl) ⟨76292, by rfl⟩ : syracuseStep 1627573 = 152585) (by norm_num)
theorem B1627685 : Blo 642303 1627685 := bbase (se 4 (by rfl) ⟨152595, by rfl⟩ : syracuseStep 1627685 = 305191) (by norm_num)
theorem B7329365 : Blo 642303 7329365 := bbase (se 8 (by rfl) ⟨42945, by rfl⟩ : syracuseStep 7329365 = 85891) (by norm_num)
theorem B2446949 : Blo 642303 2446949 := bbase (se 4 (by rfl) ⟨229401, by rfl⟩ : syracuseStep 2446949 = 458803) (by norm_num)
theorem B1627877 : Blo 642303 1627877 := bbase (se 4 (by rfl) ⟨152613, by rfl⟩ : syracuseStep 1627877 = 305227) (by norm_num)
theorem B775937 : Blo 642303 775937 := bbase (se 2 (by rfl) ⟨290976, by rfl⟩ : syracuseStep 775937 = 581953) (by norm_num)
theorem B3266405 : Blo 642303 3266405 := bbase (se 4 (by rfl) ⟨306225, by rfl⟩ : syracuseStep 3266405 = 612451) (by norm_num)
theorem B5494837 : Blo 642303 5494837 := bbase (se 5 (by rfl) ⟨257570, by rfl⟩ : syracuseStep 5494837 = 515141) (by norm_num)
theorem B776245 : Blo 642303 776245 := bbase (se 5 (by rfl) ⟨36386, by rfl⟩ : syracuseStep 776245 = 72773) (by norm_num)
theorem B1628221 : Blo 642303 1628221 := bbase (se 3 (by rfl) ⟨305291, by rfl⟩ : syracuseStep 1628221 = 610583) (by norm_num)
theorem B4642933 : Blo 642303 4642933 := bbase (se 5 (by rfl) ⟨217637, by rfl⟩ : syracuseStep 4642933 = 435275) (by norm_num)
theorem B2316437 : Blo 642303 2316437 := bbase (se 6 (by rfl) ⟨54291, by rfl⟩ : syracuseStep 2316437 = 108583) (by norm_num)
theorem B1628333 : Blo 642303 1628333 := bbase (se 3 (by rfl) ⟨305312, by rfl⟩ : syracuseStep 1628333 = 610625) (by norm_num)
theorem B1628525 : Blo 642303 1628525 := bbase (se 3 (by rfl) ⟨305348, by rfl⟩ : syracuseStep 1628525 = 610697) (by norm_num)
theorem B2316853 : Blo 642303 2316853 := bbase (se 5 (by rfl) ⟨108602, by rfl⟩ : syracuseStep 2316853 = 217205) (by norm_num)
theorem B3103285 : Blo 642303 3103285 := bbase (se 5 (by rfl) ⟨145466, by rfl⟩ : syracuseStep 3103285 = 290933) (by norm_num)
theorem B2316869 : Blo 642303 2316869 := bbase (se 4 (by rfl) ⟨217206, by rfl⟩ : syracuseStep 2316869 = 434413) (by norm_num)
theorem B1432205 : Blo 642303 1432205 := bbase (se 3 (by rfl) ⟨268538, by rfl⟩ : syracuseStep 1432205 = 537077) (by norm_num)
theorem B1465013 : Blo 642303 1465013 := bbase (se 5 (by rfl) ⟨68672, by rfl⟩ : syracuseStep 1465013 = 137345) (by norm_num)
theorem B1628869 : Blo 642303 1628869 := bbase (se 4 (by rfl) ⟨152706, by rfl⟩ : syracuseStep 1628869 = 305413) (by norm_num)
theorem B1628981 : Blo 642303 1628981 := bbase (se 5 (by rfl) ⟨76358, by rfl⟩ : syracuseStep 1628981 = 152717) (by norm_num)
theorem B2317157 : Blo 642303 2317157 := bbase (se 4 (by rfl) ⟨217233, by rfl⟩ : syracuseStep 2317157 = 434467) (by norm_num)
theorem B1858405 : Blo 642303 1858405 := bbase (se 4 (by rfl) ⟨174225, by rfl⟩ : syracuseStep 1858405 = 348451) (by norm_num)
theorem B1629173 : Blo 642303 1629173 := bbase (se 5 (by rfl) ⟨76367, by rfl⟩ : syracuseStep 1629173 = 152735) (by norm_num)
theorem B3267701 : Blo 642303 3267701 := bbase (se 5 (by rfl) ⟨153173, by rfl⟩ : syracuseStep 3267701 = 306347) (by norm_num)
theorem B744665 : Blo 642303 744665 := bbase (se 2 (by rfl) ⟨279249, by rfl⟩ : syracuseStep 744665 = 558499) (by norm_num)
theorem B1629517 : Blo 642303 1629517 := bbase (se 3 (by rfl) ⟨305534, by rfl⟩ : syracuseStep 1629517 = 611069) (by norm_num)
theorem B1105301 : Blo 642303 1105301 := bbase (se 6 (by rfl) ⟨25905, by rfl⟩ : syracuseStep 1105301 = 51811) (by norm_num)
theorem B1629629 : Blo 642303 1629629 := bbase (se 3 (by rfl) ⟨305555, by rfl⟩ : syracuseStep 1629629 = 611111) (by norm_num)
theorem B1629821 : Blo 642303 1629821 := bbase (se 3 (by rfl) ⟨305591, by rfl⟩ : syracuseStep 1629821 = 611183) (by norm_num)
theorem B2449061 : Blo 642303 2449061 := bbase (se 4 (by rfl) ⟨229599, by rfl⟩ : syracuseStep 2449061 = 459199) (by norm_num)
theorem B2088629 : Blo 642303 2088629 := bbase (se 5 (by rfl) ⟨97904, by rfl⟩ : syracuseStep 2088629 = 195809) (by norm_num)
theorem B4185877 : Blo 642303 4185877 := bbase (se 6 (by rfl) ⟨98106, by rfl⟩ : syracuseStep 4185877 = 196213) (by norm_num)
theorem B3137381 : Blo 642303 3137381 := bbase (se 4 (by rfl) ⟨294129, by rfl⟩ : syracuseStep 3137381 = 588259) (by norm_num)
theorem B2449349 : Blo 642303 2449349 := bbase (se 4 (by rfl) ⟨229626, by rfl⟩ : syracuseStep 2449349 = 459253) (by norm_num)
theorem B1630165 : Blo 642303 1630165 := bbase (se 7 (by rfl) ⟨19103, by rfl⟩ : syracuseStep 1630165 = 38207) (by norm_num)
theorem B5496821 : Blo 642303 5496821 := bbase (se 5 (by rfl) ⟨257663, by rfl⟩ : syracuseStep 5496821 = 515327) (by norm_num)
theorem B1630277 : Blo 642303 1630277 := bbase (se 4 (by rfl) ⟨152838, by rfl⟩ : syracuseStep 1630277 = 305677) (by norm_num)
theorem B1401013 : Blo 642303 1401013 := bbase (se 5 (by rfl) ⟨65672, by rfl⟩ : syracuseStep 1401013 = 131345) (by norm_num)
theorem B2744549 : Blo 642303 2744549 := bbase (se 4 (by rfl) ⟨257301, by rfl⟩ : syracuseStep 2744549 = 514603) (by norm_num)
theorem B2318597 : Blo 642303 2318597 := bbase (se 4 (by rfl) ⟨217368, by rfl⟩ : syracuseStep 2318597 = 434737) (by norm_num)
theorem B1630469 : Blo 642303 1630469 := bbase (se 4 (by rfl) ⟨152856, by rfl⟩ : syracuseStep 1630469 = 305713) (by norm_num)
theorem B3268997 : Blo 642303 3268997 := bbase (se 4 (by rfl) ⟨306468, by rfl⟩ : syracuseStep 3268997 = 612937) (by norm_num)
theorem B2482741 : Blo 642303 2482741 := bbase (se 5 (by rfl) ⟨116378, by rfl⟩ : syracuseStep 2482741 = 232757) (by norm_num)
theorem B1630813 : Blo 642303 1630813 := bbase (se 3 (by rfl) ⟨305777, by rfl⟩ : syracuseStep 1630813 = 611555) (by norm_num)
theorem B1303141 : Blo 642303 1303141 := bbase (se 4 (by rfl) ⟨122169, by rfl⟩ : syracuseStep 1303141 = 244339) (by norm_num)
theorem B1630925 : Blo 642303 1630925 := bbase (se 3 (by rfl) ⟨305798, by rfl⟩ : syracuseStep 1630925 = 611597) (by norm_num)
theorem B1631117 : Blo 642303 1631117 := bbase (se 3 (by rfl) ⟨305834, by rfl⟩ : syracuseStep 1631117 = 611669) (by norm_num)
theorem B2450533 : Blo 642303 2450533 := bbase (se 4 (by rfl) ⟨229737, by rfl⟩ : syracuseStep 2450533 = 459475) (by norm_num)
theorem B1631461 : Blo 642303 1631461 := bbase (se 4 (by rfl) ⟨152949, by rfl⟩ : syracuseStep 1631461 = 305899) (by norm_num)
theorem B1631573 : Blo 642303 1631573 := bbase (se 12 (by rfl) ⟨597, by rfl⟩ : syracuseStep 1631573 = 1195) (by norm_num)
theorem B1467749 : Blo 642303 1467749 := bbase (se 4 (by rfl) ⟨137601, by rfl⟩ : syracuseStep 1467749 = 275203) (by norm_num)
theorem B2450837 : Blo 642303 2450837 := bbase (se 6 (by rfl) ⟨57441, by rfl⟩ : syracuseStep 2450837 = 114883) (by norm_num)
theorem B1467821 : Blo 642303 1467821 := bbase (se 3 (by rfl) ⟨275216, by rfl⟩ : syracuseStep 1467821 = 550433) (by norm_num)
theorem B1631765 : Blo 642303 1631765 := bbase (se 6 (by rfl) ⟨38244, by rfl⟩ : syracuseStep 1631765 = 76489) (by norm_num)
theorem B23881301 : Blo 642303 23881301 := bbase (se 8 (by rfl) ⟨139929, by rfl⟩ : syracuseStep 23881301 = 279859) (by norm_num)
theorem B6186613 : Blo 642303 6186613 := bbase (se 5 (by rfl) ⟨289997, by rfl⟩ : syracuseStep 6186613 = 579995) (by norm_num)
theorem B3270293 : Blo 642303 3270293 := bbase (se 6 (by rfl) ⟨76647, by rfl⟩ : syracuseStep 3270293 = 153295) (by norm_num)
theorem B4187861 : Blo 642303 4187861 := bbase (se 7 (by rfl) ⟨49076, by rfl⟩ : syracuseStep 4187861 = 98153) (by norm_num)
theorem B1632109 : Blo 642303 1632109 := bbase (se 3 (by rfl) ⟨306020, by rfl⟩ : syracuseStep 1632109 = 612041) (by norm_num)
theorem B2746325 : Blo 642303 2746325 := bbase (se 7 (by rfl) ⟨32183, by rfl⟩ : syracuseStep 2746325 = 64367) (by norm_num)
theorem B813017 : Blo 642303 813017 := bbase (se 2 (by rfl) ⟨304881, by rfl⟩ : syracuseStep 813017 = 609763) (by norm_num)
theorem B1632221 : Blo 642303 1632221 := bbase (se 3 (by rfl) ⟨306041, by rfl⟩ : syracuseStep 1632221 = 612083) (by norm_num)
theorem B1468405 : Blo 642303 1468405 := bbase (se 5 (by rfl) ⟨68831, by rfl⟩ : syracuseStep 1468405 = 137663) (by norm_num)
theorem B813073 : Blo 642303 813073 := bbase (se 2 (by rfl) ⟨304902, by rfl⟩ : syracuseStep 813073 = 609805) (by norm_num)
theorem B813169 : Blo 642303 813169 := bbase (se 2 (by rfl) ⟨304938, by rfl⟩ : syracuseStep 813169 = 609877) (by norm_num)
theorem B2615429 : Blo 642303 2615429 := bbase (se 4 (by rfl) ⟨245196, by rfl⟩ : syracuseStep 2615429 = 490393) (by norm_num)
theorem B2943125 : Blo 642303 2943125 := bbase (se 6 (by rfl) ⟨68979, by rfl⟩ : syracuseStep 2943125 = 137959) (by norm_num)
theorem B1632413 : Blo 642303 1632413 := bbase (se 3 (by rfl) ⟨306077, by rfl⟩ : syracuseStep 1632413 = 612155) (by norm_num)
theorem B1173685 : Blo 642303 1173685 := bbase (se 5 (by rfl) ⟨55016, by rfl⟩ : syracuseStep 1173685 = 110033) (by norm_num)
theorem B1173773 : Blo 642303 1173773 := bbase (se 3 (by rfl) ⟨220082, by rfl⟩ : syracuseStep 1173773 = 440165) (by norm_num)
theorem B813341 : Blo 642303 813341 := bbase (se 3 (by rfl) ⟨152501, by rfl⟩ : syracuseStep 813341 = 305003) (by norm_num)
theorem B813397 : Blo 642303 813397 := bbase (se 10 (by rfl) ⟨1191, by rfl⟩ : syracuseStep 813397 = 2383) (by norm_num)
theorem B813493 : Blo 642303 813493 := bbase (se 5 (by rfl) ⟨38132, by rfl⟩ : syracuseStep 813493 = 76265) (by norm_num)
theorem B1632757 : Blo 642303 1632757 := bbase (se 5 (by rfl) ⟨76535, by rfl⟩ : syracuseStep 1632757 = 153071) (by norm_num)
theorem B3926549 : Blo 642303 3926549 := bbase (se 6 (by rfl) ⟨92028, by rfl⟩ : syracuseStep 3926549 = 184057) (by norm_num)
theorem B813665 : Blo 642303 813665 := bbase (se 2 (by rfl) ⟨305124, by rfl⟩ : syracuseStep 813665 = 610249) (by norm_num)
theorem B1632869 : Blo 642303 1632869 := bbase (se 4 (by rfl) ⟨153081, by rfl⟩ : syracuseStep 1632869 = 306163) (by norm_num)
theorem B813721 : Blo 642303 813721 := bbase (se 2 (by rfl) ⟨305145, by rfl⟩ : syracuseStep 813721 = 610291) (by norm_num)
theorem B1174181 : Blo 642303 1174181 := bbase (se 4 (by rfl) ⟨110079, by rfl⟩ : syracuseStep 1174181 = 220159) (by norm_num)
theorem B813817 : Blo 642303 813817 := bbase (se 2 (by rfl) ⟨305181, by rfl⟩ : syracuseStep 813817 = 610363) (by norm_num)
theorem B1633061 : Blo 642303 1633061 := bbase (se 4 (by rfl) ⟨153099, by rfl⟩ : syracuseStep 1633061 = 306199) (by norm_num)
theorem B1567565 : Blo 642303 1567565 := bbase (se 3 (by rfl) ⟨293918, by rfl⟩ : syracuseStep 1567565 = 587837) (by norm_num)
theorem B813989 : Blo 642303 813989 := bbase (se 4 (by rfl) ⟨76311, by rfl⟩ : syracuseStep 813989 = 152623) (by norm_num)
theorem B3271589 : Blo 642303 3271589 := bbase (se 4 (by rfl) ⟨306711, by rfl⟩ : syracuseStep 3271589 = 613423) (by norm_num)
theorem B2747317 : Blo 642303 2747317 := bbase (se 5 (by rfl) ⟨128780, by rfl⟩ : syracuseStep 2747317 = 257561) (by norm_num)
theorem B814045 : Blo 642303 814045 := bbase (se 3 (by rfl) ⟨152633, by rfl⟩ : syracuseStep 814045 = 305267) (by norm_num)
theorem B814141 : Blo 642303 814141 := bbase (se 3 (by rfl) ⟨152651, by rfl⟩ : syracuseStep 814141 = 305303) (by norm_num)
theorem B1633405 : Blo 642303 1633405 := bbase (se 3 (by rfl) ⟨306263, by rfl⟩ : syracuseStep 1633405 = 612527) (by norm_num)
theorem B1830053 : Blo 642303 1830053 := bbase (se 4 (by rfl) ⟨171567, by rfl⟩ : syracuseStep 1830053 = 343135) (by norm_num)
theorem B2616533 : Blo 642303 2616533 := bbase (se 7 (by rfl) ⟨30662, by rfl⟩ : syracuseStep 2616533 = 61325) (by norm_num)
theorem B814313 : Blo 642303 814313 := bbase (se 2 (by rfl) ⟨305367, by rfl⟩ : syracuseStep 814313 = 610735) (by norm_num)
theorem B1633517 : Blo 642303 1633517 := bbase (se 3 (by rfl) ⟨306284, by rfl⟩ : syracuseStep 1633517 = 612569) (by norm_num)
theorem B814369 : Blo 642303 814369 := bbase (se 2 (by rfl) ⟨305388, by rfl⟩ : syracuseStep 814369 = 610777) (by norm_num)
theorem B814465 : Blo 642303 814465 := bbase (se 2 (by rfl) ⟨305424, by rfl⟩ : syracuseStep 814465 = 610849) (by norm_num)
theorem B7925141 : Blo 642303 7925141 := bbase (se 6 (by rfl) ⟨185745, by rfl⟩ : syracuseStep 7925141 = 371491) (by norm_num)
theorem B2616725 : Blo 642303 2616725 := bbase (se 6 (by rfl) ⟨61329, by rfl⟩ : syracuseStep 2616725 = 122659) (by norm_num)
theorem B1043885 : Blo 642303 1043885 := bbase (se 3 (by rfl) ⟨195728, by rfl⟩ : syracuseStep 1043885 = 391457) (by norm_num)
theorem B1633709 : Blo 642303 1633709 := bbase (se 3 (by rfl) ⟨306320, by rfl⟩ : syracuseStep 1633709 = 612641) (by norm_num)
theorem B2452949 : Blo 642303 2452949 := bbase (se 7 (by rfl) ⟨28745, by rfl⟩ : syracuseStep 2452949 = 57491) (by norm_num)
theorem B2321941 : Blo 642303 2321941 := bbase (se 6 (by rfl) ⟨54420, by rfl⟩ : syracuseStep 2321941 = 108841) (by norm_num)
theorem B814637 : Blo 642303 814637 := bbase (se 3 (by rfl) ⟨152744, by rfl⟩ : syracuseStep 814637 = 305489) (by norm_num)
theorem B814693 : Blo 642303 814693 := bbase (se 4 (by rfl) ⟨76377, by rfl⟩ : syracuseStep 814693 = 152755) (by norm_num)
theorem B814789 : Blo 642303 814789 := bbase (se 4 (by rfl) ⟨76386, by rfl⟩ : syracuseStep 814789 = 152773) (by norm_num)
theorem B2453237 : Blo 642303 2453237 := bbase (se 5 (by rfl) ⟨114995, by rfl⟩ : syracuseStep 2453237 = 229991) (by norm_num)
theorem B1634053 : Blo 642303 1634053 := bbase (se 4 (by rfl) ⟨153192, by rfl⟩ : syracuseStep 1634053 = 306385) (by norm_num)
theorem B1830725 : Blo 642303 1830725 := bbase (se 4 (by rfl) ⟨171630, by rfl⟩ : syracuseStep 1830725 = 343261) (by norm_num)
theorem B814961 : Blo 642303 814961 := bbase (se 2 (by rfl) ⟨305610, by rfl⟩ : syracuseStep 814961 = 611221) (by norm_num)
theorem B1634165 : Blo 642303 1634165 := bbase (se 5 (by rfl) ⟨76601, by rfl⟩ : syracuseStep 1634165 = 153203) (by norm_num)
theorem B651173 : Blo 642303 651173 := bbase (se 4 (by rfl) ⟨61047, by rfl⟩ : syracuseStep 651173 = 122095) (by norm_num)
theorem B1372069 : Blo 642303 1372069 := bbase (se 4 (by rfl) ⟨128631, by rfl⟩ : syracuseStep 1372069 = 257263) (by norm_num)
theorem B815017 : Blo 642303 815017 := bbase (se 2 (by rfl) ⟨305631, by rfl⟩ : syracuseStep 815017 = 611263) (by norm_num)
theorem B2060245 : Blo 642303 2060245 := bbase (se 7 (by rfl) ⟨24143, by rfl⟩ : syracuseStep 2060245 = 48287) (by norm_num)
theorem B2322389 : Blo 642303 2322389 := bbase (se 7 (by rfl) ⟨27215, by rfl⟩ : syracuseStep 2322389 = 54431) (by norm_num)
theorem B815113 : Blo 642303 815113 := bbase (se 2 (by rfl) ⟨305667, by rfl⟩ : syracuseStep 815113 = 611335) (by norm_num)
theorem B2060309 : Blo 642303 2060309 := bbase (se 6 (by rfl) ⟨48288, by rfl⟩ : syracuseStep 2060309 = 96577) (by norm_num)
theorem B1634357 : Blo 642303 1634357 := bbase (se 5 (by rfl) ⟨76610, by rfl⟩ : syracuseStep 1634357 = 153221) (by norm_num)
theorem B3666005 : Blo 642303 3666005 := bbase (se 8 (by rfl) ⟨21480, by rfl⟩ : syracuseStep 3666005 = 42961) (by norm_num)
theorem B2650229 : Blo 642303 2650229 := bbase (se 5 (by rfl) ⟨124229, by rfl⟩ : syracuseStep 2650229 = 248459) (by norm_num)
theorem B815285 : Blo 642303 815285 := bbase (se 5 (by rfl) ⟨38216, by rfl⟩ : syracuseStep 815285 = 76433) (by norm_num)
theorem B815341 : Blo 642303 815341 := bbase (se 3 (by rfl) ⟨152876, by rfl⟩ : syracuseStep 815341 = 305753) (by norm_num)
theorem B1831157 : Blo 642303 1831157 := bbase (se 5 (by rfl) ⟨85835, by rfl⟩ : syracuseStep 1831157 = 171671) (by norm_num)
theorem B815437 : Blo 642303 815437 := bbase (se 3 (by rfl) ⟨152894, by rfl⟩ : syracuseStep 815437 = 305789) (by norm_num)
theorem B1634701 : Blo 642303 1634701 := bbase (se 3 (by rfl) ⟨306506, by rfl⟩ : syracuseStep 1634701 = 613013) (by norm_num)
theorem B1372565 : Blo 642303 1372565 := bbase (se 6 (by rfl) ⟨32169, by rfl⟩ : syracuseStep 1372565 = 64339) (by norm_num)
theorem B4125077 : Blo 642303 4125077 := bbase (se 6 (by rfl) ⟨96681, by rfl⟩ : syracuseStep 4125077 = 193363) (by norm_num)
theorem B815609 : Blo 642303 815609 := bbase (se 2 (by rfl) ⟨305853, by rfl⟩ : syracuseStep 815609 = 611707) (by norm_num)
theorem B1634813 : Blo 642303 1634813 := bbase (se 3 (by rfl) ⟨306527, by rfl⟩ : syracuseStep 1634813 = 613055) (by norm_num)
theorem B1470997 : Blo 642303 1470997 := bbase (se 6 (by rfl) ⟨34476, by rfl⟩ : syracuseStep 1470997 = 68953) (by norm_num)
theorem B815665 : Blo 642303 815665 := bbase (se 2 (by rfl) ⟨305874, by rfl⟩ : syracuseStep 815665 = 611749) (by norm_num)
theorem B815761 : Blo 642303 815761 := bbase (se 2 (by rfl) ⟨305910, by rfl⟩ : syracuseStep 815761 = 611821) (by norm_num)
theorem B1635005 : Blo 642303 1635005 := bbase (se 3 (by rfl) ⟨306563, by rfl⟩ : syracuseStep 1635005 = 613127) (by norm_num)
theorem B815933 : Blo 642303 815933 := bbase (se 3 (by rfl) ⟨152987, by rfl⟩ : syracuseStep 815933 = 305975) (by norm_num)
theorem B815989 : Blo 642303 815989 := bbase (se 5 (by rfl) ⟨38249, by rfl⟩ : syracuseStep 815989 = 76499) (by norm_num)
theorem B816085 : Blo 642303 816085 := bbase (se 7 (by rfl) ⟨9563, by rfl⟩ : syracuseStep 816085 = 19127) (by norm_num)
theorem B1831909 : Blo 642303 1831909 := bbase (se 4 (by rfl) ⟨171741, by rfl⟩ : syracuseStep 1831909 = 343483) (by norm_num)
theorem B1635349 : Blo 642303 1635349 := bbase (se 6 (by rfl) ⟨38328, by rfl⟩ : syracuseStep 1635349 = 76657) (by norm_num)
theorem B816257 : Blo 642303 816257 := bbase (se 2 (by rfl) ⟨306096, by rfl⟩ : syracuseStep 816257 = 612193) (by norm_num)
theorem B1635461 : Blo 642303 1635461 := bbase (se 4 (by rfl) ⟨153324, by rfl⟩ : syracuseStep 1635461 = 306649) (by norm_num)
theorem B816313 : Blo 642303 816313 := bbase (se 2 (by rfl) ⟨306117, by rfl⟩ : syracuseStep 816313 = 612235) (by norm_num)
theorem B1471709 : Blo 642303 1471709 := bbase (se 3 (by rfl) ⟨275945, by rfl⟩ : syracuseStep 1471709 = 551891) (by norm_num)
theorem B1373429 : Blo 642303 1373429 := bbase (se 5 (by rfl) ⟨64379, by rfl⟩ : syracuseStep 1373429 = 128759) (by norm_num)
theorem B816409 : Blo 642303 816409 := bbase (se 2 (by rfl) ⟨306153, by rfl⟩ : syracuseStep 816409 = 612307) (by norm_num)
theorem B1635653 : Blo 642303 1635653 := bbase (se 4 (by rfl) ⟨153342, by rfl⟩ : syracuseStep 1635653 = 306685) (by norm_num)
theorem B1373573 : Blo 642303 1373573 := bbase (se 4 (by rfl) ⟨128772, by rfl⟩ : syracuseStep 1373573 = 257545) (by norm_num)
theorem B914861 : Blo 642303 914861 := bbase (se 3 (by rfl) ⟨171536, by rfl⟩ : syracuseStep 914861 = 343073) (by norm_num)
theorem B816581 : Blo 642303 816581 := bbase (se 4 (by rfl) ⟨76554, by rfl⟩ : syracuseStep 816581 = 153109) (by norm_num)
theorem B816637 : Blo 642303 816637 := bbase (se 3 (by rfl) ⟨153119, by rfl⟩ : syracuseStep 816637 = 306239) (by norm_num)
theorem B6190613 : Blo 642303 6190613 := bbase (se 6 (by rfl) ⟨145092, by rfl⟩ : syracuseStep 6190613 = 290185) (by norm_num)
theorem B4879925 : Blo 642303 4879925 := bbase (se 5 (by rfl) ⟨228746, by rfl⟩ : syracuseStep 4879925 = 457493) (by norm_num)
theorem B816733 : Blo 642303 816733 := bbase (se 3 (by rfl) ⟨153137, by rfl⟩ : syracuseStep 816733 = 306275) (by norm_num)
theorem B783977 : Blo 642303 783977 := bbase (se 2 (by rfl) ⟨293991, by rfl⟩ : syracuseStep 783977 = 587983) (by norm_num)
theorem B2291381 : Blo 642303 2291381 := bbase (se 5 (by rfl) ⟨107408, by rfl⟩ : syracuseStep 2291381 = 214817) (by norm_num)
theorem B6715061 : Blo 642303 6715061 := bbase (se 5 (by rfl) ⟨314768, by rfl⟩ : syracuseStep 6715061 = 629537) (by norm_num)
theorem B816905 : Blo 642303 816905 := bbase (se 2 (by rfl) ⟨306339, by rfl⟩ : syracuseStep 816905 = 612679) (by norm_num)
theorem B816961 : Blo 642303 816961 := bbase (se 2 (by rfl) ⟨306360, by rfl⟩ : syracuseStep 816961 = 612721) (by norm_num)
theorem B817057 : Blo 642303 817057 := bbase (se 2 (by rfl) ⟨306396, by rfl⟩ : syracuseStep 817057 = 612793) (by norm_num)
theorem B653249 : Blo 642303 653249 := bbase (se 2 (by rfl) ⟨244968, by rfl⟩ : syracuseStep 653249 = 489937) (by norm_num)
theorem B980957 : Blo 642303 980957 := bbase (se 3 (by rfl) ⟨183929, by rfl⟩ : syracuseStep 980957 = 367859) (by norm_num)
theorem B686065 : Blo 642303 686065 := bbase (se 2 (by rfl) ⟨257274, by rfl⟩ : syracuseStep 686065 = 514549) (by norm_num)
theorem B1964101 : Blo 642303 1964101 := bbase (se 4 (by rfl) ⟨184134, by rfl⟩ : syracuseStep 1964101 = 368269) (by norm_num)
theorem B817229 : Blo 642303 817229 := bbase (se 3 (by rfl) ⟨153230, by rfl⟩ : syracuseStep 817229 = 306461) (by norm_num)
theorem B1374317 : Blo 642303 1374317 := bbase (se 3 (by rfl) ⟨257684, by rfl⟩ : syracuseStep 1374317 = 515369) (by norm_num)
theorem B4421749 : Blo 642303 4421749 := bbase (se 5 (by rfl) ⟨207269, by rfl⟩ : syracuseStep 4421749 = 414539) (by norm_num)
theorem B817285 : Blo 642303 817285 := bbase (se 4 (by rfl) ⟨76620, by rfl⟩ : syracuseStep 817285 = 153241) (by norm_num)
theorem B653509 : Blo 642303 653509 := bbase (se 4 (by rfl) ⟨61266, by rfl⟩ : syracuseStep 653509 = 122533) (by norm_num)
theorem B817381 : Blo 642303 817381 := bbase (se 4 (by rfl) ⟨76629, by rfl⟩ : syracuseStep 817381 = 153259) (by norm_num)
theorem B1046885 : Blo 642303 1046885 := bbase (se 4 (by rfl) ⟨98145, by rfl⟩ : syracuseStep 1046885 = 196291) (by norm_num)
theorem B686441 : Blo 642303 686441 := bbase (se 2 (by rfl) ⟨257415, by rfl⟩ : syracuseStep 686441 = 514831) (by norm_num)
theorem B817553 : Blo 642303 817553 := bbase (se 2 (by rfl) ⟨306582, by rfl⟩ : syracuseStep 817553 = 613165) (by norm_num)
theorem B686513 : Blo 642303 686513 := bbase (se 2 (by rfl) ⟨257442, by rfl⟩ : syracuseStep 686513 = 514885) (by norm_num)
theorem B817609 : Blo 642303 817609 := bbase (se 2 (by rfl) ⟨306603, by rfl⟩ : syracuseStep 817609 = 613207) (by norm_num)
theorem B817705 : Blo 642303 817705 := bbase (se 2 (by rfl) ⟨306639, by rfl⟩ : syracuseStep 817705 = 613279) (by norm_num)
theorem B2652725 : Blo 642303 2652725 := bbase (se 5 (by rfl) ⟨124346, by rfl⟩ : syracuseStep 2652725 = 248693) (by norm_num)
theorem B686701 : Blo 642303 686701 := bbase (se 3 (by rfl) ⟨128756, by rfl⟩ : syracuseStep 686701 = 257513) (by norm_num)
theorem B981613 : Blo 642303 981613 := bbase (se 3 (by rfl) ⟨184052, by rfl⟩ : syracuseStep 981613 = 368105) (by norm_num)
theorem B817877 : Blo 642303 817877 := bbase (se 7 (by rfl) ⟨9584, by rfl⟩ : syracuseStep 817877 = 19169) (by norm_num)
theorem B817933 : Blo 642303 817933 := bbase (se 3 (by rfl) ⟨153362, by rfl⟩ : syracuseStep 817933 = 306725) (by norm_num)
theorem B1178389 : Blo 642303 1178389 := bbase (se 6 (by rfl) ⟨27618, by rfl⟩ : syracuseStep 1178389 = 55237) (by norm_num)
theorem B686885 : Blo 642303 686885 := bbase (se 4 (by rfl) ⟨64395, by rfl⟩ : syracuseStep 686885 = 128791) (by norm_num)
theorem B916285 : Blo 642303 916285 := bbase (se 3 (by rfl) ⟨171803, by rfl⟩ : syracuseStep 916285 = 343607) (by norm_num)
theorem B981821 : Blo 642303 981821 := bbase (se 3 (by rfl) ⟨184091, by rfl⟩ : syracuseStep 981821 = 368183) (by norm_num)
theorem B1375069 : Blo 642303 1375069 := bbase (se 3 (by rfl) ⟨257825, by rfl⟩ : syracuseStep 1375069 = 515651) (by norm_num)
theorem B785281 : Blo 642303 785281 := bbase (se 2 (by rfl) ⟨294480, by rfl⟩ : syracuseStep 785281 = 588961) (by norm_num)
theorem B2063333 : Blo 642303 2063333 := bbase (se 4 (by rfl) ⟨193437, by rfl⟩ : syracuseStep 2063333 = 386875) (by norm_num)
theorem B1375213 : Blo 642303 1375213 := bbase (se 3 (by rfl) ⟨257852, by rfl⟩ : syracuseStep 1375213 = 515705) (by norm_num)
theorem B1965269 : Blo 642303 1965269 := bbase (se 7 (by rfl) ⟨23030, by rfl⟩ : syracuseStep 1965269 = 46061) (by norm_num)
theorem B1375589 : Blo 642303 1375589 := bbase (se 4 (by rfl) ⟨128961, by rfl⟩ : syracuseStep 1375589 = 257923) (by norm_num)
theorem B916877 : Blo 642303 916877 := bbase (se 3 (by rfl) ⟨171914, by rfl⟩ : syracuseStep 916877 = 343829) (by norm_num)
theorem B916957 : Blo 642303 916957 := bbase (se 3 (by rfl) ⟨171929, by rfl⟩ : syracuseStep 916957 = 343859) (by norm_num)
theorem B687637 : Blo 642303 687637 := bbase (se 6 (by rfl) ⟨16116, by rfl⟩ : syracuseStep 687637 = 32233) (by norm_num)
theorem B917077 : Blo 642303 917077 := bbase (se 8 (by rfl) ⟨5373, by rfl⟩ : syracuseStep 917077 = 10747) (by norm_num)
theorem B687709 : Blo 642303 687709 := bbase (se 3 (by rfl) ⟨128945, by rfl⟩ : syracuseStep 687709 = 257891) (by norm_num)
theorem B917173 : Blo 642303 917173 := bbase (se 5 (by rfl) ⟨42992, by rfl⟩ : syracuseStep 917173 = 85985) (by norm_num)
theorem B1375957 : Blo 642303 1375957 := bbase (se 7 (by rfl) ⟨16124, by rfl⟩ : syracuseStep 1375957 = 32249) (by norm_num)
theorem B1834757 : Blo 642303 1834757 := bbase (se 4 (by rfl) ⟨172008, by rfl⟩ : syracuseStep 1834757 = 344017) (by norm_num)
theorem B687889 : Blo 642303 687889 := bbase (se 2 (by rfl) ⟨257958, by rfl⟩ : syracuseStep 687889 = 515917) (by norm_num)
theorem B2752325 : Blo 642303 2752325 := bbase (se 4 (by rfl) ⟨258030, by rfl⟩ : syracuseStep 2752325 = 516061) (by norm_num)
theorem B1376273 : Blo 642303 1376273 := bstep (se 2 (by rfl) ⟨516102, by rfl⟩ : syracuseStep 1376273 = 1032205) B1032205
theorem B1048627 : Blo 642303 1048627 := bstep (se 1 (by rfl) ⟨786470, by rfl⟩ : syracuseStep 1048627 = 1572941) B1572941
theorem B1835075 : Blo 642303 1835075 := bstep (se 1 (by rfl) ⟨1376306, by rfl⟩ : syracuseStep 1835075 = 2752613) B2752613
theorem B1868017 : Blo 642303 1868017 := bstep (se 2 (by rfl) ⟨700506, by rfl⟩ : syracuseStep 1868017 = 1401013) B1401013
theorem B917777 : Blo 642303 917777 := bstep (se 2 (by rfl) ⟨344166, by rfl⟩ : syracuseStep 917777 = 688333) B688333
theorem B1769777 : Blo 642303 1769777 := bstep (se 2 (by rfl) ⟨663666, by rfl⟩ : syracuseStep 1769777 = 1327333) B1327333
theorem B9929101 : Blo 642303 9929101 := bstep (se 3 (by rfl) ⟨1861706, by rfl⟩ : syracuseStep 9929101 = 3723413) B3723413
theorem B1180145 : Blo 642303 1180145 := bstep (se 2 (by rfl) ⟨442554, by rfl⟩ : syracuseStep 1180145 = 885109) B885109
theorem B1376785 : Blo 642303 1376785 := bstep (se 2 (by rfl) ⟨516294, by rfl⟩ : syracuseStep 1376785 = 1032589) B1032589
theorem B2327075 : Blo 642303 2327075 := bstep (se 1 (by rfl) ⟨1745306, by rfl⟩ : syracuseStep 2327075 = 3490613) B3490613
theorem B9306677 : Blo 642303 9306677 := bstep (se 5 (by rfl) ⟨436250, by rfl⟩ : syracuseStep 9306677 = 872501) B872501
theorem B2064973 : Blo 642303 2064973 := bstep (se 3 (by rfl) ⟨387182, by rfl⟩ : syracuseStep 2064973 = 774365) B774365
theorem B7078499 : Blo 642303 7078499 := bstep (se 1 (by rfl) ⟨5308874, by rfl⟩ : syracuseStep 7078499 = 10617749) B10617749
theorem B1180259 : Blo 642303 1180259 := bstep (se 1 (by rfl) ⟨885194, by rfl⟩ : syracuseStep 1180259 = 1770389) B1770389
theorem B13075085 : Blo 642303 13075085 := bstep (se 3 (by rfl) ⟨2451578, by rfl⟩ : syracuseStep 13075085 = 4903157) B4903157
theorem B3310321 : Blo 642303 3310321 := bstep (se 2 (by rfl) ⟨1241370, by rfl⟩ : syracuseStep 3310321 = 2482741) B2482741
theorem B918307 : Blo 642303 918307 := bstep (se 1 (by rfl) ⟨688730, by rfl⟩ : syracuseStep 918307 = 1377461) B1377461
theorem B1737521 : Blo 642303 1737521 := bstep (se 2 (by rfl) ⟨651570, by rfl⟩ : syracuseStep 1737521 = 1303141) B1303141
theorem B1835885 : Blo 642303 1835885 := bstep (se 3 (by rfl) ⟨344228, by rfl⟩ : syracuseStep 1835885 = 688457) B688457
theorem B1409905 : Blo 642303 1409905 := bstep (se 2 (by rfl) ⟨528714, by rfl⟩ : syracuseStep 1409905 = 1057429) B1057429
theorem B5309297 : Blo 642303 5309297 := bstep (se 2 (by rfl) ⟨1990986, by rfl⟩ : syracuseStep 5309297 = 3981973) B3981973
theorem B19104709 : Blo 642303 19104709 := bstep (se 4 (by rfl) ⟨1791066, by rfl⟩ : syracuseStep 19104709 = 3582133) B3582133
theorem B1836067 : Blo 642303 1836067 := bstep (se 1 (by rfl) ⟨1377050, by rfl⟩ : syracuseStep 1836067 = 2754101) B2754101
theorem B3671153 : Blo 642303 3671153 := bstep (se 2 (by rfl) ⟨1376682, by rfl⟩ : syracuseStep 3671153 = 2753365) B2753365
theorem B918643 : Blo 642303 918643 := bstep (se 1 (by rfl) ⟨688982, by rfl⟩ : syracuseStep 918643 = 1377965) B1377965
theorem B689315 : Blo 642303 689315 := bstep (se 1 (by rfl) ⟨516986, by rfl⟩ : syracuseStep 689315 = 1033973) B1033973
theorem B9045233 : Blo 642303 9045233 := bstep (se 2 (by rfl) ⟨3391962, by rfl⟩ : syracuseStep 9045233 = 6783925) B6783925
theorem B1836557 : Blo 642303 1836557 := bstep (se 3 (by rfl) ⟨344354, by rfl⟩ : syracuseStep 1836557 = 688709) B688709
theorem B919201 : Blo 642303 919201 := bstep (se 2 (by rfl) ⟨344700, by rfl⟩ : syracuseStep 919201 = 689401) B689401
theorem B919235 : Blo 642303 919235 := bstep (se 1 (by rfl) ⟨689426, by rfl⟩ : syracuseStep 919235 = 1378853) B1378853
theorem B2754253 : Blo 642303 2754253 := bstep (se 3 (by rfl) ⟨516422, by rfl⟩ : syracuseStep 2754253 = 1032845) B1032845
theorem B722659 : Blo 642303 722659 := bstep (se 1 (by rfl) ⟨541994, by rfl⟩ : syracuseStep 722659 = 1083989) B1083989
theorem B722803 : Blo 642303 722803 := bstep (se 1 (by rfl) ⟨542102, by rfl⟩ : syracuseStep 722803 = 1084205) B1084205
theorem B690067 : Blo 642303 690067 := bstep (se 1 (by rfl) ⟨517550, by rfl⟩ : syracuseStep 690067 = 1035101) B1035101
theorem B1378289 : Blo 642303 1378289 := bstep (se 2 (by rfl) ⟨516858, by rfl⟩ : syracuseStep 1378289 = 1033717) B1033717
theorem B722947 : Blo 642303 722947 := bstep (se 1 (by rfl) ⟨542210, by rfl⟩ : syracuseStep 722947 = 1084421) B1084421
theorem B2066435 : Blo 642303 2066435 := bstep (se 1 (by rfl) ⟨1549826, by rfl⟩ : syracuseStep 2066435 = 3099653) B3099653
theorem B2328689 : Blo 642303 2328689 := bstep (se 2 (by rfl) ⟨873258, by rfl⟩ : syracuseStep 2328689 = 1746517) B1746517
theorem B723091 : Blo 642303 723091 := bstep (se 1 (by rfl) ⟨542318, by rfl⟩ : syracuseStep 723091 = 1084637) B1084637
theorem B7833827 : Blo 642303 7833827 := bstep (se 1 (by rfl) ⟨5875370, by rfl⟩ : syracuseStep 7833827 = 11750741) B11750741
theorem B919793 : Blo 642303 919793 := bstep (se 2 (by rfl) ⟨344922, by rfl⟩ : syracuseStep 919793 = 689845) B689845
theorem B2066705 : Blo 642303 2066705 := bstep (se 2 (by rfl) ⟨775014, by rfl⟩ : syracuseStep 2066705 = 1550029) B1550029
theorem B723235 : Blo 642303 723235 := bstep (se 1 (by rfl) ⟨542426, by rfl⟩ : syracuseStep 723235 = 1084853) B1084853
theorem B919873 : Blo 642303 919873 := bstep (se 2 (by rfl) ⟨344952, by rfl⟩ : syracuseStep 919873 = 689905) B689905
theorem B1378691 : Blo 642303 1378691 := bstep (se 1 (by rfl) ⟨1034018, by rfl⟩ : syracuseStep 1378691 = 2068037) B2068037
theorem B2197901 : Blo 642303 2197901 := bstep (se 3 (by rfl) ⟨412106, by rfl⟩ : syracuseStep 2197901 = 824213) B824213
theorem B723379 : Blo 642303 723379 := bstep (se 1 (by rfl) ⟨542534, by rfl⟩ : syracuseStep 723379 = 1085069) B1085069
theorem B3672611 : Blo 642303 3672611 := bstep (se 1 (by rfl) ⟨2754458, by rfl⟩ : syracuseStep 3672611 = 5508917) B5508917
theorem B1083955 : Blo 642303 1083955 := bstep (se 1 (by rfl) ⟨812966, by rfl⟩ : syracuseStep 1083955 = 1625933) B1625933
theorem B723523 : Blo 642303 723523 := bstep (se 1 (by rfl) ⟨542642, by rfl⟩ : syracuseStep 723523 = 1085285) B1085285
theorem B1837741 : Blo 642303 1837741 := bstep (se 3 (by rfl) ⟨344576, by rfl⟩ : syracuseStep 1837741 = 689153) B689153
theorem B1084097 : Blo 642303 1084097 := bstep (se 2 (by rfl) ⟨406536, by rfl⟩ : syracuseStep 1084097 = 813073) B813073
theorem B723667 : Blo 642303 723667 := bstep (se 1 (by rfl) ⟨542750, by rfl⟩ : syracuseStep 723667 = 1085501) B1085501
theorem B1084225 : Blo 642303 1084225 := bstep (se 2 (by rfl) ⟨406584, by rfl⟩ : syracuseStep 1084225 = 813169) B813169
theorem B1084259 : Blo 642303 1084259 := bstep (se 1 (by rfl) ⟨813194, by rfl⟩ : syracuseStep 1084259 = 1626389) B1626389
theorem B723811 : Blo 642303 723811 := bstep (se 1 (by rfl) ⟨542858, by rfl⟩ : syracuseStep 723811 = 1085717) B1085717
theorem B12356549 : Blo 642303 12356549 := bstep (se 4 (by rfl) ⟨1158426, by rfl⟩ : syracuseStep 12356549 = 2316853) B2316853
theorem B1084387 : Blo 642303 1084387 := bstep (se 1 (by rfl) ⟨813290, by rfl⟩ : syracuseStep 1084387 = 1626581) B1626581
theorem B723955 : Blo 642303 723955 := bstep (se 1 (by rfl) ⟨542966, by rfl⟩ : syracuseStep 723955 = 1085933) B1085933
theorem B1084529 : Blo 642303 1084529 := bstep (se 2 (by rfl) ⟨406698, by rfl⟩ : syracuseStep 1084529 = 813397) B813397
theorem B59477105 : Blo 642303 59477105 := bstep (se 2 (by rfl) ⟨22303914, by rfl⟩ : syracuseStep 59477105 = 44607829) B44607829
theorem B724099 : Blo 642303 724099 := bstep (se 1 (by rfl) ⟨543074, by rfl⟩ : syracuseStep 724099 = 1086149) B1086149
theorem B2198765 : Blo 642303 2198765 := bstep (se 3 (by rfl) ⟨412268, by rfl⟩ : syracuseStep 2198765 = 824537) B824537
theorem B1084657 : Blo 642303 1084657 := bstep (se 2 (by rfl) ⟨406746, by rfl⟩ : syracuseStep 1084657 = 813493) B813493
theorem B1379587 : Blo 642303 1379587 := bstep (se 1 (by rfl) ⟨1034690, by rfl⟩ : syracuseStep 1379587 = 2069381) B2069381
theorem B1084691 : Blo 642303 1084691 := bstep (se 1 (by rfl) ⟨813518, by rfl⟩ : syracuseStep 1084691 = 1627037) B1627037
theorem B724243 : Blo 642303 724243 := bstep (se 1 (by rfl) ⟨543182, by rfl⟩ : syracuseStep 724243 = 1086365) B1086365
theorem B1445201 : Blo 642303 1445201 := bstep (se 2 (by rfl) ⟨541950, by rfl⟩ : syracuseStep 1445201 = 1083901) B1083901
theorem B1445219 : Blo 642303 1445219 := bstep (se 1 (by rfl) ⟨1083914, by rfl⟩ : syracuseStep 1445219 = 2167829) B2167829
theorem B1084819 : Blo 642303 1084819 := bstep (se 1 (by rfl) ⟨813614, by rfl⟩ : syracuseStep 1084819 = 1627229) B1627229
theorem B724387 : Blo 642303 724387 := bstep (se 1 (by rfl) ⟨543290, by rfl⟩ : syracuseStep 724387 = 1086581) B1086581
theorem B3673613 : Blo 642303 3673613 := bstep (se 3 (by rfl) ⟨688802, by rfl⟩ : syracuseStep 3673613 = 1377605) B1377605
theorem B1084961 : Blo 642303 1084961 := bstep (se 2 (by rfl) ⟨406860, by rfl⟩ : syracuseStep 1084961 = 813721) B813721
theorem B724531 : Blo 642303 724531 := bstep (se 1 (by rfl) ⟨543398, by rfl⟩ : syracuseStep 724531 = 1086797) B1086797
theorem B1445489 : Blo 642303 1445489 := bstep (se 2 (by rfl) ⟨542058, by rfl⟩ : syracuseStep 1445489 = 1084117) B1084117
theorem B1445507 : Blo 642303 1445507 := bstep (se 1 (by rfl) ⟨1084130, by rfl⟩ : syracuseStep 1445507 = 2168261) B2168261
theorem B1085089 : Blo 642303 1085089 := bstep (se 2 (by rfl) ⟨406908, by rfl⟩ : syracuseStep 1085089 = 813817) B813817
theorem B1085123 : Blo 642303 1085123 := bstep (se 1 (by rfl) ⟨813842, by rfl⟩ : syracuseStep 1085123 = 1627685) B1627685
theorem B724675 : Blo 642303 724675 := bstep (se 1 (by rfl) ⟨543506, by rfl⟩ : syracuseStep 724675 = 1087013) B1087013
theorem B1838801 : Blo 642303 1838801 := bstep (se 2 (by rfl) ⟨689550, by rfl⟩ : syracuseStep 1838801 = 1379101) B1379101
theorem B4886243 : Blo 642303 4886243 := bstep (se 1 (by rfl) ⟨3664682, by rfl⟩ : syracuseStep 4886243 = 7329365) B7329365
theorem B1085251 : Blo 642303 1085251 := bstep (se 1 (by rfl) ⟨813938, by rfl⟩ : syracuseStep 1085251 = 1627877) B1627877
theorem B724819 : Blo 642303 724819 := bstep (se 1 (by rfl) ⟨543614, by rfl⟩ : syracuseStep 724819 = 1087229) B1087229
theorem B1445777 : Blo 642303 1445777 := bstep (se 2 (by rfl) ⟨542166, by rfl⟩ : syracuseStep 1445777 = 1084333) B1084333
theorem B1445795 : Blo 642303 1445795 := bstep (se 1 (by rfl) ⟨1084346, by rfl⟩ : syracuseStep 1445795 = 2168693) B2168693
theorem B1085393 : Blo 642303 1085393 := bstep (se 2 (by rfl) ⟨407022, by rfl⟩ : syracuseStep 1085393 = 814045) B814045
theorem B724963 : Blo 642303 724963 := bstep (se 1 (by rfl) ⟨543722, by rfl⟩ : syracuseStep 724963 = 1087445) B1087445
theorem B1085521 : Blo 642303 1085521 := bstep (se 2 (by rfl) ⟨407070, by rfl⟩ : syracuseStep 1085521 = 814141) B814141
theorem B1544291 : Blo 642303 1544291 := bstep (se 1 (by rfl) ⟨1158218, by rfl⟩ : syracuseStep 1544291 = 2316437) B2316437
theorem B1085555 : Blo 642303 1085555 := bstep (se 1 (by rfl) ⟨814166, by rfl⟩ : syracuseStep 1085555 = 1628333) B1628333
theorem B725107 : Blo 642303 725107 := bstep (se 1 (by rfl) ⟨543830, by rfl⟩ : syracuseStep 725107 = 1087661) B1087661
theorem B1446065 : Blo 642303 1446065 := bstep (se 2 (by rfl) ⟨542274, by rfl⟩ : syracuseStep 1446065 = 1084549) B1084549
theorem B1446083 : Blo 642303 1446083 := bstep (se 1 (by rfl) ⟨1084562, by rfl⟩ : syracuseStep 1446083 = 2169125) B2169125
theorem B1085683 : Blo 642303 1085683 := bstep (se 1 (by rfl) ⟨814262, by rfl⟩ : syracuseStep 1085683 = 1628525) B1628525
theorem B725251 : Blo 642303 725251 := bstep (se 1 (by rfl) ⟨543938, by rfl⟩ : syracuseStep 725251 = 1087877) B1087877
theorem B18583829 : Blo 642303 18583829 := bstep (se 6 (by rfl) ⟨435558, by rfl⟩ : syracuseStep 18583829 = 871117) B871117
theorem B3477809 : Blo 642303 3477809 := bstep (se 2 (by rfl) ⟨1304178, by rfl⟩ : syracuseStep 3477809 = 2608357) B2608357
theorem B1839473 : Blo 642303 1839473 := bstep (se 2 (by rfl) ⟨689802, by rfl⟩ : syracuseStep 1839473 = 1379605) B1379605
theorem B1085825 : Blo 642303 1085825 := bstep (se 2 (by rfl) ⟨407184, by rfl⟩ : syracuseStep 1085825 = 814369) B814369
theorem B1544579 : Blo 642303 1544579 := bstep (se 1 (by rfl) ⟨1158434, by rfl⟩ : syracuseStep 1544579 = 2316869) B2316869
theorem B725395 : Blo 642303 725395 := bstep (se 1 (by rfl) ⟨544046, by rfl⟩ : syracuseStep 725395 = 1088093) B1088093
theorem B1446353 : Blo 642303 1446353 := bstep (se 2 (by rfl) ⟨542382, by rfl⟩ : syracuseStep 1446353 = 1084765) B1084765
theorem B1446371 : Blo 642303 1446371 := bstep (se 1 (by rfl) ⟨1084778, by rfl⟩ : syracuseStep 1446371 = 2169557) B2169557
theorem B1085953 : Blo 642303 1085953 := bstep (se 2 (by rfl) ⟨407232, by rfl⟩ : syracuseStep 1085953 = 814465) B814465
theorem B1085987 : Blo 642303 1085987 := bstep (se 1 (by rfl) ⟨814490, by rfl⟩ : syracuseStep 1085987 = 1628981) B1628981
theorem B725539 : Blo 642303 725539 := bstep (se 1 (by rfl) ⟨544154, by rfl⟩ : syracuseStep 725539 = 1088309) B1088309
theorem B1544771 : Blo 642303 1544771 := bstep (se 1 (by rfl) ⟨1158578, by rfl⟩ : syracuseStep 1544771 = 2317157) B2317157
theorem B1086115 : Blo 642303 1086115 := bstep (se 1 (by rfl) ⟨814586, by rfl⟩ : syracuseStep 1086115 = 1629173) B1629173
theorem B2069165 : Blo 642303 2069165 := bstep (se 3 (by rfl) ⟨387968, by rfl⟩ : syracuseStep 2069165 = 775937) B775937
theorem B725683 : Blo 642303 725683 := bstep (se 1 (by rfl) ⟨544262, by rfl⟩ : syracuseStep 725683 = 1088525) B1088525
theorem B1446641 : Blo 642303 1446641 := bstep (se 2 (by rfl) ⟨542490, by rfl⟩ : syracuseStep 1446641 = 1084981) B1084981
theorem B1446659 : Blo 642303 1446659 := bstep (se 1 (by rfl) ⟨1084994, by rfl⟩ : syracuseStep 1446659 = 2169989) B2169989
theorem B1086257 : Blo 642303 1086257 := bstep (se 2 (by rfl) ⟨407346, by rfl⟩ : syracuseStep 1086257 = 814693) B814693
theorem B725827 : Blo 642303 725827 := bstep (se 1 (by rfl) ⟨544370, by rfl⟩ : syracuseStep 725827 = 1088741) B1088741
theorem B1086385 : Blo 642303 1086385 := bstep (se 2 (by rfl) ⟨407394, by rfl⟩ : syracuseStep 1086385 = 814789) B814789
theorem B1086419 : Blo 642303 1086419 := bstep (se 1 (by rfl) ⟨814814, by rfl⟩ : syracuseStep 1086419 = 1629629) B1629629
theorem B725971 : Blo 642303 725971 := bstep (se 1 (by rfl) ⟨544478, by rfl⟩ : syracuseStep 725971 = 1088957) B1088957
theorem B1446929 : Blo 642303 1446929 := bstep (se 2 (by rfl) ⟨542598, by rfl⟩ : syracuseStep 1446929 = 1085197) B1085197
theorem B1446947 : Blo 642303 1446947 := bstep (se 1 (by rfl) ⟨1085210, by rfl⟩ : syracuseStep 1446947 = 2170421) B2170421
theorem B1086547 : Blo 642303 1086547 := bstep (se 1 (by rfl) ⟨814910, by rfl⟩ : syracuseStep 1086547 = 1629821) B1629821
theorem B726115 : Blo 642303 726115 := bstep (se 1 (by rfl) ⟨544586, by rfl⟩ : syracuseStep 726115 = 1089173) B1089173
theorem B1840259 : Blo 642303 1840259 := bstep (se 1 (by rfl) ⟨1380194, by rfl⟩ : syracuseStep 1840259 = 2760389) B2760389
theorem B1741997 : Blo 642303 1741997 := bstep (se 3 (by rfl) ⟨326624, by rfl⟩ : syracuseStep 1741997 = 653249) B653249
theorem B1086689 : Blo 642303 1086689 := bstep (se 2 (by rfl) ⟨407508, by rfl⟩ : syracuseStep 1086689 = 815017) B815017
theorem B2168045 : Blo 642303 2168045 := bstep (se 3 (by rfl) ⟨406508, by rfl⟩ : syracuseStep 2168045 = 813017) B813017
theorem B726259 : Blo 642303 726259 := bstep (se 1 (by rfl) ⟨544694, by rfl⟩ : syracuseStep 726259 = 1089389) B1089389
theorem B4134149 : Blo 642303 4134149 := bstep (se 4 (by rfl) ⟨387576, by rfl⟩ : syracuseStep 4134149 = 775153) B775153
theorem B2168099 : Blo 642303 2168099 := bstep (se 1 (by rfl) ⟨1626074, by rfl⟩ : syracuseStep 2168099 = 3252149) B3252149
theorem B1447217 : Blo 642303 1447217 := bstep (se 2 (by rfl) ⟨542706, by rfl⟩ : syracuseStep 1447217 = 1085413) B1085413
theorem B1447235 : Blo 642303 1447235 := bstep (se 1 (by rfl) ⟨1085426, by rfl⟩ : syracuseStep 1447235 = 2170853) B2170853
theorem B1086817 : Blo 642303 1086817 := bstep (se 2 (by rfl) ⟨407556, by rfl⟩ : syracuseStep 1086817 = 815113) B815113
theorem B1086851 : Blo 642303 1086851 := bstep (se 1 (by rfl) ⟨815138, by rfl⟩ : syracuseStep 1086851 = 1630277) B1630277
theorem B726403 : Blo 642303 726403 := bstep (se 1 (by rfl) ⟨544802, by rfl⟩ : syracuseStep 726403 = 1089605) B1089605
theorem B1545617 : Blo 642303 1545617 := bstep (se 2 (by rfl) ⟨579606, by rfl⟩ : syracuseStep 1545617 = 1159213) B1159213
theorem B1545731 : Blo 642303 1545731 := bstep (se 1 (by rfl) ⟨1159298, by rfl⟩ : syracuseStep 1545731 = 2318597) B2318597
theorem B1086979 : Blo 642303 1086979 := bstep (se 1 (by rfl) ⟨815234, by rfl⟩ : syracuseStep 1086979 = 1630469) B1630469
theorem B726547 : Blo 642303 726547 := bstep (se 1 (by rfl) ⟨544910, by rfl⟩ : syracuseStep 726547 = 1089821) B1089821
theorem B2168369 : Blo 642303 2168369 := bstep (se 2 (by rfl) ⟨813138, by rfl⟩ : syracuseStep 2168369 = 1626277) B1626277
theorem B1447505 : Blo 642303 1447505 := bstep (se 2 (by rfl) ⟨542814, by rfl⟩ : syracuseStep 1447505 = 1085629) B1085629
theorem B1447523 : Blo 642303 1447523 := bstep (se 1 (by rfl) ⟨1085642, by rfl⟩ : syracuseStep 1447523 = 2171285) B2171285
theorem B1087121 : Blo 642303 1087121 := bstep (se 2 (by rfl) ⟨407670, by rfl⟩ : syracuseStep 1087121 = 815341) B815341
theorem B726691 : Blo 642303 726691 := bstep (se 1 (by rfl) ⟨545018, by rfl⟩ : syracuseStep 726691 = 1090037) B1090037
theorem B1545905 : Blo 642303 1545905 := bstep (se 2 (by rfl) ⟨579714, by rfl⟩ : syracuseStep 1545905 = 1159429) B1159429
theorem B1087249 : Blo 642303 1087249 := bstep (se 2 (by rfl) ⟨407718, by rfl⟩ : syracuseStep 1087249 = 815437) B815437
theorem B1087283 : Blo 642303 1087283 := bstep (se 1 (by rfl) ⟨815462, by rfl⟩ : syracuseStep 1087283 = 1630925) B1630925
theorem B726835 : Blo 642303 726835 := bstep (se 1 (by rfl) ⟨545126, by rfl⟩ : syracuseStep 726835 = 1090253) B1090253
theorem B1447793 : Blo 642303 1447793 := bstep (se 2 (by rfl) ⟨542922, by rfl⟩ : syracuseStep 1447793 = 1085845) B1085845
theorem B1447811 : Blo 642303 1447811 := bstep (se 1 (by rfl) ⟨1085858, by rfl⟩ : syracuseStep 1447811 = 2171717) B2171717
theorem B1087411 : Blo 642303 1087411 := bstep (se 1 (by rfl) ⟨815558, by rfl⟩ : syracuseStep 1087411 = 1631117) B1631117
theorem B726979 : Blo 642303 726979 := bstep (se 1 (by rfl) ⟨545234, by rfl⟩ : syracuseStep 726979 = 1090469) B1090469
theorem B2758627 : Blo 642303 2758627 := bstep (se 1 (by rfl) ⟨2068970, by rfl⟩ : syracuseStep 2758627 = 4137941) B4137941
theorem B1087553 : Blo 642303 1087553 := bstep (se 2 (by rfl) ⟨407832, by rfl⟩ : syracuseStep 1087553 = 815665) B815665
theorem B2168909 : Blo 642303 2168909 := bstep (se 3 (by rfl) ⟨406670, by rfl⟩ : syracuseStep 2168909 = 813341) B813341
theorem B2168963 : Blo 642303 2168963 := bstep (se 1 (by rfl) ⟨1626722, by rfl⟩ : syracuseStep 2168963 = 3253445) B3253445
theorem B1448081 : Blo 642303 1448081 := bstep (se 2 (by rfl) ⟨543030, by rfl⟩ : syracuseStep 1448081 = 1086061) B1086061
theorem B1448099 : Blo 642303 1448099 := bstep (se 1 (by rfl) ⟨1086074, by rfl⟩ : syracuseStep 1448099 = 2172149) B2172149
theorem B1087681 : Blo 642303 1087681 := bstep (se 2 (by rfl) ⟨407880, by rfl⟩ : syracuseStep 1087681 = 815761) B815761
theorem B1087715 : Blo 642303 1087715 := bstep (se 1 (by rfl) ⟨815786, by rfl⟩ : syracuseStep 1087715 = 1631573) B1631573
theorem B2791693 : Blo 642303 2791693 := bstep (se 3 (by rfl) ⟨523442, by rfl⟩ : syracuseStep 2791693 = 1046885) B1046885
theorem B1087843 : Blo 642303 1087843 := bstep (se 1 (by rfl) ⟨815882, by rfl⟩ : syracuseStep 1087843 = 1631765) B1631765
theorem B3676529 : Blo 642303 3676529 := bstep (se 2 (by rfl) ⟨1378698, by rfl⟩ : syracuseStep 3676529 = 2757397) B2757397
theorem B2169233 : Blo 642303 2169233 := bstep (se 2 (by rfl) ⟨813462, by rfl⟩ : syracuseStep 2169233 = 1626925) B1626925
theorem B1448369 : Blo 642303 1448369 := bstep (se 2 (by rfl) ⟨543138, by rfl⟩ : syracuseStep 1448369 = 1086277) B1086277
theorem B1448387 : Blo 642303 1448387 := bstep (se 1 (by rfl) ⟨1086290, by rfl⟩ : syracuseStep 1448387 = 2172581) B2172581
theorem B2791907 : Blo 642303 2791907 := bstep (se 1 (by rfl) ⟨2093930, by rfl⟩ : syracuseStep 2791907 = 4187861) B4187861
theorem B1087985 : Blo 642303 1087985 := bstep (se 2 (by rfl) ⟨407994, by rfl⟩ : syracuseStep 1087985 = 815989) B815989
theorem B1088113 : Blo 642303 1088113 := bstep (se 2 (by rfl) ⟨408042, by rfl⟩ : syracuseStep 1088113 = 816085) B816085
theorem B1088147 : Blo 642303 1088147 := bstep (se 1 (by rfl) ⟨816110, by rfl⟩ : syracuseStep 1088147 = 1632221) B1632221
theorem B4397773 : Blo 642303 4397773 := bstep (se 3 (by rfl) ⟨824582, by rfl⟩ : syracuseStep 4397773 = 1649165) B1649165
theorem B1448657 : Blo 642303 1448657 := bstep (se 2 (by rfl) ⟨543246, by rfl⟩ : syracuseStep 1448657 = 1086493) B1086493
theorem B1448675 : Blo 642303 1448675 := bstep (se 1 (by rfl) ⟨1086506, by rfl⟩ : syracuseStep 1448675 = 2173013) B2173013
theorem B1743619 : Blo 642303 1743619 := bstep (se 1 (by rfl) ⟨1307714, by rfl⟩ : syracuseStep 1743619 = 2615429) B2615429
theorem B1088275 : Blo 642303 1088275 := bstep (se 1 (by rfl) ⟨816206, by rfl⟩ : syracuseStep 1088275 = 1632413) B1632413
theorem B15276853 : Blo 642303 15276853 := bstep (se 5 (by rfl) ⟨716102, by rfl⟩ : syracuseStep 15276853 = 1432205) B1432205
theorem B1088417 : Blo 642303 1088417 := bstep (se 2 (by rfl) ⟨408156, by rfl⟩ : syracuseStep 1088417 = 816313) B816313
theorem B2169773 : Blo 642303 2169773 := bstep (se 3 (by rfl) ⟨406832, by rfl⟩ : syracuseStep 2169773 = 813665) B813665
theorem B8919989 : Blo 642303 8919989 := bstep (se 5 (by rfl) ⟨418124, by rfl⟩ : syracuseStep 8919989 = 836249) B836249
theorem B2169827 : Blo 642303 2169827 := bstep (se 1 (by rfl) ⟨1627370, by rfl⟩ : syracuseStep 2169827 = 3254741) B3254741
theorem B1448945 : Blo 642303 1448945 := bstep (se 2 (by rfl) ⟨543354, by rfl⟩ : syracuseStep 1448945 = 1086709) B1086709
theorem B1448963 : Blo 642303 1448963 := bstep (se 1 (by rfl) ⟨1086722, by rfl⟩ : syracuseStep 1448963 = 2173445) B2173445
theorem B1088545 : Blo 642303 1088545 := bstep (se 2 (by rfl) ⟨408204, by rfl⟩ : syracuseStep 1088545 = 816409) B816409
theorem B1088579 : Blo 642303 1088579 := bstep (se 1 (by rfl) ⟨816434, by rfl⟩ : syracuseStep 1088579 = 1632869) B1632869
theorem B2235491 : Blo 642303 2235491 := bstep (se 1 (by rfl) ⟨1676618, by rfl⟩ : syracuseStep 2235491 = 3353237) B3353237
theorem B3906701 : Blo 642303 3906701 := bstep (se 3 (by rfl) ⟨732506, by rfl⟩ : syracuseStep 3906701 = 1465013) B1465013
theorem B5512333 : Blo 642303 5512333 := bstep (se 3 (by rfl) ⟨1033562, by rfl⟩ : syracuseStep 5512333 = 2067125) B2067125
theorem B1088707 : Blo 642303 1088707 := bstep (se 1 (by rfl) ⟨816530, by rfl⟩ : syracuseStep 1088707 = 1633061) B1633061
theorem B2170097 : Blo 642303 2170097 := bstep (se 2 (by rfl) ⟨813786, by rfl⟩ : syracuseStep 2170097 = 1627573) B1627573
theorem B4955377 : Blo 642303 4955377 := bstep (se 2 (by rfl) ⟨1858266, by rfl⟩ : syracuseStep 4955377 = 3716533) B3716533
theorem B1449233 : Blo 642303 1449233 := bstep (se 2 (by rfl) ⟨543462, by rfl⟩ : syracuseStep 1449233 = 1086925) B1086925
theorem B1449251 : Blo 642303 1449251 := bstep (se 1 (by rfl) ⟨1086938, by rfl⟩ : syracuseStep 1449251 = 2173877) B2173877
theorem B1088849 : Blo 642303 1088849 := bstep (se 2 (by rfl) ⟨408318, by rfl⟩ : syracuseStep 1088849 = 816637) B816637
theorem B1220035 : Blo 642303 1220035 := bstep (se 1 (by rfl) ⟨915026, by rfl⟩ : syracuseStep 1220035 = 1830053) B1830053
theorem B1088977 : Blo 642303 1088977 := bstep (se 2 (by rfl) ⟨408366, by rfl⟩ : syracuseStep 1088977 = 816733) B816733
theorem B1744355 : Blo 642303 1744355 := bstep (se 1 (by rfl) ⟨1308266, by rfl⟩ : syracuseStep 1744355 = 2616533) B2616533
theorem B1089011 : Blo 642303 1089011 := bstep (se 1 (by rfl) ⟨816758, by rfl⟩ : syracuseStep 1089011 = 1633517) B1633517
theorem B1449521 : Blo 642303 1449521 := bstep (se 2 (by rfl) ⟨543570, by rfl⟩ : syracuseStep 1449521 = 1087141) B1087141
theorem B1449539 : Blo 642303 1449539 := bstep (se 1 (by rfl) ⟨1087154, by rfl⟩ : syracuseStep 1449539 = 2174309) B2174309
theorem B5283427 : Blo 642303 5283427 := bstep (se 1 (by rfl) ⟨3962570, by rfl⟩ : syracuseStep 5283427 = 7925141) B7925141
theorem B3251825 : Blo 642303 3251825 := bstep (se 2 (by rfl) ⟨1219434, by rfl⟩ : syracuseStep 3251825 = 2438869) B2438869
theorem B1089139 : Blo 642303 1089139 := bstep (se 1 (by rfl) ⟨816854, by rfl⟩ : syracuseStep 1089139 = 1633709) B1633709
theorem B1089281 : Blo 642303 1089281 := bstep (se 2 (by rfl) ⟨408480, by rfl⟩ : syracuseStep 1089281 = 816961) B816961
theorem B2170637 : Blo 642303 2170637 := bstep (se 3 (by rfl) ⟨406994, by rfl⟩ : syracuseStep 2170637 = 813989) B813989
theorem B3677987 : Blo 642303 3677987 := bstep (se 1 (by rfl) ⟨2758490, by rfl⟩ : syracuseStep 3677987 = 5516981) B5516981
theorem B2170691 : Blo 642303 2170691 := bstep (se 1 (by rfl) ⟨1628018, by rfl⟩ : syracuseStep 2170691 = 3256037) B3256037
theorem B1449809 : Blo 642303 1449809 := bstep (se 2 (by rfl) ⟨543678, by rfl⟩ : syracuseStep 1449809 = 1087357) B1087357
theorem B1449827 : Blo 642303 1449827 := bstep (se 1 (by rfl) ⟨1087370, by rfl⟩ : syracuseStep 1449827 = 2174741) B2174741
theorem B1089409 : Blo 642303 1089409 := bstep (se 2 (by rfl) ⟨408528, by rfl⟩ : syracuseStep 1089409 = 817057) B817057
theorem B1220483 : Blo 642303 1220483 := bstep (se 1 (by rfl) ⟨915362, by rfl⟩ : syracuseStep 1220483 = 1830725) B1830725
theorem B1089443 : Blo 642303 1089443 := bstep (se 1 (by rfl) ⟨817082, by rfl⟩ : syracuseStep 1089443 = 1634165) B1634165
theorem B1089571 : Blo 642303 1089571 := bstep (se 1 (by rfl) ⟨817178, by rfl⟩ : syracuseStep 1089571 = 1634357) B1634357
theorem B2170961 : Blo 642303 2170961 := bstep (se 2 (by rfl) ⟨814110, by rfl⟩ : syracuseStep 2170961 = 1628221) B1628221
theorem B1450097 : Blo 642303 1450097 := bstep (se 2 (by rfl) ⟨543786, by rfl⟩ : syracuseStep 1450097 = 1087573) B1087573
theorem B1450115 : Blo 642303 1450115 := bstep (se 1 (by rfl) ⟨1087586, by rfl⟩ : syracuseStep 1450115 = 2175173) B2175173
theorem B1220771 : Blo 642303 1220771 := bstep (se 1 (by rfl) ⟨915578, by rfl⟩ : syracuseStep 1220771 = 1831157) B1831157
theorem B1089713 : Blo 642303 1089713 := bstep (se 2 (by rfl) ⟨408642, by rfl⟩ : syracuseStep 1089713 = 817285) B817285
theorem B1089841 : Blo 642303 1089841 := bstep (se 2 (by rfl) ⟨408690, by rfl⟩ : syracuseStep 1089841 = 817381) B817381
theorem B1089875 : Blo 642303 1089875 := bstep (se 1 (by rfl) ⟨817406, by rfl⟩ : syracuseStep 1089875 = 1634813) B1634813
theorem B1450385 : Blo 642303 1450385 := bstep (se 2 (by rfl) ⟨543894, by rfl⟩ : syracuseStep 1450385 = 1087789) B1087789
theorem B1450403 : Blo 642303 1450403 := bstep (se 1 (by rfl) ⟨1087802, by rfl⟩ : syracuseStep 1450403 = 2175605) B2175605
theorem B5513669 : Blo 642303 5513669 := bstep (se 4 (by rfl) ⟨516906, by rfl⟩ : syracuseStep 5513669 = 1033813) B1033813
theorem B1090003 : Blo 642303 1090003 := bstep (se 1 (by rfl) ⟨817502, by rfl⟩ : syracuseStep 1090003 = 1635005) B1635005
theorem B5972549 : Blo 642303 5972549 := bstep (se 4 (by rfl) ⟨559926, by rfl⟩ : syracuseStep 5972549 = 1119853) B1119853
theorem B1090145 : Blo 642303 1090145 := bstep (se 2 (by rfl) ⟨408804, by rfl⟩ : syracuseStep 1090145 = 817609) B817609
theorem B2171501 : Blo 642303 2171501 := bstep (se 3 (by rfl) ⟨407156, by rfl⟩ : syracuseStep 2171501 = 814313) B814313
theorem B2171555 : Blo 642303 2171555 := bstep (se 1 (by rfl) ⟨1628666, by rfl⟩ : syracuseStep 2171555 = 3257333) B3257333
theorem B1450673 : Blo 642303 1450673 := bstep (se 2 (by rfl) ⟨544002, by rfl⟩ : syracuseStep 1450673 = 1088005) B1088005
theorem B1450691 : Blo 642303 1450691 := bstep (se 1 (by rfl) ⟨1088018, by rfl⟩ : syracuseStep 1450691 = 2176037) B2176037
theorem B1090273 : Blo 642303 1090273 := bstep (se 2 (by rfl) ⟨408852, by rfl⟩ : syracuseStep 1090273 = 817705) B817705
theorem B4137713 : Blo 642303 4137713 := bstep (se 2 (by rfl) ⟨1551642, by rfl⟩ : syracuseStep 4137713 = 3103285) B3103285
theorem B1090307 : Blo 642303 1090307 := bstep (se 1 (by rfl) ⟨817730, by rfl⟩ : syracuseStep 1090307 = 1635461) B1635461
theorem B1090435 : Blo 642303 1090435 := bstep (se 1 (by rfl) ⟨817826, by rfl⟩ : syracuseStep 1090435 = 1635653) B1635653
theorem B2171825 : Blo 642303 2171825 := bstep (se 2 (by rfl) ⟨814434, by rfl⟩ : syracuseStep 2171825 = 1628869) B1628869
theorem B4891589 : Blo 642303 4891589 := bstep (se 4 (by rfl) ⟨458586, by rfl⟩ : syracuseStep 4891589 = 917173) B917173
theorem B1450961 : Blo 642303 1450961 := bstep (se 2 (by rfl) ⟨544110, by rfl⟩ : syracuseStep 1450961 = 1088221) B1088221
theorem B1450979 : Blo 642303 1450979 := bstep (se 1 (by rfl) ⟨1088234, by rfl⟩ : syracuseStep 1450979 = 2176469) B2176469
theorem B1090577 : Blo 642303 1090577 := bstep (se 2 (by rfl) ⟨408966, by rfl⟩ : syracuseStep 1090577 = 817933) B817933
theorem B3253283 : Blo 642303 3253283 := bstep (se 1 (by rfl) ⟨2439962, by rfl⟩ : syracuseStep 3253283 = 4879925) B4879925
theorem B1221713 : Blo 642303 1221713 := bstep (se 2 (by rfl) ⟨458142, by rfl⟩ : syracuseStep 1221713 = 916285) B916285
theorem B1451249 : Blo 642303 1451249 := bstep (se 2 (by rfl) ⟨544218, by rfl⟩ : syracuseStep 1451249 = 1088437) B1088437
theorem B1451267 : Blo 642303 1451267 := bstep (se 1 (by rfl) ⟨1088450, by rfl⟩ : syracuseStep 1451267 = 2176901) B2176901
theorem B2205073 : Blo 642303 2205073 := bstep (se 2 (by rfl) ⟨826902, by rfl⟩ : syracuseStep 2205073 = 1653805) B1653805
theorem B2172365 : Blo 642303 2172365 := bstep (se 3 (by rfl) ⟨407318, by rfl⟩ : syracuseStep 2172365 = 814637) B814637
theorem B2172419 : Blo 642303 2172419 := bstep (se 1 (by rfl) ⟨1629314, by rfl⟩ : syracuseStep 2172419 = 3258629) B3258629
theorem B1451537 : Blo 642303 1451537 := bstep (se 2 (by rfl) ⟨544326, by rfl⟩ : syracuseStep 1451537 = 1088653) B1088653
theorem B1451555 : Blo 642303 1451555 := bstep (se 1 (by rfl) ⟨1088666, by rfl⟩ : syracuseStep 1451555 = 2177333) B2177333
theorem B2238211 : Blo 642303 2238211 := bstep (se 1 (by rfl) ⟨1678658, by rfl⟩ : syracuseStep 2238211 = 3357317) B3357317
theorem B2172689 : Blo 642303 2172689 := bstep (se 2 (by rfl) ⟨814758, by rfl⟩ : syracuseStep 2172689 = 1629517) B1629517
theorem B1451825 : Blo 642303 1451825 := bstep (se 2 (by rfl) ⟨544434, by rfl⟩ : syracuseStep 1451825 = 1088869) B1088869
theorem B1451843 : Blo 642303 1451843 := bstep (se 1 (by rfl) ⟨1088882, by rfl⟩ : syracuseStep 1451843 = 2177765) B2177765
theorem B3254093 : Blo 642303 3254093 := bstep (se 3 (by rfl) ⟨610142, by rfl⟩ : syracuseStep 3254093 = 1220285) B1220285
theorem B1222609 : Blo 642303 1222609 := bstep (se 2 (by rfl) ⟨458478, by rfl⟩ : syracuseStep 1222609 = 916957) B916957
theorem B1452113 : Blo 642303 1452113 := bstep (se 2 (by rfl) ⟨544542, by rfl⟩ : syracuseStep 1452113 = 1089085) B1089085
theorem B1452131 : Blo 642303 1452131 := bstep (se 1 (by rfl) ⟨1089098, by rfl⟩ : syracuseStep 1452131 = 2178197) B2178197
theorem B1222769 : Blo 642303 1222769 := bstep (se 2 (by rfl) ⟨458538, by rfl⟩ : syracuseStep 1222769 = 917077) B917077
theorem B4139171 : Blo 642303 4139171 := bstep (se 1 (by rfl) ⟨3104378, by rfl⟩ : syracuseStep 4139171 = 6208757) B6208757
theorem B7317701 : Blo 642303 7317701 := bstep (se 4 (by rfl) ⟨686034, by rfl⟩ : syracuseStep 7317701 = 1372069) B1372069
theorem B2173229 : Blo 642303 2173229 := bstep (se 3 (by rfl) ⟨407480, by rfl⟩ : syracuseStep 2173229 = 814961) B814961
theorem B2173283 : Blo 642303 2173283 := bstep (se 1 (by rfl) ⟨1629962, by rfl⟩ : syracuseStep 2173283 = 3259925) B3259925
theorem B5581169 : Blo 642303 5581169 := bstep (se 2 (by rfl) ⟨2092938, by rfl⟩ : syracuseStep 5581169 = 4185877) B4185877
theorem B1452401 : Blo 642303 1452401 := bstep (se 2 (by rfl) ⟨544650, by rfl⟩ : syracuseStep 1452401 = 1089301) B1089301
theorem B1452419 : Blo 642303 1452419 := bstep (se 1 (by rfl) ⟨1089314, by rfl⟩ : syracuseStep 1452419 = 2178629) B2178629
theorem B1223171 : Blo 642303 1223171 := bstep (se 1 (by rfl) ⟨917378, by rfl⟩ : syracuseStep 1223171 = 1834757) B1834757
theorem B2173553 : Blo 642303 2173553 := bstep (se 2 (by rfl) ⟨815082, by rfl⟩ : syracuseStep 2173553 = 1630165) B1630165
theorem B1452689 : Blo 642303 1452689 := bstep (se 2 (by rfl) ⟨544758, by rfl⟩ : syracuseStep 1452689 = 1089517) B1089517
theorem B1452707 : Blo 642303 1452707 := bstep (se 1 (by rfl) ⟨1089530, by rfl⟩ : syracuseStep 1452707 = 2179061) B2179061
theorem B1452977 : Blo 642303 1452977 := bstep (se 2 (by rfl) ⟨544866, by rfl⟩ : syracuseStep 1452977 = 1089733) B1089733
theorem B1452995 : Blo 642303 1452995 := bstep (se 1 (by rfl) ⟨1089746, by rfl⟩ : syracuseStep 1452995 = 2179493) B2179493
theorem B2174093 : Blo 642303 2174093 := bstep (se 3 (by rfl) ⟨407642, by rfl⟩ : syracuseStep 2174093 = 815285) B815285
theorem B4140173 : Blo 642303 4140173 := bstep (se 3 (by rfl) ⟨776282, by rfl⟩ : syracuseStep 4140173 = 1552565) B1552565
theorem B2174147 : Blo 642303 2174147 := bstep (se 1 (by rfl) ⟨1630610, by rfl⟩ : syracuseStep 2174147 = 3261221) B3261221
theorem B1453265 : Blo 642303 1453265 := bstep (se 2 (by rfl) ⟨544974, by rfl⟩ : syracuseStep 1453265 = 1089949) B1089949
theorem B11775203 : Blo 642303 11775203 := bstep (se 1 (by rfl) ⟨8831402, by rfl⟩ : syracuseStep 11775203 = 17662805) B17662805
theorem B1453283 : Blo 642303 1453283 := bstep (se 1 (by rfl) ⟨1089962, by rfl⟩ : syracuseStep 1453283 = 2179925) B2179925
theorem B732451 : Blo 642303 732451 := bstep (se 1 (by rfl) ⟨549338, by rfl⟩ : syracuseStep 732451 = 1098677) B1098677
theorem B1224067 : Blo 642303 1224067 := bstep (se 1 (by rfl) ⟨918050, by rfl⟩ : syracuseStep 1224067 = 1836101) B1836101
theorem B4632005 : Blo 642303 4632005 := bstep (se 4 (by rfl) ⟨434250, by rfl⟩ : syracuseStep 4632005 = 868501) B868501
theorem B1486289 : Blo 642303 1486289 := bstep (se 2 (by rfl) ⟨557358, by rfl⟩ : syracuseStep 1486289 = 1114717) B1114717
theorem B2174417 : Blo 642303 2174417 := bstep (se 2 (by rfl) ⟨815406, by rfl⟩ : syracuseStep 2174417 = 1630813) B1630813
theorem B1453553 : Blo 642303 1453553 := bstep (se 2 (by rfl) ⟨545082, by rfl⟩ : syracuseStep 1453553 = 1090165) B1090165
theorem B1453571 : Blo 642303 1453571 := bstep (se 1 (by rfl) ⟨1090178, by rfl⟩ : syracuseStep 1453571 = 2180357) B2180357
theorem B1224227 : Blo 642303 1224227 := bstep (se 1 (by rfl) ⟨918170, by rfl⟩ : syracuseStep 1224227 = 1836341) B1836341
theorem B1453841 : Blo 642303 1453841 := bstep (se 2 (by rfl) ⟨545190, by rfl⟩ : syracuseStep 1453841 = 1090381) B1090381
theorem B1453859 : Blo 642303 1453859 := bstep (se 1 (by rfl) ⟨1090394, by rfl⟩ : syracuseStep 1453859 = 2180789) B2180789
theorem B1650563 : Blo 642303 1650563 := bstep (se 1 (by rfl) ⟨1237922, by rfl⟩ : syracuseStep 1650563 = 2475845) B2475845
theorem B2174957 : Blo 642303 2174957 := bstep (se 3 (by rfl) ⟨407804, by rfl⟩ : syracuseStep 2174957 = 815609) B815609
theorem B2175011 : Blo 642303 2175011 := bstep (se 1 (by rfl) ⟨1631258, by rfl⟩ : syracuseStep 2175011 = 3262517) B3262517
theorem B1454129 : Blo 642303 1454129 := bstep (se 2 (by rfl) ⟨545298, by rfl⟩ : syracuseStep 1454129 = 1090597) B1090597
theorem B1454147 : Blo 642303 1454147 := bstep (se 1 (by rfl) ⟨1090610, by rfl⟩ : syracuseStep 1454147 = 2181221) B2181221
theorem B3092579 : Blo 642303 3092579 := bstep (se 1 (by rfl) ⟨2319434, by rfl⟩ : syracuseStep 3092579 = 4638869) B4638869
theorem B6697073 : Blo 642303 6697073 := bstep (se 2 (by rfl) ⟨2511402, by rfl⟩ : syracuseStep 6697073 = 5022805) B5022805
theorem B8269937 : Blo 642303 8269937 := bstep (se 2 (by rfl) ⟨3101226, by rfl⟩ : syracuseStep 8269937 = 6202453) B6202453
theorem B2175281 : Blo 642303 2175281 := bstep (se 2 (by rfl) ⟨815730, by rfl⟩ : syracuseStep 2175281 = 1631461) B1631461
theorem B1225297 : Blo 642303 1225297 := bstep (se 2 (by rfl) ⟨459486, by rfl⟩ : syracuseStep 1225297 = 918973) B918973
theorem B2241197 : Blo 642303 2241197 := bstep (se 3 (by rfl) ⟨420224, by rfl⟩ : syracuseStep 2241197 = 840449) B840449
theorem B3257009 : Blo 642303 3257009 := bstep (se 2 (by rfl) ⟨1221378, by rfl⟩ : syracuseStep 3257009 = 2442757) B2442757
theorem B2175821 : Blo 642303 2175821 := bstep (se 3 (by rfl) ⟨407966, by rfl⟩ : syracuseStep 2175821 = 815933) B815933
theorem B1028963 : Blo 642303 1028963 := bstep (se 1 (by rfl) ⟨771722, by rfl⟩ : syracuseStep 1028963 = 1543445) B1543445
theorem B2175875 : Blo 642303 2175875 := bstep (se 1 (by rfl) ⟨1631906, by rfl⟩ : syracuseStep 2175875 = 3263813) B3263813
theorem B963473 : Blo 642303 963473 := bstep (se 2 (by rfl) ⟨361302, by rfl⟩ : syracuseStep 963473 = 722605) B722605
theorem B963491 : Blo 642303 963491 := bstep (se 1 (by rfl) ⟨722618, by rfl⟩ : syracuseStep 963491 = 1445237) B1445237
theorem B7943093 : Blo 642303 7943093 := bstep (se 5 (by rfl) ⟨372332, by rfl⟩ : syracuseStep 7943093 = 744665) B744665
theorem B963521 : Blo 642303 963521 := bstep (se 2 (by rfl) ⟨361320, by rfl⟩ : syracuseStep 963521 = 722641) B722641
theorem B963539 : Blo 642303 963539 := bstep (se 1 (by rfl) ⟨722654, by rfl⟩ : syracuseStep 963539 = 1445309) B1445309
theorem B963569 : Blo 642303 963569 := bstep (se 2 (by rfl) ⟨361338, by rfl⟩ : syracuseStep 963569 = 722677) B722677
theorem B963587 : Blo 642303 963587 := bstep (se 1 (by rfl) ⟨722690, by rfl⟩ : syracuseStep 963587 = 1445381) B1445381
theorem B963617 : Blo 642303 963617 := bstep (se 2 (by rfl) ⟨361356, by rfl⟩ : syracuseStep 963617 = 722713) B722713
theorem B963635 : Blo 642303 963635 := bstep (se 1 (by rfl) ⟨722726, by rfl⟩ : syracuseStep 963635 = 1445453) B1445453
theorem B963665 : Blo 642303 963665 := bstep (se 2 (by rfl) ⟨361374, by rfl⟩ : syracuseStep 963665 = 722749) B722749
theorem B963683 : Blo 642303 963683 := bstep (se 1 (by rfl) ⟨722762, by rfl⟩ : syracuseStep 963683 = 1445525) B1445525
theorem B963713 : Blo 642303 963713 := bstep (se 2 (by rfl) ⟨361392, by rfl⟩ : syracuseStep 963713 = 722785) B722785
theorem B2176145 : Blo 642303 2176145 := bstep (se 2 (by rfl) ⟨816054, by rfl⟩ : syracuseStep 2176145 = 1632109) B1632109
theorem B963731 : Blo 642303 963731 := bstep (se 1 (by rfl) ⟨722798, by rfl⟩ : syracuseStep 963731 = 1445597) B1445597
theorem B963761 : Blo 642303 963761 := bstep (se 2 (by rfl) ⟨361410, by rfl⟩ : syracuseStep 963761 = 722821) B722821
theorem B963779 : Blo 642303 963779 := bstep (se 1 (by rfl) ⟨722834, by rfl⟩ : syracuseStep 963779 = 1445669) B1445669
theorem B963809 : Blo 642303 963809 := bstep (se 2 (by rfl) ⟨361428, by rfl⟩ : syracuseStep 963809 = 722857) B722857
theorem B963827 : Blo 642303 963827 := bstep (se 1 (by rfl) ⟨722870, by rfl⟩ : syracuseStep 963827 = 1445741) B1445741
theorem B963857 : Blo 642303 963857 := bstep (se 2 (by rfl) ⟨361446, by rfl⟩ : syracuseStep 963857 = 722893) B722893
theorem B963875 : Blo 642303 963875 := bstep (se 1 (by rfl) ⟨722906, by rfl⟩ : syracuseStep 963875 = 1445813) B1445813
theorem B963905 : Blo 642303 963905 := bstep (se 2 (by rfl) ⟨361464, by rfl⟩ : syracuseStep 963905 = 722929) B722929
theorem B963923 : Blo 642303 963923 := bstep (se 1 (by rfl) ⟨722942, by rfl⟩ : syracuseStep 963923 = 1445885) B1445885
theorem B2209123 : Blo 642303 2209123 := bstep (se 1 (by rfl) ⟨1656842, by rfl⟩ : syracuseStep 2209123 = 3313685) B3313685
theorem B5518691 : Blo 642303 5518691 := bstep (se 1 (by rfl) ⟨4139018, by rfl⟩ : syracuseStep 5518691 = 8278037) B8278037
theorem B963953 : Blo 642303 963953 := bstep (se 2 (by rfl) ⟨361482, by rfl⟩ : syracuseStep 963953 = 722965) B722965
theorem B963971 : Blo 642303 963971 := bstep (se 1 (by rfl) ⟨722978, by rfl⟩ : syracuseStep 963971 = 1445957) B1445957
theorem B964001 : Blo 642303 964001 := bstep (se 2 (by rfl) ⟨361500, by rfl⟩ : syracuseStep 964001 = 723001) B723001
theorem B964019 : Blo 642303 964019 := bstep (se 1 (by rfl) ⟨723014, by rfl⟩ : syracuseStep 964019 = 1446029) B1446029
theorem B964049 : Blo 642303 964049 := bstep (se 2 (by rfl) ⟨361518, by rfl⟩ : syracuseStep 964049 = 723037) B723037
theorem B964067 : Blo 642303 964067 := bstep (se 1 (by rfl) ⟨723050, by rfl⟩ : syracuseStep 964067 = 1446101) B1446101
theorem B964097 : Blo 642303 964097 := bstep (se 2 (by rfl) ⟨361536, by rfl⟩ : syracuseStep 964097 = 723073) B723073
theorem B964115 : Blo 642303 964115 := bstep (se 1 (by rfl) ⟨723086, by rfl⟩ : syracuseStep 964115 = 1446173) B1446173
theorem B964145 : Blo 642303 964145 := bstep (se 2 (by rfl) ⟨361554, by rfl⟩ : syracuseStep 964145 = 723109) B723109
theorem B964163 : Blo 642303 964163 := bstep (se 1 (by rfl) ⟨723122, by rfl⟩ : syracuseStep 964163 = 1446245) B1446245
theorem B964193 : Blo 642303 964193 := bstep (se 2 (by rfl) ⟨361572, by rfl⟩ : syracuseStep 964193 = 723145) B723145
theorem B1226353 : Blo 642303 1226353 := bstep (se 2 (by rfl) ⟨459882, by rfl⟩ : syracuseStep 1226353 = 919765) B919765
theorem B964211 : Blo 642303 964211 := bstep (se 1 (by rfl) ⟨723158, by rfl⟩ : syracuseStep 964211 = 1446317) B1446317
theorem B964241 : Blo 642303 964241 := bstep (se 2 (by rfl) ⟨361590, by rfl⟩ : syracuseStep 964241 = 723181) B723181
theorem B1160849 : Blo 642303 1160849 := bstep (se 2 (by rfl) ⟨435318, by rfl⟩ : syracuseStep 1160849 = 870637) B870637
theorem B964259 : Blo 642303 964259 := bstep (se 1 (by rfl) ⟨723194, by rfl⟩ : syracuseStep 964259 = 1446389) B1446389
theorem B2176685 : Blo 642303 2176685 := bstep (se 3 (by rfl) ⟨408128, by rfl⟩ : syracuseStep 2176685 = 816257) B816257
theorem B964289 : Blo 642303 964289 := bstep (se 2 (by rfl) ⟨361608, by rfl⟩ : syracuseStep 964289 = 723217) B723217
theorem B964307 : Blo 642303 964307 := bstep (se 1 (by rfl) ⟨723230, by rfl⟩ : syracuseStep 964307 = 1446461) B1446461
theorem B2176739 : Blo 642303 2176739 := bstep (se 1 (by rfl) ⟨1632554, by rfl⟩ : syracuseStep 2176739 = 3265109) B3265109
theorem B964337 : Blo 642303 964337 := bstep (se 2 (by rfl) ⟨361626, by rfl⟩ : syracuseStep 964337 = 723253) B723253
theorem B964355 : Blo 642303 964355 := bstep (se 1 (by rfl) ⟨723266, by rfl⟩ : syracuseStep 964355 = 1446533) B1446533
theorem B964385 : Blo 642303 964385 := bstep (se 2 (by rfl) ⟨361644, by rfl⟩ : syracuseStep 964385 = 723289) B723289
theorem B1029937 : Blo 642303 1029937 := bstep (se 2 (by rfl) ⟨386226, by rfl⟩ : syracuseStep 1029937 = 772453) B772453
theorem B964403 : Blo 642303 964403 := bstep (se 1 (by rfl) ⟨723302, by rfl⟩ : syracuseStep 964403 = 1446605) B1446605
theorem B964433 : Blo 642303 964433 := bstep (se 2 (by rfl) ⟨361662, by rfl⟩ : syracuseStep 964433 = 723325) B723325
theorem B964451 : Blo 642303 964451 := bstep (se 1 (by rfl) ⟨723338, by rfl⟩ : syracuseStep 964451 = 1446677) B1446677
theorem B964481 : Blo 642303 964481 := bstep (se 2 (by rfl) ⟨361680, by rfl⟩ : syracuseStep 964481 = 723361) B723361
theorem B964499 : Blo 642303 964499 := bstep (se 1 (by rfl) ⟨723374, by rfl⟩ : syracuseStep 964499 = 1446749) B1446749
theorem B964529 : Blo 642303 964529 := bstep (se 2 (by rfl) ⟨361698, by rfl⟩ : syracuseStep 964529 = 723397) B723397
theorem B964547 : Blo 642303 964547 := bstep (se 1 (by rfl) ⟨723410, by rfl⟩ : syracuseStep 964547 = 1446821) B1446821
theorem B964577 : Blo 642303 964577 := bstep (se 2 (by rfl) ⟨361716, by rfl⟩ : syracuseStep 964577 = 723433) B723433
theorem B2177009 : Blo 642303 2177009 := bstep (se 2 (by rfl) ⟨816378, by rfl⟩ : syracuseStep 2177009 = 1632757) B1632757
theorem B964595 : Blo 642303 964595 := bstep (se 1 (by rfl) ⟨723446, by rfl⟩ : syracuseStep 964595 = 1446893) B1446893
theorem B1226755 : Blo 642303 1226755 := bstep (se 1 (by rfl) ⟨920066, by rfl⟩ : syracuseStep 1226755 = 1840133) B1840133
theorem B964625 : Blo 642303 964625 := bstep (se 2 (by rfl) ⟨361734, by rfl⟩ : syracuseStep 964625 = 723469) B723469
theorem B964643 : Blo 642303 964643 := bstep (se 1 (by rfl) ⟨723482, by rfl⟩ : syracuseStep 964643 = 1446965) B1446965
theorem B1226801 : Blo 642303 1226801 := bstep (se 2 (by rfl) ⟨460050, by rfl⟩ : syracuseStep 1226801 = 920101) B920101
theorem B964673 : Blo 642303 964673 := bstep (se 2 (by rfl) ⟨361752, by rfl⟩ : syracuseStep 964673 = 723505) B723505
theorem B964691 : Blo 642303 964691 := bstep (se 1 (by rfl) ⟨723518, by rfl⟩ : syracuseStep 964691 = 1447037) B1447037
theorem B3258467 : Blo 642303 3258467 := bstep (se 1 (by rfl) ⟨2443850, by rfl⟩ : syracuseStep 3258467 = 4887701) B4887701
theorem B964721 : Blo 642303 964721 := bstep (se 2 (by rfl) ⟨361770, by rfl⟩ : syracuseStep 964721 = 723541) B723541
theorem B964739 : Blo 642303 964739 := bstep (se 1 (by rfl) ⟨723554, by rfl⟩ : syracuseStep 964739 = 1447109) B1447109
theorem B964769 : Blo 642303 964769 := bstep (se 2 (by rfl) ⟨361788, by rfl⟩ : syracuseStep 964769 = 723577) B723577
theorem B964787 : Blo 642303 964787 := bstep (se 1 (by rfl) ⟨723590, by rfl⟩ : syracuseStep 964787 = 1447181) B1447181
theorem B964817 : Blo 642303 964817 := bstep (se 2 (by rfl) ⟨361806, by rfl⟩ : syracuseStep 964817 = 723613) B723613
theorem B964835 : Blo 642303 964835 := bstep (se 1 (by rfl) ⟨723626, by rfl⟩ : syracuseStep 964835 = 1447253) B1447253
theorem B1030385 : Blo 642303 1030385 := bstep (se 2 (by rfl) ⟨386394, by rfl⟩ : syracuseStep 1030385 = 772789) B772789
theorem B964865 : Blo 642303 964865 := bstep (se 2 (by rfl) ⟨361824, by rfl⟩ : syracuseStep 964865 = 723649) B723649
theorem B964883 : Blo 642303 964883 := bstep (se 1 (by rfl) ⟨723662, by rfl⟩ : syracuseStep 964883 = 1447325) B1447325
theorem B964913 : Blo 642303 964913 := bstep (se 2 (by rfl) ⟨361842, by rfl⟩ : syracuseStep 964913 = 723685) B723685
theorem B964931 : Blo 642303 964931 := bstep (se 1 (by rfl) ⟨723698, by rfl⟩ : syracuseStep 964931 = 1447397) B1447397
theorem B964961 : Blo 642303 964961 := bstep (se 2 (by rfl) ⟨361860, by rfl⟩ : syracuseStep 964961 = 723721) B723721
theorem B964979 : Blo 642303 964979 := bstep (se 1 (by rfl) ⟨723734, by rfl⟩ : syracuseStep 964979 = 1447469) B1447469
theorem B965009 : Blo 642303 965009 := bstep (se 2 (by rfl) ⟨361878, by rfl⟩ : syracuseStep 965009 = 723757) B723757
theorem B965027 : Blo 642303 965027 := bstep (se 1 (by rfl) ⟨723770, by rfl⟩ : syracuseStep 965027 = 1447541) B1447541
theorem B965057 : Blo 642303 965057 := bstep (se 2 (by rfl) ⟨361896, by rfl⟩ : syracuseStep 965057 = 723793) B723793
theorem B2439629 : Blo 642303 2439629 := bstep (se 3 (by rfl) ⟨457430, by rfl⟩ : syracuseStep 2439629 = 914861) B914861
theorem B3914189 : Blo 642303 3914189 := bstep (se 3 (by rfl) ⟨733910, by rfl⟩ : syracuseStep 3914189 = 1467821) B1467821
theorem B965075 : Blo 642303 965075 := bstep (se 1 (by rfl) ⟨723806, by rfl⟩ : syracuseStep 965075 = 1447613) B1447613
theorem B965105 : Blo 642303 965105 := bstep (se 2 (by rfl) ⟨361914, by rfl⟩ : syracuseStep 965105 = 723829) B723829
theorem B965123 : Blo 642303 965123 := bstep (se 1 (by rfl) ⟨723842, by rfl⟩ : syracuseStep 965123 = 1447685) B1447685
theorem B2177549 : Blo 642303 2177549 := bstep (se 3 (by rfl) ⟨408290, by rfl⟩ : syracuseStep 2177549 = 816581) B816581
theorem B965153 : Blo 642303 965153 := bstep (se 2 (by rfl) ⟨361932, by rfl⟩ : syracuseStep 965153 = 723865) B723865
theorem B965171 : Blo 642303 965171 := bstep (se 1 (by rfl) ⟨723878, by rfl⟩ : syracuseStep 965171 = 1447757) B1447757
theorem B2177603 : Blo 642303 2177603 := bstep (se 1 (by rfl) ⟨1633202, by rfl⟩ : syracuseStep 2177603 = 3266405) B3266405
theorem B965201 : Blo 642303 965201 := bstep (se 2 (by rfl) ⟨361950, by rfl⟩ : syracuseStep 965201 = 723901) B723901
theorem B965219 : Blo 642303 965219 := bstep (se 1 (by rfl) ⟨723914, by rfl⟩ : syracuseStep 965219 = 1447829) B1447829
theorem B965249 : Blo 642303 965249 := bstep (se 2 (by rfl) ⟨361968, by rfl⟩ : syracuseStep 965249 = 723937) B723937
theorem B4897421 : Blo 642303 4897421 := bstep (se 3 (by rfl) ⟨918266, by rfl⟩ : syracuseStep 4897421 = 1836533) B1836533
theorem B965267 : Blo 642303 965267 := bstep (se 1 (by rfl) ⟨723950, by rfl⟩ : syracuseStep 965267 = 1447901) B1447901
theorem B965297 : Blo 642303 965297 := bstep (se 2 (by rfl) ⟨361986, by rfl⟩ : syracuseStep 965297 = 723973) B723973
theorem B965315 : Blo 642303 965315 := bstep (se 1 (by rfl) ⟨723986, by rfl⟩ : syracuseStep 965315 = 1447973) B1447973
theorem B965345 : Blo 642303 965345 := bstep (se 2 (by rfl) ⟨362004, by rfl⟩ : syracuseStep 965345 = 724009) B724009
theorem B965363 : Blo 642303 965363 := bstep (se 1 (by rfl) ⟨724022, by rfl⟩ : syracuseStep 965363 = 1448045) B1448045
theorem B965393 : Blo 642303 965393 := bstep (se 2 (by rfl) ⟨362022, by rfl⟩ : syracuseStep 965393 = 724045) B724045
theorem B965411 : Blo 642303 965411 := bstep (se 1 (by rfl) ⟨724058, by rfl⟩ : syracuseStep 965411 = 1448117) B1448117
theorem B965441 : Blo 642303 965441 := bstep (se 2 (by rfl) ⟨362040, by rfl⟩ : syracuseStep 965441 = 724081) B724081
theorem B2177873 : Blo 642303 2177873 := bstep (se 2 (by rfl) ⟨816702, by rfl⟩ : syracuseStep 2177873 = 1633405) B1633405
theorem B965459 : Blo 642303 965459 := bstep (se 1 (by rfl) ⟨724094, by rfl⟩ : syracuseStep 965459 = 1448189) B1448189
theorem B965489 : Blo 642303 965489 := bstep (se 2 (by rfl) ⟨362058, by rfl⟩ : syracuseStep 965489 = 724117) B724117
theorem B965507 : Blo 642303 965507 := bstep (se 1 (by rfl) ⟨724130, by rfl⟩ : syracuseStep 965507 = 1448261) B1448261
theorem B3259277 : Blo 642303 3259277 := bstep (se 3 (by rfl) ⟨611114, by rfl⟩ : syracuseStep 3259277 = 1222229) B1222229
theorem B965537 : Blo 642303 965537 := bstep (se 2 (by rfl) ⟨362076, by rfl⟩ : syracuseStep 965537 = 724153) B724153
theorem B965555 : Blo 642303 965555 := bstep (se 1 (by rfl) ⟨724166, by rfl⟩ : syracuseStep 965555 = 1448333) B1448333
theorem B965585 : Blo 642303 965585 := bstep (se 2 (by rfl) ⟨362094, by rfl⟩ : syracuseStep 965585 = 724189) B724189
theorem B965603 : Blo 642303 965603 := bstep (se 1 (by rfl) ⟨724202, by rfl⟩ : syracuseStep 965603 = 1448405) B1448405
theorem B965633 : Blo 642303 965633 := bstep (se 2 (by rfl) ⟨362112, by rfl⟩ : syracuseStep 965633 = 724225) B724225
theorem B965651 : Blo 642303 965651 := bstep (se 1 (by rfl) ⟨724238, by rfl⟩ : syracuseStep 965651 = 1448477) B1448477
theorem B965681 : Blo 642303 965681 := bstep (se 2 (by rfl) ⟨362130, by rfl⟩ : syracuseStep 965681 = 724261) B724261
theorem B965699 : Blo 642303 965699 := bstep (se 1 (by rfl) ⟨724274, by rfl⟩ : syracuseStep 965699 = 1448549) B1448549
theorem B965729 : Blo 642303 965729 := bstep (se 2 (by rfl) ⟨362148, by rfl⟩ : syracuseStep 965729 = 724297) B724297
theorem B965747 : Blo 642303 965747 := bstep (se 1 (by rfl) ⟨724310, by rfl⟩ : syracuseStep 965747 = 1448621) B1448621
theorem B965777 : Blo 642303 965777 := bstep (se 2 (by rfl) ⟨362166, by rfl⟩ : syracuseStep 965777 = 724333) B724333
theorem B965795 : Blo 642303 965795 := bstep (se 1 (by rfl) ⟨724346, by rfl⟩ : syracuseStep 965795 = 1448693) B1448693
theorem B965825 : Blo 642303 965825 := bstep (se 2 (by rfl) ⟨362184, by rfl⟩ : syracuseStep 965825 = 724369) B724369
theorem B965843 : Blo 642303 965843 := bstep (se 1 (by rfl) ⟨724382, by rfl⟩ : syracuseStep 965843 = 1448765) B1448765
theorem B965873 : Blo 642303 965873 := bstep (se 2 (by rfl) ⟨362202, by rfl⟩ : syracuseStep 965873 = 724405) B724405
theorem B965891 : Blo 642303 965891 := bstep (se 1 (by rfl) ⟨724418, by rfl⟩ : syracuseStep 965891 = 1448837) B1448837
theorem B965921 : Blo 642303 965921 := bstep (se 2 (by rfl) ⟨362220, by rfl⟩ : syracuseStep 965921 = 724441) B724441
theorem B965939 : Blo 642303 965939 := bstep (se 1 (by rfl) ⟨724454, by rfl⟩ : syracuseStep 965939 = 1448909) B1448909
theorem B965969 : Blo 642303 965969 := bstep (se 2 (by rfl) ⟨362238, by rfl⟩ : syracuseStep 965969 = 724477) B724477
theorem B965987 : Blo 642303 965987 := bstep (se 1 (by rfl) ⟨724490, by rfl⟩ : syracuseStep 965987 = 1448981) B1448981
theorem B2178413 : Blo 642303 2178413 := bstep (se 3 (by rfl) ⟨408452, by rfl⟩ : syracuseStep 2178413 = 816905) B816905
theorem B3095921 : Blo 642303 3095921 := bstep (se 2 (by rfl) ⟨1160970, by rfl⟩ : syracuseStep 3095921 = 2321941) B2321941
theorem B966017 : Blo 642303 966017 := bstep (se 2 (by rfl) ⟨362256, by rfl⟩ : syracuseStep 966017 = 724513) B724513
theorem B966035 : Blo 642303 966035 := bstep (se 1 (by rfl) ⟨724526, by rfl⟩ : syracuseStep 966035 = 1449053) B1449053
theorem B2178467 : Blo 642303 2178467 := bstep (se 1 (by rfl) ⟨1633850, by rfl⟩ : syracuseStep 2178467 = 3267701) B3267701
theorem B966065 : Blo 642303 966065 := bstep (se 2 (by rfl) ⟨362274, by rfl⟩ : syracuseStep 966065 = 724549) B724549
theorem B966083 : Blo 642303 966083 := bstep (se 1 (by rfl) ⟨724562, by rfl⟩ : syracuseStep 966083 = 1449125) B1449125
theorem B966113 : Blo 642303 966113 := bstep (se 2 (by rfl) ⟨362292, by rfl⟩ : syracuseStep 966113 = 724585) B724585
theorem B966131 : Blo 642303 966131 := bstep (se 1 (by rfl) ⟨724598, by rfl⟩ : syracuseStep 966131 = 1449197) B1449197
theorem B966161 : Blo 642303 966161 := bstep (se 2 (by rfl) ⟨362310, by rfl⟩ : syracuseStep 966161 = 724621) B724621
theorem B966179 : Blo 642303 966179 := bstep (se 1 (by rfl) ⟨724634, by rfl⟩ : syracuseStep 966179 = 1449269) B1449269
theorem B966209 : Blo 642303 966209 := bstep (se 2 (by rfl) ⟨362328, by rfl⟩ : syracuseStep 966209 = 724657) B724657
theorem B966227 : Blo 642303 966227 := bstep (se 1 (by rfl) ⟨724670, by rfl⟩ : syracuseStep 966227 = 1449341) B1449341
theorem B736867 : Blo 642303 736867 := bstep (se 1 (by rfl) ⟨552650, by rfl⟩ : syracuseStep 736867 = 1105301) B1105301
theorem B966257 : Blo 642303 966257 := bstep (se 2 (by rfl) ⟨362346, by rfl⟩ : syracuseStep 966257 = 724693) B724693
theorem B1031795 : Blo 642303 1031795 := bstep (se 1 (by rfl) ⟨773846, by rfl⟩ : syracuseStep 1031795 = 1547693) B1547693
theorem B966275 : Blo 642303 966275 := bstep (se 1 (by rfl) ⟨724706, by rfl⟩ : syracuseStep 966275 = 1449413) B1449413
theorem B966305 : Blo 642303 966305 := bstep (se 2 (by rfl) ⟨362364, by rfl⟩ : syracuseStep 966305 = 724729) B724729
theorem B2178737 : Blo 642303 2178737 := bstep (se 2 (by rfl) ⟨817026, by rfl⟩ : syracuseStep 2178737 = 1634053) B1634053
theorem B966323 : Blo 642303 966323 := bstep (se 1 (by rfl) ⟨724742, by rfl⟩ : syracuseStep 966323 = 1449485) B1449485
theorem B3096269 : Blo 642303 3096269 := bstep (se 3 (by rfl) ⟨580550, by rfl⟩ : syracuseStep 3096269 = 1161101) B1161101
theorem B966353 : Blo 642303 966353 := bstep (se 2 (by rfl) ⟨362382, by rfl⟩ : syracuseStep 966353 = 724765) B724765
theorem B966371 : Blo 642303 966371 := bstep (se 1 (by rfl) ⟨724778, by rfl⟩ : syracuseStep 966371 = 1449557) B1449557
theorem B966401 : Blo 642303 966401 := bstep (se 2 (by rfl) ⟨362400, by rfl⟩ : syracuseStep 966401 = 724801) B724801
theorem B966419 : Blo 642303 966419 := bstep (se 1 (by rfl) ⟨724814, by rfl⟩ : syracuseStep 966419 = 1449629) B1449629
theorem B1392419 : Blo 642303 1392419 := bstep (se 1 (by rfl) ⟨1044314, by rfl⟩ : syracuseStep 1392419 = 2088629) B2088629
theorem B966449 : Blo 642303 966449 := bstep (se 2 (by rfl) ⟨362418, by rfl⟩ : syracuseStep 966449 = 724837) B724837
theorem B1031987 : Blo 642303 1031987 := bstep (se 1 (by rfl) ⟨773990, by rfl⟩ : syracuseStep 1031987 = 1547981) B1547981
theorem B966467 : Blo 642303 966467 := bstep (se 1 (by rfl) ⟨724850, by rfl⟩ : syracuseStep 966467 = 1449701) B1449701
theorem B966497 : Blo 642303 966497 := bstep (se 2 (by rfl) ⟨362436, by rfl⟩ : syracuseStep 966497 = 724873) B724873
theorem B966515 : Blo 642303 966515 := bstep (se 1 (by rfl) ⟨724886, by rfl⟩ : syracuseStep 966515 = 1449773) B1449773
theorem B7323533 : Blo 642303 7323533 := bstep (se 3 (by rfl) ⟨1373162, by rfl⟩ : syracuseStep 7323533 = 2746325) B2746325
theorem B966545 : Blo 642303 966545 := bstep (se 2 (by rfl) ⟨362454, by rfl⟩ : syracuseStep 966545 = 724909) B724909
theorem B966563 : Blo 642303 966563 := bstep (se 1 (by rfl) ⟨724922, by rfl⟩ : syracuseStep 966563 = 1449845) B1449845
theorem B966593 : Blo 642303 966593 := bstep (se 2 (by rfl) ⟨362472, by rfl⟩ : syracuseStep 966593 = 724945) B724945
theorem B966611 : Blo 642303 966611 := bstep (se 1 (by rfl) ⟨724958, by rfl⟩ : syracuseStep 966611 = 1449917) B1449917
theorem B966641 : Blo 642303 966641 := bstep (se 2 (by rfl) ⟨362490, by rfl⟩ : syracuseStep 966641 = 724981) B724981
theorem B966659 : Blo 642303 966659 := bstep (se 1 (by rfl) ⟨724994, by rfl⟩ : syracuseStep 966659 = 1449989) B1449989
theorem B966689 : Blo 642303 966689 := bstep (se 2 (by rfl) ⟨362508, by rfl⟩ : syracuseStep 966689 = 725017) B725017
theorem B966707 : Blo 642303 966707 := bstep (se 1 (by rfl) ⟨725030, by rfl⟩ : syracuseStep 966707 = 1450061) B1450061
theorem B966737 : Blo 642303 966737 := bstep (se 2 (by rfl) ⟨362526, by rfl⟩ : syracuseStep 966737 = 725053) B725053
theorem B966755 : Blo 642303 966755 := bstep (se 1 (by rfl) ⟨725066, by rfl⟩ : syracuseStep 966755 = 1450133) B1450133
theorem B966785 : Blo 642303 966785 := bstep (se 2 (by rfl) ⟨362544, by rfl⟩ : syracuseStep 966785 = 725089) B725089
theorem B966803 : Blo 642303 966803 := bstep (se 1 (by rfl) ⟨725102, by rfl⟩ : syracuseStep 966803 = 1450205) B1450205
theorem B966833 : Blo 642303 966833 := bstep (se 2 (by rfl) ⟨362562, by rfl⟩ : syracuseStep 966833 = 725125) B725125
theorem B966851 : Blo 642303 966851 := bstep (se 1 (by rfl) ⟨725138, by rfl⟩ : syracuseStep 966851 = 1450277) B1450277
theorem B2179277 : Blo 642303 2179277 := bstep (se 3 (by rfl) ⟨408614, by rfl⟩ : syracuseStep 2179277 = 817229) B817229
theorem B966881 : Blo 642303 966881 := bstep (se 2 (by rfl) ⟨362580, by rfl⟩ : syracuseStep 966881 = 725161) B725161
theorem B966899 : Blo 642303 966899 := bstep (se 1 (by rfl) ⟨725174, by rfl⟩ : syracuseStep 966899 = 1450349) B1450349
theorem B2179331 : Blo 642303 2179331 := bstep (se 1 (by rfl) ⟨1634498, by rfl⟩ : syracuseStep 2179331 = 3268997) B3268997
theorem B966929 : Blo 642303 966929 := bstep (se 2 (by rfl) ⟨362598, by rfl⟩ : syracuseStep 966929 = 725197) B725197
theorem B966947 : Blo 642303 966947 := bstep (se 1 (by rfl) ⟨725210, by rfl⟩ : syracuseStep 966947 = 1450421) B1450421
theorem B966977 : Blo 642303 966977 := bstep (se 2 (by rfl) ⟨362616, by rfl⟩ : syracuseStep 966977 = 725233) B725233
theorem B966995 : Blo 642303 966995 := bstep (se 1 (by rfl) ⟨725246, by rfl⟩ : syracuseStep 966995 = 1450493) B1450493
theorem B967025 : Blo 642303 967025 := bstep (se 2 (by rfl) ⟨362634, by rfl⟩ : syracuseStep 967025 = 725269) B725269
theorem B967043 : Blo 642303 967043 := bstep (se 1 (by rfl) ⟨725282, by rfl⟩ : syracuseStep 967043 = 1450565) B1450565
theorem B967073 : Blo 642303 967073 := bstep (se 2 (by rfl) ⟨362652, by rfl⟩ : syracuseStep 967073 = 725305) B725305
theorem B967091 : Blo 642303 967091 := bstep (se 1 (by rfl) ⟨725318, by rfl⟩ : syracuseStep 967091 = 1450637) B1450637
theorem B967121 : Blo 642303 967121 := bstep (se 2 (by rfl) ⟨362670, by rfl⟩ : syracuseStep 967121 = 725341) B725341
theorem B967139 : Blo 642303 967139 := bstep (se 1 (by rfl) ⟨725354, by rfl⟩ : syracuseStep 967139 = 1450709) B1450709
theorem B967169 : Blo 642303 967169 := bstep (se 2 (by rfl) ⟨362688, by rfl⟩ : syracuseStep 967169 = 725377) B725377
theorem B2179601 : Blo 642303 2179601 := bstep (se 2 (by rfl) ⟨817350, by rfl⟩ : syracuseStep 2179601 = 1634701) B1634701
theorem B967187 : Blo 642303 967187 := bstep (se 1 (by rfl) ⟨725390, by rfl⟩ : syracuseStep 967187 = 1450781) B1450781
theorem B967217 : Blo 642303 967217 := bstep (se 2 (by rfl) ⟨362706, by rfl⟩ : syracuseStep 967217 = 725413) B725413
theorem B967235 : Blo 642303 967235 := bstep (se 1 (by rfl) ⟨725426, by rfl⟩ : syracuseStep 967235 = 1450853) B1450853
theorem B967265 : Blo 642303 967265 := bstep (se 2 (by rfl) ⟨362724, by rfl⟩ : syracuseStep 967265 = 725449) B725449
theorem B967283 : Blo 642303 967283 := bstep (se 1 (by rfl) ⟨725462, by rfl⟩ : syracuseStep 967283 = 1450925) B1450925
theorem B967313 : Blo 642303 967313 := bstep (se 2 (by rfl) ⟨362742, by rfl⟩ : syracuseStep 967313 = 725485) B725485
theorem B967331 : Blo 642303 967331 := bstep (se 1 (by rfl) ⟨725498, by rfl⟩ : syracuseStep 967331 = 1450997) B1450997
theorem B3719857 : Blo 642303 3719857 := bstep (se 2 (by rfl) ⟨1394946, by rfl⟩ : syracuseStep 3719857 = 2789893) B2789893
theorem B967361 : Blo 642303 967361 := bstep (se 2 (by rfl) ⟨362760, by rfl⟩ : syracuseStep 967361 = 725521) B725521
theorem B967379 : Blo 642303 967379 := bstep (se 1 (by rfl) ⟨725534, by rfl⟩ : syracuseStep 967379 = 1451069) B1451069
theorem B967409 : Blo 642303 967409 := bstep (se 2 (by rfl) ⟨362778, by rfl⟩ : syracuseStep 967409 = 725557) B725557
theorem B967427 : Blo 642303 967427 := bstep (se 1 (by rfl) ⟨725570, by rfl⟩ : syracuseStep 967427 = 1451141) B1451141
theorem B967457 : Blo 642303 967457 := bstep (se 2 (by rfl) ⟨362796, by rfl⟩ : syracuseStep 967457 = 725593) B725593
theorem B967475 : Blo 642303 967475 := bstep (se 1 (by rfl) ⟨725606, by rfl⟩ : syracuseStep 967475 = 1451213) B1451213
theorem B967505 : Blo 642303 967505 := bstep (se 2 (by rfl) ⟨362814, by rfl⟩ : syracuseStep 967505 = 725629) B725629
theorem B967523 : Blo 642303 967523 := bstep (se 1 (by rfl) ⟨725642, by rfl⟩ : syracuseStep 967523 = 1451285) B1451285
theorem B967553 : Blo 642303 967553 := bstep (se 2 (by rfl) ⟨362832, by rfl⟩ : syracuseStep 967553 = 725665) B725665
theorem B967571 : Blo 642303 967571 := bstep (se 1 (by rfl) ⟨725678, by rfl⟩ : syracuseStep 967571 = 1451357) B1451357
theorem B967601 : Blo 642303 967601 := bstep (se 2 (by rfl) ⟨362850, by rfl⟩ : syracuseStep 967601 = 725701) B725701
theorem B967619 : Blo 642303 967619 := bstep (se 1 (by rfl) ⟨725714, by rfl⟩ : syracuseStep 967619 = 1451429) B1451429
theorem B967649 : Blo 642303 967649 := bstep (se 2 (by rfl) ⟨362868, by rfl⟩ : syracuseStep 967649 = 725737) B725737
theorem B967667 : Blo 642303 967667 := bstep (se 1 (by rfl) ⟨725750, by rfl⟩ : syracuseStep 967667 = 1451501) B1451501
theorem B967697 : Blo 642303 967697 := bstep (se 2 (by rfl) ⟨362886, by rfl⟩ : syracuseStep 967697 = 725773) B725773
theorem B1098787 : Blo 642303 1098787 := bstep (se 1 (by rfl) ⟨824090, by rfl⟩ : syracuseStep 1098787 = 1648181) B1648181
theorem B967715 : Blo 642303 967715 := bstep (se 1 (by rfl) ⟨725786, by rfl⟩ : syracuseStep 967715 = 1451573) B1451573
theorem B2180141 : Blo 642303 2180141 := bstep (se 3 (by rfl) ⟨408776, by rfl⟩ : syracuseStep 2180141 = 817553) B817553
theorem B967745 : Blo 642303 967745 := bstep (se 2 (by rfl) ⟨362904, by rfl⟩ : syracuseStep 967745 = 725809) B725809
theorem B967763 : Blo 642303 967763 := bstep (se 1 (by rfl) ⟨725822, by rfl⟩ : syracuseStep 967763 = 1451645) B1451645
theorem B2180195 : Blo 642303 2180195 := bstep (se 1 (by rfl) ⟨1635146, by rfl⟩ : syracuseStep 2180195 = 3270293) B3270293
theorem B967793 : Blo 642303 967793 := bstep (se 2 (by rfl) ⟨362922, by rfl⟩ : syracuseStep 967793 = 725845) B725845
theorem B967811 : Blo 642303 967811 := bstep (se 1 (by rfl) ⟨725858, by rfl⟩ : syracuseStep 967811 = 1451717) B1451717
theorem B967841 : Blo 642303 967841 := bstep (se 2 (by rfl) ⟨362940, by rfl⟩ : syracuseStep 967841 = 725881) B725881
theorem B967859 : Blo 642303 967859 := bstep (se 1 (by rfl) ⟨725894, by rfl⟩ : syracuseStep 967859 = 1451789) B1451789
theorem B1033409 : Blo 642303 1033409 := bstep (se 2 (by rfl) ⟨387528, by rfl⟩ : syracuseStep 1033409 = 775057) B775057
theorem B967889 : Blo 642303 967889 := bstep (se 2 (by rfl) ⟨362958, by rfl⟩ : syracuseStep 967889 = 725917) B725917
theorem B967907 : Blo 642303 967907 := bstep (se 1 (by rfl) ⟨725930, by rfl⟩ : syracuseStep 967907 = 1451861) B1451861
theorem B967937 : Blo 642303 967937 := bstep (se 2 (by rfl) ⟨362976, by rfl⟩ : syracuseStep 967937 = 725953) B725953
theorem B967955 : Blo 642303 967955 := bstep (se 1 (by rfl) ⟨725966, by rfl⟩ : syracuseStep 967955 = 1451933) B1451933
theorem B2442545 : Blo 642303 2442545 := bstep (se 2 (by rfl) ⟨915954, by rfl⟩ : syracuseStep 2442545 = 1831909) B1831909
theorem B967985 : Blo 642303 967985 := bstep (se 2 (by rfl) ⟨362994, by rfl⟩ : syracuseStep 967985 = 725989) B725989
theorem B968003 : Blo 642303 968003 := bstep (se 1 (by rfl) ⟨726002, by rfl⟩ : syracuseStep 968003 = 1452005) B1452005
theorem B1885517 : Blo 642303 1885517 := bstep (se 3 (by rfl) ⟨353534, by rfl⟩ : syracuseStep 1885517 = 707069) B707069
theorem B968033 : Blo 642303 968033 := bstep (se 2 (by rfl) ⟨363012, by rfl⟩ : syracuseStep 968033 = 726025) B726025
theorem B2180465 : Blo 642303 2180465 := bstep (se 2 (by rfl) ⟨817674, by rfl⟩ : syracuseStep 2180465 = 1635349) B1635349
theorem B968051 : Blo 642303 968051 := bstep (se 1 (by rfl) ⟨726038, by rfl⟩ : syracuseStep 968051 = 1452077) B1452077
theorem B968081 : Blo 642303 968081 := bstep (se 2 (by rfl) ⟨363030, by rfl⟩ : syracuseStep 968081 = 726061) B726061
theorem B968099 : Blo 642303 968099 := bstep (se 1 (by rfl) ⟨726074, by rfl⟩ : syracuseStep 968099 = 1452149) B1452149
theorem B968129 : Blo 642303 968129 := bstep (se 2 (by rfl) ⟨363048, by rfl⟩ : syracuseStep 968129 = 726097) B726097
theorem B968147 : Blo 642303 968147 := bstep (se 1 (by rfl) ⟨726110, by rfl⟩ : syracuseStep 968147 = 1452221) B1452221
theorem B4900337 : Blo 642303 4900337 := bstep (se 2 (by rfl) ⟨1837626, by rfl⟩ : syracuseStep 4900337 = 3675253) B3675253
theorem B968177 : Blo 642303 968177 := bstep (se 2 (by rfl) ⟨363066, by rfl⟩ : syracuseStep 968177 = 726133) B726133
theorem B968195 : Blo 642303 968195 := bstep (se 1 (by rfl) ⟨726146, by rfl⟩ : syracuseStep 968195 = 1452293) B1452293
theorem B968225 : Blo 642303 968225 := bstep (se 2 (by rfl) ⟨363084, by rfl⟩ : syracuseStep 968225 = 726169) B726169
theorem B968243 : Blo 642303 968243 := bstep (se 1 (by rfl) ⟨726182, by rfl⟩ : syracuseStep 968243 = 1452365) B1452365
theorem B968273 : Blo 642303 968273 := bstep (se 2 (by rfl) ⟨363102, by rfl⟩ : syracuseStep 968273 = 726205) B726205
theorem B968291 : Blo 642303 968291 := bstep (se 1 (by rfl) ⟨726218, by rfl⟩ : syracuseStep 968291 = 1452437) B1452437
theorem B968321 : Blo 642303 968321 := bstep (se 2 (by rfl) ⟨363120, by rfl⟩ : syracuseStep 968321 = 726241) B726241
theorem B968339 : Blo 642303 968339 := bstep (se 1 (by rfl) ⟨726254, by rfl⟩ : syracuseStep 968339 = 1452509) B1452509
theorem B968369 : Blo 642303 968369 := bstep (se 2 (by rfl) ⟨363138, by rfl⟩ : syracuseStep 968369 = 726277) B726277
theorem B968387 : Blo 642303 968387 := bstep (se 1 (by rfl) ⟨726290, by rfl⟩ : syracuseStep 968387 = 1452581) B1452581
theorem B968417 : Blo 642303 968417 := bstep (se 2 (by rfl) ⟨363156, by rfl⟩ : syracuseStep 968417 = 726313) B726313
theorem B3262193 : Blo 642303 3262193 := bstep (se 2 (by rfl) ⟨1223322, by rfl⟩ : syracuseStep 3262193 = 2446645) B2446645
theorem B968435 : Blo 642303 968435 := bstep (se 1 (by rfl) ⟨726326, by rfl⟩ : syracuseStep 968435 = 1452653) B1452653
theorem B3131149 : Blo 642303 3131149 := bstep (se 3 (by rfl) ⟨587090, by rfl⟩ : syracuseStep 3131149 = 1174181) B1174181
theorem B968465 : Blo 642303 968465 := bstep (se 2 (by rfl) ⟨363174, by rfl⟩ : syracuseStep 968465 = 726349) B726349
theorem B968483 : Blo 642303 968483 := bstep (se 1 (by rfl) ⟨726362, by rfl⟩ : syracuseStep 968483 = 1452725) B1452725
theorem B968513 : Blo 642303 968513 := bstep (se 2 (by rfl) ⟨363192, by rfl⟩ : syracuseStep 968513 = 726385) B726385
theorem B2934605 : Blo 642303 2934605 := bstep (se 3 (by rfl) ⟨550238, by rfl⟩ : syracuseStep 2934605 = 1100477) B1100477
theorem B968531 : Blo 642303 968531 := bstep (se 1 (by rfl) ⟨726398, by rfl⟩ : syracuseStep 968531 = 1452797) B1452797
theorem B968561 : Blo 642303 968561 := bstep (se 2 (by rfl) ⟨363210, by rfl⟩ : syracuseStep 968561 = 726421) B726421
theorem B968579 : Blo 642303 968579 := bstep (se 1 (by rfl) ⟨726434, by rfl⟩ : syracuseStep 968579 = 1452869) B1452869
theorem B2181005 : Blo 642303 2181005 := bstep (se 3 (by rfl) ⟨408938, by rfl⟩ : syracuseStep 2181005 = 817877) B817877
theorem B968609 : Blo 642303 968609 := bstep (se 2 (by rfl) ⟨363228, by rfl⟩ : syracuseStep 968609 = 726457) B726457
theorem B968627 : Blo 642303 968627 := bstep (se 1 (by rfl) ⟨726470, by rfl⟩ : syracuseStep 968627 = 1452941) B1452941
theorem B2181059 : Blo 642303 2181059 := bstep (se 1 (by rfl) ⟨1635794, by rfl⟩ : syracuseStep 2181059 = 3271589) B3271589
theorem B6211525 : Blo 642303 6211525 := bstep (se 4 (by rfl) ⟨582330, by rfl⟩ : syracuseStep 6211525 = 1164661) B1164661
theorem B968657 : Blo 642303 968657 := bstep (se 2 (by rfl) ⟨363246, by rfl⟩ : syracuseStep 968657 = 726493) B726493
theorem B968675 : Blo 642303 968675 := bstep (se 1 (by rfl) ⟨726506, by rfl⟩ : syracuseStep 968675 = 1453013) B1453013
theorem B968705 : Blo 642303 968705 := bstep (se 2 (by rfl) ⟨363264, by rfl⟩ : syracuseStep 968705 = 726529) B726529
theorem B968723 : Blo 642303 968723 := bstep (se 1 (by rfl) ⟨726542, by rfl⟩ : syracuseStep 968723 = 1453085) B1453085
theorem B968753 : Blo 642303 968753 := bstep (se 2 (by rfl) ⟨363282, by rfl⟩ : syracuseStep 968753 = 726565) B726565
theorem B968771 : Blo 642303 968771 := bstep (se 1 (by rfl) ⟨726578, by rfl⟩ : syracuseStep 968771 = 1453157) B1453157
theorem B968801 : Blo 642303 968801 := bstep (se 2 (by rfl) ⟨363300, by rfl⟩ : syracuseStep 968801 = 726601) B726601
theorem B968819 : Blo 642303 968819 := bstep (se 1 (by rfl) ⟨726614, by rfl⟩ : syracuseStep 968819 = 1453229) B1453229
theorem B16468109 : Blo 642303 16468109 := bstep (se 3 (by rfl) ⟨3087770, by rfl⟩ : syracuseStep 16468109 = 6175541) B6175541
theorem B968849 : Blo 642303 968849 := bstep (se 2 (by rfl) ⟨363318, by rfl⟩ : syracuseStep 968849 = 726637) B726637
theorem B968867 : Blo 642303 968867 := bstep (se 1 (by rfl) ⟨726650, by rfl⟩ : syracuseStep 968867 = 1453301) B1453301
theorem B968897 : Blo 642303 968897 := bstep (se 2 (by rfl) ⟨363336, by rfl⟩ : syracuseStep 968897 = 726673) B726673
theorem B968915 : Blo 642303 968915 := bstep (se 1 (by rfl) ⟨726686, by rfl⟩ : syracuseStep 968915 = 1453373) B1453373
theorem B968945 : Blo 642303 968945 := bstep (se 2 (by rfl) ⟨363354, by rfl⟩ : syracuseStep 968945 = 726709) B726709
theorem B968963 : Blo 642303 968963 := bstep (se 1 (by rfl) ⟨726722, by rfl⟩ : syracuseStep 968963 = 1453445) B1453445
theorem B968993 : Blo 642303 968993 := bstep (se 2 (by rfl) ⟨363372, by rfl⟩ : syracuseStep 968993 = 726745) B726745
theorem B969011 : Blo 642303 969011 := bstep (se 1 (by rfl) ⟨726758, by rfl⟩ : syracuseStep 969011 = 1453517) B1453517
theorem B969041 : Blo 642303 969041 := bstep (se 2 (by rfl) ⟨363390, by rfl⟩ : syracuseStep 969041 = 726781) B726781
theorem B969059 : Blo 642303 969059 := bstep (se 1 (by rfl) ⟨726794, by rfl⟩ : syracuseStep 969059 = 1453589) B1453589
theorem B969089 : Blo 642303 969089 := bstep (se 2 (by rfl) ⟨363408, by rfl⟩ : syracuseStep 969089 = 726817) B726817
theorem B969107 : Blo 642303 969107 := bstep (se 1 (by rfl) ⟨726830, by rfl⟩ : syracuseStep 969107 = 1453661) B1453661
theorem B969137 : Blo 642303 969137 := bstep (se 2 (by rfl) ⟨363426, by rfl⟩ : syracuseStep 969137 = 726853) B726853
theorem B969155 : Blo 642303 969155 := bstep (se 1 (by rfl) ⟨726866, by rfl⟩ : syracuseStep 969155 = 1453733) B1453733
theorem B969185 : Blo 642303 969185 := bstep (se 2 (by rfl) ⟨363444, by rfl⟩ : syracuseStep 969185 = 726889) B726889
theorem B969203 : Blo 642303 969203 := bstep (se 1 (by rfl) ⟨726902, by rfl⟩ : syracuseStep 969203 = 1453805) B1453805
theorem B969233 : Blo 642303 969233 := bstep (se 2 (by rfl) ⟨363462, by rfl⟩ : syracuseStep 969233 = 726925) B726925
theorem B969251 : Blo 642303 969251 := bstep (se 1 (by rfl) ⟨726938, by rfl⟩ : syracuseStep 969251 = 1453877) B1453877
theorem B969281 : Blo 642303 969281 := bstep (se 2 (by rfl) ⟨363480, by rfl⟩ : syracuseStep 969281 = 726961) B726961
theorem B969299 : Blo 642303 969299 := bstep (se 1 (by rfl) ⟨726974, by rfl⟩ : syracuseStep 969299 = 1453949) B1453949
theorem B969329 : Blo 642303 969329 := bstep (se 2 (by rfl) ⟨363498, by rfl⟩ : syracuseStep 969329 = 726997) B726997
theorem B969347 : Blo 642303 969347 := bstep (se 1 (by rfl) ⟨727010, by rfl⟩ : syracuseStep 969347 = 1454021) B1454021
theorem B969377 : Blo 642303 969377 := bstep (se 2 (by rfl) ⟨363516, by rfl⟩ : syracuseStep 969377 = 727033) B727033
theorem B969395 : Blo 642303 969395 := bstep (se 1 (by rfl) ⟨727046, by rfl⟩ : syracuseStep 969395 = 1454093) B1454093
theorem B1034947 : Blo 642303 1034947 := bstep (se 1 (by rfl) ⟨776210, by rfl⟩ : syracuseStep 1034947 = 1552421) B1552421
theorem B969425 : Blo 642303 969425 := bstep (se 2 (by rfl) ⟨363534, by rfl⟩ : syracuseStep 969425 = 727069) B727069
theorem B2444003 : Blo 642303 2444003 := bstep (se 1 (by rfl) ⟨1833002, by rfl⟩ : syracuseStep 2444003 = 3666005) B3666005
theorem B969443 : Blo 642303 969443 := bstep (se 1 (by rfl) ⟨727082, by rfl⟩ : syracuseStep 969443 = 1454165) B1454165
theorem B7326449 : Blo 642303 7326449 := bstep (se 2 (by rfl) ⟨2747418, by rfl⟩ : syracuseStep 7326449 = 5494837) B5494837
theorem B1034993 : Blo 642303 1034993 := bstep (se 2 (by rfl) ⟨388122, by rfl⟩ : syracuseStep 1034993 = 776245) B776245
theorem B871345 : Blo 642303 871345 := bstep (se 2 (by rfl) ⟨326754, by rfl⟩ : syracuseStep 871345 = 653509) B653509
theorem B4115569 : Blo 642303 4115569 := bstep (se 2 (by rfl) ⟨1543338, by rfl⟩ : syracuseStep 4115569 = 3086677) B3086677
theorem B3263651 : Blo 642303 3263651 := bstep (se 1 (by rfl) ⟨2447738, by rfl⟩ : syracuseStep 3263651 = 4895477) B4895477
theorem B642307 : Blo 642303 642307 := bstep (se 1 (by rfl) ⟨481730, by rfl⟩ : syracuseStep 642307 = 963461) B963461
theorem B642323 : Blo 642303 642323 := bstep (se 1 (by rfl) ⟨481742, by rfl⟩ : syracuseStep 642323 = 963485) B963485
theorem B642339 : Blo 642303 642339 := bstep (se 1 (by rfl) ⟨481754, by rfl⟩ : syracuseStep 642339 = 963509) B963509
theorem B642355 : Blo 642303 642355 := bstep (se 1 (by rfl) ⟨481766, by rfl⟩ : syracuseStep 642355 = 963533) B963533
theorem B642371 : Blo 642303 642371 := bstep (se 1 (by rfl) ⟨481778, by rfl⟩ : syracuseStep 642371 = 963557) B963557
theorem B642387 : Blo 642303 642387 := bstep (se 1 (by rfl) ⟨481790, by rfl⟩ : syracuseStep 642387 = 963581) B963581
theorem B642403 : Blo 642303 642403 := bstep (se 1 (by rfl) ⟨481802, by rfl⟩ : syracuseStep 642403 = 963605) B963605
theorem B642419 : Blo 642303 642419 := bstep (se 1 (by rfl) ⟨481814, by rfl⟩ : syracuseStep 642419 = 963629) B963629
theorem B642435 : Blo 642303 642435 := bstep (se 1 (by rfl) ⟨481826, by rfl⟩ : syracuseStep 642435 = 963653) B963653
theorem B642451 : Blo 642303 642451 := bstep (se 1 (by rfl) ⟨481838, by rfl⟩ : syracuseStep 642451 = 963677) B963677
theorem B642467 : Blo 642303 642467 := bstep (se 1 (by rfl) ⟨481850, by rfl⟩ : syracuseStep 642467 = 963701) B963701
theorem B642483 : Blo 642303 642483 := bstep (se 1 (by rfl) ⟨481862, by rfl⟩ : syracuseStep 642483 = 963725) B963725
theorem B642499 : Blo 642303 642499 := bstep (se 1 (by rfl) ⟨481874, by rfl⟩ : syracuseStep 642499 = 963749) B963749
theorem B642515 : Blo 642303 642515 := bstep (se 1 (by rfl) ⟨481886, by rfl⟩ : syracuseStep 642515 = 963773) B963773
theorem B642531 : Blo 642303 642531 := bstep (se 1 (by rfl) ⟨481898, by rfl⟩ : syracuseStep 642531 = 963797) B963797
theorem B642547 : Blo 642303 642547 := bstep (se 1 (by rfl) ⟨481910, by rfl⟩ : syracuseStep 642547 = 963821) B963821
theorem B642563 : Blo 642303 642563 := bstep (se 1 (by rfl) ⟨481922, by rfl⟩ : syracuseStep 642563 = 963845) B963845
theorem B642579 : Blo 642303 642579 := bstep (se 1 (by rfl) ⟨481934, by rfl⟩ : syracuseStep 642579 = 963869) B963869
theorem B642595 : Blo 642303 642595 := bstep (se 1 (by rfl) ⟨481946, by rfl⟩ : syracuseStep 642595 = 963893) B963893
theorem B642611 : Blo 642303 642611 := bstep (se 1 (by rfl) ⟨481958, by rfl⟩ : syracuseStep 642611 = 963917) B963917
theorem B642627 : Blo 642303 642627 := bstep (se 1 (by rfl) ⟨481970, by rfl⟩ : syracuseStep 642627 = 963941) B963941
theorem B642643 : Blo 642303 642643 := bstep (se 1 (by rfl) ⟨481982, by rfl⟩ : syracuseStep 642643 = 963965) B963965
theorem B642659 : Blo 642303 642659 := bstep (se 1 (by rfl) ⟨481994, by rfl⟩ : syracuseStep 642659 = 963989) B963989
theorem B642675 : Blo 642303 642675 := bstep (se 1 (by rfl) ⟨482006, by rfl⟩ : syracuseStep 642675 = 964013) B964013
theorem B642691 : Blo 642303 642691 := bstep (se 1 (by rfl) ⟨482018, by rfl⟩ : syracuseStep 642691 = 964037) B964037
theorem B642707 : Blo 642303 642707 := bstep (se 1 (by rfl) ⟨482030, by rfl⟩ : syracuseStep 642707 = 964061) B964061
theorem B642723 : Blo 642303 642723 := bstep (se 1 (by rfl) ⟨482042, by rfl⟩ : syracuseStep 642723 = 964085) B964085
theorem B642739 : Blo 642303 642739 := bstep (se 1 (by rfl) ⟨482054, by rfl⟩ : syracuseStep 642739 = 964109) B964109
theorem B642755 : Blo 642303 642755 := bstep (se 1 (by rfl) ⟨482066, by rfl⟩ : syracuseStep 642755 = 964133) B964133
theorem B2445005 : Blo 642303 2445005 := bstep (se 3 (by rfl) ⟨458438, by rfl⟩ : syracuseStep 2445005 = 916877) B916877
theorem B642771 : Blo 642303 642771 := bstep (se 1 (by rfl) ⟨482078, by rfl⟩ : syracuseStep 642771 = 964157) B964157
theorem B1101523 : Blo 642303 1101523 := bstep (se 1 (by rfl) ⟨826142, by rfl⟩ : syracuseStep 1101523 = 1652285) B1652285
theorem B642787 : Blo 642303 642787 := bstep (se 1 (by rfl) ⟨482090, by rfl⟩ : syracuseStep 642787 = 964181) B964181
theorem B642803 : Blo 642303 642803 := bstep (se 1 (by rfl) ⟨482102, by rfl⟩ : syracuseStep 642803 = 964205) B964205
theorem B642819 : Blo 642303 642819 := bstep (se 1 (by rfl) ⟨482114, by rfl⟩ : syracuseStep 642819 = 964229) B964229
theorem B642835 : Blo 642303 642835 := bstep (se 1 (by rfl) ⟨482126, by rfl⟩ : syracuseStep 642835 = 964253) B964253
theorem B642851 : Blo 642303 642851 := bstep (se 1 (by rfl) ⟨482138, by rfl⟩ : syracuseStep 642851 = 964277) B964277
theorem B1527587 : Blo 642303 1527587 := bstep (se 1 (by rfl) ⟨1145690, by rfl⟩ : syracuseStep 1527587 = 2291381) B2291381
theorem B773923 : Blo 642303 773923 := bstep (se 1 (by rfl) ⟨580442, by rfl⟩ : syracuseStep 773923 = 1160885) B1160885
theorem B4476707 : Blo 642303 4476707 := bstep (se 1 (by rfl) ⟨3357530, by rfl⟩ : syracuseStep 4476707 = 6715061) B6715061
theorem B2477873 : Blo 642303 2477873 := bstep (se 2 (by rfl) ⟨929202, by rfl⟩ : syracuseStep 2477873 = 1858405) B1858405
theorem B642867 : Blo 642303 642867 := bstep (se 1 (by rfl) ⟨482150, by rfl⟩ : syracuseStep 642867 = 964301) B964301
theorem B642883 : Blo 642303 642883 := bstep (se 1 (by rfl) ⟨482162, by rfl⟩ : syracuseStep 642883 = 964325) B964325
theorem B642899 : Blo 642303 642899 := bstep (se 1 (by rfl) ⟨482174, by rfl⟩ : syracuseStep 642899 = 964349) B964349
theorem B642915 : Blo 642303 642915 := bstep (se 1 (by rfl) ⟨482186, by rfl⟩ : syracuseStep 642915 = 964373) B964373
theorem B642931 : Blo 642303 642931 := bstep (se 1 (by rfl) ⟨482198, by rfl⟩ : syracuseStep 642931 = 964397) B964397
theorem B642947 : Blo 642303 642947 := bstep (se 1 (by rfl) ⟨482210, by rfl⟩ : syracuseStep 642947 = 964421) B964421
theorem B774019 : Blo 642303 774019 := bstep (se 1 (by rfl) ⟨580514, by rfl⟩ : syracuseStep 774019 = 1161029) B1161029
theorem B642963 : Blo 642303 642963 := bstep (se 1 (by rfl) ⟨482222, by rfl⟩ : syracuseStep 642963 = 964445) B964445
theorem B642979 : Blo 642303 642979 := bstep (se 1 (by rfl) ⟨482234, by rfl⟩ : syracuseStep 642979 = 964469) B964469
theorem B642995 : Blo 642303 642995 := bstep (se 1 (by rfl) ⟨482246, by rfl⟩ : syracuseStep 642995 = 964493) B964493
theorem B643011 : Blo 642303 643011 := bstep (se 1 (by rfl) ⟨482258, by rfl⟩ : syracuseStep 643011 = 964517) B964517
theorem B3264461 : Blo 642303 3264461 := bstep (se 3 (by rfl) ⟨612086, by rfl⟩ : syracuseStep 3264461 = 1224173) B1224173
theorem B1626065 : Blo 642303 1626065 := bstep (se 2 (by rfl) ⟨609774, by rfl⟩ : syracuseStep 1626065 = 1219549) B1219549
theorem B643027 : Blo 642303 643027 := bstep (se 1 (by rfl) ⟨482270, by rfl⟩ : syracuseStep 643027 = 964541) B964541
theorem B643043 : Blo 642303 643043 := bstep (se 1 (by rfl) ⟨482282, by rfl⟩ : syracuseStep 643043 = 964565) B964565
theorem B643059 : Blo 642303 643059 := bstep (se 1 (by rfl) ⟨482294, by rfl⟩ : syracuseStep 643059 = 964589) B964589
theorem B1626115 : Blo 642303 1626115 := bstep (se 1 (by rfl) ⟨1219586, by rfl⟩ : syracuseStep 1626115 = 2439173) B2439173
theorem B643075 : Blo 642303 643075 := bstep (se 1 (by rfl) ⟨482306, by rfl⟩ : syracuseStep 643075 = 964613) B964613
theorem B643091 : Blo 642303 643091 := bstep (se 1 (by rfl) ⟨482318, by rfl⟩ : syracuseStep 643091 = 964637) B964637
theorem B643107 : Blo 642303 643107 := bstep (se 1 (by rfl) ⟨482330, by rfl⟩ : syracuseStep 643107 = 964661) B964661
theorem B643123 : Blo 642303 643123 := bstep (se 1 (by rfl) ⟨482342, by rfl⟩ : syracuseStep 643123 = 964685) B964685
theorem B643139 : Blo 642303 643139 := bstep (se 1 (by rfl) ⟨482354, by rfl⟩ : syracuseStep 643139 = 964709) B964709
theorem B643155 : Blo 642303 643155 := bstep (se 1 (by rfl) ⟨482366, by rfl⟩ : syracuseStep 643155 = 964733) B964733
theorem B643171 : Blo 642303 643171 := bstep (se 1 (by rfl) ⟨482378, by rfl⟩ : syracuseStep 643171 = 964757) B964757
theorem B643187 : Blo 642303 643187 := bstep (se 1 (by rfl) ⟨482390, by rfl⟩ : syracuseStep 643187 = 964781) B964781
theorem B643203 : Blo 642303 643203 := bstep (se 1 (by rfl) ⟨482402, by rfl⟩ : syracuseStep 643203 = 964805) B964805
theorem B1626257 : Blo 642303 1626257 := bstep (se 2 (by rfl) ⟨609846, by rfl⟩ : syracuseStep 1626257 = 1219693) B1219693
theorem B643219 : Blo 642303 643219 := bstep (se 1 (by rfl) ⟨482414, by rfl⟩ : syracuseStep 643219 = 964829) B964829
theorem B643235 : Blo 642303 643235 := bstep (se 1 (by rfl) ⟨482426, by rfl⟩ : syracuseStep 643235 = 964853) B964853
theorem B643251 : Blo 642303 643251 := bstep (se 1 (by rfl) ⟨482438, by rfl⟩ : syracuseStep 643251 = 964877) B964877
theorem B643267 : Blo 642303 643267 := bstep (se 1 (by rfl) ⟨482450, by rfl⟩ : syracuseStep 643267 = 964901) B964901
theorem B643283 : Blo 642303 643283 := bstep (se 1 (by rfl) ⟨482462, by rfl⟩ : syracuseStep 643283 = 964925) B964925
theorem B643299 : Blo 642303 643299 := bstep (se 1 (by rfl) ⟨482474, by rfl⟩ : syracuseStep 643299 = 964949) B964949
theorem B643315 : Blo 642303 643315 := bstep (se 1 (by rfl) ⟨482486, by rfl⟩ : syracuseStep 643315 = 964973) B964973
theorem B643331 : Blo 642303 643331 := bstep (se 1 (by rfl) ⟨482498, by rfl⟩ : syracuseStep 643331 = 964997) B964997
theorem B774403 : Blo 642303 774403 := bstep (se 1 (by rfl) ⟨580802, by rfl⟩ : syracuseStep 774403 = 1161605) B1161605
theorem B643347 : Blo 642303 643347 := bstep (se 1 (by rfl) ⟨482510, by rfl⟩ : syracuseStep 643347 = 965021) B965021
theorem B643363 : Blo 642303 643363 := bstep (se 1 (by rfl) ⟨482522, by rfl⟩ : syracuseStep 643363 = 965045) B965045
theorem B643379 : Blo 642303 643379 := bstep (se 1 (by rfl) ⟨482534, by rfl⟩ : syracuseStep 643379 = 965069) B965069
theorem B643395 : Blo 642303 643395 := bstep (se 1 (by rfl) ⟨482546, by rfl⟩ : syracuseStep 643395 = 965093) B965093
theorem B643411 : Blo 642303 643411 := bstep (se 1 (by rfl) ⟨482558, by rfl⟩ : syracuseStep 643411 = 965117) B965117
theorem B643427 : Blo 642303 643427 := bstep (se 1 (by rfl) ⟨482570, by rfl⟩ : syracuseStep 643427 = 965141) B965141
theorem B643443 : Blo 642303 643443 := bstep (se 1 (by rfl) ⟨482582, by rfl⟩ : syracuseStep 643443 = 965165) B965165
theorem B643459 : Blo 642303 643459 := bstep (se 1 (by rfl) ⟨482594, by rfl⟩ : syracuseStep 643459 = 965189) B965189
theorem B643475 : Blo 642303 643475 := bstep (se 1 (by rfl) ⟨482606, by rfl⟩ : syracuseStep 643475 = 965213) B965213
theorem B643491 : Blo 642303 643491 := bstep (se 1 (by rfl) ⟨482618, by rfl⟩ : syracuseStep 643491 = 965237) B965237
theorem B643507 : Blo 642303 643507 := bstep (se 1 (by rfl) ⟨482630, by rfl⟩ : syracuseStep 643507 = 965261) B965261
theorem B643523 : Blo 642303 643523 := bstep (se 1 (by rfl) ⟨482642, by rfl⟩ : syracuseStep 643523 = 965285) B965285
theorem B643539 : Blo 642303 643539 := bstep (se 1 (by rfl) ⟨482654, by rfl⟩ : syracuseStep 643539 = 965309) B965309
theorem B643555 : Blo 642303 643555 := bstep (se 1 (by rfl) ⟨482666, by rfl⟩ : syracuseStep 643555 = 965333) B965333
theorem B643571 : Blo 642303 643571 := bstep (se 1 (by rfl) ⟨482678, by rfl⟩ : syracuseStep 643571 = 965357) B965357
theorem B643587 : Blo 642303 643587 := bstep (se 1 (by rfl) ⟨482690, by rfl⟩ : syracuseStep 643587 = 965381) B965381
theorem B643603 : Blo 642303 643603 := bstep (se 1 (by rfl) ⟨482702, by rfl⟩ : syracuseStep 643603 = 965405) B965405
theorem B643619 : Blo 642303 643619 := bstep (se 1 (by rfl) ⟨482714, by rfl⟩ : syracuseStep 643619 = 965429) B965429
theorem B643635 : Blo 642303 643635 := bstep (se 1 (by rfl) ⟨482726, by rfl⟩ : syracuseStep 643635 = 965453) B965453
theorem B643651 : Blo 642303 643651 := bstep (se 1 (by rfl) ⟨482738, by rfl⟩ : syracuseStep 643651 = 965477) B965477
theorem B643667 : Blo 642303 643667 := bstep (se 1 (by rfl) ⟨482750, by rfl⟩ : syracuseStep 643667 = 965501) B965501
theorem B643683 : Blo 642303 643683 := bstep (se 1 (by rfl) ⟨482762, by rfl⟩ : syracuseStep 643683 = 965525) B965525
theorem B643699 : Blo 642303 643699 := bstep (se 1 (by rfl) ⟨482774, by rfl⟩ : syracuseStep 643699 = 965549) B965549
theorem B643715 : Blo 642303 643715 := bstep (se 1 (by rfl) ⟨482786, by rfl⟩ : syracuseStep 643715 = 965573) B965573
theorem B643731 : Blo 642303 643731 := bstep (se 1 (by rfl) ⟨482798, by rfl⟩ : syracuseStep 643731 = 965597) B965597
theorem B643747 : Blo 642303 643747 := bstep (se 1 (by rfl) ⟨482810, by rfl⟩ : syracuseStep 643747 = 965621) B965621
theorem B643763 : Blo 642303 643763 := bstep (se 1 (by rfl) ⟨482822, by rfl⟩ : syracuseStep 643763 = 965645) B965645
theorem B643779 : Blo 642303 643779 := bstep (se 1 (by rfl) ⟨482834, by rfl⟩ : syracuseStep 643779 = 965669) B965669
theorem B643795 : Blo 642303 643795 := bstep (se 1 (by rfl) ⟨482846, by rfl⟩ : syracuseStep 643795 = 965693) B965693
theorem B643811 : Blo 642303 643811 := bstep (se 1 (by rfl) ⟨482858, by rfl⟩ : syracuseStep 643811 = 965717) B965717
theorem B643827 : Blo 642303 643827 := bstep (se 1 (by rfl) ⟨482870, by rfl⟩ : syracuseStep 643827 = 965741) B965741
theorem B643843 : Blo 642303 643843 := bstep (se 1 (by rfl) ⟨482882, by rfl⟩ : syracuseStep 643843 = 965765) B965765
theorem B643859 : Blo 642303 643859 := bstep (se 1 (by rfl) ⟨482894, by rfl⟩ : syracuseStep 643859 = 965789) B965789
theorem B643875 : Blo 642303 643875 := bstep (se 1 (by rfl) ⟨482906, by rfl⟩ : syracuseStep 643875 = 965813) B965813
theorem B643891 : Blo 642303 643891 := bstep (se 1 (by rfl) ⟨482918, by rfl⟩ : syracuseStep 643891 = 965837) B965837
theorem B643907 : Blo 642303 643907 := bstep (se 1 (by rfl) ⟨482930, by rfl⟩ : syracuseStep 643907 = 965861) B965861
theorem B643923 : Blo 642303 643923 := bstep (se 1 (by rfl) ⟨482942, by rfl⟩ : syracuseStep 643923 = 965885) B965885
theorem B643939 : Blo 642303 643939 := bstep (se 1 (by rfl) ⟨482954, by rfl⟩ : syracuseStep 643939 = 965909) B965909
theorem B643955 : Blo 642303 643955 := bstep (se 1 (by rfl) ⟨482966, by rfl⟩ : syracuseStep 643955 = 965933) B965933
theorem B643971 : Blo 642303 643971 := bstep (se 1 (by rfl) ⟨482978, by rfl⟩ : syracuseStep 643971 = 965957) B965957
theorem B643987 : Blo 642303 643987 := bstep (se 1 (by rfl) ⟨482990, by rfl⟩ : syracuseStep 643987 = 965981) B965981
theorem B644003 : Blo 642303 644003 := bstep (se 1 (by rfl) ⟨483002, by rfl⟩ : syracuseStep 644003 = 966005) B966005
theorem B644019 : Blo 642303 644019 := bstep (se 1 (by rfl) ⟨483014, by rfl⟩ : syracuseStep 644019 = 966029) B966029
theorem B644035 : Blo 642303 644035 := bstep (se 1 (by rfl) ⟨483026, by rfl⟩ : syracuseStep 644035 = 966053) B966053
theorem B644051 : Blo 642303 644051 := bstep (se 1 (by rfl) ⟨483038, by rfl⟩ : syracuseStep 644051 = 966077) B966077
theorem B644067 : Blo 642303 644067 := bstep (se 1 (by rfl) ⟨483050, by rfl⟩ : syracuseStep 644067 = 966101) B966101
theorem B644083 : Blo 642303 644083 := bstep (se 1 (by rfl) ⟨483062, by rfl⟩ : syracuseStep 644083 = 966125) B966125
theorem B644099 : Blo 642303 644099 := bstep (se 1 (by rfl) ⟨483074, by rfl⟩ : syracuseStep 644099 = 966149) B966149
theorem B644115 : Blo 642303 644115 := bstep (se 1 (by rfl) ⟨483086, by rfl⟩ : syracuseStep 644115 = 966173) B966173
theorem B644131 : Blo 642303 644131 := bstep (se 1 (by rfl) ⟨483098, by rfl⟩ : syracuseStep 644131 = 966197) B966197
theorem B644147 : Blo 642303 644147 := bstep (se 1 (by rfl) ⟨483110, by rfl⟩ : syracuseStep 644147 = 966221) B966221
theorem B644163 : Blo 642303 644163 := bstep (se 1 (by rfl) ⟨483122, by rfl⟩ : syracuseStep 644163 = 966245) B966245
theorem B644179 : Blo 642303 644179 := bstep (se 1 (by rfl) ⟨483134, by rfl⟩ : syracuseStep 644179 = 966269) B966269
theorem B644195 : Blo 642303 644195 := bstep (se 1 (by rfl) ⟨483146, by rfl⟩ : syracuseStep 644195 = 966293) B966293
theorem B1627249 : Blo 642303 1627249 := bstep (se 2 (by rfl) ⟨610218, by rfl⟩ : syracuseStep 1627249 = 1220437) B1220437
theorem B644211 : Blo 642303 644211 := bstep (se 1 (by rfl) ⟨483158, by rfl⟩ : syracuseStep 644211 = 966317) B966317
theorem B644227 : Blo 642303 644227 := bstep (se 1 (by rfl) ⟨483170, by rfl⟩ : syracuseStep 644227 = 966341) B966341
theorem B644243 : Blo 642303 644243 := bstep (se 1 (by rfl) ⟨483182, by rfl⟩ : syracuseStep 644243 = 966365) B966365
theorem B644259 : Blo 642303 644259 := bstep (se 1 (by rfl) ⟨483194, by rfl⟩ : syracuseStep 644259 = 966389) B966389
theorem B644275 : Blo 642303 644275 := bstep (se 1 (by rfl) ⟨483206, by rfl⟩ : syracuseStep 644275 = 966413) B966413
theorem B644291 : Blo 642303 644291 := bstep (se 1 (by rfl) ⟨483218, by rfl⟩ : syracuseStep 644291 = 966437) B966437
theorem B644307 : Blo 642303 644307 := bstep (se 1 (by rfl) ⟨483230, by rfl⟩ : syracuseStep 644307 = 966461) B966461
theorem B644323 : Blo 642303 644323 := bstep (se 1 (by rfl) ⟨483242, by rfl⟩ : syracuseStep 644323 = 966485) B966485
theorem B644339 : Blo 642303 644339 := bstep (se 1 (by rfl) ⟨483254, by rfl⟩ : syracuseStep 644339 = 966509) B966509
theorem B644355 : Blo 642303 644355 := bstep (se 1 (by rfl) ⟨483266, by rfl⟩ : syracuseStep 644355 = 966533) B966533
theorem B644371 : Blo 642303 644371 := bstep (se 1 (by rfl) ⟨483278, by rfl⟩ : syracuseStep 644371 = 966557) B966557
theorem B644387 : Blo 642303 644387 := bstep (se 1 (by rfl) ⟨483290, by rfl⟩ : syracuseStep 644387 = 966581) B966581
theorem B644403 : Blo 642303 644403 := bstep (se 1 (by rfl) ⟨483302, by rfl⟩ : syracuseStep 644403 = 966605) B966605
theorem B644419 : Blo 642303 644419 := bstep (se 1 (by rfl) ⟨483314, by rfl⟩ : syracuseStep 644419 = 966629) B966629
theorem B644435 : Blo 642303 644435 := bstep (se 1 (by rfl) ⟨483326, by rfl⟩ : syracuseStep 644435 = 966653) B966653
theorem B644451 : Blo 642303 644451 := bstep (se 1 (by rfl) ⟨483338, by rfl⟩ : syracuseStep 644451 = 966677) B966677
theorem B644467 : Blo 642303 644467 := bstep (se 1 (by rfl) ⟨483350, by rfl⟩ : syracuseStep 644467 = 966701) B966701
theorem B1627523 : Blo 642303 1627523 := bstep (se 1 (by rfl) ⟨1220642, by rfl⟩ : syracuseStep 1627523 = 2441285) B2441285
theorem B644483 : Blo 642303 644483 := bstep (se 1 (by rfl) ⟨483362, by rfl⟩ : syracuseStep 644483 = 966725) B966725
theorem B644499 : Blo 642303 644499 := bstep (se 1 (by rfl) ⟨483374, by rfl⟩ : syracuseStep 644499 = 966749) B966749
theorem B644515 : Blo 642303 644515 := bstep (se 1 (by rfl) ⟨483386, by rfl⟩ : syracuseStep 644515 = 966773) B966773
theorem B644531 : Blo 642303 644531 := bstep (se 1 (by rfl) ⟨483398, by rfl⟩ : syracuseStep 644531 = 966797) B966797
theorem B644547 : Blo 642303 644547 := bstep (se 1 (by rfl) ⟨483410, by rfl⟩ : syracuseStep 644547 = 966821) B966821
theorem B644563 : Blo 642303 644563 := bstep (se 1 (by rfl) ⟨483422, by rfl⟩ : syracuseStep 644563 = 966845) B966845
theorem B644579 : Blo 642303 644579 := bstep (se 1 (by rfl) ⟨483434, by rfl⟩ : syracuseStep 644579 = 966869) B966869
theorem B644595 : Blo 642303 644595 := bstep (se 1 (by rfl) ⟨483446, by rfl⟩ : syracuseStep 644595 = 966893) B966893
theorem B644611 : Blo 642303 644611 := bstep (se 1 (by rfl) ⟨483458, by rfl⟩ : syracuseStep 644611 = 966917) B966917
theorem B644627 : Blo 642303 644627 := bstep (se 1 (by rfl) ⟨483470, by rfl⟩ : syracuseStep 644627 = 966941) B966941
theorem B644643 : Blo 642303 644643 := bstep (se 1 (by rfl) ⟨483482, by rfl⟩ : syracuseStep 644643 = 966965) B966965
theorem B644659 : Blo 642303 644659 := bstep (se 1 (by rfl) ⟨483494, by rfl⟩ : syracuseStep 644659 = 966989) B966989
theorem B1627715 : Blo 642303 1627715 := bstep (se 1 (by rfl) ⟨1220786, by rfl⟩ : syracuseStep 1627715 = 2441573) B2441573
theorem B644675 : Blo 642303 644675 := bstep (se 1 (by rfl) ⟨483506, by rfl⟩ : syracuseStep 644675 = 967013) B967013
theorem B644691 : Blo 642303 644691 := bstep (se 1 (by rfl) ⟨483518, by rfl⟩ : syracuseStep 644691 = 967037) B967037
theorem B644707 : Blo 642303 644707 := bstep (se 1 (by rfl) ⟨483530, by rfl⟩ : syracuseStep 644707 = 967061) B967061
theorem B644723 : Blo 642303 644723 := bstep (se 1 (by rfl) ⟨483542, by rfl⟩ : syracuseStep 644723 = 967085) B967085
theorem B644739 : Blo 642303 644739 := bstep (se 1 (by rfl) ⟨483554, by rfl⟩ : syracuseStep 644739 = 967109) B967109
theorem B644755 : Blo 642303 644755 := bstep (se 1 (by rfl) ⟨483566, by rfl⟩ : syracuseStep 644755 = 967133) B967133
theorem B644771 : Blo 642303 644771 := bstep (se 1 (by rfl) ⟨483578, by rfl⟩ : syracuseStep 644771 = 967157) B967157
theorem B644787 : Blo 642303 644787 := bstep (se 1 (by rfl) ⟨483590, by rfl⟩ : syracuseStep 644787 = 967181) B967181
theorem B644803 : Blo 642303 644803 := bstep (se 1 (by rfl) ⟨483602, by rfl⟩ : syracuseStep 644803 = 967205) B967205
theorem B644819 : Blo 642303 644819 := bstep (se 1 (by rfl) ⟨483614, by rfl⟩ : syracuseStep 644819 = 967229) B967229
theorem B644835 : Blo 642303 644835 := bstep (se 1 (by rfl) ⟨483626, by rfl⟩ : syracuseStep 644835 = 967253) B967253
theorem B644851 : Blo 642303 644851 := bstep (se 1 (by rfl) ⟨483638, by rfl⟩ : syracuseStep 644851 = 967277) B967277
theorem B644867 : Blo 642303 644867 := bstep (se 1 (by rfl) ⟨483650, by rfl⟩ : syracuseStep 644867 = 967301) B967301
theorem B2447117 : Blo 642303 2447117 := bstep (se 3 (by rfl) ⟨458834, by rfl⟩ : syracuseStep 2447117 = 917669) B917669
theorem B644883 : Blo 642303 644883 := bstep (se 1 (by rfl) ⟨483662, by rfl⟩ : syracuseStep 644883 = 967325) B967325
theorem B644899 : Blo 642303 644899 := bstep (se 1 (by rfl) ⟨483674, by rfl⟩ : syracuseStep 644899 = 967349) B967349
theorem B644915 : Blo 642303 644915 := bstep (se 1 (by rfl) ⟨483686, by rfl⟩ : syracuseStep 644915 = 967373) B967373
theorem B644931 : Blo 642303 644931 := bstep (se 1 (by rfl) ⟨483698, by rfl⟩ : syracuseStep 644931 = 967397) B967397
theorem B644947 : Blo 642303 644947 := bstep (se 1 (by rfl) ⟨483710, by rfl⟩ : syracuseStep 644947 = 967421) B967421
theorem B644963 : Blo 642303 644963 := bstep (se 1 (by rfl) ⟨483722, by rfl⟩ : syracuseStep 644963 = 967445) B967445
theorem B644979 : Blo 642303 644979 := bstep (se 1 (by rfl) ⟨483734, by rfl⟩ : syracuseStep 644979 = 967469) B967469
theorem B644995 : Blo 642303 644995 := bstep (se 1 (by rfl) ⟨483746, by rfl⟩ : syracuseStep 644995 = 967493) B967493
theorem B645011 : Blo 642303 645011 := bstep (se 1 (by rfl) ⟨483758, by rfl⟩ : syracuseStep 645011 = 967517) B967517
theorem B645027 : Blo 642303 645027 := bstep (se 1 (by rfl) ⟨483770, by rfl⟩ : syracuseStep 645027 = 967541) B967541
theorem B645043 : Blo 642303 645043 := bstep (se 1 (by rfl) ⟨483782, by rfl⟩ : syracuseStep 645043 = 967565) B967565
theorem B645059 : Blo 642303 645059 := bstep (se 1 (by rfl) ⟨483794, by rfl⟩ : syracuseStep 645059 = 967589) B967589
theorem B645075 : Blo 642303 645075 := bstep (se 1 (by rfl) ⟨483806, by rfl⟩ : syracuseStep 645075 = 967613) B967613
theorem B645091 : Blo 642303 645091 := bstep (se 1 (by rfl) ⟨483818, by rfl⟩ : syracuseStep 645091 = 967637) B967637
theorem B645107 : Blo 642303 645107 := bstep (se 1 (by rfl) ⟨483830, by rfl⟩ : syracuseStep 645107 = 967661) B967661
theorem B645123 : Blo 642303 645123 := bstep (se 1 (by rfl) ⟨483842, by rfl⟩ : syracuseStep 645123 = 967685) B967685
theorem B645139 : Blo 642303 645139 := bstep (se 1 (by rfl) ⟨483854, by rfl⟩ : syracuseStep 645139 = 967709) B967709
theorem B645155 : Blo 642303 645155 := bstep (se 1 (by rfl) ⟨483866, by rfl⟩ : syracuseStep 645155 = 967733) B967733
theorem B645171 : Blo 642303 645171 := bstep (se 1 (by rfl) ⟨483878, by rfl⟩ : syracuseStep 645171 = 967757) B967757
theorem B645187 : Blo 642303 645187 := bstep (se 1 (by rfl) ⟨483890, by rfl⟩ : syracuseStep 645187 = 967781) B967781
theorem B645203 : Blo 642303 645203 := bstep (se 1 (by rfl) ⟨483902, by rfl⟩ : syracuseStep 645203 = 967805) B967805
theorem B645219 : Blo 642303 645219 := bstep (se 1 (by rfl) ⟨483914, by rfl⟩ : syracuseStep 645219 = 967829) B967829
theorem B645235 : Blo 642303 645235 := bstep (se 1 (by rfl) ⟨483926, by rfl⟩ : syracuseStep 645235 = 967853) B967853
theorem B1857667 : Blo 642303 1857667 := bstep (se 1 (by rfl) ⟨1393250, by rfl⟩ : syracuseStep 1857667 = 2786501) B2786501
theorem B645251 : Blo 642303 645251 := bstep (se 1 (by rfl) ⟨483938, by rfl⟩ : syracuseStep 645251 = 967877) B967877
theorem B645267 : Blo 642303 645267 := bstep (se 1 (by rfl) ⟨483950, by rfl⟩ : syracuseStep 645267 = 967901) B967901
theorem B645283 : Blo 642303 645283 := bstep (se 1 (by rfl) ⟨483962, by rfl⟩ : syracuseStep 645283 = 967925) B967925
theorem B645299 : Blo 642303 645299 := bstep (se 1 (by rfl) ⟨483974, by rfl⟩ : syracuseStep 645299 = 967949) B967949
theorem B645315 : Blo 642303 645315 := bstep (se 1 (by rfl) ⟨483986, by rfl⟩ : syracuseStep 645315 = 967973) B967973
theorem B645331 : Blo 642303 645331 := bstep (se 1 (by rfl) ⟨483998, by rfl⟩ : syracuseStep 645331 = 967997) B967997
theorem B645347 : Blo 642303 645347 := bstep (se 1 (by rfl) ⟨484010, by rfl⟩ : syracuseStep 645347 = 968021) B968021
theorem B645363 : Blo 642303 645363 := bstep (se 1 (by rfl) ⟨484022, by rfl⟩ : syracuseStep 645363 = 968045) B968045
theorem B645379 : Blo 642303 645379 := bstep (se 1 (by rfl) ⟨484034, by rfl⟩ : syracuseStep 645379 = 968069) B968069
theorem B645395 : Blo 642303 645395 := bstep (se 1 (by rfl) ⟨484046, by rfl⟩ : syracuseStep 645395 = 968093) B968093
theorem B645411 : Blo 642303 645411 := bstep (se 1 (by rfl) ⟨484058, by rfl⟩ : syracuseStep 645411 = 968117) B968117
theorem B645427 : Blo 642303 645427 := bstep (se 1 (by rfl) ⟨484070, by rfl⟩ : syracuseStep 645427 = 968141) B968141
theorem B645443 : Blo 642303 645443 := bstep (se 1 (by rfl) ⟨484082, by rfl⟩ : syracuseStep 645443 = 968165) B968165
theorem B645459 : Blo 642303 645459 := bstep (se 1 (by rfl) ⟨484094, by rfl⟩ : syracuseStep 645459 = 968189) B968189
theorem B645475 : Blo 642303 645475 := bstep (se 1 (by rfl) ⟨484106, by rfl⟩ : syracuseStep 645475 = 968213) B968213
theorem B645491 : Blo 642303 645491 := bstep (se 1 (by rfl) ⟨484118, by rfl⟩ : syracuseStep 645491 = 968237) B968237
theorem B645507 : Blo 642303 645507 := bstep (se 1 (by rfl) ⟨484130, by rfl⟩ : syracuseStep 645507 = 968261) B968261
theorem B3660173 : Blo 642303 3660173 := bstep (se 3 (by rfl) ⟨686282, by rfl⟩ : syracuseStep 3660173 = 1372565) B1372565
theorem B645523 : Blo 642303 645523 := bstep (se 1 (by rfl) ⟨484142, by rfl⟩ : syracuseStep 645523 = 968285) B968285
theorem B645539 : Blo 642303 645539 := bstep (se 1 (by rfl) ⟨484154, by rfl⟩ : syracuseStep 645539 = 968309) B968309
theorem B645555 : Blo 642303 645555 := bstep (se 1 (by rfl) ⟨484166, by rfl⟩ : syracuseStep 645555 = 968333) B968333
theorem B645571 : Blo 642303 645571 := bstep (se 1 (by rfl) ⟨484178, by rfl⟩ : syracuseStep 645571 = 968357) B968357
theorem B645587 : Blo 642303 645587 := bstep (se 1 (by rfl) ⟨484190, by rfl⟩ : syracuseStep 645587 = 968381) B968381
theorem B645603 : Blo 642303 645603 := bstep (se 1 (by rfl) ⟨484202, by rfl⟩ : syracuseStep 645603 = 968405) B968405
theorem B1628657 : Blo 642303 1628657 := bstep (se 2 (by rfl) ⟨610746, by rfl⟩ : syracuseStep 1628657 = 1221493) B1221493
theorem B645619 : Blo 642303 645619 := bstep (se 1 (by rfl) ⟨484214, by rfl⟩ : syracuseStep 645619 = 968429) B968429
theorem B645635 : Blo 642303 645635 := bstep (se 1 (by rfl) ⟨484226, by rfl⟩ : syracuseStep 645635 = 968453) B968453
theorem B645651 : Blo 642303 645651 := bstep (se 1 (by rfl) ⟨484238, by rfl⟩ : syracuseStep 645651 = 968477) B968477
theorem B1628707 : Blo 642303 1628707 := bstep (se 1 (by rfl) ⟨1221530, by rfl⟩ : syracuseStep 1628707 = 2443061) B2443061
theorem B645667 : Blo 642303 645667 := bstep (se 1 (by rfl) ⟨484250, by rfl⟩ : syracuseStep 645667 = 968501) B968501
theorem B2447921 : Blo 642303 2447921 := bstep (se 2 (by rfl) ⟨917970, by rfl⟩ : syracuseStep 2447921 = 1835941) B1835941
theorem B645683 : Blo 642303 645683 := bstep (se 1 (by rfl) ⟨484262, by rfl⟩ : syracuseStep 645683 = 968525) B968525
theorem B645699 : Blo 642303 645699 := bstep (se 1 (by rfl) ⟨484274, by rfl⟩ : syracuseStep 645699 = 968549) B968549
theorem B645715 : Blo 642303 645715 := bstep (se 1 (by rfl) ⟨484286, by rfl⟩ : syracuseStep 645715 = 968573) B968573
theorem B645731 : Blo 642303 645731 := bstep (se 1 (by rfl) ⟨484298, by rfl⟩ : syracuseStep 645731 = 968597) B968597
theorem B645747 : Blo 642303 645747 := bstep (se 1 (by rfl) ⟨484310, by rfl⟩ : syracuseStep 645747 = 968621) B968621
theorem B645763 : Blo 642303 645763 := bstep (se 1 (by rfl) ⟨484322, by rfl⟩ : syracuseStep 645763 = 968645) B968645
theorem B645779 : Blo 642303 645779 := bstep (se 1 (by rfl) ⟨484334, by rfl⟩ : syracuseStep 645779 = 968669) B968669
theorem B645795 : Blo 642303 645795 := bstep (se 1 (by rfl) ⟨484346, by rfl⟩ : syracuseStep 645795 = 968693) B968693
theorem B1628849 : Blo 642303 1628849 := bstep (se 2 (by rfl) ⟨610818, by rfl⟩ : syracuseStep 1628849 = 1221637) B1221637
theorem B645811 : Blo 642303 645811 := bstep (se 1 (by rfl) ⟨484358, by rfl⟩ : syracuseStep 645811 = 968717) B968717
theorem B645827 : Blo 642303 645827 := bstep (se 1 (by rfl) ⟨484370, by rfl⟩ : syracuseStep 645827 = 968741) B968741
theorem B645843 : Blo 642303 645843 := bstep (se 1 (by rfl) ⟨484382, by rfl⟩ : syracuseStep 645843 = 968765) B968765
theorem B645859 : Blo 642303 645859 := bstep (se 1 (by rfl) ⟨484394, by rfl⟩ : syracuseStep 645859 = 968789) B968789
theorem B645875 : Blo 642303 645875 := bstep (se 1 (by rfl) ⟨484406, by rfl⟩ : syracuseStep 645875 = 968813) B968813
theorem B645891 : Blo 642303 645891 := bstep (se 1 (by rfl) ⟨484418, by rfl⟩ : syracuseStep 645891 = 968837) B968837
theorem B645907 : Blo 642303 645907 := bstep (se 1 (by rfl) ⟨484430, by rfl⟩ : syracuseStep 645907 = 968861) B968861
theorem B645923 : Blo 642303 645923 := bstep (se 1 (by rfl) ⟨484442, by rfl⟩ : syracuseStep 645923 = 968885) B968885
theorem B3267377 : Blo 642303 3267377 := bstep (se 2 (by rfl) ⟨1225266, by rfl⟩ : syracuseStep 3267377 = 2450533) B2450533
theorem B645939 : Blo 642303 645939 := bstep (se 1 (by rfl) ⟨484454, by rfl⟩ : syracuseStep 645939 = 968909) B968909
theorem B645955 : Blo 642303 645955 := bstep (se 1 (by rfl) ⟨484466, by rfl⟩ : syracuseStep 645955 = 968933) B968933
theorem B645971 : Blo 642303 645971 := bstep (se 1 (by rfl) ⟨484478, by rfl⟩ : syracuseStep 645971 = 968957) B968957
theorem B645987 : Blo 642303 645987 := bstep (se 1 (by rfl) ⟨484490, by rfl⟩ : syracuseStep 645987 = 968981) B968981
theorem B646003 : Blo 642303 646003 := bstep (se 1 (by rfl) ⟨484502, by rfl⟩ : syracuseStep 646003 = 969005) B969005
theorem B646019 : Blo 642303 646019 := bstep (se 1 (by rfl) ⟨484514, by rfl⟩ : syracuseStep 646019 = 969029) B969029
theorem B646035 : Blo 642303 646035 := bstep (se 1 (by rfl) ⟨484526, by rfl⟩ : syracuseStep 646035 = 969053) B969053
theorem B646051 : Blo 642303 646051 := bstep (se 1 (by rfl) ⟨484538, by rfl⟩ : syracuseStep 646051 = 969077) B969077
theorem B646067 : Blo 642303 646067 := bstep (se 1 (by rfl) ⟨484550, by rfl⟩ : syracuseStep 646067 = 969101) B969101
theorem B1956803 : Blo 642303 1956803 := bstep (se 1 (by rfl) ⟨1467602, by rfl⟩ : syracuseStep 1956803 = 2935205) B2935205
theorem B646083 : Blo 642303 646083 := bstep (se 1 (by rfl) ⟨484562, by rfl⟩ : syracuseStep 646083 = 969125) B969125
theorem B646099 : Blo 642303 646099 := bstep (se 1 (by rfl) ⟨484574, by rfl⟩ : syracuseStep 646099 = 969149) B969149
theorem B646115 : Blo 642303 646115 := bstep (se 1 (by rfl) ⟨484586, by rfl⟩ : syracuseStep 646115 = 969173) B969173
theorem B646131 : Blo 642303 646131 := bstep (se 1 (by rfl) ⟨484598, by rfl⟩ : syracuseStep 646131 = 969197) B969197
theorem B646147 : Blo 642303 646147 := bstep (se 1 (by rfl) ⟨484610, by rfl⟩ : syracuseStep 646147 = 969221) B969221
theorem B646163 : Blo 642303 646163 := bstep (se 1 (by rfl) ⟨484622, by rfl⟩ : syracuseStep 646163 = 969245) B969245
theorem B646179 : Blo 642303 646179 := bstep (se 1 (by rfl) ⟨484634, by rfl⟩ : syracuseStep 646179 = 969269) B969269
theorem B646195 : Blo 642303 646195 := bstep (se 1 (by rfl) ⟨484646, by rfl⟩ : syracuseStep 646195 = 969293) B969293
theorem B646211 : Blo 642303 646211 := bstep (se 1 (by rfl) ⟨484658, by rfl⟩ : syracuseStep 646211 = 969317) B969317
theorem B646227 : Blo 642303 646227 := bstep (se 1 (by rfl) ⟨484670, by rfl⟩ : syracuseStep 646227 = 969341) B969341
theorem B646243 : Blo 642303 646243 := bstep (se 1 (by rfl) ⟨484682, by rfl⟩ : syracuseStep 646243 = 969365) B969365
theorem B646259 : Blo 642303 646259 := bstep (se 1 (by rfl) ⟨484694, by rfl⟩ : syracuseStep 646259 = 969389) B969389
theorem B646275 : Blo 642303 646275 := bstep (se 1 (by rfl) ⟨484706, by rfl⟩ : syracuseStep 646275 = 969413) B969413
theorem B646291 : Blo 642303 646291 := bstep (se 1 (by rfl) ⟨484718, by rfl⟩ : syracuseStep 646291 = 969437) B969437
theorem B2448589 : Blo 642303 2448589 := bstep (se 3 (by rfl) ⟨459110, by rfl⟩ : syracuseStep 2448589 = 918221) B918221
theorem B1465777 : Blo 642303 1465777 := bstep (se 2 (by rfl) ⟨549666, by rfl⟩ : syracuseStep 1465777 = 1099333) B1099333
theorem B8248817 : Blo 642303 8248817 := bstep (se 2 (by rfl) ⟨3093306, by rfl⟩ : syracuseStep 8248817 = 6186613) B6186613
theorem B14900849 : Blo 642303 14900849 := bstep (se 2 (by rfl) ⟨5587818, by rfl⟩ : syracuseStep 14900849 = 11175637) B11175637
theorem B1629841 : Blo 642303 1629841 := bstep (se 2 (by rfl) ⟨611190, by rfl⟩ : syracuseStep 1629841 = 1222381) B1222381
theorem B1630115 : Blo 642303 1630115 := bstep (se 1 (by rfl) ⟨1222586, by rfl⟩ : syracuseStep 1630115 = 2445173) B2445173
theorem B2449379 : Blo 642303 2449379 := bstep (se 1 (by rfl) ⟨1837034, by rfl⟩ : syracuseStep 2449379 = 3674069) B3674069
theorem B1957873 : Blo 642303 1957873 := bstep (se 2 (by rfl) ⟨734202, by rfl⟩ : syracuseStep 1957873 = 1468405) B1468405
theorem B1466435 : Blo 642303 1466435 := bstep (se 1 (by rfl) ⟨1099826, by rfl⟩ : syracuseStep 1466435 = 2199653) B2199653
theorem B1630307 : Blo 642303 1630307 := bstep (se 1 (by rfl) ⟨1222730, by rfl⟩ : syracuseStep 1630307 = 2445461) B2445461
theorem B3268835 : Blo 642303 3268835 := bstep (se 1 (by rfl) ⟨2451626, by rfl⟩ : syracuseStep 3268835 = 4903253) B4903253
theorem B1564913 : Blo 642303 1564913 := bstep (se 2 (by rfl) ⟨586842, by rfl⟩ : syracuseStep 1564913 = 1173685) B1173685
theorem B4120901 : Blo 642303 4120901 := bstep (se 4 (by rfl) ⟨386334, by rfl⟩ : syracuseStep 4120901 = 772669) B772669
theorem B1302979 : Blo 642303 1302979 := bstep (se 1 (by rfl) ⟨977234, by rfl⟩ : syracuseStep 1302979 = 1954469) B1954469
theorem B3662405 : Blo 642303 3662405 := bstep (se 4 (by rfl) ⟨343350, by rfl⟩ : syracuseStep 3662405 = 686701) B686701
theorem B3924557 : Blo 642303 3924557 := bstep (se 3 (by rfl) ⟨735854, by rfl⟩ : syracuseStep 3924557 = 1471709) B1471709
theorem B2450033 : Blo 642303 2450033 := bstep (se 2 (by rfl) ⟨918762, by rfl⟩ : syracuseStep 2450033 = 1837525) B1837525
theorem B5497571 : Blo 642303 5497571 := bstep (se 1 (by rfl) ⟨4123178, by rfl⟩ : syracuseStep 5497571 = 8246357) B8246357
theorem B3269645 : Blo 642303 3269645 := bstep (se 3 (by rfl) ⟨613058, by rfl⟩ : syracuseStep 3269645 = 1226117) B1226117
theorem B1631249 : Blo 642303 1631249 := bstep (se 2 (by rfl) ⟨611718, by rfl⟩ : syracuseStep 1631249 = 1223437) B1223437
theorem B1631299 : Blo 642303 1631299 := bstep (se 1 (by rfl) ⟨1223474, by rfl⟩ : syracuseStep 1631299 = 2446949) B2446949
theorem B1631441 : Blo 642303 1631441 := bstep (se 2 (by rfl) ⟨611790, by rfl⟩ : syracuseStep 1631441 = 1223581) B1223581
theorem B3663089 : Blo 642303 3663089 := bstep (se 2 (by rfl) ⟨1373658, by rfl⟩ : syracuseStep 3663089 = 2747317) B2747317
theorem B2745677 : Blo 642303 2745677 := bstep (se 3 (by rfl) ⟨514814, by rfl⟩ : syracuseStep 2745677 = 1029629) B1029629
theorem B8250821 : Blo 642303 8250821 := bstep (se 4 (by rfl) ⟨773514, by rfl⟩ : syracuseStep 8250821 = 1547029) B1547029
theorem B2090605 : Blo 642303 2090605 := bstep (se 3 (by rfl) ⟨391988, by rfl⟩ : syracuseStep 2090605 = 783977) B783977
theorem B1959821 : Blo 642303 1959821 := bstep (se 3 (by rfl) ⟨367466, by rfl⟩ : syracuseStep 1959821 = 734933) B734933
theorem B2451491 : Blo 642303 2451491 := bstep (se 1 (by rfl) ⟨1838618, by rfl⟩ : syracuseStep 2451491 = 3677237) B3677237
theorem B2451505 : Blo 642303 2451505 := bstep (se 2 (by rfl) ⟨919314, by rfl⟩ : syracuseStep 2451505 = 1838629) B1838629
theorem B1632433 : Blo 642303 1632433 := bstep (se 2 (by rfl) ⟨612162, by rfl⟩ : syracuseStep 1632433 = 1224325) B1224325
theorem B813235 : Blo 642303 813235 := bstep (se 1 (by rfl) ⟨609926, by rfl⟩ : syracuseStep 813235 = 1219853) B1219853
theorem B813331 : Blo 642303 813331 := bstep (se 1 (by rfl) ⟨609998, by rfl⟩ : syracuseStep 813331 = 1219997) B1219997
theorem B2058605 : Blo 642303 2058605 := bstep (se 3 (by rfl) ⟨385988, by rfl⟩ : syracuseStep 2058605 = 771977) B771977
theorem B2320817 : Blo 642303 2320817 := bstep (se 2 (by rfl) ⟨870306, by rfl⟩ : syracuseStep 2320817 = 1740613) B1740613
theorem B1632707 : Blo 642303 1632707 := bstep (se 1 (by rfl) ⟨1224530, by rfl⟩ : syracuseStep 1632707 = 2449061) B2449061
theorem B2091587 : Blo 642303 2091587 := bstep (se 1 (by rfl) ⟨1568690, by rfl⟩ : syracuseStep 2091587 = 3137381) B3137381
theorem B2615885 : Blo 642303 2615885 := bstep (se 3 (by rfl) ⟨490478, by rfl⟩ : syracuseStep 2615885 = 980957) B980957
theorem B2746993 : Blo 642303 2746993 := bstep (se 2 (by rfl) ⟨1030122, by rfl⟩ : syracuseStep 2746993 = 2060245) B2060245
theorem B1632899 : Blo 642303 1632899 := bstep (se 1 (by rfl) ⟨1224674, by rfl⟩ : syracuseStep 1632899 = 2449349) B2449349
theorem B3664547 : Blo 642303 3664547 := bstep (se 1 (by rfl) ⟨2748410, by rfl⟩ : syracuseStep 3664547 = 5496821) B5496821
theorem B813827 : Blo 642303 813827 := bstep (se 1 (by rfl) ⟨610370, by rfl⟩ : syracuseStep 813827 = 1220741) B1220741
theorem B1829699 : Blo 642303 1829699 := bstep (se 1 (by rfl) ⟨1372274, by rfl⟩ : syracuseStep 1829699 = 2744549) B2744549
theorem B1961329 : Blo 642303 1961329 := bstep (se 2 (by rfl) ⟨735498, by rfl⟩ : syracuseStep 1961329 = 1470997) B1470997
theorem B814531 : Blo 642303 814531 := bstep (se 1 (by rfl) ⟨610898, by rfl⟩ : syracuseStep 814531 = 1221797) B1221797
theorem B2452963 : Blo 642303 2452963 := bstep (se 1 (by rfl) ⟨1839722, by rfl⟩ : syracuseStep 2452963 = 3679445) B3679445
theorem B814627 : Blo 642303 814627 := bstep (se 1 (by rfl) ⟨610970, by rfl⟩ : syracuseStep 814627 = 1221941) B1221941
theorem B1633841 : Blo 642303 1633841 := bstep (se 2 (by rfl) ⟨612690, by rfl⟩ : syracuseStep 1633841 = 1225381) B1225381
theorem B978499 : Blo 642303 978499 := bstep (se 1 (by rfl) ⟨733874, by rfl⟩ : syracuseStep 978499 = 1467749) B1467749
theorem B1633891 : Blo 642303 1633891 := bstep (se 1 (by rfl) ⟨1225418, by rfl⟩ : syracuseStep 1633891 = 2450837) B2450837
theorem B1830509 : Blo 642303 1830509 := bstep (se 3 (by rfl) ⟨343220, by rfl⟩ : syracuseStep 1830509 = 686441) B686441
theorem B2059949 : Blo 642303 2059949 := bstep (se 3 (by rfl) ⟨386240, by rfl⟩ : syracuseStep 2059949 = 772481) B772481
theorem B15920867 : Blo 642303 15920867 := bstep (se 1 (by rfl) ⟨11940650, by rfl⟩ : syracuseStep 15920867 = 23881301) B23881301
theorem B1634033 : Blo 642303 1634033 := bstep (se 2 (by rfl) ⟨612762, by rfl⟩ : syracuseStep 1634033 = 1225525) B1225525
theorem B978689 : Blo 642303 978689 := bstep (se 2 (by rfl) ⟨367008, by rfl⟩ : syracuseStep 978689 = 734017) B734017
theorem B1830701 : Blo 642303 1830701 := bstep (se 3 (by rfl) ⟨343256, by rfl⟩ : syracuseStep 1830701 = 686513) B686513
theorem B978785 : Blo 642303 978785 := bstep (se 2 (by rfl) ⟨367044, by rfl⟩ : syracuseStep 978785 = 734089) B734089
theorem B1470449 : Blo 642303 1470449 := bstep (se 2 (by rfl) ⟨551418, by rfl⟩ : syracuseStep 1470449 = 1102837) B1102837
theorem B815123 : Blo 642303 815123 := bstep (se 1 (by rfl) ⟨611342, by rfl⟩ : syracuseStep 815123 = 1222685) B1222685
theorem B1372241 : Blo 642303 1372241 := bstep (se 2 (by rfl) ⟨514590, by rfl⟩ : syracuseStep 1372241 = 1029181) B1029181
theorem B2060387 : Blo 642303 2060387 := bstep (se 1 (by rfl) ⟨1545290, by rfl⟩ : syracuseStep 2060387 = 3090581) B3090581
theorem B1962083 : Blo 642303 1962083 := bstep (se 1 (by rfl) ⟨1471562, by rfl⟩ : syracuseStep 1962083 = 2943125) B2943125
theorem B782515 : Blo 642303 782515 := bstep (se 1 (by rfl) ⟨586886, by rfl⟩ : syracuseStep 782515 = 1173773) B1173773
theorem B2617699 : Blo 642303 2617699 := bstep (se 1 (by rfl) ⟨1963274, by rfl⟩ : syracuseStep 2617699 = 3926549) B3926549
theorem B1045043 : Blo 642303 1045043 := bstep (se 1 (by rfl) ⟨783782, by rfl⟩ : syracuseStep 1045043 = 1567565) B1567565
theorem B881219 : Blo 642303 881219 := bstep (se 1 (by rfl) ⟨660914, by rfl⟩ : syracuseStep 881219 = 1321829) B1321829
theorem B1635025 : Blo 642303 1635025 := bstep (se 2 (by rfl) ⟨613134, by rfl⟩ : syracuseStep 1635025 = 1226269) B1226269
theorem B815827 : Blo 642303 815827 := bstep (se 1 (by rfl) ⟨611870, by rfl⟩ : syracuseStep 815827 = 1223741) B1223741
theorem B1831693 : Blo 642303 1831693 := bstep (se 3 (by rfl) ⟨343442, by rfl⟩ : syracuseStep 1831693 = 686885) B686885
theorem B881425 : Blo 642303 881425 := bstep (se 2 (by rfl) ⟨330534, by rfl⟩ : syracuseStep 881425 = 661069) B661069
theorem B815923 : Blo 642303 815923 := bstep (se 1 (by rfl) ⟨611942, by rfl⟩ : syracuseStep 815923 = 1223885) B1223885
theorem B2618189 : Blo 642303 2618189 := bstep (se 3 (by rfl) ⟨490910, by rfl⟩ : syracuseStep 2618189 = 981821) B981821
theorem B2323313 : Blo 642303 2323313 := bstep (se 2 (by rfl) ⟨871242, by rfl⟩ : syracuseStep 2323313 = 1742485) B1742485
theorem B1635299 : Blo 642303 1635299 := bstep (se 1 (by rfl) ⟨1226474, by rfl⟩ : syracuseStep 1635299 = 2452949) B2452949
theorem B1635491 : Blo 642303 1635491 := bstep (se 1 (by rfl) ⟨1226618, by rfl⟩ : syracuseStep 1635491 = 2453237) B2453237
theorem B2389283 : Blo 642303 2389283 := bstep (se 1 (by rfl) ⟨1791962, by rfl⟩ : syracuseStep 2389283 = 3583925) B3583925
theorem B816419 : Blo 642303 816419 := bstep (se 1 (by rfl) ⟨612314, by rfl⟩ : syracuseStep 816419 = 1224629) B1224629
theorem B12711221 : Blo 642303 12711221 := bstep (se 5 (by rfl) ⟨595838, by rfl⟩ : syracuseStep 12711221 = 1191677) B1191677
theorem B914753 : Blo 642303 914753 := bstep (se 2 (by rfl) ⟨343032, by rfl⟩ : syracuseStep 914753 = 686065) B686065
theorem B1373539 : Blo 642303 1373539 := bstep (se 1 (by rfl) ⟨1030154, by rfl⟩ : syracuseStep 1373539 = 2060309) B2060309
theorem B1766819 : Blo 642303 1766819 := bstep (se 1 (by rfl) ⟨1325114, by rfl⟩ : syracuseStep 1766819 = 2650229) B2650229
theorem B2618801 : Blo 642303 2618801 := bstep (se 2 (by rfl) ⟨982050, by rfl⟩ : syracuseStep 2618801 = 1964101) B1964101
theorem B6190577 : Blo 642303 6190577 := bstep (se 2 (by rfl) ⟨2321466, by rfl⟩ : syracuseStep 6190577 = 4642933) B4642933
theorem B5895665 : Blo 642303 5895665 := bstep (se 2 (by rfl) ⟨2210874, by rfl⟩ : syracuseStep 5895665 = 4421749) B4421749
theorem B2750051 : Blo 642303 2750051 := bstep (se 1 (by rfl) ⟨2062538, by rfl⟩ : syracuseStep 2750051 = 4125077) B4125077
theorem B980689 : Blo 642303 980689 := bstep (se 2 (by rfl) ⟨367758, by rfl⟩ : syracuseStep 980689 = 735517) B735517
theorem B3667781 : Blo 642303 3667781 := bstep (se 4 (by rfl) ⟨343854, by rfl⟩ : syracuseStep 3667781 = 687709) B687709
theorem B2062307 : Blo 642303 2062307 := bstep (se 1 (by rfl) ⟨1546730, by rfl⟩ : syracuseStep 2062307 = 3093461) B3093461
theorem B817123 : Blo 642303 817123 := bstep (se 1 (by rfl) ⟨612842, by rfl⟩ : syracuseStep 817123 = 1225685) B1225685
theorem B817219 : Blo 642303 817219 := bstep (se 1 (by rfl) ⟨612914, by rfl⟩ : syracuseStep 817219 = 1225829) B1225829
theorem B1308817 : Blo 642303 1308817 := bstep (se 2 (by rfl) ⟨490806, by rfl⟩ : syracuseStep 1308817 = 981613) B981613
theorem B915619 : Blo 642303 915619 := bstep (se 1 (by rfl) ⟨686714, by rfl⟩ : syracuseStep 915619 = 1373429) B1373429
theorem B686291 : Blo 642303 686291 := bstep (se 1 (by rfl) ⟨514718, by rfl⟩ : syracuseStep 686291 = 1029437) B1029437
theorem B1767665 : Blo 642303 1767665 := bstep (se 2 (by rfl) ⟨662874, by rfl⟩ : syracuseStep 1767665 = 1325749) B1325749
theorem B915715 : Blo 642303 915715 := bstep (se 1 (by rfl) ⟨686786, by rfl⟩ : syracuseStep 915715 = 1373573) B1373573
theorem B3668237 : Blo 642303 3668237 := bstep (se 3 (by rfl) ⟨687794, by rfl⟩ : syracuseStep 3668237 = 1375589) B1375589
theorem B1767761 : Blo 642303 1767761 := bstep (se 2 (by rfl) ⟨662910, by rfl⟩ : syracuseStep 1767761 = 1325821) B1325821
theorem B4127075 : Blo 642303 4127075 := bstep (se 1 (by rfl) ⟨3095306, by rfl⟩ : syracuseStep 4127075 = 6190613) B6190613
theorem B1571185 : Blo 642303 1571185 := bstep (se 2 (by rfl) ⟨589194, by rfl⟩ : syracuseStep 1571185 = 1178389) B1178389
theorem B6977933 : Blo 642303 6977933 := bstep (se 3 (by rfl) ⟨1308362, by rfl⟩ : syracuseStep 6977933 = 2616725) B2616725
theorem B2783693 : Blo 642303 2783693 := bstep (se 3 (by rfl) ⟨521942, by rfl⟩ : syracuseStep 2783693 = 1043885) B1043885
theorem B1833425 : Blo 642303 1833425 := bstep (se 2 (by rfl) ⟨687534, by rfl⟩ : syracuseStep 1833425 = 1375069) B1375069
theorem B1047041 : Blo 642303 1047041 := bstep (se 2 (by rfl) ⟨392640, by rfl⟩ : syracuseStep 1047041 = 785281) B785281
theorem B1374769 : Blo 642303 1374769 := bstep (se 2 (by rfl) ⟨515538, by rfl⟩ : syracuseStep 1374769 = 1031077) B1031077
theorem B817715 : Blo 642303 817715 := bstep (se 1 (by rfl) ⟨613286, by rfl⟩ : syracuseStep 817715 = 1226573) B1226573
theorem B1833617 : Blo 642303 1833617 := bstep (se 2 (by rfl) ⟨687606, by rfl⟩ : syracuseStep 1833617 = 1375213) B1375213
theorem B916211 : Blo 642303 916211 := bstep (se 1 (by rfl) ⟨687158, by rfl⟩ : syracuseStep 916211 = 1374317) B1374317
theorem B4127537 : Blo 642303 4127537 := bstep (se 2 (by rfl) ⟨1547826, by rfl⟩ : syracuseStep 4127537 = 3095653) B3095653
theorem B981857 : Blo 642303 981857 := bstep (se 2 (by rfl) ⟨368196, by rfl⟩ : syracuseStep 981857 = 736393) B736393
theorem B687043 : Blo 642303 687043 := bstep (se 1 (by rfl) ⟨515282, by rfl⟩ : syracuseStep 687043 = 1030565) B1030565
theorem B1768483 : Blo 642303 1768483 := bstep (se 1 (by rfl) ⟨1326362, by rfl⟩ : syracuseStep 1768483 = 2652725) B2652725
theorem B1965197 : Blo 642303 1965197 := bstep (se 3 (by rfl) ⟨368474, by rfl⟩ : syracuseStep 1965197 = 736949) B736949
theorem B687299 : Blo 642303 687299 := bstep (se 1 (by rfl) ⟨515474, by rfl⟩ : syracuseStep 687299 = 1030949) B1030949
theorem B1375555 : Blo 642303 1375555 := bstep (se 1 (by rfl) ⟨1031666, by rfl⟩ : syracuseStep 1375555 = 2063333) B2063333
theorem B916849 : Blo 642303 916849 := bstep (se 2 (by rfl) ⟨343818, by rfl⟩ : syracuseStep 916849 = 687637) B687637
theorem B1310179 : Blo 642303 1310179 := bstep (se 1 (by rfl) ⟨982634, by rfl⟩ : syracuseStep 1310179 = 1965269) B1965269
theorem B1834609 : Blo 642303 1834609 := bstep (se 2 (by rfl) ⟨687978, by rfl⟩ : syracuseStep 1834609 = 1375957) B1375957
theorem B917185 : Blo 642303 917185 := bstep (se 2 (by rfl) ⟨343944, by rfl⟩ : syracuseStep 917185 = 687889) B687889
theorem B1736461 : Blo 642303 1736461 := bstep (se 3 (by rfl) ⟨325586, by rfl⟩ : syracuseStep 1736461 = 651173) B651173
theorem B1834883 : Blo 642303 1834883 := bstep (se 1 (by rfl) ⟨1376162, by rfl⟩ : syracuseStep 1834883 = 2752325) B2752325
theorem B6193037 : Blo 642303 6193037 := bstep (se 3 (by rfl) ⟨1161194, by rfl⟩ : syracuseStep 6193037 = 2322389) B2322389
theorem B688051 : Blo 642303 688051 := bstep (se 1 (by rfl) ⟨516038, by rfl⟩ : syracuseStep 688051 = 1032077) B1032077
theorem B13565893 : Blo 642303 13565893 := bstep (se 4 (by rfl) ⟨1271802, by rfl⟩ : syracuseStep 13565893 = 2543605) B2543605
theorem B917515 : Blo 642303 917515 := bstep (se 1 (by rfl) ⟨688136, by rfl⟩ : syracuseStep 917515 = 1376273) B1376273
theorem B1179851 : Blo 642303 1179851 := bstep (se 1 (by rfl) ⟨884888, by rfl⟩ : syracuseStep 1179851 = 1769777) B1769777
theorem B2490689 : Blo 642303 2490689 := bstep (se 2 (by rfl) ⟨934008, by rfl⟩ : syracuseStep 2490689 = 1868017) B1868017
theorem B786763 : Blo 642303 786763 := bstep (se 1 (by rfl) ⟨590072, by rfl⟩ : syracuseStep 786763 = 1180145) B1180145
theorem B4718999 : Blo 642303 4718999 := bstep (se 1 (by rfl) ⟨3539249, by rfl⟩ : syracuseStep 4718999 = 7078499) B7078499
theorem B786839 : Blo 642303 786839 := bstep (se 1 (by rfl) ⟨590129, by rfl⟩ : syracuseStep 786839 = 1180259) B1180259
theorem B13238801 : Blo 642303 13238801 := bstep (se 2 (by rfl) ⟨4964550, by rfl⟩ : syracuseStep 13238801 = 9929101) B9929101
theorem B3539531 : Blo 642303 3539531 := bstep (se 1 (by rfl) ⟨2654648, by rfl⟩ : syracuseStep 3539531 = 5309297) B5309297
theorem B1737305 : Blo 642303 1737305 := bstep (se 2 (by rfl) ⟨651489, by rfl⟩ : syracuseStep 1737305 = 1302979) B1302979
theorem B1835713 : Blo 642303 1835713 := bstep (se 2 (by rfl) ⟨688392, by rfl⟩ : syracuseStep 1835713 = 1376785) B1376785
theorem B6980357 : Blo 642303 6980357 := bstep (se 4 (by rfl) ⟨654408, by rfl⟩ : syracuseStep 6980357 = 1308817) B1308817
theorem B2753297 : Blo 642303 2753297 := bstep (se 2 (by rfl) ⟨1032486, by rfl⟩ : syracuseStep 2753297 = 2064973) B2064973
theorem B6030155 : Blo 642303 6030155 := bstep (se 1 (by rfl) ⟨4522616, by rfl⟩ : syracuseStep 6030155 = 9045233) B9045233
theorem B918859 : Blo 642303 918859 := bstep (se 1 (by rfl) ⟨689144, by rfl⟩ : syracuseStep 918859 = 1378289) B1378289
theorem B1377623 : Blo 642303 1377623 := bstep (se 1 (by rfl) ⟨1033217, by rfl⟩ : syracuseStep 1377623 = 2066435) B2066435
theorem B4883813 : Blo 642303 4883813 := bstep (se 4 (by rfl) ⟨457857, by rfl⟩ : syracuseStep 4883813 = 915715) B915715
theorem B10978739 : Blo 642303 10978739 := bstep (se 1 (by rfl) ⟨8234054, by rfl⟩ : syracuseStep 10978739 = 16468109) B16468109
theorem B1377803 : Blo 642303 1377803 := bstep (se 1 (by rfl) ⟨1033352, by rfl⟩ : syracuseStep 1377803 = 2066705) B2066705
theorem B15926797 : Blo 642303 15926797 := bstep (se 3 (by rfl) ⟨2986274, by rfl⟩ : syracuseStep 15926797 = 5972549) B5972549
theorem B919127 : Blo 642303 919127 := bstep (se 1 (by rfl) ⟨689345, by rfl⟩ : syracuseStep 919127 = 1378691) B1378691
theorem B34866893 : Blo 642303 34866893 := bstep (se 3 (by rfl) ⟨6537542, by rfl⟩ : syracuseStep 34866893 = 13075085) B13075085
theorem B722731 : Blo 642303 722731 := bstep (se 1 (by rfl) ⟨542048, by rfl⟩ : syracuseStep 722731 = 1084097) B1084097
theorem B4884299 : Blo 642303 4884299 := bstep (se 1 (by rfl) ⟨3663224, by rfl⟩ : syracuseStep 4884299 = 7326449) B7326449
theorem B689995 : Blo 642303 689995 := bstep (se 1 (by rfl) ⟨517496, by rfl⟩ : syracuseStep 689995 = 1034993) B1034993
theorem B722839 : Blo 642303 722839 := bstep (se 1 (by rfl) ⟨542129, by rfl⟩ : syracuseStep 722839 = 1084259) B1084259
theorem B723019 : Blo 642303 723019 := bstep (se 1 (by rfl) ⟨542264, by rfl⟩ : syracuseStep 723019 = 1084529) B1084529
theorem B39651403 : Blo 642303 39651403 := bstep (se 1 (by rfl) ⟨29738552, by rfl⟩ : syracuseStep 39651403 = 59477105) B59477105
theorem B2787473 : Blo 642303 2787473 := bstep (se 2 (by rfl) ⟨1045302, by rfl⟩ : syracuseStep 2787473 = 2090605) B2090605
theorem B723127 : Blo 642303 723127 := bstep (se 1 (by rfl) ⟨542345, by rfl⟩ : syracuseStep 723127 = 1084691) B1084691
theorem B3672337 : Blo 642303 3672337 := bstep (se 2 (by rfl) ⟨1377126, by rfl⟩ : syracuseStep 3672337 = 2754253) B2754253
theorem B723307 : Blo 642303 723307 := bstep (se 1 (by rfl) ⟨542480, by rfl⟩ : syracuseStep 723307 = 1084961) B1084961
theorem B723415 : Blo 642303 723415 := bstep (se 1 (by rfl) ⟨542561, by rfl⟩ : syracuseStep 723415 = 1085123) B1085123
theorem B1018391 : Blo 642303 1018391 := bstep (se 1 (by rfl) ⟨763793, by rfl⟩ : syracuseStep 1018391 = 1527587) B1527587
theorem B2984471 : Blo 642303 2984471 := bstep (se 1 (by rfl) ⟨2238353, by rfl⟩ : syracuseStep 2984471 = 4476707) B4476707
theorem B920089 : Blo 642303 920089 := bstep (se 2 (by rfl) ⟨345033, by rfl⟩ : syracuseStep 920089 = 690067) B690067
theorem B1084043 : Blo 642303 1084043 := bstep (se 1 (by rfl) ⟨813032, by rfl⟩ : syracuseStep 1084043 = 1626065) B1626065
theorem B723595 : Blo 642303 723595 := bstep (se 1 (by rfl) ⟨542696, by rfl⟩ : syracuseStep 723595 = 1085393) B1085393
theorem B723703 : Blo 642303 723703 := bstep (se 1 (by rfl) ⟨542777, by rfl⟩ : syracuseStep 723703 = 1085555) B1085555
theorem B1084171 : Blo 642303 1084171 := bstep (se 1 (by rfl) ⟨813128, by rfl⟩ : syracuseStep 1084171 = 1626257) B1626257
theorem B12389219 : Blo 642303 12389219 := bstep (se 1 (by rfl) ⟨9291914, by rfl⟩ : syracuseStep 12389219 = 18583829) B18583829
theorem B1084313 : Blo 642303 1084313 := bstep (se 2 (by rfl) ⟨406617, by rfl⟩ : syracuseStep 1084313 = 813235) B813235
theorem B723883 : Blo 642303 723883 := bstep (se 1 (by rfl) ⟨542912, by rfl⟩ : syracuseStep 723883 = 1085825) B1085825
theorem B723991 : Blo 642303 723991 := bstep (se 1 (by rfl) ⟨542993, by rfl⟩ : syracuseStep 723991 = 1085987) B1085987
theorem B1084441 : Blo 642303 1084441 := bstep (se 2 (by rfl) ⟨406665, by rfl⟩ : syracuseStep 1084441 = 813331) B813331
theorem B1379443 : Blo 642303 1379443 := bstep (se 1 (by rfl) ⟨1034582, by rfl⟩ : syracuseStep 1379443 = 2069165) B2069165
theorem B2755757 : Blo 642303 2755757 := bstep (se 3 (by rfl) ⟨516704, by rfl⟩ : syracuseStep 2755757 = 1033409) B1033409
theorem B724171 : Blo 642303 724171 := bstep (se 1 (by rfl) ⟨543128, by rfl⟩ : syracuseStep 724171 = 1086257) B1086257
theorem B724279 : Blo 642303 724279 := bstep (se 1 (by rfl) ⟨543209, by rfl⟩ : syracuseStep 724279 = 1086419) B1086419
theorem B1445273 : Blo 642303 1445273 := bstep (se 2 (by rfl) ⟨541977, by rfl⟩ : syracuseStep 1445273 = 1083955) B1083955
theorem B724459 : Blo 642303 724459 := bstep (se 1 (by rfl) ⟨543344, by rfl⟩ : syracuseStep 724459 = 1086689) B1086689
theorem B1445363 : Blo 642303 1445363 := bstep (se 1 (by rfl) ⟨1084022, by rfl⟩ : syracuseStep 1445363 = 2168045) B2168045
theorem B2756099 : Blo 642303 2756099 := bstep (se 1 (by rfl) ⟨2067074, by rfl⟩ : syracuseStep 2756099 = 4134149) B4134149
theorem B1445399 : Blo 642303 1445399 := bstep (se 1 (by rfl) ⟨1084049, by rfl⟩ : syracuseStep 1445399 = 2168099) B2168099
theorem B1085015 : Blo 642303 1085015 := bstep (se 1 (by rfl) ⟨813761, by rfl⟩ : syracuseStep 1085015 = 1627523) B1627523
theorem B724567 : Blo 642303 724567 := bstep (se 1 (by rfl) ⟨543425, by rfl⟩ : syracuseStep 724567 = 1086851) B1086851
theorem B1379929 : Blo 642303 1379929 := bstep (se 2 (by rfl) ⟨517473, by rfl⟩ : syracuseStep 1379929 = 1034947) B1034947
theorem B1445579 : Blo 642303 1445579 := bstep (se 1 (by rfl) ⟨1084184, by rfl⟩ : syracuseStep 1445579 = 2168369) B2168369
theorem B1085143 : Blo 642303 1085143 := bstep (se 1 (by rfl) ⟨813857, by rfl⟩ : syracuseStep 1085143 = 1627715) B1627715
theorem B1445633 : Blo 642303 1445633 := bstep (se 2 (by rfl) ⟨542112, by rfl⟩ : syracuseStep 1445633 = 1084225) B1084225
theorem B724747 : Blo 642303 724747 := bstep (se 1 (by rfl) ⟨543560, by rfl⟩ : syracuseStep 724747 = 1087121) B1087121
theorem B724855 : Blo 642303 724855 := bstep (se 1 (by rfl) ⟨543641, by rfl⟩ : syracuseStep 724855 = 1087283) B1087283
theorem B1445849 : Blo 642303 1445849 := bstep (se 2 (by rfl) ⟨542193, by rfl⟩ : syracuseStep 1445849 = 1084387) B1084387
theorem B725035 : Blo 642303 725035 := bstep (se 1 (by rfl) ⟨543776, by rfl⟩ : syracuseStep 725035 = 1087553) B1087553
theorem B1445939 : Blo 642303 1445939 := bstep (se 1 (by rfl) ⟨1084454, by rfl⟩ : syracuseStep 1445939 = 2168909) B2168909
theorem B1445975 : Blo 642303 1445975 := bstep (se 1 (by rfl) ⟨1084481, by rfl⟩ : syracuseStep 1445975 = 2168963) B2168963
theorem B725143 : Blo 642303 725143 := bstep (se 1 (by rfl) ⟨543857, by rfl⟩ : syracuseStep 725143 = 1087715) B1087715
theorem B1446155 : Blo 642303 1446155 := bstep (se 1 (by rfl) ⟨1084616, by rfl⟩ : syracuseStep 1446155 = 2169233) B2169233
theorem B1446209 : Blo 642303 1446209 := bstep (se 2 (by rfl) ⟨542328, by rfl⟩ : syracuseStep 1446209 = 1084657) B1084657
theorem B1085771 : Blo 642303 1085771 := bstep (se 1 (by rfl) ⟨814328, by rfl⟩ : syracuseStep 1085771 = 1628657) B1628657
theorem B725323 : Blo 642303 725323 := bstep (se 1 (by rfl) ⟨543992, by rfl⟩ : syracuseStep 725323 = 1087985) B1087985
theorem B1839449 : Blo 642303 1839449 := bstep (se 2 (by rfl) ⟨689793, by rfl⟩ : syracuseStep 1839449 = 1379587) B1379587
theorem B725431 : Blo 642303 725431 := bstep (se 1 (by rfl) ⟨544073, by rfl⟩ : syracuseStep 725431 = 1088147) B1088147
theorem B1085899 : Blo 642303 1085899 := bstep (se 1 (by rfl) ⟨814424, by rfl⟩ : syracuseStep 1085899 = 1628849) B1628849
theorem B1446425 : Blo 642303 1446425 := bstep (se 2 (by rfl) ⟨542409, by rfl⟩ : syracuseStep 1446425 = 1084819) B1084819
theorem B1086041 : Blo 642303 1086041 := bstep (se 2 (by rfl) ⟨407265, by rfl⟩ : syracuseStep 1086041 = 814531) B814531
theorem B725611 : Blo 642303 725611 := bstep (se 1 (by rfl) ⟨544208, by rfl⟩ : syracuseStep 725611 = 1088417) B1088417
theorem B1446515 : Blo 642303 1446515 := bstep (se 1 (by rfl) ⟨1084886, by rfl⟩ : syracuseStep 1446515 = 2169773) B2169773
theorem B1446551 : Blo 642303 1446551 := bstep (se 1 (by rfl) ⟨1084913, by rfl⟩ : syracuseStep 1446551 = 2169827) B2169827
theorem B725719 : Blo 642303 725719 := bstep (se 1 (by rfl) ⟨544289, by rfl⟩ : syracuseStep 725719 = 1088579) B1088579
theorem B1086169 : Blo 642303 1086169 := bstep (se 2 (by rfl) ⟨407313, by rfl⟩ : syracuseStep 1086169 = 814627) B814627
theorem B1446731 : Blo 642303 1446731 := bstep (se 1 (by rfl) ⟨1085048, by rfl⟩ : syracuseStep 1446731 = 2170097) B2170097
theorem B1446785 : Blo 642303 1446785 := bstep (se 2 (by rfl) ⟨542544, by rfl⟩ : syracuseStep 1446785 = 1085089) B1085089
theorem B725899 : Blo 642303 725899 := bstep (se 1 (by rfl) ⟨544424, by rfl⟩ : syracuseStep 725899 = 1088849) B1088849
theorem B726007 : Blo 642303 726007 := bstep (se 1 (by rfl) ⟨544505, by rfl⟩ : syracuseStep 726007 = 1089011) B1089011
theorem B2167883 : Blo 642303 2167883 := bstep (se 1 (by rfl) ⟨1625912, by rfl⟩ : syracuseStep 2167883 = 3251825) B3251825
theorem B9933899 : Blo 642303 9933899 := bstep (se 1 (by rfl) ⟨7450424, by rfl⟩ : syracuseStep 9933899 = 14900849) B14900849
theorem B1447001 : Blo 642303 1447001 := bstep (se 2 (by rfl) ⟨542625, by rfl⟩ : syracuseStep 1447001 = 1085251) B1085251
theorem B726187 : Blo 642303 726187 := bstep (se 1 (by rfl) ⟨544640, by rfl⟩ : syracuseStep 726187 = 1089281) B1089281
theorem B1447091 : Blo 642303 1447091 := bstep (se 1 (by rfl) ⟨1085318, by rfl⟩ : syracuseStep 1447091 = 2170637) B2170637
theorem B1447127 : Blo 642303 1447127 := bstep (se 1 (by rfl) ⟨1085345, by rfl⟩ : syracuseStep 1447127 = 2170691) B2170691
theorem B726295 : Blo 642303 726295 := bstep (se 1 (by rfl) ⟨544721, by rfl⟩ : syracuseStep 726295 = 1089443) B1089443
theorem B1086743 : Blo 642303 1086743 := bstep (se 1 (by rfl) ⟨815057, by rfl⟩ : syracuseStep 1086743 = 1630115) B1630115
theorem B2168153 : Blo 642303 2168153 := bstep (se 2 (by rfl) ⟨813057, by rfl⟩ : syracuseStep 2168153 = 1626115) B1626115
theorem B1447307 : Blo 642303 1447307 := bstep (se 1 (by rfl) ⟨1085480, by rfl⟩ : syracuseStep 1447307 = 2170961) B2170961
theorem B16520597 : Blo 642303 16520597 := bstep (se 6 (by rfl) ⟨387201, by rfl⟩ : syracuseStep 16520597 = 774403) B774403
theorem B1086871 : Blo 642303 1086871 := bstep (se 1 (by rfl) ⟨815153, by rfl⟩ : syracuseStep 1086871 = 1630307) B1630307
theorem B1447361 : Blo 642303 1447361 := bstep (se 2 (by rfl) ⟨542760, by rfl⟩ : syracuseStep 1447361 = 1085521) B1085521
theorem B726475 : Blo 642303 726475 := bstep (se 1 (by rfl) ⟨544856, by rfl⟩ : syracuseStep 726475 = 1089713) B1089713
theorem B726583 : Blo 642303 726583 := bstep (se 1 (by rfl) ⟨544937, by rfl⟩ : syracuseStep 726583 = 1089875) B1089875
theorem B3675779 : Blo 642303 3675779 := bstep (se 1 (by rfl) ⟨2756834, by rfl⟩ : syracuseStep 3675779 = 5513669) B5513669
theorem B1447577 : Blo 642303 1447577 := bstep (se 2 (by rfl) ⟨542841, by rfl⟩ : syracuseStep 1447577 = 1085683) B1085683
theorem B726763 : Blo 642303 726763 := bstep (se 1 (by rfl) ⟨545072, by rfl⟩ : syracuseStep 726763 = 1090145) B1090145
theorem B1447667 : Blo 642303 1447667 := bstep (se 1 (by rfl) ⟨1085750, by rfl⟩ : syracuseStep 1447667 = 2171501) B2171501
theorem B1447703 : Blo 642303 1447703 := bstep (se 1 (by rfl) ⟨1085777, by rfl⟩ : syracuseStep 1447703 = 2171555) B2171555
theorem B2758475 : Blo 642303 2758475 := bstep (se 1 (by rfl) ⟨2068856, by rfl⟩ : syracuseStep 2758475 = 4137713) B4137713
theorem B726871 : Blo 642303 726871 := bstep (se 1 (by rfl) ⟨545153, by rfl⟩ : syracuseStep 726871 = 1090307) B1090307
theorem B1447883 : Blo 642303 1447883 := bstep (se 1 (by rfl) ⟨1085912, by rfl⟩ : syracuseStep 1447883 = 2171825) B2171825
theorem B1447937 : Blo 642303 1447937 := bstep (se 2 (by rfl) ⟨542976, by rfl⟩ : syracuseStep 1447937 = 1085953) B1085953
theorem B1087499 : Blo 642303 1087499 := bstep (se 1 (by rfl) ⟨815624, by rfl⟩ : syracuseStep 1087499 = 1631249) B1631249
theorem B727051 : Blo 642303 727051 := bstep (se 1 (by rfl) ⟨545288, by rfl⟩ : syracuseStep 727051 = 1090577) B1090577
theorem B2168855 : Blo 642303 2168855 := bstep (se 1 (by rfl) ⟨1626641, by rfl⟩ : syracuseStep 2168855 = 3253283) B3253283
theorem B1087627 : Blo 642303 1087627 := bstep (se 1 (by rfl) ⟨815720, by rfl⟩ : syracuseStep 1087627 = 1631441) B1631441
theorem B1448153 : Blo 642303 1448153 := bstep (se 2 (by rfl) ⟨543057, by rfl⟩ : syracuseStep 1448153 = 1086115) B1086115
theorem B1087769 : Blo 642303 1087769 := bstep (se 2 (by rfl) ⟨407913, by rfl⟩ : syracuseStep 1087769 = 815827) B815827
theorem B1448243 : Blo 642303 1448243 := bstep (se 1 (by rfl) ⟨1086182, by rfl⟩ : syracuseStep 1448243 = 2172365) B2172365
theorem B1448279 : Blo 642303 1448279 := bstep (se 1 (by rfl) ⟨1086209, by rfl⟩ : syracuseStep 1448279 = 2172419) B2172419
theorem B1087897 : Blo 642303 1087897 := bstep (se 2 (by rfl) ⟨407961, by rfl⟩ : syracuseStep 1087897 = 815923) B815923
theorem B1448459 : Blo 642303 1448459 := bstep (se 1 (by rfl) ⟨1086344, by rfl⟩ : syracuseStep 1448459 = 2172689) B2172689
theorem B2169395 : Blo 642303 2169395 := bstep (se 1 (by rfl) ⟨1627046, by rfl⟩ : syracuseStep 2169395 = 3254093) B3254093
theorem B1448513 : Blo 642303 1448513 := bstep (se 2 (by rfl) ⟨543192, by rfl⟩ : syracuseStep 1448513 = 1086385) B1086385
theorem B2759447 : Blo 642303 2759447 := bstep (se 1 (by rfl) ⟨2069585, by rfl⟩ : syracuseStep 2759447 = 4139171) B4139171
theorem B1448729 : Blo 642303 1448729 := bstep (se 2 (by rfl) ⟨543273, by rfl⟩ : syracuseStep 1448729 = 1086547) B1086547
theorem B2169665 : Blo 642303 2169665 := bstep (se 2 (by rfl) ⟨813624, by rfl⟩ : syracuseStep 2169665 = 1627249) B1627249
theorem B1448819 : Blo 642303 1448819 := bstep (se 1 (by rfl) ⟨1086614, by rfl⟩ : syracuseStep 1448819 = 2173229) B2173229
theorem B1448855 : Blo 642303 1448855 := bstep (se 1 (by rfl) ⟨1086641, by rfl⟩ : syracuseStep 1448855 = 2173283) B2173283
theorem B1088471 : Blo 642303 1088471 := bstep (se 1 (by rfl) ⟨816353, by rfl⟩ : syracuseStep 1088471 = 1632707) B1632707
theorem B4889645 : Blo 642303 4889645 := bstep (se 3 (by rfl) ⟨916808, by rfl⟩ : syracuseStep 4889645 = 1833617) B1833617
theorem B1743923 : Blo 642303 1743923 := bstep (se 1 (by rfl) ⟨1307942, by rfl⟩ : syracuseStep 1743923 = 2615885) B2615885
theorem B1449035 : Blo 642303 1449035 := bstep (se 1 (by rfl) ⟨1086776, by rfl⟩ : syracuseStep 1449035 = 2173553) B2173553
theorem B1088599 : Blo 642303 1088599 := bstep (se 1 (by rfl) ⟨816449, by rfl⟩ : syracuseStep 1088599 = 1632899) B1632899
theorem B1449089 : Blo 642303 1449089 := bstep (se 2 (by rfl) ⟨543408, by rfl⟩ : syracuseStep 1449089 = 1086817) B1086817
theorem B1219799 : Blo 642303 1219799 := bstep (se 1 (by rfl) ⟨914849, by rfl⟩ : syracuseStep 1219799 = 1829699) B1829699
theorem B1449305 : Blo 642303 1449305 := bstep (se 2 (by rfl) ⟨543489, by rfl⟩ : syracuseStep 1449305 = 1086979) B1086979
theorem B2170205 : Blo 642303 2170205 := bstep (se 3 (by rfl) ⟨406913, by rfl⟩ : syracuseStep 2170205 = 813827) B813827
theorem B1449395 : Blo 642303 1449395 := bstep (se 1 (by rfl) ⟨1087046, by rfl⟩ : syracuseStep 1449395 = 2174093) B2174093
theorem B2760115 : Blo 642303 2760115 := bstep (se 1 (by rfl) ⟨2070086, by rfl⟩ : syracuseStep 2760115 = 4140173) B4140173
theorem B1449431 : Blo 642303 1449431 := bstep (se 1 (by rfl) ⟨1087073, by rfl⟩ : syracuseStep 1449431 = 2174147) B2174147
theorem B3088003 : Blo 642303 3088003 := bstep (se 1 (by rfl) ⟨2316002, by rfl⟩ : syracuseStep 3088003 = 4632005) B4632005
theorem B990859 : Blo 642303 990859 := bstep (se 1 (by rfl) ⟨743144, by rfl⟩ : syracuseStep 990859 = 1486289) B1486289
theorem B1449611 : Blo 642303 1449611 := bstep (se 1 (by rfl) ⟨1087208, by rfl⟩ : syracuseStep 1449611 = 2174417) B2174417
theorem B1449665 : Blo 642303 1449665 := bstep (se 2 (by rfl) ⟨543624, by rfl⟩ : syracuseStep 1449665 = 1087249) B1087249
theorem B1089227 : Blo 642303 1089227 := bstep (se 1 (by rfl) ⟨816920, by rfl⟩ : syracuseStep 1089227 = 1633841) B1633841
theorem B1220339 : Blo 642303 1220339 := bstep (se 1 (by rfl) ⟨915254, by rfl⟩ : syracuseStep 1220339 = 1830509) B1830509
theorem B1089355 : Blo 642303 1089355 := bstep (se 1 (by rfl) ⟨817016, by rfl⟩ : syracuseStep 1089355 = 1634033) B1634033
theorem B5218141 : Blo 642303 5218141 := bstep (se 3 (by rfl) ⟨978401, by rfl⟩ : syracuseStep 5218141 = 1956803) B1956803
theorem B1449881 : Blo 642303 1449881 := bstep (se 2 (by rfl) ⟨543705, by rfl⟩ : syracuseStep 1449881 = 1087411) B1087411
theorem B1089497 : Blo 642303 1089497 := bstep (se 2 (by rfl) ⟨408561, by rfl⟩ : syracuseStep 1089497 = 817123) B817123
theorem B3678169 : Blo 642303 3678169 := bstep (se 2 (by rfl) ⟨1379313, by rfl⟩ : syracuseStep 3678169 = 2758627) B2758627
theorem B1449971 : Blo 642303 1449971 := bstep (se 1 (by rfl) ⟨1087478, by rfl⟩ : syracuseStep 1449971 = 2174957) B2174957
theorem B1450007 : Blo 642303 1450007 := bstep (se 1 (by rfl) ⟨1087505, by rfl⟩ : syracuseStep 1450007 = 2175011) B2175011
theorem B4464715 : Blo 642303 4464715 := bstep (se 1 (by rfl) ⟨3348536, by rfl⟩ : syracuseStep 4464715 = 6697073) B6697073
theorem B5513291 : Blo 642303 5513291 := bstep (se 1 (by rfl) ⟨4134968, by rfl⟩ : syracuseStep 5513291 = 8269937) B8269937
theorem B1089625 : Blo 642303 1089625 := bstep (se 2 (by rfl) ⟨408609, by rfl⟩ : syracuseStep 1089625 = 817219) B817219
theorem B1450187 : Blo 642303 1450187 := bstep (se 1 (by rfl) ⟨1087640, by rfl⟩ : syracuseStep 1450187 = 2175281) B2175281
theorem B1220825 : Blo 642303 1220825 := bstep (se 2 (by rfl) ⟨457809, by rfl⟩ : syracuseStep 1220825 = 915619) B915619
theorem B1450241 : Blo 642303 1450241 := bstep (se 2 (by rfl) ⟨543840, by rfl⟩ : syracuseStep 1450241 = 1087681) B1087681
theorem B5218661 : Blo 642303 5218661 := bstep (se 4 (by rfl) ⟨489249, by rfl⟩ : syracuseStep 5218661 = 978499) B978499
theorem B696695 : Blo 642303 696695 := bstep (se 1 (by rfl) ⟨522521, by rfl⟩ : syracuseStep 696695 = 1045043) B1045043
theorem B2171339 : Blo 642303 2171339 := bstep (se 1 (by rfl) ⟨1628504, by rfl⟩ : syracuseStep 2171339 = 3257009) B3257009
theorem B1450457 : Blo 642303 1450457 := bstep (se 2 (by rfl) ⟨543921, by rfl⟩ : syracuseStep 1450457 = 1087843) B1087843
theorem B1450547 : Blo 642303 1450547 := bstep (se 1 (by rfl) ⟨1087910, by rfl⟩ : syracuseStep 1450547 = 2175821) B2175821
theorem B1745459 : Blo 642303 1745459 := bstep (se 1 (by rfl) ⟨1309094, by rfl⟩ : syracuseStep 1745459 = 2618189) B2618189
theorem B1548875 : Blo 642303 1548875 := bstep (se 1 (by rfl) ⟨1161656, by rfl⟩ : syracuseStep 1548875 = 2323313) B2323313
theorem B1450583 : Blo 642303 1450583 := bstep (se 1 (by rfl) ⟨1087937, by rfl⟩ : syracuseStep 1450583 = 2175875) B2175875
theorem B1090199 : Blo 642303 1090199 := bstep (se 1 (by rfl) ⟨817649, by rfl⟩ : syracuseStep 1090199 = 1635299) B1635299
theorem B2171609 : Blo 642303 2171609 := bstep (se 2 (by rfl) ⟨814353, by rfl⟩ : syracuseStep 2171609 = 1628707) B1628707
theorem B1450763 : Blo 642303 1450763 := bstep (se 1 (by rfl) ⟨1088072, by rfl⟩ : syracuseStep 1450763 = 2176145) B2176145
theorem B1090327 : Blo 642303 1090327 := bstep (se 1 (by rfl) ⟨817745, by rfl⟩ : syracuseStep 1090327 = 1635491) B1635491
theorem B1450817 : Blo 642303 1450817 := bstep (se 2 (by rfl) ⟨544056, by rfl⟩ : syracuseStep 1450817 = 1088113) B1088113
theorem B3679127 : Blo 642303 3679127 := bstep (se 1 (by rfl) ⟨2759345, by rfl⟩ : syracuseStep 3679127 = 5518691) B5518691
theorem B1745867 : Blo 642303 1745867 := bstep (se 1 (by rfl) ⟨1309400, by rfl⟩ : syracuseStep 1745867 = 2618801) B2618801
theorem B1451033 : Blo 642303 1451033 := bstep (se 2 (by rfl) ⟨544137, by rfl⟩ : syracuseStep 1451033 = 1088275) B1088275
theorem B1451123 : Blo 642303 1451123 := bstep (se 1 (by rfl) ⟨1088342, by rfl⟩ : syracuseStep 1451123 = 2176685) B2176685
theorem B1451159 : Blo 642303 1451159 := bstep (se 1 (by rfl) ⟨1088369, by rfl⟩ : syracuseStep 1451159 = 2176739) B2176739
theorem B1451339 : Blo 642303 1451339 := bstep (se 1 (by rfl) ⟨1088504, by rfl⟩ : syracuseStep 1451339 = 2177009) B2177009
theorem B11937125 : Blo 642303 11937125 := bstep (se 4 (by rfl) ⟨1119105, by rfl⟩ : syracuseStep 11937125 = 2238211) B2238211
theorem B1451393 : Blo 642303 1451393 := bstep (se 2 (by rfl) ⟨544272, by rfl⟩ : syracuseStep 1451393 = 1088545) B1088545
theorem B2172311 : Blo 642303 2172311 := bstep (se 1 (by rfl) ⟨1629233, by rfl⟩ : syracuseStep 2172311 = 3258467) B3258467
theorem B7349777 : Blo 642303 7349777 := bstep (se 2 (by rfl) ⟨2756166, by rfl⟩ : syracuseStep 7349777 = 5512333) B5512333
theorem B1451609 : Blo 642303 1451609 := bstep (se 2 (by rfl) ⟨544353, by rfl⟩ : syracuseStep 1451609 = 1088707) B1088707
theorem B1222283 : Blo 642303 1222283 := bstep (se 1 (by rfl) ⟨916712, by rfl⟩ : syracuseStep 1222283 = 1833425) B1833425
theorem B698027 : Blo 642303 698027 := bstep (se 1 (by rfl) ⟨523520, by rfl⟩ : syracuseStep 698027 = 1047041) B1047041
theorem B1451699 : Blo 642303 1451699 := bstep (se 1 (by rfl) ⟨1088774, by rfl⟩ : syracuseStep 1451699 = 2177549) B2177549
theorem B1451735 : Blo 642303 1451735 := bstep (se 1 (by rfl) ⟨1088801, by rfl⟩ : syracuseStep 1451735 = 2177603) B2177603
theorem B1222465 : Blo 642303 1222465 := bstep (se 2 (by rfl) ⟨458424, by rfl⟩ : syracuseStep 1222465 = 916849) B916849
theorem B1451915 : Blo 642303 1451915 := bstep (se 1 (by rfl) ⟨1088936, by rfl⟩ : syracuseStep 1451915 = 2177873) B2177873
theorem B2172851 : Blo 642303 2172851 := bstep (se 1 (by rfl) ⟨1629638, by rfl⟩ : syracuseStep 2172851 = 3259277) B3259277
theorem B1451969 : Blo 642303 1451969 := bstep (se 2 (by rfl) ⟨544488, by rfl⟩ : syracuseStep 1451969 = 1088977) B1088977
theorem B1746905 : Blo 642303 1746905 := bstep (se 2 (by rfl) ⟨655089, by rfl⟩ : syracuseStep 1746905 = 1310179) B1310179
theorem B1452185 : Blo 642303 1452185 := bstep (se 2 (by rfl) ⟨544569, by rfl⟩ : syracuseStep 1452185 = 1089139) B1089139
theorem B2173121 : Blo 642303 2173121 := bstep (se 2 (by rfl) ⟨814920, by rfl⟩ : syracuseStep 2173121 = 1629841) B1629841
theorem B1452275 : Blo 642303 1452275 := bstep (se 1 (by rfl) ⟨1089206, by rfl⟩ : syracuseStep 1452275 = 2178413) B2178413
theorem B1222913 : Blo 642303 1222913 := bstep (se 2 (by rfl) ⟨458592, by rfl⟩ : syracuseStep 1222913 = 917185) B917185
theorem B1452311 : Blo 642303 1452311 := bstep (se 1 (by rfl) ⟨1089233, by rfl⟩ : syracuseStep 1452311 = 2178467) B2178467
theorem B1452491 : Blo 642303 1452491 := bstep (se 1 (by rfl) ⟨1089368, by rfl⟩ : syracuseStep 1452491 = 2178737) B2178737
theorem B1452545 : Blo 642303 1452545 := bstep (se 2 (by rfl) ⟨544704, by rfl⟩ : syracuseStep 1452545 = 1089409) B1089409
theorem B928279 : Blo 642303 928279 := bstep (se 1 (by rfl) ⟨696209, by rfl⟩ : syracuseStep 928279 = 1392419) B1392419
theorem B1223255 : Blo 642303 1223255 := bstep (se 1 (by rfl) ⟨917441, by rfl⟩ : syracuseStep 1223255 = 1834883) B1834883
theorem B1452761 : Blo 642303 1452761 := bstep (se 2 (by rfl) ⟨544785, by rfl⟩ : syracuseStep 1452761 = 1089571) B1089571
theorem B2173661 : Blo 642303 2173661 := bstep (se 3 (by rfl) ⟨407561, by rfl⟩ : syracuseStep 2173661 = 815123) B815123
theorem B1452851 : Blo 642303 1452851 := bstep (se 1 (by rfl) ⟨1089638, by rfl⟩ : syracuseStep 1452851 = 2179277) B2179277
theorem B1452887 : Blo 642303 1452887 := bstep (se 1 (by rfl) ⟨1089665, by rfl⟩ : syracuseStep 1452887 = 2179331) B2179331
theorem B3910493 : Blo 642303 3910493 := bstep (se 3 (by rfl) ⟨733217, by rfl⟩ : syracuseStep 3910493 = 1466435) B1466435
theorem B4893533 : Blo 642303 4893533 := bstep (se 3 (by rfl) ⟨917537, by rfl⟩ : syracuseStep 4893533 = 1835075) B1835075
theorem B1453067 : Blo 642303 1453067 := bstep (se 1 (by rfl) ⟨1089800, by rfl⟩ : syracuseStep 1453067 = 2179601) B2179601
theorem B1551383 : Blo 642303 1551383 := bstep (se 1 (by rfl) ⟨1163537, by rfl⟩ : syracuseStep 1551383 = 2327075) B2327075
theorem B6204451 : Blo 642303 6204451 := bstep (se 1 (by rfl) ⟨4653338, by rfl⟩ : syracuseStep 6204451 = 9306677) B9306677
theorem B1453121 : Blo 642303 1453121 := bstep (se 2 (by rfl) ⟨544920, by rfl⟩ : syracuseStep 1453121 = 1089841) B1089841
theorem B3255389 : Blo 642303 3255389 := bstep (se 3 (by rfl) ⟨610385, by rfl⟩ : syracuseStep 3255389 = 1220771) B1220771
theorem B1158347 : Blo 642303 1158347 := bstep (se 1 (by rfl) ⟨868760, by rfl⟩ : syracuseStep 1158347 = 1737521) B1737521
theorem B1223923 : Blo 642303 1223923 := bstep (se 1 (by rfl) ⟨917942, by rfl⟩ : syracuseStep 1223923 = 1835885) B1835885
theorem B1453337 : Blo 642303 1453337 := bstep (se 2 (by rfl) ⟨545001, by rfl⟩ : syracuseStep 1453337 = 1090003) B1090003
theorem B1453427 : Blo 642303 1453427 := bstep (se 1 (by rfl) ⟨1090070, by rfl⟩ : syracuseStep 1453427 = 2180141) B2180141
theorem B1453463 : Blo 642303 1453463 := bstep (se 1 (by rfl) ⟨1090097, by rfl⟩ : syracuseStep 1453463 = 2180195) B2180195
theorem B1257011 : Blo 642303 1257011 := bstep (se 1 (by rfl) ⟨942758, by rfl⟩ : syracuseStep 1257011 = 1885517) B1885517
theorem B4959809 : Blo 642303 4959809 := bstep (se 2 (by rfl) ⟨1859928, by rfl⟩ : syracuseStep 4959809 = 3719857) B3719857
theorem B1453643 : Blo 642303 1453643 := bstep (se 1 (by rfl) ⟨1090232, by rfl⟩ : syracuseStep 1453643 = 2180465) B2180465
theorem B1453697 : Blo 642303 1453697 := bstep (se 2 (by rfl) ⟨545136, by rfl⟩ : syracuseStep 1453697 = 1090273) B1090273
theorem B1224371 : Blo 642303 1224371 := bstep (se 1 (by rfl) ⟨918278, by rfl⟩ : syracuseStep 1224371 = 1836557) B1836557
theorem B1224409 : Blo 642303 1224409 := bstep (se 2 (by rfl) ⟨459153, by rfl⟩ : syracuseStep 1224409 = 918307) B918307
theorem B2174795 : Blo 642303 2174795 := bstep (se 1 (by rfl) ⟨1631096, by rfl⟩ : syracuseStep 2174795 = 3262193) B3262193
theorem B1453913 : Blo 642303 1453913 := bstep (se 2 (by rfl) ⟨545217, by rfl⟩ : syracuseStep 1453913 = 1090435) B1090435
theorem B25472945 : Blo 642303 25472945 := bstep (se 2 (by rfl) ⟨9552354, by rfl⟩ : syracuseStep 25472945 = 19104709) B19104709
theorem B1454003 : Blo 642303 1454003 := bstep (se 1 (by rfl) ⟨1090502, by rfl⟩ : syracuseStep 1454003 = 2181005) B2181005
theorem B1454039 : Blo 642303 1454039 := bstep (se 1 (by rfl) ⟨1090529, by rfl⟩ : syracuseStep 1454039 = 2181059) B2181059
theorem B1552459 : Blo 642303 1552459 := bstep (se 1 (by rfl) ⟨1164344, by rfl⟩ : syracuseStep 1552459 = 2328689) B2328689
theorem B2175065 : Blo 642303 2175065 := bstep (se 2 (by rfl) ⟨815649, by rfl⟩ : syracuseStep 2175065 = 1631299) B1631299
theorem B5222551 : Blo 642303 5222551 := bstep (se 1 (by rfl) ⟨3916913, by rfl⟩ : syracuseStep 5222551 = 7833827) B7833827
theorem B1224857 : Blo 642303 1224857 := bstep (se 2 (by rfl) ⟨459321, by rfl⟩ : syracuseStep 1224857 = 918643) B918643
theorem B7352693 : Blo 642303 7352693 := bstep (se 5 (by rfl) ⟨344657, by rfl⟩ : syracuseStep 7352693 = 689315) B689315
theorem B8237699 : Blo 642303 8237699 := bstep (se 1 (by rfl) ⟨6178274, by rfl⟩ : syracuseStep 8237699 = 12356549) B12356549
theorem B2175767 : Blo 642303 2175767 := bstep (se 1 (by rfl) ⟨1631825, by rfl⟩ : syracuseStep 2175767 = 3263651) B3263651
theorem B1225601 : Blo 642303 1225601 := bstep (se 2 (by rfl) ⟨459600, by rfl⟩ : syracuseStep 1225601 = 919201) B919201
theorem B963467 : Blo 642303 963467 := bstep (se 1 (by rfl) ⟨722600, by rfl⟩ : syracuseStep 963467 = 1445201) B1445201
theorem B963479 : Blo 642303 963479 := bstep (se 1 (by rfl) ⟨722609, by rfl⟩ : syracuseStep 963479 = 1445219) B1445219
theorem B963545 : Blo 642303 963545 := bstep (se 2 (by rfl) ⟨361329, by rfl⟩ : syracuseStep 963545 = 722659) B722659
theorem B4174865 : Blo 642303 4174865 := bstep (se 2 (by rfl) ⟨1565574, by rfl⟩ : syracuseStep 4174865 = 3131149) B3131149
theorem B963659 : Blo 642303 963659 := bstep (se 1 (by rfl) ⟨722744, by rfl⟩ : syracuseStep 963659 = 1445489) B1445489
theorem B963671 : Blo 642303 963671 := bstep (se 1 (by rfl) ⟨722753, by rfl⟩ : syracuseStep 963671 = 1445507) B1445507
theorem B1225867 : Blo 642303 1225867 := bstep (se 1 (by rfl) ⟨919400, by rfl⟩ : syracuseStep 1225867 = 1838801) B1838801
theorem B3257495 : Blo 642303 3257495 := bstep (se 1 (by rfl) ⟨2443121, by rfl⟩ : syracuseStep 3257495 = 4886243) B4886243
theorem B963737 : Blo 642303 963737 := bstep (se 2 (by rfl) ⟨361401, by rfl⟩ : syracuseStep 963737 = 722803) B722803
theorem B1651915 : Blo 642303 1651915 := bstep (se 1 (by rfl) ⟨1238936, by rfl⟩ : syracuseStep 1651915 = 2477873) B2477873
theorem B963851 : Blo 642303 963851 := bstep (se 1 (by rfl) ⟨722888, by rfl⟩ : syracuseStep 963851 = 1445777) B1445777
theorem B963863 : Blo 642303 963863 := bstep (se 1 (by rfl) ⟨722897, by rfl⟩ : syracuseStep 963863 = 1445795) B1445795
theorem B2176307 : Blo 642303 2176307 := bstep (se 1 (by rfl) ⟨1632230, by rfl⟩ : syracuseStep 2176307 = 3264461) B3264461
theorem B963929 : Blo 642303 963929 := bstep (se 2 (by rfl) ⟨361473, by rfl⟩ : syracuseStep 963929 = 722947) B722947
theorem B1029527 : Blo 642303 1029527 := bstep (se 1 (by rfl) ⟨772145, by rfl⟩ : syracuseStep 1029527 = 1544291) B1544291
theorem B964043 : Blo 642303 964043 := bstep (se 1 (by rfl) ⟨723032, by rfl⟩ : syracuseStep 964043 = 1446065) B1446065
theorem B964055 : Blo 642303 964055 := bstep (se 1 (by rfl) ⟨723041, by rfl⟩ : syracuseStep 964055 = 1446083) B1446083
theorem B964121 : Blo 642303 964121 := bstep (se 2 (by rfl) ⟨361545, by rfl⟩ : syracuseStep 964121 = 723091) B723091
theorem B2176577 : Blo 642303 2176577 := bstep (se 2 (by rfl) ⟨816216, by rfl⟩ : syracuseStep 2176577 = 1632433) B1632433
theorem B1226315 : Blo 642303 1226315 := bstep (se 1 (by rfl) ⟨919736, by rfl⟩ : syracuseStep 1226315 = 1839473) B1839473
theorem B1029719 : Blo 642303 1029719 := bstep (se 1 (by rfl) ⟨772289, by rfl⟩ : syracuseStep 1029719 = 1544579) B1544579
theorem B964235 : Blo 642303 964235 := bstep (se 1 (by rfl) ⟨723176, by rfl⟩ : syracuseStep 964235 = 1446353) B1446353
theorem B964247 : Blo 642303 964247 := bstep (se 1 (by rfl) ⟨723185, by rfl⟩ : syracuseStep 964247 = 1446371) B1446371
theorem B1029847 : Blo 642303 1029847 := bstep (se 1 (by rfl) ⟨772385, by rfl⟩ : syracuseStep 1029847 = 1544771) B1544771
theorem B964313 : Blo 642303 964313 := bstep (se 2 (by rfl) ⟨361617, by rfl⟩ : syracuseStep 964313 = 723235) B723235
theorem B1226497 : Blo 642303 1226497 := bstep (se 2 (by rfl) ⟨459936, by rfl⟩ : syracuseStep 1226497 = 919873) B919873
theorem B964427 : Blo 642303 964427 := bstep (se 1 (by rfl) ⟨723320, by rfl⟩ : syracuseStep 964427 = 1446641) B1446641
theorem B964439 : Blo 642303 964439 := bstep (se 1 (by rfl) ⟨723329, by rfl⟩ : syracuseStep 964439 = 1446659) B1446659
theorem B964505 : Blo 642303 964505 := bstep (se 2 (by rfl) ⟨361689, by rfl⟩ : syracuseStep 964505 = 723379) B723379
theorem B964619 : Blo 642303 964619 := bstep (se 1 (by rfl) ⟨723464, by rfl⟩ : syracuseStep 964619 = 1446929) B1446929
theorem B964631 : Blo 642303 964631 := bstep (se 1 (by rfl) ⟨723473, by rfl⟩ : syracuseStep 964631 = 1446947) B1446947
theorem B1226839 : Blo 642303 1226839 := bstep (se 1 (by rfl) ⟨920129, by rfl⟩ : syracuseStep 1226839 = 1840259) B1840259
theorem B964697 : Blo 642303 964697 := bstep (se 2 (by rfl) ⟨361761, by rfl⟩ : syracuseStep 964697 = 723523) B723523
theorem B2177117 : Blo 642303 2177117 := bstep (se 3 (by rfl) ⟨408209, by rfl⟩ : syracuseStep 2177117 = 816419) B816419
theorem B2439341 : Blo 642303 2439341 := bstep (se 3 (by rfl) ⟨457376, by rfl⟩ : syracuseStep 2439341 = 914753) B914753
theorem B964811 : Blo 642303 964811 := bstep (se 1 (by rfl) ⟨723608, by rfl⟩ : syracuseStep 964811 = 1447217) B1447217
theorem B964823 : Blo 642303 964823 := bstep (se 1 (by rfl) ⟨723617, by rfl⟩ : syracuseStep 964823 = 1447235) B1447235
theorem B1030411 : Blo 642303 1030411 := bstep (se 1 (by rfl) ⟨772808, by rfl⟩ : syracuseStep 1030411 = 1545617) B1545617
theorem B964889 : Blo 642303 964889 := bstep (se 2 (by rfl) ⟨361833, by rfl⟩ : syracuseStep 964889 = 723667) B723667
theorem B1030487 : Blo 642303 1030487 := bstep (se 1 (by rfl) ⟨772865, by rfl⟩ : syracuseStep 1030487 = 1545731) B1545731
theorem B965003 : Blo 642303 965003 := bstep (se 1 (by rfl) ⟨723752, by rfl⟩ : syracuseStep 965003 = 1447505) B1447505
theorem B965015 : Blo 642303 965015 := bstep (se 1 (by rfl) ⟨723761, by rfl⟩ : syracuseStep 965015 = 1447523) B1447523
theorem B965081 : Blo 642303 965081 := bstep (se 2 (by rfl) ⟨361905, by rfl⟩ : syracuseStep 965081 = 723811) B723811
theorem B1161793 : Blo 642303 1161793 := bstep (se 2 (by rfl) ⟨435672, by rfl⟩ : syracuseStep 1161793 = 871345) B871345
theorem B965195 : Blo 642303 965195 := bstep (se 1 (by rfl) ⟨723896, by rfl⟩ : syracuseStep 965195 = 1447793) B1447793
theorem B965207 : Blo 642303 965207 := bstep (se 1 (by rfl) ⟨723905, by rfl⟩ : syracuseStep 965207 = 1447811) B1447811
theorem B965273 : Blo 642303 965273 := bstep (se 2 (by rfl) ⟨361977, by rfl⟩ : syracuseStep 965273 = 723955) B723955
theorem B965387 : Blo 642303 965387 := bstep (se 1 (by rfl) ⟨724040, by rfl⟩ : syracuseStep 965387 = 1448081) B1448081
theorem B965399 : Blo 642303 965399 := bstep (se 1 (by rfl) ⟨724049, by rfl⟩ : syracuseStep 965399 = 1448099) B1448099
theorem B5487425 : Blo 642303 5487425 := bstep (se 2 (by rfl) ⟨2057784, by rfl⟩ : syracuseStep 5487425 = 4115569) B4115569
theorem B965465 : Blo 642303 965465 := bstep (se 2 (by rfl) ⟨362049, by rfl⟩ : syracuseStep 965465 = 724099) B724099
theorem B2440115 : Blo 642303 2440115 := bstep (se 1 (by rfl) ⟨1830086, by rfl⟩ : syracuseStep 2440115 = 3660173) B3660173
theorem B81476549 : Blo 642303 81476549 := bstep (se 4 (by rfl) ⟨7638426, by rfl⟩ : syracuseStep 81476549 = 15276853) B15276853
theorem B965579 : Blo 642303 965579 := bstep (se 1 (by rfl) ⟨724184, by rfl⟩ : syracuseStep 965579 = 1448369) B1448369
theorem B965591 : Blo 642303 965591 := bstep (se 1 (by rfl) ⟨724193, by rfl⟩ : syracuseStep 965591 = 1448387) B1448387
theorem B965657 : Blo 642303 965657 := bstep (se 2 (by rfl) ⟨362121, by rfl⟩ : syracuseStep 965657 = 724243) B724243
theorem B3095597 : Blo 642303 3095597 := bstep (se 3 (by rfl) ⟨580424, by rfl⟩ : syracuseStep 3095597 = 1160849) B1160849
theorem B965771 : Blo 642303 965771 := bstep (se 1 (by rfl) ⟨724328, by rfl⟩ : syracuseStep 965771 = 1448657) B1448657
theorem B965783 : Blo 642303 965783 := bstep (se 1 (by rfl) ⟨724337, by rfl⟩ : syracuseStep 965783 = 1448675) B1448675
theorem B2178251 : Blo 642303 2178251 := bstep (se 1 (by rfl) ⟨1633688, by rfl⟩ : syracuseStep 2178251 = 3267377) B3267377
theorem B965849 : Blo 642303 965849 := bstep (se 2 (by rfl) ⟨362193, by rfl⟩ : syracuseStep 965849 = 724387) B724387
theorem B7519493 : Blo 642303 7519493 := bstep (se 4 (by rfl) ⟨704952, by rfl⟩ : syracuseStep 7519493 = 1409905) B1409905
theorem B5946659 : Blo 642303 5946659 := bstep (se 1 (by rfl) ⟨4459994, by rfl⟩ : syracuseStep 5946659 = 8919989) B8919989
theorem B965963 : Blo 642303 965963 := bstep (se 1 (by rfl) ⟨724472, by rfl⟩ : syracuseStep 965963 = 1448945) B1448945
theorem B965975 : Blo 642303 965975 := bstep (se 1 (by rfl) ⟨724481, by rfl⟩ : syracuseStep 965975 = 1448963) B1448963
theorem B1490327 : Blo 642303 1490327 := bstep (se 1 (by rfl) ⟨1117745, by rfl⟩ : syracuseStep 1490327 = 2235491) B2235491
theorem B966041 : Blo 642303 966041 := bstep (se 2 (by rfl) ⟨362265, by rfl⟩ : syracuseStep 966041 = 724531) B724531
theorem B2604467 : Blo 642303 2604467 := bstep (se 1 (by rfl) ⟨1953350, by rfl⟩ : syracuseStep 2604467 = 3906701) B3906701
theorem B2178521 : Blo 642303 2178521 := bstep (se 2 (by rfl) ⟨816945, by rfl⟩ : syracuseStep 2178521 = 1633891) B1633891
theorem B966155 : Blo 642303 966155 := bstep (se 1 (by rfl) ⟨724616, by rfl⟩ : syracuseStep 966155 = 1449233) B1449233
theorem B966167 : Blo 642303 966167 := bstep (se 1 (by rfl) ⟨724625, by rfl⟩ : syracuseStep 966167 = 1449251) B1449251
theorem B966233 : Blo 642303 966233 := bstep (se 2 (by rfl) ⟨362337, by rfl⟩ : syracuseStep 966233 = 724675) B724675
theorem B966347 : Blo 642303 966347 := bstep (se 1 (by rfl) ⟨724760, by rfl⟩ : syracuseStep 966347 = 1449521) B1449521
theorem B966359 : Blo 642303 966359 := bstep (se 1 (by rfl) ⟨724769, by rfl⟩ : syracuseStep 966359 = 1449539) B1449539
theorem B1031897 : Blo 642303 1031897 := bstep (se 2 (by rfl) ⟨386961, by rfl⟩ : syracuseStep 1031897 = 773923) B773923
theorem B966425 : Blo 642303 966425 := bstep (se 2 (by rfl) ⟨362409, by rfl⟩ : syracuseStep 966425 = 724819) B724819
theorem B1032025 : Blo 642303 1032025 := bstep (se 2 (by rfl) ⟨387009, by rfl⟩ : syracuseStep 1032025 = 774019) B774019
theorem B966539 : Blo 642303 966539 := bstep (se 1 (by rfl) ⟨724904, by rfl⟩ : syracuseStep 966539 = 1449809) B1449809
theorem B966551 : Blo 642303 966551 := bstep (se 1 (by rfl) ⟨724913, by rfl⟩ : syracuseStep 966551 = 1449827) B1449827
theorem B966617 : Blo 642303 966617 := bstep (se 2 (by rfl) ⟨362481, by rfl⟩ : syracuseStep 966617 = 724963) B724963
theorem B966731 : Blo 642303 966731 := bstep (se 1 (by rfl) ⟨725048, by rfl⟩ : syracuseStep 966731 = 1450097) B1450097
theorem B966743 : Blo 642303 966743 := bstep (se 1 (by rfl) ⟨725057, by rfl⟩ : syracuseStep 966743 = 1450115) B1450115
theorem B2179223 : Blo 642303 2179223 := bstep (se 1 (by rfl) ⟨1634417, by rfl⟩ : syracuseStep 2179223 = 3268835) B3268835
theorem B966809 : Blo 642303 966809 := bstep (se 2 (by rfl) ⟨362553, by rfl⟩ : syracuseStep 966809 = 725107) B725107
theorem B966923 : Blo 642303 966923 := bstep (se 1 (by rfl) ⟨725192, by rfl⟩ : syracuseStep 966923 = 1450385) B1450385
theorem B966935 : Blo 642303 966935 := bstep (se 1 (by rfl) ⟨725201, by rfl⟩ : syracuseStep 966935 = 1450403) B1450403
theorem B967001 : Blo 642303 967001 := bstep (se 2 (by rfl) ⟨362625, by rfl⟩ : syracuseStep 967001 = 725251) B725251
theorem B2441603 : Blo 642303 2441603 := bstep (se 1 (by rfl) ⟨1831202, by rfl⟩ : syracuseStep 2441603 = 3662405) B3662405
theorem B967115 : Blo 642303 967115 := bstep (se 1 (by rfl) ⟨725336, by rfl⟩ : syracuseStep 967115 = 1450673) B1450673
theorem B967127 : Blo 642303 967127 := bstep (se 1 (by rfl) ⟨725345, by rfl⟩ : syracuseStep 967127 = 1450691) B1450691
theorem B3490265 : Blo 642303 3490265 := bstep (se 2 (by rfl) ⟨1308849, by rfl⟩ : syracuseStep 3490265 = 2617699) B2617699
theorem B967193 : Blo 642303 967193 := bstep (se 2 (by rfl) ⟨362697, by rfl⟩ : syracuseStep 967193 = 725395) B725395
theorem B3261059 : Blo 642303 3261059 := bstep (se 1 (by rfl) ⟨2445794, by rfl⟩ : syracuseStep 3261059 = 4891589) B4891589
theorem B967307 : Blo 642303 967307 := bstep (se 1 (by rfl) ⟨725480, by rfl⟩ : syracuseStep 967307 = 1450961) B1450961
theorem B967319 : Blo 642303 967319 := bstep (se 1 (by rfl) ⟨725489, by rfl⟩ : syracuseStep 967319 = 1450979) B1450979
theorem B2179763 : Blo 642303 2179763 := bstep (se 1 (by rfl) ⟨1634822, by rfl⟩ : syracuseStep 2179763 = 3269645) B3269645
theorem B967385 : Blo 642303 967385 := bstep (se 2 (by rfl) ⟨362769, by rfl⟩ : syracuseStep 967385 = 725539) B725539
theorem B2442059 : Blo 642303 2442059 := bstep (se 1 (by rfl) ⟨1831544, by rfl⟩ : syracuseStep 2442059 = 3663089) B3663089
theorem B967499 : Blo 642303 967499 := bstep (se 1 (by rfl) ⟨725624, by rfl⟩ : syracuseStep 967499 = 1451249) B1451249
theorem B967511 : Blo 642303 967511 := bstep (se 1 (by rfl) ⟨725633, by rfl⟩ : syracuseStep 967511 = 1451267) B1451267
theorem B967577 : Blo 642303 967577 := bstep (se 2 (by rfl) ⟨362841, by rfl⟩ : syracuseStep 967577 = 725683) B725683
theorem B2180033 : Blo 642303 2180033 := bstep (se 2 (by rfl) ⟨817512, by rfl⟩ : syracuseStep 2180033 = 1635025) B1635025
theorem B967691 : Blo 642303 967691 := bstep (se 1 (by rfl) ⟨725768, by rfl⟩ : syracuseStep 967691 = 1451537) B1451537
theorem B2442257 : Blo 642303 2442257 := bstep (se 2 (by rfl) ⟨915846, by rfl⟩ : syracuseStep 2442257 = 1831693) B1831693
theorem B967703 : Blo 642303 967703 := bstep (se 1 (by rfl) ⟨725777, by rfl⟩ : syracuseStep 967703 = 1451555) B1451555
theorem B967769 : Blo 642303 967769 := bstep (se 2 (by rfl) ⟨362913, by rfl⟩ : syracuseStep 967769 = 725827) B725827
theorem B967883 : Blo 642303 967883 := bstep (se 1 (by rfl) ⟨725912, by rfl⟩ : syracuseStep 967883 = 1451825) B1451825
theorem B967895 : Blo 642303 967895 := bstep (se 1 (by rfl) ⟨725921, by rfl⟩ : syracuseStep 967895 = 1451843) B1451843
theorem B967961 : Blo 642303 967961 := bstep (se 2 (by rfl) ⟨362985, by rfl⟩ : syracuseStep 967961 = 725971) B725971
theorem B968075 : Blo 642303 968075 := bstep (se 1 (by rfl) ⟨726056, by rfl⟩ : syracuseStep 968075 = 1452113) B1452113
theorem B968087 : Blo 642303 968087 := bstep (se 1 (by rfl) ⟨726065, by rfl⟩ : syracuseStep 968087 = 1452131) B1452131
theorem B968153 : Blo 642303 968153 := bstep (se 2 (by rfl) ⟨363057, by rfl⟩ : syracuseStep 968153 = 726115) B726115
theorem B2180573 : Blo 642303 2180573 := bstep (se 3 (by rfl) ⟨408857, by rfl⟩ : syracuseStep 2180573 = 817715) B817715
theorem B3720779 : Blo 642303 3720779 := bstep (se 1 (by rfl) ⟨2790584, by rfl⟩ : syracuseStep 3720779 = 5581169) B5581169
theorem B968267 : Blo 642303 968267 := bstep (se 1 (by rfl) ⟨726200, by rfl⟩ : syracuseStep 968267 = 1452401) B1452401
theorem B968279 : Blo 642303 968279 := bstep (se 1 (by rfl) ⟨726209, by rfl⟩ : syracuseStep 968279 = 1452419) B1452419
theorem B968345 : Blo 642303 968345 := bstep (se 2 (by rfl) ⟨363129, by rfl⟩ : syracuseStep 968345 = 726259) B726259
theorem B968459 : Blo 642303 968459 := bstep (se 1 (by rfl) ⟨726344, by rfl⟩ : syracuseStep 968459 = 1452689) B1452689
theorem B2443031 : Blo 642303 2443031 := bstep (se 1 (by rfl) ⟨1832273, by rfl⟩ : syracuseStep 2443031 = 3664547) B3664547
theorem B968471 : Blo 642303 968471 := bstep (se 1 (by rfl) ⟨726353, by rfl⟩ : syracuseStep 968471 = 1452707) B1452707
theorem B968537 : Blo 642303 968537 := bstep (se 2 (by rfl) ⟨363201, by rfl⟩ : syracuseStep 968537 = 726403) B726403
theorem B968651 : Blo 642303 968651 := bstep (se 1 (by rfl) ⟨726488, by rfl⟩ : syracuseStep 968651 = 1452977) B1452977
theorem B968663 : Blo 642303 968663 := bstep (se 1 (by rfl) ⟨726497, by rfl⟩ : syracuseStep 968663 = 1452995) B1452995
theorem B2443229 : Blo 642303 2443229 := bstep (se 3 (by rfl) ⟨458105, by rfl⟩ : syracuseStep 2443229 = 916211) B916211
theorem B968729 : Blo 642303 968729 := bstep (se 2 (by rfl) ⟨363273, by rfl⟩ : syracuseStep 968729 = 726547) B726547
theorem B968843 : Blo 642303 968843 := bstep (se 1 (by rfl) ⟨726632, by rfl⟩ : syracuseStep 968843 = 1453265) B1453265
theorem B7850135 : Blo 642303 7850135 := bstep (se 1 (by rfl) ⟨5887601, by rfl⟩ : syracuseStep 7850135 = 11775203) B11775203
theorem B968855 : Blo 642303 968855 := bstep (se 1 (by rfl) ⟨726641, by rfl⟩ : syracuseStep 968855 = 1453283) B1453283
theorem B968921 : Blo 642303 968921 := bstep (se 2 (by rfl) ⟨363345, by rfl⟩ : syracuseStep 968921 = 726691) B726691
theorem B7817477 : Blo 642303 7817477 := bstep (se 4 (by rfl) ⟨732888, by rfl⟩ : syracuseStep 7817477 = 1465777) B1465777
theorem B969035 : Blo 642303 969035 := bstep (se 1 (by rfl) ⟨726776, by rfl⟩ : syracuseStep 969035 = 1453553) B1453553
theorem B969047 : Blo 642303 969047 := bstep (se 1 (by rfl) ⟨726785, by rfl⟩ : syracuseStep 969047 = 1453571) B1453571
theorem B969113 : Blo 642303 969113 := bstep (se 2 (by rfl) ⟨363417, by rfl⟩ : syracuseStep 969113 = 726835) B726835
theorem B969227 : Blo 642303 969227 := bstep (se 1 (by rfl) ⟨726920, by rfl⟩ : syracuseStep 969227 = 1453841) B1453841
theorem B969239 : Blo 642303 969239 := bstep (se 1 (by rfl) ⟨726929, by rfl⟩ : syracuseStep 969239 = 1453859) B1453859
theorem B1100375 : Blo 642303 1100375 := bstep (se 1 (by rfl) ⟨825281, by rfl⟩ : syracuseStep 1100375 = 1650563) B1650563
theorem B969305 : Blo 642303 969305 := bstep (se 2 (by rfl) ⟨363489, by rfl⟩ : syracuseStep 969305 = 726979) B726979
theorem B969419 : Blo 642303 969419 := bstep (se 1 (by rfl) ⟨727064, by rfl⟩ : syracuseStep 969419 = 1454129) B1454129
theorem B969431 : Blo 642303 969431 := bstep (se 1 (by rfl) ⟨727073, by rfl⟩ : syracuseStep 969431 = 1454147) B1454147
theorem B2476889 : Blo 642303 2476889 := bstep (se 2 (by rfl) ⟨928833, by rfl⟩ : syracuseStep 2476889 = 1857667) B1857667
theorem B3722257 : Blo 642303 3722257 := bstep (se 2 (by rfl) ⟨1395846, by rfl⟩ : syracuseStep 3722257 = 2791693) B2791693
theorem B1494131 : Blo 642303 1494131 := bstep (se 1 (by rfl) ⟨1120598, by rfl⟩ : syracuseStep 1494131 = 2241197) B2241197
theorem B642315 : Blo 642303 642315 := bstep (se 1 (by rfl) ⟨481736, by rfl⟩ : syracuseStep 642315 = 963473) B963473
theorem B642327 : Blo 642303 642327 := bstep (se 1 (by rfl) ⟨481745, by rfl⟩ : syracuseStep 642327 = 963491) B963491
theorem B5295395 : Blo 642303 5295395 := bstep (se 1 (by rfl) ⟨3971546, by rfl⟩ : syracuseStep 5295395 = 7943093) B7943093
theorem B642347 : Blo 642303 642347 := bstep (se 1 (by rfl) ⟨481760, by rfl⟩ : syracuseStep 642347 = 963521) B963521
theorem B642359 : Blo 642303 642359 := bstep (se 1 (by rfl) ⟨481769, by rfl⟩ : syracuseStep 642359 = 963539) B963539
theorem B642379 : Blo 642303 642379 := bstep (se 1 (by rfl) ⟨481784, by rfl⟩ : syracuseStep 642379 = 963569) B963569
theorem B642391 : Blo 642303 642391 := bstep (se 1 (by rfl) ⟨481793, by rfl⟩ : syracuseStep 642391 = 963587) B963587
theorem B642411 : Blo 642303 642411 := bstep (se 1 (by rfl) ⟨481808, by rfl⟩ : syracuseStep 642411 = 963617) B963617
theorem B642423 : Blo 642303 642423 := bstep (se 1 (by rfl) ⟨481817, by rfl⟩ : syracuseStep 642423 = 963635) B963635
theorem B642443 : Blo 642303 642443 := bstep (se 1 (by rfl) ⟨481832, by rfl⟩ : syracuseStep 642443 = 963665) B963665
theorem B642455 : Blo 642303 642455 := bstep (se 1 (by rfl) ⟨481841, by rfl⟩ : syracuseStep 642455 = 963683) B963683
theorem B642475 : Blo 642303 642475 := bstep (se 1 (by rfl) ⟨481856, by rfl⟩ : syracuseStep 642475 = 963713) B963713
theorem B642487 : Blo 642303 642487 := bstep (se 1 (by rfl) ⟨481865, by rfl⟩ : syracuseStep 642487 = 963731) B963731
theorem B642507 : Blo 642303 642507 := bstep (se 1 (by rfl) ⟨481880, by rfl⟩ : syracuseStep 642507 = 963761) B963761
theorem B642519 : Blo 642303 642519 := bstep (se 1 (by rfl) ⟨481889, by rfl⟩ : syracuseStep 642519 = 963779) B963779
theorem B642539 : Blo 642303 642539 := bstep (se 1 (by rfl) ⟨481904, by rfl⟩ : syracuseStep 642539 = 963809) B963809
theorem B642551 : Blo 642303 642551 := bstep (se 1 (by rfl) ⟨481913, by rfl⟩ : syracuseStep 642551 = 963827) B963827
theorem B642571 : Blo 642303 642571 := bstep (se 1 (by rfl) ⟨481928, by rfl⟩ : syracuseStep 642571 = 963857) B963857
theorem B642583 : Blo 642303 642583 := bstep (se 1 (by rfl) ⟨481937, by rfl⟩ : syracuseStep 642583 = 963875) B963875
theorem B1592855 : Blo 642303 1592855 := bstep (se 1 (by rfl) ⟨1194641, by rfl⟩ : syracuseStep 1592855 = 2389283) B2389283
theorem B8474147 : Blo 642303 8474147 := bstep (se 1 (by rfl) ⟨6355610, by rfl⟩ : syracuseStep 8474147 = 12711221) B12711221
theorem B642603 : Blo 642303 642603 := bstep (se 1 (by rfl) ⟨481952, by rfl⟩ : syracuseStep 642603 = 963905) B963905
theorem B642615 : Blo 642303 642615 := bstep (se 1 (by rfl) ⟨481961, by rfl⟩ : syracuseStep 642615 = 963923) B963923
theorem B642635 : Blo 642303 642635 := bstep (se 1 (by rfl) ⟨481976, by rfl⟩ : syracuseStep 642635 = 963953) B963953
theorem B642647 : Blo 642303 642647 := bstep (se 1 (by rfl) ⟨481985, by rfl⟩ : syracuseStep 642647 = 963971) B963971
theorem B642667 : Blo 642303 642667 := bstep (se 1 (by rfl) ⟨482000, by rfl⟩ : syracuseStep 642667 = 964001) B964001
theorem B642679 : Blo 642303 642679 := bstep (se 1 (by rfl) ⟨482009, by rfl⟩ : syracuseStep 642679 = 964019) B964019
theorem B642699 : Blo 642303 642699 := bstep (se 1 (by rfl) ⟨482024, by rfl⟩ : syracuseStep 642699 = 964049) B964049
theorem B642711 : Blo 642303 642711 := bstep (se 1 (by rfl) ⟨482033, by rfl⟩ : syracuseStep 642711 = 964067) B964067
theorem B642731 : Blo 642303 642731 := bstep (se 1 (by rfl) ⟨482048, by rfl⟩ : syracuseStep 642731 = 964097) B964097
theorem B10440373 : Blo 642303 10440373 := bstep (se 5 (by rfl) ⟨489392, by rfl⟩ : syracuseStep 10440373 = 978785) B978785
theorem B642743 : Blo 642303 642743 := bstep (se 1 (by rfl) ⟨482057, by rfl⟩ : syracuseStep 642743 = 964115) B964115
theorem B642763 : Blo 642303 642763 := bstep (se 1 (by rfl) ⟨482072, by rfl⟩ : syracuseStep 642763 = 964145) B964145
theorem B642775 : Blo 642303 642775 := bstep (se 1 (by rfl) ⟨482081, by rfl⟩ : syracuseStep 642775 = 964163) B964163
theorem B642795 : Blo 642303 642795 := bstep (se 1 (by rfl) ⟨482096, by rfl⟩ : syracuseStep 642795 = 964193) B964193
theorem B642807 : Blo 642303 642807 := bstep (se 1 (by rfl) ⟨482105, by rfl⟩ : syracuseStep 642807 = 964211) B964211
theorem B642827 : Blo 642303 642827 := bstep (se 1 (by rfl) ⟨482120, by rfl⟩ : syracuseStep 642827 = 964241) B964241
theorem B642839 : Blo 642303 642839 := bstep (se 1 (by rfl) ⟨482129, by rfl⟩ : syracuseStep 642839 = 964259) B964259
theorem B642859 : Blo 642303 642859 := bstep (se 1 (by rfl) ⟨482144, by rfl⟩ : syracuseStep 642859 = 964289) B964289
theorem B642871 : Blo 642303 642871 := bstep (se 1 (by rfl) ⟨482153, by rfl⟩ : syracuseStep 642871 = 964307) B964307
theorem B642891 : Blo 642303 642891 := bstep (se 1 (by rfl) ⟨482168, by rfl⟩ : syracuseStep 642891 = 964337) B964337
theorem B642903 : Blo 642303 642903 := bstep (se 1 (by rfl) ⟨482177, by rfl⟩ : syracuseStep 642903 = 964355) B964355
theorem B642923 : Blo 642303 642923 := bstep (se 1 (by rfl) ⟨482192, by rfl⟩ : syracuseStep 642923 = 964385) B964385
theorem B642935 : Blo 642303 642935 := bstep (se 1 (by rfl) ⟨482201, by rfl⟩ : syracuseStep 642935 = 964403) B964403
theorem B2445187 : Blo 642303 2445187 := bstep (se 1 (by rfl) ⟨1833890, by rfl⟩ : syracuseStep 2445187 = 3667781) B3667781
theorem B642955 : Blo 642303 642955 := bstep (se 1 (by rfl) ⟨482216, by rfl⟩ : syracuseStep 642955 = 964433) B964433
theorem B642967 : Blo 642303 642967 := bstep (se 1 (by rfl) ⟨482225, by rfl⟩ : syracuseStep 642967 = 964451) B964451
theorem B642987 : Blo 642303 642987 := bstep (se 1 (by rfl) ⟨482240, by rfl⟩ : syracuseStep 642987 = 964481) B964481
theorem B642999 : Blo 642303 642999 := bstep (se 1 (by rfl) ⟨482249, by rfl⟩ : syracuseStep 642999 = 964499) B964499
theorem B643019 : Blo 642303 643019 := bstep (se 1 (by rfl) ⟨482264, by rfl⟩ : syracuseStep 643019 = 964529) B964529
theorem B643031 : Blo 642303 643031 := bstep (se 1 (by rfl) ⟨482273, by rfl⟩ : syracuseStep 643031 = 964547) B964547
theorem B643051 : Blo 642303 643051 := bstep (se 1 (by rfl) ⟨482288, by rfl⟩ : syracuseStep 643051 = 964577) B964577
theorem B643063 : Blo 642303 643063 := bstep (se 1 (by rfl) ⟨482297, by rfl⟩ : syracuseStep 643063 = 964595) B964595
theorem B643083 : Blo 642303 643083 := bstep (se 1 (by rfl) ⟨482312, by rfl⟩ : syracuseStep 643083 = 964625) B964625
theorem B643095 : Blo 642303 643095 := bstep (se 1 (by rfl) ⟨482321, by rfl⟩ : syracuseStep 643095 = 964643) B964643
theorem B643115 : Blo 642303 643115 := bstep (se 1 (by rfl) ⟨482336, by rfl⟩ : syracuseStep 643115 = 964673) B964673
theorem B643127 : Blo 642303 643127 := bstep (se 1 (by rfl) ⟨482345, by rfl⟩ : syracuseStep 643127 = 964691) B964691
theorem B9261125 : Blo 642303 9261125 := bstep (se 4 (by rfl) ⟨868230, by rfl⟩ : syracuseStep 9261125 = 1736461) B1736461
theorem B643147 : Blo 642303 643147 := bstep (se 1 (by rfl) ⟨482360, by rfl⟩ : syracuseStep 643147 = 964721) B964721
theorem B643159 : Blo 642303 643159 := bstep (se 1 (by rfl) ⟨482369, by rfl⟩ : syracuseStep 643159 = 964739) B964739
theorem B643179 : Blo 642303 643179 := bstep (se 1 (by rfl) ⟨482384, by rfl⟩ : syracuseStep 643179 = 964769) B964769
theorem B643191 : Blo 642303 643191 := bstep (se 1 (by rfl) ⟨482393, by rfl⟩ : syracuseStep 643191 = 964787) B964787
theorem B643211 : Blo 642303 643211 := bstep (se 1 (by rfl) ⟨482408, by rfl⟩ : syracuseStep 643211 = 964817) B964817
theorem B643223 : Blo 642303 643223 := bstep (se 1 (by rfl) ⟨482417, by rfl⟩ : syracuseStep 643223 = 964835) B964835
theorem B643243 : Blo 642303 643243 := bstep (se 1 (by rfl) ⟨482432, by rfl⟩ : syracuseStep 643243 = 964865) B964865
theorem B2445491 : Blo 642303 2445491 := bstep (se 1 (by rfl) ⟨1834118, by rfl⟩ : syracuseStep 2445491 = 3668237) B3668237
theorem B643255 : Blo 642303 643255 := bstep (se 1 (by rfl) ⟨482441, by rfl⟩ : syracuseStep 643255 = 964883) B964883
theorem B643275 : Blo 642303 643275 := bstep (se 1 (by rfl) ⟨482456, by rfl⟩ : syracuseStep 643275 = 964913) B964913
theorem B643287 : Blo 642303 643287 := bstep (se 1 (by rfl) ⟨482465, by rfl⟩ : syracuseStep 643287 = 964931) B964931
theorem B643307 : Blo 642303 643307 := bstep (se 1 (by rfl) ⟨482480, by rfl⟩ : syracuseStep 643307 = 964961) B964961
theorem B643319 : Blo 642303 643319 := bstep (se 1 (by rfl) ⟨482489, by rfl⟩ : syracuseStep 643319 = 964979) B964979
theorem B643339 : Blo 642303 643339 := bstep (se 1 (by rfl) ⟨482504, by rfl⟩ : syracuseStep 643339 = 965009) B965009
theorem B3264785 : Blo 642303 3264785 := bstep (se 2 (by rfl) ⟨1224294, by rfl⟩ : syracuseStep 3264785 = 2448589) B2448589
theorem B643351 : Blo 642303 643351 := bstep (se 1 (by rfl) ⟨482513, by rfl⟩ : syracuseStep 643351 = 965027) B965027
theorem B643371 : Blo 642303 643371 := bstep (se 1 (by rfl) ⟨482528, by rfl⟩ : syracuseStep 643371 = 965057) B965057
theorem B1626419 : Blo 642303 1626419 := bstep (se 1 (by rfl) ⟨1219814, by rfl⟩ : syracuseStep 1626419 = 2439629) B2439629
theorem B1855795 : Blo 642303 1855795 := bstep (se 1 (by rfl) ⟨1391846, by rfl⟩ : syracuseStep 1855795 = 2783693) B2783693
theorem B2609459 : Blo 642303 2609459 := bstep (se 1 (by rfl) ⟨1957094, by rfl⟩ : syracuseStep 2609459 = 3914189) B3914189
theorem B643383 : Blo 642303 643383 := bstep (se 1 (by rfl) ⟨482537, by rfl⟩ : syracuseStep 643383 = 965075) B965075
theorem B6607169 : Blo 642303 6607169 := bstep (se 2 (by rfl) ⟨2477688, by rfl⟩ : syracuseStep 6607169 = 4955377) B4955377
theorem B643403 : Blo 642303 643403 := bstep (se 1 (by rfl) ⟨482552, by rfl⟩ : syracuseStep 643403 = 965105) B965105
theorem B643415 : Blo 642303 643415 := bstep (se 1 (by rfl) ⟨482561, by rfl⟩ : syracuseStep 643415 = 965123) B965123
theorem B643435 : Blo 642303 643435 := bstep (se 1 (by rfl) ⟨482576, by rfl⟩ : syracuseStep 643435 = 965153) B965153
theorem B643447 : Blo 642303 643447 := bstep (se 1 (by rfl) ⟨482585, by rfl⟩ : syracuseStep 643447 = 965171) B965171
theorem B643467 : Blo 642303 643467 := bstep (se 1 (by rfl) ⟨482600, by rfl⟩ : syracuseStep 643467 = 965201) B965201
theorem B643479 : Blo 642303 643479 := bstep (se 1 (by rfl) ⟨482609, by rfl⟩ : syracuseStep 643479 = 965219) B965219
theorem B643499 : Blo 642303 643499 := bstep (se 1 (by rfl) ⟨482624, by rfl⟩ : syracuseStep 643499 = 965249) B965249
theorem B3264947 : Blo 642303 3264947 := bstep (se 1 (by rfl) ⟨2448710, by rfl⟩ : syracuseStep 3264947 = 4897421) B4897421
theorem B643511 : Blo 642303 643511 := bstep (se 1 (by rfl) ⟨482633, by rfl⟩ : syracuseStep 643511 = 965267) B965267
theorem B643531 : Blo 642303 643531 := bstep (se 1 (by rfl) ⟨482648, by rfl⟩ : syracuseStep 643531 = 965297) B965297
theorem B5493197 : Blo 642303 5493197 := bstep (se 3 (by rfl) ⟨1029974, by rfl⟩ : syracuseStep 5493197 = 2059949) B2059949
theorem B643543 : Blo 642303 643543 := bstep (se 1 (by rfl) ⟨482657, by rfl⟩ : syracuseStep 643543 = 965315) B965315
theorem B643563 : Blo 642303 643563 := bstep (se 1 (by rfl) ⟨482672, by rfl⟩ : syracuseStep 643563 = 965345) B965345
theorem B643575 : Blo 642303 643575 := bstep (se 1 (by rfl) ⟨482681, by rfl⟩ : syracuseStep 643575 = 965363) B965363
theorem B643595 : Blo 642303 643595 := bstep (se 1 (by rfl) ⟨482696, by rfl⟩ : syracuseStep 643595 = 965393) B965393
theorem B643607 : Blo 642303 643607 := bstep (se 1 (by rfl) ⟨482705, by rfl⟩ : syracuseStep 643607 = 965411) B965411
theorem B643627 : Blo 642303 643627 := bstep (se 1 (by rfl) ⟨482720, by rfl⟩ : syracuseStep 643627 = 965441) B965441
theorem B643639 : Blo 642303 643639 := bstep (se 1 (by rfl) ⟨482729, by rfl⟩ : syracuseStep 643639 = 965459) B965459
theorem B643659 : Blo 642303 643659 := bstep (se 1 (by rfl) ⟨482744, by rfl⟩ : syracuseStep 643659 = 965489) B965489
theorem B643671 : Blo 642303 643671 := bstep (se 1 (by rfl) ⟨482753, by rfl⟩ : syracuseStep 643671 = 965507) B965507
theorem B1626713 : Blo 642303 1626713 := bstep (se 2 (by rfl) ⟨610017, by rfl⟩ : syracuseStep 1626713 = 1220035) B1220035
theorem B643691 : Blo 642303 643691 := bstep (se 1 (by rfl) ⟨482768, by rfl⟩ : syracuseStep 643691 = 965537) B965537
theorem B643703 : Blo 642303 643703 := bstep (se 1 (by rfl) ⟨482777, by rfl⟩ : syracuseStep 643703 = 965555) B965555
theorem B643723 : Blo 642303 643723 := bstep (se 1 (by rfl) ⟨482792, by rfl⟩ : syracuseStep 643723 = 965585) B965585
theorem B643735 : Blo 642303 643735 := bstep (se 1 (by rfl) ⟨482801, by rfl⟩ : syracuseStep 643735 = 965603) B965603
theorem B643755 : Blo 642303 643755 := bstep (se 1 (by rfl) ⟨482816, by rfl⟩ : syracuseStep 643755 = 965633) B965633
theorem B643767 : Blo 642303 643767 := bstep (se 1 (by rfl) ⟨482825, by rfl⟩ : syracuseStep 643767 = 965651) B965651
theorem B643787 : Blo 642303 643787 := bstep (se 1 (by rfl) ⟨482840, by rfl⟩ : syracuseStep 643787 = 965681) B965681
theorem B643799 : Blo 642303 643799 := bstep (se 1 (by rfl) ⟨482849, by rfl⟩ : syracuseStep 643799 = 965699) B965699
theorem B643819 : Blo 642303 643819 := bstep (se 1 (by rfl) ⟨482864, by rfl⟩ : syracuseStep 643819 = 965729) B965729
theorem B643831 : Blo 642303 643831 := bstep (se 1 (by rfl) ⟨482873, by rfl⟩ : syracuseStep 643831 = 965747) B965747
theorem B643851 : Blo 642303 643851 := bstep (se 1 (by rfl) ⟨482888, by rfl⟩ : syracuseStep 643851 = 965777) B965777
theorem B643863 : Blo 642303 643863 := bstep (se 1 (by rfl) ⟨482897, by rfl⟩ : syracuseStep 643863 = 965795) B965795
theorem B643883 : Blo 642303 643883 := bstep (se 1 (by rfl) ⟨482912, by rfl⟩ : syracuseStep 643883 = 965825) B965825
theorem B643895 : Blo 642303 643895 := bstep (se 1 (by rfl) ⟨482921, by rfl⟩ : syracuseStep 643895 = 965843) B965843
theorem B2446145 : Blo 642303 2446145 := bstep (se 2 (by rfl) ⟨917304, by rfl⟩ : syracuseStep 2446145 = 1834609) B1834609
theorem B643915 : Blo 642303 643915 := bstep (se 1 (by rfl) ⟨482936, by rfl⟩ : syracuseStep 643915 = 965873) B965873
theorem B643927 : Blo 642303 643927 := bstep (se 1 (by rfl) ⟨482945, by rfl⟩ : syracuseStep 643927 = 965891) B965891
theorem B643947 : Blo 642303 643947 := bstep (se 1 (by rfl) ⟨482960, by rfl⟩ : syracuseStep 643947 = 965921) B965921
theorem B643959 : Blo 642303 643959 := bstep (se 1 (by rfl) ⟨482969, by rfl⟩ : syracuseStep 643959 = 965939) B965939
theorem B643979 : Blo 642303 643979 := bstep (se 1 (by rfl) ⟨482984, by rfl⟩ : syracuseStep 643979 = 965969) B965969
theorem B643991 : Blo 642303 643991 := bstep (se 1 (by rfl) ⟨482993, by rfl⟩ : syracuseStep 643991 = 965987) B965987
theorem B644011 : Blo 642303 644011 := bstep (se 1 (by rfl) ⟨483008, by rfl⟩ : syracuseStep 644011 = 966017) B966017
theorem B644023 : Blo 642303 644023 := bstep (se 1 (by rfl) ⟨483017, by rfl⟩ : syracuseStep 644023 = 966035) B966035
theorem B644043 : Blo 642303 644043 := bstep (se 1 (by rfl) ⟨483032, by rfl⟩ : syracuseStep 644043 = 966065) B966065
theorem B644055 : Blo 642303 644055 := bstep (se 1 (by rfl) ⟨483041, by rfl⟩ : syracuseStep 644055 = 966083) B966083
theorem B644075 : Blo 642303 644075 := bstep (se 1 (by rfl) ⟨483056, by rfl⟩ : syracuseStep 644075 = 966113) B966113
theorem B644087 : Blo 642303 644087 := bstep (se 1 (by rfl) ⟨483065, by rfl⟩ : syracuseStep 644087 = 966131) B966131
theorem B644107 : Blo 642303 644107 := bstep (se 1 (by rfl) ⟨483080, by rfl⟩ : syracuseStep 644107 = 966161) B966161
theorem B644119 : Blo 642303 644119 := bstep (se 1 (by rfl) ⟨483089, by rfl⟩ : syracuseStep 644119 = 966179) B966179
theorem B644139 : Blo 642303 644139 := bstep (se 1 (by rfl) ⟨483104, by rfl⟩ : syracuseStep 644139 = 966209) B966209
theorem B644151 : Blo 642303 644151 := bstep (se 1 (by rfl) ⟨483113, by rfl⟩ : syracuseStep 644151 = 966227) B966227
theorem B644171 : Blo 642303 644171 := bstep (se 1 (by rfl) ⟨483128, by rfl⟩ : syracuseStep 644171 = 966257) B966257
theorem B644183 : Blo 642303 644183 := bstep (se 1 (by rfl) ⟨483137, by rfl⟩ : syracuseStep 644183 = 966275) B966275
theorem B644203 : Blo 642303 644203 := bstep (se 1 (by rfl) ⟨483152, by rfl⟩ : syracuseStep 644203 = 966305) B966305
theorem B644215 : Blo 642303 644215 := bstep (se 1 (by rfl) ⟨483161, by rfl⟩ : syracuseStep 644215 = 966323) B966323
theorem B644235 : Blo 642303 644235 := bstep (se 1 (by rfl) ⟨483176, by rfl⟩ : syracuseStep 644235 = 966353) B966353
theorem B644247 : Blo 642303 644247 := bstep (se 1 (by rfl) ⟨483185, by rfl⟩ : syracuseStep 644247 = 966371) B966371
theorem B644267 : Blo 642303 644267 := bstep (se 1 (by rfl) ⟨483200, by rfl⟩ : syracuseStep 644267 = 966401) B966401
theorem B644279 : Blo 642303 644279 := bstep (se 1 (by rfl) ⟨483209, by rfl⟩ : syracuseStep 644279 = 966419) B966419
theorem B644299 : Blo 642303 644299 := bstep (se 1 (by rfl) ⟨483224, by rfl⟩ : syracuseStep 644299 = 966449) B966449
theorem B644311 : Blo 642303 644311 := bstep (se 1 (by rfl) ⟨483233, by rfl⟩ : syracuseStep 644311 = 966467) B966467
theorem B644331 : Blo 642303 644331 := bstep (se 1 (by rfl) ⟨483248, by rfl⟩ : syracuseStep 644331 = 966497) B966497
theorem B644343 : Blo 642303 644343 := bstep (se 1 (by rfl) ⟨483257, by rfl⟩ : syracuseStep 644343 = 966515) B966515
theorem B644363 : Blo 642303 644363 := bstep (se 1 (by rfl) ⟨483272, by rfl⟩ : syracuseStep 644363 = 966545) B966545
theorem B644375 : Blo 642303 644375 := bstep (se 1 (by rfl) ⟨483281, by rfl⟩ : syracuseStep 644375 = 966563) B966563
theorem B644395 : Blo 642303 644395 := bstep (se 1 (by rfl) ⟨483296, by rfl⟩ : syracuseStep 644395 = 966593) B966593
theorem B644407 : Blo 642303 644407 := bstep (se 1 (by rfl) ⟨483305, by rfl⟩ : syracuseStep 644407 = 966611) B966611
theorem B2610497 : Blo 642303 2610497 := bstep (se 2 (by rfl) ⟨978936, by rfl⟩ : syracuseStep 2610497 = 1957873) B1957873
theorem B644427 : Blo 642303 644427 := bstep (se 1 (by rfl) ⟨483320, by rfl⟩ : syracuseStep 644427 = 966641) B966641
theorem B644439 : Blo 642303 644439 := bstep (se 1 (by rfl) ⟨483329, by rfl⟩ : syracuseStep 644439 = 966659) B966659
theorem B644459 : Blo 642303 644459 := bstep (se 1 (by rfl) ⟨483344, by rfl⟩ : syracuseStep 644459 = 966689) B966689
theorem B644471 : Blo 642303 644471 := bstep (se 1 (by rfl) ⟨483353, by rfl⟩ : syracuseStep 644471 = 966707) B966707
theorem B644491 : Blo 642303 644491 := bstep (se 1 (by rfl) ⟨483368, by rfl⟩ : syracuseStep 644491 = 966737) B966737
theorem B644503 : Blo 642303 644503 := bstep (se 1 (by rfl) ⟨483377, by rfl⟩ : syracuseStep 644503 = 966755) B966755
theorem B1398169 : Blo 642303 1398169 := bstep (se 2 (by rfl) ⟨524313, by rfl⟩ : syracuseStep 1398169 = 1048627) B1048627
theorem B644523 : Blo 642303 644523 := bstep (se 1 (by rfl) ⟨483392, by rfl⟩ : syracuseStep 644523 = 966785) B966785
theorem B644535 : Blo 642303 644535 := bstep (se 1 (by rfl) ⟨483401, by rfl⟩ : syracuseStep 644535 = 966803) B966803
theorem B644555 : Blo 642303 644555 := bstep (se 1 (by rfl) ⟨483416, by rfl⟩ : syracuseStep 644555 = 966833) B966833
theorem B644567 : Blo 642303 644567 := bstep (se 1 (by rfl) ⟨483425, by rfl⟩ : syracuseStep 644567 = 966851) B966851
theorem B644587 : Blo 642303 644587 := bstep (se 1 (by rfl) ⟨483440, by rfl⟩ : syracuseStep 644587 = 966881) B966881
theorem B644599 : Blo 642303 644599 := bstep (se 1 (by rfl) ⟨483449, by rfl⟩ : syracuseStep 644599 = 966899) B966899
theorem B644619 : Blo 642303 644619 := bstep (se 1 (by rfl) ⟨483464, by rfl⟩ : syracuseStep 644619 = 966929) B966929
theorem B644631 : Blo 642303 644631 := bstep (se 1 (by rfl) ⟨483473, by rfl⟩ : syracuseStep 644631 = 966947) B966947
theorem B644651 : Blo 642303 644651 := bstep (se 1 (by rfl) ⟨483488, by rfl⟩ : syracuseStep 644651 = 966977) B966977
theorem B644663 : Blo 642303 644663 := bstep (se 1 (by rfl) ⟨483497, by rfl⟩ : syracuseStep 644663 = 966995) B966995
theorem B644683 : Blo 642303 644683 := bstep (se 1 (by rfl) ⟨483512, by rfl⟩ : syracuseStep 644683 = 967025) B967025
theorem B644695 : Blo 642303 644695 := bstep (se 1 (by rfl) ⟨483521, by rfl⟩ : syracuseStep 644695 = 967043) B967043
theorem B5232221 : Blo 642303 5232221 := bstep (se 3 (by rfl) ⟨981041, by rfl⟩ : syracuseStep 5232221 = 1962083) B1962083
theorem B644715 : Blo 642303 644715 := bstep (se 1 (by rfl) ⟨483536, by rfl⟩ : syracuseStep 644715 = 967073) B967073
theorem B644727 : Blo 642303 644727 := bstep (se 1 (by rfl) ⟨483545, by rfl⟩ : syracuseStep 644727 = 967091) B967091
theorem B644747 : Blo 642303 644747 := bstep (se 1 (by rfl) ⟨483560, by rfl⟩ : syracuseStep 644747 = 967121) B967121
theorem B644759 : Blo 642303 644759 := bstep (se 1 (by rfl) ⟨483569, by rfl⟩ : syracuseStep 644759 = 967139) B967139
theorem B644779 : Blo 642303 644779 := bstep (se 1 (by rfl) ⟨483584, by rfl⟩ : syracuseStep 644779 = 967169) B967169
theorem B644791 : Blo 642303 644791 := bstep (se 1 (by rfl) ⟨483593, by rfl⟩ : syracuseStep 644791 = 967187) B967187
theorem B644811 : Blo 642303 644811 := bstep (se 1 (by rfl) ⟨483608, by rfl⟩ : syracuseStep 644811 = 967217) B967217
theorem B644823 : Blo 642303 644823 := bstep (se 1 (by rfl) ⟨483617, by rfl⟩ : syracuseStep 644823 = 967235) B967235
theorem B644843 : Blo 642303 644843 := bstep (se 1 (by rfl) ⟨483632, by rfl⟩ : syracuseStep 644843 = 967265) B967265
theorem B644855 : Blo 642303 644855 := bstep (se 1 (by rfl) ⟨483641, by rfl⟩ : syracuseStep 644855 = 967283) B967283
theorem B644875 : Blo 642303 644875 := bstep (se 1 (by rfl) ⟨483656, by rfl⟩ : syracuseStep 644875 = 967313) B967313
theorem B644887 : Blo 642303 644887 := bstep (se 1 (by rfl) ⟨483665, by rfl⟩ : syracuseStep 644887 = 967331) B967331
theorem B644907 : Blo 642303 644907 := bstep (se 1 (by rfl) ⟨483680, by rfl⟩ : syracuseStep 644907 = 967361) B967361
theorem B644919 : Blo 642303 644919 := bstep (se 1 (by rfl) ⟨483689, by rfl⟩ : syracuseStep 644919 = 967379) B967379
theorem B644939 : Blo 642303 644939 := bstep (se 1 (by rfl) ⟨483704, by rfl⟩ : syracuseStep 644939 = 967409) B967409
theorem B644951 : Blo 642303 644951 := bstep (se 1 (by rfl) ⟨483713, by rfl⟩ : syracuseStep 644951 = 967427) B967427
theorem B644971 : Blo 642303 644971 := bstep (se 1 (by rfl) ⟨483728, by rfl⟩ : syracuseStep 644971 = 967457) B967457
theorem B644983 : Blo 642303 644983 := bstep (se 1 (by rfl) ⟨483737, by rfl⟩ : syracuseStep 644983 = 967475) B967475
theorem B645003 : Blo 642303 645003 := bstep (se 1 (by rfl) ⟨483752, by rfl⟩ : syracuseStep 645003 = 967505) B967505
theorem B645015 : Blo 642303 645015 := bstep (se 1 (by rfl) ⟨483761, by rfl⟩ : syracuseStep 645015 = 967523) B967523
theorem B645035 : Blo 642303 645035 := bstep (se 1 (by rfl) ⟨483776, by rfl⟩ : syracuseStep 645035 = 967553) B967553
theorem B645047 : Blo 642303 645047 := bstep (se 1 (by rfl) ⟨483785, by rfl⟩ : syracuseStep 645047 = 967571) B967571
theorem B645067 : Blo 642303 645067 := bstep (se 1 (by rfl) ⟨483800, by rfl⟩ : syracuseStep 645067 = 967601) B967601
theorem B645079 : Blo 642303 645079 := bstep (se 1 (by rfl) ⟨483809, by rfl⟩ : syracuseStep 645079 = 967619) B967619
theorem B645099 : Blo 642303 645099 := bstep (se 1 (by rfl) ⟨483824, by rfl⟩ : syracuseStep 645099 = 967649) B967649
theorem B645111 : Blo 642303 645111 := bstep (se 1 (by rfl) ⟨483833, by rfl⟩ : syracuseStep 645111 = 967667) B967667
theorem B645131 : Blo 642303 645131 := bstep (se 1 (by rfl) ⟨483848, by rfl⟩ : syracuseStep 645131 = 967697) B967697
theorem B645143 : Blo 642303 645143 := bstep (se 1 (by rfl) ⟨483857, by rfl⟩ : syracuseStep 645143 = 967715) B967715
theorem B645163 : Blo 642303 645163 := bstep (se 1 (by rfl) ⟨483872, by rfl⟩ : syracuseStep 645163 = 967745) B967745
theorem B2447405 : Blo 642303 2447405 := bstep (se 3 (by rfl) ⟨458888, by rfl⟩ : syracuseStep 2447405 = 917777) B917777
theorem B645175 : Blo 642303 645175 := bstep (se 1 (by rfl) ⟨483881, by rfl⟩ : syracuseStep 645175 = 967763) B967763
theorem B2447435 : Blo 642303 2447435 := bstep (se 1 (by rfl) ⟨1835576, by rfl⟩ : syracuseStep 2447435 = 3671153) B3671153
theorem B645195 : Blo 642303 645195 := bstep (se 1 (by rfl) ⟨483896, by rfl⟩ : syracuseStep 645195 = 967793) B967793
theorem B645207 : Blo 642303 645207 := bstep (se 1 (by rfl) ⟨483905, by rfl⟩ : syracuseStep 645207 = 967811) B967811
theorem B645227 : Blo 642303 645227 := bstep (se 1 (by rfl) ⟨483920, by rfl⟩ : syracuseStep 645227 = 967841) B967841
theorem B645239 : Blo 642303 645239 := bstep (se 1 (by rfl) ⟨483929, by rfl⟩ : syracuseStep 645239 = 967859) B967859
theorem B645259 : Blo 642303 645259 := bstep (se 1 (by rfl) ⟨483944, by rfl⟩ : syracuseStep 645259 = 967889) B967889
theorem B645271 : Blo 642303 645271 := bstep (se 1 (by rfl) ⟨483953, by rfl⟩ : syracuseStep 645271 = 967907) B967907
theorem B645291 : Blo 642303 645291 := bstep (se 1 (by rfl) ⟨483968, by rfl⟩ : syracuseStep 645291 = 967937) B967937
theorem B645303 : Blo 642303 645303 := bstep (se 1 (by rfl) ⟨483977, by rfl⟩ : syracuseStep 645303 = 967955) B967955
theorem B1628363 : Blo 642303 1628363 := bstep (se 1 (by rfl) ⟨1221272, by rfl⟩ : syracuseStep 1628363 = 2442545) B2442545
theorem B645323 : Blo 642303 645323 := bstep (se 1 (by rfl) ⟨483992, by rfl⟩ : syracuseStep 645323 = 967985) B967985
theorem B645335 : Blo 642303 645335 := bstep (se 1 (by rfl) ⟨484001, by rfl⟩ : syracuseStep 645335 = 968003) B968003
theorem B645355 : Blo 642303 645355 := bstep (se 1 (by rfl) ⟨484016, by rfl⟩ : syracuseStep 645355 = 968033) B968033
theorem B645367 : Blo 642303 645367 := bstep (se 1 (by rfl) ⟨484025, by rfl⟩ : syracuseStep 645367 = 968051) B968051
theorem B645387 : Blo 642303 645387 := bstep (se 1 (by rfl) ⟨484040, by rfl⟩ : syracuseStep 645387 = 968081) B968081
theorem B645399 : Blo 642303 645399 := bstep (se 1 (by rfl) ⟨484049, by rfl⟩ : syracuseStep 645399 = 968099) B968099
theorem B645419 : Blo 642303 645419 := bstep (se 1 (by rfl) ⟨484064, by rfl⟩ : syracuseStep 645419 = 968129) B968129
theorem B645431 : Blo 642303 645431 := bstep (se 1 (by rfl) ⟨484073, by rfl⟩ : syracuseStep 645431 = 968147) B968147
theorem B4413761 : Blo 642303 4413761 := bstep (se 2 (by rfl) ⟨1655160, by rfl⟩ : syracuseStep 4413761 = 3310321) B3310321
theorem B3266891 : Blo 642303 3266891 := bstep (se 1 (by rfl) ⟨2450168, by rfl⟩ : syracuseStep 3266891 = 4900337) B4900337
theorem B645451 : Blo 642303 645451 := bstep (se 1 (by rfl) ⟨484088, by rfl⟩ : syracuseStep 645451 = 968177) B968177
theorem B645463 : Blo 642303 645463 := bstep (se 1 (by rfl) ⟨484097, by rfl⟩ : syracuseStep 645463 = 968195) B968195
theorem B645483 : Blo 642303 645483 := bstep (se 1 (by rfl) ⟨484112, by rfl⟩ : syracuseStep 645483 = 968225) B968225
theorem B645495 : Blo 642303 645495 := bstep (se 1 (by rfl) ⟨484121, by rfl⟩ : syracuseStep 645495 = 968243) B968243
theorem B645515 : Blo 642303 645515 := bstep (se 1 (by rfl) ⟨484136, by rfl⟩ : syracuseStep 645515 = 968273) B968273
theorem B645527 : Blo 642303 645527 := bstep (se 1 (by rfl) ⟨484145, by rfl⟩ : syracuseStep 645527 = 968291) B968291
theorem B645547 : Blo 642303 645547 := bstep (se 1 (by rfl) ⟨484160, by rfl⟩ : syracuseStep 645547 = 968321) B968321
theorem B645559 : Blo 642303 645559 := bstep (se 1 (by rfl) ⟨484169, by rfl⟩ : syracuseStep 645559 = 968339) B968339
theorem B645579 : Blo 642303 645579 := bstep (se 1 (by rfl) ⟨484184, by rfl⟩ : syracuseStep 645579 = 968369) B968369
theorem B645591 : Blo 642303 645591 := bstep (se 1 (by rfl) ⟨484193, by rfl⟩ : syracuseStep 645591 = 968387) B968387
theorem B645611 : Blo 642303 645611 := bstep (se 1 (by rfl) ⟨484208, by rfl⟩ : syracuseStep 645611 = 968417) B968417
theorem B645623 : Blo 642303 645623 := bstep (se 1 (by rfl) ⟨484217, by rfl⟩ : syracuseStep 645623 = 968435) B968435
theorem B645643 : Blo 642303 645643 := bstep (se 1 (by rfl) ⟨484232, by rfl⟩ : syracuseStep 645643 = 968465) B968465
theorem B645655 : Blo 642303 645655 := bstep (se 1 (by rfl) ⟨484241, by rfl⟩ : syracuseStep 645655 = 968483) B968483
theorem B645675 : Blo 642303 645675 := bstep (se 1 (by rfl) ⟨484256, by rfl⟩ : syracuseStep 645675 = 968513) B968513
theorem B1956403 : Blo 642303 1956403 := bstep (se 1 (by rfl) ⟨1467302, by rfl⟩ : syracuseStep 1956403 = 2934605) B2934605
theorem B645687 : Blo 642303 645687 := bstep (se 1 (by rfl) ⟨484265, by rfl⟩ : syracuseStep 645687 = 968531) B968531
theorem B645707 : Blo 642303 645707 := bstep (se 1 (by rfl) ⟨484280, by rfl⟩ : syracuseStep 645707 = 968561) B968561
theorem B645719 : Blo 642303 645719 := bstep (se 1 (by rfl) ⟨484289, by rfl⟩ : syracuseStep 645719 = 968579) B968579
theorem B645739 : Blo 642303 645739 := bstep (se 1 (by rfl) ⟨484304, by rfl⟩ : syracuseStep 645739 = 968609) B968609
theorem B645751 : Blo 642303 645751 := bstep (se 1 (by rfl) ⟨484313, by rfl⟩ : syracuseStep 645751 = 968627) B968627
theorem B645771 : Blo 642303 645771 := bstep (se 1 (by rfl) ⟨484328, by rfl⟩ : syracuseStep 645771 = 968657) B968657
theorem B645783 : Blo 642303 645783 := bstep (se 1 (by rfl) ⟨484337, by rfl⟩ : syracuseStep 645783 = 968675) B968675
theorem B645803 : Blo 642303 645803 := bstep (se 1 (by rfl) ⟨484352, by rfl⟩ : syracuseStep 645803 = 968705) B968705
theorem B645815 : Blo 642303 645815 := bstep (se 1 (by rfl) ⟨484361, by rfl⟩ : syracuseStep 645815 = 968723) B968723
theorem B645835 : Blo 642303 645835 := bstep (se 1 (by rfl) ⟨484376, by rfl⟩ : syracuseStep 645835 = 968753) B968753
theorem B645847 : Blo 642303 645847 := bstep (se 1 (by rfl) ⟨484385, by rfl⟩ : syracuseStep 645847 = 968771) B968771
theorem B1465049 : Blo 642303 1465049 := bstep (se 2 (by rfl) ⟨549393, by rfl⟩ : syracuseStep 1465049 = 1098787) B1098787
theorem B2448089 : Blo 642303 2448089 := bstep (se 2 (by rfl) ⟨918033, by rfl⟩ : syracuseStep 2448089 = 1836067) B1836067
theorem B645867 : Blo 642303 645867 := bstep (se 1 (by rfl) ⟨484400, by rfl⟩ : syracuseStep 645867 = 968801) B968801
theorem B645879 : Blo 642303 645879 := bstep (se 1 (by rfl) ⟨484409, by rfl⟩ : syracuseStep 645879 = 968819) B968819
theorem B645899 : Blo 642303 645899 := bstep (se 1 (by rfl) ⟨484424, by rfl⟩ : syracuseStep 645899 = 968849) B968849
theorem B645911 : Blo 642303 645911 := bstep (se 1 (by rfl) ⟨484433, by rfl⟩ : syracuseStep 645911 = 968867) B968867
theorem B645931 : Blo 642303 645931 := bstep (se 1 (by rfl) ⟨484448, by rfl⟩ : syracuseStep 645931 = 968897) B968897
theorem B645943 : Blo 642303 645943 := bstep (se 1 (by rfl) ⟨484457, by rfl⟩ : syracuseStep 645943 = 968915) B968915
theorem B645963 : Blo 642303 645963 := bstep (se 1 (by rfl) ⟨484472, by rfl⟩ : syracuseStep 645963 = 968945) B968945
theorem B645975 : Blo 642303 645975 := bstep (se 1 (by rfl) ⟨484481, by rfl⟩ : syracuseStep 645975 = 968963) B968963
theorem B2349917 : Blo 642303 2349917 := bstep (se 3 (by rfl) ⟨440609, by rfl⟩ : syracuseStep 2349917 = 881219) B881219
theorem B645995 : Blo 642303 645995 := bstep (se 1 (by rfl) ⟨484496, by rfl⟩ : syracuseStep 645995 = 968993) B968993
theorem B646007 : Blo 642303 646007 := bstep (se 1 (by rfl) ⟨484505, by rfl⟩ : syracuseStep 646007 = 969011) B969011
theorem B646027 : Blo 642303 646027 := bstep (se 1 (by rfl) ⟨484520, by rfl⟩ : syracuseStep 646027 = 969041) B969041
theorem B646039 : Blo 642303 646039 := bstep (se 1 (by rfl) ⟨484529, by rfl⟩ : syracuseStep 646039 = 969059) B969059
theorem B646059 : Blo 642303 646059 := bstep (se 1 (by rfl) ⟨484544, by rfl⟩ : syracuseStep 646059 = 969089) B969089
theorem B646071 : Blo 642303 646071 := bstep (se 1 (by rfl) ⟨484553, by rfl⟩ : syracuseStep 646071 = 969107) B969107
theorem B646091 : Blo 642303 646091 := bstep (se 1 (by rfl) ⟨484568, by rfl⟩ : syracuseStep 646091 = 969137) B969137
theorem B646103 : Blo 642303 646103 := bstep (se 1 (by rfl) ⟨484577, by rfl⟩ : syracuseStep 646103 = 969155) B969155
theorem B646123 : Blo 642303 646123 := bstep (se 1 (by rfl) ⟨484592, by rfl⟩ : syracuseStep 646123 = 969185) B969185
theorem B646135 : Blo 642303 646135 := bstep (se 1 (by rfl) ⟨484601, by rfl⟩ : syracuseStep 646135 = 969203) B969203
theorem B646155 : Blo 642303 646155 := bstep (se 1 (by rfl) ⟨484616, by rfl⟩ : syracuseStep 646155 = 969233) B969233
theorem B2448407 : Blo 642303 2448407 := bstep (se 1 (by rfl) ⟨1836305, by rfl⟩ : syracuseStep 2448407 = 3672611) B3672611
theorem B646167 : Blo 642303 646167 := bstep (se 1 (by rfl) ⟨484625, by rfl⟩ : syracuseStep 646167 = 969251) B969251
theorem B646187 : Blo 642303 646187 := bstep (se 1 (by rfl) ⟨484640, by rfl⟩ : syracuseStep 646187 = 969281) B969281
theorem B646199 : Blo 642303 646199 := bstep (se 1 (by rfl) ⟨484649, by rfl⟩ : syracuseStep 646199 = 969299) B969299
theorem B646219 : Blo 642303 646219 := bstep (se 1 (by rfl) ⟨484664, by rfl⟩ : syracuseStep 646219 = 969329) B969329
theorem B646231 : Blo 642303 646231 := bstep (se 1 (by rfl) ⟨484673, by rfl⟩ : syracuseStep 646231 = 969347) B969347
theorem B646251 : Blo 642303 646251 := bstep (se 1 (by rfl) ⟨484688, by rfl⟩ : syracuseStep 646251 = 969377) B969377
theorem B646263 : Blo 642303 646263 := bstep (se 1 (by rfl) ⟨484697, by rfl⟩ : syracuseStep 646263 = 969395) B969395
theorem B646283 : Blo 642303 646283 := bstep (se 1 (by rfl) ⟨484712, by rfl⟩ : syracuseStep 646283 = 969425) B969425
theorem B1629335 : Blo 642303 1629335 := bstep (se 1 (by rfl) ⟨1222001, by rfl⟩ : syracuseStep 1629335 = 2444003) B2444003
theorem B646295 : Blo 642303 646295 := bstep (se 1 (by rfl) ⟨484721, by rfl⟩ : syracuseStep 646295 = 969443) B969443
theorem B1465843 : Blo 642303 1465843 := bstep (se 1 (by rfl) ⟨1099382, by rfl⟩ : syracuseStep 1465843 = 2198765) B2198765
theorem B2743901 : Blo 642303 2743901 := bstep (se 3 (by rfl) ⟨514481, by rfl⟩ : syracuseStep 2743901 = 1028963) B1028963
theorem B2449075 : Blo 642303 2449075 := bstep (se 1 (by rfl) ⟨1836806, by rfl⟩ : syracuseStep 2449075 = 3673613) B3673613
theorem B1630003 : Blo 642303 1630003 := bstep (se 1 (by rfl) ⟨1222502, by rfl⟩ : syracuseStep 1630003 = 2445005) B2445005
theorem B8282033 : Blo 642303 8282033 := bstep (se 2 (by rfl) ⟨3105762, by rfl⟩ : syracuseStep 8282033 = 6211525) B6211525
theorem B1630145 : Blo 642303 1630145 := bstep (se 2 (by rfl) ⟨611304, by rfl⟩ : syracuseStep 1630145 = 1222609) B1222609
theorem B3268673 : Blo 642303 3268673 := bstep (se 2 (by rfl) ⟨1225752, by rfl⟩ : syracuseStep 3268673 = 2451505) B2451505
theorem B2318539 : Blo 642303 2318539 := bstep (se 1 (by rfl) ⟨1738904, by rfl⟩ : syracuseStep 2318539 = 3477809) B3477809
theorem B4645325 : Blo 642303 4645325 := bstep (se 3 (by rfl) ⟨870998, by rfl⟩ : syracuseStep 4645325 = 1741997) B1741997
theorem B3662657 : Blo 642303 3662657 := bstep (se 2 (by rfl) ⟨1373496, by rfl⟩ : syracuseStep 3662657 = 2746993) B2746993
theorem B2450321 : Blo 642303 2450321 := bstep (se 2 (by rfl) ⟨918870, by rfl⟩ : syracuseStep 2450321 = 1837741) B1837741
theorem B4711517 : Blo 642303 4711517 := bstep (se 3 (by rfl) ⟨883409, by rfl⟩ : syracuseStep 4711517 = 1766819) B1766819
theorem B1631411 : Blo 642303 1631411 := bstep (se 1 (by rfl) ⟨1223558, by rfl⟩ : syracuseStep 1631411 = 2447117) B2447117
theorem B2451019 : Blo 642303 2451019 := bstep (se 1 (by rfl) ⟨1838264, by rfl⟩ : syracuseStep 2451019 = 3676529) B3676529
theorem B1861271 : Blo 642303 1861271 := bstep (se 1 (by rfl) ⟨1395953, by rfl⟩ : syracuseStep 1861271 = 2791907) B2791907
theorem B1631947 : Blo 642303 1631947 := bstep (se 1 (by rfl) ⟨1223960, by rfl⟩ : syracuseStep 1631947 = 2447921) B2447921
theorem B976601 : Blo 642303 976601 := bstep (se 2 (by rfl) ⟨366225, by rfl⟩ : syracuseStep 976601 = 732451) B732451
theorem B4122413 : Blo 642303 4122413 := bstep (se 3 (by rfl) ⟨772952, by rfl⟩ : syracuseStep 4122413 = 1545905) B1545905
theorem B2615105 : Blo 642303 2615105 := bstep (se 2 (by rfl) ⟨980664, by rfl⟩ : syracuseStep 2615105 = 1961329) B1961329
theorem B1632089 : Blo 642303 1632089 := bstep (se 2 (by rfl) ⟨612033, by rfl⟩ : syracuseStep 1632089 = 1224067) B1224067
theorem B2451293 : Blo 642303 2451293 := bstep (se 3 (by rfl) ⟨459617, by rfl⟩ : syracuseStep 2451293 = 919235) B919235
theorem B3270617 : Blo 642303 3270617 := bstep (se 2 (by rfl) ⟨1226481, by rfl⟩ : syracuseStep 3270617 = 2452963) B2452963
theorem B1468697 : Blo 642303 1468697 := bstep (se 2 (by rfl) ⟨550761, by rfl⟩ : syracuseStep 1468697 = 1101523) B1101523
theorem B5499211 : Blo 642303 5499211 := bstep (se 1 (by rfl) ⟨4124408, by rfl⟩ : syracuseStep 5499211 = 8248817) B8248817
theorem B2451991 : Blo 642303 2451991 := bstep (se 1 (by rfl) ⟨1838993, by rfl⟩ : syracuseStep 2451991 = 3677987) B3677987
theorem B813655 : Blo 642303 813655 := bstep (se 1 (by rfl) ⟨610241, by rfl⟩ : syracuseStep 813655 = 1220483) B1220483
theorem B5499485 : Blo 642303 5499485 := bstep (se 3 (by rfl) ⟨1031153, by rfl⟩ : syracuseStep 5499485 = 2062307) B2062307
theorem B1632919 : Blo 642303 1632919 := bstep (se 1 (by rfl) ⟨1224689, by rfl⟩ : syracuseStep 1632919 = 2449379) B2449379
theorem B1043275 : Blo 642303 1043275 := bstep (se 1 (by rfl) ⟨782456, by rfl⟩ : syracuseStep 1043275 = 1564913) B1564913
theorem B9431909 : Blo 642303 9431909 := bstep (se 4 (by rfl) ⟨884241, by rfl⟩ : syracuseStep 9431909 = 1768483) B1768483
theorem B2747267 : Blo 642303 2747267 := bstep (se 1 (by rfl) ⟨2060450, by rfl⟩ : syracuseStep 2747267 = 4120901) B4120901
theorem B1043353 : Blo 642303 1043353 := bstep (se 2 (by rfl) ⟨391257, by rfl⟩ : syracuseStep 1043353 = 782515) B782515
theorem B2616371 : Blo 642303 2616371 := bstep (se 1 (by rfl) ⟨1962278, by rfl⟩ : syracuseStep 2616371 = 3924557) B3924557
theorem B1633355 : Blo 642303 1633355 := bstep (se 1 (by rfl) ⟨1225016, by rfl⟩ : syracuseStep 1633355 = 2450033) B2450033
theorem B3665047 : Blo 642303 3665047 := bstep (se 1 (by rfl) ⟨2748785, by rfl⟩ : syracuseStep 3665047 = 5497571) B5497571
theorem B1830109 : Blo 642303 1830109 := bstep (se 3 (by rfl) ⟨343145, by rfl⟩ : syracuseStep 1830109 = 686291) B686291
theorem B2452781 : Blo 642303 2452781 := bstep (se 3 (by rfl) ⟨459896, by rfl⟩ : syracuseStep 2452781 = 919793) B919793
theorem B22310261 : Blo 642303 22310261 := bstep (se 5 (by rfl) ⟨1045793, by rfl⟩ : syracuseStep 22310261 = 2091587) B2091587
theorem B814475 : Blo 642303 814475 := bstep (se 1 (by rfl) ⟨610856, by rfl⟩ : syracuseStep 814475 = 1221713) B1221713
theorem B1633729 : Blo 642303 1633729 := bstep (se 2 (by rfl) ⟨612648, by rfl⟩ : syracuseStep 1633729 = 1225297) B1225297
theorem B1830451 : Blo 642303 1830451 := bstep (se 1 (by rfl) ⟨1372838, by rfl⟩ : syracuseStep 1830451 = 2745677) B2745677
theorem B5500547 : Blo 642303 5500547 := bstep (se 1 (by rfl) ⟨4125410, by rfl⟩ : syracuseStep 5500547 = 8250821) B8250821
theorem B1175233 : Blo 642303 1175233 := bstep (se 2 (by rfl) ⟨440712, by rfl⟩ : syracuseStep 1175233 = 881425) B881425
theorem B5861069 : Blo 642303 5861069 := bstep (se 3 (by rfl) ⟨1098950, by rfl⟩ : syracuseStep 5861069 = 2197901) B2197901
theorem B6188845 : Blo 642303 6188845 := bstep (se 3 (by rfl) ⟨1160408, by rfl⟩ : syracuseStep 6188845 = 2320817) B2320817
theorem B1306547 : Blo 642303 1306547 := bstep (se 1 (by rfl) ⟨979910, by rfl⟩ : syracuseStep 1306547 = 1959821) B1959821
theorem B1634327 : Blo 642303 1634327 := bstep (se 1 (by rfl) ⟨1225745, by rfl⟩ : syracuseStep 1634327 = 2451491) B2451491
theorem B815179 : Blo 642303 815179 := bstep (se 1 (by rfl) ⟨611384, by rfl⟩ : syracuseStep 815179 = 1222769) B1222769
theorem B4878467 : Blo 642303 4878467 := bstep (se 1 (by rfl) ⟨3658850, by rfl⟩ : syracuseStep 4878467 = 7317701) B7317701
theorem B1372403 : Blo 642303 1372403 := bstep (se 1 (by rfl) ⟨1029302, by rfl⟩ : syracuseStep 1372403 = 2058605) B2058605
theorem B815447 : Blo 642303 815447 := bstep (se 1 (by rfl) ⟨611585, by rfl⟩ : syracuseStep 815447 = 1223171) B1223171
theorem B1831385 : Blo 642303 1831385 := bstep (se 2 (by rfl) ⟨686769, by rfl⟩ : syracuseStep 1831385 = 1373539) B1373539
theorem B2945497 : Blo 642303 2945497 := bstep (se 2 (by rfl) ⟨1104561, by rfl⟩ : syracuseStep 2945497 = 2209123) B2209123
theorem B11760389 : Blo 642303 11760389 := bstep (se 4 (by rfl) ⟨1102536, by rfl⟩ : syracuseStep 11760389 = 2205073) B2205073
theorem B1635137 : Blo 642303 1635137 := bstep (se 2 (by rfl) ⟨613176, by rfl⟩ : syracuseStep 1635137 = 1226353) B1226353
theorem B1307585 : Blo 642303 1307585 := bstep (se 2 (by rfl) ⟨490344, by rfl⟩ : syracuseStep 1307585 = 980689) B980689
theorem B816151 : Blo 642303 816151 := bstep (se 1 (by rfl) ⟨612113, by rfl⟩ : syracuseStep 816151 = 1224227) B1224227
theorem B1373249 : Blo 642303 1373249 := bstep (se 2 (by rfl) ⟨514968, by rfl⟩ : syracuseStep 1373249 = 1029937) B1029937
theorem B10613911 : Blo 642303 10613911 := bstep (se 1 (by rfl) ⟨7960433, by rfl⟩ : syracuseStep 10613911 = 15920867) B15920867
theorem B652459 : Blo 642303 652459 := bstep (se 1 (by rfl) ⟨489344, by rfl⟩ : syracuseStep 652459 = 978689) B978689
theorem B980299 : Blo 642303 980299 := bstep (se 1 (by rfl) ⟨735224, by rfl⟩ : syracuseStep 980299 = 1470449) B1470449
theorem B1635673 : Blo 642303 1635673 := bstep (se 2 (by rfl) ⟨613377, by rfl⟩ : syracuseStep 1635673 = 1226755) B1226755
theorem B914827 : Blo 642303 914827 := bstep (se 1 (by rfl) ⟨686120, by rfl⟩ : syracuseStep 914827 = 1372241) B1372241
theorem B1373591 : Blo 642303 1373591 := bstep (se 1 (by rfl) ⟨1030193, by rfl⟩ : syracuseStep 1373591 = 2060387) B2060387
theorem B2061719 : Blo 642303 2061719 := bstep (se 1 (by rfl) ⟨1546289, by rfl⟩ : syracuseStep 2061719 = 3092579) B3092579
theorem B2094913 : Blo 642303 2094913 := bstep (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) B1571185
theorem B1832797 : Blo 642303 1832797 := bstep (se 3 (by rfl) ⟨343649, by rfl⟩ : syracuseStep 1832797 = 687299) B687299
theorem B3929957 : Blo 642303 3929957 := bstep (se 4 (by rfl) ⟨368433, by rfl⟩ : syracuseStep 3929957 = 736867) B736867
theorem B1833025 : Blo 642303 1833025 := bstep (se 2 (by rfl) ⟨687384, by rfl⟩ : syracuseStep 1833025 = 1374769) B1374769
theorem B5863697 : Blo 642303 5863697 := bstep (se 2 (by rfl) ⟨2198886, by rfl⟩ : syracuseStep 5863697 = 4397773) B4397773
theorem B8255789 : Blo 642303 8255789 := bstep (se 3 (by rfl) ⟨1547960, by rfl⟩ : syracuseStep 8255789 = 3095921) B3095921
theorem B4127051 : Blo 642303 4127051 := bstep (se 1 (by rfl) ⟨3095288, by rfl⟩ : syracuseStep 4127051 = 6190577) B6190577
theorem B3930443 : Blo 642303 3930443 := bstep (se 1 (by rfl) ⟨2947832, by rfl⟩ : syracuseStep 3930443 = 5895665) B5895665
theorem B2324825 : Blo 642303 2324825 := bstep (se 2 (by rfl) ⟨871809, by rfl⟩ : syracuseStep 2324825 = 1743619) B1743619
theorem B1833367 : Blo 642303 1833367 := bstep (se 1 (by rfl) ⟨1375025, by rfl⟩ : syracuseStep 1833367 = 2750051) B2750051
theorem B916057 : Blo 642303 916057 := bstep (se 2 (by rfl) ⟨343521, by rfl⟩ : syracuseStep 916057 = 687043) B687043
theorem B4651613 : Blo 642303 4651613 := bstep (se 3 (by rfl) ⟨872177, by rfl⟩ : syracuseStep 4651613 = 1744355) B1744355
theorem B817867 : Blo 642303 817867 := bstep (se 1 (by rfl) ⟨613400, by rfl⟩ : syracuseStep 817867 = 1226801) B1226801
theorem B686923 : Blo 642303 686923 := bstep (se 1 (by rfl) ⟨515192, by rfl⟩ : syracuseStep 686923 = 1030385) B1030385
theorem B1178443 : Blo 642303 1178443 := bstep (se 1 (by rfl) ⟨883832, by rfl⟩ : syracuseStep 1178443 = 1767665) B1767665
theorem B1178507 : Blo 642303 1178507 := bstep (se 1 (by rfl) ⟨883880, by rfl⟩ : syracuseStep 1178507 = 1767761) B1767761
theorem B2751383 : Blo 642303 2751383 := bstep (se 1 (by rfl) ⟨2063537, by rfl⟩ : syracuseStep 2751383 = 4127075) B4127075
theorem B4651955 : Blo 642303 4651955 := bstep (se 1 (by rfl) ⟨3488966, by rfl⟩ : syracuseStep 4651955 = 6977933) B6977933
theorem B1834073 : Blo 642303 1834073 := bstep (se 2 (by rfl) ⟨687777, by rfl⟩ : syracuseStep 1834073 = 1375555) B1375555
theorem B2751691 : Blo 642303 2751691 := bstep (se 1 (by rfl) ⟨2063768, by rfl⟩ : syracuseStep 2751691 = 4127537) B4127537
theorem B654571 : Blo 642303 654571 := bstep (se 1 (by rfl) ⟨490928, by rfl⟩ : syracuseStep 654571 = 981857) B981857
theorem B1310131 : Blo 642303 1310131 := bstep (se 1 (by rfl) ⟨982598, by rfl⟩ : syracuseStep 1310131 = 1965197) B1965197
theorem B4881869 : Blo 642303 4881869 := bstep (se 3 (by rfl) ⟨915350, by rfl⟩ : syracuseStep 4881869 = 1830701) B1830701
theorem B7044569 : Blo 642303 7044569 := bstep (se 2 (by rfl) ⟨2641713, by rfl⟩ : syracuseStep 7044569 = 5283427) B5283427
theorem B2751965 : Blo 642303 2751965 := bstep (se 3 (by rfl) ⟨515993, by rfl⟩ : syracuseStep 2751965 = 1031987) B1031987
theorem B687863 : Blo 642303 687863 := bstep (se 1 (by rfl) ⟨515897, by rfl⟩ : syracuseStep 687863 = 1031795) B1031795
theorem B2064179 : Blo 642303 2064179 := bstep (se 1 (by rfl) ⟨1548134, by rfl⟩ : syracuseStep 2064179 = 3096269) B3096269
theorem B917401 : Blo 642303 917401 := bstep (se 2 (by rfl) ⟨344025, by rfl⟩ : syracuseStep 917401 = 688051) B688051
theorem B18087857 : Blo 642303 18087857 := bstep (se 2 (by rfl) ⟨6782946, by rfl⟩ : syracuseStep 18087857 = 13565893) B13565893
theorem B4882355 : Blo 642303 4882355 := bstep (se 1 (by rfl) ⟨3661766, by rfl⟩ : syracuseStep 4882355 = 7323533) B7323533
theorem B4128691 : Blo 642303 4128691 := bstep (se 1 (by rfl) ⟨3096518, by rfl⟩ : syracuseStep 4128691 = 6193037) B6193037
theorem B2326843 : Blo 642303 2326843 := bstep (se 1 (by rfl) ⟨1745132, by rfl⟩ : syracuseStep 2326843 = 3490265) B3490265
theorem B2359687 : Blo 642303 2359687 := bstep (se 1 (by rfl) ⟨1769765, by rfl⟩ : syracuseStep 2359687 = 3539531) B3539531
theorem B4653571 : Blo 642303 4653571 := bstep (se 1 (by rfl) ⟨3490178, by rfl⟩ : syracuseStep 4653571 = 6980357) B6980357
theorem B1835531 : Blo 642303 1835531 := bstep (se 1 (by rfl) ⟨1376648, by rfl⟩ : syracuseStep 1835531 = 2753297) B2753297
theorem B918415 : Blo 642303 918415 := bstep (se 1 (by rfl) ⟨688811, by rfl⟩ : syracuseStep 918415 = 1377623) B1377623
theorem B918535 : Blo 642303 918535 := bstep (se 1 (by rfl) ⟨688901, by rfl⟩ : syracuseStep 918535 = 1377803) B1377803
theorem B12583997 : Blo 642303 12583997 := bstep (se 3 (by rfl) ⟨2359499, by rfl⟩ : syracuseStep 12583997 = 4718999) B4718999
theorem B4196069 : Blo 642303 4196069 := bstep (se 4 (by rfl) ⟨393381, by rfl⟩ : syracuseStep 4196069 = 786763) B786763
theorem B722695 : Blo 642303 722695 := bstep (se 1 (by rfl) ⟨542021, by rfl⟩ : syracuseStep 722695 = 1084043) B1084043
theorem B8259479 : Blo 642303 8259479 := bstep (se 1 (by rfl) ⟨6194609, by rfl⟩ : syracuseStep 8259479 = 12389219) B12389219
theorem B722875 : Blo 642303 722875 := bstep (se 1 (by rfl) ⟨542156, by rfl⟩ : syracuseStep 722875 = 1084313) B1084313
theorem B21235729 : Blo 642303 21235729 := bstep (se 2 (by rfl) ⟨7963398, by rfl⟩ : syracuseStep 21235729 = 15926797) B15926797
theorem B1837171 : Blo 642303 1837171 := bstep (se 1 (by rfl) ⟨1377878, by rfl⟩ : syracuseStep 1837171 = 2755757) B2755757
theorem B12585077 : Blo 642303 12585077 := bstep (se 5 (by rfl) ⟨589925, by rfl⟩ : syracuseStep 12585077 = 1179851) B1179851
theorem B1837399 : Blo 642303 1837399 := bstep (se 1 (by rfl) ⟨1378049, by rfl⟩ : syracuseStep 1837399 = 2756099) B2756099
theorem B723343 : Blo 642303 723343 := bstep (se 1 (by rfl) ⟨542507, by rfl⟩ : syracuseStep 723343 = 1085015) B1085015
theorem B919993 : Blo 642303 919993 := bstep (se 2 (by rfl) ⟨344997, by rfl⟩ : syracuseStep 919993 = 689995) B689995
theorem B4655645 : Blo 642303 4655645 := bstep (se 3 (by rfl) ⟨872933, by rfl⟩ : syracuseStep 4655645 = 1745867) B1745867
theorem B4950821 : Blo 642303 4950821 := bstep (se 4 (by rfl) ⟨464139, by rfl⟩ : syracuseStep 4950821 = 928279) B928279
theorem B1084279 : Blo 642303 1084279 := bstep (se 1 (by rfl) ⟨813209, by rfl⟩ : syracuseStep 1084279 = 1626419) B1626419
theorem B1739639 : Blo 642303 1739639 := bstep (se 1 (by rfl) ⟨1304729, by rfl⟩ : syracuseStep 1739639 = 2609459) B2609459
theorem B723847 : Blo 642303 723847 := bstep (se 1 (by rfl) ⟨542885, by rfl⟩ : syracuseStep 723847 = 1085771) B1085771
theorem B1084475 : Blo 642303 1084475 := bstep (se 1 (by rfl) ⟨813356, by rfl⟩ : syracuseStep 1084475 = 1626713) B1626713
theorem B724027 : Blo 642303 724027 := bstep (se 1 (by rfl) ⟨543020, by rfl⟩ : syracuseStep 724027 = 1086041) B1086041
theorem B1445255 : Blo 642303 1445255 := bstep (se 1 (by rfl) ⟨1083941, by rfl⟩ : syracuseStep 1445255 = 2167883) B2167883
theorem B1084873 : Blo 642303 1084873 := bstep (se 2 (by rfl) ⟨406827, by rfl⟩ : syracuseStep 1084873 = 813655) B813655
theorem B724495 : Blo 642303 724495 := bstep (se 1 (by rfl) ⟨543371, by rfl⟩ : syracuseStep 724495 = 1086743) B1086743
theorem B1740331 : Blo 642303 1740331 := bstep (se 1 (by rfl) ⟨1305248, by rfl⟩ : syracuseStep 1740331 = 2610497) B2610497
theorem B1445435 : Blo 642303 1445435 := bstep (se 1 (by rfl) ⟨1084076, by rfl⟩ : syracuseStep 1445435 = 2168153) B2168153
theorem B11013731 : Blo 642303 11013731 := bstep (se 1 (by rfl) ⟨8260298, by rfl⟩ : syracuseStep 11013731 = 16520597) B16520597
theorem B1445561 : Blo 642303 1445561 := bstep (se 2 (by rfl) ⟨542085, by rfl⟩ : syracuseStep 1445561 = 1084171) B1084171
theorem B1838983 : Blo 642303 1838983 := bstep (se 1 (by rfl) ⟨1379237, by rfl⟩ : syracuseStep 1838983 = 2758475) B2758475
theorem B724999 : Blo 642303 724999 := bstep (se 1 (by rfl) ⟨543749, by rfl⟩ : syracuseStep 724999 = 1087499) B1087499
theorem B1445903 : Blo 642303 1445903 := bstep (se 1 (by rfl) ⟨1084427, by rfl⟩ : syracuseStep 1445903 = 2168855) B2168855
theorem B1445921 : Blo 642303 1445921 := bstep (se 2 (by rfl) ⟨542220, by rfl⟩ : syracuseStep 1445921 = 1084441) B1084441
theorem B1085575 : Blo 642303 1085575 := bstep (se 1 (by rfl) ⟨814181, by rfl⟩ : syracuseStep 1085575 = 1628363) B1628363
theorem B1839257 : Blo 642303 1839257 := bstep (se 2 (by rfl) ⟨689721, by rfl⟩ : syracuseStep 1839257 = 1379443) B1379443
theorem B725179 : Blo 642303 725179 := bstep (se 1 (by rfl) ⟨543884, by rfl⟩ : syracuseStep 725179 = 1087769) B1087769
theorem B4886729 : Blo 642303 4886729 := bstep (se 2 (by rfl) ⟨1832523, by rfl⟩ : syracuseStep 4886729 = 3665047) B3665047
theorem B8392949 : Blo 642303 8392949 := bstep (se 5 (by rfl) ⟨393419, by rfl⟩ : syracuseStep 8392949 = 786839) B786839
theorem B1446263 : Blo 642303 1446263 := bstep (se 1 (by rfl) ⟨1084697, by rfl⟩ : syracuseStep 1446263 = 2169395) B2169395
theorem B1446443 : Blo 642303 1446443 := bstep (se 1 (by rfl) ⟨1084832, by rfl⟩ : syracuseStep 1446443 = 2169665) B2169665
theorem B725647 : Blo 642303 725647 := bstep (se 1 (by rfl) ⟨544235, by rfl⟩ : syracuseStep 725647 = 1088471) B1088471
theorem B1086223 : Blo 642303 1086223 := bstep (se 1 (by rfl) ⟨814667, by rfl⟩ : syracuseStep 1086223 = 1629335) B1629335
theorem B1839905 : Blo 642303 1839905 := bstep (se 2 (by rfl) ⟨689964, by rfl⟩ : syracuseStep 1839905 = 1379929) B1379929
theorem B1446803 : Blo 642303 1446803 := bstep (se 1 (by rfl) ⟨1085102, by rfl⟩ : syracuseStep 1446803 = 2170205) B2170205
theorem B1446857 : Blo 642303 1446857 := bstep (se 2 (by rfl) ⟨542571, by rfl⟩ : syracuseStep 1446857 = 1085143) B1085143
theorem B726151 : Blo 642303 726151 := bstep (se 1 (by rfl) ⟨544613, by rfl⟩ : syracuseStep 726151 = 1089227) B1089227
theorem B4658413 : Blo 642303 4658413 := bstep (se 3 (by rfl) ⟨873452, by rfl⟩ : syracuseStep 4658413 = 1746905) B1746905
theorem B1086763 : Blo 642303 1086763 := bstep (se 1 (by rfl) ⟨815072, by rfl⟩ : syracuseStep 1086763 = 1630145) B1630145
theorem B726331 : Blo 642303 726331 := bstep (se 1 (by rfl) ⟨544748, by rfl⟩ : syracuseStep 726331 = 1089497) B1089497
theorem B3675527 : Blo 642303 3675527 := bstep (se 1 (by rfl) ⟨2756645, by rfl⟩ : syracuseStep 3675527 = 5513291) B5513291
theorem B1086905 : Blo 642303 1086905 := bstep (se 2 (by rfl) ⟨407589, by rfl⟩ : syracuseStep 1086905 = 815179) B815179
theorem B2069945 : Blo 642303 2069945 := bstep (se 2 (by rfl) ⟨776229, by rfl⟩ : syracuseStep 2069945 = 1552459) B1552459
theorem B3479107 : Blo 642303 3479107 := bstep (se 1 (by rfl) ⟨2609330, by rfl⟩ : syracuseStep 3479107 = 5218661) B5218661
theorem B1447559 : Blo 642303 1447559 := bstep (se 1 (by rfl) ⟨1085669, by rfl⟩ : syracuseStep 1447559 = 2171339) B2171339
theorem B726799 : Blo 642303 726799 := bstep (se 1 (by rfl) ⟨545099, by rfl⟩ : syracuseStep 726799 = 1090199) B1090199
theorem B1447739 : Blo 642303 1447739 := bstep (se 1 (by rfl) ⟨1085804, by rfl⟩ : syracuseStep 1447739 = 2171609) B2171609
theorem B1447865 : Blo 642303 1447865 := bstep (se 2 (by rfl) ⟨542949, by rfl⟩ : syracuseStep 1447865 = 1085899) B1085899
theorem B20846605 : Blo 642303 20846605 := bstep (se 3 (by rfl) ⟨3908738, by rfl⟩ : syracuseStep 20846605 = 7817477) B7817477
theorem B39688309 : Blo 642303 39688309 := bstep (se 5 (by rfl) ⟨1860389, by rfl⟩ : syracuseStep 39688309 = 3720779) B3720779
theorem B1087607 : Blo 642303 1087607 := bstep (se 1 (by rfl) ⟨815705, by rfl⟩ : syracuseStep 1087607 = 1631411) B1631411
theorem B1448207 : Blo 642303 1448207 := bstep (se 1 (by rfl) ⟨1086155, by rfl⟩ : syracuseStep 1448207 = 2172311) B2172311
theorem B1448225 : Blo 642303 1448225 := bstep (se 2 (by rfl) ⟨543084, by rfl⟩ : syracuseStep 1448225 = 1086169) B1086169
theorem B1088059 : Blo 642303 1088059 := bstep (se 1 (by rfl) ⟨816044, by rfl⟩ : syracuseStep 1088059 = 1632089) B1632089
theorem B1448567 : Blo 642303 1448567 := bstep (se 1 (by rfl) ⟨1086425, by rfl⟩ : syracuseStep 1448567 = 2172851) B2172851
theorem B1088201 : Blo 642303 1088201 := bstep (se 2 (by rfl) ⟨408075, by rfl⟩ : syracuseStep 1088201 = 816151) B816151
theorem B1448747 : Blo 642303 1448747 := bstep (se 1 (by rfl) ⟨1086560, by rfl⟩ : syracuseStep 1448747 = 2173121) B2173121
theorem B2202553 : Blo 642303 2202553 := bstep (se 2 (by rfl) ⟨825957, by rfl⟩ : syracuseStep 2202553 = 1651915) B1651915
theorem B7445621 : Blo 642303 7445621 := bstep (se 5 (by rfl) ⟨349013, by rfl⟩ : syracuseStep 7445621 = 698027) B698027
theorem B1449107 : Blo 642303 1449107 := bstep (se 1 (by rfl) ⟨1086830, by rfl⟩ : syracuseStep 1449107 = 2173661) B2173661
theorem B1219769 : Blo 642303 1219769 := bstep (se 2 (by rfl) ⟨457413, by rfl⟩ : syracuseStep 1219769 = 914827) B914827
theorem B1449161 : Blo 642303 1449161 := bstep (se 2 (by rfl) ⟨543435, by rfl⟩ : syracuseStep 1449161 = 1086871) B1086871
theorem B1744247 : Blo 642303 1744247 := bstep (se 1 (by rfl) ⟨1308185, by rfl⟩ : syracuseStep 1744247 = 2616371) B2616371
theorem B1088903 : Blo 642303 1088903 := bstep (se 1 (by rfl) ⟨816677, by rfl⟩ : syracuseStep 1088903 = 1633355) B1633355
theorem B2170259 : Blo 642303 2170259 := bstep (se 1 (by rfl) ⟨1627694, by rfl⟩ : syracuseStep 2170259 = 3255389) B3255389
theorem B2793217 : Blo 642303 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B3907379 : Blo 642303 3907379 := bstep (se 1 (by rfl) ⟨2930534, by rfl⟩ : syracuseStep 3907379 = 5861069) B5861069
theorem B1449863 : Blo 642303 1449863 := bstep (se 1 (by rfl) ⟨1087397, by rfl⟩ : syracuseStep 1449863 = 2174795) B2174795
theorem B1089551 : Blo 642303 1089551 := bstep (se 1 (by rfl) ⟨817163, by rfl⟩ : syracuseStep 1089551 = 1634327) B1634327
theorem B1450043 : Blo 642303 1450043 := bstep (se 1 (by rfl) ⟨1087532, by rfl⟩ : syracuseStep 1450043 = 2175065) B2175065
theorem B3252311 : Blo 642303 3252311 := bstep (se 1 (by rfl) ⟨2439233, by rfl⟩ : syracuseStep 3252311 = 4878467) B4878467
theorem B1450169 : Blo 642303 1450169 := bstep (se 2 (by rfl) ⟨543813, by rfl⟩ : syracuseStep 1450169 = 1087627) B1087627
theorem B1220923 : Blo 642303 1220923 := bstep (se 1 (by rfl) ⟨915692, by rfl⟩ : syracuseStep 1220923 = 1831385) B1831385
theorem B7840259 : Blo 642303 7840259 := bstep (se 1 (by rfl) ⟨5880194, by rfl⟩ : syracuseStep 7840259 = 11760389) B11760389
theorem B1450511 : Blo 642303 1450511 := bstep (se 1 (by rfl) ⟨1087883, by rfl⟩ : syracuseStep 1450511 = 2175767) B2175767
theorem B3088925 : Blo 642303 3088925 := bstep (se 3 (by rfl) ⟨579173, by rfl⟩ : syracuseStep 3088925 = 1158347) B1158347
theorem B1450529 : Blo 642303 1450529 := bstep (se 2 (by rfl) ⟨543948, by rfl⟩ : syracuseStep 1450529 = 1087897) B1087897
theorem B1090091 : Blo 642303 1090091 := bstep (se 1 (by rfl) ⟨817568, by rfl⟩ : syracuseStep 1090091 = 1635137) B1635137
theorem B3252797 : Blo 642303 3252797 := bstep (se 3 (by rfl) ⟨609899, by rfl⟩ : syracuseStep 3252797 = 1219799) B1219799
theorem B1549057 : Blo 642303 1549057 := bstep (se 2 (by rfl) ⟨580896, by rfl⟩ : syracuseStep 1549057 = 1161793) B1161793
theorem B2171663 : Blo 642303 2171663 := bstep (se 1 (by rfl) ⟨1628747, by rfl⟩ : syracuseStep 2171663 = 3257495) B3257495
theorem B1221409 : Blo 642303 1221409 := bstep (se 2 (by rfl) ⟨458028, by rfl⟩ : syracuseStep 1221409 = 916057) B916057
theorem B1450871 : Blo 642303 1450871 := bstep (se 1 (by rfl) ⟨1088153, by rfl⟩ : syracuseStep 1450871 = 2176307) B2176307
theorem B1090489 : Blo 642303 1090489 := bstep (se 2 (by rfl) ⟨408933, by rfl⟩ : syracuseStep 1090489 = 817867) B817867
theorem B2171933 : Blo 642303 2171933 := bstep (se 3 (by rfl) ⟨407237, by rfl⟩ : syracuseStep 2171933 = 814475) B814475
theorem B1451051 : Blo 642303 1451051 := bstep (se 1 (by rfl) ⟨1088288, by rfl⟩ : syracuseStep 1451051 = 2176577) B2176577
theorem B1451411 : Blo 642303 1451411 := bstep (se 1 (by rfl) ⟨1088558, by rfl⟩ : syracuseStep 1451411 = 2177117) B2177117
theorem B1451465 : Blo 642303 1451465 := bstep (se 2 (by rfl) ⟨544299, by rfl⟩ : syracuseStep 1451465 = 1088599) B1088599
theorem B3909131 : Blo 642303 3909131 := bstep (se 1 (by rfl) ⟨2931848, by rfl⟩ : syracuseStep 3909131 = 5863697) B5863697
theorem B1549883 : Blo 642303 1549883 := bstep (se 1 (by rfl) ⟨1162412, by rfl⟩ : syracuseStep 1549883 = 2324825) B2324825
theorem B3680153 : Blo 642303 3680153 := bstep (se 2 (by rfl) ⟨1380057, by rfl⟩ : syracuseStep 3680153 = 2760115) B2760115
theorem B1746841 : Blo 642303 1746841 := bstep (se 2 (by rfl) ⟨655065, by rfl⟩ : syracuseStep 1746841 = 1310131) B1310131
theorem B1222715 : Blo 642303 1222715 := bstep (se 1 (by rfl) ⟨917036, by rfl⟩ : syracuseStep 1222715 = 1834073) B1834073
theorem B1452167 : Blo 642303 1452167 := bstep (se 1 (by rfl) ⟨1089125, by rfl⟩ : syracuseStep 1452167 = 2178251) B2178251
theorem B1321145 : Blo 642303 1321145 := bstep (se 2 (by rfl) ⟨495429, by rfl⟩ : syracuseStep 1321145 = 990859) B990859
theorem B993551 : Blo 642303 993551 := bstep (se 1 (by rfl) ⟨745163, by rfl⟩ : syracuseStep 993551 = 1490327) B1490327
theorem B3254579 : Blo 642303 3254579 := bstep (se 1 (by rfl) ⟨2440934, by rfl⟩ : syracuseStep 3254579 = 4881869) B4881869
theorem B4696379 : Blo 642303 4696379 := bstep (se 1 (by rfl) ⟨3522284, by rfl⟩ : syracuseStep 4696379 = 7044569) B7044569
theorem B1452347 : Blo 642303 1452347 := bstep (se 1 (by rfl) ⟨1089260, by rfl⟩ : syracuseStep 1452347 = 2178521) B2178521
theorem B2173337 : Blo 642303 2173337 := bstep (se 2 (by rfl) ⟨815001, by rfl⟩ : syracuseStep 2173337 = 1630003) B1630003
theorem B1452473 : Blo 642303 1452473 := bstep (se 2 (by rfl) ⟨544677, by rfl⟩ : syracuseStep 1452473 = 1089355) B1089355
theorem B6957521 : Blo 642303 6957521 := bstep (se 2 (by rfl) ⟨2609070, by rfl⟩ : syracuseStep 6957521 = 5218141) B5218141
theorem B1223201 : Blo 642303 1223201 := bstep (se 2 (by rfl) ⟨458700, by rfl⟩ : syracuseStep 1223201 = 917401) B917401
theorem B3254903 : Blo 642303 3254903 := bstep (se 1 (by rfl) ⟨2441177, by rfl⟩ : syracuseStep 3254903 = 4882355) B4882355
theorem B1223353 : Blo 642303 1223353 := bstep (se 2 (by rfl) ⟨458757, by rfl⟩ : syracuseStep 1223353 = 917515) B917515
theorem B1452815 : Blo 642303 1452815 := bstep (se 1 (by rfl) ⟨1089611, by rfl⟩ : syracuseStep 1452815 = 2179223) B2179223
theorem B1452833 : Blo 642303 1452833 := bstep (se 2 (by rfl) ⟨544812, by rfl⟩ : syracuseStep 1452833 = 1089625) B1089625
theorem B3091385 : Blo 642303 3091385 := bstep (se 2 (by rfl) ⟨1159269, by rfl⟩ : syracuseStep 3091385 = 2318539) B2318539
theorem B8825867 : Blo 642303 8825867 := bstep (se 1 (by rfl) ⟨6619400, by rfl⟩ : syracuseStep 8825867 = 13238801) B13238801
theorem B1158203 : Blo 642303 1158203 := bstep (se 1 (by rfl) ⟨868652, by rfl⟩ : syracuseStep 1158203 = 1737305) B1737305
theorem B2174039 : Blo 642303 2174039 := bstep (se 1 (by rfl) ⟨1630529, by rfl⟩ : syracuseStep 2174039 = 3261059) B3261059
theorem B1453175 : Blo 642303 1453175 := bstep (se 1 (by rfl) ⟨1089881, by rfl⟩ : syracuseStep 1453175 = 2179763) B2179763
theorem B1453355 : Blo 642303 1453355 := bstep (se 1 (by rfl) ⟨1090016, by rfl⟩ : syracuseStep 1453355 = 2180033) B2180033
theorem B2174525 : Blo 642303 2174525 := bstep (se 3 (by rfl) ⟨407723, by rfl⟩ : syracuseStep 2174525 = 815447) B815447
theorem B3255875 : Blo 642303 3255875 := bstep (se 1 (by rfl) ⟨2441906, by rfl⟩ : syracuseStep 3255875 = 4883813) B4883813
theorem B7319159 : Blo 642303 7319159 := bstep (se 1 (by rfl) ⟨5489369, by rfl⟩ : syracuseStep 7319159 = 10978739) B10978739
theorem B1453715 : Blo 642303 1453715 := bstep (se 1 (by rfl) ⟨1090286, by rfl⟩ : syracuseStep 1453715 = 2180573) B2180573
theorem B1453769 : Blo 642303 1453769 := bstep (se 2 (by rfl) ⟨545163, by rfl⟩ : syracuseStep 1453769 = 1090327) B1090327
theorem B3256199 : Blo 642303 3256199 := bstep (se 1 (by rfl) ⟨2442149, by rfl⟩ : syracuseStep 3256199 = 4884299) B4884299
theorem B733583 : Blo 642303 733583 := bstep (se 1 (by rfl) ⟨550187, by rfl⟩ : syracuseStep 733583 = 1100375) B1100375
theorem B1225145 : Blo 642303 1225145 := bstep (se 2 (by rfl) ⟨459429, by rfl⟩ : syracuseStep 1225145 = 918859) B918859
theorem B1651259 : Blo 642303 1651259 := bstep (se 1 (by rfl) ⟨1238444, by rfl⟩ : syracuseStep 1651259 = 2476889) B2476889
theorem B2175929 : Blo 642303 2175929 := bstep (se 2 (by rfl) ⟨815973, by rfl⟩ : syracuseStep 2175929 = 1631947) B1631947
theorem B963515 : Blo 642303 963515 := bstep (se 1 (by rfl) ⟨722636, by rfl⟩ : syracuseStep 963515 = 1445273) B1445273
theorem B963575 : Blo 642303 963575 := bstep (se 1 (by rfl) ⟨722681, by rfl⟩ : syracuseStep 963575 = 1445363) B1445363
theorem B1061903 : Blo 642303 1061903 := bstep (se 1 (by rfl) ⟨796427, by rfl⟩ : syracuseStep 1061903 = 1592855) B1592855
theorem B963599 : Blo 642303 963599 := bstep (se 1 (by rfl) ⟨722699, by rfl⟩ : syracuseStep 963599 = 1445399) B1445399
theorem B5649431 : Blo 642303 5649431 := bstep (se 1 (by rfl) ⟨4237073, by rfl⟩ : syracuseStep 5649431 = 8474147) B8474147
theorem B963641 : Blo 642303 963641 := bstep (se 2 (by rfl) ⟨361365, by rfl⟩ : syracuseStep 963641 = 722731) B722731
theorem B963719 : Blo 642303 963719 := bstep (se 1 (by rfl) ⟨722789, by rfl⟩ : syracuseStep 963719 = 1445579) B1445579
theorem B963755 : Blo 642303 963755 := bstep (se 1 (by rfl) ⟨722816, by rfl⟩ : syracuseStep 963755 = 1445633) B1445633
theorem B963785 : Blo 642303 963785 := bstep (se 2 (by rfl) ⟨361419, by rfl⟩ : syracuseStep 963785 = 722839) B722839
theorem B963899 : Blo 642303 963899 := bstep (se 1 (by rfl) ⟨722924, by rfl⟩ : syracuseStep 963899 = 1445849) B1445849
theorem B963959 : Blo 642303 963959 := bstep (se 1 (by rfl) ⟨722969, by rfl⟩ : syracuseStep 963959 = 1445939) B1445939
theorem B6174083 : Blo 642303 6174083 := bstep (se 1 (by rfl) ⟨4630562, by rfl⟩ : syracuseStep 6174083 = 9261125) B9261125
theorem B963983 : Blo 642303 963983 := bstep (se 1 (by rfl) ⟨722987, by rfl⟩ : syracuseStep 963983 = 1445975) B1445975
theorem B964025 : Blo 642303 964025 := bstep (se 2 (by rfl) ⟨361509, by rfl⟩ : syracuseStep 964025 = 723019) B723019
theorem B52868537 : Blo 642303 52868537 := bstep (se 2 (by rfl) ⟨19825701, by rfl⟩ : syracuseStep 52868537 = 39651403) B39651403
theorem B964103 : Blo 642303 964103 := bstep (se 1 (by rfl) ⟨723077, by rfl⟩ : syracuseStep 964103 = 1446155) B1446155
theorem B2176523 : Blo 642303 2176523 := bstep (se 1 (by rfl) ⟨1632392, by rfl⟩ : syracuseStep 2176523 = 3264785) B3264785
theorem B26490397 : Blo 642303 26490397 := bstep (se 3 (by rfl) ⟨4966949, by rfl⟩ : syracuseStep 26490397 = 9933899) B9933899
theorem B964139 : Blo 642303 964139 := bstep (se 1 (by rfl) ⟨723104, by rfl⟩ : syracuseStep 964139 = 1446209) B1446209
theorem B4404779 : Blo 642303 4404779 := bstep (se 1 (by rfl) ⟨3303584, by rfl⟩ : syracuseStep 4404779 = 6607169) B6607169
theorem B964169 : Blo 642303 964169 := bstep (se 2 (by rfl) ⟨361563, by rfl⟩ : syracuseStep 964169 = 723127) B723127
theorem B2176631 : Blo 642303 2176631 := bstep (se 1 (by rfl) ⟨1632473, by rfl⟩ : syracuseStep 2176631 = 3264947) B3264947
theorem B964283 : Blo 642303 964283 := bstep (se 1 (by rfl) ⟨723212, by rfl⟩ : syracuseStep 964283 = 1446425) B1446425
theorem B4896449 : Blo 642303 4896449 := bstep (se 2 (by rfl) ⟨1836168, by rfl⟩ : syracuseStep 4896449 = 3672337) B3672337
theorem B964343 : Blo 642303 964343 := bstep (se 1 (by rfl) ⟨723257, by rfl⟩ : syracuseStep 964343 = 1446515) B1446515
theorem B964367 : Blo 642303 964367 := bstep (se 1 (by rfl) ⟨723275, by rfl⟩ : syracuseStep 964367 = 1446551) B1446551
theorem B964409 : Blo 642303 964409 := bstep (se 2 (by rfl) ⟨361653, by rfl⟩ : syracuseStep 964409 = 723307) B723307
theorem B964487 : Blo 642303 964487 := bstep (se 1 (by rfl) ⟨723365, by rfl⟩ : syracuseStep 964487 = 1446731) B1446731
theorem B964523 : Blo 642303 964523 := bstep (se 1 (by rfl) ⟨723392, by rfl⟩ : syracuseStep 964523 = 1446785) B1446785
theorem B964553 : Blo 642303 964553 := bstep (se 2 (by rfl) ⟨361707, by rfl⟩ : syracuseStep 964553 = 723415) B723415
theorem B964667 : Blo 642303 964667 := bstep (se 1 (by rfl) ⟨723500, by rfl⟩ : syracuseStep 964667 = 1447001) B1447001
theorem B964727 : Blo 642303 964727 := bstep (se 1 (by rfl) ⟨723545, by rfl⟩ : syracuseStep 964727 = 1447091) B1447091
theorem B964751 : Blo 642303 964751 := bstep (se 1 (by rfl) ⟨723563, by rfl⟩ : syracuseStep 964751 = 1447127) B1447127
theorem B964793 : Blo 642303 964793 := bstep (se 2 (by rfl) ⟨361797, by rfl⟩ : syracuseStep 964793 = 723595) B723595
theorem B2177225 : Blo 642303 2177225 := bstep (se 2 (by rfl) ⟨816459, by rfl⟩ : syracuseStep 2177225 = 1632919) B1632919
theorem B10991861 : Blo 642303 10991861 := bstep (se 5 (by rfl) ⟨515243, by rfl⟩ : syracuseStep 10991861 = 1030487) B1030487
theorem B964871 : Blo 642303 964871 := bstep (se 1 (by rfl) ⟨723653, by rfl⟩ : syracuseStep 964871 = 1447307) B1447307
theorem B964907 : Blo 642303 964907 := bstep (se 1 (by rfl) ⟨723680, by rfl⟩ : syracuseStep 964907 = 1447361) B1447361
theorem B964937 : Blo 642303 964937 := bstep (se 2 (by rfl) ⟨361851, by rfl⟩ : syracuseStep 964937 = 723703) B723703
theorem B3488147 : Blo 642303 3488147 := bstep (se 1 (by rfl) ⟨2616110, by rfl⟩ : syracuseStep 3488147 = 5232221) B5232221
theorem B1391033 : Blo 642303 1391033 := bstep (se 2 (by rfl) ⟨521637, by rfl⟩ : syracuseStep 1391033 = 1043275) B1043275
theorem B965051 : Blo 642303 965051 := bstep (se 1 (by rfl) ⟨723788, by rfl⟩ : syracuseStep 965051 = 1447577) B1447577
theorem B965111 : Blo 642303 965111 := bstep (se 1 (by rfl) ⟨723833, by rfl⟩ : syracuseStep 965111 = 1447667) B1447667
theorem B965135 : Blo 642303 965135 := bstep (se 1 (by rfl) ⟨723851, by rfl⟩ : syracuseStep 965135 = 1447703) B1447703
theorem B1391137 : Blo 642303 1391137 := bstep (se 2 (by rfl) ⟨521676, by rfl⟩ : syracuseStep 1391137 = 1043353) B1043353
theorem B965177 : Blo 642303 965177 := bstep (se 2 (by rfl) ⟨361941, by rfl⟩ : syracuseStep 965177 = 723883) B723883
theorem B965255 : Blo 642303 965255 := bstep (se 1 (by rfl) ⟨723941, by rfl⟩ : syracuseStep 965255 = 1447883) B1447883
theorem B965291 : Blo 642303 965291 := bstep (se 1 (by rfl) ⟨723968, by rfl⟩ : syracuseStep 965291 = 1447937) B1447937
theorem B965321 : Blo 642303 965321 := bstep (se 2 (by rfl) ⟨361995, by rfl⟩ : syracuseStep 965321 = 723991) B723991
theorem B8272601 : Blo 642303 8272601 := bstep (se 2 (by rfl) ⟨3102225, by rfl⟩ : syracuseStep 8272601 = 6204451) B6204451
theorem B965435 : Blo 642303 965435 := bstep (se 1 (by rfl) ⟨724076, by rfl⟩ : syracuseStep 965435 = 1448153) B1448153
theorem B965495 : Blo 642303 965495 := bstep (se 1 (by rfl) ⟨724121, by rfl⟩ : syracuseStep 965495 = 1448243) B1448243
theorem B2177927 : Blo 642303 2177927 := bstep (se 1 (by rfl) ⟨1633445, by rfl⟩ : syracuseStep 2177927 = 3266891) B3266891
theorem B965519 : Blo 642303 965519 := bstep (se 1 (by rfl) ⟨724139, by rfl⟩ : syracuseStep 965519 = 1448279) B1448279
theorem B965561 : Blo 642303 965561 := bstep (se 2 (by rfl) ⟨362085, by rfl⟩ : syracuseStep 965561 = 724171) B724171
theorem B2440145 : Blo 642303 2440145 := bstep (se 2 (by rfl) ⟨915054, by rfl⟩ : syracuseStep 2440145 = 1830109) B1830109
theorem B965639 : Blo 642303 965639 := bstep (se 1 (by rfl) ⟨724229, by rfl⟩ : syracuseStep 965639 = 1448459) B1448459
theorem B965675 : Blo 642303 965675 := bstep (se 1 (by rfl) ⟨724256, by rfl⟩ : syracuseStep 965675 = 1448513) B1448513
theorem B965705 : Blo 642303 965705 := bstep (se 2 (by rfl) ⟨362139, by rfl⟩ : syracuseStep 965705 = 724279) B724279
theorem B965819 : Blo 642303 965819 := bstep (se 1 (by rfl) ⟨724364, by rfl⟩ : syracuseStep 965819 = 1448729) B1448729
theorem B92978381 : Blo 642303 92978381 := bstep (se 3 (by rfl) ⟨17433446, by rfl⟩ : syracuseStep 92978381 = 34866893) B34866893
theorem B2604269 : Blo 642303 2604269 := bstep (se 3 (by rfl) ⟨488300, by rfl⟩ : syracuseStep 2604269 = 976601) B976601
theorem B965879 : Blo 642303 965879 := bstep (se 1 (by rfl) ⟨724409, by rfl⟩ : syracuseStep 965879 = 1448819) B1448819
theorem B2178305 : Blo 642303 2178305 := bstep (se 2 (by rfl) ⟨816864, by rfl⟩ : syracuseStep 2178305 = 1633729) B1633729
theorem B965903 : Blo 642303 965903 := bstep (se 1 (by rfl) ⟨724427, by rfl⟩ : syracuseStep 965903 = 1448855) B1448855
theorem B965945 : Blo 642303 965945 := bstep (se 2 (by rfl) ⟨362229, by rfl⟩ : syracuseStep 965945 = 724459) B724459
theorem B3259763 : Blo 642303 3259763 := bstep (se 1 (by rfl) ⟨2444822, by rfl⟩ : syracuseStep 3259763 = 4889645) B4889645
theorem B1162615 : Blo 642303 1162615 := bstep (se 1 (by rfl) ⟨871961, by rfl⟩ : syracuseStep 1162615 = 1743923) B1743923
theorem B966023 : Blo 642303 966023 := bstep (se 1 (by rfl) ⟨724517, by rfl⟩ : syracuseStep 966023 = 1449035) B1449035
theorem B2440601 : Blo 642303 2440601 := bstep (se 2 (by rfl) ⟨915225, by rfl⟩ : syracuseStep 2440601 = 1830451) B1830451
theorem B966059 : Blo 642303 966059 := bstep (se 1 (by rfl) ⟨724544, by rfl⟩ : syracuseStep 966059 = 1449089) B1449089
theorem B966089 : Blo 642303 966089 := bstep (se 2 (by rfl) ⟨362283, by rfl⟩ : syracuseStep 966089 = 724567) B724567
theorem B966203 : Blo 642303 966203 := bstep (se 1 (by rfl) ⟨724652, by rfl⟩ : syracuseStep 966203 = 1449305) B1449305
theorem B966263 : Blo 642303 966263 := bstep (se 1 (by rfl) ⟨724697, by rfl⟩ : syracuseStep 966263 = 1449395) B1449395
theorem B966287 : Blo 642303 966287 := bstep (se 1 (by rfl) ⟨724715, by rfl⟩ : syracuseStep 966287 = 1449431) B1449431
theorem B966329 : Blo 642303 966329 := bstep (se 2 (by rfl) ⟨362373, by rfl⟩ : syracuseStep 966329 = 724747) B724747
theorem B966407 : Blo 642303 966407 := bstep (se 1 (by rfl) ⟨724805, by rfl⟩ : syracuseStep 966407 = 1449611) B1449611
theorem B966443 : Blo 642303 966443 := bstep (se 1 (by rfl) ⟨724832, by rfl⟩ : syracuseStep 966443 = 1449665) B1449665
theorem B966473 : Blo 642303 966473 := bstep (se 2 (by rfl) ⟨362427, by rfl⟩ : syracuseStep 966473 = 724855) B724855
theorem B3260249 : Blo 642303 3260249 := bstep (se 2 (by rfl) ⟨1222593, by rfl⟩ : syracuseStep 3260249 = 2445187) B2445187
theorem B966587 : Blo 642303 966587 := bstep (se 1 (by rfl) ⟨724940, by rfl⟩ : syracuseStep 966587 = 1449881) B1449881
theorem B5521355 : Blo 642303 5521355 := bstep (se 1 (by rfl) ⟨4141016, by rfl⟩ : syracuseStep 5521355 = 8282033) B8282033
theorem B966647 : Blo 642303 966647 := bstep (se 1 (by rfl) ⟨724985, by rfl⟩ : syracuseStep 966647 = 1449971) B1449971
theorem B966671 : Blo 642303 966671 := bstep (se 1 (by rfl) ⟨725003, by rfl⟩ : syracuseStep 966671 = 1450007) B1450007
theorem B2179115 : Blo 642303 2179115 := bstep (se 1 (by rfl) ⟨1634336, by rfl⟩ : syracuseStep 2179115 = 3268673) B3268673
theorem B966713 : Blo 642303 966713 := bstep (se 2 (by rfl) ⟨362517, by rfl⟩ : syracuseStep 966713 = 725035) B725035
theorem B966791 : Blo 642303 966791 := bstep (se 1 (by rfl) ⟨725093, by rfl⟩ : syracuseStep 966791 = 1450187) B1450187
theorem B966827 : Blo 642303 966827 := bstep (se 1 (by rfl) ⟨725120, by rfl⟩ : syracuseStep 966827 = 1450241) B1450241
theorem B6963401 : Blo 642303 6963401 := bstep (se 2 (by rfl) ⟨2611275, by rfl⟩ : syracuseStep 6963401 = 5222551) B5222551
theorem B966857 : Blo 642303 966857 := bstep (se 2 (by rfl) ⟨362571, by rfl⟩ : syracuseStep 966857 = 725143) B725143
theorem B3096883 : Blo 642303 3096883 := bstep (se 1 (by rfl) ⟨2322662, by rfl⟩ : syracuseStep 3096883 = 4645325) B4645325
theorem B966971 : Blo 642303 966971 := bstep (se 1 (by rfl) ⟨725228, by rfl⟩ : syracuseStep 966971 = 1450457) B1450457
theorem B967031 : Blo 642303 967031 := bstep (se 1 (by rfl) ⟨725273, by rfl⟩ : syracuseStep 967031 = 1450547) B1450547
theorem B1163639 : Blo 642303 1163639 := bstep (se 1 (by rfl) ⟨872729, by rfl⟩ : syracuseStep 1163639 = 1745459) B1745459
theorem B1032583 : Blo 642303 1032583 := bstep (se 1 (by rfl) ⟨774437, by rfl⟩ : syracuseStep 1032583 = 1548875) B1548875
theorem B967055 : Blo 642303 967055 := bstep (se 1 (by rfl) ⟨725291, by rfl⟩ : syracuseStep 967055 = 1450583) B1450583
theorem B2474393 : Blo 642303 2474393 := bstep (se 2 (by rfl) ⟨927897, by rfl⟩ : syracuseStep 2474393 = 1855795) B1855795
theorem B967097 : Blo 642303 967097 := bstep (se 2 (by rfl) ⟨362661, by rfl⟩ : syracuseStep 967097 = 725323) B725323
theorem B967175 : Blo 642303 967175 := bstep (se 1 (by rfl) ⟨725381, by rfl⟩ : syracuseStep 967175 = 1450763) B1450763
theorem B2441771 : Blo 642303 2441771 := bstep (se 1 (by rfl) ⟨1831328, by rfl⟩ : syracuseStep 2441771 = 3662657) B3662657
theorem B967211 : Blo 642303 967211 := bstep (se 1 (by rfl) ⟨725408, by rfl⟩ : syracuseStep 967211 = 1450817) B1450817
theorem B967241 : Blo 642303 967241 := bstep (se 2 (by rfl) ⟨362715, by rfl⟩ : syracuseStep 967241 = 725431) B725431
theorem B967355 : Blo 642303 967355 := bstep (se 1 (by rfl) ⟨725516, by rfl⟩ : syracuseStep 967355 = 1451033) B1451033
theorem B3916525 : Blo 642303 3916525 := bstep (se 3 (by rfl) ⟨734348, by rfl⟩ : syracuseStep 3916525 = 1468697) B1468697
theorem B967415 : Blo 642303 967415 := bstep (se 1 (by rfl) ⟨725561, by rfl⟩ : syracuseStep 967415 = 1451123) B1451123
theorem B967439 : Blo 642303 967439 := bstep (se 1 (by rfl) ⟨725579, by rfl⟩ : syracuseStep 967439 = 1451159) B1451159
theorem B967481 : Blo 642303 967481 := bstep (se 2 (by rfl) ⟨362805, by rfl⟩ : syracuseStep 967481 = 725611) B725611
theorem B967559 : Blo 642303 967559 := bstep (se 1 (by rfl) ⟨725669, by rfl⟩ : syracuseStep 967559 = 1451339) B1451339
theorem B967595 : Blo 642303 967595 := bstep (se 1 (by rfl) ⟨725696, by rfl⟩ : syracuseStep 967595 = 1451393) B1451393
theorem B967625 : Blo 642303 967625 := bstep (se 2 (by rfl) ⟨362859, by rfl⟩ : syracuseStep 967625 = 725719) B725719
theorem B4899851 : Blo 642303 4899851 := bstep (se 1 (by rfl) ⟨3674888, by rfl⟩ : syracuseStep 4899851 = 7349777) B7349777
theorem B967739 : Blo 642303 967739 := bstep (se 1 (by rfl) ⟨725804, by rfl⟩ : syracuseStep 967739 = 1451609) B1451609
theorem B967799 : Blo 642303 967799 := bstep (se 1 (by rfl) ⟨725849, by rfl⟩ : syracuseStep 967799 = 1451699) B1451699
theorem B967823 : Blo 642303 967823 := bstep (se 1 (by rfl) ⟨725867, by rfl⟩ : syracuseStep 967823 = 1451735) B1451735
theorem B967865 : Blo 642303 967865 := bstep (se 2 (by rfl) ⟨362949, by rfl⟩ : syracuseStep 967865 = 725899) B725899
theorem B967943 : Blo 642303 967943 := bstep (se 1 (by rfl) ⟨725957, by rfl⟩ : syracuseStep 967943 = 1451915) B1451915
theorem B967979 : Blo 642303 967979 := bstep (se 1 (by rfl) ⟨725984, by rfl⟩ : syracuseStep 967979 = 1451969) B1451969
theorem B2180411 : Blo 642303 2180411 := bstep (se 1 (by rfl) ⟨1635308, by rfl⟩ : syracuseStep 2180411 = 3270617) B3270617
theorem B968009 : Blo 642303 968009 := bstep (se 2 (by rfl) ⟨363003, by rfl⟩ : syracuseStep 968009 = 726007) B726007
theorem B968123 : Blo 642303 968123 := bstep (se 1 (by rfl) ⟨726092, by rfl⟩ : syracuseStep 968123 = 1452185) B1452185
theorem B968183 : Blo 642303 968183 := bstep (se 1 (by rfl) ⟨726137, by rfl⟩ : syracuseStep 968183 = 1452275) B1452275
theorem B968207 : Blo 642303 968207 := bstep (se 1 (by rfl) ⟨726155, by rfl⟩ : syracuseStep 968207 = 1452311) B1452311
theorem B869945 : Blo 642303 869945 := bstep (se 2 (by rfl) ⟨326229, by rfl⟩ : syracuseStep 869945 = 652459) B652459
theorem B968249 : Blo 642303 968249 := bstep (se 2 (by rfl) ⟨363093, by rfl⟩ : syracuseStep 968249 = 726187) B726187
theorem B968327 : Blo 642303 968327 := bstep (se 1 (by rfl) ⟨726245, by rfl⟩ : syracuseStep 968327 = 1452491) B1452491
theorem B968363 : Blo 642303 968363 := bstep (se 1 (by rfl) ⟨726272, by rfl⟩ : syracuseStep 968363 = 1452545) B1452545
theorem B968393 : Blo 642303 968393 := bstep (se 2 (by rfl) ⟨363147, by rfl⟩ : syracuseStep 968393 = 726295) B726295
theorem B2180897 : Blo 642303 2180897 := bstep (se 2 (by rfl) ⟨817836, by rfl⟩ : syracuseStep 2180897 = 1635673) B1635673
theorem B968507 : Blo 642303 968507 := bstep (se 1 (by rfl) ⟨726380, by rfl⟩ : syracuseStep 968507 = 1452761) B1452761
theorem B968567 : Blo 642303 968567 := bstep (se 1 (by rfl) ⟨726425, by rfl⟩ : syracuseStep 968567 = 1452851) B1452851
theorem B968591 : Blo 642303 968591 := bstep (se 1 (by rfl) ⟨726443, by rfl⟩ : syracuseStep 968591 = 1452887) B1452887
theorem B2606995 : Blo 642303 2606995 := bstep (se 1 (by rfl) ⟨1955246, by rfl⟩ : syracuseStep 2606995 = 3910493) B3910493
theorem B3262355 : Blo 642303 3262355 := bstep (se 1 (by rfl) ⟨2446766, by rfl⟩ : syracuseStep 3262355 = 4893533) B4893533
theorem B968633 : Blo 642303 968633 := bstep (se 2 (by rfl) ⟨363237, by rfl⟩ : syracuseStep 968633 = 726475) B726475
theorem B968711 : Blo 642303 968711 := bstep (se 1 (by rfl) ⟨726533, by rfl⟩ : syracuseStep 968711 = 1453067) B1453067
theorem B1034255 : Blo 642303 1034255 := bstep (se 1 (by rfl) ⟨775691, by rfl⟩ : syracuseStep 1034255 = 1551383) B1551383
theorem B968747 : Blo 642303 968747 := bstep (se 1 (by rfl) ⟨726560, by rfl⟩ : syracuseStep 968747 = 1453121) B1453121
theorem B7358525 : Blo 642303 7358525 := bstep (se 3 (by rfl) ⟨1379723, by rfl⟩ : syracuseStep 7358525 = 2759447) B2759447
theorem B968777 : Blo 642303 968777 := bstep (se 2 (by rfl) ⟨363291, by rfl⟩ : syracuseStep 968777 = 726583) B726583
theorem B968891 : Blo 642303 968891 := bstep (se 1 (by rfl) ⟨726668, by rfl⟩ : syracuseStep 968891 = 1453337) B1453337
theorem B968951 : Blo 642303 968951 := bstep (se 1 (by rfl) ⟨726713, by rfl⟩ : syracuseStep 968951 = 1453427) B1453427
theorem B968975 : Blo 642303 968975 := bstep (se 1 (by rfl) ⟨726731, by rfl⟩ : syracuseStep 968975 = 1453463) B1453463
theorem B969017 : Blo 642303 969017 := bstep (se 2 (by rfl) ⟨363381, by rfl⟩ : syracuseStep 969017 = 726763) B726763
theorem B969095 : Blo 642303 969095 := bstep (se 1 (by rfl) ⟨726821, by rfl⟩ : syracuseStep 969095 = 1453643) B1453643
theorem B969131 : Blo 642303 969131 := bstep (se 1 (by rfl) ⟨726848, by rfl⟩ : syracuseStep 969131 = 1453697) B1453697
theorem B969161 : Blo 642303 969161 := bstep (se 2 (by rfl) ⟨363435, by rfl⟩ : syracuseStep 969161 = 726871) B726871
theorem B2443729 : Blo 642303 2443729 := bstep (se 2 (by rfl) ⟨916398, by rfl⟩ : syracuseStep 2443729 = 1832797) B1832797
theorem B969275 : Blo 642303 969275 := bstep (se 1 (by rfl) ⟨726956, by rfl⟩ : syracuseStep 969275 = 1453913) B1453913
theorem B871031 : Blo 642303 871031 := bstep (se 1 (by rfl) ⟨653273, by rfl⟩ : syracuseStep 871031 = 1306547) B1306547
theorem B969335 : Blo 642303 969335 := bstep (se 1 (by rfl) ⟨727001, by rfl⟩ : syracuseStep 969335 = 1454003) B1454003
theorem B969359 : Blo 642303 969359 := bstep (se 1 (by rfl) ⟨727019, by rfl⟩ : syracuseStep 969359 = 1454039) B1454039
theorem B969401 : Blo 642303 969401 := bstep (se 2 (by rfl) ⟨363525, by rfl⟩ : syracuseStep 969401 = 727051) B727051
theorem B2444033 : Blo 642303 2444033 := bstep (se 2 (by rfl) ⟨916512, by rfl⟩ : syracuseStep 2444033 = 1833025) B1833025
theorem B4901795 : Blo 642303 4901795 := bstep (se 1 (by rfl) ⟨3676346, by rfl⟩ : syracuseStep 4901795 = 7352693) B7352693
theorem B3984349 : Blo 642303 3984349 := bstep (se 3 (by rfl) ⟨747065, by rfl⟩ : syracuseStep 3984349 = 1494131) B1494131
theorem B5491799 : Blo 642303 5491799 := bstep (se 1 (by rfl) ⟨4118849, by rfl⟩ : syracuseStep 5491799 = 8237699) B8237699
theorem B2444489 : Blo 642303 2444489 := bstep (se 2 (by rfl) ⟨916683, by rfl⟩ : syracuseStep 2444489 = 1833367) B1833367
theorem B642311 : Blo 642303 642311 := bstep (se 1 (by rfl) ⟨481733, by rfl⟩ : syracuseStep 642311 = 963467) B963467
theorem B642319 : Blo 642303 642319 := bstep (se 1 (by rfl) ⟨481739, by rfl⟩ : syracuseStep 642319 = 963479) B963479
theorem B871723 : Blo 642303 871723 := bstep (se 1 (by rfl) ⟨653792, by rfl⟩ : syracuseStep 871723 = 1307585) B1307585
theorem B642363 : Blo 642303 642363 := bstep (se 1 (by rfl) ⟨481772, by rfl⟩ : syracuseStep 642363 = 963545) B963545
theorem B642439 : Blo 642303 642439 := bstep (se 1 (by rfl) ⟨481829, by rfl⟩ : syracuseStep 642439 = 963659) B963659
theorem B642447 : Blo 642303 642447 := bstep (se 1 (by rfl) ⟨481835, by rfl⟩ : syracuseStep 642447 = 963671) B963671
theorem B2608537 : Blo 642303 2608537 := bstep (se 2 (by rfl) ⟨978201, by rfl⟩ : syracuseStep 2608537 = 1956403) B1956403
theorem B642491 : Blo 642303 642491 := bstep (se 1 (by rfl) ⟨481868, by rfl⟩ : syracuseStep 642491 = 963737) B963737
theorem B642567 : Blo 642303 642567 := bstep (se 1 (by rfl) ⟨481925, by rfl⟩ : syracuseStep 642567 = 963851) B963851
theorem B642575 : Blo 642303 642575 := bstep (se 1 (by rfl) ⟨481931, by rfl⟩ : syracuseStep 642575 = 963863) B963863
theorem B642619 : Blo 642303 642619 := bstep (se 1 (by rfl) ⟨481964, by rfl⟩ : syracuseStep 642619 = 963929) B963929
theorem B642695 : Blo 642303 642695 := bstep (se 1 (by rfl) ⟨482021, by rfl⟩ : syracuseStep 642695 = 964043) B964043
theorem B642703 : Blo 642303 642703 := bstep (se 1 (by rfl) ⟨482027, by rfl⟩ : syracuseStep 642703 = 964055) B964055
theorem B642747 : Blo 642303 642747 := bstep (se 1 (by rfl) ⟨482060, by rfl⟩ : syracuseStep 642747 = 964121) B964121
theorem B642823 : Blo 642303 642823 := bstep (se 1 (by rfl) ⟨482117, by rfl⟩ : syracuseStep 642823 = 964235) B964235
theorem B642831 : Blo 642303 642831 := bstep (se 1 (by rfl) ⟨482123, by rfl⟩ : syracuseStep 642831 = 964247) B964247
theorem B642875 : Blo 642303 642875 := bstep (se 1 (by rfl) ⟨482156, by rfl⟩ : syracuseStep 642875 = 964313) B964313
theorem B642951 : Blo 642303 642951 := bstep (se 1 (by rfl) ⟨482213, by rfl⟩ : syracuseStep 642951 = 964427) B964427
theorem B642959 : Blo 642303 642959 := bstep (se 1 (by rfl) ⟨482219, by rfl⟩ : syracuseStep 642959 = 964439) B964439
theorem B643003 : Blo 642303 643003 := bstep (se 1 (by rfl) ⟨482252, by rfl⟩ : syracuseStep 643003 = 964505) B964505
theorem B643079 : Blo 642303 643079 := bstep (se 1 (by rfl) ⟨482309, by rfl⟩ : syracuseStep 643079 = 964619) B964619
theorem B643087 : Blo 642303 643087 := bstep (se 1 (by rfl) ⟨482315, by rfl⟩ : syracuseStep 643087 = 964631) B964631
theorem B643131 : Blo 642303 643131 := bstep (se 1 (by rfl) ⟨482348, by rfl⟩ : syracuseStep 643131 = 964697) B964697
theorem B1626227 : Blo 642303 1626227 := bstep (se 1 (by rfl) ⟨1219670, by rfl⟩ : syracuseStep 1626227 = 2439341) B2439341
theorem B643207 : Blo 642303 643207 := bstep (se 1 (by rfl) ⟨482405, by rfl⟩ : syracuseStep 643207 = 964811) B964811
theorem B643215 : Blo 642303 643215 := bstep (se 1 (by rfl) ⟨482411, by rfl⟩ : syracuseStep 643215 = 964823) B964823
theorem B643259 : Blo 642303 643259 := bstep (se 1 (by rfl) ⟨482444, by rfl⟩ : syracuseStep 643259 = 964889) B964889
theorem B643335 : Blo 642303 643335 := bstep (se 1 (by rfl) ⟨482501, by rfl⟩ : syracuseStep 643335 = 965003) B965003
theorem B643343 : Blo 642303 643343 := bstep (se 1 (by rfl) ⟨482507, by rfl⟩ : syracuseStep 643343 = 965015) B965015
theorem B872761 : Blo 642303 872761 := bstep (se 2 (by rfl) ⟨327285, by rfl⟩ : syracuseStep 872761 = 654571) B654571
theorem B643387 : Blo 642303 643387 := bstep (se 1 (by rfl) ⟨482540, by rfl⟩ : syracuseStep 643387 = 965081) B965081
theorem B643463 : Blo 642303 643463 := bstep (se 1 (by rfl) ⟨482597, by rfl⟩ : syracuseStep 643463 = 965195) B965195
theorem B643471 : Blo 642303 643471 := bstep (se 1 (by rfl) ⟨482603, by rfl⟩ : syracuseStep 643471 = 965207) B965207
theorem B3101075 : Blo 642303 3101075 := bstep (se 1 (by rfl) ⟨2325806, by rfl⟩ : syracuseStep 3101075 = 4651613) B4651613
theorem B643515 : Blo 642303 643515 := bstep (se 1 (by rfl) ⟨482636, by rfl⟩ : syracuseStep 643515 = 965273) B965273
theorem B643591 : Blo 642303 643591 := bstep (se 1 (by rfl) ⟨482693, by rfl⟩ : syracuseStep 643591 = 965387) B965387
theorem B643599 : Blo 642303 643599 := bstep (se 1 (by rfl) ⟨482699, by rfl⟩ : syracuseStep 643599 = 965399) B965399
theorem B3658283 : Blo 642303 3658283 := bstep (se 1 (by rfl) ⟨2743712, by rfl⟩ : syracuseStep 3658283 = 5487425) B5487425
theorem B643643 : Blo 642303 643643 := bstep (se 1 (by rfl) ⟨482732, by rfl⟩ : syracuseStep 643643 = 965465) B965465
theorem B1626743 : Blo 642303 1626743 := bstep (se 1 (by rfl) ⟨1220057, by rfl⟩ : syracuseStep 1626743 = 2440115) B2440115
theorem B3101303 : Blo 642303 3101303 := bstep (se 1 (by rfl) ⟨2325977, by rfl⟩ : syracuseStep 3101303 = 4651955) B4651955
theorem B54317699 : Blo 642303 54317699 := bstep (se 1 (by rfl) ⟨40738274, by rfl⟩ : syracuseStep 54317699 = 81476549) B81476549
theorem B643719 : Blo 642303 643719 := bstep (se 1 (by rfl) ⟨482789, by rfl⟩ : syracuseStep 643719 = 965579) B965579
theorem B643727 : Blo 642303 643727 := bstep (se 1 (by rfl) ⟨482795, by rfl⟩ : syracuseStep 643727 = 965591) B965591
theorem B1954457 : Blo 642303 1954457 := bstep (se 2 (by rfl) ⟨732921, by rfl⟩ : syracuseStep 1954457 = 1465843) B1465843
theorem B643771 : Blo 642303 643771 := bstep (se 1 (by rfl) ⟨482828, by rfl⟩ : syracuseStep 643771 = 965657) B965657
theorem B643847 : Blo 642303 643847 := bstep (se 1 (by rfl) ⟨482885, by rfl⟩ : syracuseStep 643847 = 965771) B965771
theorem B643855 : Blo 642303 643855 := bstep (se 1 (by rfl) ⟨482891, by rfl⟩ : syracuseStep 643855 = 965783) B965783
theorem B643899 : Blo 642303 643899 := bstep (se 1 (by rfl) ⟨482924, by rfl⟩ : syracuseStep 643899 = 965849) B965849
theorem B4117337 : Blo 642303 4117337 := bstep (se 2 (by rfl) ⟨1544001, by rfl⟩ : syracuseStep 4117337 = 3088003) B3088003
theorem B643975 : Blo 642303 643975 := bstep (se 1 (by rfl) ⟨482981, by rfl⟩ : syracuseStep 643975 = 965963) B965963
theorem B643983 : Blo 642303 643983 := bstep (se 1 (by rfl) ⟨482987, by rfl⟩ : syracuseStep 643983 = 965975) B965975
theorem B3265433 : Blo 642303 3265433 := bstep (se 2 (by rfl) ⟨1224537, by rfl⟩ : syracuseStep 3265433 = 2449075) B2449075
theorem B644027 : Blo 642303 644027 := bstep (se 1 (by rfl) ⟨483020, by rfl⟩ : syracuseStep 644027 = 966041) B966041
theorem B644103 : Blo 642303 644103 := bstep (se 1 (by rfl) ⟨483077, by rfl⟩ : syracuseStep 644103 = 966155) B966155
theorem B644111 : Blo 642303 644111 := bstep (se 1 (by rfl) ⟨483083, by rfl⟩ : syracuseStep 644111 = 966167) B966167
theorem B644155 : Blo 642303 644155 := bstep (se 1 (by rfl) ⟨483116, by rfl⟩ : syracuseStep 644155 = 966233) B966233
theorem B644231 : Blo 642303 644231 := bstep (se 1 (by rfl) ⟨483173, by rfl⟩ : syracuseStep 644231 = 966347) B966347
theorem B644239 : Blo 642303 644239 := bstep (se 1 (by rfl) ⟨483179, by rfl⟩ : syracuseStep 644239 = 966359) B966359
theorem B644283 : Blo 642303 644283 := bstep (se 1 (by rfl) ⟨483212, by rfl⟩ : syracuseStep 644283 = 966425) B966425
theorem B644359 : Blo 642303 644359 := bstep (se 1 (by rfl) ⟨483269, by rfl⟩ : syracuseStep 644359 = 966539) B966539
theorem B644367 : Blo 642303 644367 := bstep (se 1 (by rfl) ⟨483275, by rfl⟩ : syracuseStep 644367 = 966551) B966551
theorem B4904225 : Blo 642303 4904225 := bstep (se 2 (by rfl) ⟨1839084, by rfl⟩ : syracuseStep 4904225 = 3678169) B3678169
theorem B644411 : Blo 642303 644411 := bstep (se 1 (by rfl) ⟨483308, by rfl⟩ : syracuseStep 644411 = 966617) B966617
theorem B644487 : Blo 642303 644487 := bstep (se 1 (by rfl) ⟨483365, by rfl⟩ : syracuseStep 644487 = 966731) B966731
theorem B644495 : Blo 642303 644495 := bstep (se 1 (by rfl) ⟨483371, by rfl⟩ : syracuseStep 644495 = 966743) B966743
theorem B5952953 : Blo 642303 5952953 := bstep (se 2 (by rfl) ⟨2232357, by rfl⟩ : syracuseStep 5952953 = 4464715) B4464715
theorem B644539 : Blo 642303 644539 := bstep (se 1 (by rfl) ⟨483404, by rfl⟩ : syracuseStep 644539 = 966809) B966809
theorem B644615 : Blo 642303 644615 := bstep (se 1 (by rfl) ⟨483461, by rfl⟩ : syracuseStep 644615 = 966923) B966923
theorem B644623 : Blo 642303 644623 := bstep (se 1 (by rfl) ⟨483467, by rfl⟩ : syracuseStep 644623 = 966935) B966935
theorem B644667 : Blo 642303 644667 := bstep (se 1 (by rfl) ⟨483500, by rfl⟩ : syracuseStep 644667 = 967001) B967001
theorem B1627735 : Blo 642303 1627735 := bstep (se 1 (by rfl) ⟨1220801, by rfl⟩ : syracuseStep 1627735 = 2441603) B2441603
theorem B644743 : Blo 642303 644743 := bstep (se 1 (by rfl) ⟨483557, by rfl⟩ : syracuseStep 644743 = 967115) B967115
theorem B644751 : Blo 642303 644751 := bstep (se 1 (by rfl) ⟨483563, by rfl⟩ : syracuseStep 644751 = 967127) B967127
theorem B644795 : Blo 642303 644795 := bstep (se 1 (by rfl) ⟨483596, by rfl⟩ : syracuseStep 644795 = 967193) B967193
theorem B644871 : Blo 642303 644871 := bstep (se 1 (by rfl) ⟨483653, by rfl⟩ : syracuseStep 644871 = 967307) B967307
theorem B644879 : Blo 642303 644879 := bstep (se 1 (by rfl) ⟨483659, by rfl⟩ : syracuseStep 644879 = 967319) B967319
theorem B644923 : Blo 642303 644923 := bstep (se 1 (by rfl) ⟨483692, by rfl⟩ : syracuseStep 644923 = 967385) B967385
theorem B1628039 : Blo 642303 1628039 := bstep (se 1 (by rfl) ⟨1221029, by rfl⟩ : syracuseStep 1628039 = 2442059) B2442059
theorem B644999 : Blo 642303 644999 := bstep (se 1 (by rfl) ⟨483749, by rfl⟩ : syracuseStep 644999 = 967499) B967499
theorem B645007 : Blo 642303 645007 := bstep (se 1 (by rfl) ⟨483755, by rfl⟩ : syracuseStep 645007 = 967511) B967511
theorem B645051 : Blo 642303 645051 := bstep (se 1 (by rfl) ⟨483788, by rfl⟩ : syracuseStep 645051 = 967577) B967577
theorem B3659741 : Blo 642303 3659741 := bstep (se 3 (by rfl) ⟨686201, by rfl⟩ : syracuseStep 3659741 = 1372403) B1372403
theorem B645127 : Blo 642303 645127 := bstep (se 1 (by rfl) ⟨483845, by rfl⟩ : syracuseStep 645127 = 967691) B967691
theorem B1628171 : Blo 642303 1628171 := bstep (se 1 (by rfl) ⟨1221128, by rfl⟩ : syracuseStep 1628171 = 2442257) B2442257
theorem B645135 : Blo 642303 645135 := bstep (se 1 (by rfl) ⟨483851, by rfl⟩ : syracuseStep 645135 = 967703) B967703
theorem B645179 : Blo 642303 645179 := bstep (se 1 (by rfl) ⟨483884, by rfl⟩ : syracuseStep 645179 = 967769) B967769
theorem B645255 : Blo 642303 645255 := bstep (se 1 (by rfl) ⟨483941, by rfl⟩ : syracuseStep 645255 = 967883) B967883
theorem B645263 : Blo 642303 645263 := bstep (se 1 (by rfl) ⟨483947, by rfl⟩ : syracuseStep 645263 = 967895) B967895
theorem B6641837 : Blo 642303 6641837 := bstep (se 3 (by rfl) ⟨1245344, by rfl⟩ : syracuseStep 6641837 = 2490689) B2490689
theorem B645307 : Blo 642303 645307 := bstep (se 1 (by rfl) ⟨483980, by rfl⟩ : syracuseStep 645307 = 967961) B967961
theorem B4905197 : Blo 642303 4905197 := bstep (se 3 (by rfl) ⟨919724, by rfl⟩ : syracuseStep 4905197 = 1839449) B1839449
theorem B2447617 : Blo 642303 2447617 := bstep (se 2 (by rfl) ⟨917856, by rfl⟩ : syracuseStep 2447617 = 1835713) B1835713
theorem B645383 : Blo 642303 645383 := bstep (se 1 (by rfl) ⟨484037, by rfl⟩ : syracuseStep 645383 = 968075) B968075
theorem B645391 : Blo 642303 645391 := bstep (se 1 (by rfl) ⟨484043, by rfl⟩ : syracuseStep 645391 = 968087) B968087
theorem B645435 : Blo 642303 645435 := bstep (se 1 (by rfl) ⟨484076, by rfl⟩ : syracuseStep 645435 = 968153) B968153
theorem B1857853 : Blo 642303 1857853 := bstep (se 3 (by rfl) ⟨348347, by rfl⟩ : syracuseStep 1857853 = 696695) B696695
theorem B645511 : Blo 642303 645511 := bstep (se 1 (by rfl) ⟨484133, by rfl⟩ : syracuseStep 645511 = 968267) B968267
theorem B645519 : Blo 642303 645519 := bstep (se 1 (by rfl) ⟨484139, by rfl⟩ : syracuseStep 645519 = 968279) B968279
theorem B645563 : Blo 642303 645563 := bstep (se 1 (by rfl) ⟨484172, by rfl⟩ : syracuseStep 645563 = 968345) B968345
theorem B645639 : Blo 642303 645639 := bstep (se 1 (by rfl) ⟨484229, by rfl⟩ : syracuseStep 645639 = 968459) B968459
theorem B1628687 : Blo 642303 1628687 := bstep (se 1 (by rfl) ⟨1221515, by rfl⟩ : syracuseStep 1628687 = 2443031) B2443031
theorem B645647 : Blo 642303 645647 := bstep (se 1 (by rfl) ⟨484235, by rfl⟩ : syracuseStep 645647 = 968471) B968471
theorem B645691 : Blo 642303 645691 := bstep (se 1 (by rfl) ⟨484268, by rfl⟩ : syracuseStep 645691 = 968537) B968537
theorem B645767 : Blo 642303 645767 := bstep (se 1 (by rfl) ⟨484325, by rfl⟩ : syracuseStep 645767 = 968651) B968651
theorem B645775 : Blo 642303 645775 := bstep (se 1 (by rfl) ⟨484331, by rfl⟩ : syracuseStep 645775 = 968663) B968663
theorem B1628819 : Blo 642303 1628819 := bstep (se 1 (by rfl) ⟨1221614, by rfl⟩ : syracuseStep 1628819 = 2443229) B2443229
theorem B645819 : Blo 642303 645819 := bstep (se 1 (by rfl) ⟨484364, by rfl⟩ : syracuseStep 645819 = 968729) B968729
theorem B645895 : Blo 642303 645895 := bstep (se 1 (by rfl) ⟨484421, by rfl⟩ : syracuseStep 645895 = 968843) B968843
theorem B1858315 : Blo 642303 1858315 := bstep (se 1 (by rfl) ⟨1393736, by rfl⟩ : syracuseStep 1858315 = 2787473) B2787473
theorem B5233423 : Blo 642303 5233423 := bstep (se 1 (by rfl) ⟨3925067, by rfl⟩ : syracuseStep 5233423 = 7850135) B7850135
theorem B645903 : Blo 642303 645903 := bstep (se 1 (by rfl) ⟨484427, by rfl⟩ : syracuseStep 645903 = 968855) B968855
theorem B645947 : Blo 642303 645947 := bstep (se 1 (by rfl) ⟨484460, by rfl⟩ : syracuseStep 645947 = 968921) B968921
theorem B646023 : Blo 642303 646023 := bstep (se 1 (by rfl) ⟨484517, by rfl⟩ : syracuseStep 646023 = 969035) B969035
theorem B646031 : Blo 642303 646031 := bstep (se 1 (by rfl) ⟨484523, by rfl⟩ : syracuseStep 646031 = 969047) B969047
theorem B646075 : Blo 642303 646075 := bstep (se 1 (by rfl) ⟨484556, by rfl⟩ : syracuseStep 646075 = 969113) B969113
theorem B646151 : Blo 642303 646151 := bstep (se 1 (by rfl) ⟨484613, by rfl⟩ : syracuseStep 646151 = 969227) B969227
theorem B1989647 : Blo 642303 1989647 := bstep (se 1 (by rfl) ⟨1492235, by rfl⟩ : syracuseStep 1989647 = 2984471) B2984471
theorem B646159 : Blo 642303 646159 := bstep (se 1 (by rfl) ⟨484619, by rfl⟩ : syracuseStep 646159 = 969239) B969239
theorem B646203 : Blo 642303 646203 := bstep (se 1 (by rfl) ⟨484652, by rfl⟩ : syracuseStep 646203 = 969305) B969305
theorem B646279 : Blo 642303 646279 := bstep (se 1 (by rfl) ⟨484709, by rfl⟩ : syracuseStep 646279 = 969419) B969419
theorem B646287 : Blo 642303 646287 := bstep (se 1 (by rfl) ⟨484715, by rfl⟩ : syracuseStep 646287 = 969431) B969431
theorem B3268025 : Blo 642303 3268025 := bstep (se 2 (by rfl) ⟨1225509, by rfl⟩ : syracuseStep 3268025 = 2451019) B2451019
theorem B53632469 : Blo 642303 53632469 := bstep (se 7 (by rfl) ⟨628505, by rfl⟩ : syracuseStep 53632469 = 1257011) B1257011
theorem B3530263 : Blo 642303 3530263 := bstep (se 1 (by rfl) ⟨2647697, by rfl⟩ : syracuseStep 3530263 = 5295395) B5295395
theorem B16080413 : Blo 642303 16080413 := bstep (se 3 (by rfl) ⟨3015077, by rfl⟩ : syracuseStep 16080413 = 6030155) B6030155
theorem B1629953 : Blo 642303 1629953 := bstep (se 2 (by rfl) ⟨611232, by rfl⟩ : syracuseStep 1629953 = 1222465) B1222465
theorem B1630327 : Blo 642303 1630327 := bstep (se 1 (by rfl) ⟨1222745, by rfl⟩ : syracuseStep 1630327 = 2445491) B2445491
theorem B4907141 : Blo 642303 4907141 := bstep (se 4 (by rfl) ⟨460044, by rfl⟩ : syracuseStep 4907141 = 920089) B920089
theorem B3662131 : Blo 642303 3662131 := bstep (se 1 (by rfl) ⟨2746598, by rfl⟩ : syracuseStep 3662131 = 5493197) B5493197
theorem B7332281 : Blo 642303 7332281 := bstep (se 2 (by rfl) ⟨2749605, by rfl⟩ : syracuseStep 7332281 = 5499211) B5499211
theorem B1630763 : Blo 642303 1630763 := bstep (se 1 (by rfl) ⟨1223072, by rfl⟩ : syracuseStep 1630763 = 2446145) B2446145
theorem B3269321 : Blo 642303 3269321 := bstep (se 2 (by rfl) ⟨1225995, by rfl⟩ : syracuseStep 3269321 = 2451991) B2451991
theorem B2450519 : Blo 642303 2450519 := bstep (se 1 (by rfl) ⟨1837889, by rfl⟩ : syracuseStep 2450519 = 3675779) B3675779
theorem B1631603 : Blo 642303 1631603 := bstep (se 1 (by rfl) ⟨1223702, by rfl⟩ : syracuseStep 1631603 = 2447405) B2447405
theorem B1631623 : Blo 642303 1631623 := bstep (se 1 (by rfl) ⟨1223717, by rfl⟩ : syracuseStep 1631623 = 2447435) B2447435
theorem B2942507 : Blo 642303 2942507 := bstep (se 1 (by rfl) ⟨2206880, by rfl⟩ : syracuseStep 2942507 = 4413761) B4413761
theorem B2451005 : Blo 642303 2451005 := bstep (se 3 (by rfl) ⟨459563, by rfl⟩ : syracuseStep 2451005 = 919127) B919127
theorem B1631897 : Blo 642303 1631897 := bstep (se 2 (by rfl) ⟨611961, by rfl⟩ : syracuseStep 1631897 = 1223923) B1223923
theorem B3663589 : Blo 642303 3663589 := bstep (se 4 (by rfl) ⟨343461, by rfl⟩ : syracuseStep 3663589 = 686923) B686923
theorem B976699 : Blo 642303 976699 := bstep (se 1 (by rfl) ⟨732524, by rfl⟩ : syracuseStep 976699 = 1465049) B1465049
theorem B1632059 : Blo 642303 1632059 := bstep (se 1 (by rfl) ⟨1224044, by rfl⟩ : syracuseStep 1632059 = 2448089) B2448089
theorem B1566611 : Blo 642303 1566611 := bstep (se 1 (by rfl) ⟨1174958, by rfl⟩ : syracuseStep 1566611 = 2349917) B2349917
theorem B1632271 : Blo 642303 1632271 := bstep (se 1 (by rfl) ⟨1224203, by rfl⟩ : syracuseStep 1632271 = 2448407) B2448407
theorem B6973613 : Blo 642303 6973613 := bstep (se 3 (by rfl) ⟨1307552, by rfl⟩ : syracuseStep 6973613 = 2615105) B2615105
theorem B13920497 : Blo 642303 13920497 := bstep (se 2 (by rfl) ⟨5220186, by rfl⟩ : syracuseStep 13920497 = 10440373) B10440373
theorem B1566977 : Blo 642303 1566977 := bstep (se 2 (by rfl) ⟨587616, by rfl⟩ : syracuseStep 1566977 = 1175233) B1175233
theorem B1632545 : Blo 642303 1632545 := bstep (se 2 (by rfl) ⟨612204, by rfl⟩ : syracuseStep 1632545 = 1224409) B1224409
theorem B8251793 : Blo 642303 8251793 := bstep (se 2 (by rfl) ⟨3094422, by rfl⟩ : syracuseStep 8251793 = 6188845) B6188845
theorem B1829267 : Blo 642303 1829267 := bstep (se 1 (by rfl) ⟨1371950, by rfl⟩ : syracuseStep 1829267 = 2743901) B2743901
theorem B813559 : Blo 642303 813559 := bstep (se 1 (by rfl) ⟨610169, by rfl⟩ : syracuseStep 813559 = 1220339) B1220339
theorem B19852037 : Blo 642303 19852037 := bstep (se 4 (by rfl) ⟨1861128, by rfl⟩ : syracuseStep 19852037 = 3722257) B3722257
theorem B813883 : Blo 642303 813883 := bstep (se 1 (by rfl) ⟨610412, by rfl⟩ : syracuseStep 813883 = 1220825) B1220825
theorem B1633547 : Blo 642303 1633547 := bstep (se 1 (by rfl) ⟨1225160, by rfl⟩ : syracuseStep 1633547 = 2450321) B2450321
theorem B2452751 : Blo 642303 2452751 := bstep (se 1 (by rfl) ⟨1839563, by rfl⟩ : syracuseStep 2452751 = 3679127) B3679127
theorem B3927329 : Blo 642303 3927329 := bstep (se 2 (by rfl) ⟨1472748, by rfl⟩ : syracuseStep 3927329 = 2945497) B2945497
theorem B3141011 : Blo 642303 3141011 := bstep (se 1 (by rfl) ⟨2355758, by rfl⟩ : syracuseStep 3141011 = 4711517) B4711517
theorem B7958083 : Blo 642303 7958083 := bstep (se 1 (by rfl) ⟨5968562, by rfl⟩ : syracuseStep 7958083 = 11937125) B11937125
theorem B814855 : Blo 642303 814855 := bstep (se 1 (by rfl) ⟨611141, by rfl⟩ : syracuseStep 814855 = 1222283) B1222283
theorem B1240847 : Blo 642303 1240847 := bstep (se 1 (by rfl) ⟨930635, by rfl⟩ : syracuseStep 1240847 = 1861271) B1861271
theorem B2748275 : Blo 642303 2748275 := bstep (se 1 (by rfl) ⟨2061206, by rfl⟩ : syracuseStep 2748275 = 4122413) B4122413
theorem B1634195 : Blo 642303 1634195 := bstep (se 1 (by rfl) ⟨1225646, by rfl⟩ : syracuseStep 1634195 = 2451293) B2451293
theorem B2715709 : Blo 642303 2715709 := bstep (se 3 (by rfl) ⟨509195, by rfl⟩ : syracuseStep 2715709 = 1018391) B1018391
theorem B815275 : Blo 642303 815275 := bstep (se 1 (by rfl) ⟨611456, by rfl⟩ : syracuseStep 815275 = 1222913) B1222913
theorem B1634489 : Blo 642303 1634489 := bstep (se 2 (by rfl) ⟨612933, by rfl⟩ : syracuseStep 1634489 = 1225867) B1225867
theorem B14151881 : Blo 642303 14151881 := bstep (se 2 (by rfl) ⟨5306955, by rfl⟩ : syracuseStep 14151881 = 10613911) B10613911
theorem B815503 : Blo 642303 815503 := bstep (se 1 (by rfl) ⟨611627, by rfl⟩ : syracuseStep 815503 = 1223255) B1223255
theorem B3666323 : Blo 642303 3666323 := bstep (se 1 (by rfl) ⟨2749742, by rfl⟩ : syracuseStep 3666323 = 5499485) B5499485
theorem B1307065 : Blo 642303 1307065 := bstep (se 2 (by rfl) ⟨490149, by rfl⟩ : syracuseStep 1307065 = 980299) B980299
theorem B1864225 : Blo 642303 1864225 := bstep (se 2 (by rfl) ⟨699084, by rfl⟩ : syracuseStep 1864225 = 1398169) B1398169
theorem B6287939 : Blo 642303 6287939 := bstep (se 1 (by rfl) ⟨4715954, by rfl⟩ : syracuseStep 6287939 = 9431909) B9431909
theorem B1831511 : Blo 642303 1831511 := bstep (se 1 (by rfl) ⟨1373633, by rfl⟩ : syracuseStep 1831511 = 2747267) B2747267
theorem B1635187 : Blo 642303 1635187 := bstep (se 1 (by rfl) ⟨1226390, by rfl⟩ : syracuseStep 1635187 = 2452781) B2452781
theorem B14873507 : Blo 642303 14873507 := bstep (se 1 (by rfl) ⟨11155130, by rfl⟩ : syracuseStep 14873507 = 22310261) B22310261
theorem B1373129 : Blo 642303 1373129 := bstep (se 2 (by rfl) ⟨514923, by rfl⟩ : syracuseStep 1373129 = 1029847) B1029847
theorem B1635329 : Blo 642303 1635329 := bstep (se 2 (by rfl) ⟨613248, by rfl⟩ : syracuseStep 1635329 = 1226497) B1226497
theorem B3142685 : Blo 642303 3142685 := bstep (se 3 (by rfl) ⟨589253, by rfl⟩ : syracuseStep 3142685 = 1178507) B1178507
theorem B3306539 : Blo 642303 3306539 := bstep (se 1 (by rfl) ⟨2479904, by rfl⟩ : syracuseStep 3306539 = 4959809) B4959809
theorem B3667031 : Blo 642303 3667031 := bstep (se 1 (by rfl) ⟨2750273, by rfl⟩ : syracuseStep 3667031 = 5500547) B5500547
theorem B816247 : Blo 642303 816247 := bstep (se 1 (by rfl) ⟨612185, by rfl⟩ : syracuseStep 816247 = 1224371) B1224371
theorem B816571 : Blo 642303 816571 := bstep (se 1 (by rfl) ⟨612428, by rfl⟩ : syracuseStep 816571 = 1224857) B1224857
theorem B1635785 : Blo 642303 1635785 := bstep (se 2 (by rfl) ⟨613419, by rfl⟩ : syracuseStep 1635785 = 1226839) B1226839
theorem B1373881 : Blo 642303 1373881 := bstep (se 2 (by rfl) ⟨515205, by rfl⟩ : syracuseStep 1373881 = 1030411) B1030411
theorem B817067 : Blo 642303 817067 := bstep (se 1 (by rfl) ⟨612800, by rfl⟩ : syracuseStep 817067 = 1225601) B1225601
theorem B2783243 : Blo 642303 2783243 := bstep (se 1 (by rfl) ⟨2087432, by rfl⟩ : syracuseStep 2783243 = 4174865) B4174865
theorem B20051981 : Blo 642303 20051981 := bstep (se 3 (by rfl) ⟨3759746, by rfl⟩ : syracuseStep 20051981 = 7519493) B7519493
theorem B915499 : Blo 642303 915499 := bstep (se 1 (by rfl) ⟨686624, by rfl⟩ : syracuseStep 915499 = 1373249) B1373249
theorem B686351 : Blo 642303 686351 := bstep (se 1 (by rfl) ⟨514763, by rfl⟩ : syracuseStep 686351 = 1029527) B1029527
theorem B915727 : Blo 642303 915727 := bstep (se 1 (by rfl) ⟨686795, by rfl⟩ : syracuseStep 915727 = 1373591) B1373591
theorem B1374479 : Blo 642303 1374479 := bstep (se 1 (by rfl) ⟨1030859, by rfl⟩ : syracuseStep 1374479 = 2061719) B2061719
theorem B817543 : Blo 642303 817543 := bstep (se 1 (by rfl) ⟨613157, by rfl⟩ : syracuseStep 817543 = 1226315) B1226315
theorem B686479 : Blo 642303 686479 := bstep (se 1 (by rfl) ⟨514859, by rfl⟩ : syracuseStep 686479 = 1029719) B1029719
theorem B1571257 : Blo 642303 1571257 := bstep (se 2 (by rfl) ⟨589221, by rfl⟩ : syracuseStep 1571257 = 1178443) B1178443
theorem B2619971 : Blo 642303 2619971 := bstep (se 1 (by rfl) ⟨1964978, by rfl⟩ : syracuseStep 2619971 = 3929957) B3929957
theorem B5503859 : Blo 642303 5503859 := bstep (se 1 (by rfl) ⟨4127894, by rfl⟩ : syracuseStep 5503859 = 8255789) B8255789
theorem B2751367 : Blo 642303 2751367 := bstep (se 1 (by rfl) ⟨2063525, by rfl⟩ : syracuseStep 2751367 = 4127051) B4127051
theorem B2620295 : Blo 642303 2620295 := bstep (se 1 (by rfl) ⟨1965221, by rfl⟩ : syracuseStep 2620295 = 3930443) B3930443
theorem B3668921 : Blo 642303 3668921 := bstep (se 2 (by rfl) ⟨1375845, by rfl⟩ : syracuseStep 3668921 = 2751691) B2751691
theorem B2751725 : Blo 642303 2751725 := bstep (se 3 (by rfl) ⟨515948, by rfl⟩ : syracuseStep 2751725 = 1031897) B1031897
theorem B1834255 : Blo 642303 1834255 := bstep (se 1 (by rfl) ⟨1375691, by rfl⟩ : syracuseStep 1834255 = 2751383) B2751383
theorem B1834301 : Blo 642303 1834301 := bstep (se 3 (by rfl) ⟨343931, by rfl⟩ : syracuseStep 1834301 = 687863) B687863
theorem B2063731 : Blo 642303 2063731 := bstep (se 1 (by rfl) ⟨1547798, by rfl⟩ : syracuseStep 2063731 = 3095597) B3095597
theorem B3964439 : Blo 642303 3964439 := bstep (se 1 (by rfl) ⟨2973329, by rfl⟩ : syracuseStep 3964439 = 5946659) B5946659
theorem B1736311 : Blo 642303 1736311 := bstep (se 1 (by rfl) ⟨1302233, by rfl⟩ : syracuseStep 1736311 = 2604467) B2604467
theorem B1834643 : Blo 642303 1834643 := bstep (se 1 (by rfl) ⟨1375982, by rfl⟩ : syracuseStep 1834643 = 2751965) B2751965
theorem B1376033 : Blo 642303 1376033 := bstep (se 2 (by rfl) ⟨516012, by rfl⟩ : syracuseStep 1376033 = 1032025) B1032025
theorem B67927853 : Blo 642303 67927853 := bstep (se 3 (by rfl) ⟨12736472, by rfl⟩ : syracuseStep 67927853 = 25472945) B25472945
theorem B1376119 : Blo 642303 1376119 := bstep (se 1 (by rfl) ⟨1032089, by rfl⟩ : syracuseStep 1376119 = 2064179) B2064179
theorem B5504921 : Blo 642303 5504921 := bstep (se 2 (by rfl) ⟨2064345, by rfl⟩ : syracuseStep 5504921 = 4128691) B4128691
theorem B12058571 : Blo 642303 12058571 := bstep (se 1 (by rfl) ⟨9043928, by rfl⟩ : syracuseStep 12058571 = 18087857) B18087857
theorem B4882841 : Blo 642303 4882841 := bstep (se 2 (by rfl) ⟨1831065, by rfl⟩ : syracuseStep 4882841 = 3662131) B3662131
theorem B4129177 : Blo 642303 4129177 := bstep (se 2 (by rfl) ⟨1548441, by rfl⟩ : syracuseStep 4129177 = 3096883) B3096883
theorem B1376777 : Blo 642303 1376777 := bstep (se 2 (by rfl) ⟨516291, by rfl⟩ : syracuseStep 1376777 = 1032583) B1032583
theorem B3146249 : Blo 642303 3146249 := bstep (se 2 (by rfl) ⟨1179843, by rfl⟩ : syracuseStep 3146249 = 2359687) B2359687
theorem B8389331 : Blo 642303 8389331 := bstep (se 1 (by rfl) ⟨6291998, by rfl⟩ : syracuseStep 8389331 = 12583997) B12583997
theorem B2065409 : Blo 642303 2065409 := bstep (se 2 (by rfl) ⟨774528, by rfl⟩ : syracuseStep 2065409 = 1549057) B1549057
theorem B5506319 : Blo 642303 5506319 := bstep (se 1 (by rfl) ⟨4129739, by rfl⟩ : syracuseStep 5506319 = 8259479) B8259479
theorem B8390051 : Blo 642303 8390051 := bstep (se 1 (by rfl) ⟨6292538, by rfl⟩ : syracuseStep 8390051 = 12585077) B12585077
theorem B722983 : Blo 642303 722983 := bstep (se 1 (by rfl) ⟨542237, by rfl⟩ : syracuseStep 722983 = 1084475) B1084475
theorem B4884785 : Blo 642303 4884785 := bstep (se 2 (by rfl) ⟨1831794, by rfl⟩ : syracuseStep 4884785 = 3663589) B3663589
theorem B7342487 : Blo 642303 7342487 := bstep (se 1 (by rfl) ⟨5506865, by rfl⟩ : syracuseStep 7342487 = 11013731) B11013731
theorem B3475993 : Blo 642303 3475993 := bstep (se 2 (by rfl) ⟨1303497, by rfl⟩ : syracuseStep 3475993 = 2606995) B2606995
theorem B2329121 : Blo 642303 2329121 := bstep (se 2 (by rfl) ⟨873420, by rfl⟩ : syracuseStep 2329121 = 1746841) B1746841
theorem B16714421 : Blo 642303 16714421 := bstep (se 5 (by rfl) ⟨783488, by rfl⟩ : syracuseStep 16714421 = 1566977) B1566977
theorem B28314305 : Blo 642303 28314305 := bstep (se 2 (by rfl) ⟨10617864, by rfl⟩ : syracuseStep 28314305 = 21235729) B21235729
theorem B1084151 : Blo 642303 1084151 := bstep (se 1 (by rfl) ⟨813113, by rfl⟩ : syracuseStep 1084151 = 1626227) B1626227
theorem B8817437 : Blo 642303 8817437 := bstep (se 3 (by rfl) ⟨1653269, by rfl⟩ : syracuseStep 8817437 = 3306539) B3306539
theorem B2067383 : Blo 642303 2067383 := bstep (se 1 (by rfl) ⟨1550537, by rfl⟩ : syracuseStep 2067383 = 3101075) B3101075
theorem B1084495 : Blo 642303 1084495 := bstep (se 1 (by rfl) ⟨813371, by rfl⟩ : syracuseStep 1084495 = 1626743) B1626743
theorem B2067535 : Blo 642303 2067535 := bstep (se 1 (by rfl) ⟨1550651, by rfl⟩ : syracuseStep 2067535 = 3101303) B3101303
theorem B36211799 : Blo 642303 36211799 := bstep (se 1 (by rfl) ⟨27158849, by rfl⟩ : syracuseStep 36211799 = 54317699) B54317699
theorem B1084745 : Blo 642303 1084745 := bstep (se 2 (by rfl) ⟨406779, by rfl⟩ : syracuseStep 1084745 = 813559) B813559
theorem B3968635 : Blo 642303 3968635 := bstep (se 1 (by rfl) ⟨2976476, by rfl⟩ : syracuseStep 3968635 = 5952953) B5952953
theorem B724603 : Blo 642303 724603 := bstep (se 1 (by rfl) ⟨543452, by rfl⟩ : syracuseStep 724603 = 1086905) B1086905
theorem B1379963 : Blo 642303 1379963 := bstep (se 1 (by rfl) ⟨1034972, by rfl⟩ : syracuseStep 1379963 = 2069945) B2069945
theorem B1085177 : Blo 642303 1085177 := bstep (se 2 (by rfl) ⟨406941, by rfl⟩ : syracuseStep 1085177 = 813883) B813883
theorem B1445705 : Blo 642303 1445705 := bstep (se 2 (by rfl) ⟨542139, by rfl⟩ : syracuseStep 1445705 = 1084279) B1084279
theorem B1085359 : Blo 642303 1085359 := bstep (se 1 (by rfl) ⟨814019, by rfl⟩ : syracuseStep 1085359 = 1628039) B1628039
theorem B5312465 : Blo 642303 5312465 := bstep (se 2 (by rfl) ⟨1992174, by rfl⟩ : syracuseStep 5312465 = 3984349) B3984349
theorem B1085447 : Blo 642303 1085447 := bstep (se 1 (by rfl) ⟨814085, by rfl⟩ : syracuseStep 1085447 = 1628171) B1628171
theorem B725071 : Blo 642303 725071 := bstep (se 1 (by rfl) ⟨543803, by rfl⟩ : syracuseStep 725071 = 1087607) B1087607
theorem B4427891 : Blo 642303 4427891 := bstep (se 1 (by rfl) ⟨3320918, by rfl⟩ : syracuseStep 4427891 = 6641837) B6641837
theorem B1085791 : Blo 642303 1085791 := bstep (se 1 (by rfl) ⟨814343, by rfl⟩ : syracuseStep 1085791 = 1628687) B1628687
theorem B1085879 : Blo 642303 1085879 := bstep (se 1 (by rfl) ⟨814409, by rfl⟩ : syracuseStep 1085879 = 1628819) B1628819
theorem B725467 : Blo 642303 725467 := bstep (se 1 (by rfl) ⟨544100, by rfl⟩ : syracuseStep 725467 = 1088201) B1088201
theorem B3478049 : Blo 642303 3478049 := bstep (se 2 (by rfl) ⟨1304268, by rfl⟩ : syracuseStep 3478049 = 2608537) B2608537
theorem B1446497 : Blo 642303 1446497 := bstep (se 2 (by rfl) ⟨542436, by rfl⟩ : syracuseStep 1446497 = 1084873) B1084873
theorem B725935 : Blo 642303 725935 := bstep (se 1 (by rfl) ⟨544451, by rfl⟩ : syracuseStep 725935 = 1088903) B1088903
theorem B1446839 : Blo 642303 1446839 := bstep (se 1 (by rfl) ⟨1085129, by rfl⟩ : syracuseStep 1446839 = 2170259) B2170259
theorem B35754979 : Blo 642303 35754979 := bstep (se 1 (by rfl) ⟨26816234, by rfl⟩ : syracuseStep 35754979 = 53632469) B53632469
theorem B1086473 : Blo 642303 1086473 := bstep (se 2 (by rfl) ⟨407427, by rfl⟩ : syracuseStep 1086473 = 814855) B814855
theorem B1086635 : Blo 642303 1086635 := bstep (se 1 (by rfl) ⟨814976, by rfl⟩ : syracuseStep 1086635 = 1629953) B1629953
theorem B726367 : Blo 642303 726367 := bstep (se 1 (by rfl) ⟨544775, by rfl⟩ : syracuseStep 726367 = 1089551) B1089551
theorem B2758013 : Blo 642303 2758013 := bstep (se 3 (by rfl) ⟨517127, by rfl⟩ : syracuseStep 2758013 = 1034255) B1034255
theorem B2168207 : Blo 642303 2168207 := bstep (se 1 (by rfl) ⟨1626155, by rfl⟩ : syracuseStep 2168207 = 3252311) B3252311
theorem B1447433 : Blo 642303 1447433 := bstep (se 2 (by rfl) ⟨542787, by rfl⟩ : syracuseStep 1447433 = 1085575) B1085575
theorem B1087033 : Blo 642303 1087033 := bstep (se 2 (by rfl) ⟨407637, by rfl⟩ : syracuseStep 1087033 = 815275) B815275
theorem B4888187 : Blo 642303 4888187 := bstep (se 1 (by rfl) ⟨3666140, by rfl⟩ : syracuseStep 4888187 = 7332281) B7332281
theorem B1087175 : Blo 642303 1087175 := bstep (se 1 (by rfl) ⟨815381, by rfl⟩ : syracuseStep 1087175 = 1630763) B1630763
theorem B726727 : Blo 642303 726727 := bstep (se 1 (by rfl) ⟨545045, by rfl⟩ : syracuseStep 726727 = 1090091) B1090091
theorem B2168531 : Blo 642303 2168531 := bstep (se 1 (by rfl) ⟨1626398, by rfl⟩ : syracuseStep 2168531 = 3252797) B3252797
theorem B1447775 : Blo 642303 1447775 := bstep (se 1 (by rfl) ⟨1085831, by rfl⟩ : syracuseStep 1447775 = 2171663) B2171663
theorem B1087337 : Blo 642303 1087337 := bstep (se 2 (by rfl) ⟨407751, by rfl⟩ : syracuseStep 1087337 = 815503) B815503
theorem B1742753 : Blo 642303 1742753 := bstep (se 2 (by rfl) ⟨653532, by rfl⟩ : syracuseStep 1742753 = 1307065) B1307065
theorem B1447955 : Blo 642303 1447955 := bstep (se 1 (by rfl) ⟨1085966, by rfl⟩ : syracuseStep 1447955 = 2171933) B2171933
theorem B1087735 : Blo 642303 1087735 := bstep (se 1 (by rfl) ⟨815801, by rfl⟩ : syracuseStep 1087735 = 1631603) B1631603
theorem B1448297 : Blo 642303 1448297 := bstep (se 2 (by rfl) ⟨543111, by rfl⟩ : syracuseStep 1448297 = 1086223) B1086223
theorem B1087931 : Blo 642303 1087931 := bstep (se 1 (by rfl) ⟨815948, by rfl⟩ : syracuseStep 1087931 = 1631897) B1631897
theorem B3709421 : Blo 642303 3709421 := bstep (se 3 (by rfl) ⟨695516, by rfl⟩ : syracuseStep 3709421 = 1391033) B1391033
theorem B1088039 : Blo 642303 1088039 := bstep (se 1 (by rfl) ⟨816029, by rfl⟩ : syracuseStep 1088039 = 1632059) B1632059
theorem B1088329 : Blo 642303 1088329 := bstep (se 2 (by rfl) ⟨408123, by rfl⟩ : syracuseStep 1088329 = 816247) B816247
theorem B9280331 : Blo 642303 9280331 := bstep (se 1 (by rfl) ⟨6960248, by rfl⟩ : syracuseStep 9280331 = 13920497) B13920497
theorem B1088363 : Blo 642303 1088363 := bstep (se 1 (by rfl) ⟨816272, by rfl⟩ : syracuseStep 1088363 = 1632545) B1632545
theorem B2169719 : Blo 642303 2169719 := bstep (se 1 (by rfl) ⟨1627289, by rfl⟩ : syracuseStep 2169719 = 3254579) B3254579
theorem B1219511 : Blo 642303 1219511 := bstep (se 1 (by rfl) ⟨914633, by rfl⟩ : syracuseStep 1219511 = 1829267) B1829267
theorem B1448891 : Blo 642303 1448891 := bstep (se 1 (by rfl) ⟨1086668, by rfl⟩ : syracuseStep 1448891 = 2173337) B2173337
theorem B1449017 : Blo 642303 1449017 := bstep (se 2 (by rfl) ⟨543381, by rfl⟩ : syracuseStep 1449017 = 1086763) B1086763
theorem B2169935 : Blo 642303 2169935 := bstep (se 1 (by rfl) ⟨1627451, by rfl⟩ : syracuseStep 2169935 = 3254903) B3254903
theorem B1088761 : Blo 642303 1088761 := bstep (se 2 (by rfl) ⟨408285, by rfl⟩ : syracuseStep 1088761 = 816571) B816571
theorem B1449359 : Blo 642303 1449359 := bstep (se 1 (by rfl) ⟨1087019, by rfl⟩ : syracuseStep 1449359 = 2174039) B2174039
theorem B2170313 : Blo 642303 2170313 := bstep (se 2 (by rfl) ⟨813867, by rfl⟩ : syracuseStep 2170313 = 1627735) B1627735
theorem B1089031 : Blo 642303 1089031 := bstep (se 1 (by rfl) ⟨816773, by rfl⟩ : syracuseStep 1089031 = 1633547) B1633547
theorem B1449683 : Blo 642303 1449683 := bstep (se 1 (by rfl) ⟨1087262, by rfl⟩ : syracuseStep 1449683 = 2174525) B2174525
theorem B2170583 : Blo 642303 2170583 := bstep (se 1 (by rfl) ⟨1627937, by rfl⟩ : syracuseStep 2170583 = 3255875) B3255875
theorem B827231 : Blo 642303 827231 := bstep (se 1 (by rfl) ⟨620423, by rfl⟩ : syracuseStep 827231 = 1240847) B1240847
theorem B2170799 : Blo 642303 2170799 := bstep (se 1 (by rfl) ⟨1628099, by rfl⟩ : syracuseStep 2170799 = 3256199) B3256199
theorem B1089463 : Blo 642303 1089463 := bstep (se 1 (by rfl) ⟨817097, by rfl⟩ : syracuseStep 1089463 = 1634195) B1634195
theorem B27795473 : Blo 642303 27795473 := bstep (se 2 (by rfl) ⟨10423302, by rfl⟩ : syracuseStep 27795473 = 20846605) B20846605
theorem B1220665 : Blo 642303 1220665 := bstep (se 2 (by rfl) ⟨457749, by rfl⟩ : syracuseStep 1220665 = 915499) B915499
theorem B1089659 : Blo 642303 1089659 := bstep (se 1 (by rfl) ⟨817244, by rfl⟩ : syracuseStep 1089659 = 1634489) B1634489
theorem B9281765 : Blo 642303 9281765 := bstep (se 4 (by rfl) ⟨870165, by rfl⟩ : syracuseStep 9281765 = 1740331) B1740331
theorem B1220969 : Blo 642303 1220969 := bstep (se 2 (by rfl) ⟨457863, by rfl⟩ : syracuseStep 1220969 = 915727) B915727
theorem B1221007 : Blo 642303 1221007 := bstep (se 1 (by rfl) ⟨915755, by rfl⟩ : syracuseStep 1221007 = 1831511) B1831511
theorem B1090057 : Blo 642303 1090057 := bstep (se 2 (by rfl) ⟨408771, by rfl⟩ : syracuseStep 1090057 = 817543) B817543
theorem B1450619 : Blo 642303 1450619 := bstep (se 1 (by rfl) ⟨1087964, by rfl⟩ : syracuseStep 1450619 = 2175929) B2175929
theorem B1090219 : Blo 642303 1090219 := bstep (se 1 (by rfl) ⟨817664, by rfl⟩ : syracuseStep 1090219 = 1635329) B1635329
theorem B1450745 : Blo 642303 1450745 := bstep (se 2 (by rfl) ⟨544029, by rfl⟩ : syracuseStep 1450745 = 1088059) B1088059
theorem B1090523 : Blo 642303 1090523 := bstep (se 1 (by rfl) ⟨817892, by rfl⟩ : syracuseStep 1090523 = 1635785) B1635785
theorem B1451015 : Blo 642303 1451015 := bstep (se 1 (by rfl) ⟨1088261, by rfl⟩ : syracuseStep 1451015 = 2176523) B2176523
theorem B1451087 : Blo 642303 1451087 := bstep (se 1 (by rfl) ⟨1088315, by rfl⟩ : syracuseStep 1451087 = 2176631) B2176631
theorem B1451483 : Blo 642303 1451483 := bstep (se 1 (by rfl) ⟨1088612, by rfl⟩ : syracuseStep 1451483 = 2177225) B2177225
theorem B1746647 : Blo 642303 1746647 := bstep (se 1 (by rfl) ⟨1309985, by rfl⟩ : syracuseStep 1746647 = 2619971) B2619971
theorem B5515067 : Blo 642303 5515067 := bstep (se 1 (by rfl) ⟨4136300, by rfl⟩ : syracuseStep 5515067 = 8272601) B8272601
theorem B1550153 : Blo 642303 1550153 := bstep (se 2 (by rfl) ⟨581307, by rfl⟩ : syracuseStep 1550153 = 1162615) B1162615
theorem B1451951 : Blo 642303 1451951 := bstep (se 1 (by rfl) ⟨1088963, by rfl⟩ : syracuseStep 1451951 = 2177927) B2177927
theorem B1746863 : Blo 642303 1746863 := bstep (se 1 (by rfl) ⟨1310147, by rfl⟩ : syracuseStep 1746863 = 2620295) B2620295
theorem B1452203 : Blo 642303 1452203 := bstep (se 1 (by rfl) ⟨1089152, by rfl⟩ : syracuseStep 1452203 = 2178305) B2178305
theorem B1222867 : Blo 642303 1222867 := bstep (se 1 (by rfl) ⟨917150, by rfl⟩ : syracuseStep 1222867 = 1834301) B1834301
theorem B2173175 : Blo 642303 2173175 := bstep (se 1 (by rfl) ⟨1629881, by rfl⟩ : syracuseStep 2173175 = 3259763) B3259763
theorem B1223095 : Blo 642303 1223095 := bstep (se 1 (by rfl) ⟨917321, by rfl⟩ : syracuseStep 1223095 = 1834643) B1834643
theorem B32156189 : Blo 642303 32156189 := bstep (se 3 (by rfl) ⟨6029285, by rfl⟩ : syracuseStep 32156189 = 12058571) B12058571
theorem B2173499 : Blo 642303 2173499 := bstep (se 1 (by rfl) ⟨1630124, by rfl⟩ : syracuseStep 2173499 = 3260249) B3260249
theorem B3680903 : Blo 642303 3680903 := bstep (se 1 (by rfl) ⟨2760677, by rfl⟩ : syracuseStep 3680903 = 5521355) B5521355
theorem B1452743 : Blo 642303 1452743 := bstep (se 1 (by rfl) ⟨1089557, by rfl⟩ : syracuseStep 1452743 = 2179115) B2179115
theorem B2173769 : Blo 642303 2173769 := bstep (se 2 (by rfl) ⟨815163, by rfl⟩ : syracuseStep 2173769 = 1630327) B1630327
theorem B1223687 : Blo 642303 1223687 := bstep (se 1 (by rfl) ⟨917765, by rfl⟩ : syracuseStep 1223687 = 1835531) B1835531
theorem B6204761 : Blo 642303 6204761 := bstep (se 2 (by rfl) ⟨2326785, by rfl⟩ : syracuseStep 6204761 = 4653571) B4653571
theorem B1453607 : Blo 642303 1453607 := bstep (se 1 (by rfl) ⟨1090205, by rfl⟩ : syracuseStep 1453607 = 2180411) B2180411
theorem B5222033 : Blo 642303 5222033 := bstep (se 2 (by rfl) ⟨1958262, by rfl⟩ : syracuseStep 5222033 = 3916525) B3916525
theorem B6598381 : Blo 642303 6598381 := bstep (se 3 (by rfl) ⟨1237196, by rfl⟩ : syracuseStep 6598381 = 2474393) B2474393
theorem B2797379 : Blo 642303 2797379 := bstep (se 1 (by rfl) ⟨2098034, by rfl⟩ : syracuseStep 2797379 = 4196069) B4196069
theorem B1224553 : Blo 642303 1224553 := bstep (se 2 (by rfl) ⟨459207, by rfl⟩ : syracuseStep 1224553 = 918415) B918415
theorem B1453931 : Blo 642303 1453931 := bstep (se 1 (by rfl) ⟨1090448, by rfl⟩ : syracuseStep 1453931 = 2180897) B2180897
theorem B1453985 : Blo 642303 1453985 := bstep (se 2 (by rfl) ⟨545244, by rfl⟩ : syracuseStep 1453985 = 1090489) B1090489
theorem B2174903 : Blo 642303 2174903 := bstep (se 1 (by rfl) ⟨1631177, by rfl⟩ : syracuseStep 2174903 = 3262355) B3262355
theorem B1224713 : Blo 642303 1224713 := bstep (se 2 (by rfl) ⟨459267, by rfl⟩ : syracuseStep 1224713 = 918535) B918535
theorem B2175497 : Blo 642303 2175497 := bstep (se 2 (by rfl) ⟨815811, by rfl⟩ : syracuseStep 2175497 = 1631623) B1631623
theorem B963503 : Blo 642303 963503 := bstep (se 1 (by rfl) ⟨722627, by rfl⟩ : syracuseStep 963503 = 1445255) B1445255
theorem B963593 : Blo 642303 963593 := bstep (se 2 (by rfl) ⟨361347, by rfl⟩ : syracuseStep 963593 = 722695) B722695
theorem B963623 : Blo 642303 963623 := bstep (se 1 (by rfl) ⟨722717, by rfl⟩ : syracuseStep 963623 = 1445435) B1445435
theorem B963707 : Blo 642303 963707 := bstep (se 1 (by rfl) ⟨722780, by rfl⟩ : syracuseStep 963707 = 1445561) B1445561
theorem B963833 : Blo 642303 963833 := bstep (se 2 (by rfl) ⟨361437, by rfl⟩ : syracuseStep 963833 = 722875) B722875
theorem B963935 : Blo 642303 963935 := bstep (se 1 (by rfl) ⟨722951, by rfl⟩ : syracuseStep 963935 = 1445903) B1445903
theorem B2176361 : Blo 642303 2176361 := bstep (se 2 (by rfl) ⟨816135, by rfl⟩ : syracuseStep 2176361 = 1632271) B1632271
theorem B963947 : Blo 642303 963947 := bstep (se 1 (by rfl) ⟨722960, by rfl⟩ : syracuseStep 963947 = 1445921) B1445921
theorem B1226171 : Blo 642303 1226171 := bstep (se 1 (by rfl) ⟨919628, by rfl⟩ : syracuseStep 1226171 = 1839257) B1839257
theorem B3257819 : Blo 642303 3257819 := bstep (se 1 (by rfl) ⟨2443364, by rfl⟩ : syracuseStep 3257819 = 4886729) B4886729
theorem B10597877 : Blo 642303 10597877 := bstep (se 5 (by rfl) ⟨496775, by rfl⟩ : syracuseStep 10597877 = 993551) B993551
theorem B964175 : Blo 642303 964175 := bstep (se 1 (by rfl) ⟨723131, by rfl⟩ : syracuseStep 964175 = 1446263) B1446263
theorem B2438855 : Blo 642303 2438855 := bstep (se 1 (by rfl) ⟨1829141, by rfl⟩ : syracuseStep 2438855 = 3658283) B3658283
theorem B964295 : Blo 642303 964295 := bstep (se 1 (by rfl) ⟨723221, by rfl⟩ : syracuseStep 964295 = 1446443) B1446443
theorem B964457 : Blo 642303 964457 := bstep (se 2 (by rfl) ⟨361671, by rfl⟩ : syracuseStep 964457 = 723343) B723343
theorem B1226603 : Blo 642303 1226603 := bstep (se 1 (by rfl) ⟨919952, by rfl⟩ : syracuseStep 1226603 = 1839905) B1839905
theorem B1226657 : Blo 642303 1226657 := bstep (se 2 (by rfl) ⟨459996, by rfl⟩ : syracuseStep 1226657 = 919993) B919993
theorem B964535 : Blo 642303 964535 := bstep (se 1 (by rfl) ⟨723401, by rfl⟩ : syracuseStep 964535 = 1446803) B1446803
theorem B2176955 : Blo 642303 2176955 := bstep (se 1 (by rfl) ⟨1632716, by rfl⟩ : syracuseStep 2176955 = 3265433) B3265433
theorem B3258305 : Blo 642303 3258305 := bstep (se 2 (by rfl) ⟨1221864, by rfl⟩ : syracuseStep 3258305 = 2443729) B2443729
theorem B964571 : Blo 642303 964571 := bstep (se 1 (by rfl) ⟨723428, by rfl⟩ : syracuseStep 964571 = 1446857) B1446857
theorem B965039 : Blo 642303 965039 := bstep (se 1 (by rfl) ⟨723779, by rfl⟩ : syracuseStep 965039 = 1447559) B1447559
theorem B965129 : Blo 642303 965129 := bstep (se 2 (by rfl) ⟨361923, by rfl⟩ : syracuseStep 965129 = 723847) B723847
theorem B965159 : Blo 642303 965159 := bstep (se 1 (by rfl) ⟨723869, by rfl⟩ : syracuseStep 965159 = 1447739) B1447739
theorem B965243 : Blo 642303 965243 := bstep (se 1 (by rfl) ⟨723932, by rfl⟩ : syracuseStep 965243 = 1447865) B1447865
theorem B2439827 : Blo 642303 2439827 := bstep (se 1 (by rfl) ⟨1829870, by rfl⟩ : syracuseStep 2439827 = 3659741) B3659741
theorem B965369 : Blo 642303 965369 := bstep (se 2 (by rfl) ⟨362013, by rfl⟩ : syracuseStep 965369 = 724027) B724027
theorem B965471 : Blo 642303 965471 := bstep (se 1 (by rfl) ⟨724103, by rfl⟩ : syracuseStep 965471 = 1448207) B1448207
theorem B965483 : Blo 642303 965483 := bstep (se 1 (by rfl) ⟨724112, by rfl⟩ : syracuseStep 965483 = 1448225) B1448225
theorem B1162297 : Blo 642303 1162297 := bstep (se 2 (by rfl) ⟨435861, by rfl⟩ : syracuseStep 1162297 = 871723) B871723
theorem B965711 : Blo 642303 965711 := bstep (se 1 (by rfl) ⟨724283, by rfl⟩ : syracuseStep 965711 = 1448567) B1448567
theorem B965831 : Blo 642303 965831 := bstep (se 1 (by rfl) ⟨724373, by rfl⟩ : syracuseStep 965831 = 1448747) B1448747
theorem B1326431 : Blo 642303 1326431 := bstep (se 1 (by rfl) ⟨994823, by rfl⟩ : syracuseStep 1326431 = 1989647) B1989647
theorem B965993 : Blo 642303 965993 := bstep (se 2 (by rfl) ⟨362247, by rfl⟩ : syracuseStep 965993 = 724495) B724495
theorem B966071 : Blo 642303 966071 := bstep (se 1 (by rfl) ⟨724553, by rfl⟩ : syracuseStep 966071 = 1449107) B1449107
theorem B966107 : Blo 642303 966107 := bstep (se 1 (by rfl) ⟨724580, by rfl⟩ : syracuseStep 966107 = 1449161) B1449161
theorem B1162831 : Blo 642303 1162831 := bstep (se 1 (by rfl) ⟨872123, by rfl⟩ : syracuseStep 1162831 = 1744247) B1744247
theorem B2178683 : Blo 642303 2178683 := bstep (se 1 (by rfl) ⟨1634012, by rfl⟩ : syracuseStep 2178683 = 3268025) B3268025
theorem B2178845 : Blo 642303 2178845 := bstep (se 3 (by rfl) ⟨408533, by rfl⟩ : syracuseStep 2178845 = 817067) B817067
theorem B2604919 : Blo 642303 2604919 := bstep (se 1 (by rfl) ⟨1953689, by rfl⟩ : syracuseStep 2604919 = 3907379) B3907379
theorem B966575 : Blo 642303 966575 := bstep (se 1 (by rfl) ⟨724931, by rfl⟩ : syracuseStep 966575 = 1449863) B1449863
theorem B966665 : Blo 642303 966665 := bstep (se 2 (by rfl) ⟨362499, by rfl⟩ : syracuseStep 966665 = 724999) B724999
theorem B966695 : Blo 642303 966695 := bstep (se 1 (by rfl) ⟨725021, by rfl⟩ : syracuseStep 966695 = 1450043) B1450043
theorem B3620945 : Blo 642303 3620945 := bstep (se 2 (by rfl) ⟨1357854, by rfl⟩ : syracuseStep 3620945 = 2715709) B2715709
theorem B966779 : Blo 642303 966779 := bstep (se 1 (by rfl) ⟨725084, by rfl⟩ : syracuseStep 966779 = 1450169) B1450169
theorem B3260573 : Blo 642303 3260573 := bstep (se 3 (by rfl) ⟨611357, by rfl⟩ : syracuseStep 3260573 = 1222715) B1222715
theorem B966905 : Blo 642303 966905 := bstep (se 2 (by rfl) ⟨362589, by rfl⟩ : syracuseStep 966905 = 725179) B725179
theorem B171524405 : Blo 642303 171524405 := bstep (se 5 (by rfl) ⟨8040206, by rfl⟩ : syracuseStep 171524405 = 16080413) B16080413
theorem B5226839 : Blo 642303 5226839 := bstep (se 1 (by rfl) ⟨3920129, by rfl⟩ : syracuseStep 5226839 = 7840259) B7840259
theorem B967007 : Blo 642303 967007 := bstep (se 1 (by rfl) ⟨725255, by rfl⟩ : syracuseStep 967007 = 1450511) B1450511
theorem B967019 : Blo 642303 967019 := bstep (se 1 (by rfl) ⟨725264, by rfl⟩ : syracuseStep 967019 = 1450529) B1450529
theorem B1163681 : Blo 642303 1163681 := bstep (se 2 (by rfl) ⟨436380, by rfl⟩ : syracuseStep 1163681 = 872761) B872761
theorem B2179547 : Blo 642303 2179547 := bstep (se 1 (by rfl) ⟨1634660, by rfl⟩ : syracuseStep 2179547 = 3269321) B3269321
theorem B967247 : Blo 642303 967247 := bstep (se 1 (by rfl) ⟨725435, by rfl⟩ : syracuseStep 967247 = 1450871) B1450871
theorem B967367 : Blo 642303 967367 := bstep (se 1 (by rfl) ⟨725525, by rfl⟩ : syracuseStep 967367 = 1451051) B1451051
theorem B967529 : Blo 642303 967529 := bstep (se 2 (by rfl) ⟨362823, by rfl⟩ : syracuseStep 967529 = 725647) B725647
theorem B967607 : Blo 642303 967607 := bstep (se 1 (by rfl) ⟨725705, by rfl⟩ : syracuseStep 967607 = 1451411) B1451411
theorem B967643 : Blo 642303 967643 := bstep (se 1 (by rfl) ⟨725732, by rfl⟩ : syracuseStep 967643 = 1451465) B1451465
theorem B2606087 : Blo 642303 2606087 := bstep (se 1 (by rfl) ⟨1954565, by rfl⟩ : syracuseStep 2606087 = 3909131) B3909131
theorem B1033255 : Blo 642303 1033255 := bstep (se 1 (by rfl) ⟨774941, by rfl⟩ : syracuseStep 1033255 = 1549883) B1549883
theorem B2180249 : Blo 642303 2180249 := bstep (se 2 (by rfl) ⟨817593, by rfl⟩ : syracuseStep 2180249 = 1635187) B1635187
theorem B3261869 : Blo 642303 3261869 := bstep (se 3 (by rfl) ⟨611600, by rfl⟩ : syracuseStep 3261869 = 1223201) B1223201
theorem B968111 : Blo 642303 968111 := bstep (se 1 (by rfl) ⟨726083, by rfl⟩ : syracuseStep 968111 = 1452167) B1452167
theorem B968201 : Blo 642303 968201 := bstep (se 2 (by rfl) ⟨363075, by rfl⟩ : syracuseStep 968201 = 726151) B726151
theorem B3130919 : Blo 642303 3130919 := bstep (se 1 (by rfl) ⟨2348189, by rfl⟩ : syracuseStep 3130919 = 4696379) B4696379
theorem B968231 : Blo 642303 968231 := bstep (se 1 (by rfl) ⟨726173, by rfl⟩ : syracuseStep 968231 = 1452347) B1452347
theorem B968315 : Blo 642303 968315 := bstep (se 1 (by rfl) ⟨726236, by rfl⟩ : syracuseStep 968315 = 1452473) B1452473
theorem B4638347 : Blo 642303 4638347 := bstep (se 1 (by rfl) ⟨3478760, by rfl⟩ : syracuseStep 4638347 = 6957521) B6957521
theorem B6211217 : Blo 642303 6211217 := bstep (se 2 (by rfl) ⟨2329206, by rfl⟩ : syracuseStep 6211217 = 4658413) B4658413
theorem B968441 : Blo 642303 968441 := bstep (se 2 (by rfl) ⟨363165, by rfl⟩ : syracuseStep 968441 = 726331) B726331
theorem B968543 : Blo 642303 968543 := bstep (se 1 (by rfl) ⟨726407, by rfl⟩ : syracuseStep 968543 = 1452815) B1452815
theorem B968555 : Blo 642303 968555 := bstep (se 1 (by rfl) ⟨726416, by rfl⟩ : syracuseStep 968555 = 1452833) B1452833
theorem B5883911 : Blo 642303 5883911 := bstep (se 1 (by rfl) ⟨4412933, by rfl⟩ : syracuseStep 5883911 = 8825867) B8825867
theorem B772135 : Blo 642303 772135 := bstep (se 1 (by rfl) ⟨579101, by rfl⟩ : syracuseStep 772135 = 1158203) B1158203
theorem B968783 : Blo 642303 968783 := bstep (se 1 (by rfl) ⟨726587, by rfl⟩ : syracuseStep 968783 = 1453175) B1453175
theorem B4638809 : Blo 642303 4638809 := bstep (se 2 (by rfl) ⟨1739553, by rfl⟩ : syracuseStep 4638809 = 3479107) B3479107
theorem B968903 : Blo 642303 968903 := bstep (se 1 (by rfl) ⟨726677, by rfl⟩ : syracuseStep 968903 = 1453355) B1453355
theorem B4639037 : Blo 642303 4639037 := bstep (se 3 (by rfl) ⟨869819, by rfl⟩ : syracuseStep 4639037 = 1739639) B1739639
theorem B969065 : Blo 642303 969065 := bstep (se 2 (by rfl) ⟨363399, by rfl⟩ : syracuseStep 969065 = 726799) B726799
theorem B969143 : Blo 642303 969143 := bstep (se 1 (by rfl) ⟨726857, by rfl⟩ : syracuseStep 969143 = 1453715) B1453715
theorem B969179 : Blo 642303 969179 := bstep (se 1 (by rfl) ⟨726884, by rfl⟩ : syracuseStep 969179 = 1453769) B1453769
theorem B8243693 : Blo 642303 8243693 := bstep (se 3 (by rfl) ⟨1545692, by rfl⟩ : syracuseStep 8243693 = 3091385) B3091385
theorem B2444215 : Blo 642303 2444215 := bstep (se 1 (by rfl) ⟨1833161, by rfl⟩ : syracuseStep 2444215 = 3666323) B3666323
theorem B3263489 : Blo 642303 3263489 := bstep (se 2 (by rfl) ⟨1223808, by rfl⟩ : syracuseStep 3263489 = 2447617) B2447617
theorem B1100839 : Blo 642303 1100839 := bstep (se 1 (by rfl) ⟨825629, by rfl⟩ : syracuseStep 1100839 = 1651259) B1651259
theorem B2477137 : Blo 642303 2477137 := bstep (se 2 (by rfl) ⟨928926, by rfl⟩ : syracuseStep 2477137 = 1857853) B1857853
theorem B9915671 : Blo 642303 9915671 := bstep (se 1 (by rfl) ⟨7436753, by rfl⟩ : syracuseStep 9915671 = 14873507) B14873507
theorem B642343 : Blo 642303 642343 := bstep (se 1 (by rfl) ⟨481757, by rfl⟩ : syracuseStep 642343 = 963515) B963515
theorem B642383 : Blo 642303 642383 := bstep (se 1 (by rfl) ⟨481787, by rfl⟩ : syracuseStep 642383 = 963575) B963575
theorem B642399 : Blo 642303 642399 := bstep (se 1 (by rfl) ⟨481799, by rfl⟩ : syracuseStep 642399 = 963599) B963599
theorem B707935 : Blo 642303 707935 := bstep (se 1 (by rfl) ⟨530951, by rfl⟩ : syracuseStep 707935 = 1061903) B1061903
theorem B642427 : Blo 642303 642427 := bstep (se 1 (by rfl) ⟨481820, by rfl⟩ : syracuseStep 642427 = 963641) B963641
theorem B2444687 : Blo 642303 2444687 := bstep (se 1 (by rfl) ⟨1833515, by rfl⟩ : syracuseStep 2444687 = 3667031) B3667031
theorem B642479 : Blo 642303 642479 := bstep (se 1 (by rfl) ⟨481859, by rfl⟩ : syracuseStep 642479 = 963719) B963719
theorem B642503 : Blo 642303 642503 := bstep (se 1 (by rfl) ⟨481877, by rfl⟩ : syracuseStep 642503 = 963755) B963755
theorem B642523 : Blo 642303 642523 := bstep (se 1 (by rfl) ⟨481892, by rfl⟩ : syracuseStep 642523 = 963785) B963785
theorem B642599 : Blo 642303 642599 := bstep (se 1 (by rfl) ⟨481949, by rfl⟩ : syracuseStep 642599 = 963899) B963899
theorem B642639 : Blo 642303 642639 := bstep (se 1 (by rfl) ⟨481979, by rfl⟩ : syracuseStep 642639 = 963959) B963959
theorem B4116055 : Blo 642303 4116055 := bstep (se 1 (by rfl) ⟨3087041, by rfl⟩ : syracuseStep 4116055 = 6174083) B6174083
theorem B642655 : Blo 642303 642655 := bstep (se 1 (by rfl) ⟨481991, by rfl⟩ : syracuseStep 642655 = 963983) B963983
theorem B642683 : Blo 642303 642683 := bstep (se 1 (by rfl) ⟨482012, by rfl⟩ : syracuseStep 642683 = 964025) B964025
theorem B35245691 : Blo 642303 35245691 := bstep (se 1 (by rfl) ⟨26434268, by rfl⟩ : syracuseStep 35245691 = 52868537) B52868537
theorem B642735 : Blo 642303 642735 := bstep (se 1 (by rfl) ⟨482051, by rfl⟩ : syracuseStep 642735 = 964103) B964103
theorem B2477753 : Blo 642303 2477753 := bstep (se 2 (by rfl) ⟨929157, by rfl⟩ : syracuseStep 2477753 = 1858315) B1858315
theorem B642759 : Blo 642303 642759 := bstep (se 1 (by rfl) ⟨482069, by rfl⟩ : syracuseStep 642759 = 964139) B964139
theorem B2936519 : Blo 642303 2936519 := bstep (se 1 (by rfl) ⟨2202389, by rfl⟩ : syracuseStep 2936519 = 4404779) B4404779
theorem B642779 : Blo 642303 642779 := bstep (se 1 (by rfl) ⟨482084, by rfl⟩ : syracuseStep 642779 = 964169) B964169
theorem B642855 : Blo 642303 642855 := bstep (se 1 (by rfl) ⟨482141, by rfl⟩ : syracuseStep 642855 = 964283) B964283
theorem B3264299 : Blo 642303 3264299 := bstep (se 1 (by rfl) ⟨2448224, by rfl⟩ : syracuseStep 3264299 = 4896449) B4896449
theorem B642895 : Blo 642303 642895 := bstep (se 1 (by rfl) ⟨482171, by rfl⟩ : syracuseStep 642895 = 964343) B964343
theorem B642911 : Blo 642303 642911 := bstep (se 1 (by rfl) ⟨482183, by rfl⟩ : syracuseStep 642911 = 964367) B964367
theorem B642939 : Blo 642303 642939 := bstep (se 1 (by rfl) ⟨482204, by rfl⟩ : syracuseStep 642939 = 964409) B964409
theorem B2936737 : Blo 642303 2936737 := bstep (se 2 (by rfl) ⟨1101276, by rfl⟩ : syracuseStep 2936737 = 2202553) B2202553
theorem B642991 : Blo 642303 642991 := bstep (se 1 (by rfl) ⟨482243, by rfl⟩ : syracuseStep 642991 = 964487) B964487
theorem B643015 : Blo 642303 643015 := bstep (se 1 (by rfl) ⟨482261, by rfl⟩ : syracuseStep 643015 = 964523) B964523
theorem B643035 : Blo 642303 643035 := bstep (se 1 (by rfl) ⟨482276, by rfl⟩ : syracuseStep 643035 = 964553) B964553
theorem B1855495 : Blo 642303 1855495 := bstep (se 1 (by rfl) ⟨1391621, by rfl⟩ : syracuseStep 1855495 = 2783243) B2783243
theorem B643111 : Blo 642303 643111 := bstep (se 1 (by rfl) ⟨482333, by rfl⟩ : syracuseStep 643111 = 964667) B964667
theorem B643151 : Blo 642303 643151 := bstep (se 1 (by rfl) ⟨482363, by rfl⟩ : syracuseStep 643151 = 964727) B964727
theorem B643167 : Blo 642303 643167 := bstep (se 1 (by rfl) ⟨482375, by rfl⟩ : syracuseStep 643167 = 964751) B964751
theorem B643195 : Blo 642303 643195 := bstep (se 1 (by rfl) ⟨482396, by rfl⟩ : syracuseStep 643195 = 964793) B964793
theorem B7327907 : Blo 642303 7327907 := bstep (se 1 (by rfl) ⟨5495930, by rfl⟩ : syracuseStep 7327907 = 10991861) B10991861
theorem B643247 : Blo 642303 643247 := bstep (se 1 (by rfl) ⟨482435, by rfl⟩ : syracuseStep 643247 = 964871) B964871
theorem B643271 : Blo 642303 643271 := bstep (se 1 (by rfl) ⟨482453, by rfl⟩ : syracuseStep 643271 = 964907) B964907
theorem B643291 : Blo 642303 643291 := bstep (se 1 (by rfl) ⟨482468, by rfl⟩ : syracuseStep 643291 = 964937) B964937
theorem B643367 : Blo 642303 643367 := bstep (se 1 (by rfl) ⟨482525, by rfl⟩ : syracuseStep 643367 = 965051) B965051
theorem B643407 : Blo 642303 643407 := bstep (se 1 (by rfl) ⟨482555, by rfl⟩ : syracuseStep 643407 = 965111) B965111
theorem B643423 : Blo 642303 643423 := bstep (se 1 (by rfl) ⟨482567, by rfl⟩ : syracuseStep 643423 = 965135) B965135
theorem B2445673 : Blo 642303 2445673 := bstep (se 2 (by rfl) ⟨917127, by rfl⟩ : syracuseStep 2445673 = 1834255) B1834255
theorem B643451 : Blo 642303 643451 := bstep (se 1 (by rfl) ⟨482588, by rfl⟩ : syracuseStep 643451 = 965177) B965177
theorem B643503 : Blo 642303 643503 := bstep (se 1 (by rfl) ⟨482627, by rfl⟩ : syracuseStep 643503 = 965255) B965255
theorem B643527 : Blo 642303 643527 := bstep (se 1 (by rfl) ⟨482645, by rfl⟩ : syracuseStep 643527 = 965291) B965291
theorem B643547 : Blo 642303 643547 := bstep (se 1 (by rfl) ⟨482660, by rfl⟩ : syracuseStep 643547 = 965321) B965321
theorem B643623 : Blo 642303 643623 := bstep (se 1 (by rfl) ⟨482717, by rfl⟩ : syracuseStep 643623 = 965435) B965435
theorem B643663 : Blo 642303 643663 := bstep (se 1 (by rfl) ⟨482747, by rfl⟩ : syracuseStep 643663 = 965495) B965495
theorem B643679 : Blo 642303 643679 := bstep (se 1 (by rfl) ⟨482759, by rfl⟩ : syracuseStep 643679 = 965519) B965519
theorem B643707 : Blo 642303 643707 := bstep (se 1 (by rfl) ⟨482780, by rfl⟩ : syracuseStep 643707 = 965561) B965561
theorem B2445947 : Blo 642303 2445947 := bstep (se 1 (by rfl) ⟨1834460, by rfl⟩ : syracuseStep 2445947 = 3668921) B3668921
theorem B1626763 : Blo 642303 1626763 := bstep (se 1 (by rfl) ⟨1220072, by rfl⟩ : syracuseStep 1626763 = 2440145) B2440145
theorem B643759 : Blo 642303 643759 := bstep (se 1 (by rfl) ⟨482819, by rfl⟩ : syracuseStep 643759 = 965639) B965639
theorem B643783 : Blo 642303 643783 := bstep (se 1 (by rfl) ⟨482837, by rfl⟩ : syracuseStep 643783 = 965675) B965675
theorem B4707017 : Blo 642303 4707017 := bstep (se 2 (by rfl) ⟨1765131, by rfl⟩ : syracuseStep 4707017 = 3530263) B3530263
theorem B643803 : Blo 642303 643803 := bstep (se 1 (by rfl) ⟨482852, by rfl⟩ : syracuseStep 643803 = 965705) B965705
theorem B643879 : Blo 642303 643879 := bstep (se 1 (by rfl) ⟨482909, by rfl⟩ : syracuseStep 643879 = 965819) B965819
theorem B61985587 : Blo 642303 61985587 := bstep (se 1 (by rfl) ⟨46489190, by rfl⟩ : syracuseStep 61985587 = 92978381) B92978381
theorem B2315081 : Blo 642303 2315081 := bstep (se 2 (by rfl) ⟨868155, by rfl⟩ : syracuseStep 2315081 = 1736311) B1736311
theorem B643919 : Blo 642303 643919 := bstep (se 1 (by rfl) ⟨482939, by rfl⟩ : syracuseStep 643919 = 965879) B965879
theorem B643935 : Blo 642303 643935 := bstep (se 1 (by rfl) ⟨482951, by rfl⟩ : syracuseStep 643935 = 965903) B965903
theorem B643963 : Blo 642303 643963 := bstep (se 1 (by rfl) ⟨482972, by rfl⟩ : syracuseStep 643963 = 965945) B965945
theorem B644015 : Blo 642303 644015 := bstep (se 1 (by rfl) ⟨483011, by rfl⟩ : syracuseStep 644015 = 966023) B966023
theorem B1627067 : Blo 642303 1627067 := bstep (se 1 (by rfl) ⟨1220300, by rfl⟩ : syracuseStep 1627067 = 2440601) B2440601
theorem B644039 : Blo 642303 644039 := bstep (se 1 (by rfl) ⟨483029, by rfl⟩ : syracuseStep 644039 = 966059) B966059
theorem B644059 : Blo 642303 644059 := bstep (se 1 (by rfl) ⟨483044, by rfl⟩ : syracuseStep 644059 = 966089) B966089
theorem B3724289 : Blo 642303 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B2642959 : Blo 642303 2642959 := bstep (se 1 (by rfl) ⟨1982219, by rfl⟩ : syracuseStep 2642959 = 3964439) B3964439
theorem B644135 : Blo 642303 644135 := bstep (se 1 (by rfl) ⟨483101, by rfl⟩ : syracuseStep 644135 = 966203) B966203
theorem B644175 : Blo 642303 644175 := bstep (se 1 (by rfl) ⟨483131, by rfl⟩ : syracuseStep 644175 = 966263) B966263
theorem B644191 : Blo 642303 644191 := bstep (se 1 (by rfl) ⟨483143, by rfl⟩ : syracuseStep 644191 = 966287) B966287
theorem B644219 : Blo 642303 644219 := bstep (se 1 (by rfl) ⟨483164, by rfl⟩ : syracuseStep 644219 = 966329) B966329
theorem B644271 : Blo 642303 644271 := bstep (se 1 (by rfl) ⟨483203, by rfl⟩ : syracuseStep 644271 = 966407) B966407
theorem B644295 : Blo 642303 644295 := bstep (se 1 (by rfl) ⟨483221, by rfl⟩ : syracuseStep 644295 = 966443) B966443
theorem B644315 : Blo 642303 644315 := bstep (se 1 (by rfl) ⟨483236, by rfl⟩ : syracuseStep 644315 = 966473) B966473
theorem B644391 : Blo 642303 644391 := bstep (se 1 (by rfl) ⟨483293, by rfl⟩ : syracuseStep 644391 = 966587) B966587
theorem B644431 : Blo 642303 644431 := bstep (se 1 (by rfl) ⟨483323, by rfl⟩ : syracuseStep 644431 = 966647) B966647
theorem B644447 : Blo 642303 644447 := bstep (se 1 (by rfl) ⟨483335, by rfl⟩ : syracuseStep 644447 = 966671) B966671
theorem B644475 : Blo 642303 644475 := bstep (se 1 (by rfl) ⟨483356, by rfl⟩ : syracuseStep 644475 = 966713) B966713
theorem B644527 : Blo 642303 644527 := bstep (se 1 (by rfl) ⟨483395, by rfl⟩ : syracuseStep 644527 = 966791) B966791
theorem B644551 : Blo 642303 644551 := bstep (se 1 (by rfl) ⟨483413, by rfl⟩ : syracuseStep 644551 = 966827) B966827
theorem B4642267 : Blo 642303 4642267 := bstep (se 1 (by rfl) ⟨3481700, by rfl⟩ : syracuseStep 4642267 = 6963401) B6963401
theorem B644571 : Blo 642303 644571 := bstep (se 1 (by rfl) ⟨483428, by rfl⟩ : syracuseStep 644571 = 966857) B966857
theorem B644647 : Blo 642303 644647 := bstep (se 1 (by rfl) ⟨483485, by rfl⟩ : syracuseStep 644647 = 966971) B966971
theorem B644687 : Blo 642303 644687 := bstep (se 1 (by rfl) ⟨483515, by rfl⟩ : syracuseStep 644687 = 967031) B967031
theorem B775759 : Blo 642303 775759 := bstep (se 1 (by rfl) ⟨581819, by rfl⟩ : syracuseStep 775759 = 1163639) B1163639
theorem B644703 : Blo 642303 644703 := bstep (se 1 (by rfl) ⟨483527, by rfl⟩ : syracuseStep 644703 = 967055) B967055
theorem B644731 : Blo 642303 644731 := bstep (se 1 (by rfl) ⟨483548, by rfl⟩ : syracuseStep 644731 = 967097) B967097
theorem B644783 : Blo 642303 644783 := bstep (se 1 (by rfl) ⟨483587, by rfl⟩ : syracuseStep 644783 = 967175) B967175
theorem B1627847 : Blo 642303 1627847 := bstep (se 1 (by rfl) ⟨1220885, by rfl⟩ : syracuseStep 1627847 = 2441771) B2441771
theorem B644807 : Blo 642303 644807 := bstep (se 1 (by rfl) ⟨483605, by rfl⟩ : syracuseStep 644807 = 967211) B967211
theorem B644827 : Blo 642303 644827 := bstep (se 1 (by rfl) ⟨483620, by rfl⟩ : syracuseStep 644827 = 967241) B967241
theorem B1627897 : Blo 642303 1627897 := bstep (se 2 (by rfl) ⟨610461, by rfl⟩ : syracuseStep 1627897 = 1220923) B1220923
theorem B3102457 : Blo 642303 3102457 := bstep (se 2 (by rfl) ⟨1163421, by rfl⟩ : syracuseStep 3102457 = 2326843) B2326843
theorem B644903 : Blo 642303 644903 := bstep (se 1 (by rfl) ⟨483677, by rfl⟩ : syracuseStep 644903 = 967355) B967355
theorem B644943 : Blo 642303 644943 := bstep (se 1 (by rfl) ⟨483707, by rfl⟩ : syracuseStep 644943 = 967415) B967415
theorem B644959 : Blo 642303 644959 := bstep (se 1 (by rfl) ⟨483719, by rfl⟩ : syracuseStep 644959 = 967439) B967439
theorem B37738349 : Blo 642303 37738349 := bstep (se 3 (by rfl) ⟨7075940, by rfl⟩ : syracuseStep 37738349 = 14151881) B14151881
theorem B644987 : Blo 642303 644987 := bstep (se 1 (by rfl) ⟨483740, by rfl⟩ : syracuseStep 644987 = 967481) B967481
theorem B645039 : Blo 642303 645039 := bstep (se 1 (by rfl) ⟨483779, by rfl⟩ : syracuseStep 645039 = 967559) B967559
theorem B645063 : Blo 642303 645063 := bstep (se 1 (by rfl) ⟨483797, by rfl⟩ : syracuseStep 645063 = 967595) B967595
theorem B645083 : Blo 642303 645083 := bstep (se 1 (by rfl) ⟨483812, by rfl⟩ : syracuseStep 645083 = 967625) B967625
theorem B3266567 : Blo 642303 3266567 := bstep (se 1 (by rfl) ⟨2449925, by rfl⟩ : syracuseStep 3266567 = 4899851) B4899851
theorem B29677589 : Blo 642303 29677589 := bstep (se 6 (by rfl) ⟨695568, by rfl⟩ : syracuseStep 29677589 = 1391137) B1391137
theorem B645159 : Blo 642303 645159 := bstep (se 1 (by rfl) ⟨483869, by rfl⟩ : syracuseStep 645159 = 967739) B967739
theorem B645199 : Blo 642303 645199 := bstep (se 1 (by rfl) ⟨483899, by rfl⟩ : syracuseStep 645199 = 967799) B967799
theorem B645215 : Blo 642303 645215 := bstep (se 1 (by rfl) ⟨483911, by rfl⟩ : syracuseStep 645215 = 967823) B967823
theorem B645243 : Blo 642303 645243 := bstep (se 1 (by rfl) ⟨483932, by rfl⟩ : syracuseStep 645243 = 967865) B967865
theorem B645295 : Blo 642303 645295 := bstep (se 1 (by rfl) ⟨483971, by rfl⟩ : syracuseStep 645295 = 967943) B967943
theorem B645319 : Blo 642303 645319 := bstep (se 1 (by rfl) ⟨483989, by rfl⟩ : syracuseStep 645319 = 967979) B967979
theorem B645339 : Blo 642303 645339 := bstep (se 1 (by rfl) ⟨484004, by rfl⟩ : syracuseStep 645339 = 968009) B968009
theorem B645415 : Blo 642303 645415 := bstep (se 1 (by rfl) ⟨484061, by rfl⟩ : syracuseStep 645415 = 968123) B968123
theorem B645455 : Blo 642303 645455 := bstep (se 1 (by rfl) ⟨484091, by rfl⟩ : syracuseStep 645455 = 968183) B968183
theorem B645471 : Blo 642303 645471 := bstep (se 1 (by rfl) ⟨484103, by rfl⟩ : syracuseStep 645471 = 968207) B968207
theorem B645499 : Blo 642303 645499 := bstep (se 1 (by rfl) ⟨484124, by rfl⟩ : syracuseStep 645499 = 968249) B968249
theorem B1956221 : Blo 642303 1956221 := bstep (se 3 (by rfl) ⟨366791, by rfl⟩ : syracuseStep 1956221 = 733583) B733583
theorem B1628545 : Blo 642303 1628545 := bstep (se 2 (by rfl) ⟨610704, by rfl⟩ : syracuseStep 1628545 = 1221409) B1221409
theorem B645551 : Blo 642303 645551 := bstep (se 1 (by rfl) ⟨484163, by rfl⟩ : syracuseStep 645551 = 968327) B968327
theorem B645575 : Blo 642303 645575 := bstep (se 1 (by rfl) ⟨484181, by rfl⟩ : syracuseStep 645575 = 968363) B968363
theorem B645595 : Blo 642303 645595 := bstep (se 1 (by rfl) ⟨484196, by rfl⟩ : syracuseStep 645595 = 968393) B968393
theorem B3267053 : Blo 642303 3267053 := bstep (se 3 (by rfl) ⟨612572, by rfl⟩ : syracuseStep 3267053 = 1225145) B1225145
theorem B645671 : Blo 642303 645671 := bstep (se 1 (by rfl) ⟨484253, by rfl⟩ : syracuseStep 645671 = 968507) B968507
theorem B645711 : Blo 642303 645711 := bstep (se 1 (by rfl) ⟨484283, by rfl⟩ : syracuseStep 645711 = 968567) B968567
theorem B645727 : Blo 642303 645727 := bstep (se 1 (by rfl) ⟨484295, by rfl⟩ : syracuseStep 645727 = 968591) B968591
theorem B645755 : Blo 642303 645755 := bstep (se 1 (by rfl) ⟨484316, by rfl⟩ : syracuseStep 645755 = 968633) B968633
theorem B645807 : Blo 642303 645807 := bstep (se 1 (by rfl) ⟨484355, by rfl⟩ : syracuseStep 645807 = 968711) B968711
theorem B645831 : Blo 642303 645831 := bstep (se 1 (by rfl) ⟨484373, by rfl⟩ : syracuseStep 645831 = 968747) B968747
theorem B4905683 : Blo 642303 4905683 := bstep (se 1 (by rfl) ⟨3679262, by rfl⟩ : syracuseStep 4905683 = 7358525) B7358525
theorem B645851 : Blo 642303 645851 := bstep (se 1 (by rfl) ⟨484388, by rfl⟩ : syracuseStep 645851 = 968777) B968777
theorem B645927 : Blo 642303 645927 := bstep (se 1 (by rfl) ⟨484445, by rfl⟩ : syracuseStep 645927 = 968891) B968891
theorem B645967 : Blo 642303 645967 := bstep (se 1 (by rfl) ⟨484475, by rfl⟩ : syracuseStep 645967 = 968951) B968951
theorem B645983 : Blo 642303 645983 := bstep (se 1 (by rfl) ⟨484487, by rfl⟩ : syracuseStep 645983 = 968975) B968975
theorem B646011 : Blo 642303 646011 := bstep (se 1 (by rfl) ⟨484508, by rfl⟩ : syracuseStep 646011 = 969017) B969017
theorem B646063 : Blo 642303 646063 := bstep (se 1 (by rfl) ⟨484547, by rfl⟩ : syracuseStep 646063 = 969095) B969095
theorem B646087 : Blo 642303 646087 := bstep (se 1 (by rfl) ⟨484565, by rfl⟩ : syracuseStep 646087 = 969131) B969131
theorem B646107 : Blo 642303 646107 := bstep (se 1 (by rfl) ⟨484580, by rfl⟩ : syracuseStep 646107 = 969161) B969161
theorem B3103763 : Blo 642303 3103763 := bstep (se 1 (by rfl) ⟨2327822, by rfl⟩ : syracuseStep 3103763 = 4655645) B4655645
theorem B646183 : Blo 642303 646183 := bstep (se 1 (by rfl) ⟨484637, by rfl⟩ : syracuseStep 646183 = 969275) B969275
theorem B646223 : Blo 642303 646223 := bstep (se 1 (by rfl) ⟨484667, by rfl⟩ : syracuseStep 646223 = 969335) B969335
theorem B646239 : Blo 642303 646239 := bstep (se 1 (by rfl) ⟨484679, by rfl⟩ : syracuseStep 646239 = 969359) B969359
theorem B646267 : Blo 642303 646267 := bstep (se 1 (by rfl) ⟨484700, by rfl⟩ : syracuseStep 646267 = 969401) B969401
theorem B1629355 : Blo 642303 1629355 := bstep (se 1 (by rfl) ⟨1222016, by rfl⟩ : syracuseStep 1629355 = 2444033) B2444033
theorem B3267863 : Blo 642303 3267863 := bstep (se 1 (by rfl) ⟨2450897, by rfl⟩ : syracuseStep 3267863 = 4901795) B4901795
theorem B3661199 : Blo 642303 3661199 := bstep (se 1 (by rfl) ⟨2745899, by rfl⟩ : syracuseStep 3661199 = 5491799) B5491799
theorem B1629659 : Blo 642303 1629659 := bstep (se 1 (by rfl) ⟨1222244, by rfl⟩ : syracuseStep 1629659 = 2444489) B2444489
theorem B8380037 : Blo 642303 8380037 := bstep (se 4 (by rfl) ⟨785628, by rfl⟩ : syracuseStep 8380037 = 1571257) B1571257
theorem B1302265 : Blo 642303 1302265 := bstep (se 2 (by rfl) ⟨488349, by rfl⟩ : syracuseStep 1302265 = 976699) B976699
theorem B15065149 : Blo 642303 15065149 := bstep (se 3 (by rfl) ⟨2824715, by rfl⟩ : syracuseStep 15065149 = 5649431) B5649431
theorem B8380493 : Blo 642303 8380493 := bstep (se 3 (by rfl) ⟨1571342, by rfl⟩ : syracuseStep 8380493 = 3142685) B3142685
theorem B2449561 : Blo 642303 2449561 := bstep (se 2 (by rfl) ⟨918585, by rfl⟩ : syracuseStep 2449561 = 1837171) B1837171
theorem B5595299 : Blo 642303 5595299 := bstep (se 1 (by rfl) ⟨4196474, by rfl⟩ : syracuseStep 5595299 = 8392949) B8392949
theorem B1302971 : Blo 642303 1302971 := bstep (se 1 (by rfl) ⟨977228, by rfl⟩ : syracuseStep 1302971 = 1954457) B1954457
theorem B2449865 : Blo 642303 2449865 := bstep (se 2 (by rfl) ⟨918699, by rfl⟩ : syracuseStep 2449865 = 1837399) B1837399
theorem B2744891 : Blo 642303 2744891 := bstep (se 1 (by rfl) ⟨2058668, by rfl⟩ : syracuseStep 2744891 = 4117337) B4117337
theorem B3269483 : Blo 642303 3269483 := bstep (se 1 (by rfl) ⟨2452112, by rfl⟩ : syracuseStep 3269483 = 4904225) B4904225
theorem B1631137 : Blo 642303 1631137 := bstep (se 2 (by rfl) ⟨611676, by rfl⟩ : syracuseStep 1631137 = 1223353) B1223353
theorem B2450351 : Blo 642303 2450351 := bstep (se 1 (by rfl) ⟨1837763, by rfl⟩ : syracuseStep 2450351 = 3675527) B3675527
theorem B2319853 : Blo 642303 2319853 := bstep (se 3 (by rfl) ⟨434972, by rfl⟩ : syracuseStep 2319853 = 869945) B869945
theorem B3270131 : Blo 642303 3270131 := bstep (se 1 (by rfl) ⟨2452598, by rfl⟩ : syracuseStep 3270131 = 4905197) B4905197
theorem B10610777 : Blo 642303 10610777 := bstep (se 2 (by rfl) ⟨3979041, by rfl⟩ : syracuseStep 10610777 = 7958083) B7958083
theorem B813179 : Blo 642303 813179 := bstep (se 1 (by rfl) ⟨609884, by rfl⟩ : syracuseStep 813179 = 1219769) B1219769
theorem B2451977 : Blo 642303 2451977 := bstep (se 2 (by rfl) ⟨919491, by rfl⟩ : syracuseStep 2451977 = 1838983) B1838983
theorem B3271427 : Blo 642303 3271427 := bstep (se 1 (by rfl) ⟨2453570, by rfl⟩ : syracuseStep 3271427 = 4907141) B4907141
theorem B2059283 : Blo 642303 2059283 := bstep (se 1 (by rfl) ⟨1544462, by rfl⟩ : syracuseStep 2059283 = 3088925) B3088925
theorem B1830269 : Blo 642303 1830269 := bstep (se 3 (by rfl) ⟨343175, by rfl⟩ : syracuseStep 1830269 = 686351) B686351
theorem B2485633 : Blo 642303 2485633 := bstep (se 2 (by rfl) ⟨932112, by rfl⟩ : syracuseStep 2485633 = 1864225) B1864225
theorem B1633679 : Blo 642303 1633679 := bstep (se 1 (by rfl) ⟨1225259, by rfl⟩ : syracuseStep 1633679 = 2450519) B2450519
theorem B1961671 : Blo 642303 1961671 := bstep (se 1 (by rfl) ⟨1471253, by rfl⟩ : syracuseStep 1961671 = 2942507) B2942507
theorem B1634003 : Blo 642303 1634003 := bstep (se 1 (by rfl) ⟨1225502, by rfl⟩ : syracuseStep 1634003 = 2451005) B2451005
theorem B1044407 : Blo 642303 1044407 := bstep (se 1 (by rfl) ⟨783305, by rfl⟩ : syracuseStep 1044407 = 1566611) B1566611
theorem B2453435 : Blo 642303 2453435 := bstep (se 1 (by rfl) ⟨1840076, by rfl⟩ : syracuseStep 2453435 = 3680153) B3680153
theorem B4649075 : Blo 642303 4649075 := bstep (se 1 (by rfl) ⟨3486806, by rfl⟩ : syracuseStep 4649075 = 6973613) B6973613
theorem B880763 : Blo 642303 880763 := bstep (se 1 (by rfl) ⟨660572, by rfl⟩ : syracuseStep 880763 = 1321145) B1321145
theorem B5501195 : Blo 642303 5501195 := bstep (se 1 (by rfl) ⟨4125896, by rfl⟩ : syracuseStep 5501195 = 8251793) B8251793
theorem B2322749 : Blo 642303 2322749 := bstep (se 3 (by rfl) ⟨435515, by rfl⟩ : syracuseStep 2322749 = 871031) B871031
theorem B13234691 : Blo 642303 13234691 := bstep (se 1 (by rfl) ⟨9926018, by rfl⟩ : syracuseStep 13234691 = 19852037) B19852037
theorem B35320529 : Blo 642303 35320529 := bstep (se 2 (by rfl) ⟨13245198, by rfl⟩ : syracuseStep 35320529 = 26490397) B26490397
theorem B13202189 : Blo 642303 13202189 := bstep (se 3 (by rfl) ⟨2475410, by rfl⟩ : syracuseStep 13202189 = 4950821) B4950821
theorem B1635167 : Blo 642303 1635167 := bstep (se 1 (by rfl) ⟨1226375, by rfl⟩ : syracuseStep 1635167 = 2452751) B2452751
theorem B2618219 : Blo 642303 2618219 := bstep (se 1 (by rfl) ⟨1963664, by rfl⟩ : syracuseStep 2618219 = 3927329) B3927329
theorem B1831841 : Blo 642303 1831841 := bstep (se 2 (by rfl) ⟨686940, by rfl⟩ : syracuseStep 1831841 = 1373881) B1373881
theorem B2094007 : Blo 642303 2094007 := bstep (se 1 (by rfl) ⟨1570505, by rfl⟩ : syracuseStep 2094007 = 3141011) B3141011
theorem B4879439 : Blo 642303 4879439 := bstep (se 1 (by rfl) ⟨3659579, by rfl⟩ : syracuseStep 4879439 = 7319159) B7319159
theorem B1832183 : Blo 642303 1832183 := bstep (se 1 (by rfl) ⟨1374137, by rfl⟩ : syracuseStep 1832183 = 2748275) B2748275
theorem B52917745 : Blo 642303 52917745 := bstep (se 2 (by rfl) ⟨19844154, by rfl⟩ : syracuseStep 52917745 = 39688309) B39688309
theorem B19854989 : Blo 642303 19854989 := bstep (se 3 (by rfl) ⟨3722810, by rfl⟩ : syracuseStep 19854989 = 7445621) B7445621
theorem B4191959 : Blo 642303 4191959 := bstep (se 1 (by rfl) ⟨3143969, by rfl⟩ : syracuseStep 4191959 = 6287939) B6287939
theorem B915305 : Blo 642303 915305 := bstep (se 2 (by rfl) ⟨343239, by rfl⟩ : syracuseStep 915305 = 686479) B686479
theorem B6944717 : Blo 642303 6944717 := bstep (se 3 (by rfl) ⟨1302134, by rfl⟩ : syracuseStep 6944717 = 2604269) B2604269
theorem B915419 : Blo 642303 915419 := bstep (se 1 (by rfl) ⟨686564, by rfl⟩ : syracuseStep 915419 = 1373129) B1373129
theorem B6977897 : Blo 642303 6977897 := bstep (se 2 (by rfl) ⟨2616711, by rfl⟩ : syracuseStep 6977897 = 5233423) B5233423
theorem B3668489 : Blo 642303 3668489 := bstep (se 2 (by rfl) ⟨1375683, by rfl⟩ : syracuseStep 3668489 = 2751367) B2751367
theorem B13367987 : Blo 642303 13367987 := bstep (se 1 (by rfl) ⟨10025990, by rfl⟩ : syracuseStep 13367987 = 20051981) B20051981
theorem B916319 : Blo 642303 916319 := bstep (se 1 (by rfl) ⟨687239, by rfl⟩ : syracuseStep 916319 = 1374479) B1374479
theorem B2325431 : Blo 642303 2325431 := bstep (se 1 (by rfl) ⟨1744073, by rfl⟩ : syracuseStep 2325431 = 3488147) B3488147
theorem B2751641 : Blo 642303 2751641 := bstep (se 2 (by rfl) ⟨1031865, by rfl⟩ : syracuseStep 2751641 = 2063731) B2063731
theorem B3669239 : Blo 642303 3669239 := bstep (se 1 (by rfl) ⟨2751929, by rfl⟩ : syracuseStep 3669239 = 5503859) B5503859
theorem B3669421 : Blo 642303 3669421 := bstep (se 3 (by rfl) ⟨688016, by rfl⟩ : syracuseStep 3669421 = 1376033) B1376033
theorem B181140941 : Blo 642303 181140941 := bstep (se 3 (by rfl) ⟨33963926, by rfl⟩ : syracuseStep 181140941 = 67927853) B67927853
theorem B1834483 : Blo 642303 1834483 := bstep (se 1 (by rfl) ⟨1375862, by rfl⟩ : syracuseStep 1834483 = 2751725) B2751725
theorem B1834825 : Blo 642303 1834825 := bstep (se 2 (by rfl) ⟨688059, by rfl⟩ : syracuseStep 1834825 = 1376119) B1376119
theorem B3669947 : Blo 642303 3669947 := bstep (se 1 (by rfl) ⟨2752460, by rfl⟩ : syracuseStep 3669947 = 5504921) B5504921
theorem B20086865 : Blo 642303 20086865 := bstep (se 2 (by rfl) ⟨7532574, by rfl⟩ : syracuseStep 20086865 = 15065149) B15065149
theorem B2097499 : Blo 642303 2097499 := bstep (se 1 (by rfl) ⟨1573124, by rfl⟩ : syracuseStep 2097499 = 3146249) B3146249
theorem B5505569 : Blo 642303 5505569 := bstep (se 2 (by rfl) ⟨2064588, by rfl⟩ : syracuseStep 5505569 = 4129177) B4129177
theorem B1376939 : Blo 642303 1376939 := bstep (se 1 (by rfl) ⟨1032704, by rfl⟩ : syracuseStep 1376939 = 2065409) B2065409
theorem B1737391 : Blo 642303 1737391 := bstep (se 1 (by rfl) ⟨1303043, by rfl⟩ : syracuseStep 1737391 = 2606087) B2606087
theorem B3670879 : Blo 642303 3670879 := bstep (se 1 (by rfl) ⟨2753159, by rfl⟩ : syracuseStep 3670879 = 5506319) B5506319
theorem B3474589 : Blo 642303 3474589 := bstep (se 3 (by rfl) ⟨651485, by rfl⟩ : syracuseStep 3474589 = 1302971) B1302971
theorem B35292509 : Blo 642303 35292509 := bstep (se 3 (by rfl) ⟨6617345, by rfl⟩ : syracuseStep 35292509 = 13234691) B13234691
theorem B3671405 : Blo 642303 3671405 := bstep (se 3 (by rfl) ⟨688388, by rfl⟩ : syracuseStep 3671405 = 1376777) B1376777
theorem B11142947 : Blo 642303 11142947 := bstep (se 1 (by rfl) ⟨8357210, by rfl⟩ : syracuseStep 11142947 = 16714421) B16714421
theorem B18876203 : Blo 642303 18876203 := bstep (se 1 (by rfl) ⟨14157152, by rfl⟩ : syracuseStep 18876203 = 28314305) B28314305
theorem B722767 : Blo 642303 722767 := bstep (se 1 (by rfl) ⟨542075, by rfl⟩ : syracuseStep 722767 = 1084151) B1084151
theorem B1378255 : Blo 642303 1378255 := bstep (se 1 (by rfl) ⟨1033691, by rfl⟩ : syracuseStep 1378255 = 2067383) B2067383
theorem B723163 : Blo 642303 723163 := bstep (se 1 (by rfl) ⟨542372, by rfl⟩ : syracuseStep 723163 = 1084745) B1084745
theorem B23497127 : Blo 642303 23497127 := bstep (se 1 (by rfl) ⟨17622845, by rfl⟩ : syracuseStep 23497127 = 35245691) B35245691
theorem B723451 : Blo 642303 723451 := bstep (se 1 (by rfl) ⟨542588, by rfl⟩ : syracuseStep 723451 = 1085177) B1085177
theorem B3541643 : Blo 642303 3541643 := bstep (se 1 (by rfl) ⟨2656232, by rfl⟩ : syracuseStep 3541643 = 5312465) B5312465
theorem B723631 : Blo 642303 723631 := bstep (se 1 (by rfl) ⟨542723, by rfl⟩ : syracuseStep 723631 = 1085447) B1085447
theorem B2951927 : Blo 642303 2951927 := bstep (se 1 (by rfl) ⟨2213945, by rfl⟩ : syracuseStep 2951927 = 4427891) B4427891
theorem B4885271 : Blo 642303 4885271 := bstep (se 1 (by rfl) ⟨3663953, by rfl⟩ : syracuseStep 4885271 = 7327907) B7327907
theorem B723919 : Blo 642303 723919 := bstep (se 1 (by rfl) ⟨542939, by rfl⟩ : syracuseStep 723919 = 1085879) B1085879
theorem B1543387 : Blo 642303 1543387 := bstep (se 1 (by rfl) ⟨1157540, by rfl⟩ : syracuseStep 1543387 = 2315081) B2315081
theorem B1084711 : Blo 642303 1084711 := bstep (se 1 (by rfl) ⟨813533, by rfl⟩ : syracuseStep 1084711 = 1627067) B1627067
theorem B724315 : Blo 642303 724315 := bstep (se 1 (by rfl) ⟨543236, by rfl⟩ : syracuseStep 724315 = 1086473) B1086473
theorem B724423 : Blo 642303 724423 := bstep (se 1 (by rfl) ⟨543317, by rfl⟩ : syracuseStep 724423 = 1086635) B1086635
theorem B1838675 : Blo 642303 1838675 := bstep (se 1 (by rfl) ⟨1379006, by rfl⟩ : syracuseStep 1838675 = 2758013) B2758013
theorem B1445471 : Blo 642303 1445471 := bstep (se 1 (by rfl) ⟨1084103, by rfl⟩ : syracuseStep 1445471 = 2168207) B2168207
theorem B1085231 : Blo 642303 1085231 := bstep (se 1 (by rfl) ⟨813923, by rfl⟩ : syracuseStep 1085231 = 1627847) B1627847
theorem B724783 : Blo 642303 724783 := bstep (se 1 (by rfl) ⟨543587, by rfl⟩ : syracuseStep 724783 = 1087175) B1087175
theorem B1445687 : Blo 642303 1445687 := bstep (se 1 (by rfl) ⟨1084265, by rfl⟩ : syracuseStep 1445687 = 2168531) B2168531
theorem B724891 : Blo 642303 724891 := bstep (se 1 (by rfl) ⟨543668, by rfl⟩ : syracuseStep 724891 = 1087337) B1087337
theorem B1445993 : Blo 642303 1445993 := bstep (se 2 (by rfl) ⟨542247, by rfl⟩ : syracuseStep 1445993 = 1084495) B1084495
theorem B725287 : Blo 642303 725287 := bstep (se 1 (by rfl) ⟨543965, by rfl⟩ : syracuseStep 725287 = 1087931) B1087931
theorem B725359 : Blo 642303 725359 := bstep (se 1 (by rfl) ⟨544019, by rfl⟩ : syracuseStep 725359 = 1088039) B1088039
theorem B3314177 : Blo 642303 3314177 := bstep (se 2 (by rfl) ⟨1242816, by rfl⟩ : syracuseStep 3314177 = 2485633) B2485633
theorem B11178557 : Blo 642303 11178557 := bstep (se 3 (by rfl) ⟨2095979, by rfl⟩ : syracuseStep 11178557 = 4191959) B4191959
theorem B725575 : Blo 642303 725575 := bstep (se 1 (by rfl) ⟨544181, by rfl⟩ : syracuseStep 725575 = 1088363) B1088363
theorem B1446479 : Blo 642303 1446479 := bstep (se 1 (by rfl) ⟨1084859, by rfl⟩ : syracuseStep 1446479 = 2169719) B2169719
theorem B1446623 : Blo 642303 1446623 := bstep (se 1 (by rfl) ⟨1084967, by rfl⟩ : syracuseStep 1446623 = 2169935) B2169935
theorem B1446875 : Blo 642303 1446875 := bstep (se 1 (by rfl) ⟨1085156, by rfl⟩ : syracuseStep 1446875 = 2170313) B2170313
theorem B1086439 : Blo 642303 1086439 := bstep (se 1 (by rfl) ⟨814829, by rfl⟩ : syracuseStep 1086439 = 1629659) B1629659
theorem B1447055 : Blo 642303 1447055 := bstep (se 1 (by rfl) ⟨1085291, by rfl⟩ : syracuseStep 1447055 = 2170583) B2170583
theorem B1447145 : Blo 642303 1447145 := bstep (se 2 (by rfl) ⟨542679, by rfl⟩ : syracuseStep 1447145 = 1085359) B1085359
theorem B1447199 : Blo 642303 1447199 := bstep (se 1 (by rfl) ⟨1085399, by rfl⟩ : syracuseStep 1447199 = 2170799) B2170799
theorem B726439 : Blo 642303 726439 := bstep (se 1 (by rfl) ⟨544829, by rfl⟩ : syracuseStep 726439 = 1089659) B1089659
theorem B5510693 : Blo 642303 5510693 := bstep (se 4 (by rfl) ⟨516627, by rfl⟩ : syracuseStep 5510693 = 1033255) B1033255
theorem B2168477 : Blo 642303 2168477 := bstep (se 3 (by rfl) ⟨406589, by rfl⟩ : syracuseStep 2168477 = 813179) B813179
theorem B1447721 : Blo 642303 1447721 := bstep (se 2 (by rfl) ⟨542895, by rfl⟩ : syracuseStep 1447721 = 1085791) B1085791
theorem B727015 : Blo 642303 727015 := bstep (se 1 (by rfl) ⟨545261, by rfl⟩ : syracuseStep 727015 = 1090523) B1090523
theorem B2169017 : Blo 642303 2169017 := bstep (se 2 (by rfl) ⟨813381, by rfl⟩ : syracuseStep 2169017 = 1626763) B1626763
theorem B82647449 : Blo 642303 82647449 := bstep (se 2 (by rfl) ⟨30992793, by rfl⟩ : syracuseStep 82647449 = 61985587) B61985587
theorem B3676711 : Blo 642303 3676711 := bstep (se 1 (by rfl) ⟨2757533, by rfl⟩ : syracuseStep 3676711 = 5515067) B5515067
theorem B2792009 : Blo 642303 2792009 := bstep (se 2 (by rfl) ⟨1047003, by rfl⟩ : syracuseStep 2792009 = 2094007) B2094007
theorem B1448783 : Blo 642303 1448783 := bstep (se 1 (by rfl) ⟨1086587, by rfl⟩ : syracuseStep 1448783 = 2173175) B2173175
theorem B21437459 : Blo 642303 21437459 := bstep (se 1 (by rfl) ⟨16078094, by rfl⟩ : syracuseStep 21437459 = 32156189) B32156189
theorem B1448999 : Blo 642303 1448999 := bstep (se 1 (by rfl) ⟨1086749, by rfl⟩ : syracuseStep 1448999 = 2173499) B2173499
theorem B1449179 : Blo 642303 1449179 := bstep (se 1 (by rfl) ⟨1086884, by rfl⟩ : syracuseStep 1449179 = 2173769) B2173769
theorem B70556993 : Blo 642303 70556993 := bstep (se 2 (by rfl) ⟨26458872, by rfl⟩ : syracuseStep 70556993 = 52917745) B52917745
theorem B1449377 : Blo 642303 1449377 := bstep (se 2 (by rfl) ⟨543516, by rfl⟩ : syracuseStep 1449377 = 1087033) B1087033
theorem B4136507 : Blo 642303 4136507 := bstep (se 1 (by rfl) ⟨3102380, by rfl⟩ : syracuseStep 4136507 = 6204761) B6204761
theorem B1220179 : Blo 642303 1220179 := bstep (se 1 (by rfl) ⟨915134, by rfl⟩ : syracuseStep 1220179 = 1830269) B1830269
theorem B1089119 : Blo 642303 1089119 := bstep (se 1 (by rfl) ⟨816839, by rfl⟩ : syracuseStep 1089119 = 1633679) B1633679
theorem B2170529 : Blo 642303 2170529 := bstep (se 2 (by rfl) ⟨813948, by rfl⟩ : syracuseStep 2170529 = 1627897) B1627897
theorem B4136609 : Blo 642303 4136609 := bstep (se 2 (by rfl) ⟨1551228, by rfl⟩ : syracuseStep 4136609 = 3102457) B3102457
theorem B3481355 : Blo 642303 3481355 := bstep (se 1 (by rfl) ⟨2611016, by rfl⟩ : syracuseStep 3481355 = 5222033) B5222033
theorem B1089335 : Blo 642303 1089335 := bstep (se 1 (by rfl) ⟨817001, by rfl⟩ : syracuseStep 1089335 = 1634003) B1634003
theorem B696271 : Blo 642303 696271 := bstep (se 1 (by rfl) ⟨522203, by rfl⟩ : syracuseStep 696271 = 1044407) B1044407
theorem B1449935 : Blo 642303 1449935 := bstep (se 1 (by rfl) ⟨1087451, by rfl⟩ : syracuseStep 1449935 = 2174903) B2174903
theorem B1548499 : Blo 642303 1548499 := bstep (se 1 (by rfl) ⟨1161374, by rfl⟩ : syracuseStep 1548499 = 2322749) B2322749
theorem B1450313 : Blo 642303 1450313 := bstep (se 2 (by rfl) ⟨543867, by rfl⟩ : syracuseStep 1450313 = 1087735) B1087735
theorem B1450331 : Blo 642303 1450331 := bstep (se 1 (by rfl) ⟨1087748, by rfl⟩ : syracuseStep 1450331 = 2175497) B2175497
theorem B2171393 : Blo 642303 2171393 := bstep (se 2 (by rfl) ⟨814272, by rfl⟩ : syracuseStep 2171393 = 1628545) B1628545
theorem B1090111 : Blo 642303 1090111 := bstep (se 1 (by rfl) ⟨817583, by rfl⟩ : syracuseStep 1090111 = 1635167) B1635167
theorem B1745479 : Blo 642303 1745479 := bstep (se 1 (by rfl) ⟨1309109, by rfl⟩ : syracuseStep 1745479 = 2618219) B2618219
theorem B1221227 : Blo 642303 1221227 := bstep (se 1 (by rfl) ⟨915920, by rfl⟩ : syracuseStep 1221227 = 1831841) B1831841
theorem B3252959 : Blo 642303 3252959 := bstep (se 1 (by rfl) ⟨2439719, by rfl⟩ : syracuseStep 3252959 = 4879439) B4879439
theorem B1221455 : Blo 642303 1221455 := bstep (se 1 (by rfl) ⟨916091, by rfl⟩ : syracuseStep 1221455 = 1832183) B1832183
theorem B1450907 : Blo 642303 1450907 := bstep (se 1 (by rfl) ⟨1088180, by rfl⟩ : syracuseStep 1450907 = 2176361) B2176361
theorem B2171879 : Blo 642303 2171879 := bstep (se 1 (by rfl) ⟨1628909, by rfl⟩ : syracuseStep 2171879 = 3257819) B3257819
theorem B1451105 : Blo 642303 1451105 := bstep (se 2 (by rfl) ⟨544164, by rfl⟩ : syracuseStep 1451105 = 1088329) B1088329
theorem B1451303 : Blo 642303 1451303 := bstep (se 1 (by rfl) ⟨1088477, by rfl⟩ : syracuseStep 1451303 = 2176955) B2176955
theorem B2172203 : Blo 642303 2172203 := bstep (se 1 (by rfl) ⟨1629152, by rfl⟩ : syracuseStep 2172203 = 3258305) B3258305
theorem B4629811 : Blo 642303 4629811 := bstep (se 1 (by rfl) ⟨3472358, by rfl⟩ : syracuseStep 4629811 = 6944717) B6944717
theorem B1549729 : Blo 642303 1549729 := bstep (se 2 (by rfl) ⟨581148, by rfl⟩ : syracuseStep 1549729 = 1162297) B1162297
theorem B2172473 : Blo 642303 2172473 := bstep (se 2 (by rfl) ⟨814677, by rfl⟩ : syracuseStep 2172473 = 1629355) B1629355
theorem B3679901 : Blo 642303 3679901 := bstep (se 3 (by rfl) ⟨689981, by rfl⟩ : syracuseStep 3679901 = 1379963) B1379963
theorem B1451681 : Blo 642303 1451681 := bstep (se 2 (by rfl) ⟨544380, by rfl⟩ : syracuseStep 1451681 = 1088761) B1088761
theorem B4892561 : Blo 642303 4892561 := bstep (se 2 (by rfl) ⟨1834710, by rfl⟩ : syracuseStep 4892561 = 3669421) B3669421
theorem B1550287 : Blo 642303 1550287 := bstep (se 1 (by rfl) ⟨1162715, by rfl⟩ : syracuseStep 1550287 = 2325431) B2325431
theorem B1452041 : Blo 642303 1452041 := bstep (se 2 (by rfl) ⟨544515, by rfl⟩ : syracuseStep 1452041 = 1089031) B1089031
theorem B1550441 : Blo 642303 1550441 := bstep (se 2 (by rfl) ⟨581415, by rfl⟩ : syracuseStep 1550441 = 1162831) B1162831
theorem B2205949 : Blo 642303 2205949 := bstep (se 3 (by rfl) ⟨413615, by rfl⟩ : syracuseStep 2205949 = 827231) B827231
theorem B120760627 : Blo 642303 120760627 := bstep (se 1 (by rfl) ⟨90570470, by rfl⟩ : syracuseStep 120760627 = 181140941) B181140941
theorem B1452455 : Blo 642303 1452455 := bstep (se 1 (by rfl) ⟨1089341, by rfl⟩ : syracuseStep 1452455 = 2178683) B2178683
theorem B1452563 : Blo 642303 1452563 := bstep (se 1 (by rfl) ⟨1089422, by rfl⟩ : syracuseStep 1452563 = 2178845) B2178845
theorem B1452617 : Blo 642303 1452617 := bstep (se 2 (by rfl) ⟨544731, by rfl⟩ : syracuseStep 1452617 = 1089463) B1089463
theorem B2173715 : Blo 642303 2173715 := bstep (se 1 (by rfl) ⟨1630286, by rfl⟩ : syracuseStep 2173715 = 3260573) B3260573
theorem B3484559 : Blo 642303 3484559 := bstep (se 1 (by rfl) ⟨2613419, by rfl⟩ : syracuseStep 3484559 = 5226839) B5226839
theorem B3255227 : Blo 642303 3255227 := bstep (se 1 (by rfl) ⟨2441420, by rfl⟩ : syracuseStep 3255227 = 4882841) B4882841
theorem B1453031 : Blo 642303 1453031 := bstep (se 1 (by rfl) ⟨1089773, by rfl⟩ : syracuseStep 1453031 = 2179547) B2179547
theorem B1453409 : Blo 642303 1453409 := bstep (se 2 (by rfl) ⟨545028, by rfl⟩ : syracuseStep 1453409 = 1090057) B1090057
theorem B1453499 : Blo 642303 1453499 := bstep (se 1 (by rfl) ⟨1090124, by rfl⟩ : syracuseStep 1453499 = 2180249) B2180249
theorem B1453625 : Blo 642303 1453625 := bstep (se 2 (by rfl) ⟨545109, by rfl⟩ : syracuseStep 1453625 = 1090219) B1090219
theorem B2174579 : Blo 642303 2174579 := bstep (se 1 (by rfl) ⟨1630934, by rfl⟩ : syracuseStep 2174579 = 3261869) B3261869
theorem B3092231 : Blo 642303 3092231 := bstep (se 1 (by rfl) ⟨2319173, by rfl⟩ : syracuseStep 3092231 = 4638347) B4638347
theorem B4140811 : Blo 642303 4140811 := bstep (se 1 (by rfl) ⟨3105608, by rfl⟩ : syracuseStep 4140811 = 6211217) B6211217
theorem B2174849 : Blo 642303 2174849 := bstep (se 2 (by rfl) ⟨815568, by rfl⟩ : syracuseStep 2174849 = 1631137) B1631137
theorem B3092539 : Blo 642303 3092539 := bstep (se 1 (by rfl) ⟨2319404, by rfl⟩ : syracuseStep 3092539 = 4638809) B4638809
theorem B3256523 : Blo 642303 3256523 := bstep (se 1 (by rfl) ⟨2442392, by rfl⟩ : syracuseStep 3256523 = 4884785) B4884785
theorem B4894991 : Blo 642303 4894991 := bstep (se 1 (by rfl) ⟨3671243, by rfl⟩ : syracuseStep 4894991 = 7342487) B7342487
theorem B59683189 : Blo 642303 59683189 := bstep (se 5 (by rfl) ⟨2797649, by rfl⟩ : syracuseStep 59683189 = 5595299) B5595299
theorem B5878291 : Blo 642303 5878291 := bstep (se 1 (by rfl) ⟨4408718, by rfl⟩ : syracuseStep 5878291 = 8817437) B8817437
theorem B3093137 : Blo 642303 3093137 := bstep (se 2 (by rfl) ⟨1159926, by rfl⟩ : syracuseStep 3093137 = 2319853) B2319853
theorem B2175659 : Blo 642303 2175659 := bstep (se 1 (by rfl) ⟨1631744, by rfl⟩ : syracuseStep 2175659 = 3263489) B3263489
theorem B1651835 : Blo 642303 1651835 := bstep (se 1 (by rfl) ⟨1238876, by rfl⟩ : syracuseStep 1651835 = 2477753) B2477753
theorem B2176199 : Blo 642303 2176199 := bstep (se 1 (by rfl) ⟨1632149, by rfl⟩ : syracuseStep 2176199 = 3264299) B3264299
theorem B963803 : Blo 642303 963803 := bstep (se 1 (by rfl) ⟨722852, by rfl⟩ : syracuseStep 963803 = 1445705) B1445705
theorem B963977 : Blo 642303 963977 := bstep (se 2 (by rfl) ⟨361491, by rfl⟩ : syracuseStep 963977 = 722983) B722983
theorem B964331 : Blo 642303 964331 := bstep (se 1 (by rfl) ⟨723248, by rfl⟩ : syracuseStep 964331 = 1446497) B1446497
theorem B964559 : Blo 642303 964559 := bstep (se 1 (by rfl) ⟨723419, by rfl⟩ : syracuseStep 964559 = 1446839) B1446839
theorem B4634657 : Blo 642303 4634657 := bstep (se 2 (by rfl) ⟨1737996, by rfl⟩ : syracuseStep 4634657 = 3475993) B3475993
theorem B964955 : Blo 642303 964955 := bstep (se 1 (by rfl) ⟨723716, by rfl⟩ : syracuseStep 964955 = 1447433) B1447433
theorem B3258791 : Blo 642303 3258791 := bstep (se 1 (by rfl) ⟨2444093, by rfl⟩ : syracuseStep 3258791 = 4888187) B4888187
theorem B965183 : Blo 642303 965183 := bstep (se 1 (by rfl) ⟨723887, by rfl⟩ : syracuseStep 965183 = 1447775) B1447775
theorem B3258953 : Blo 642303 3258953 := bstep (se 2 (by rfl) ⟨1222107, by rfl⟩ : syracuseStep 3258953 = 2444215) B2444215
theorem B2177711 : Blo 642303 2177711 := bstep (se 1 (by rfl) ⟨1633283, by rfl⟩ : syracuseStep 2177711 = 3266567) B3266567
theorem B965303 : Blo 642303 965303 := bstep (se 1 (by rfl) ⟨723977, by rfl⟩ : syracuseStep 965303 = 1447955) B1447955
theorem B965531 : Blo 642303 965531 := bstep (se 1 (by rfl) ⟨724148, by rfl⟩ : syracuseStep 965531 = 1448297) B1448297
theorem B2472947 : Blo 642303 2472947 := bstep (se 1 (by rfl) ⟨1854710, by rfl⟩ : syracuseStep 2472947 = 3709421) B3709421
theorem B2178035 : Blo 642303 2178035 := bstep (se 1 (by rfl) ⟨1633526, by rfl⟩ : syracuseStep 2178035 = 3267053) B3267053
theorem B965927 : Blo 642303 965927 := bstep (se 1 (by rfl) ⟨724445, by rfl⟩ : syracuseStep 965927 = 1448891) B1448891
theorem B966011 : Blo 642303 966011 := bstep (se 1 (by rfl) ⟨724508, by rfl⟩ : syracuseStep 966011 = 1449017) B1449017
theorem B5488073 : Blo 642303 5488073 := bstep (se 2 (by rfl) ⟨2058027, by rfl⟩ : syracuseStep 5488073 = 4116055) B4116055
theorem B5291513 : Blo 642303 5291513 := bstep (se 2 (by rfl) ⟨1984317, by rfl⟩ : syracuseStep 5291513 = 3968635) B3968635
theorem B966137 : Blo 642303 966137 := bstep (se 2 (by rfl) ⟨362301, by rfl⟩ : syracuseStep 966137 = 724603) B724603
theorem B2178575 : Blo 642303 2178575 := bstep (se 1 (by rfl) ⟨1633931, by rfl⟩ : syracuseStep 2178575 = 3267863) B3267863
theorem B2440799 : Blo 642303 2440799 := bstep (se 1 (by rfl) ⟨1830599, by rfl⟩ : syracuseStep 2440799 = 3661199) B3661199
theorem B966239 : Blo 642303 966239 := bstep (se 1 (by rfl) ⟨724679, by rfl⟩ : syracuseStep 966239 = 1449359) B1449359
theorem B2440813 : Blo 642303 2440813 := bstep (se 3 (by rfl) ⟨457652, by rfl⟩ : syracuseStep 2440813 = 915305) B915305
theorem B8797841 : Blo 642303 8797841 := bstep (se 2 (by rfl) ⟨3299190, by rfl⟩ : syracuseStep 8797841 = 6598381) B6598381
theorem B5586691 : Blo 642303 5586691 := bstep (se 1 (by rfl) ⟨4190018, by rfl⟩ : syracuseStep 5586691 = 8380037) B8380037
theorem B966455 : Blo 642303 966455 := bstep (se 1 (by rfl) ⟨724841, by rfl⟩ : syracuseStep 966455 = 1449683) B1449683
theorem B3915649 : Blo 642303 3915649 := bstep (se 2 (by rfl) ⟨1468368, by rfl⟩ : syracuseStep 3915649 = 2936737) B2936737
theorem B2441117 : Blo 642303 2441117 := bstep (se 3 (by rfl) ⟨457709, by rfl⟩ : syracuseStep 2441117 = 915419) B915419
theorem B2473993 : Blo 642303 2473993 := bstep (se 2 (by rfl) ⟨927747, by rfl⟩ : syracuseStep 2473993 = 1855495) B1855495
theorem B18530315 : Blo 642303 18530315 := bstep (se 1 (by rfl) ⟨13897736, by rfl⟩ : syracuseStep 18530315 = 27795473) B27795473
theorem B5586995 : Blo 642303 5586995 := bstep (se 1 (by rfl) ⟨4190246, by rfl⟩ : syracuseStep 5586995 = 8380493) B8380493
theorem B966761 : Blo 642303 966761 := bstep (se 2 (by rfl) ⟨362535, by rfl⟩ : syracuseStep 966761 = 725071) B725071
theorem B11026853 : Blo 642303 11026853 := bstep (se 4 (by rfl) ⟨1033767, by rfl⟩ : syracuseStep 11026853 = 2067535) B2067535
theorem B967079 : Blo 642303 967079 := bstep (se 1 (by rfl) ⟨725309, by rfl⟩ : syracuseStep 967079 = 1450619) B1450619
theorem B3260897 : Blo 642303 3260897 := bstep (se 2 (by rfl) ⟨1222836, by rfl⟩ : syracuseStep 3260897 = 2445673) B2445673
theorem B967163 : Blo 642303 967163 := bstep (se 1 (by rfl) ⟨725372, by rfl⟩ : syracuseStep 967163 = 1450745) B1450745
theorem B2179655 : Blo 642303 2179655 := bstep (se 1 (by rfl) ⟨1634741, by rfl⟩ : syracuseStep 2179655 = 3269483) B3269483
theorem B967289 : Blo 642303 967289 := bstep (se 2 (by rfl) ⟨362733, by rfl⟩ : syracuseStep 967289 = 725467) B725467
theorem B967343 : Blo 642303 967343 := bstep (se 1 (by rfl) ⟨725507, by rfl⟩ : syracuseStep 967343 = 1451015) B1451015
theorem B967391 : Blo 642303 967391 := bstep (se 1 (by rfl) ⟨725543, by rfl⟩ : syracuseStep 967391 = 1451087) B1451087
theorem B12370765 : Blo 642303 12370765 := bstep (se 3 (by rfl) ⟨2319518, by rfl⟩ : syracuseStep 12370765 = 4639037) B4639037
theorem B967655 : Blo 642303 967655 := bstep (se 1 (by rfl) ⟨725741, by rfl⟩ : syracuseStep 967655 = 1451483) B1451483
theorem B2180087 : Blo 642303 2180087 := bstep (se 1 (by rfl) ⟨1635065, by rfl⟩ : syracuseStep 2180087 = 3270131) B3270131
theorem B1164431 : Blo 642303 1164431 := bstep (se 1 (by rfl) ⟨873323, by rfl⟩ : syracuseStep 1164431 = 1746647) B1746647
theorem B1033435 : Blo 642303 1033435 := bstep (se 1 (by rfl) ⟨775076, by rfl⟩ : syracuseStep 1033435 = 1550153) B1550153
theorem B967913 : Blo 642303 967913 := bstep (se 2 (by rfl) ⟨362967, by rfl⟩ : syracuseStep 967913 = 725935) B725935
theorem B967967 : Blo 642303 967967 := bstep (se 1 (by rfl) ⟨725975, by rfl⟩ : syracuseStep 967967 = 1451951) B1451951
theorem B1164575 : Blo 642303 1164575 := bstep (se 1 (by rfl) ⟨873431, by rfl⟩ : syracuseStep 1164575 = 1746863) B1746863
theorem B3523945 : Blo 642303 3523945 := bstep (se 2 (by rfl) ⟨1321479, by rfl⟩ : syracuseStep 3523945 = 2642959) B2642959
theorem B6210989 : Blo 642303 6210989 := bstep (se 3 (by rfl) ⟨1164560, by rfl⟩ : syracuseStep 6210989 = 2329121) B2329121
theorem B968135 : Blo 642303 968135 := bstep (se 1 (by rfl) ⟨726101, by rfl⟩ : syracuseStep 968135 = 1452203) B1452203
theorem B968489 : Blo 642303 968489 := bstep (se 2 (by rfl) ⟨363183, by rfl⟩ : syracuseStep 968489 = 726367) B726367
theorem B968495 : Blo 642303 968495 := bstep (se 1 (by rfl) ⟨726371, by rfl⟩ : syracuseStep 968495 = 1452743) B1452743
theorem B2180951 : Blo 642303 2180951 := bstep (se 1 (by rfl) ⟨1635713, by rfl⟩ : syracuseStep 2180951 = 3271427) B3271427
theorem B1034345 : Blo 642303 1034345 := bstep (se 2 (by rfl) ⟨387879, by rfl⟩ : syracuseStep 1034345 = 775759) B775759
theorem B2443517 : Blo 642303 2443517 := bstep (se 3 (by rfl) ⟨458159, by rfl⟩ : syracuseStep 2443517 = 916319) B916319
theorem B968969 : Blo 642303 968969 := bstep (se 2 (by rfl) ⟨363363, by rfl⟩ : syracuseStep 968969 = 726727) B726727
theorem B969071 : Blo 642303 969071 := bstep (se 1 (by rfl) ⟨726803, by rfl⟩ : syracuseStep 969071 = 1453607) B1453607
theorem B969287 : Blo 642303 969287 := bstep (se 1 (by rfl) ⟨726965, by rfl⟩ : syracuseStep 969287 = 1453931) B1453931
theorem B969323 : Blo 642303 969323 := bstep (se 1 (by rfl) ⟨726992, by rfl⟩ : syracuseStep 969323 = 1453985) B1453985
theorem B3263165 : Blo 642303 3263165 := bstep (se 3 (by rfl) ⟨611843, by rfl⟩ : syracuseStep 3263165 = 1223687) B1223687
theorem B5491421 : Blo 642303 5491421 := bstep (se 3 (by rfl) ⟨1029641, by rfl⟩ : syracuseStep 5491421 = 2059283) B2059283
theorem B8276701 : Blo 642303 8276701 := bstep (se 3 (by rfl) ⟨1551881, by rfl⟩ : syracuseStep 8276701 = 3103763) B3103763
theorem B3099383 : Blo 642303 3099383 := bstep (se 1 (by rfl) ⟨2324537, by rfl⟩ : syracuseStep 3099383 = 4649075) B4649075
theorem B23547019 : Blo 642303 23547019 := bstep (se 1 (by rfl) ⟨17660264, by rfl⟩ : syracuseStep 23547019 = 35320529) B35320529
theorem B8801459 : Blo 642303 8801459 := bstep (se 1 (by rfl) ⟨6601094, by rfl⟩ : syracuseStep 8801459 = 13202189) B13202189
theorem B642335 : Blo 642303 642335 := bstep (se 1 (by rfl) ⟨481751, by rfl⟩ : syracuseStep 642335 = 963503) B963503
theorem B642395 : Blo 642303 642395 := bstep (se 1 (by rfl) ⟨481796, by rfl⟩ : syracuseStep 642395 = 963593) B963593
theorem B642415 : Blo 642303 642415 := bstep (se 1 (by rfl) ⟨481811, by rfl⟩ : syracuseStep 642415 = 963623) B963623
theorem B642471 : Blo 642303 642471 := bstep (se 1 (by rfl) ⟨481853, by rfl⟩ : syracuseStep 642471 = 963707) B963707
theorem B642555 : Blo 642303 642555 := bstep (se 1 (by rfl) ⟨481916, by rfl⟩ : syracuseStep 642555 = 963833) B963833
theorem B642623 : Blo 642303 642623 := bstep (se 1 (by rfl) ⟨481967, by rfl⟩ : syracuseStep 642623 = 963935) B963935
theorem B642631 : Blo 642303 642631 := bstep (se 1 (by rfl) ⟨481973, by rfl⟩ : syracuseStep 642631 = 963947) B963947
theorem B7065251 : Blo 642303 7065251 := bstep (se 1 (by rfl) ⟨5298938, by rfl⟩ : syracuseStep 7065251 = 10597877) B10597877
theorem B642783 : Blo 642303 642783 := bstep (se 1 (by rfl) ⟨482087, by rfl⟩ : syracuseStep 642783 = 964175) B964175
theorem B1625903 : Blo 642303 1625903 := bstep (se 1 (by rfl) ⟨1219427, by rfl⟩ : syracuseStep 1625903 = 2438855) B2438855
theorem B642863 : Blo 642303 642863 := bstep (se 1 (by rfl) ⟨482147, by rfl⟩ : syracuseStep 642863 = 964295) B964295
theorem B642971 : Blo 642303 642971 := bstep (se 1 (by rfl) ⟨482228, by rfl⟩ : syracuseStep 642971 = 964457) B964457
theorem B643023 : Blo 642303 643023 := bstep (se 1 (by rfl) ⟨482267, by rfl⟩ : syracuseStep 643023 = 964535) B964535
theorem B643047 : Blo 642303 643047 := bstep (se 1 (by rfl) ⟨482285, by rfl⟩ : syracuseStep 643047 = 964571) B964571
theorem B643359 : Blo 642303 643359 := bstep (se 1 (by rfl) ⟨482519, by rfl⟩ : syracuseStep 643359 = 965039) B965039
theorem B643419 : Blo 642303 643419 := bstep (se 1 (by rfl) ⟨482564, by rfl⟩ : syracuseStep 643419 = 965129) B965129
theorem B2445659 : Blo 642303 2445659 := bstep (se 1 (by rfl) ⟨1834244, by rfl⟩ : syracuseStep 2445659 = 3668489) B3668489
theorem B643439 : Blo 642303 643439 := bstep (se 1 (by rfl) ⟨482579, by rfl⟩ : syracuseStep 643439 = 965159) B965159
theorem B643495 : Blo 642303 643495 := bstep (se 1 (by rfl) ⟨482621, by rfl⟩ : syracuseStep 643495 = 965243) B965243
theorem B1626551 : Blo 642303 1626551 := bstep (se 1 (by rfl) ⟨1219913, by rfl⟩ : syracuseStep 1626551 = 2439827) B2439827
theorem B643579 : Blo 642303 643579 := bstep (se 1 (by rfl) ⟨482684, by rfl⟩ : syracuseStep 643579 = 965369) B965369
theorem B643647 : Blo 642303 643647 := bstep (se 1 (by rfl) ⟨482735, by rfl⟩ : syracuseStep 643647 = 965471) B965471
theorem B643655 : Blo 642303 643655 := bstep (se 1 (by rfl) ⟨482741, by rfl⟩ : syracuseStep 643655 = 965483) B965483
theorem B2445977 : Blo 642303 2445977 := bstep (se 2 (by rfl) ⟨917241, by rfl⟩ : syracuseStep 2445977 = 1834483) B1834483
theorem B643807 : Blo 642303 643807 := bstep (se 1 (by rfl) ⟨482855, by rfl⟩ : syracuseStep 643807 = 965711) B965711
theorem B643887 : Blo 642303 643887 := bstep (se 1 (by rfl) ⟨482915, by rfl⟩ : syracuseStep 643887 = 965831) B965831
theorem B2446159 : Blo 642303 2446159 := bstep (se 1 (by rfl) ⟨1834619, by rfl⟩ : syracuseStep 2446159 = 3669239) B3669239
theorem B643995 : Blo 642303 643995 := bstep (se 1 (by rfl) ⟨482996, by rfl⟩ : syracuseStep 643995 = 965993) B965993
theorem B644047 : Blo 642303 644047 := bstep (se 1 (by rfl) ⟨483035, by rfl⟩ : syracuseStep 644047 = 966071) B966071
theorem B644071 : Blo 642303 644071 := bstep (se 1 (by rfl) ⟨483053, by rfl⟩ : syracuseStep 644071 = 966107) B966107
theorem B2446433 : Blo 642303 2446433 := bstep (se 2 (by rfl) ⟨917412, by rfl⟩ : syracuseStep 2446433 = 1834825) B1834825
theorem B644383 : Blo 642303 644383 := bstep (se 1 (by rfl) ⟨483287, by rfl⟩ : syracuseStep 644383 = 966575) B966575
theorem B2446631 : Blo 642303 2446631 := bstep (se 1 (by rfl) ⟨1834973, by rfl⟩ : syracuseStep 2446631 = 3669947) B3669947
theorem B644443 : Blo 642303 644443 := bstep (se 1 (by rfl) ⟨483332, by rfl⟩ : syracuseStep 644443 = 966665) B966665
theorem B644463 : Blo 642303 644463 := bstep (se 1 (by rfl) ⟨483347, by rfl⟩ : syracuseStep 644463 = 966695) B966695
theorem B1627553 : Blo 642303 1627553 := bstep (se 2 (by rfl) ⟨610332, by rfl⟩ : syracuseStep 1627553 = 1220665) B1220665
theorem B644519 : Blo 642303 644519 := bstep (se 1 (by rfl) ⟨483389, by rfl⟩ : syracuseStep 644519 = 966779) B966779
theorem B644603 : Blo 642303 644603 := bstep (se 1 (by rfl) ⟨483452, by rfl⟩ : syracuseStep 644603 = 966905) B966905
theorem B3266081 : Blo 642303 3266081 := bstep (se 2 (by rfl) ⟨1224780, by rfl⟩ : syracuseStep 3266081 = 2449561) B2449561
theorem B114349603 : Blo 642303 114349603 := bstep (se 1 (by rfl) ⟨85762202, by rfl⟩ : syracuseStep 114349603 = 171524405) B171524405
theorem B4118053 : Blo 642303 4118053 := bstep (se 4 (by rfl) ⟨386067, by rfl⟩ : syracuseStep 4118053 = 772135) B772135
theorem B9655853 : Blo 642303 9655853 := bstep (se 3 (by rfl) ⟨1810472, by rfl⟩ : syracuseStep 9655853 = 3620945) B3620945
theorem B644671 : Blo 642303 644671 := bstep (se 1 (by rfl) ⟨483503, by rfl⟩ : syracuseStep 644671 = 967007) B967007
theorem B644679 : Blo 642303 644679 := bstep (se 1 (by rfl) ⟨483509, by rfl⟩ : syracuseStep 644679 = 967019) B967019
theorem B775787 : Blo 642303 775787 := bstep (se 1 (by rfl) ⟨581840, by rfl⟩ : syracuseStep 775787 = 1163681) B1163681
theorem B644831 : Blo 642303 644831 := bstep (se 1 (by rfl) ⟨483623, by rfl⟩ : syracuseStep 644831 = 967247) B967247
theorem B644911 : Blo 642303 644911 := bstep (se 1 (by rfl) ⟨483683, by rfl⟩ : syracuseStep 644911 = 967367) B967367
theorem B5592887 : Blo 642303 5592887 := bstep (se 1 (by rfl) ⟨4194665, by rfl⟩ : syracuseStep 5592887 = 8389331) B8389331
theorem B1628009 : Blo 642303 1628009 := bstep (se 2 (by rfl) ⟨610503, by rfl⟩ : syracuseStep 1628009 = 1221007) B1221007
theorem B645019 : Blo 642303 645019 := bstep (se 1 (by rfl) ⟨483764, by rfl⟩ : syracuseStep 645019 = 967529) B967529
theorem B645071 : Blo 642303 645071 := bstep (se 1 (by rfl) ⟨483803, by rfl⟩ : syracuseStep 645071 = 967607) B967607
theorem B645095 : Blo 642303 645095 := bstep (se 1 (by rfl) ⟨483821, by rfl⟩ : syracuseStep 645095 = 967643) B967643
theorem B5593367 : Blo 642303 5593367 := bstep (se 1 (by rfl) ⟨4195025, by rfl⟩ : syracuseStep 5593367 = 8390051) B8390051
theorem B645407 : Blo 642303 645407 := bstep (se 1 (by rfl) ⟨484055, by rfl⟩ : syracuseStep 645407 = 968111) B968111
theorem B645467 : Blo 642303 645467 := bstep (se 1 (by rfl) ⟨484100, by rfl⟩ : syracuseStep 645467 = 968201) B968201
theorem B2087279 : Blo 642303 2087279 := bstep (se 1 (by rfl) ⟨1565459, by rfl⟩ : syracuseStep 2087279 = 3130919) B3130919
theorem B645487 : Blo 642303 645487 := bstep (se 1 (by rfl) ⟨484115, by rfl⟩ : syracuseStep 645487 = 968231) B968231
theorem B645543 : Blo 642303 645543 := bstep (se 1 (by rfl) ⟨484157, by rfl⟩ : syracuseStep 645543 = 968315) B968315
theorem B645627 : Blo 642303 645627 := bstep (se 1 (by rfl) ⟨484220, by rfl⟩ : syracuseStep 645627 = 968441) B968441
theorem B645695 : Blo 642303 645695 := bstep (se 1 (by rfl) ⟨484271, by rfl⟩ : syracuseStep 645695 = 968543) B968543
theorem B645703 : Blo 642303 645703 := bstep (se 1 (by rfl) ⟨484277, by rfl⟩ : syracuseStep 645703 = 968555) B968555
theorem B9394805 : Blo 642303 9394805 := bstep (se 5 (by rfl) ⟨440381, by rfl⟩ : syracuseStep 9394805 = 880763) B880763
theorem B3922607 : Blo 642303 3922607 := bstep (se 1 (by rfl) ⟨2941955, by rfl⟩ : syracuseStep 3922607 = 5883911) B5883911
theorem B645855 : Blo 642303 645855 := bstep (se 1 (by rfl) ⟨484391, by rfl⟩ : syracuseStep 645855 = 968783) B968783
theorem B645935 : Blo 642303 645935 := bstep (se 1 (by rfl) ⟨484451, by rfl⟩ : syracuseStep 645935 = 968903) B968903
theorem B646043 : Blo 642303 646043 := bstep (se 1 (by rfl) ⟨484532, by rfl⟩ : syracuseStep 646043 = 969065) B969065
theorem B646095 : Blo 642303 646095 := bstep (se 1 (by rfl) ⟨484571, by rfl⟩ : syracuseStep 646095 = 969143) B969143
theorem B646119 : Blo 642303 646119 := bstep (se 1 (by rfl) ⟨484589, by rfl⟩ : syracuseStep 646119 = 969179) B969179
theorem B5495795 : Blo 642303 5495795 := bstep (se 1 (by rfl) ⟨4121846, by rfl⟩ : syracuseStep 5495795 = 8243693) B8243693
theorem B24141199 : Blo 642303 24141199 := bstep (se 1 (by rfl) ⟨18105899, by rfl⟩ : syracuseStep 24141199 = 36211799) B36211799
theorem B6610447 : Blo 642303 6610447 := bstep (se 1 (by rfl) ⟨4957835, by rfl⟩ : syracuseStep 6610447 = 9915671) B9915671
theorem B1629791 : Blo 642303 1629791 := bstep (se 1 (by rfl) ⟨1222343, by rfl⟩ : syracuseStep 1629791 = 2444687) B2444687
theorem B1957679 : Blo 642303 1957679 := bstep (se 1 (by rfl) ⟨1468259, by rfl⟩ : syracuseStep 1957679 = 2936519) B2936519
theorem B1630489 : Blo 642303 1630489 := bstep (se 2 (by rfl) ⟨611433, by rfl⟩ : syracuseStep 1630489 = 1222867) B1222867
theorem B2318699 : Blo 642303 2318699 := bstep (se 1 (by rfl) ⟨1739024, by rfl⟩ : syracuseStep 2318699 = 3478049) B3478049
theorem B1630631 : Blo 642303 1630631 := bstep (se 1 (by rfl) ⟨1222973, by rfl⟩ : syracuseStep 1630631 = 2445947) B2445947
theorem B3138011 : Blo 642303 3138011 := bstep (se 1 (by rfl) ⟨2353508, by rfl⟩ : syracuseStep 3138011 = 4707017) B4707017
theorem B1630793 : Blo 642303 1630793 := bstep (se 2 (by rfl) ⟨611547, by rfl⟩ : syracuseStep 1630793 = 1223095) B1223095
theorem B2482859 : Blo 642303 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B25158899 : Blo 642303 25158899 := bstep (se 1 (by rfl) ⟨18869174, by rfl⟩ : syracuseStep 25158899 = 37738349) B37738349
theorem B19785059 : Blo 642303 19785059 := bstep (se 1 (by rfl) ⟨14838794, by rfl⟩ : syracuseStep 19785059 = 29677589) B29677589
theorem B1467785 : Blo 642303 1467785 := bstep (se 2 (by rfl) ⟨550419, by rfl⟩ : syracuseStep 1467785 = 1100839) B1100839
theorem B3302849 : Blo 642303 3302849 := bstep (se 2 (by rfl) ⟨1238568, by rfl⟩ : syracuseStep 3302849 = 2477137) B2477137
theorem B1304147 : Blo 642303 1304147 := bstep (se 1 (by rfl) ⟨978110, by rfl⟩ : syracuseStep 1304147 = 1956221) B1956221
theorem B943913 : Blo 642303 943913 := bstep (se 2 (by rfl) ⟨353967, by rfl⟩ : syracuseStep 943913 = 707935) B707935
theorem B3270455 : Blo 642303 3270455 := bstep (se 1 (by rfl) ⟨2452841, by rfl⟩ : syracuseStep 3270455 = 4905683) B4905683
theorem B6186887 : Blo 642303 6186887 := bstep (se 1 (by rfl) ⟨4640165, by rfl⟩ : syracuseStep 6186887 = 9280331) B9280331
theorem B813007 : Blo 642303 813007 := bstep (se 1 (by rfl) ⟨609755, by rfl⟩ : syracuseStep 813007 = 1219511) B1219511
theorem B2615561 : Blo 642303 2615561 := bstep (se 2 (by rfl) ⟨980835, by rfl⟩ : syracuseStep 2615561 = 1961671) B1961671
theorem B3270941 : Blo 642303 3270941 := bstep (se 3 (by rfl) ⟨613301, by rfl⟩ : syracuseStep 3270941 = 1226603) B1226603
theorem B4647341 : Blo 642303 4647341 := bstep (se 3 (by rfl) ⟨871376, by rfl⟩ : syracuseStep 4647341 = 1742753) B1742753
theorem B1632737 : Blo 642303 1632737 := bstep (se 2 (by rfl) ⟨612276, by rfl⟩ : syracuseStep 1632737 = 1224553) B1224553
theorem B6187843 : Blo 642303 6187843 := bstep (se 1 (by rfl) ⟨4640882, by rfl⟩ : syracuseStep 6187843 = 9281765) B9281765
theorem B813979 : Blo 642303 813979 := bstep (se 1 (by rfl) ⟨610484, by rfl⟩ : syracuseStep 813979 = 1220969) B1220969
theorem B1633243 : Blo 642303 1633243 := bstep (se 1 (by rfl) ⟨1224932, by rfl⟩ : syracuseStep 1633243 = 2449865) B2449865
theorem B1829927 : Blo 642303 1829927 := bstep (se 1 (by rfl) ⟨1372445, by rfl⟩ : syracuseStep 1829927 = 2744891) B2744891
theorem B1633567 : Blo 642303 1633567 := bstep (se 1 (by rfl) ⟨1225175, by rfl⟩ : syracuseStep 1633567 = 2450351) B2450351
theorem B47673305 : Blo 642303 47673305 := bstep (se 2 (by rfl) ⟨17877489, by rfl⟩ : syracuseStep 47673305 = 35754979) B35754979
theorem B7073851 : Blo 642303 7073851 := bstep (se 1 (by rfl) ⟨5305388, by rfl⟩ : syracuseStep 7073851 = 10610777) B10610777
theorem B1634651 : Blo 642303 1634651 := bstep (se 1 (by rfl) ⟨1225988, by rfl⟩ : syracuseStep 1634651 = 2451977) B2451977
theorem B2453935 : Blo 642303 2453935 := bstep (se 1 (by rfl) ⟨1840451, by rfl⟩ : syracuseStep 2453935 = 3680903) B3680903
theorem B6189689 : Blo 642303 6189689 := bstep (se 2 (by rfl) ⟨2321133, by rfl⟩ : syracuseStep 6189689 = 4642267) B4642267
theorem B1864919 : Blo 642303 1864919 := bstep (se 1 (by rfl) ⟨1398689, by rfl⟩ : syracuseStep 1864919 = 2797379) B2797379
theorem B1635623 : Blo 642303 1635623 := bstep (se 1 (by rfl) ⟨1226717, by rfl⟩ : syracuseStep 1635623 = 2453435) B2453435
theorem B816475 : Blo 642303 816475 := bstep (se 1 (by rfl) ⟨612356, by rfl⟩ : syracuseStep 816475 = 1224713) B1224713
theorem B3667463 : Blo 642303 3667463 := bstep (se 1 (by rfl) ⟨2750597, by rfl⟩ : syracuseStep 3667463 = 5501195) B5501195
theorem B817447 : Blo 642303 817447 := bstep (se 1 (by rfl) ⟨613085, by rfl⟩ : syracuseStep 817447 = 1226171) B1226171
theorem B13236659 : Blo 642303 13236659 := bstep (se 1 (by rfl) ⟨9927494, by rfl⟩ : syracuseStep 13236659 = 19854989) B19854989
theorem B817771 : Blo 642303 817771 := bstep (se 1 (by rfl) ⟨613328, by rfl⟩ : syracuseStep 817771 = 1226657) B1226657
theorem B4651931 : Blo 642303 4651931 := bstep (se 1 (by rfl) ⟨3488948, by rfl⟩ : syracuseStep 4651931 = 6977897) B6977897
theorem B8911991 : Blo 642303 8911991 := bstep (se 1 (by rfl) ⟨6683993, by rfl⟩ : syracuseStep 8911991 = 13367987) B13367987
theorem B1834427 : Blo 642303 1834427 := bstep (se 1 (by rfl) ⟨1375820, by rfl⟩ : syracuseStep 1834427 = 2751641) B2751641
theorem B884287 : Blo 642303 884287 := bstep (se 1 (by rfl) ⟨663215, by rfl⟩ : syracuseStep 884287 = 1326431) B1326431
theorem B1736353 : Blo 642303 1736353 := bstep (se 2 (by rfl) ⟨651132, by rfl⟩ : syracuseStep 1736353 = 1302265) B1302265
theorem B3473225 : Blo 642303 3473225 := bstep (se 2 (by rfl) ⟨1302459, by rfl⟩ : syracuseStep 3473225 = 2604919) B2604919
theorem B12353543 : Blo 642303 12353543 := bstep (se 1 (by rfl) ⟨9265157, by rfl⟩ : syracuseStep 12353543 = 18530315) B18530315
theorem B2064665 : Blo 642303 2064665 := bstep (se 2 (by rfl) ⟨774249, by rfl⟩ : syracuseStep 2064665 = 1548499) B1548499
theorem B3670379 : Blo 642303 3670379 := bstep (se 1 (by rfl) ⟨2752784, by rfl⟩ : syracuseStep 3670379 = 5505569) B5505569
theorem B2327305 : Blo 642303 2327305 := bstep (se 2 (by rfl) ⟨872739, by rfl⟩ : syracuseStep 2327305 = 1745479) B1745479
theorem B23528339 : Blo 642303 23528339 := bstep (se 1 (by rfl) ⟨17646254, by rfl⟩ : syracuseStep 23528339 = 35292509) B35292509
theorem B12584135 : Blo 642303 12584135 := bstep (se 1 (by rfl) ⟨9438101, by rfl⟩ : syracuseStep 12584135 = 18876203) B18876203
theorem B689563 : Blo 642303 689563 := bstep (se 1 (by rfl) ⟨517172, by rfl⟩ : syracuseStep 689563 = 1034345) B1034345
theorem B15664751 : Blo 642303 15664751 := bstep (se 1 (by rfl) ⟨11748563, by rfl⟩ : syracuseStep 15664751 = 23497127) B23497127
theorem B1377913 : Blo 642303 1377913 := bstep (se 2 (by rfl) ⟨516717, by rfl⟩ : syracuseStep 1377913 = 1033435) B1033435
theorem B2361095 : Blo 642303 2361095 := bstep (se 1 (by rfl) ⟨1770821, by rfl⟩ : syracuseStep 2361095 = 3541643) B3541643
theorem B3671837 : Blo 642303 3671837 := bstep (se 3 (by rfl) ⟨688469, by rfl⟩ : syracuseStep 3671837 = 1376939) B1376939
theorem B6620957 : Blo 642303 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B2066255 : Blo 642303 2066255 := bstep (se 1 (by rfl) ⟨1549691, by rfl⟩ : syracuseStep 2066255 = 3099383) B3099383
theorem B1967951 : Blo 642303 1967951 := bstep (se 1 (by rfl) ⟨1475963, by rfl⟩ : syracuseStep 1967951 = 2951927) B2951927
theorem B2066305 : Blo 642303 2066305 := bstep (se 2 (by rfl) ⟨774864, by rfl⟩ : syracuseStep 2066305 = 1549729) B1549729
theorem B5867639 : Blo 642303 5867639 := bstep (se 1 (by rfl) ⟨4400729, by rfl⟩ : syracuseStep 5867639 = 8801459) B8801459
theorem B1083935 : Blo 642303 1083935 := bstep (se 1 (by rfl) ⟨812951, by rfl⟩ : syracuseStep 1083935 = 1625903) B1625903
theorem B723487 : Blo 642303 723487 := bstep (se 1 (by rfl) ⟨542615, by rfl⟩ : syracuseStep 723487 = 1085231) B1085231
theorem B1084009 : Blo 642303 1084009 := bstep (se 2 (by rfl) ⟨406503, by rfl⟩ : syracuseStep 1084009 = 813007) B813007
theorem B2067049 : Blo 642303 2067049 := bstep (se 2 (by rfl) ⟨775143, by rfl⟩ : syracuseStep 2067049 = 1550287) B1550287
theorem B1837673 : Blo 642303 1837673 := bstep (se 2 (by rfl) ⟨689127, by rfl⟩ : syracuseStep 1837673 = 1378255) B1378255
theorem B1084367 : Blo 642303 1084367 := bstep (se 1 (by rfl) ⟨813275, by rfl⟩ : syracuseStep 1084367 = 1626551) B1626551
theorem B1085035 : Blo 642303 1085035 := bstep (se 1 (by rfl) ⟨813776, by rfl⟩ : syracuseStep 1085035 = 1627553) B1627553
theorem B3673795 : Blo 642303 3673795 := bstep (se 1 (by rfl) ⟨2755346, by rfl⟩ : syracuseStep 3673795 = 5510693) B5510693
theorem B1445651 : Blo 642303 1445651 := bstep (se 1 (by rfl) ⟨1084238, by rfl⟩ : syracuseStep 1445651 = 2168477) B2168477
theorem B1085305 : Blo 642303 1085305 := bstep (se 2 (by rfl) ⟨406989, by rfl⟩ : syracuseStep 1085305 = 813979) B813979
theorem B1085339 : Blo 642303 1085339 := bstep (se 1 (by rfl) ⟨814004, by rfl⟩ : syracuseStep 1085339 = 1628009) B1628009
theorem B1446011 : Blo 642303 1446011 := bstep (se 1 (by rfl) ⟨1084508, by rfl⟩ : syracuseStep 1446011 = 2169017) B2169017
theorem B31396025 : Blo 642303 31396025 := bstep (se 2 (by rfl) ⟨11773509, by rfl⟩ : syracuseStep 31396025 = 23547019) B23547019
theorem B3477725 : Blo 642303 3477725 := bstep (se 3 (by rfl) ⟨652073, by rfl⟩ : syracuseStep 3477725 = 1304147) B1304147
theorem B1446281 : Blo 642303 1446281 := bstep (se 2 (by rfl) ⟨542355, by rfl⟩ : syracuseStep 1446281 = 1084711) B1084711
theorem B6263203 : Blo 642303 6263203 := bstep (se 1 (by rfl) ⟨4697402, by rfl⟩ : syracuseStep 6263203 = 9394805) B9394805
theorem B14291639 : Blo 642303 14291639 := bstep (se 1 (by rfl) ⟨10718729, by rfl⟩ : syracuseStep 14291639 = 21437459) B21437459
theorem B2757671 : Blo 642303 2757671 := bstep (se 1 (by rfl) ⟨2068253, by rfl⟩ : syracuseStep 2757671 = 4136507) B4136507
theorem B1086527 : Blo 642303 1086527 := bstep (se 1 (by rfl) ⟨814895, by rfl⟩ : syracuseStep 1086527 = 1629791) B1629791
theorem B726079 : Blo 642303 726079 := bstep (se 1 (by rfl) ⟨544559, by rfl⟩ : syracuseStep 726079 = 1089119) B1089119
theorem B1447019 : Blo 642303 1447019 := bstep (se 1 (by rfl) ⟨1085264, by rfl⟩ : syracuseStep 1447019 = 2170529) B2170529
theorem B2757739 : Blo 642303 2757739 := bstep (se 1 (by rfl) ⟨2068304, by rfl⟩ : syracuseStep 2757739 = 4136609) B4136609
theorem B726223 : Blo 642303 726223 := bstep (se 1 (by rfl) ⟨544667, by rfl⟩ : syracuseStep 726223 = 1089335) B1089335
theorem B1545799 : Blo 642303 1545799 := bstep (se 1 (by rfl) ⟨1159349, by rfl⟩ : syracuseStep 1545799 = 2318699) B2318699
theorem B4134509 : Blo 642303 4134509 := bstep (se 3 (by rfl) ⟨775220, by rfl⟩ : syracuseStep 4134509 = 1550441) B1550441
theorem B1087087 : Blo 642303 1087087 := bstep (se 1 (by rfl) ⟨815315, by rfl⟩ : syracuseStep 1087087 = 1630631) B1630631
theorem B1447595 : Blo 642303 1447595 := bstep (se 1 (by rfl) ⟨1085696, by rfl⟩ : syracuseStep 1447595 = 2171393) B2171393
theorem B1087195 : Blo 642303 1087195 := bstep (se 1 (by rfl) ⟨815396, by rfl⟩ : syracuseStep 1087195 = 1630793) B1630793
theorem B2168639 : Blo 642303 2168639 := bstep (se 1 (by rfl) ⟨1626479, by rfl⟩ : syracuseStep 2168639 = 3252959) B3252959
theorem B1447919 : Blo 642303 1447919 := bstep (se 1 (by rfl) ⟨1085939, by rfl⟩ : syracuseStep 1447919 = 2171879) B2171879
theorem B7837721 : Blo 642303 7837721 := bstep (se 2 (by rfl) ⟨2939145, by rfl⟩ : syracuseStep 7837721 = 5878291) B5878291
theorem B1448135 : Blo 642303 1448135 := bstep (se 1 (by rfl) ⟨1086101, by rfl⟩ : syracuseStep 1448135 = 2172203) B2172203
theorem B2201899 : Blo 642303 2201899 := bstep (se 1 (by rfl) ⟨1651424, by rfl⟩ : syracuseStep 2201899 = 3302849) B3302849
theorem B1448315 : Blo 642303 1448315 := bstep (se 1 (by rfl) ⟨1086236, by rfl⟩ : syracuseStep 1448315 = 2172473) B2172473
theorem B12392909 : Blo 642303 12392909 := bstep (se 3 (by rfl) ⟨2323670, by rfl⟩ : syracuseStep 12392909 = 4647341) B4647341
theorem B1448585 : Blo 642303 1448585 := bstep (se 2 (by rfl) ⟨543219, by rfl⟩ : syracuseStep 1448585 = 1086439) B1086439
theorem B1743707 : Blo 642303 1743707 := bstep (se 1 (by rfl) ⟨1307780, by rfl⟩ : syracuseStep 1743707 = 2615561) B2615561
theorem B1088491 : Blo 642303 1088491 := bstep (se 1 (by rfl) ⟨816368, by rfl⟩ : syracuseStep 1088491 = 1632737) B1632737
theorem B1088633 : Blo 642303 1088633 := bstep (se 2 (by rfl) ⟨408237, by rfl⟩ : syracuseStep 1088633 = 816475) B816475
theorem B10460285 : Blo 642303 10460285 := bstep (se 3 (by rfl) ⟨1961303, by rfl⟩ : syracuseStep 10460285 = 3922607) B3922607
theorem B1449143 : Blo 642303 1449143 := bstep (se 1 (by rfl) ⟨1086857, by rfl⟩ : syracuseStep 1449143 = 2173715) B2173715
theorem B2170151 : Blo 642303 2170151 := bstep (se 1 (by rfl) ⟨1627613, by rfl⟩ : syracuseStep 2170151 = 3255227) B3255227
theorem B1219951 : Blo 642303 1219951 := bstep (se 1 (by rfl) ⟨914963, by rfl⟩ : syracuseStep 1219951 = 1829927) B1829927
theorem B1449719 : Blo 642303 1449719 := bstep (se 1 (by rfl) ⟨1087289, by rfl⟩ : syracuseStep 1449719 = 2174579) B2174579
theorem B1449899 : Blo 642303 1449899 := bstep (se 1 (by rfl) ⟨1087424, by rfl⟩ : syracuseStep 1449899 = 2174849) B2174849
theorem B2171015 : Blo 642303 2171015 := bstep (se 1 (by rfl) ⟨1628261, by rfl⟩ : syracuseStep 2171015 = 3256523) B3256523
theorem B1089767 : Blo 642303 1089767 := bstep (se 1 (by rfl) ⟨817325, by rfl⟩ : syracuseStep 1089767 = 1634651) B1634651
theorem B23765309 : Blo 642303 23765309 := bstep (se 3 (by rfl) ⟨4455995, by rfl⟩ : syracuseStep 23765309 = 8911991) B8911991
theorem B1089929 : Blo 642303 1089929 := bstep (se 2 (by rfl) ⟨408723, by rfl⟩ : syracuseStep 1089929 = 817447) B817447
theorem B1450439 : Blo 642303 1450439 := bstep (se 1 (by rfl) ⟨1087829, by rfl⟩ : syracuseStep 1450439 = 2175659) B2175659
theorem B1450799 : Blo 642303 1450799 := bstep (se 1 (by rfl) ⟨1088099, by rfl⟩ : syracuseStep 1450799 = 2176199) B2176199
theorem B1090361 : Blo 642303 1090361 := bstep (se 2 (by rfl) ⟨408885, by rfl⟩ : syracuseStep 1090361 = 817771) B817771
theorem B1090415 : Blo 642303 1090415 := bstep (se 1 (by rfl) ⟨817811, by rfl⟩ : syracuseStep 1090415 = 1635623) B1635623
theorem B3089771 : Blo 642303 3089771 := bstep (se 1 (by rfl) ⟨2317328, by rfl⟩ : syracuseStep 3089771 = 4634657) B4634657
theorem B2172527 : Blo 642303 2172527 := bstep (se 1 (by rfl) ⟨1629395, by rfl⟩ : syracuseStep 2172527 = 3258791) B3258791
theorem B8824439 : Blo 642303 8824439 := bstep (se 1 (by rfl) ⟨6618329, by rfl⟩ : syracuseStep 8824439 = 13236659) B13236659
theorem B2172635 : Blo 642303 2172635 := bstep (se 1 (by rfl) ⟨1629476, by rfl⟩ : syracuseStep 2172635 = 3258953) B3258953
theorem B1451807 : Blo 642303 1451807 := bstep (se 1 (by rfl) ⟨1088855, by rfl⟩ : syracuseStep 1451807 = 2177711) B2177711
theorem B32188265 : Blo 642303 32188265 := bstep (se 2 (by rfl) ⟨12070599, by rfl⟩ : syracuseStep 32188265 = 24141199) B24141199
theorem B1648631 : Blo 642303 1648631 := bstep (se 1 (by rfl) ⟨1236473, by rfl⟩ : syracuseStep 1648631 = 2472947) B2472947
theorem B1452023 : Blo 642303 1452023 := bstep (se 1 (by rfl) ⟨1089017, by rfl⟩ : syracuseStep 1452023 = 2178035) B2178035
theorem B3254417 : Blo 642303 3254417 := bstep (se 2 (by rfl) ⟨1220406, by rfl⟩ : syracuseStep 3254417 = 2440813) B2440813
theorem B1222951 : Blo 642303 1222951 := bstep (se 1 (by rfl) ⟨917213, by rfl⟩ : syracuseStep 1222951 = 1834427) B1834427
theorem B7448921 : Blo 642303 7448921 := bstep (se 2 (by rfl) ⟨2793345, by rfl⟩ : syracuseStep 7448921 = 5586691) B5586691
theorem B1452383 : Blo 642303 1452383 := bstep (se 1 (by rfl) ⟨1089287, by rfl⟩ : syracuseStep 1452383 = 2178575) B2178575
theorem B5220865 : Blo 642303 5220865 := bstep (se 2 (by rfl) ⟨1957824, by rfl⟩ : syracuseStep 5220865 = 3915649) B3915649
theorem B928361 : Blo 642303 928361 := bstep (se 2 (by rfl) ⟨348135, by rfl⟩ : syracuseStep 928361 = 696271) B696271
theorem B7351235 : Blo 642303 7351235 := bstep (se 1 (by rfl) ⟨5513426, by rfl⟩ : syracuseStep 7351235 = 11026853) B11026853
theorem B2173931 : Blo 642303 2173931 := bstep (se 1 (by rfl) ⟨1630448, by rfl⟩ : syracuseStep 2173931 = 3260897) B3260897
theorem B2173985 : Blo 642303 2173985 := bstep (se 2 (by rfl) ⟨815244, by rfl⟩ : syracuseStep 2173985 = 1630489) B1630489
theorem B1453103 : Blo 642303 1453103 := bstep (se 1 (by rfl) ⟨1089827, by rfl⟩ : syracuseStep 1453103 = 2179655) B2179655
theorem B2796665 : Blo 642303 2796665 := bstep (se 2 (by rfl) ⟨1048749, by rfl⟩ : syracuseStep 2796665 = 2097499) B2097499
theorem B1453391 : Blo 642303 1453391 := bstep (se 1 (by rfl) ⟨1090043, by rfl⟩ : syracuseStep 1453391 = 2180087) B2180087
theorem B1453481 : Blo 642303 1453481 := bstep (se 2 (by rfl) ⟨545055, by rfl⟩ : syracuseStep 1453481 = 1090111) B1090111
theorem B4140659 : Blo 642303 4140659 := bstep (se 1 (by rfl) ⟨3105494, by rfl⟩ : syracuseStep 4140659 = 6210989) B6210989
theorem B16494353 : Blo 642303 16494353 := bstep (se 2 (by rfl) ⟨6185382, by rfl⟩ : syracuseStep 16494353 = 12370765) B12370765
theorem B4894505 : Blo 642303 4894505 := bstep (se 2 (by rfl) ⟨1835439, by rfl⟩ : syracuseStep 4894505 = 3670879) B3670879
theorem B1453967 : Blo 642303 1453967 := bstep (se 1 (by rfl) ⟨1090475, by rfl⟩ : syracuseStep 1453967 = 2180951) B2180951
theorem B4632785 : Blo 642303 4632785 := bstep (se 2 (by rfl) ⟨1737294, by rfl⟩ : syracuseStep 4632785 = 3474589) B3474589
theorem B6173081 : Blo 642303 6173081 := bstep (se 2 (by rfl) ⟨2314905, by rfl⟩ : syracuseStep 6173081 = 4629811) B4629811
theorem B2175443 : Blo 642303 2175443 := bstep (se 1 (by rfl) ⟨1631582, by rfl⟩ : syracuseStep 2175443 = 3263165) B3263165
theorem B4698593 : Blo 642303 4698593 := bstep (se 2 (by rfl) ⟨1761972, by rfl⟩ : syracuseStep 4698593 = 3523945) B3523945
theorem B3256847 : Blo 642303 3256847 := bstep (se 1 (by rfl) ⟨2442635, by rfl⟩ : syracuseStep 3256847 = 4885271) B4885271
theorem B1225783 : Blo 642303 1225783 := bstep (se 1 (by rfl) ⟨919337, by rfl⟩ : syracuseStep 1225783 = 1838675) B1838675
theorem B963647 : Blo 642303 963647 := bstep (se 1 (by rfl) ⟨722735, by rfl⟩ : syracuseStep 963647 = 1445471) B1445471
theorem B963689 : Blo 642303 963689 := bstep (se 2 (by rfl) ⟨361383, by rfl⟩ : syracuseStep 963689 = 722767) B722767
theorem B963791 : Blo 642303 963791 := bstep (se 1 (by rfl) ⟨722843, by rfl⟩ : syracuseStep 963791 = 1445687) B1445687
theorem B963995 : Blo 642303 963995 := bstep (se 1 (by rfl) ⟨722996, by rfl⟩ : syracuseStep 963995 = 1445993) B1445993
theorem B964217 : Blo 642303 964217 := bstep (se 2 (by rfl) ⟨361581, by rfl⟩ : syracuseStep 964217 = 723163) B723163
theorem B2209451 : Blo 642303 2209451 := bstep (se 1 (by rfl) ⟨1657088, by rfl⟩ : syracuseStep 2209451 = 3314177) B3314177
theorem B7452371 : Blo 642303 7452371 := bstep (se 1 (by rfl) ⟨5589278, by rfl⟩ : syracuseStep 7452371 = 11178557) B11178557
theorem B964319 : Blo 642303 964319 := bstep (se 1 (by rfl) ⟨723239, by rfl⟩ : syracuseStep 964319 = 1446479) B1446479
theorem B964415 : Blo 642303 964415 := bstep (se 1 (by rfl) ⟨723311, by rfl⟩ : syracuseStep 964415 = 1446623) B1446623
theorem B964583 : Blo 642303 964583 := bstep (se 1 (by rfl) ⟨723437, by rfl⟩ : syracuseStep 964583 = 1446875) B1446875
theorem B964601 : Blo 642303 964601 := bstep (se 2 (by rfl) ⟨361725, by rfl⟩ : syracuseStep 964601 = 723451) B723451
theorem B964703 : Blo 642303 964703 := bstep (se 1 (by rfl) ⟨723527, by rfl⟩ : syracuseStep 964703 = 1447055) B1447055
theorem B964763 : Blo 642303 964763 := bstep (se 1 (by rfl) ⟨723572, by rfl⟩ : syracuseStep 964763 = 1447145) B1447145
theorem B964799 : Blo 642303 964799 := bstep (se 1 (by rfl) ⟨723599, by rfl⟩ : syracuseStep 964799 = 1447199) B1447199
theorem B964841 : Blo 642303 964841 := bstep (se 2 (by rfl) ⟨361815, by rfl⟩ : syracuseStep 964841 = 723631) B723631
theorem B2177387 : Blo 642303 2177387 := bstep (se 1 (by rfl) ⟨1633040, by rfl⟩ : syracuseStep 2177387 = 3266081) B3266081
theorem B965147 : Blo 642303 965147 := bstep (se 1 (by rfl) ⟨723860, by rfl⟩ : syracuseStep 965147 = 1447721) B1447721
theorem B965225 : Blo 642303 965225 := bstep (se 2 (by rfl) ⟨361959, by rfl⟩ : syracuseStep 965225 = 723919) B723919
theorem B2177657 : Blo 642303 2177657 := bstep (se 2 (by rfl) ⟨816621, by rfl⟩ : syracuseStep 2177657 = 1633243) B1633243
theorem B1391519 : Blo 642303 1391519 := bstep (se 1 (by rfl) ⟨1043639, by rfl⟩ : syracuseStep 1391519 = 2087279) B2087279
theorem B55098299 : Blo 642303 55098299 := bstep (se 1 (by rfl) ⟨41323724, by rfl⟩ : syracuseStep 55098299 = 82647449) B82647449
theorem B2178089 : Blo 642303 2178089 := bstep (se 2 (by rfl) ⟨816783, by rfl⟩ : syracuseStep 2178089 = 1633567) B1633567
theorem B965753 : Blo 642303 965753 := bstep (se 2 (by rfl) ⟨362157, by rfl⟩ : syracuseStep 965753 = 724315) B724315
theorem B965855 : Blo 642303 965855 := bstep (se 1 (by rfl) ⟨724391, by rfl⟩ : syracuseStep 965855 = 1448783) B1448783
theorem B965897 : Blo 642303 965897 := bstep (se 2 (by rfl) ⟨362211, by rfl⟩ : syracuseStep 965897 = 724423) B724423
theorem B965999 : Blo 642303 965999 := bstep (se 1 (by rfl) ⟨724499, by rfl⟩ : syracuseStep 965999 = 1448999) B1448999
theorem B966119 : Blo 642303 966119 := bstep (se 1 (by rfl) ⟨724589, by rfl⟩ : syracuseStep 966119 = 1449179) B1449179
theorem B47037995 : Blo 642303 47037995 := bstep (se 1 (by rfl) ⟨35278496, by rfl⟩ : syracuseStep 47037995 = 70556993) B70556993
theorem B966251 : Blo 642303 966251 := bstep (se 1 (by rfl) ⟨724688, by rfl⟩ : syracuseStep 966251 = 1449377) B1449377
theorem B5521081 : Blo 642303 5521081 := bstep (se 2 (by rfl) ⟨2070405, by rfl⟩ : syracuseStep 5521081 = 4140811) B4140811
theorem B966377 : Blo 642303 966377 := bstep (se 2 (by rfl) ⟨362391, by rfl⟩ : syracuseStep 966377 = 724783) B724783
theorem B966521 : Blo 642303 966521 := bstep (se 2 (by rfl) ⟨362445, by rfl⟩ : syracuseStep 966521 = 724891) B724891
theorem B966623 : Blo 642303 966623 := bstep (se 1 (by rfl) ⟨724967, by rfl⟩ : syracuseStep 966623 = 1449935) B1449935
theorem B966875 : Blo 642303 966875 := bstep (se 1 (by rfl) ⟨725156, by rfl⟩ : syracuseStep 966875 = 1450313) B1450313
theorem B966887 : Blo 642303 966887 := bstep (se 1 (by rfl) ⟨725165, by rfl⟩ : syracuseStep 966887 = 1450331) B1450331
theorem B967049 : Blo 642303 967049 := bstep (se 2 (by rfl) ⟨362643, by rfl⟩ : syracuseStep 967049 = 725287) B725287
theorem B967145 : Blo 642303 967145 := bstep (se 2 (by rfl) ⟨362679, by rfl⟩ : syracuseStep 967145 = 725359) B725359
theorem B79577585 : Blo 642303 79577585 := bstep (se 2 (by rfl) ⟨29841594, by rfl⟩ : syracuseStep 79577585 = 59683189) B59683189
theorem B967271 : Blo 642303 967271 := bstep (se 1 (by rfl) ⟨725453, by rfl⟩ : syracuseStep 967271 = 1450907) B1450907
theorem B967403 : Blo 642303 967403 := bstep (se 1 (by rfl) ⟨725552, by rfl⟩ : syracuseStep 967403 = 1451105) B1451105
theorem B967433 : Blo 642303 967433 := bstep (se 2 (by rfl) ⟨362787, by rfl⟩ : syracuseStep 967433 = 725575) B725575
theorem B967535 : Blo 642303 967535 := bstep (se 1 (by rfl) ⟨725651, by rfl⟩ : syracuseStep 967535 = 1451303) B1451303
theorem B13190039 : Blo 642303 13190039 := bstep (se 1 (by rfl) ⟨9892529, by rfl⟩ : syracuseStep 13190039 = 19785059) B19785059
theorem B3261545 : Blo 642303 3261545 := bstep (se 2 (by rfl) ⟨1223079, by rfl⟩ : syracuseStep 3261545 = 2446159) B2446159
theorem B967787 : Blo 642303 967787 := bstep (se 1 (by rfl) ⟨725840, by rfl⟩ : syracuseStep 967787 = 1451681) B1451681
theorem B8275061 : Blo 642303 8275061 := bstep (se 5 (by rfl) ⟨387893, by rfl⟩ : syracuseStep 8275061 = 775787) B775787
theorem B2180303 : Blo 642303 2180303 := bstep (se 1 (by rfl) ⟨1635227, by rfl⟩ : syracuseStep 2180303 = 3270455) B3270455
theorem B3261707 : Blo 642303 3261707 := bstep (se 1 (by rfl) ⟨2446280, by rfl⟩ : syracuseStep 3261707 = 4892561) B4892561
theorem B968027 : Blo 642303 968027 := bstep (se 1 (by rfl) ⟨726020, by rfl⟩ : syracuseStep 968027 = 1452041) B1452041
theorem B2180627 : Blo 642303 2180627 := bstep (se 1 (by rfl) ⟨1635470, by rfl⟩ : syracuseStep 2180627 = 3270941) B3270941
theorem B968303 : Blo 642303 968303 := bstep (se 1 (by rfl) ⟨726227, by rfl⟩ : syracuseStep 968303 = 1452455) B1452455
theorem B968375 : Blo 642303 968375 := bstep (se 1 (by rfl) ⟨726281, by rfl⟩ : syracuseStep 968375 = 1452563) B1452563
theorem B968411 : Blo 642303 968411 := bstep (se 1 (by rfl) ⟨726308, by rfl⟩ : syracuseStep 968411 = 1452617) B1452617
theorem B968585 : Blo 642303 968585 := bstep (se 2 (by rfl) ⟨363219, by rfl⟩ : syracuseStep 968585 = 726439) B726439
theorem B968687 : Blo 642303 968687 := bstep (se 1 (by rfl) ⟨726515, by rfl⟩ : syracuseStep 968687 = 1453031) B1453031
theorem B5490737 : Blo 642303 5490737 := bstep (se 2 (by rfl) ⟨2059026, by rfl⟩ : syracuseStep 5490737 = 4118053) B4118053
theorem B968939 : Blo 642303 968939 := bstep (se 1 (by rfl) ⟨726704, by rfl⟩ : syracuseStep 968939 = 1453409) B1453409
theorem B968999 : Blo 642303 968999 := bstep (se 1 (by rfl) ⟨726749, by rfl⟩ : syracuseStep 968999 = 1453499) B1453499
theorem B969083 : Blo 642303 969083 := bstep (se 1 (by rfl) ⟨726812, by rfl⟩ : syracuseStep 969083 = 1453625) B1453625
theorem B969353 : Blo 642303 969353 := bstep (se 2 (by rfl) ⟨363507, by rfl⟩ : syracuseStep 969353 = 727015) B727015
theorem B3263327 : Blo 642303 3263327 := bstep (se 1 (by rfl) ⟨2447495, by rfl⟩ : syracuseStep 3263327 = 4894991) B4894991
theorem B4902281 : Blo 642303 4902281 := bstep (se 2 (by rfl) ⟨1838355, by rfl⟩ : syracuseStep 4902281 = 3676711) B3676711
theorem B1101223 : Blo 642303 1101223 := bstep (se 1 (by rfl) ⟨825917, by rfl⟩ : syracuseStep 1101223 = 1651835) B1651835
theorem B642535 : Blo 642303 642535 := bstep (se 1 (by rfl) ⟨481901, by rfl⟩ : syracuseStep 642535 = 963803) B963803
theorem B642651 : Blo 642303 642651 := bstep (se 1 (by rfl) ⟨481988, by rfl⟩ : syracuseStep 642651 = 963977) B963977
theorem B2444975 : Blo 642303 2444975 := bstep (se 1 (by rfl) ⟨1833731, by rfl⟩ : syracuseStep 2444975 = 3667463) B3667463
theorem B642887 : Blo 642303 642887 := bstep (se 1 (by rfl) ⟨482165, by rfl⟩ : syracuseStep 642887 = 964331) B964331
theorem B643039 : Blo 642303 643039 := bstep (se 1 (by rfl) ⟨482279, by rfl⟩ : syracuseStep 643039 = 964559) B964559
theorem B643303 : Blo 642303 643303 := bstep (se 1 (by rfl) ⟨482477, by rfl⟩ : syracuseStep 643303 = 964955) B964955
theorem B643455 : Blo 642303 643455 := bstep (se 1 (by rfl) ⟨482591, by rfl⟩ : syracuseStep 643455 = 965183) B965183
theorem B643535 : Blo 642303 643535 := bstep (se 1 (by rfl) ⟨482651, by rfl⟩ : syracuseStep 643535 = 965303) B965303
theorem B643687 : Blo 642303 643687 := bstep (se 1 (by rfl) ⟨482765, by rfl⟩ : syracuseStep 643687 = 965531) B965531
theorem B3101287 : Blo 642303 3101287 := bstep (se 1 (by rfl) ⟨2325965, by rfl⟩ : syracuseStep 3101287 = 4651931) B4651931
theorem B1626905 : Blo 642303 1626905 := bstep (se 2 (by rfl) ⟨610089, by rfl⟩ : syracuseStep 1626905 = 1220179) B1220179
theorem B643951 : Blo 642303 643951 := bstep (se 1 (by rfl) ⟨482963, by rfl⟩ : syracuseStep 643951 = 965927) B965927
theorem B2315137 : Blo 642303 2315137 := bstep (se 2 (by rfl) ⟨868176, by rfl⟩ : syracuseStep 2315137 = 1736353) B1736353
theorem B644007 : Blo 642303 644007 := bstep (se 1 (by rfl) ⟨483005, by rfl⟩ : syracuseStep 644007 = 966011) B966011
theorem B3658715 : Blo 642303 3658715 := bstep (se 1 (by rfl) ⟨2744036, by rfl⟩ : syracuseStep 3658715 = 5488073) B5488073
theorem B3527675 : Blo 642303 3527675 := bstep (se 1 (by rfl) ⟨2645756, by rfl⟩ : syracuseStep 3527675 = 5291513) B5291513
theorem B644091 : Blo 642303 644091 := bstep (se 1 (by rfl) ⟨483068, by rfl⟩ : syracuseStep 644091 = 966137) B966137
theorem B1627199 : Blo 642303 1627199 := bstep (se 1 (by rfl) ⟨1220399, by rfl⟩ : syracuseStep 1627199 = 2440799) B2440799
theorem B644159 : Blo 642303 644159 := bstep (se 1 (by rfl) ⟨483119, by rfl⟩ : syracuseStep 644159 = 966239) B966239
theorem B644303 : Blo 642303 644303 := bstep (se 1 (by rfl) ⟨483227, by rfl⟩ : syracuseStep 644303 = 966455) B966455
theorem B2315483 : Blo 642303 2315483 := bstep (se 1 (by rfl) ⟨1736612, by rfl⟩ : syracuseStep 2315483 = 3473225) B3473225
theorem B1627411 : Blo 642303 1627411 := bstep (se 1 (by rfl) ⟨1220558, by rfl⟩ : syracuseStep 1627411 = 2441117) B2441117
theorem B3298657 : Blo 642303 3298657 := bstep (se 2 (by rfl) ⟨1236996, by rfl⟩ : syracuseStep 3298657 = 2473993) B2473993
theorem B3724663 : Blo 642303 3724663 := bstep (se 1 (by rfl) ⟨2793497, by rfl⟩ : syracuseStep 3724663 = 5586995) B5586995
theorem B13391243 : Blo 642303 13391243 := bstep (se 1 (by rfl) ⟨10043432, by rfl⟩ : syracuseStep 13391243 = 20086865) B20086865
theorem B644507 : Blo 642303 644507 := bstep (se 1 (by rfl) ⟨483380, by rfl⟩ : syracuseStep 644507 = 966761) B966761
theorem B644719 : Blo 642303 644719 := bstep (se 1 (by rfl) ⟨483539, by rfl⟩ : syracuseStep 644719 = 967079) B967079
theorem B644775 : Blo 642303 644775 := bstep (se 1 (by rfl) ⟨483581, by rfl⟩ : syracuseStep 644775 = 967163) B967163
theorem B644859 : Blo 642303 644859 := bstep (se 1 (by rfl) ⟨483644, by rfl⟩ : syracuseStep 644859 = 967289) B967289
theorem B644895 : Blo 642303 644895 := bstep (se 1 (by rfl) ⟨483671, by rfl⟩ : syracuseStep 644895 = 967343) B967343
theorem B644927 : Blo 642303 644927 := bstep (se 1 (by rfl) ⟨483695, by rfl⟩ : syracuseStep 644927 = 967391) B967391
theorem B645103 : Blo 642303 645103 := bstep (se 1 (by rfl) ⟨483827, by rfl⟩ : syracuseStep 645103 = 967655) B967655
theorem B776287 : Blo 642303 776287 := bstep (se 1 (by rfl) ⟨582215, by rfl⟩ : syracuseStep 776287 = 1164431) B1164431
theorem B645275 : Blo 642303 645275 := bstep (se 1 (by rfl) ⟨483956, by rfl⟩ : syracuseStep 645275 = 967913) B967913
theorem B645311 : Blo 642303 645311 := bstep (se 1 (by rfl) ⟨483983, by rfl⟩ : syracuseStep 645311 = 967967) B967967
theorem B2316521 : Blo 642303 2316521 := bstep (se 2 (by rfl) ⟨868695, by rfl⟩ : syracuseStep 2316521 = 1737391) B1737391
theorem B2447603 : Blo 642303 2447603 := bstep (se 1 (by rfl) ⟨1835702, by rfl⟩ : syracuseStep 2447603 = 3671405) B3671405
theorem B645423 : Blo 642303 645423 := bstep (se 1 (by rfl) ⟨484067, by rfl⟩ : syracuseStep 645423 = 968135) B968135
theorem B7428631 : Blo 642303 7428631 := bstep (se 1 (by rfl) ⟨5571473, by rfl⟩ : syracuseStep 7428631 = 11142947) B11142947
theorem B645659 : Blo 642303 645659 := bstep (se 1 (by rfl) ⟨484244, by rfl⟩ : syracuseStep 645659 = 968489) B968489
theorem B645663 : Blo 642303 645663 := bstep (se 1 (by rfl) ⟨484247, by rfl⟩ : syracuseStep 645663 = 968495) B968495
theorem B1629011 : Blo 642303 1629011 := bstep (se 1 (by rfl) ⟨1221758, by rfl⟩ : syracuseStep 1629011 = 2443517) B2443517
theorem B645979 : Blo 642303 645979 := bstep (se 1 (by rfl) ⟨484484, by rfl⟩ : syracuseStep 645979 = 968969) B968969
theorem B646047 : Blo 642303 646047 := bstep (se 1 (by rfl) ⟨484535, by rfl⟩ : syracuseStep 646047 = 969071) B969071
theorem B646191 : Blo 642303 646191 := bstep (se 1 (by rfl) ⟨484643, by rfl⟩ : syracuseStep 646191 = 969287) B969287
theorem B646215 : Blo 642303 646215 := bstep (se 1 (by rfl) ⟨484661, by rfl⟩ : syracuseStep 646215 = 969323) B969323
theorem B3660947 : Blo 642303 3660947 := bstep (se 1 (by rfl) ⟨2745710, by rfl⟩ : syracuseStep 3660947 = 5491421) B5491421
theorem B4710167 : Blo 642303 4710167 := bstep (se 1 (by rfl) ⟨3532625, by rfl⟩ : syracuseStep 4710167 = 7065251) B7065251
theorem B1630439 : Blo 642303 1630439 := bstep (se 1 (by rfl) ⟨1222829, by rfl⟩ : syracuseStep 1630439 = 2445659) B2445659
theorem B2941265 : Blo 642303 2941265 := bstep (se 2 (by rfl) ⟨1102974, by rfl⟩ : syracuseStep 2941265 = 2205949) B2205949
theorem B161014169 : Blo 642303 161014169 := bstep (se 2 (by rfl) ⟨60380313, by rfl⟩ : syracuseStep 161014169 = 120760627) B120760627
theorem B1630651 : Blo 642303 1630651 := bstep (se 1 (by rfl) ⟨1222988, by rfl⟩ : syracuseStep 1630651 = 2445977) B2445977
theorem B1630955 : Blo 642303 1630955 := bstep (se 1 (by rfl) ⟨1223216, by rfl⟩ : syracuseStep 1630955 = 2446433) B2446433
theorem B3105533 : Blo 642303 3105533 := bstep (se 3 (by rfl) ⟨582287, by rfl⟩ : syracuseStep 3105533 = 1164575) B1164575
theorem B1631087 : Blo 642303 1631087 := bstep (se 1 (by rfl) ⟨1223315, by rfl⟩ : syracuseStep 1631087 = 2446631) B2446631
theorem B11035601 : Blo 642303 11035601 := bstep (se 2 (by rfl) ⟨4138350, by rfl⟩ : syracuseStep 11035601 = 8276701) B8276701
theorem B8250457 : Blo 642303 8250457 := bstep (se 2 (by rfl) ⟨3093921, by rfl⟩ : syracuseStep 8250457 = 6187843) B6187843
theorem B3728591 : Blo 642303 3728591 := bstep (se 1 (by rfl) ⟨2796443, by rfl⟩ : syracuseStep 3728591 = 5592887) B5592887
theorem B25748941 : Blo 642303 25748941 := bstep (se 3 (by rfl) ⟨4827926, by rfl⟩ : syracuseStep 25748941 = 9655853) B9655853
theorem B3728911 : Blo 642303 3728911 := bstep (se 1 (by rfl) ⟨2796683, by rfl⟩ : syracuseStep 3728911 = 5593367) B5593367
theorem B2057849 : Blo 642303 2057849 := bstep (se 2 (by rfl) ⟨771693, by rfl⟩ : syracuseStep 2057849 = 1543387) B1543387
theorem B1861339 : Blo 642303 1861339 := bstep (se 1 (by rfl) ⟨1396004, by rfl⟩ : syracuseStep 1861339 = 2792009) B2792009
theorem B3663863 : Blo 642303 3663863 := bstep (se 1 (by rfl) ⟨2747897, by rfl⟩ : syracuseStep 3663863 = 5495795) B5495795
theorem B2517101 : Blo 642303 2517101 := bstep (se 3 (by rfl) ⟨471956, by rfl⟩ : syracuseStep 2517101 = 943913) B943913
theorem B2320903 : Blo 642303 2320903 := bstep (se 1 (by rfl) ⟨1740677, by rfl⟩ : syracuseStep 2320903 = 3481355) B3481355
theorem B1305119 : Blo 642303 1305119 := bstep (se 1 (by rfl) ⟨978839, by rfl⟩ : syracuseStep 1305119 = 1957679) B1957679
theorem B4123385 : Blo 642303 4123385 := bstep (se 2 (by rfl) ⟨1546269, by rfl⟩ : syracuseStep 4123385 = 3092539) B3092539
theorem B9431801 : Blo 642303 9431801 := bstep (se 2 (by rfl) ⟨3536925, by rfl⟩ : syracuseStep 9431801 = 7073851) B7073851
theorem B2092007 : Blo 642303 2092007 := bstep (se 1 (by rfl) ⟨1569005, by rfl⟩ : syracuseStep 2092007 = 3138011) B3138011
theorem B814151 : Blo 642303 814151 := bstep (se 1 (by rfl) ⟨610613, by rfl⟩ : syracuseStep 814151 = 1221227) B1221227
theorem B814303 : Blo 642303 814303 := bstep (se 1 (by rfl) ⟨610727, by rfl⟩ : syracuseStep 814303 = 1221455) B1221455
theorem B3271913 : Blo 642303 3271913 := bstep (se 2 (by rfl) ⟨1226967, by rfl⟩ : syracuseStep 3271913 = 2453935) B2453935
theorem B16772599 : Blo 642303 16772599 := bstep (se 1 (by rfl) ⟨12579449, by rfl⟩ : syracuseStep 16772599 = 25158899) B25158899
theorem B978523 : Blo 642303 978523 := bstep (se 1 (by rfl) ⟨733892, by rfl⟩ : syracuseStep 978523 = 1467785) B1467785
theorem B2453267 : Blo 642303 2453267 := bstep (se 1 (by rfl) ⟨1839950, by rfl⟩ : syracuseStep 2453267 = 3679901) B3679901
theorem B4124591 : Blo 642303 4124591 := bstep (se 1 (by rfl) ⟨3093443, by rfl⟩ : syracuseStep 4124591 = 6186887) B6186887
theorem B2323039 : Blo 642303 2323039 := bstep (se 1 (by rfl) ⟨1742279, by rfl⟩ : syracuseStep 2323039 = 3484559) B3484559
theorem B152466137 : Blo 642303 152466137 := bstep (se 2 (by rfl) ⟨57174801, by rfl⟩ : syracuseStep 152466137 = 114349603) B114349603
theorem B2061487 : Blo 642303 2061487 := bstep (se 1 (by rfl) ⟨1546115, by rfl⟩ : syracuseStep 2061487 = 3092231) B3092231
theorem B31782203 : Blo 642303 31782203 := bstep (se 1 (by rfl) ⟨23836652, by rfl⟩ : syracuseStep 31782203 = 47673305) B47673305
theorem B4126459 : Blo 642303 4126459 := bstep (se 1 (by rfl) ⟨3094844, by rfl⟩ : syracuseStep 4126459 = 6189689) B6189689
theorem B2062091 : Blo 642303 2062091 := bstep (se 1 (by rfl) ⟨1546568, by rfl⟩ : syracuseStep 2062091 = 3093137) B3093137
theorem B1243279 : Blo 642303 1243279 := bstep (se 1 (by rfl) ⟨932459, by rfl⟩ : syracuseStep 1243279 = 1864919) B1864919
theorem B8813929 : Blo 642303 8813929 := bstep (se 2 (by rfl) ⟨3305223, by rfl⟩ : syracuseStep 8813929 = 6610447) B6610447
theorem B1179049 : Blo 642303 1179049 := bstep (se 2 (by rfl) ⟨442143, by rfl⟩ : syracuseStep 1179049 = 884287) B884287
theorem B5865227 : Blo 642303 5865227 := bstep (se 1 (by rfl) ⟨4398920, by rfl⟩ : syracuseStep 5865227 = 8797841) B8797841
theorem B1376443 : Blo 642303 1376443 := bstep (se 1 (by rfl) ⟨1032332, by rfl⟩ : syracuseStep 1376443 = 2064665) B2064665
theorem B53051723 : Blo 642303 53051723 := bstep (se 1 (by rfl) ⟨39788792, by rfl⟩ : syracuseStep 53051723 = 79577585) B79577585
theorem B8389423 : Blo 642303 8389423 := bstep (se 1 (by rfl) ⟨6292067, by rfl⟩ : syracuseStep 8389423 = 12584135) B12584135
theorem B1574063 : Blo 642303 1574063 := bstep (se 1 (by rfl) ⟨1180547, by rfl⟩ : syracuseStep 1574063 = 2361095) B2361095
theorem B1377503 : Blo 642303 1377503 := bstep (se 1 (by rfl) ⟨1033127, by rfl⟩ : syracuseStep 1377503 = 2066255) B2066255
theorem B1311967 : Blo 642303 1311967 := bstep (se 1 (by rfl) ⟨983975, by rfl⟩ : syracuseStep 1311967 = 1967951) B1967951
theorem B722623 : Blo 642303 722623 := bstep (se 1 (by rfl) ⟨541967, by rfl⟩ : syracuseStep 722623 = 1083935) B1083935
theorem B20875157 : Blo 642303 20875157 := bstep (se 6 (by rfl) ⟨489261, by rfl⟩ : syracuseStep 20875157 = 978523) B978523
theorem B722911 : Blo 642303 722911 := bstep (se 1 (by rfl) ⟨542183, by rfl⟩ : syracuseStep 722911 = 1084367) B1084367
theorem B1837217 : Blo 642303 1837217 := bstep (se 2 (by rfl) ⟨688956, by rfl⟩ : syracuseStep 1837217 = 1377913) B1377913
theorem B2755073 : Blo 642303 2755073 := bstep (se 2 (by rfl) ⟨1033152, by rfl⟩ : syracuseStep 2755073 = 2066305) B2066305
theorem B723559 : Blo 642303 723559 := bstep (se 1 (by rfl) ⟨542669, by rfl⟩ : syracuseStep 723559 = 1085339) B1085339
theorem B1084603 : Blo 642303 1084603 := bstep (se 1 (by rfl) ⟨813452, by rfl⟩ : syracuseStep 1084603 = 1626905) B1626905
theorem B1838447 : Blo 642303 1838447 := bstep (se 1 (by rfl) ⟨1378835, by rfl⟩ : syracuseStep 1838447 = 2757671) B2757671
theorem B1084799 : Blo 642303 1084799 := bstep (se 1 (by rfl) ⟨813599, by rfl⟩ : syracuseStep 1084799 = 1627199) B1627199
theorem B724351 : Blo 642303 724351 := bstep (se 1 (by rfl) ⟨543263, by rfl⟩ : syracuseStep 724351 = 1086527) B1086527
theorem B1445345 : Blo 642303 1445345 := bstep (se 2 (by rfl) ⟨542004, by rfl⟩ : syracuseStep 1445345 = 1084009) B1084009
theorem B2756065 : Blo 642303 2756065 := bstep (se 2 (by rfl) ⟨1033524, by rfl⟩ : syracuseStep 2756065 = 2067049) B2067049
theorem B1543655 : Blo 642303 1543655 := bstep (se 1 (by rfl) ⟨1157741, by rfl⟩ : syracuseStep 1543655 = 2315483) B2315483
theorem B2756339 : Blo 642303 2756339 := bstep (se 1 (by rfl) ⟨2067254, by rfl⟩ : syracuseStep 2756339 = 4134509) B4134509
theorem B1445759 : Blo 642303 1445759 := bstep (se 1 (by rfl) ⟨1084319, by rfl⟩ : syracuseStep 1445759 = 2168639) B2168639
theorem B1544347 : Blo 642303 1544347 := bstep (se 1 (by rfl) ⟨1158260, by rfl⟩ : syracuseStep 1544347 = 2316521) B2316521
theorem B1085737 : Blo 642303 1085737 := bstep (se 2 (by rfl) ⟨407151, by rfl⟩ : syracuseStep 1085737 = 814303) B814303
theorem B8261939 : Blo 642303 8261939 := bstep (se 1 (by rfl) ⟨6196454, by rfl⟩ : syracuseStep 8261939 = 12392909) B12392909
theorem B1086007 : Blo 642303 1086007 := bstep (se 1 (by rfl) ⟨814505, by rfl⟩ : syracuseStep 1086007 = 1629011) B1629011
theorem B725755 : Blo 642303 725755 := bstep (se 1 (by rfl) ⟨544316, by rfl⟩ : syracuseStep 725755 = 1088633) B1088633
theorem B1446713 : Blo 642303 1446713 := bstep (se 2 (by rfl) ⟨542517, by rfl⟩ : syracuseStep 1446713 = 1085035) B1085035
theorem B1446767 : Blo 642303 1446767 := bstep (se 1 (by rfl) ⟨1085075, by rfl⟩ : syracuseStep 1446767 = 2170151) B2170151
theorem B1447073 : Blo 642303 1447073 := bstep (se 2 (by rfl) ⟨542652, by rfl⟩ : syracuseStep 1447073 = 1085305) B1085305
theorem B4396349 : Blo 642303 4396349 := bstep (se 3 (by rfl) ⟨824315, by rfl⟩ : syracuseStep 4396349 = 1648631) B1648631
theorem B1447343 : Blo 642303 1447343 := bstep (se 1 (by rfl) ⟨1085507, by rfl⟩ : syracuseStep 1447343 = 2171015) B2171015
theorem B1086959 : Blo 642303 1086959 := bstep (se 1 (by rfl) ⟨815219, by rfl⟩ : syracuseStep 1086959 = 1630439) B1630439
theorem B726511 : Blo 642303 726511 := bstep (se 1 (by rfl) ⟨544883, by rfl⟩ : syracuseStep 726511 = 1089767) B1089767
theorem B726619 : Blo 642303 726619 := bstep (se 1 (by rfl) ⟨544964, by rfl⟩ : syracuseStep 726619 = 1089929) B1089929
theorem B1087303 : Blo 642303 1087303 := bstep (se 1 (by rfl) ⟨815477, by rfl⟩ : syracuseStep 1087303 = 1630955) B1630955
theorem B2070355 : Blo 642303 2070355 := bstep (se 1 (by rfl) ⟨1552766, by rfl⟩ : syracuseStep 2070355 = 3105533) B3105533
theorem B726907 : Blo 642303 726907 := bstep (se 1 (by rfl) ⟨545180, by rfl⟩ : syracuseStep 726907 = 1090361) B1090361
theorem B1087391 : Blo 642303 1087391 := bstep (se 1 (by rfl) ⟨815543, by rfl⟩ : syracuseStep 1087391 = 1631087) B1631087
theorem B726943 : Blo 642303 726943 := bstep (se 1 (by rfl) ⟨545207, by rfl⟩ : syracuseStep 726943 = 1090415) B1090415
theorem B4135049 : Blo 642303 4135049 := bstep (se 2 (by rfl) ⟨1550643, by rfl⟩ : syracuseStep 4135049 = 3101287) B3101287
theorem B1448351 : Blo 642303 1448351 := bstep (se 1 (by rfl) ⟨1086263, by rfl⟩ : syracuseStep 1448351 = 2172527) B2172527
theorem B1448423 : Blo 642303 1448423 := bstep (se 1 (by rfl) ⟨1086317, by rfl⟩ : syracuseStep 1448423 = 2172635) B2172635
theorem B3086849 : Blo 642303 3086849 := bstep (se 2 (by rfl) ⟨1157568, by rfl⟩ : syracuseStep 3086849 = 2315137) B2315137
theorem B1678067 : Blo 642303 1678067 := bstep (se 1 (by rfl) ⟨1258550, by rfl⟩ : syracuseStep 1678067 = 2517101) B2517101
theorem B3480317 : Blo 642303 3480317 := bstep (se 3 (by rfl) ⟨652559, by rfl⟩ : syracuseStep 3480317 = 1305119) B1305119
theorem B2169611 : Blo 642303 2169611 := bstep (se 1 (by rfl) ⟨1627208, by rfl⟩ : syracuseStep 2169611 = 3254417) B3254417
theorem B3676985 : Blo 642303 3676985 := bstep (se 2 (by rfl) ⟨1378869, by rfl⟩ : syracuseStep 3676985 = 2757739) B2757739
theorem B2169881 : Blo 642303 2169881 := bstep (se 2 (by rfl) ⟨813705, by rfl⟩ : syracuseStep 2169881 = 1627411) B1627411
theorem B4398209 : Blo 642303 4398209 := bstep (se 2 (by rfl) ⟨1649328, by rfl⟩ : syracuseStep 4398209 = 3298657) B3298657
theorem B1449287 : Blo 642303 1449287 := bstep (se 1 (by rfl) ⟨1086965, by rfl⟩ : syracuseStep 1449287 = 2173931) B2173931
theorem B1449323 : Blo 642303 1449323 := bstep (se 1 (by rfl) ⟨1086992, by rfl⟩ : syracuseStep 1449323 = 2173985) B2173985
theorem B3677669 : Blo 642303 3677669 := bstep (se 4 (by rfl) ⟨344781, by rfl⟩ : syracuseStep 3677669 = 689563) B689563
theorem B1449449 : Blo 642303 1449449 := bstep (se 2 (by rfl) ⟨543543, by rfl⟩ : syracuseStep 1449449 = 1087087) B1087087
theorem B1449593 : Blo 642303 1449593 := bstep (se 2 (by rfl) ⟨543597, by rfl⟩ : syracuseStep 1449593 = 1087195) B1087195
theorem B2760439 : Blo 642303 2760439 := bstep (se 1 (by rfl) ⟨2070329, by rfl⟩ : syracuseStep 2760439 = 4140659) B4140659
theorem B3088523 : Blo 642303 3088523 := bstep (se 1 (by rfl) ⟨2316392, by rfl⟩ : syracuseStep 3088523 = 4632785) B4632785
theorem B2171069 : Blo 642303 2171069 := bstep (se 3 (by rfl) ⟨407075, by rfl⟩ : syracuseStep 2171069 = 814151) B814151
theorem B1450295 : Blo 642303 1450295 := bstep (se 1 (by rfl) ⟨1087721, by rfl⟩ : syracuseStep 1450295 = 2175443) B2175443
theorem B2171231 : Blo 642303 2171231 := bstep (se 1 (by rfl) ⟨1628423, by rfl⟩ : syracuseStep 2171231 = 3256847) B3256847
theorem B9904841 : Blo 642303 9904841 := bstep (se 2 (by rfl) ⟨3714315, by rfl⟩ : syracuseStep 9904841 = 7428631) B7428631
theorem B1451321 : Blo 642303 1451321 := bstep (se 2 (by rfl) ⟨544245, by rfl⟩ : syracuseStep 1451321 = 1088491) B1088491
theorem B1451591 : Blo 642303 1451591 := bstep (se 1 (by rfl) ⟨1088693, by rfl⟩ : syracuseStep 1451591 = 2177387) B2177387
theorem B1451771 : Blo 642303 1451771 := bstep (se 1 (by rfl) ⟨1088828, by rfl⟩ : syracuseStep 1451771 = 2177657) B2177657
theorem B927679 : Blo 642303 927679 := bstep (se 1 (by rfl) ⟨695759, by rfl⟩ : syracuseStep 927679 = 1391519) B1391519
theorem B1452059 : Blo 642303 1452059 := bstep (se 1 (by rfl) ⟨1089044, by rfl⟩ : syracuseStep 1452059 = 2178089) B2178089
theorem B3910151 : Blo 642303 3910151 := bstep (se 1 (by rfl) ⟨2932613, by rfl⟩ : syracuseStep 3910151 = 5865227) B5865227
theorem B8235695 : Blo 642303 8235695 := bstep (se 1 (by rfl) ⟨6176771, by rfl⟩ : syracuseStep 8235695 = 12353543) B12353543
theorem B4140197 : Blo 642303 4140197 := bstep (se 4 (by rfl) ⟨388143, by rfl⟩ : syracuseStep 4140197 = 776287) B776287
theorem B2174201 : Blo 642303 2174201 := bstep (se 2 (by rfl) ⟨815325, by rfl⟩ : syracuseStep 2174201 = 1630651) B1630651
theorem B8793359 : Blo 642303 8793359 := bstep (se 1 (by rfl) ⟨6595019, by rfl⟩ : syracuseStep 8793359 = 13190039) B13190039
theorem B2174363 : Blo 642303 2174363 := bstep (se 1 (by rfl) ⟨1630772, by rfl⟩ : syracuseStep 2174363 = 3261545) B3261545
theorem B5516707 : Blo 642303 5516707 := bstep (se 1 (by rfl) ⟨4137530, by rfl⟩ : syracuseStep 5516707 = 8275061) B8275061
theorem B1453535 : Blo 642303 1453535 := bstep (se 1 (by rfl) ⟨1090151, by rfl⟩ : syracuseStep 1453535 = 2180303) B2180303
theorem B2174471 : Blo 642303 2174471 := bstep (se 1 (by rfl) ⟨1630853, by rfl⟩ : syracuseStep 2174471 = 3261707) B3261707
theorem B1453751 : Blo 642303 1453751 := bstep (se 1 (by rfl) ⟨1090313, by rfl⟩ : syracuseStep 1453751 = 2180627) B2180627
theorem B3911759 : Blo 642303 3911759 := bstep (se 1 (by rfl) ⟨2933819, by rfl⟩ : syracuseStep 3911759 = 5867639) B5867639
theorem B1225115 : Blo 642303 1225115 := bstep (se 1 (by rfl) ⟨918836, by rfl⟩ : syracuseStep 1225115 = 1837673) B1837673
theorem B2175551 : Blo 642303 2175551 := bstep (se 1 (by rfl) ⟨1631663, by rfl⟩ : syracuseStep 2175551 = 3263327) B3263327
theorem B963767 : Blo 642303 963767 := bstep (se 1 (by rfl) ⟨722825, by rfl⟩ : syracuseStep 963767 = 1445651) B1445651
theorem B964007 : Blo 642303 964007 := bstep (se 1 (by rfl) ⟨723005, by rfl⟩ : syracuseStep 964007 = 1446011) B1446011
theorem B964187 : Blo 642303 964187 := bstep (se 1 (by rfl) ⟨723140, by rfl⟩ : syracuseStep 964187 = 1446281) B1446281
theorem B2439143 : Blo 642303 2439143 := bstep (se 1 (by rfl) ⟨1829357, by rfl⟩ : syracuseStep 2439143 = 3658715) B3658715
theorem B6961153 : Blo 642303 6961153 := bstep (se 2 (by rfl) ⟨2610432, by rfl⟩ : syracuseStep 6961153 = 5220865) B5220865
theorem B3094537 : Blo 642303 3094537 := bstep (se 2 (by rfl) ⟨1160451, by rfl⟩ : syracuseStep 3094537 = 2320903) B2320903
theorem B964649 : Blo 642303 964649 := bstep (se 2 (by rfl) ⟨361743, by rfl⟩ : syracuseStep 964649 = 723487) B723487
theorem B964679 : Blo 642303 964679 := bstep (se 1 (by rfl) ⟨723509, by rfl⟩ : syracuseStep 964679 = 1447019) B1447019
theorem B8927495 : Blo 642303 8927495 := bstep (se 1 (by rfl) ⟨6695621, by rfl⟩ : syracuseStep 8927495 = 13391243) B13391243
theorem B965063 : Blo 642303 965063 := bstep (se 1 (by rfl) ⟨723797, by rfl⟩ : syracuseStep 965063 = 1447595) B1447595
theorem B965279 : Blo 642303 965279 := bstep (se 1 (by rfl) ⟨723959, by rfl⟩ : syracuseStep 965279 = 1447919) B1447919
theorem B5225147 : Blo 642303 5225147 := bstep (se 1 (by rfl) ⟨3918860, by rfl⟩ : syracuseStep 5225147 = 7837721) B7837721
theorem B965423 : Blo 642303 965423 := bstep (se 1 (by rfl) ⟨724067, by rfl⟩ : syracuseStep 965423 = 1448135) B1448135
theorem B965543 : Blo 642303 965543 := bstep (se 1 (by rfl) ⟨724157, by rfl⟩ : syracuseStep 965543 = 1448315) B1448315
theorem B965723 : Blo 642303 965723 := bstep (se 1 (by rfl) ⟨724292, by rfl⟩ : syracuseStep 965723 = 1448585) B1448585
theorem B19872989 : Blo 642303 19872989 := bstep (se 3 (by rfl) ⟨3726185, by rfl⟩ : syracuseStep 19872989 = 7452371) B7452371
theorem B1162471 : Blo 642303 1162471 := bstep (se 1 (by rfl) ⟨871853, by rfl⟩ : syracuseStep 1162471 = 1743707) B1743707
theorem B22363465 : Blo 642303 22363465 := bstep (se 2 (by rfl) ⟨8386299, by rfl⟩ : syracuseStep 22363465 = 16772599) B16772599
theorem B2440631 : Blo 642303 2440631 := bstep (se 1 (by rfl) ⟨1830473, by rfl⟩ : syracuseStep 2440631 = 3660947) B3660947
theorem B966095 : Blo 642303 966095 := bstep (se 1 (by rfl) ⟨724571, by rfl⟩ : syracuseStep 966095 = 1449143) B1449143
theorem B4898393 : Blo 642303 4898393 := bstep (se 2 (by rfl) ⟨1836897, by rfl⟩ : syracuseStep 4898393 = 3673795) B3673795
theorem B966479 : Blo 642303 966479 := bstep (se 1 (by rfl) ⟨724859, by rfl⟩ : syracuseStep 966479 = 1449719) B1449719
theorem B966599 : Blo 642303 966599 := bstep (se 1 (by rfl) ⟨724949, by rfl⟩ : syracuseStep 966599 = 1449899) B1449899
theorem B15843539 : Blo 642303 15843539 := bstep (se 1 (by rfl) ⟨11882654, by rfl⟩ : syracuseStep 15843539 = 23765309) B23765309
theorem B966959 : Blo 642303 966959 := bstep (se 1 (by rfl) ⟨725219, by rfl⟩ : syracuseStep 966959 = 1450439) B1450439
theorem B967199 : Blo 642303 967199 := bstep (se 1 (by rfl) ⟨725399, by rfl⟩ : syracuseStep 967199 = 1450799) B1450799
theorem B7357067 : Blo 642303 7357067 := bstep (se 1 (by rfl) ⟨5517800, by rfl⟩ : syracuseStep 7357067 = 11035601) B11035601
theorem B3097385 : Blo 642303 3097385 := bstep (se 2 (by rfl) ⟨1161519, by rfl⟩ : syracuseStep 3097385 = 2323039) B2323039
theorem B5882959 : Blo 642303 5882959 := bstep (se 1 (by rfl) ⟨4412219, by rfl⟩ : syracuseStep 5882959 = 8824439) B8824439
theorem B967871 : Blo 642303 967871 := bstep (se 1 (by rfl) ⟨725903, by rfl⟩ : syracuseStep 967871 = 1451807) B1451807
theorem B2442575 : Blo 642303 2442575 := bstep (se 1 (by rfl) ⟨1831931, by rfl⟩ : syracuseStep 2442575 = 3663863) B3663863
theorem B968015 : Blo 642303 968015 := bstep (se 1 (by rfl) ⟨726011, by rfl⟩ : syracuseStep 968015 = 1452023) B1452023
theorem B968105 : Blo 642303 968105 := bstep (se 2 (by rfl) ⟨363039, by rfl⟩ : syracuseStep 968105 = 726079) B726079
theorem B4965947 : Blo 642303 4965947 := bstep (se 1 (by rfl) ⟨3724460, by rfl⟩ : syracuseStep 4965947 = 7448921) B7448921
theorem B968255 : Blo 642303 968255 := bstep (se 1 (by rfl) ⟨726191, by rfl⟩ : syracuseStep 968255 = 1452383) B1452383
theorem B968297 : Blo 642303 968297 := bstep (se 2 (by rfl) ⟨363111, by rfl⟩ : syracuseStep 968297 = 726223) B726223
theorem B2475629 : Blo 642303 2475629 := bstep (se 3 (by rfl) ⟨464180, by rfl⟩ : syracuseStep 2475629 = 928361) B928361
theorem B4966217 : Blo 642303 4966217 := bstep (se 2 (by rfl) ⟨1862331, by rfl⟩ : syracuseStep 4966217 = 3724663) B3724663
theorem B4900823 : Blo 642303 4900823 := bstep (se 1 (by rfl) ⟨3675617, by rfl⟩ : syracuseStep 4900823 = 7351235) B7351235
theorem B1394671 : Blo 642303 1394671 := bstep (se 1 (by rfl) ⟨1046003, by rfl⟩ : syracuseStep 1394671 = 2092007) B2092007
theorem B968735 : Blo 642303 968735 := bstep (se 1 (by rfl) ⟨726551, by rfl⟩ : syracuseStep 968735 = 1453103) B1453103
theorem B2181275 : Blo 642303 2181275 := bstep (se 1 (by rfl) ⟨1635956, by rfl⟩ : syracuseStep 2181275 = 3271913) B3271913
theorem B968927 : Blo 642303 968927 := bstep (se 1 (by rfl) ⟨726695, by rfl⟩ : syracuseStep 968927 = 1453391) B1453391
theorem B968987 : Blo 642303 968987 := bstep (se 1 (by rfl) ⟨726740, by rfl⟩ : syracuseStep 968987 = 1453481) B1453481
theorem B10996235 : Blo 642303 10996235 := bstep (se 1 (by rfl) ⟨8247176, by rfl⟩ : syracuseStep 10996235 = 16494353) B16494353
theorem B3263003 : Blo 642303 3263003 := bstep (se 1 (by rfl) ⟨2447252, by rfl⟩ : syracuseStep 3263003 = 4894505) B4894505
theorem B969311 : Blo 642303 969311 := bstep (se 1 (by rfl) ⟨726983, by rfl⟩ : syracuseStep 969311 = 1453967) B1453967
theorem B1657705 : Blo 642303 1657705 := bstep (se 2 (by rfl) ⟨621639, by rfl⟩ : syracuseStep 1657705 = 1243279) B1243279
theorem B4115387 : Blo 642303 4115387 := bstep (se 1 (by rfl) ⟨3086540, by rfl⟩ : syracuseStep 4115387 = 6173081) B6173081
theorem B3132395 : Blo 642303 3132395 := bstep (se 1 (by rfl) ⟨2349296, by rfl⟩ : syracuseStep 3132395 = 4698593) B4698593
theorem B7457773 : Blo 642303 7457773 := bstep (se 3 (by rfl) ⟨1398332, by rfl⟩ : syracuseStep 7457773 = 2796665) B2796665
theorem B2935865 : Blo 642303 2935865 := bstep (se 2 (by rfl) ⟨1100949, by rfl⟩ : syracuseStep 2935865 = 2201899) B2201899
theorem B642431 : Blo 642303 642431 := bstep (se 1 (by rfl) ⟨481823, by rfl⟩ : syracuseStep 642431 = 963647) B963647
theorem B642459 : Blo 642303 642459 := bstep (se 1 (by rfl) ⟨481844, by rfl⟩ : syracuseStep 642459 = 963689) B963689
theorem B642527 : Blo 642303 642527 := bstep (se 1 (by rfl) ⟨481895, by rfl⟩ : syracuseStep 642527 = 963791) B963791
theorem B21188135 : Blo 642303 21188135 := bstep (se 1 (by rfl) ⟨15891101, by rfl⟩ : syracuseStep 21188135 = 31782203) B31782203
theorem B642663 : Blo 642303 642663 := bstep (se 1 (by rfl) ⟨481997, by rfl⟩ : syracuseStep 642663 = 963995) B963995
theorem B642811 : Blo 642303 642811 := bstep (se 1 (by rfl) ⟨482108, by rfl⟩ : syracuseStep 642811 = 964217) B964217
theorem B642879 : Blo 642303 642879 := bstep (se 1 (by rfl) ⟨482159, by rfl⟩ : syracuseStep 642879 = 964319) B964319
theorem B642943 : Blo 642303 642943 := bstep (se 1 (by rfl) ⟨482207, by rfl⟩ : syracuseStep 642943 = 964415) B964415
theorem B643055 : Blo 642303 643055 := bstep (se 1 (by rfl) ⟨482291, by rfl⟩ : syracuseStep 643055 = 964583) B964583
theorem B643067 : Blo 642303 643067 := bstep (se 1 (by rfl) ⟨482300, by rfl⟩ : syracuseStep 643067 = 964601) B964601
theorem B643135 : Blo 642303 643135 := bstep (se 1 (by rfl) ⟨482351, by rfl⟩ : syracuseStep 643135 = 964703) B964703
theorem B643175 : Blo 642303 643175 := bstep (se 1 (by rfl) ⟨482381, by rfl⟩ : syracuseStep 643175 = 964763) B964763
theorem B643199 : Blo 642303 643199 := bstep (se 1 (by rfl) ⟨482399, by rfl⟩ : syracuseStep 643199 = 964799) B964799
theorem B643227 : Blo 642303 643227 := bstep (se 1 (by rfl) ⟨482420, by rfl⟩ : syracuseStep 643227 = 964841) B964841
theorem B643431 : Blo 642303 643431 := bstep (se 1 (by rfl) ⟨482573, by rfl⟩ : syracuseStep 643431 = 965147) B965147
theorem B643483 : Blo 642303 643483 := bstep (se 1 (by rfl) ⟨482612, by rfl⟩ : syracuseStep 643483 = 965225) B965225
theorem B11751905 : Blo 642303 11751905 := bstep (se 2 (by rfl) ⟨4406964, by rfl⟩ : syracuseStep 11751905 = 8813929) B8813929
theorem B1626601 : Blo 642303 1626601 := bstep (se 2 (by rfl) ⟨609975, by rfl⟩ : syracuseStep 1626601 = 1219951) B1219951
theorem B643835 : Blo 642303 643835 := bstep (se 1 (by rfl) ⟨482876, by rfl⟩ : syracuseStep 643835 = 965753) B965753
theorem B643903 : Blo 642303 643903 := bstep (se 1 (by rfl) ⟨482927, by rfl⟩ : syracuseStep 643903 = 965855) B965855
theorem B643931 : Blo 642303 643931 := bstep (se 1 (by rfl) ⟨482948, by rfl⟩ : syracuseStep 643931 = 965897) B965897
theorem B643999 : Blo 642303 643999 := bstep (se 1 (by rfl) ⟨482999, by rfl⟩ : syracuseStep 643999 = 965999) B965999
theorem B7361441 : Blo 642303 7361441 := bstep (se 2 (by rfl) ⟨2760540, by rfl⟩ : syracuseStep 7361441 = 5521081) B5521081
theorem B644079 : Blo 642303 644079 := bstep (se 1 (by rfl) ⟨483059, by rfl⟩ : syracuseStep 644079 = 966119) B966119
theorem B644167 : Blo 642303 644167 := bstep (se 1 (by rfl) ⟨483125, by rfl⟩ : syracuseStep 644167 = 966251) B966251
theorem B644251 : Blo 642303 644251 := bstep (se 1 (by rfl) ⟨483188, by rfl⟩ : syracuseStep 644251 = 966377) B966377
theorem B644347 : Blo 642303 644347 := bstep (se 1 (by rfl) ⟨483260, by rfl⟩ : syracuseStep 644347 = 966521) B966521
theorem B644415 : Blo 642303 644415 := bstep (se 1 (by rfl) ⟨483311, by rfl⟩ : syracuseStep 644415 = 966623) B966623
theorem B644583 : Blo 642303 644583 := bstep (se 1 (by rfl) ⟨483437, by rfl⟩ : syracuseStep 644583 = 966875) B966875
theorem B644591 : Blo 642303 644591 := bstep (se 1 (by rfl) ⟨483443, by rfl⟩ : syracuseStep 644591 = 966887) B966887
theorem B2446919 : Blo 642303 2446919 := bstep (se 1 (by rfl) ⟨1835189, by rfl⟩ : syracuseStep 2446919 = 3670379) B3670379
theorem B644699 : Blo 642303 644699 := bstep (se 1 (by rfl) ⟨483524, by rfl⟩ : syracuseStep 644699 = 967049) B967049
theorem B644763 : Blo 642303 644763 := bstep (se 1 (by rfl) ⟨483572, by rfl⟩ : syracuseStep 644763 = 967145) B967145
theorem B644847 : Blo 642303 644847 := bstep (se 1 (by rfl) ⟨483635, by rfl⟩ : syracuseStep 644847 = 967271) B967271
theorem B644935 : Blo 642303 644935 := bstep (se 1 (by rfl) ⟨483701, by rfl⟩ : syracuseStep 644935 = 967403) B967403
theorem B644955 : Blo 642303 644955 := bstep (se 1 (by rfl) ⟨483716, by rfl⟩ : syracuseStep 644955 = 967433) B967433
theorem B645023 : Blo 642303 645023 := bstep (se 1 (by rfl) ⟨483767, by rfl⟩ : syracuseStep 645023 = 967535) B967535
theorem B15685559 : Blo 642303 15685559 := bstep (se 1 (by rfl) ⟨11764169, by rfl⟩ : syracuseStep 15685559 = 23528339) B23528339
theorem B645191 : Blo 642303 645191 := bstep (se 1 (by rfl) ⟨483893, by rfl⟩ : syracuseStep 645191 = 967787) B967787
theorem B645351 : Blo 642303 645351 := bstep (se 1 (by rfl) ⟨484013, by rfl⟩ : syracuseStep 645351 = 968027) B968027
theorem B3103073 : Blo 642303 3103073 := bstep (se 2 (by rfl) ⟨1163652, by rfl⟩ : syracuseStep 3103073 = 2327305) B2327305
theorem B10443167 : Blo 642303 10443167 := bstep (se 1 (by rfl) ⟨7832375, by rfl⟩ : syracuseStep 10443167 = 15664751) B15664751
theorem B645535 : Blo 642303 645535 := bstep (se 1 (by rfl) ⟨484151, by rfl⟩ : syracuseStep 645535 = 968303) B968303
theorem B645583 : Blo 642303 645583 := bstep (se 1 (by rfl) ⟨484187, by rfl⟩ : syracuseStep 645583 = 968375) B968375
theorem B645607 : Blo 642303 645607 := bstep (se 1 (by rfl) ⟨484205, by rfl⟩ : syracuseStep 645607 = 968411) B968411
theorem B2447891 : Blo 642303 2447891 := bstep (se 1 (by rfl) ⟨1835918, by rfl⟩ : syracuseStep 2447891 = 3671837) B3671837
theorem B4413971 : Blo 642303 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B645723 : Blo 642303 645723 := bstep (se 1 (by rfl) ⟨484292, by rfl⟩ : syracuseStep 645723 = 968585) B968585
theorem B645791 : Blo 642303 645791 := bstep (se 1 (by rfl) ⟨484343, by rfl⟩ : syracuseStep 645791 = 968687) B968687
theorem B3660491 : Blo 642303 3660491 := bstep (se 1 (by rfl) ⟨2745368, by rfl⟩ : syracuseStep 3660491 = 5490737) B5490737
theorem B11000609 : Blo 642303 11000609 := bstep (se 2 (by rfl) ⟨4125228, by rfl⟩ : syracuseStep 11000609 = 8250457) B8250457
theorem B645959 : Blo 642303 645959 := bstep (se 1 (by rfl) ⟨484469, by rfl⟩ : syracuseStep 645959 = 968939) B968939
theorem B645999 : Blo 642303 645999 := bstep (se 1 (by rfl) ⟨484499, by rfl⟩ : syracuseStep 645999 = 968999) B968999
theorem B646055 : Blo 642303 646055 := bstep (se 1 (by rfl) ⟨484541, by rfl⟩ : syracuseStep 646055 = 969083) B969083
theorem B646235 : Blo 642303 646235 := bstep (se 1 (by rfl) ⟨484676, by rfl⟩ : syracuseStep 646235 = 969353) B969353
theorem B34331921 : Blo 642303 34331921 := bstep (se 2 (by rfl) ⟨12874470, by rfl⟩ : syracuseStep 34331921 = 25748941) B25748941
theorem B4971881 : Blo 642303 4971881 := bstep (se 2 (by rfl) ⟨1864455, by rfl⟩ : syracuseStep 4971881 = 3728911) B3728911
theorem B3268187 : Blo 642303 3268187 := bstep (se 1 (by rfl) ⟨2451140, by rfl⟩ : syracuseStep 3268187 = 4902281) B4902281
theorem B2481785 : Blo 642303 2481785 := bstep (se 2 (by rfl) ⟨930669, by rfl⟩ : syracuseStep 2481785 = 1861339) B1861339
theorem B1629983 : Blo 642303 1629983 := bstep (se 1 (by rfl) ⟨1222487, by rfl⟩ : syracuseStep 1629983 = 2444975) B2444975
theorem B20930683 : Blo 642303 20930683 := bstep (se 1 (by rfl) ⟨15698012, by rfl⟩ : syracuseStep 20930683 = 31396025) B31396025
theorem B2318483 : Blo 642303 2318483 := bstep (se 1 (by rfl) ⟨1738862, by rfl⟩ : syracuseStep 2318483 = 3477725) B3477725
theorem B1630601 : Blo 642303 1630601 := bstep (se 2 (by rfl) ⟨611475, by rfl⟩ : syracuseStep 1630601 = 1222951) B1222951
theorem B9527759 : Blo 642303 9527759 := bstep (se 1 (by rfl) ⟨7145819, by rfl⟩ : syracuseStep 9527759 = 14291639) B14291639
theorem B2351783 : Blo 642303 2351783 := bstep (se 1 (by rfl) ⟨1763837, by rfl⟩ : syracuseStep 2351783 = 3527675) B3527675
theorem B1631735 : Blo 642303 1631735 := bstep (se 1 (by rfl) ⟨1223801, by rfl⟩ : syracuseStep 1631735 = 2447603) B2447603
theorem B5891869 : Blo 642303 5891869 := bstep (se 3 (by rfl) ⟨1104725, by rfl⟩ : syracuseStep 5891869 = 2209451) B2209451
theorem B1468297 : Blo 642303 1468297 := bstep (se 2 (by rfl) ⟨550611, by rfl⟩ : syracuseStep 1468297 = 1101223) B1101223
theorem B6973523 : Blo 642303 6973523 := bstep (se 1 (by rfl) ⟨5230142, by rfl⟩ : syracuseStep 6973523 = 10460285) B10460285
theorem B3140111 : Blo 642303 3140111 := bstep (se 1 (by rfl) ⟨2355083, by rfl⟩ : syracuseStep 3140111 = 4710167) B4710167
theorem B1960843 : Blo 642303 1960843 := bstep (se 1 (by rfl) ⟨1470632, by rfl⟩ : syracuseStep 1960843 = 2941265) B2941265
theorem B107342779 : Blo 642303 107342779 := bstep (se 1 (by rfl) ⟨80507084, by rfl⟩ : syracuseStep 107342779 = 161014169) B161014169
theorem B8350937 : Blo 642303 8350937 := bstep (se 2 (by rfl) ⟨3131601, by rfl⟩ : syracuseStep 8350937 = 6263203) B6263203
theorem B2485727 : Blo 642303 2485727 := bstep (se 1 (by rfl) ⟨1864295, by rfl⟩ : syracuseStep 2485727 = 3728591) B3728591
theorem B2059847 : Blo 642303 2059847 := bstep (se 1 (by rfl) ⟨1544885, by rfl⟩ : syracuseStep 2059847 = 3089771) B3089771
theorem B1371899 : Blo 642303 1371899 := bstep (se 1 (by rfl) ⟨1028924, by rfl⟩ : syracuseStep 1371899 = 2057849) B2057849
theorem B21458843 : Blo 642303 21458843 := bstep (se 1 (by rfl) ⟨16094132, by rfl⟩ : syracuseStep 21458843 = 32188265) B32188265
theorem B1634377 : Blo 642303 1634377 := bstep (se 2 (by rfl) ⟨612891, by rfl⟩ : syracuseStep 1634377 = 1225783) B1225783
theorem B2748649 : Blo 642303 2748649 := bstep (se 2 (by rfl) ⟨1030743, by rfl⟩ : syracuseStep 2748649 = 2061487) B2061487
theorem B2748923 : Blo 642303 2748923 := bstep (se 1 (by rfl) ⟨2061692, by rfl⟩ : syracuseStep 2748923 = 4123385) B4123385
theorem B6287867 : Blo 642303 6287867 := bstep (se 1 (by rfl) ⟨4715900, by rfl⟩ : syracuseStep 6287867 = 9431801) B9431801
theorem B2061065 : Blo 642303 2061065 := bstep (se 2 (by rfl) ⟨772899, by rfl⟩ : syracuseStep 2061065 = 1545799) B1545799
theorem B5501945 : Blo 642303 5501945 := bstep (se 2 (by rfl) ⟨2063229, by rfl⟩ : syracuseStep 5501945 = 4126459) B4126459
theorem B1635511 : Blo 642303 1635511 := bstep (se 1 (by rfl) ⟨1226633, by rfl⟩ : syracuseStep 1635511 = 2453267) B2453267
theorem B2749727 : Blo 642303 2749727 := bstep (se 1 (by rfl) ⟨2062295, by rfl⟩ : syracuseStep 2749727 = 4124591) B4124591
theorem B101644091 : Blo 642303 101644091 := bstep (se 1 (by rfl) ⟨76233068, by rfl⟩ : syracuseStep 101644091 = 152466137) B152466137
theorem B1374727 : Blo 642303 1374727 := bstep (se 1 (by rfl) ⟨1031045, by rfl⟩ : syracuseStep 1374727 = 2062091) B2062091
theorem B1572065 : Blo 642303 1572065 := bstep (se 2 (by rfl) ⟨589524, by rfl⟩ : syracuseStep 1572065 = 1179049) B1179049
theorem B36732199 : Blo 642303 36732199 := bstep (se 1 (by rfl) ⟨27549149, by rfl⟩ : syracuseStep 36732199 = 55098299) B55098299
theorem B31358663 : Blo 642303 31358663 := bstep (se 1 (by rfl) ⟨23518997, by rfl⟩ : syracuseStep 31358663 = 47037995) B47037995
theorem B2064923 : Blo 642303 2064923 := bstep (se 1 (by rfl) ⟨1548692, by rfl⟩ : syracuseStep 2064923 = 3097385) B3097385
theorem B1049375 : Blo 642303 1049375 := bstep (se 1 (by rfl) ⟨787031, by rfl⟩ : syracuseStep 1049375 = 1574063) B1574063
theorem B918335 : Blo 642303 918335 := bstep (se 1 (by rfl) ⟨688751, by rfl⟩ : syracuseStep 918335 = 1377503) B1377503
theorem B7341029 : Blo 642303 7341029 := bstep (se 4 (by rfl) ⟨688221, by rfl⟩ : syracuseStep 7341029 = 1376443) B1376443
theorem B3310631 : Blo 642303 3310631 := bstep (se 1 (by rfl) ⟨2482973, by rfl⟩ : syracuseStep 3310631 = 4965947) B4965947
theorem B3310811 : Blo 642303 3310811 := bstep (se 1 (by rfl) ⟨2483108, by rfl⟩ : syracuseStep 3310811 = 4966217) B4966217
theorem B723199 : Blo 642303 723199 := bstep (se 1 (by rfl) ⟨542399, by rfl⟩ : syracuseStep 723199 = 1084799) B1084799
theorem B14125423 : Blo 642303 14125423 := bstep (se 1 (by rfl) ⟨10594067, by rfl⟩ : syracuseStep 14125423 = 21188135) B21188135
theorem B1837559 : Blo 642303 1837559 := bstep (se 1 (by rfl) ⟨1378169, by rfl⟩ : syracuseStep 1837559 = 2756339) B2756339
theorem B5507959 : Blo 642303 5507959 := bstep (se 1 (by rfl) ⟨4130969, by rfl⟩ : syracuseStep 5507959 = 8261939) B8261939
theorem B724639 : Blo 642303 724639 := bstep (se 1 (by rfl) ⟨543479, by rfl⟩ : syracuseStep 724639 = 1086959) B1086959
theorem B724927 : Blo 642303 724927 := bstep (se 1 (by rfl) ⟨543695, by rfl⟩ : syracuseStep 724927 = 1087391) B1087391
theorem B10457039 : Blo 642303 10457039 := bstep (se 1 (by rfl) ⟨7842779, by rfl⟩ : syracuseStep 10457039 = 15685559) B15685559
theorem B2756699 : Blo 642303 2756699 := bstep (se 1 (by rfl) ⟨2067524, by rfl⟩ : syracuseStep 2756699 = 4135049) B4135049
theorem B2068715 : Blo 642303 2068715 := bstep (se 1 (by rfl) ⟨1551536, by rfl⟩ : syracuseStep 2068715 = 3103073) B3103073
theorem B1446137 : Blo 642303 1446137 := bstep (se 2 (by rfl) ⟨542301, by rfl⟩ : syracuseStep 1446137 = 1084603) B1084603
theorem B1118711 : Blo 642303 1118711 := bstep (se 1 (by rfl) ⟨839033, by rfl⟩ : syracuseStep 1118711 = 1678067) B1678067
theorem B1446407 : Blo 642303 1446407 := bstep (se 1 (by rfl) ⟨1084805, by rfl⟩ : syracuseStep 1446407 = 2169611) B2169611
theorem B3674753 : Blo 642303 3674753 := bstep (se 2 (by rfl) ⟨1378032, by rfl⟩ : syracuseStep 3674753 = 2756065) B2756065
theorem B1446587 : Blo 642303 1446587 := bstep (se 1 (by rfl) ⟨1084940, by rfl⟩ : syracuseStep 1446587 = 2169881) B2169881
theorem B3314587 : Blo 642303 3314587 := bstep (se 1 (by rfl) ⟨2485940, by rfl⟩ : syracuseStep 3314587 = 4971881) B4971881
theorem B1086655 : Blo 642303 1086655 := bstep (se 1 (by rfl) ⟨814991, by rfl⟩ : syracuseStep 1086655 = 1629983) B1629983
theorem B1545655 : Blo 642303 1545655 := bstep (se 1 (by rfl) ⟨1159241, by rfl⟩ : syracuseStep 1545655 = 2318483) B2318483
theorem B1447379 : Blo 642303 1447379 := bstep (se 1 (by rfl) ⟨1085534, by rfl⟩ : syracuseStep 1447379 = 2171069) B2171069
theorem B1447487 : Blo 642303 1447487 := bstep (se 1 (by rfl) ⟨1085615, by rfl⟩ : syracuseStep 1447487 = 2171231) B2171231
theorem B1087067 : Blo 642303 1087067 := bstep (se 1 (by rfl) ⟨815300, by rfl⟩ : syracuseStep 1087067 = 1630601) B1630601
theorem B1447649 : Blo 642303 1447649 := bstep (se 2 (by rfl) ⟨542868, by rfl⟩ : syracuseStep 1447649 = 1085737) B1085737
theorem B2168801 : Blo 642303 2168801 := bstep (se 2 (by rfl) ⟨813300, by rfl⟩ : syracuseStep 2168801 = 1626601) B1626601
theorem B1448009 : Blo 642303 1448009 := bstep (se 2 (by rfl) ⟨543003, by rfl⟩ : syracuseStep 1448009 = 1086007) B1086007
theorem B1087823 : Blo 642303 1087823 := bstep (se 1 (by rfl) ⟨815867, by rfl⟩ : syracuseStep 1087823 = 1631735) B1631735
theorem B7346861 : Blo 642303 7346861 := bstep (se 3 (by rfl) ⟨1377536, by rfl⟩ : syracuseStep 7346861 = 2755073) B2755073
theorem B10427069 : Blo 642303 10427069 := bstep (se 3 (by rfl) ⟨1955075, by rfl⟩ : syracuseStep 10427069 = 3910151) B3910151
theorem B11770589 : Blo 642303 11770589 := bstep (se 3 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 11770589 = 4413971) B4413971
theorem B2760131 : Blo 642303 2760131 := bstep (se 1 (by rfl) ⟨2070098, by rfl⟩ : syracuseStep 2760131 = 4140197) B4140197
theorem B1449467 : Blo 642303 1449467 := bstep (se 1 (by rfl) ⟨1087100, by rfl⟩ : syracuseStep 1449467 = 2174201) B2174201
theorem B1449575 : Blo 642303 1449575 := bstep (se 1 (by rfl) ⟨1087181, by rfl⟩ : syracuseStep 1449575 = 2174363) B2174363
theorem B1449647 : Blo 642303 1449647 := bstep (se 1 (by rfl) ⟨1087235, by rfl⟩ : syracuseStep 1449647 = 2174471) B2174471
theorem B1449737 : Blo 642303 1449737 := bstep (se 2 (by rfl) ⟨543651, by rfl⟩ : syracuseStep 1449737 = 1087303) B1087303
theorem B2760473 : Blo 642303 2760473 := bstep (se 2 (by rfl) ⟨1035177, by rfl⟩ : syracuseStep 2760473 = 2070355) B2070355
theorem B9281537 : Blo 642303 9281537 := bstep (se 2 (by rfl) ⟨3480576, by rfl⟩ : syracuseStep 9281537 = 6961153) B6961153
theorem B1450367 : Blo 642303 1450367 := bstep (se 1 (by rfl) ⟨1087775, by rfl⟩ : syracuseStep 1450367 = 2175551) B2175551
theorem B1549961 : Blo 642303 1549961 := bstep (se 2 (by rfl) ⟨581235, by rfl⟩ : syracuseStep 1549961 = 1162471) B1162471
theorem B3483431 : Blo 642303 3483431 := bstep (se 1 (by rfl) ⟨2612573, by rfl⟩ : syracuseStep 3483431 = 5225147) B5225147
theorem B13248659 : Blo 642303 13248659 := bstep (se 1 (by rfl) ⟨9936494, by rfl⟩ : syracuseStep 13248659 = 19872989) B19872989
theorem B3680585 : Blo 642303 3680585 := bstep (se 2 (by rfl) ⟨1380219, by rfl⟩ : syracuseStep 3680585 = 2760439) B2760439
theorem B35367815 : Blo 642303 35367815 := bstep (se 1 (by rfl) ⟨26525861, by rfl⟩ : syracuseStep 35367815 = 53051723) B53051723
theorem B42249437 : Blo 642303 42249437 := bstep (se 3 (by rfl) ⟨7921769, by rfl⟩ : syracuseStep 42249437 = 15843539) B15843539
theorem B11185897 : Blo 642303 11185897 := bstep (se 2 (by rfl) ⟨4194711, by rfl⟩ : syracuseStep 11185897 = 8389423) B8389423
theorem B1650419 : Blo 642303 1650419 := bstep (se 1 (by rfl) ⟨1237814, by rfl⟩ : syracuseStep 1650419 = 2475629) B2475629
theorem B31338413 : Blo 642303 31338413 := bstep (se 3 (by rfl) ⟨5875952, by rfl⟩ : syracuseStep 31338413 = 11751905) B11751905
theorem B1454183 : Blo 642303 1454183 := bstep (se 1 (by rfl) ⟨1090637, by rfl⟩ : syracuseStep 1454183 = 2181275) B2181275
theorem B1224811 : Blo 642303 1224811 := bstep (se 1 (by rfl) ⟨918608, by rfl⟩ : syracuseStep 1224811 = 1837217) B1837217
theorem B1749289 : Blo 642303 1749289 := bstep (se 2 (by rfl) ⟨655983, by rfl⟩ : syracuseStep 1749289 = 1311967) B1311967
theorem B2175335 : Blo 642303 2175335 := bstep (se 1 (by rfl) ⟨1631501, by rfl⟩ : syracuseStep 2175335 = 3263003) B3263003
theorem B1225631 : Blo 642303 1225631 := bstep (se 1 (by rfl) ⟨919223, by rfl⟩ : syracuseStep 1225631 = 1838447) B1838447
theorem B963497 : Blo 642303 963497 := bstep (se 2 (by rfl) ⟨361311, by rfl⟩ : syracuseStep 963497 = 722623) B722623
theorem B963563 : Blo 642303 963563 := bstep (se 1 (by rfl) ⟨722672, by rfl⟩ : syracuseStep 963563 = 1445345) B1445345
theorem B963839 : Blo 642303 963839 := bstep (se 1 (by rfl) ⟨722879, by rfl⟩ : syracuseStep 963839 = 1445759) B1445759
theorem B963881 : Blo 642303 963881 := bstep (se 2 (by rfl) ⟨361455, by rfl⟩ : syracuseStep 963881 = 722911) B722911
theorem B964475 : Blo 642303 964475 := bstep (se 1 (by rfl) ⟨723356, by rfl⟩ : syracuseStep 964475 = 1446713) B1446713
theorem B964511 : Blo 642303 964511 := bstep (se 1 (by rfl) ⟨723383, by rfl⟩ : syracuseStep 964511 = 1446767) B1446767
theorem B964715 : Blo 642303 964715 := bstep (se 1 (by rfl) ⟨723536, by rfl⟩ : syracuseStep 964715 = 1447073) B1447073
theorem B964745 : Blo 642303 964745 := bstep (se 2 (by rfl) ⟨361779, by rfl⟩ : syracuseStep 964745 = 723559) B723559
theorem B2930899 : Blo 642303 2930899 := bstep (se 1 (by rfl) ⟨2198174, by rfl⟩ : syracuseStep 2930899 = 4396349) B4396349
theorem B964895 : Blo 642303 964895 := bstep (se 1 (by rfl) ⟨723671, by rfl⟩ : syracuseStep 964895 = 1447343) B1447343
theorem B2210273 : Blo 642303 2210273 := bstep (se 2 (by rfl) ⟨828852, by rfl⟩ : syracuseStep 2210273 = 1657705) B1657705
theorem B9943697 : Blo 642303 9943697 := bstep (se 2 (by rfl) ⟨3728886, by rfl⟩ : syracuseStep 9943697 = 7457773) B7457773
theorem B965567 : Blo 642303 965567 := bstep (se 1 (by rfl) ⟨724175, by rfl⟩ : syracuseStep 965567 = 1448351) B1448351
theorem B6962111 : Blo 642303 6962111 := bstep (se 1 (by rfl) ⟨5221583, by rfl⟩ : syracuseStep 6962111 = 10443167) B10443167
theorem B965615 : Blo 642303 965615 := bstep (se 1 (by rfl) ⟨724211, by rfl⟩ : syracuseStep 965615 = 1448423) B1448423
theorem B2440327 : Blo 642303 2440327 := bstep (se 1 (by rfl) ⟨1830245, by rfl⟩ : syracuseStep 2440327 = 3660491) B3660491
theorem B965801 : Blo 642303 965801 := bstep (se 2 (by rfl) ⟨362175, by rfl⟩ : syracuseStep 965801 = 724351) B724351
theorem B7355609 : Blo 642303 7355609 := bstep (se 2 (by rfl) ⟨2758353, by rfl⟩ : syracuseStep 7355609 = 5516707) B5516707
theorem B2932139 : Blo 642303 2932139 := bstep (se 1 (by rfl) ⟨2199104, by rfl⟩ : syracuseStep 2932139 = 4398209) B4398209
theorem B22887947 : Blo 642303 22887947 := bstep (se 1 (by rfl) ⟨17165960, by rfl⟩ : syracuseStep 22887947 = 34331921) B34331921
theorem B966191 : Blo 642303 966191 := bstep (se 1 (by rfl) ⟨724643, by rfl⟩ : syracuseStep 966191 = 1449287) B1449287
theorem B966215 : Blo 642303 966215 := bstep (se 1 (by rfl) ⟨724661, by rfl⟩ : syracuseStep 966215 = 1449323) B1449323
theorem B966299 : Blo 642303 966299 := bstep (se 1 (by rfl) ⟨724724, by rfl⟩ : syracuseStep 966299 = 1449449) B1449449
theorem B2178791 : Blo 642303 2178791 := bstep (se 1 (by rfl) ⟨1634093, by rfl⟩ : syracuseStep 2178791 = 3268187) B3268187
theorem B966395 : Blo 642303 966395 := bstep (se 1 (by rfl) ⟨724796, by rfl⟩ : syracuseStep 966395 = 1449593) B1449593
theorem B1654523 : Blo 642303 1654523 := bstep (se 1 (by rfl) ⟨1240892, by rfl⟩ : syracuseStep 1654523 = 2481785) B2481785
theorem B2179169 : Blo 642303 2179169 := bstep (se 2 (by rfl) ⟨817188, by rfl⟩ : syracuseStep 2179169 = 1634377) B1634377
theorem B966863 : Blo 642303 966863 := bstep (se 1 (by rfl) ⟨725147, by rfl⟩ : syracuseStep 966863 = 1450295) B1450295
theorem B31375781 : Blo 642303 31375781 := bstep (se 4 (by rfl) ⟨2941479, by rfl⟩ : syracuseStep 31375781 = 5882959) B5882959
theorem B6603227 : Blo 642303 6603227 := bstep (se 1 (by rfl) ⟨4952420, by rfl⟩ : syracuseStep 6603227 = 9904841) B9904841
theorem B967547 : Blo 642303 967547 := bstep (se 1 (by rfl) ⟨725660, by rfl⟩ : syracuseStep 967547 = 1451321) B1451321
theorem B967673 : Blo 642303 967673 := bstep (se 2 (by rfl) ⟨362877, by rfl⟩ : syracuseStep 967673 = 725755) B725755
theorem B967727 : Blo 642303 967727 := bstep (se 1 (by rfl) ⟨725795, by rfl⟩ : syracuseStep 967727 = 1451591) B1451591
theorem B967847 : Blo 642303 967847 := bstep (se 1 (by rfl) ⟨725885, by rfl⟩ : syracuseStep 967847 = 1451771) B1451771
theorem B968039 : Blo 642303 968039 := bstep (se 1 (by rfl) ⟨726029, by rfl⟩ : syracuseStep 968039 = 1452059) B1452059
theorem B2180681 : Blo 642303 2180681 := bstep (se 2 (by rfl) ⟨817755, by rfl⟩ : syracuseStep 2180681 = 1635511) B1635511
theorem B5490463 : Blo 642303 5490463 := bstep (se 1 (by rfl) ⟨4117847, by rfl⟩ : syracuseStep 5490463 = 8235695) B8235695
theorem B968681 : Blo 642303 968681 := bstep (se 2 (by rfl) ⟨363255, by rfl⟩ : syracuseStep 968681 = 726511) B726511
theorem B968825 : Blo 642303 968825 := bstep (se 2 (by rfl) ⟨363309, by rfl⟩ : syracuseStep 968825 = 726619) B726619
theorem B1657151 : Blo 642303 1657151 := bstep (se 1 (by rfl) ⟨1242863, by rfl⟩ : syracuseStep 1657151 = 2485727) B2485727
theorem B969023 : Blo 642303 969023 := bstep (se 1 (by rfl) ⟨726767, by rfl⟩ : syracuseStep 969023 = 1453535) B1453535
theorem B969167 : Blo 642303 969167 := bstep (se 1 (by rfl) ⟨726875, by rfl⟩ : syracuseStep 969167 = 1453751) B1453751
theorem B969209 : Blo 642303 969209 := bstep (se 2 (by rfl) ⟨363453, by rfl⟩ : syracuseStep 969209 = 726907) B726907
theorem B969257 : Blo 642303 969257 := bstep (se 2 (by rfl) ⟨363471, by rfl⟩ : syracuseStep 969257 = 726943) B726943
theorem B14305895 : Blo 642303 14305895 := bstep (se 1 (by rfl) ⟨10729421, by rfl⟩ : syracuseStep 14305895 = 21458843) B21458843
theorem B2607839 : Blo 642303 2607839 := bstep (se 1 (by rfl) ⟨1955879, by rfl⟩ : syracuseStep 2607839 = 3911759) B3911759
theorem B642511 : Blo 642303 642511 := bstep (se 1 (by rfl) ⟨481883, by rfl⟩ : syracuseStep 642511 = 963767) B963767
theorem B642671 : Blo 642303 642671 := bstep (se 1 (by rfl) ⟨482003, by rfl⟩ : syracuseStep 642671 = 964007) B964007
theorem B642791 : Blo 642303 642791 := bstep (se 1 (by rfl) ⟨482093, by rfl⟩ : syracuseStep 642791 = 964187) B964187
theorem B4116413 : Blo 642303 4116413 := bstep (se 3 (by rfl) ⟨771827, by rfl⟩ : syracuseStep 4116413 = 1543655) B1543655
theorem B1626095 : Blo 642303 1626095 := bstep (se 1 (by rfl) ⟨1219571, by rfl⟩ : syracuseStep 1626095 = 2439143) B2439143
theorem B643099 : Blo 642303 643099 := bstep (se 1 (by rfl) ⟨482324, by rfl⟩ : syracuseStep 643099 = 964649) B964649
theorem B643119 : Blo 642303 643119 := bstep (se 1 (by rfl) ⟨482339, by rfl⟩ : syracuseStep 643119 = 964679) B964679
theorem B5951663 : Blo 642303 5951663 := bstep (se 1 (by rfl) ⟨4463747, by rfl⟩ : syracuseStep 5951663 = 8927495) B8927495
theorem B643375 : Blo 642303 643375 := bstep (se 1 (by rfl) ⟨482531, by rfl⟩ : syracuseStep 643375 = 965063) B965063
theorem B48976265 : Blo 642303 48976265 := bstep (se 2 (by rfl) ⟨18366099, by rfl⟩ : syracuseStep 48976265 = 36732199) B36732199
theorem B643519 : Blo 642303 643519 := bstep (se 1 (by rfl) ⟨482639, by rfl⟩ : syracuseStep 643519 = 965279) B965279
theorem B643615 : Blo 642303 643615 := bstep (se 1 (by rfl) ⟨482711, by rfl⟩ : syracuseStep 643615 = 965423) B965423
theorem B643695 : Blo 642303 643695 := bstep (se 1 (by rfl) ⟨482771, by rfl⟩ : syracuseStep 643695 = 965543) B965543
theorem B643815 : Blo 642303 643815 := bstep (se 1 (by rfl) ⟨482861, by rfl⟩ : syracuseStep 643815 = 965723) B965723
theorem B1627087 : Blo 642303 1627087 := bstep (se 1 (by rfl) ⟨1220315, by rfl⟩ : syracuseStep 1627087 = 2440631) B2440631
theorem B644063 : Blo 642303 644063 := bstep (se 1 (by rfl) ⟨483047, by rfl⟩ : syracuseStep 644063 = 966095) B966095
theorem B3265595 : Blo 642303 3265595 := bstep (se 1 (by rfl) ⟨2449196, by rfl⟩ : syracuseStep 3265595 = 4898393) B4898393
theorem B644319 : Blo 642303 644319 := bstep (se 1 (by rfl) ⟨483239, by rfl⟩ : syracuseStep 644319 = 966479) B966479
theorem B644399 : Blo 642303 644399 := bstep (se 1 (by rfl) ⟨483299, by rfl⟩ : syracuseStep 644399 = 966599) B966599
theorem B27907577 : Blo 642303 27907577 := bstep (se 2 (by rfl) ⟨10465341, by rfl⟩ : syracuseStep 27907577 = 20930683) B20930683
theorem B644639 : Blo 642303 644639 := bstep (se 1 (by rfl) ⟨483479, by rfl⟩ : syracuseStep 644639 = 966959) B966959
theorem B644799 : Blo 642303 644799 := bstep (se 1 (by rfl) ⟨483599, by rfl⟩ : syracuseStep 644799 = 967199) B967199
theorem B4904711 : Blo 642303 4904711 := bstep (se 1 (by rfl) ⟨3678533, by rfl⟩ : syracuseStep 4904711 = 7357067) B7357067
theorem B645247 : Blo 642303 645247 := bstep (se 1 (by rfl) ⟨483935, by rfl⟩ : syracuseStep 645247 = 967871) B967871
theorem B1628383 : Blo 642303 1628383 := bstep (se 1 (by rfl) ⟨1221287, by rfl⟩ : syracuseStep 1628383 = 2442575) B2442575
theorem B645343 : Blo 642303 645343 := bstep (se 1 (by rfl) ⟨484007, by rfl⟩ : syracuseStep 645343 = 968015) B968015
theorem B645403 : Blo 642303 645403 := bstep (se 1 (by rfl) ⟨484052, by rfl⟩ : syracuseStep 645403 = 968105) B968105
theorem B645503 : Blo 642303 645503 := bstep (se 1 (by rfl) ⟨484127, by rfl⟩ : syracuseStep 645503 = 968255) B968255
theorem B645531 : Blo 642303 645531 := bstep (se 1 (by rfl) ⟨484148, by rfl⟩ : syracuseStep 645531 = 968297) B968297
theorem B13916771 : Blo 642303 13916771 := bstep (se 1 (by rfl) ⟨10437578, by rfl⟩ : syracuseStep 13916771 = 20875157) B20875157
theorem B3267215 : Blo 642303 3267215 := bstep (se 1 (by rfl) ⟨2450411, by rfl⟩ : syracuseStep 3267215 = 4900823) B4900823
theorem B645823 : Blo 642303 645823 := bstep (se 1 (by rfl) ⟨484367, by rfl⟩ : syracuseStep 645823 = 968735) B968735
theorem B645951 : Blo 642303 645951 := bstep (se 1 (by rfl) ⟨484463, by rfl⟩ : syracuseStep 645951 = 968927) B968927
theorem B645991 : Blo 642303 645991 := bstep (se 1 (by rfl) ⟨484493, by rfl⟩ : syracuseStep 645991 = 968987) B968987
theorem B7330823 : Blo 642303 7330823 := bstep (se 1 (by rfl) ⟨5498117, by rfl⟩ : syracuseStep 7330823 = 10996235) B10996235
theorem B646207 : Blo 642303 646207 := bstep (se 1 (by rfl) ⟨484655, by rfl⟩ : syracuseStep 646207 = 969311) B969311
theorem B2088263 : Blo 642303 2088263 := bstep (se 1 (by rfl) ⟨1566197, by rfl⟩ : syracuseStep 2088263 = 3132395) B3132395
theorem B5496173 : Blo 642303 5496173 := bstep (se 3 (by rfl) ⟨1030532, by rfl⟩ : syracuseStep 5496173 = 2061065) B2061065
theorem B1957243 : Blo 642303 1957243 := bstep (se 1 (by rfl) ⟨1467932, by rfl⟩ : syracuseStep 1957243 = 2935865) B2935865
theorem B7855825 : Blo 642303 7855825 := bstep (se 2 (by rfl) ⟨2945934, by rfl⟩ : syracuseStep 7855825 = 5891869) B5891869
theorem B1236905 : Blo 642303 1236905 := bstep (se 2 (by rfl) ⟨463839, by rfl⟩ : syracuseStep 1236905 = 927679) B927679
theorem B1859561 : Blo 642303 1859561 := bstep (se 2 (by rfl) ⟨697335, by rfl⟩ : syracuseStep 1859561 = 1394671) B1394671
theorem B4907627 : Blo 642303 4907627 := bstep (se 1 (by rfl) ⟨3680720, by rfl⟩ : syracuseStep 4907627 = 7361441) B7361441
theorem B1631279 : Blo 642303 1631279 := bstep (se 1 (by rfl) ⟨1223459, by rfl⟩ : syracuseStep 1631279 = 2446919) B2446919
theorem B2614457 : Blo 642303 2614457 := bstep (se 2 (by rfl) ⟨980421, by rfl⟩ : syracuseStep 2614457 = 1960843) B1960843
theorem B143123705 : Blo 642303 143123705 := bstep (se 2 (by rfl) ⟨53671389, by rfl⟩ : syracuseStep 143123705 = 107342779) B107342779
theorem B2057899 : Blo 642303 2057899 := bstep (se 1 (by rfl) ⟨1543424, by rfl⟩ : syracuseStep 2057899 = 3086849) B3086849
theorem B1631927 : Blo 642303 1631927 := bstep (se 1 (by rfl) ⟨1223945, by rfl⟩ : syracuseStep 1631927 = 2447891) B2447891
theorem B2320211 : Blo 642303 2320211 := bstep (se 1 (by rfl) ⟨1740158, by rfl⟩ : syracuseStep 2320211 = 3480317) B3480317
theorem B7333739 : Blo 642303 7333739 := bstep (se 1 (by rfl) ⟨5500304, by rfl⟩ : syracuseStep 7333739 = 11000609) B11000609
theorem B2451323 : Blo 642303 2451323 := bstep (se 1 (by rfl) ⟨1838492, by rfl⟩ : syracuseStep 2451323 = 3676985) B3676985
theorem B2451779 : Blo 642303 2451779 := bstep (se 1 (by rfl) ⟨1838834, by rfl⟩ : syracuseStep 2451779 = 3677669) B3677669
theorem B2059015 : Blo 642303 2059015 := bstep (se 1 (by rfl) ⟨1544261, by rfl⟩ : syracuseStep 2059015 = 3088523) B3088523
theorem B2059129 : Blo 642303 2059129 := bstep (se 2 (by rfl) ⟨772173, by rfl⟩ : syracuseStep 2059129 = 1544347) B1544347
theorem B6351839 : Blo 642303 6351839 := bstep (se 1 (by rfl) ⟨4763879, by rfl⟩ : syracuseStep 6351839 = 9527759) B9527759
theorem B3664865 : Blo 642303 3664865 := bstep (se 2 (by rfl) ⟨1374324, by rfl⟩ : syracuseStep 3664865 = 2748649) B2748649
theorem B1567855 : Blo 642303 1567855 := bstep (se 1 (by rfl) ⟨1175891, by rfl⟩ : syracuseStep 1567855 = 2351783) B2351783
theorem B4649015 : Blo 642303 4649015 := bstep (se 1 (by rfl) ⟨3486761, by rfl⟩ : syracuseStep 4649015 = 6973523) B6973523
theorem B2093407 : Blo 642303 2093407 := bstep (se 1 (by rfl) ⟨1570055, by rfl⟩ : syracuseStep 2093407 = 3140111) B3140111
theorem B5567291 : Blo 642303 5567291 := bstep (se 1 (by rfl) ⟨4175468, by rfl⟩ : syracuseStep 5567291 = 8350937) B8350937
theorem B5862239 : Blo 642303 5862239 := bstep (se 1 (by rfl) ⟨4396679, by rfl⟩ : syracuseStep 5862239 = 8793359) B8793359
theorem B1373231 : Blo 642303 1373231 := bstep (se 1 (by rfl) ⟨1029923, by rfl⟩ : syracuseStep 1373231 = 2059847) B2059847
theorem B10974365 : Blo 642303 10974365 := bstep (se 3 (by rfl) ⟨2057693, by rfl⟩ : syracuseStep 10974365 = 4115387) B4115387
theorem B914599 : Blo 642303 914599 := bstep (se 1 (by rfl) ⟨685949, by rfl⟩ : syracuseStep 914599 = 1371899) B1371899
theorem B4126049 : Blo 642303 4126049 := bstep (se 2 (by rfl) ⟨1547268, by rfl⟩ : syracuseStep 4126049 = 3094537) B3094537
theorem B816743 : Blo 642303 816743 := bstep (se 1 (by rfl) ⟨612557, by rfl⟩ : syracuseStep 816743 = 1225115) B1225115
theorem B1832615 : Blo 642303 1832615 := bstep (se 1 (by rfl) ⟨1374461, by rfl⟩ : syracuseStep 1832615 = 2748923) B2748923
theorem B4191911 : Blo 642303 4191911 := bstep (se 1 (by rfl) ⟨3143933, by rfl⟩ : syracuseStep 4191911 = 6287867) B6287867
theorem B3667963 : Blo 642303 3667963 := bstep (se 1 (by rfl) ⟨2750972, by rfl⟩ : syracuseStep 3667963 = 5501945) B5501945
theorem B1832969 : Blo 642303 1832969 := bstep (se 2 (by rfl) ⟨687363, by rfl⟩ : syracuseStep 1832969 = 1374727) B1374727
theorem B1833151 : Blo 642303 1833151 := bstep (se 1 (by rfl) ⟨1374863, by rfl⟩ : syracuseStep 1833151 = 2749727) B2749727
theorem B67762727 : Blo 642303 67762727 := bstep (se 1 (by rfl) ⟨50822045, by rfl⟩ : syracuseStep 67762727 = 101644091) B101644091
theorem B29817953 : Blo 642303 29817953 := bstep (se 2 (by rfl) ⟨11181732, by rfl⟩ : syracuseStep 29817953 = 22363465) B22363465
theorem B7830917 : Blo 642303 7830917 := bstep (se 4 (by rfl) ⟨734148, by rfl⟩ : syracuseStep 7830917 = 1468297) B1468297
theorem B1048043 : Blo 642303 1048043 := bstep (se 1 (by rfl) ⟨786032, by rfl⟩ : syracuseStep 1048043 = 1572065) B1572065
theorem B20905775 : Blo 642303 20905775 := bstep (se 1 (by rfl) ⟨15679331, by rfl⟩ : syracuseStep 20905775 = 31358663) B31358663
theorem B1376615 : Blo 642303 1376615 := bstep (se 1 (by rfl) ⟨1032461, by rfl⟩ : syracuseStep 1376615 = 2064923) B2064923
theorem B2983229 : Blo 642303 2983229 := bstep (se 3 (by rfl) ⟨559355, by rfl⟩ : syracuseStep 2983229 = 1118711) B1118711
theorem B9537263 : Blo 642303 9537263 := bstep (se 1 (by rfl) ⟨7152947, by rfl⟩ : syracuseStep 9537263 = 14305895) B14305895
theorem B1738559 : Blo 642303 1738559 := bstep (se 1 (by rfl) ⟨1303919, by rfl⟩ : syracuseStep 1738559 = 2607839) B2607839
theorem B1084063 : Blo 642303 1084063 := bstep (se 1 (by rfl) ⟨813047, by rfl⟩ : syracuseStep 1084063 = 1626095) B1626095
theorem B1837799 : Blo 642303 1837799 := bstep (se 1 (by rfl) ⟨1378349, by rfl⟩ : syracuseStep 1837799 = 2756699) B2756699
theorem B3967775 : Blo 642303 3967775 := bstep (se 1 (by rfl) ⟨2975831, by rfl⟩ : syracuseStep 3967775 = 5951663) B5951663
theorem B1379143 : Blo 642303 1379143 := bstep (se 1 (by rfl) ⟨1034357, by rfl⟩ : syracuseStep 1379143 = 2068715) B2068715
theorem B724711 : Blo 642303 724711 := bstep (se 1 (by rfl) ⟨543533, by rfl⟩ : syracuseStep 724711 = 1087067) B1087067
theorem B7343945 : Blo 642303 7343945 := bstep (se 2 (by rfl) ⟨2753979, by rfl⟩ : syracuseStep 7343945 = 5507959) B5507959
theorem B1445867 : Blo 642303 1445867 := bstep (se 1 (by rfl) ⟨1084400, by rfl⟩ : syracuseStep 1445867 = 2168801) B2168801
theorem B725215 : Blo 642303 725215 := bstep (se 1 (by rfl) ⟨543911, by rfl⟩ : syracuseStep 725215 = 1087823) B1087823
theorem B9277847 : Blo 642303 9277847 := bstep (se 1 (by rfl) ⟨6958385, by rfl⟩ : syracuseStep 9277847 = 13916771) B13916771
theorem B4887215 : Blo 642303 4887215 := bstep (se 1 (by rfl) ⟨3665411, by rfl⟩ : syracuseStep 4887215 = 7330823) B7330823
theorem B1840087 : Blo 642303 1840087 := bstep (se 1 (by rfl) ⟨1380065, by rfl⟩ : syracuseStep 1840087 = 2760131) B2760131
theorem B14914529 : Blo 642303 14914529 := bstep (se 2 (by rfl) ⟨5592948, by rfl⟩ : syracuseStep 14914529 = 11185897) B11185897
theorem B1840315 : Blo 642303 1840315 := bstep (se 1 (by rfl) ⟨1380236, by rfl⟩ : syracuseStep 1840315 = 2760473) B2760473
theorem B824603 : Blo 642303 824603 := bstep (se 1 (by rfl) ⟨618452, by rfl⟩ : syracuseStep 824603 = 1236905) B1236905
theorem B2332385 : Blo 642303 2332385 := bstep (se 2 (by rfl) ⟨874644, by rfl⟩ : syracuseStep 2332385 = 1749289) B1749289
theorem B1087519 : Blo 642303 1087519 := bstep (se 1 (by rfl) ⟨815639, by rfl⟩ : syracuseStep 1087519 = 1631279) B1631279
theorem B1742971 : Blo 642303 1742971 := bstep (se 1 (by rfl) ⟨1307228, by rfl⟩ : syracuseStep 1742971 = 2614457) B2614457
theorem B1087951 : Blo 642303 1087951 := bstep (se 1 (by rfl) ⟨815963, by rfl⟩ : syracuseStep 1087951 = 1631927) B1631927
theorem B4889159 : Blo 642303 4889159 := bstep (se 1 (by rfl) ⟨3666869, by rfl⟩ : syracuseStep 4889159 = 7333739) B7333739
theorem B2169449 : Blo 642303 2169449 := bstep (se 2 (by rfl) ⟨813543, by rfl⟩ : syracuseStep 2169449 = 1627087) B1627087
theorem B1219465 : Blo 642303 1219465 := bstep (se 2 (by rfl) ⟨457299, by rfl⟩ : syracuseStep 1219465 = 914599) B914599
theorem B1448873 : Blo 642303 1448873 := bstep (se 2 (by rfl) ⟨543327, by rfl⟩ : syracuseStep 1448873 = 1086655) B1086655
theorem B4234559 : Blo 642303 4234559 := bstep (se 1 (by rfl) ⟨3175919, by rfl⟩ : syracuseStep 4234559 = 6351839) B6351839
theorem B4890617 : Blo 642303 4890617 := bstep (se 2 (by rfl) ⟨1833981, by rfl⟩ : syracuseStep 4890617 = 3667963) B3667963
theorem B1450223 : Blo 642303 1450223 := bstep (se 1 (by rfl) ⟨1087667, by rfl⟩ : syracuseStep 1450223 = 2175335) B2175335
theorem B3907865 : Blo 642303 3907865 := bstep (se 2 (by rfl) ⟨1465449, by rfl⟩ : syracuseStep 3907865 = 2930899) B2930899
theorem B2171177 : Blo 642303 2171177 := bstep (se 2 (by rfl) ⟨814191, by rfl⟩ : syracuseStep 2171177 = 1628383) B1628383
theorem B3711527 : Blo 642303 3711527 := bstep (se 1 (by rfl) ⟨2783645, by rfl⟩ : syracuseStep 3711527 = 5567291) B5567291
theorem B3908159 : Blo 642303 3908159 := bstep (se 1 (by rfl) ⟨2931119, by rfl⟩ : syracuseStep 3908159 = 5862239) B5862239
theorem B7316243 : Blo 642303 7316243 := bstep (se 1 (by rfl) ⟨5487182, by rfl⟩ : syracuseStep 7316243 = 10974365) B10974365
theorem B1221743 : Blo 642303 1221743 := bstep (se 1 (by rfl) ⟨916307, by rfl⟩ : syracuseStep 1221743 = 1832615) B1832615
theorem B2794607 : Blo 642303 2794607 := bstep (se 1 (by rfl) ⟨2095955, by rfl⟩ : syracuseStep 2794607 = 4191911) B4191911
theorem B2794781 : Blo 642303 2794781 := bstep (se 3 (by rfl) ⟨524021, by rfl⟩ : syracuseStep 2794781 = 1048043) B1048043
theorem B1221979 : Blo 642303 1221979 := bstep (se 1 (by rfl) ⟨916484, by rfl⟩ : syracuseStep 1221979 = 1832969) B1832969
theorem B3253769 : Blo 642303 3253769 := bstep (se 2 (by rfl) ⟨1220163, by rfl⟩ : syracuseStep 3253769 = 2440327) B2440327
theorem B6629131 : Blo 642303 6629131 := bstep (se 1 (by rfl) ⟨4971848, by rfl⟩ : syracuseStep 6629131 = 9943697) B9943697
theorem B5220611 : Blo 642303 5220611 := bstep (se 1 (by rfl) ⟨3915458, by rfl⟩ : syracuseStep 5220611 = 7830917) B7830917
theorem B1452527 : Blo 642303 1452527 := bstep (se 1 (by rfl) ⟨1089395, by rfl⟩ : syracuseStep 1452527 = 2178791) B2178791
theorem B13937183 : Blo 642303 13937183 := bstep (se 1 (by rfl) ⟨10452887, by rfl⟩ : syracuseStep 13937183 = 20905775) B20905775
theorem B1452779 : Blo 642303 1452779 := bstep (se 1 (by rfl) ⟨1089584, by rfl⟩ : syracuseStep 1452779 = 2179169) B2179169
theorem B12397373 : Blo 642303 12397373 := bstep (se 3 (by rfl) ⟨2324507, by rfl⟩ : syracuseStep 12397373 = 4649015) B4649015
theorem B20917187 : Blo 642303 20917187 := bstep (se 1 (by rfl) ⟨15687890, by rfl⟩ : syracuseStep 20917187 = 31375781) B31375781
theorem B4402151 : Blo 642303 4402151 := bstep (se 1 (by rfl) ⟨3301613, by rfl⟩ : syracuseStep 4402151 = 6603227) B6603227
theorem B4894019 : Blo 642303 4894019 := bstep (se 1 (by rfl) ⟨3670514, by rfl⟩ : syracuseStep 4894019 = 7341029) B7341029
theorem B2207087 : Blo 642303 2207087 := bstep (se 1 (by rfl) ⟨1655315, by rfl⟩ : syracuseStep 2207087 = 3310631) B3310631
theorem B2207207 : Blo 642303 2207207 := bstep (se 1 (by rfl) ⟨1655405, by rfl⟩ : syracuseStep 2207207 = 3310811) B3310811
theorem B1453787 : Blo 642303 1453787 := bstep (se 1 (by rfl) ⟨1090340, by rfl⟩ : syracuseStep 1453787 = 2180681) B2180681
theorem B1225039 : Blo 642303 1225039 := bstep (se 1 (by rfl) ⟨918779, by rfl⟩ : syracuseStep 1225039 = 1837559) B1837559
theorem B2798333 : Blo 642303 2798333 := bstep (se 3 (by rfl) ⟨524687, by rfl⟩ : syracuseStep 2798333 = 1049375) B1049375
theorem B7320617 : Blo 642303 7320617 := bstep (se 2 (by rfl) ⟨2745231, by rfl⟩ : syracuseStep 7320617 = 5490463) B5490463
theorem B964091 : Blo 642303 964091 := bstep (se 1 (by rfl) ⟨723068, by rfl⟩ : syracuseStep 964091 = 1446137) B1446137
theorem B964265 : Blo 642303 964265 := bstep (se 2 (by rfl) ⟨361599, by rfl⟩ : syracuseStep 964265 = 723199) B723199
theorem B964271 : Blo 642303 964271 := bstep (se 1 (by rfl) ⟨723203, by rfl⟩ : syracuseStep 964271 = 1446407) B1446407
theorem B964391 : Blo 642303 964391 := bstep (se 1 (by rfl) ⟨723293, by rfl⟩ : syracuseStep 964391 = 1446587) B1446587
theorem B2177063 : Blo 642303 2177063 := bstep (se 1 (by rfl) ⟨1632797, by rfl⟩ : syracuseStep 2177063 = 3265595) B3265595
theorem B964919 : Blo 642303 964919 := bstep (se 1 (by rfl) ⟨723689, by rfl⟩ : syracuseStep 964919 = 1447379) B1447379
theorem B964991 : Blo 642303 964991 := bstep (se 1 (by rfl) ⟨723743, by rfl⟩ : syracuseStep 964991 = 1447487) B1447487
theorem B965099 : Blo 642303 965099 := bstep (se 1 (by rfl) ⟨723824, by rfl⟩ : syracuseStep 965099 = 1447649) B1447649
theorem B965339 : Blo 642303 965339 := bstep (se 1 (by rfl) ⟨724004, by rfl⟩ : syracuseStep 965339 = 1448009) B1448009
theorem B2177981 : Blo 642303 2177981 := bstep (se 3 (by rfl) ⟨408371, by rfl⟩ : syracuseStep 2177981 = 816743) B816743
theorem B2178143 : Blo 642303 2178143 := bstep (se 1 (by rfl) ⟨1633607, by rfl⟩ : syracuseStep 2178143 = 3267215) B3267215
theorem B4897907 : Blo 642303 4897907 := bstep (se 1 (by rfl) ⟨3673430, by rfl⟩ : syracuseStep 4897907 = 7346861) B7346861
theorem B7847059 : Blo 642303 7847059 := bstep (se 1 (by rfl) ⟨5885294, by rfl⟩ : syracuseStep 7847059 = 11770589) B11770589
theorem B966185 : Blo 642303 966185 := bstep (se 2 (by rfl) ⟨362319, by rfl⟩ : syracuseStep 966185 = 724639) B724639
theorem B1392175 : Blo 642303 1392175 := bstep (se 1 (by rfl) ⟨1044131, by rfl⟩ : syracuseStep 1392175 = 2088263) B2088263
theorem B966311 : Blo 642303 966311 := bstep (se 1 (by rfl) ⟨724733, by rfl⟩ : syracuseStep 966311 = 1449467) B1449467
theorem B966383 : Blo 642303 966383 := bstep (se 1 (by rfl) ⟨724787, by rfl⟩ : syracuseStep 966383 = 1449575) B1449575
theorem B966431 : Blo 642303 966431 := bstep (se 1 (by rfl) ⟨724823, by rfl⟩ : syracuseStep 966431 = 1449647) B1449647
theorem B966491 : Blo 642303 966491 := bstep (se 1 (by rfl) ⟨724868, by rfl⟩ : syracuseStep 966491 = 1449737) B1449737
theorem B966569 : Blo 642303 966569 := bstep (se 2 (by rfl) ⟨362463, by rfl⟩ : syracuseStep 966569 = 724927) B724927
theorem B966911 : Blo 642303 966911 := bstep (se 1 (by rfl) ⟨725183, by rfl⟩ : syracuseStep 966911 = 1450367) B1450367
theorem B1033307 : Blo 642303 1033307 := bstep (se 1 (by rfl) ⟨774980, by rfl⟩ : syracuseStep 1033307 = 1549961) B1549961
theorem B8832439 : Blo 642303 8832439 := bstep (se 1 (by rfl) ⟨6624329, by rfl⟩ : syracuseStep 8832439 = 13248659) B13248659
theorem B27805517 : Blo 642303 27805517 := bstep (se 3 (by rfl) ⟨5213534, by rfl⟩ : syracuseStep 27805517 = 10427069) B10427069
theorem B23578543 : Blo 642303 23578543 := bstep (se 1 (by rfl) ⟨17683907, by rfl⟩ : syracuseStep 23578543 = 35367815) B35367815
theorem B2443243 : Blo 642303 2443243 := bstep (se 1 (by rfl) ⟨1832432, by rfl⟩ : syracuseStep 2443243 = 3664865) B3664865
theorem B28166291 : Blo 642303 28166291 := bstep (se 1 (by rfl) ⟨21124718, by rfl⟩ : syracuseStep 28166291 = 42249437) B42249437
theorem B1100279 : Blo 642303 1100279 := bstep (se 1 (by rfl) ⟨825209, by rfl⟩ : syracuseStep 1100279 = 1650419) B1650419
theorem B20892275 : Blo 642303 20892275 := bstep (se 1 (by rfl) ⟨15669206, by rfl⟩ : syracuseStep 20892275 = 31338413) B31338413
theorem B969455 : Blo 642303 969455 := bstep (se 1 (by rfl) ⟨727091, by rfl⟩ : syracuseStep 969455 = 1454183) B1454183
theorem B2444201 : Blo 642303 2444201 := bstep (se 2 (by rfl) ⟨916575, by rfl⟩ : syracuseStep 2444201 = 1833151) B1833151
theorem B642331 : Blo 642303 642331 := bstep (se 1 (by rfl) ⟨481748, by rfl⟩ : syracuseStep 642331 = 963497) B963497
theorem B642375 : Blo 642303 642375 := bstep (se 1 (by rfl) ⟨481781, by rfl⟩ : syracuseStep 642375 = 963563) B963563
theorem B642559 : Blo 642303 642559 := bstep (se 1 (by rfl) ⟨481919, by rfl⟩ : syracuseStep 642559 = 963839) B963839
theorem B642587 : Blo 642303 642587 := bstep (se 1 (by rfl) ⟨481940, by rfl⟩ : syracuseStep 642587 = 963881) B963881
theorem B642983 : Blo 642303 642983 := bstep (se 1 (by rfl) ⟨482237, by rfl⟩ : syracuseStep 642983 = 964475) B964475
theorem B643007 : Blo 642303 643007 := bstep (se 1 (by rfl) ⟨482255, by rfl⟩ : syracuseStep 643007 = 964511) B964511
theorem B643143 : Blo 642303 643143 := bstep (se 1 (by rfl) ⟨482357, by rfl⟩ : syracuseStep 643143 = 964715) B964715
theorem B643163 : Blo 642303 643163 := bstep (se 1 (by rfl) ⟨482372, by rfl⟩ : syracuseStep 643163 = 964745) B964745
theorem B643263 : Blo 642303 643263 := bstep (se 1 (by rfl) ⟨482447, by rfl⟩ : syracuseStep 643263 = 964895) B964895
theorem B45175151 : Blo 642303 45175151 := bstep (se 1 (by rfl) ⟨33881363, by rfl⟩ : syracuseStep 45175151 = 67762727) B67762727
theorem B2609657 : Blo 642303 2609657 := bstep (se 2 (by rfl) ⟨978621, by rfl⟩ : syracuseStep 2609657 = 1957243) B1957243
theorem B643711 : Blo 642303 643711 := bstep (se 1 (by rfl) ⟨482783, by rfl⟩ : syracuseStep 643711 = 965567) B965567
theorem B4641407 : Blo 642303 4641407 := bstep (se 1 (by rfl) ⟨3481055, by rfl⟩ : syracuseStep 4641407 = 6962111) B6962111
theorem B643743 : Blo 642303 643743 := bstep (se 1 (by rfl) ⟨482807, by rfl⟩ : syracuseStep 643743 = 965615) B965615
theorem B19878635 : Blo 642303 19878635 := bstep (se 1 (by rfl) ⟨14908976, by rfl⟩ : syracuseStep 19878635 = 29817953) B29817953
theorem B643867 : Blo 642303 643867 := bstep (se 1 (by rfl) ⟨482900, by rfl⟩ : syracuseStep 643867 = 965801) B965801
theorem B4903739 : Blo 642303 4903739 := bstep (se 1 (by rfl) ⟨3677804, by rfl⟩ : syracuseStep 4903739 = 7355609) B7355609
theorem B10474433 : Blo 642303 10474433 := bstep (se 2 (by rfl) ⟨3927912, by rfl⟩ : syracuseStep 10474433 = 7855825) B7855825
theorem B1954759 : Blo 642303 1954759 := bstep (se 1 (by rfl) ⟨1466069, by rfl⟩ : syracuseStep 1954759 = 2932139) B2932139
theorem B15258631 : Blo 642303 15258631 := bstep (se 1 (by rfl) ⟨11443973, by rfl⟩ : syracuseStep 15258631 = 22887947) B22887947
theorem B644127 : Blo 642303 644127 := bstep (se 1 (by rfl) ⟨483095, by rfl⟩ : syracuseStep 644127 = 966191) B966191
theorem B644143 : Blo 642303 644143 := bstep (se 1 (by rfl) ⟨483107, by rfl⟩ : syracuseStep 644143 = 966215) B966215
theorem B644199 : Blo 642303 644199 := bstep (se 1 (by rfl) ⟨483149, by rfl⟩ : syracuseStep 644199 = 966299) B966299
theorem B644263 : Blo 642303 644263 := bstep (se 1 (by rfl) ⟨483197, by rfl⟩ : syracuseStep 644263 = 966395) B966395
theorem B1103015 : Blo 642303 1103015 := bstep (se 1 (by rfl) ⟨827261, by rfl⟩ : syracuseStep 1103015 = 1654523) B1654523
theorem B644575 : Blo 642303 644575 := bstep (se 1 (by rfl) ⟨483431, by rfl⟩ : syracuseStep 644575 = 966863) B966863
theorem B645031 : Blo 642303 645031 := bstep (se 1 (by rfl) ⟨483773, by rfl⟩ : syracuseStep 645031 = 967547) B967547
theorem B645115 : Blo 642303 645115 := bstep (se 1 (by rfl) ⟨483836, by rfl⟩ : syracuseStep 645115 = 967673) B967673
theorem B645151 : Blo 642303 645151 := bstep (se 1 (by rfl) ⟨483863, by rfl⟩ : syracuseStep 645151 = 967727) B967727
theorem B645231 : Blo 642303 645231 := bstep (se 1 (by rfl) ⟨483923, by rfl⟩ : syracuseStep 645231 = 967847) B967847
theorem B645359 : Blo 642303 645359 := bstep (se 1 (by rfl) ⟨484019, by rfl⟩ : syracuseStep 645359 = 968039) B968039
theorem B130603373 : Blo 642303 130603373 := bstep (se 3 (by rfl) ⟨24488132, by rfl⟩ : syracuseStep 130603373 = 48976265) B48976265
theorem B645787 : Blo 642303 645787 := bstep (se 1 (by rfl) ⟨484340, by rfl⟩ : syracuseStep 645787 = 968681) B968681
theorem B645883 : Blo 642303 645883 := bstep (se 1 (by rfl) ⟨484412, by rfl⟩ : syracuseStep 645883 = 968825) B968825
theorem B1104767 : Blo 642303 1104767 := bstep (se 1 (by rfl) ⟨828575, by rfl⟩ : syracuseStep 1104767 = 1657151) B1657151
theorem B646015 : Blo 642303 646015 := bstep (se 1 (by rfl) ⟨484511, by rfl⟩ : syracuseStep 646015 = 969023) B969023
theorem B646111 : Blo 642303 646111 := bstep (se 1 (by rfl) ⟨484583, by rfl⟩ : syracuseStep 646111 = 969167) B969167
theorem B646139 : Blo 642303 646139 := bstep (se 1 (by rfl) ⟨484604, by rfl⟩ : syracuseStep 646139 = 969209) B969209
theorem B646171 : Blo 642303 646171 := bstep (se 1 (by rfl) ⟨484628, by rfl⟩ : syracuseStep 646171 = 969257) B969257
theorem B11164837 : Blo 642303 11164837 := bstep (se 4 (by rfl) ⟨1046703, by rfl⟩ : syracuseStep 11164837 = 2093407) B2093407
theorem B2448893 : Blo 642303 2448893 := bstep (se 3 (by rfl) ⟨459167, by rfl⟩ : syracuseStep 2448893 = 918335) B918335
theorem B2743865 : Blo 642303 2743865 := bstep (se 2 (by rfl) ⟨1028949, by rfl⟩ : syracuseStep 2743865 = 2057899) B2057899
theorem B3268349 : Blo 642303 3268349 := bstep (se 3 (by rfl) ⟨612815, by rfl⟩ : syracuseStep 3268349 = 1225631) B1225631
theorem B2744275 : Blo 642303 2744275 := bstep (se 1 (by rfl) ⟨2058206, by rfl⟩ : syracuseStep 2744275 = 4116413) B4116413
theorem B6971359 : Blo 642303 6971359 := bstep (se 1 (by rfl) ⟨5228519, by rfl⟩ : syracuseStep 6971359 = 10457039) B10457039
theorem B3661949 : Blo 642303 3661949 := bstep (se 3 (by rfl) ⟨686615, by rfl⟩ : syracuseStep 3661949 = 1373231) B1373231
theorem B2449835 : Blo 642303 2449835 := bstep (se 1 (by rfl) ⟨1837376, by rfl⟩ : syracuseStep 2449835 = 3674753) B3674753
theorem B18833897 : Blo 642303 18833897 := bstep (se 2 (by rfl) ⟨7062711, by rfl⟩ : syracuseStep 18833897 = 14125423) B14125423
theorem B18605051 : Blo 642303 18605051 := bstep (se 1 (by rfl) ⟨13953788, by rfl⟩ : syracuseStep 18605051 = 27907577) B27907577
theorem B2745353 : Blo 642303 2745353 := bstep (se 2 (by rfl) ⟨1029507, by rfl⟩ : syracuseStep 2745353 = 2059015) B2059015
theorem B2745505 : Blo 642303 2745505 := bstep (se 2 (by rfl) ⟨1029564, by rfl⟩ : syracuseStep 2745505 = 2059129) B2059129
theorem B3269807 : Blo 642303 3269807 := bstep (se 1 (by rfl) ⟨2452355, by rfl⟩ : syracuseStep 3269807 = 4904711) B4904711
theorem B2090473 : Blo 642303 2090473 := bstep (se 2 (by rfl) ⟨783927, by rfl⟩ : syracuseStep 2090473 = 1567855) B1567855
theorem B6187229 : Blo 642303 6187229 := bstep (se 3 (by rfl) ⟨1160105, by rfl⟩ : syracuseStep 6187229 = 2320211) B2320211
theorem B3664115 : Blo 642303 3664115 := bstep (se 1 (by rfl) ⟨2748086, by rfl⟩ : syracuseStep 3664115 = 5496173) B5496173
theorem B1239707 : Blo 642303 1239707 := bstep (se 1 (by rfl) ⟨929780, by rfl⟩ : syracuseStep 1239707 = 1859561) B1859561
theorem B6187691 : Blo 642303 6187691 := bstep (se 1 (by rfl) ⟨4640768, by rfl⟩ : syracuseStep 6187691 = 9281537) B9281537
theorem B1633081 : Blo 642303 1633081 := bstep (se 2 (by rfl) ⟨612405, by rfl⟩ : syracuseStep 1633081 = 1224811) B1224811
theorem B3271751 : Blo 642303 3271751 := bstep (se 1 (by rfl) ⟨2453813, by rfl⟩ : syracuseStep 3271751 = 4907627) B4907627
theorem B95415803 : Blo 642303 95415803 := bstep (se 1 (by rfl) ⟨71561852, by rfl⟩ : syracuseStep 95415803 = 143123705) B143123705
theorem B2322287 : Blo 642303 2322287 := bstep (se 1 (by rfl) ⟨1741715, by rfl⟩ : syracuseStep 2322287 = 3483431) B3483431
theorem B4419449 : Blo 642303 4419449 := bstep (se 2 (by rfl) ⟨1657293, by rfl⟩ : syracuseStep 4419449 = 3314587) B3314587
theorem B1634215 : Blo 642303 1634215 := bstep (se 1 (by rfl) ⟨1225661, by rfl⟩ : syracuseStep 1634215 = 2451323) B2451323
theorem B1634519 : Blo 642303 1634519 := bstep (se 1 (by rfl) ⟨1225889, by rfl⟩ : syracuseStep 1634519 = 2451779) B2451779
theorem B2453723 : Blo 642303 2453723 := bstep (se 1 (by rfl) ⟨1840292, by rfl⟩ : syracuseStep 2453723 = 3680585) B3680585
theorem B2060873 : Blo 642303 2060873 := bstep (se 2 (by rfl) ⟨772827, by rfl⟩ : syracuseStep 2060873 = 1545655) B1545655
theorem B2750699 : Blo 642303 2750699 := bstep (se 1 (by rfl) ⟨2063024, by rfl⟩ : syracuseStep 2750699 = 4126049) B4126049
theorem B1473515 : Blo 642303 1473515 := bstep (se 1 (by rfl) ⟨1105136, by rfl⟩ : syracuseStep 1473515 = 2210273) B2210273
theorem B917743 : Blo 642303 917743 := bstep (se 1 (by rfl) ⟨688307, by rfl⟩ : syracuseStep 917743 = 1376615) B1376615
theorem B688871 : Blo 642303 688871 := bstep (se 1 (by rfl) ⟨516653, by rfl⟩ : syracuseStep 688871 = 1033307) B1033307
theorem B10420973 : Blo 642303 10420973 := bstep (se 3 (by rfl) ⟨1953932, by rfl⟩ : syracuseStep 10420973 = 3907865) B3907865
theorem B6358175 : Blo 642303 6358175 := bstep (se 1 (by rfl) ⟨4768631, by rfl⟩ : syracuseStep 6358175 = 9537263) B9537263
theorem B18777527 : Blo 642303 18777527 := bstep (se 1 (by rfl) ⟨14083145, by rfl⟩ : syracuseStep 18777527 = 28166291) B28166291
theorem B13928183 : Blo 642303 13928183 := bstep (se 1 (by rfl) ⟨10446137, by rfl⟩ : syracuseStep 13928183 = 20892275) B20892275
theorem B30116767 : Blo 642303 30116767 := bstep (se 1 (by rfl) ⟨22587575, by rfl⟩ : syracuseStep 30116767 = 45175151) B45175151
theorem B1739771 : Blo 642303 1739771 := bstep (se 1 (by rfl) ⟨1304828, by rfl⟩ : syracuseStep 1739771 = 2609657) B2609657
theorem B6982955 : Blo 642303 6982955 := bstep (se 1 (by rfl) ⟨5237216, by rfl⟩ : syracuseStep 6982955 = 10474433) B10474433
theorem B1445417 : Blo 642303 1445417 := bstep (se 2 (by rfl) ⟨542031, by rfl⟩ : syracuseStep 1445417 = 1084063) B1084063
theorem B1838857 : Blo 642303 1838857 := bstep (se 2 (by rfl) ⟨689571, by rfl⟩ : syracuseStep 1838857 = 1379143) B1379143
theorem B87068915 : Blo 642303 87068915 := bstep (se 1 (by rfl) ⟨65301686, by rfl⟩ : syracuseStep 87068915 = 130603373) B130603373
theorem B1446299 : Blo 642303 1446299 := bstep (se 1 (by rfl) ⟨1084724, by rfl⟩ : syracuseStep 1446299 = 2169449) B2169449
theorem B1447451 : Blo 642303 1447451 := bstep (se 1 (by rfl) ⟨1085588, by rfl⟩ : syracuseStep 1447451 = 2171177) B2171177
theorem B12555931 : Blo 642303 12555931 := bstep (se 1 (by rfl) ⟨9416948, by rfl⟩ : syracuseStep 12555931 = 18833897) B18833897
theorem B2169179 : Blo 642303 2169179 := bstep (se 1 (by rfl) ⟨1626884, by rfl⟩ : syracuseStep 2169179 = 3253769) B3253769
theorem B3480407 : Blo 642303 3480407 := bstep (se 1 (by rfl) ⟨2610305, by rfl⟩ : syracuseStep 3480407 = 5220611) B5220611
theorem B826471 : Blo 642303 826471 := bstep (se 1 (by rfl) ⟨619853, by rfl⟩ : syracuseStep 826471 = 1239707) B1239707
theorem B8264915 : Blo 642303 8264915 := bstep (se 1 (by rfl) ⟨6198686, by rfl⟩ : syracuseStep 8264915 = 12397373) B12397373
theorem B63610535 : Blo 642303 63610535 := bstep (se 1 (by rfl) ⟨47707901, by rfl⟩ : syracuseStep 63610535 = 95415803) B95415803
theorem B1548191 : Blo 642303 1548191 := bstep (se 1 (by rfl) ⟨1161143, by rfl⟩ : syracuseStep 1548191 = 2322287) B2322287
theorem B1450025 : Blo 642303 1450025 := bstep (se 2 (by rfl) ⟨543759, by rfl⟩ : syracuseStep 1450025 = 1087519) B1087519
theorem B1089679 : Blo 642303 1089679 := bstep (se 1 (by rfl) ⟨817259, by rfl⟩ : syracuseStep 1089679 = 1634519) B1634519
theorem B1450601 : Blo 642303 1450601 := bstep (se 2 (by rfl) ⟨543975, by rfl⟩ : syracuseStep 1450601 = 1087951) B1087951
theorem B1451375 : Blo 642303 1451375 := bstep (se 1 (by rfl) ⟨1088531, by rfl⟩ : syracuseStep 1451375 = 2177063) B2177063
theorem B10462745 : Blo 642303 10462745 := bstep (se 2 (by rfl) ⟨3923529, by rfl⟩ : syracuseStep 10462745 = 7847059) B7847059
theorem B14886449 : Blo 642303 14886449 := bstep (se 2 (by rfl) ⟨5582418, by rfl⟩ : syracuseStep 14886449 = 11164837) B11164837
theorem B1451987 : Blo 642303 1451987 := bstep (se 1 (by rfl) ⟨1088990, by rfl⟩ : syracuseStep 1451987 = 2177981) B2177981
theorem B1452095 : Blo 642303 1452095 := bstep (se 1 (by rfl) ⟨1089071, by rfl⟩ : syracuseStep 1452095 = 2178143) B2178143
theorem B1159039 : Blo 642303 1159039 := bstep (se 1 (by rfl) ⟨869279, by rfl⟩ : syracuseStep 1159039 = 1738559) B1738559
theorem B733519 : Blo 642303 733519 := bstep (se 1 (by rfl) ⟨550139, by rfl⟩ : syracuseStep 733519 = 1100279) B1100279
theorem B1225199 : Blo 642303 1225199 := bstep (se 1 (by rfl) ⟨918899, by rfl⟩ : syracuseStep 1225199 = 1837799) B1837799
theorem B11776585 : Blo 642303 11776585 := bstep (se 2 (by rfl) ⟨4416219, by rfl⟩ : syracuseStep 11776585 = 8832439) B8832439
theorem B4895963 : Blo 642303 4895963 := bstep (se 1 (by rfl) ⟨3671972, by rfl⟩ : syracuseStep 4895963 = 7343945) B7343945
theorem B31438057 : Blo 642303 31438057 := bstep (se 2 (by rfl) ⟨11789271, by rfl⟩ : syracuseStep 31438057 = 23578543) B23578543
theorem B3257657 : Blo 642303 3257657 := bstep (se 2 (by rfl) ⟨1221621, by rfl⟩ : syracuseStep 3257657 = 2443243) B2443243
theorem B963911 : Blo 642303 963911 := bstep (se 1 (by rfl) ⟨722933, by rfl⟩ : syracuseStep 963911 = 1445867) B1445867
theorem B8795765 : Blo 642303 8795765 := bstep (se 5 (by rfl) ⟨412301, by rfl⟩ : syracuseStep 8795765 = 824603) B824603
theorem B3257981 : Blo 642303 3257981 := bstep (se 3 (by rfl) ⟨610871, by rfl⟩ : syracuseStep 3257981 = 1221743) B1221743
theorem B3094271 : Blo 642303 3094271 := bstep (se 1 (by rfl) ⟨2320703, by rfl⟩ : syracuseStep 3094271 = 4641407) B4641407
theorem B3258143 : Blo 642303 3258143 := bstep (se 1 (by rfl) ⟨2443607, by rfl⟩ : syracuseStep 3258143 = 4887215) B4887215
theorem B13252423 : Blo 642303 13252423 := bstep (se 1 (by rfl) ⟨9939317, by rfl⟩ : syracuseStep 13252423 = 19878635) B19878635
theorem B9943019 : Blo 642303 9943019 := bstep (se 1 (by rfl) ⟨7457264, by rfl⟩ : syracuseStep 9943019 = 14914529) B14914529
theorem B7452749 : Blo 642303 7452749 := bstep (se 3 (by rfl) ⟨1397390, by rfl⟩ : syracuseStep 7452749 = 2794781) B2794781
theorem B2177441 : Blo 642303 2177441 := bstep (se 2 (by rfl) ⟨816540, by rfl⟩ : syracuseStep 2177441 = 1633081) B1633081
theorem B1554923 : Blo 642303 1554923 := bstep (se 1 (by rfl) ⟨1166192, by rfl⟩ : syracuseStep 1554923 = 2332385) B2332385
theorem B3259439 : Blo 642303 3259439 := bstep (se 1 (by rfl) ⟨2444579, by rfl⟩ : syracuseStep 3259439 = 4889159) B4889159
theorem B736511 : Blo 642303 736511 := bstep (se 1 (by rfl) ⟨552383, by rfl⟩ : syracuseStep 736511 = 1104767) B1104767
theorem B965915 : Blo 642303 965915 := bstep (se 1 (by rfl) ⟨724436, by rfl⟩ : syracuseStep 965915 = 1448873) B1448873
theorem B966281 : Blo 642303 966281 := bstep (se 2 (by rfl) ⟨362355, by rfl⟩ : syracuseStep 966281 = 724711) B724711
theorem B2178899 : Blo 642303 2178899 := bstep (se 1 (by rfl) ⟨1634174, by rfl⟩ : syracuseStep 2178899 = 3268349) B3268349
theorem B2178953 : Blo 642303 2178953 := bstep (se 2 (by rfl) ⟨817107, by rfl⟩ : syracuseStep 2178953 = 1634215) B1634215
theorem B3260411 : Blo 642303 3260411 := bstep (se 1 (by rfl) ⟨2445308, by rfl⟩ : syracuseStep 3260411 = 4890617) B4890617
theorem B2441299 : Blo 642303 2441299 := bstep (se 1 (by rfl) ⟨1830974, by rfl⟩ : syracuseStep 2441299 = 3661949) B3661949
theorem B966815 : Blo 642303 966815 := bstep (se 1 (by rfl) ⟨725111, by rfl⟩ : syracuseStep 966815 = 1450223) B1450223
theorem B966953 : Blo 642303 966953 := bstep (se 2 (by rfl) ⟨362607, by rfl⟩ : syracuseStep 966953 = 725215) B725215
theorem B2474351 : Blo 642303 2474351 := bstep (se 1 (by rfl) ⟨1855763, by rfl⟩ : syracuseStep 2474351 = 3711527) B3711527
theorem B2605439 : Blo 642303 2605439 := bstep (se 1 (by rfl) ⟨1954079, by rfl⟩ : syracuseStep 2605439 = 3908159) B3908159
theorem B12403367 : Blo 642303 12403367 := bstep (se 1 (by rfl) ⟨9302525, by rfl⟩ : syracuseStep 12403367 = 18605051) B18605051
theorem B2179871 : Blo 642303 2179871 := bstep (se 1 (by rfl) ⟨1634903, by rfl⟩ : syracuseStep 2179871 = 3269807) B3269807
theorem B2606345 : Blo 642303 2606345 := bstep (se 2 (by rfl) ⟨977379, by rfl⟩ : syracuseStep 2606345 = 1954759) B1954759
theorem B2442743 : Blo 642303 2442743 := bstep (se 1 (by rfl) ⟨1832057, by rfl⟩ : syracuseStep 2442743 = 3664115) B3664115
theorem B968351 : Blo 642303 968351 := bstep (se 1 (by rfl) ⟨726263, by rfl⟩ : syracuseStep 968351 = 1452527) B1452527
theorem B9291455 : Blo 642303 9291455 := bstep (se 1 (by rfl) ⟨6968591, by rfl⟩ : syracuseStep 9291455 = 13937183) B13937183
theorem B968519 : Blo 642303 968519 := bstep (se 1 (by rfl) ⟨726389, by rfl⟩ : syracuseStep 968519 = 1452779) B1452779
theorem B13944791 : Blo 642303 13944791 := bstep (se 1 (by rfl) ⟨10458593, by rfl⟩ : syracuseStep 13944791 = 20917187) B20917187
theorem B2934767 : Blo 642303 2934767 := bstep (se 1 (by rfl) ⟨2201075, by rfl⟩ : syracuseStep 2934767 = 4402151) B4402151
theorem B2181167 : Blo 642303 2181167 := bstep (se 1 (by rfl) ⟨1635875, by rfl⟩ : syracuseStep 2181167 = 3271751) B3271751
theorem B3262679 : Blo 642303 3262679 := bstep (se 1 (by rfl) ⟨2447009, by rfl⟩ : syracuseStep 3262679 = 4894019) B4894019
theorem B969191 : Blo 642303 969191 := bstep (se 1 (by rfl) ⟨726893, by rfl⟩ : syracuseStep 969191 = 1453787) B1453787
theorem B11292157 : Blo 642303 11292157 := bstep (se 3 (by rfl) ⟨2117279, by rfl⟩ : syracuseStep 11292157 = 4234559) B4234559
theorem B642727 : Blo 642303 642727 := bstep (se 1 (by rfl) ⟨482045, by rfl⟩ : syracuseStep 642727 = 964091) B964091
theorem B642843 : Blo 642303 642843 := bstep (se 1 (by rfl) ⟨482132, by rfl⟩ : syracuseStep 642843 = 964265) B964265
theorem B642847 : Blo 642303 642847 := bstep (se 1 (by rfl) ⟨482135, by rfl⟩ : syracuseStep 642847 = 964271) B964271
theorem B1625953 : Blo 642303 1625953 := bstep (se 2 (by rfl) ⟨609732, by rfl⟩ : syracuseStep 1625953 = 1219465) B1219465
theorem B642927 : Blo 642303 642927 := bstep (se 1 (by rfl) ⟨482195, by rfl⟩ : syracuseStep 642927 = 964391) B964391
theorem B5885885 : Blo 642303 5885885 := bstep (se 3 (by rfl) ⟨1103603, by rfl⟩ : syracuseStep 5885885 = 2207207) B2207207
theorem B643279 : Blo 642303 643279 := bstep (se 1 (by rfl) ⟨482459, by rfl⟩ : syracuseStep 643279 = 964919) B964919
theorem B643327 : Blo 642303 643327 := bstep (se 1 (by rfl) ⟨482495, by rfl⟩ : syracuseStep 643327 = 964991) B964991
theorem B643399 : Blo 642303 643399 := bstep (se 1 (by rfl) ⟨482549, by rfl⟩ : syracuseStep 643399 = 965099) B965099
theorem B643559 : Blo 642303 643559 := bstep (se 1 (by rfl) ⟨482669, by rfl⟩ : syracuseStep 643559 = 965339) B965339
theorem B1856233 : Blo 642303 1856233 := bstep (se 2 (by rfl) ⟨696087, by rfl⟩ : syracuseStep 1856233 = 1392175) B1392175
theorem B3265271 : Blo 642303 3265271 := bstep (se 1 (by rfl) ⟨2448953, by rfl⟩ : syracuseStep 3265271 = 4897907) B4897907
theorem B644123 : Blo 642303 644123 := bstep (se 1 (by rfl) ⟨483092, by rfl⟩ : syracuseStep 644123 = 966185) B966185
theorem B644207 : Blo 642303 644207 := bstep (se 1 (by rfl) ⟨483155, by rfl⟩ : syracuseStep 644207 = 966311) B966311
theorem B644255 : Blo 642303 644255 := bstep (se 1 (by rfl) ⟨483191, by rfl⟩ : syracuseStep 644255 = 966383) B966383
theorem B644287 : Blo 642303 644287 := bstep (se 1 (by rfl) ⟨483215, by rfl⟩ : syracuseStep 644287 = 966431) B966431
theorem B644327 : Blo 642303 644327 := bstep (se 1 (by rfl) ⟨483245, by rfl⟩ : syracuseStep 644327 = 966491) B966491
theorem B3659033 : Blo 642303 3659033 := bstep (se 2 (by rfl) ⟨1372137, by rfl⟩ : syracuseStep 3659033 = 2744275) B2744275
theorem B644379 : Blo 642303 644379 := bstep (se 1 (by rfl) ⟨483284, by rfl⟩ : syracuseStep 644379 = 966569) B966569
theorem B9295145 : Blo 642303 9295145 := bstep (se 2 (by rfl) ⟨3485679, by rfl⟩ : syracuseStep 9295145 = 6971359) B6971359
theorem B644607 : Blo 642303 644607 := bstep (se 1 (by rfl) ⟨483455, by rfl⟩ : syracuseStep 644607 = 966911) B966911
theorem B1988819 : Blo 642303 1988819 := bstep (se 1 (by rfl) ⟨1491614, by rfl⟩ : syracuseStep 1988819 = 2983229) B2983229
theorem B18537011 : Blo 642303 18537011 := bstep (se 1 (by rfl) ⟨13902758, by rfl⟩ : syracuseStep 18537011 = 27805517) B27805517
theorem B3660673 : Blo 642303 3660673 := bstep (se 2 (by rfl) ⟨1372752, by rfl⟩ : syracuseStep 3660673 = 2745505) B2745505
theorem B1629305 : Blo 642303 1629305 := bstep (se 2 (by rfl) ⟨610989, by rfl⟩ : syracuseStep 1629305 = 1221979) B1221979
theorem B646303 : Blo 642303 646303 := bstep (se 1 (by rfl) ⟨484727, by rfl⟩ : syracuseStep 646303 = 969455) B969455
theorem B2645183 : Blo 642303 2645183 := bstep (se 1 (by rfl) ⟨1983887, by rfl⟩ : syracuseStep 2645183 = 3967775) B3967775
theorem B1629467 : Blo 642303 1629467 := bstep (se 1 (by rfl) ⟨1222100, by rfl⟩ : syracuseStep 1629467 = 2444201) B2444201
theorem B8838841 : Blo 642303 8838841 := bstep (se 2 (by rfl) ⟨3314565, by rfl⟩ : syracuseStep 8838841 = 6629131) B6629131
theorem B6185231 : Blo 642303 6185231 := bstep (se 1 (by rfl) ⟨4638923, by rfl⟩ : syracuseStep 6185231 = 9277847) B9277847
theorem B2941373 : Blo 642303 2941373 := bstep (se 3 (by rfl) ⟨551507, by rfl⟩ : syracuseStep 2941373 = 1103015) B1103015
theorem B3269159 : Blo 642303 3269159 := bstep (se 1 (by rfl) ⟨2451869, by rfl⟩ : syracuseStep 3269159 = 4903739) B4903739
theorem B1632595 : Blo 642303 1632595 := bstep (se 1 (by rfl) ⟨1224446, by rfl⟩ : syracuseStep 1632595 = 2448893) B2448893
theorem B1829243 : Blo 642303 1829243 := bstep (se 1 (by rfl) ⟨1371932, by rfl⟩ : syracuseStep 1829243 = 2743865) B2743865
theorem B1633223 : Blo 642303 1633223 := bstep (se 1 (by rfl) ⟨1224917, by rfl⟩ : syracuseStep 1633223 = 2449835) B2449835
theorem B1633385 : Blo 642303 1633385 := bstep (se 2 (by rfl) ⟨612519, by rfl⟩ : syracuseStep 1633385 = 1225039) B1225039
theorem B4877495 : Blo 642303 4877495 := bstep (se 1 (by rfl) ⟨3658121, by rfl⟩ : syracuseStep 4877495 = 7316243) B7316243
theorem B7335197 : Blo 642303 7335197 := bstep (se 3 (by rfl) ⟨1375349, by rfl⟩ : syracuseStep 7335197 = 2750699) B2750699
theorem B1830235 : Blo 642303 1830235 := bstep (se 1 (by rfl) ⟨1372676, by rfl⟩ : syracuseStep 1830235 = 2745353) B2745353
theorem B1863071 : Blo 642303 1863071 := bstep (se 1 (by rfl) ⟨1397303, by rfl⟩ : syracuseStep 1863071 = 2794607) B2794607
theorem B2453449 : Blo 642303 2453449 := bstep (se 2 (by rfl) ⟨920043, by rfl⟩ : syracuseStep 2453449 = 1840087) B1840087
theorem B20344841 : Blo 642303 20344841 := bstep (se 2 (by rfl) ⟨7629315, by rfl⟩ : syracuseStep 20344841 = 15258631) B15258631
theorem B4124819 : Blo 642303 4124819 := bstep (se 1 (by rfl) ⟨3093614, by rfl⟩ : syracuseStep 4124819 = 6187229) B6187229
theorem B2453753 : Blo 642303 2453753 := bstep (se 2 (by rfl) ⟨920157, by rfl⟩ : syracuseStep 2453753 = 1840315) B1840315
theorem B4125127 : Blo 642303 4125127 := bstep (se 1 (by rfl) ⟨3093845, by rfl⟩ : syracuseStep 4125127 = 6187691) B6187691
theorem B1471391 : Blo 642303 1471391 := bstep (se 1 (by rfl) ⟨1103543, by rfl⟩ : syracuseStep 1471391 = 2207087) B2207087
theorem B2946299 : Blo 642303 2946299 := bstep (se 1 (by rfl) ⟨2209724, by rfl⟩ : syracuseStep 2946299 = 4419449) B4419449
theorem B1635815 : Blo 642303 1635815 := bstep (se 1 (by rfl) ⟨1226861, by rfl⟩ : syracuseStep 1635815 = 2453723) B2453723
theorem B2323961 : Blo 642303 2323961 := bstep (se 2 (by rfl) ⟨871485, by rfl⟩ : syracuseStep 2323961 = 1742971) B1742971
theorem B1373915 : Blo 642303 1373915 := bstep (se 1 (by rfl) ⟨1030436, by rfl⟩ : syracuseStep 1373915 = 2060873) B2060873
theorem B1865555 : Blo 642303 1865555 := bstep (se 1 (by rfl) ⟨1399166, by rfl⟩ : syracuseStep 1865555 = 2798333) B2798333
theorem B4880411 : Blo 642303 4880411 := bstep (se 1 (by rfl) ⟨3660308, by rfl⟩ : syracuseStep 4880411 = 7320617) B7320617
theorem B982343 : Blo 642303 982343 := bstep (se 1 (by rfl) ⟨736757, by rfl⟩ : syracuseStep 982343 = 1473515) B1473515
theorem B44596757 : Blo 642303 44596757 := bstep (se 6 (by rfl) ⟨1045236, by rfl⟩ : syracuseStep 44596757 = 2090473) B2090473
theorem B1736959 : Blo 642303 1736959 := bstep (se 1 (by rfl) ⟨1302719, by rfl⟩ : syracuseStep 1736959 = 2605439) B2605439
theorem B6947315 : Blo 642303 6947315 := bstep (se 1 (by rfl) ⟨5210486, by rfl⟩ : syracuseStep 6947315 = 10420973) B10420973
theorem B1737563 : Blo 642303 1737563 := bstep (se 1 (by rfl) ⟨1303172, by rfl⟩ : syracuseStep 1737563 = 2606345) B2606345
theorem B12518351 : Blo 642303 12518351 := bstep (se 1 (by rfl) ⟨9388763, by rfl⟩ : syracuseStep 12518351 = 18777527) B18777527
theorem B6194303 : Blo 642303 6194303 := bstep (se 1 (by rfl) ⟨4645727, by rfl⟩ : syracuseStep 6194303 = 9291455) B9291455
theorem B1836989 : Blo 642303 1836989 := bstep (se 3 (by rfl) ⟨344435, by rfl⟩ : syracuseStep 1836989 = 688871) B688871
theorem B4655303 : Blo 642303 4655303 := bstep (se 1 (by rfl) ⟨3491477, by rfl⟩ : syracuseStep 4655303 = 6982955) B6982955
theorem B6196763 : Blo 642303 6196763 := bstep (se 1 (by rfl) ⟨4647572, by rfl⟩ : syracuseStep 6196763 = 9295145) B9295145
theorem B1446119 : Blo 642303 1446119 := bstep (se 1 (by rfl) ⟨1084589, by rfl⟩ : syracuseStep 1446119 = 2169179) B2169179
theorem B12358007 : Blo 642303 12358007 := bstep (se 1 (by rfl) ⟨9268505, by rfl⟩ : syracuseStep 12358007 = 18537011) B18537011
theorem B1086203 : Blo 642303 1086203 := bstep (se 1 (by rfl) ⟨814652, by rfl⟩ : syracuseStep 1086203 = 1629305) B1629305
theorem B5509943 : Blo 642303 5509943 := bstep (se 1 (by rfl) ⟨4132457, by rfl⟩ : syracuseStep 5509943 = 8264915) B8264915
theorem B1086311 : Blo 642303 1086311 := bstep (se 1 (by rfl) ⟨814733, by rfl⟩ : syracuseStep 1086311 = 1629467) B1629467
theorem B42407023 : Blo 642303 42407023 := bstep (se 1 (by rfl) ⟨31805267, by rfl⟩ : syracuseStep 42407023 = 63610535) B63610535
theorem B2167937 : Blo 642303 2167937 := bstep (se 2 (by rfl) ⟨812976, by rfl⟩ : syracuseStep 2167937 = 1625953) B1625953
theorem B15702113 : Blo 642303 15702113 := bstep (se 2 (by rfl) ⟨5888292, by rfl⟩ : syracuseStep 15702113 = 11776585) B11776585
theorem B41917409 : Blo 642303 41917409 := bstep (se 2 (by rfl) ⟨15719028, by rfl⟩ : syracuseStep 41917409 = 31438057) B31438057
theorem B1088815 : Blo 642303 1088815 := bstep (se 1 (by rfl) ⟨816611, by rfl⟩ : syracuseStep 1088815 = 1633223) B1633223
theorem B1088923 : Blo 642303 1088923 := bstep (se 1 (by rfl) ⟨816692, by rfl⟩ : syracuseStep 1088923 = 1633385) B1633385
theorem B3251663 : Blo 642303 3251663 := bstep (se 1 (by rfl) ⟨2438747, by rfl⟩ : syracuseStep 3251663 = 4877495) B4877495
theorem B4890131 : Blo 642303 4890131 := bstep (se 1 (by rfl) ⟨3667598, by rfl⟩ : syracuseStep 4890131 = 7335197) B7335197
theorem B17669897 : Blo 642303 17669897 := bstep (se 2 (by rfl) ⟨6626211, by rfl⟩ : syracuseStep 17669897 = 13252423) B13252423
theorem B2171771 : Blo 642303 2171771 := bstep (se 1 (by rfl) ⟨1628828, by rfl⟩ : syracuseStep 2171771 = 3257657) B3257657
theorem B1090543 : Blo 642303 1090543 := bstep (se 1 (by rfl) ⟨817907, by rfl⟩ : syracuseStep 1090543 = 1635815) B1635815
theorem B1549307 : Blo 642303 1549307 := bstep (se 1 (by rfl) ⟨1161980, by rfl⟩ : syracuseStep 1549307 = 2323961) B2323961
theorem B2171987 : Blo 642303 2171987 := bstep (se 1 (by rfl) ⟨1628990, by rfl⟩ : syracuseStep 2171987 = 3257981) B3257981
theorem B2172095 : Blo 642303 2172095 := bstep (se 1 (by rfl) ⟨1629071, by rfl⟩ : syracuseStep 2172095 = 3258143) B3258143
theorem B6628679 : Blo 642303 6628679 := bstep (se 1 (by rfl) ⟨4971509, by rfl⟩ : syracuseStep 6628679 = 9943019) B9943019
theorem B3253607 : Blo 642303 3253607 := bstep (se 1 (by rfl) ⟨2440205, by rfl⟩ : syracuseStep 3253607 = 4880411) B4880411
theorem B1451627 : Blo 642303 1451627 := bstep (se 1 (by rfl) ⟨1088720, by rfl⟩ : syracuseStep 1451627 = 2177441) B2177441
theorem B2172959 : Blo 642303 2172959 := bstep (se 1 (by rfl) ⟨1629719, by rfl⟩ : syracuseStep 2172959 = 3259439) B3259439
theorem B29731171 : Blo 642303 29731171 := bstep (se 1 (by rfl) ⟨22298378, by rfl⟩ : syracuseStep 29731171 = 44596757) B44596757
theorem B1452599 : Blo 642303 1452599 := bstep (se 1 (by rfl) ⟨1089449, by rfl⟩ : syracuseStep 1452599 = 2178899) B2178899
theorem B1452635 : Blo 642303 1452635 := bstep (se 1 (by rfl) ⟨1089476, by rfl⟩ : syracuseStep 1452635 = 2178953) B2178953
theorem B2173607 : Blo 642303 2173607 := bstep (se 1 (by rfl) ⟨1630205, by rfl⟩ : syracuseStep 2173607 = 3260411) B3260411
theorem B3255065 : Blo 642303 3255065 := bstep (se 2 (by rfl) ⟨1220649, by rfl⟩ : syracuseStep 3255065 = 2441299) B2441299
theorem B1452905 : Blo 642303 1452905 := bstep (se 2 (by rfl) ⟨544839, by rfl⟩ : syracuseStep 1452905 = 1089679) B1089679
theorem B1649567 : Blo 642303 1649567 := bstep (se 1 (by rfl) ⟨1237175, by rfl⟩ : syracuseStep 1649567 = 2474351) B2474351
theorem B1223657 : Blo 642303 1223657 := bstep (se 2 (by rfl) ⟨458871, by rfl⟩ : syracuseStep 1223657 = 917743) B917743
theorem B8268911 : Blo 642303 8268911 := bstep (se 1 (by rfl) ⟨6201683, by rfl⟩ : syracuseStep 8268911 = 12403367) B12403367
theorem B1453247 : Blo 642303 1453247 := bstep (se 1 (by rfl) ⟨1089935, by rfl⟩ : syracuseStep 1453247 = 2179871) B2179871
theorem B4238783 : Blo 642303 4238783 := bstep (se 1 (by rfl) ⟨3179087, by rfl⟩ : syracuseStep 4238783 = 6358175) B6358175
theorem B7843661 : Blo 642303 7843661 := bstep (se 3 (by rfl) ⟨1470686, by rfl⟩ : syracuseStep 7843661 = 2941373) B2941373
theorem B9285455 : Blo 642303 9285455 := bstep (se 1 (by rfl) ⟨6964091, by rfl⟩ : syracuseStep 9285455 = 13928183) B13928183
theorem B1454111 : Blo 642303 1454111 := bstep (se 1 (by rfl) ⟨1090583, by rfl⟩ : syracuseStep 1454111 = 2181167) B2181167
theorem B2175119 : Blo 642303 2175119 := bstep (se 1 (by rfl) ⟨1631339, by rfl⟩ : syracuseStep 2175119 = 3262679) B3262679
theorem B1159847 : Blo 642303 1159847 := bstep (se 1 (by rfl) ⟨869885, by rfl⟩ : syracuseStep 1159847 = 1739771) B1739771
theorem B963611 : Blo 642303 963611 := bstep (se 1 (by rfl) ⟨722708, by rfl⟩ : syracuseStep 963611 = 1445417) B1445417
theorem B58045943 : Blo 642303 58045943 := bstep (se 1 (by rfl) ⟨43534457, by rfl⟩ : syracuseStep 58045943 = 87068915) B87068915
theorem B964199 : Blo 642303 964199 := bstep (se 1 (by rfl) ⟨723149, by rfl⟩ : syracuseStep 964199 = 1446299) B1446299
theorem B2176793 : Blo 642303 2176793 := bstep (se 2 (by rfl) ⟨816297, by rfl⟩ : syracuseStep 2176793 = 1632595) B1632595
theorem B2176847 : Blo 642303 2176847 := bstep (se 1 (by rfl) ⟨1632635, by rfl⟩ : syracuseStep 2176847 = 3265271) B3265271
theorem B2439355 : Blo 642303 2439355 := bstep (se 1 (by rfl) ⟨1829516, by rfl⟩ : syracuseStep 2439355 = 3659033) B3659033
theorem B964967 : Blo 642303 964967 := bstep (se 1 (by rfl) ⟨723725, by rfl⟩ : syracuseStep 964967 = 1447451) B1447451
theorem B40155689 : Blo 642303 40155689 := bstep (se 2 (by rfl) ⟨15058383, by rfl⟩ : syracuseStep 40155689 = 30116767) B30116767
theorem B1325879 : Blo 642303 1325879 := bstep (se 1 (by rfl) ⟨994409, by rfl⟩ : syracuseStep 1325879 = 1988819) B1988819
theorem B2440313 : Blo 642303 2440313 := bstep (se 2 (by rfl) ⟨915117, by rfl⟩ : syracuseStep 2440313 = 1830235) B1830235
theorem B15056209 : Blo 642303 15056209 := bstep (se 2 (by rfl) ⟨5646078, by rfl⟩ : syracuseStep 15056209 = 11292157) B11292157
theorem B966683 : Blo 642303 966683 := bstep (se 1 (by rfl) ⟨725012, by rfl⟩ : syracuseStep 966683 = 1450025) B1450025
theorem B2179439 : Blo 642303 2179439 := bstep (se 1 (by rfl) ⟨1634579, by rfl⟩ : syracuseStep 2179439 = 3269159) B3269159
theorem B967067 : Blo 642303 967067 := bstep (se 1 (by rfl) ⟨725300, by rfl⟩ : syracuseStep 967067 = 1450601) B1450601
theorem B967583 : Blo 642303 967583 := bstep (se 1 (by rfl) ⟨725687, by rfl⟩ : syracuseStep 967583 = 1451375) B1451375
theorem B2474977 : Blo 642303 2474977 := bstep (se 2 (by rfl) ⟨928116, by rfl⟩ : syracuseStep 2474977 = 1856233) B1856233
theorem B4146461 : Blo 642303 4146461 := bstep (se 3 (by rfl) ⟨777461, by rfl⟩ : syracuseStep 4146461 = 1554923) B1554923
theorem B967991 : Blo 642303 967991 := bstep (se 1 (by rfl) ⟨725993, by rfl⟩ : syracuseStep 967991 = 1451987) B1451987
theorem B968063 : Blo 642303 968063 := bstep (se 1 (by rfl) ⟨726047, by rfl⟩ : syracuseStep 968063 = 1452095) B1452095
theorem B3263975 : Blo 642303 3263975 := bstep (se 1 (by rfl) ⟨2447981, by rfl⟩ : syracuseStep 3263975 = 4895963) B4895963
theorem B642607 : Blo 642303 642607 := bstep (se 1 (by rfl) ⟨481955, by rfl⟩ : syracuseStep 642607 = 963911) B963911
theorem B4968499 : Blo 642303 4968499 := bstep (se 1 (by rfl) ⟨3726374, by rfl⟩ : syracuseStep 4968499 = 7452749) B7452749
theorem B1101961 : Blo 642303 1101961 := bstep (se 2 (by rfl) ⟨413235, by rfl⟩ : syracuseStep 1101961 = 826471) B826471
theorem B6181541 : Blo 642303 6181541 := bstep (se 4 (by rfl) ⟨579519, by rfl⟩ : syracuseStep 6181541 = 1159039) B1159039
theorem B643943 : Blo 642303 643943 := bstep (se 1 (by rfl) ⟨482957, by rfl⟩ : syracuseStep 643943 = 965915) B965915
theorem B11785121 : Blo 642303 11785121 := bstep (se 2 (by rfl) ⟨4419420, by rfl⟩ : syracuseStep 11785121 = 8838841) B8838841
theorem B644187 : Blo 642303 644187 := bstep (se 1 (by rfl) ⟨483140, by rfl⟩ : syracuseStep 644187 = 966281) B966281
theorem B644543 : Blo 642303 644543 := bstep (se 1 (by rfl) ⟨483407, by rfl⟩ : syracuseStep 644543 = 966815) B966815
theorem B644635 : Blo 642303 644635 := bstep (se 1 (by rfl) ⟨483476, by rfl⟩ : syracuseStep 644635 = 966953) B966953
theorem B1628495 : Blo 642303 1628495 := bstep (se 1 (by rfl) ⟨1221371, by rfl⟩ : syracuseStep 1628495 = 2442743) B2442743
theorem B645567 : Blo 642303 645567 := bstep (se 1 (by rfl) ⟨484175, by rfl⟩ : syracuseStep 645567 = 968351) B968351
theorem B645679 : Blo 642303 645679 := bstep (se 1 (by rfl) ⟨484259, by rfl⟩ : syracuseStep 645679 = 968519) B968519
theorem B9296527 : Blo 642303 9296527 := bstep (se 1 (by rfl) ⟨6972395, by rfl⟩ : syracuseStep 9296527 = 13944791) B13944791
theorem B1956511 : Blo 642303 1956511 := bstep (se 1 (by rfl) ⟨1467383, by rfl⟩ : syracuseStep 1956511 = 2934767) B2934767
theorem B646127 : Blo 642303 646127 := bstep (se 1 (by rfl) ⟨484595, by rfl⟩ : syracuseStep 646127 = 969191) B969191
theorem B3923923 : Blo 642303 3923923 := bstep (se 1 (by rfl) ⟨2942942, by rfl⟩ : syracuseStep 3923923 = 5885885) B5885885
theorem B7856797 : Blo 642303 7856797 := bstep (se 3 (by rfl) ⟨1473149, by rfl⟩ : syracuseStep 7856797 = 2946299) B2946299
theorem B2320271 : Blo 642303 2320271 := bstep (se 1 (by rfl) ⟨1740203, by rfl⟩ : syracuseStep 2320271 = 3480407) B3480407
theorem B1763455 : Blo 642303 1763455 := bstep (se 1 (by rfl) ⟨1322591, by rfl⟩ : syracuseStep 1763455 = 2645183) B2645183
theorem B2451809 : Blo 642303 2451809 := bstep (se 2 (by rfl) ⟨919428, by rfl⟩ : syracuseStep 2451809 = 1838857) B1838857
theorem B3271265 : Blo 642303 3271265 := bstep (se 2 (by rfl) ⟨1226724, by rfl⟩ : syracuseStep 3271265 = 2453449) B2453449
theorem B4123487 : Blo 642303 4123487 := bstep (se 1 (by rfl) ⟨3092615, by rfl⟩ : syracuseStep 4123487 = 6185231) B6185231
theorem B978025 : Blo 642303 978025 := bstep (se 2 (by rfl) ⟨366759, by rfl⟩ : syracuseStep 978025 = 733519) B733519
theorem B5500169 : Blo 642303 5500169 := bstep (se 2 (by rfl) ⟨2062563, by rfl⟩ : syracuseStep 5500169 = 4125127) B4125127
theorem B4877981 : Blo 642303 4877981 := bstep (se 3 (by rfl) ⟨914621, by rfl⟩ : syracuseStep 4877981 = 1829243) B1829243
theorem B6975163 : Blo 642303 6975163 := bstep (se 1 (by rfl) ⟨5231372, by rfl⟩ : syracuseStep 6975163 = 10462745) B10462745
theorem B9924299 : Blo 642303 9924299 := bstep (se 1 (by rfl) ⟨7443224, by rfl⟩ : syracuseStep 9924299 = 14886449) B14886449
theorem B16741241 : Blo 642303 16741241 := bstep (se 2 (by rfl) ⟨6277965, by rfl⟩ : syracuseStep 16741241 = 12555931) B12555931
theorem B1242047 : Blo 642303 1242047 := bstep (se 1 (by rfl) ⟨931535, by rfl⟩ : syracuseStep 1242047 = 1863071) B1863071
theorem B13563227 : Blo 642303 13563227 := bstep (se 1 (by rfl) ⟨10172420, by rfl⟩ : syracuseStep 13563227 = 20344841) B20344841
theorem B2749879 : Blo 642303 2749879 := bstep (se 1 (by rfl) ⟨2062409, by rfl⟩ : syracuseStep 2749879 = 4124819) B4124819
theorem B1635835 : Blo 642303 1635835 := bstep (se 1 (by rfl) ⟨1226876, by rfl⟩ : syracuseStep 1635835 = 2453753) B2453753
theorem B816799 : Blo 642303 816799 := bstep (se 1 (by rfl) ⟨612599, by rfl⟩ : syracuseStep 816799 = 1225199) B1225199
theorem B980927 : Blo 642303 980927 := bstep (se 1 (by rfl) ⟨735695, by rfl⟩ : syracuseStep 980927 = 1471391) B1471391
theorem B1964029 : Blo 642303 1964029 := bstep (se 3 (by rfl) ⟨368255, by rfl⟩ : syracuseStep 1964029 = 736511) B736511
theorem B5863843 : Blo 642303 5863843 := bstep (se 1 (by rfl) ⟨4397882, by rfl⟩ : syracuseStep 5863843 = 8795765) B8795765
theorem B915943 : Blo 642303 915943 := bstep (se 1 (by rfl) ⟨686957, by rfl⟩ : syracuseStep 915943 = 1373915) B1373915
theorem B2062847 : Blo 642303 2062847 := bstep (se 1 (by rfl) ⟨1547135, by rfl⟩ : syracuseStep 2062847 = 3094271) B3094271
theorem B4880897 : Blo 642303 4880897 := bstep (se 2 (by rfl) ⟨1830336, by rfl⟩ : syracuseStep 4880897 = 3660673) B3660673
theorem B1243703 : Blo 642303 1243703 := bstep (se 1 (by rfl) ⟨932777, by rfl⟩ : syracuseStep 1243703 = 1865555) B1865555
theorem B654895 : Blo 642303 654895 := bstep (se 1 (by rfl) ⟨491171, by rfl⟩ : syracuseStep 654895 = 982343) B982343
theorem B4128509 : Blo 642303 4128509 := bstep (se 3 (by rfl) ⟨774095, by rfl⟩ : syracuseStep 4128509 = 1548191) B1548191
theorem B4129535 : Blo 642303 4129535 := bstep (se 1 (by rfl) ⟨3097151, by rfl⟩ : syracuseStep 4129535 = 6194303) B6194303
theorem B4131175 : Blo 642303 4131175 := bstep (se 1 (by rfl) ⟨3098381, by rfl⟩ : syracuseStep 4131175 = 6196763) B6196763
theorem B4131485 : Blo 642303 4131485 := bstep (se 3 (by rfl) ⟨774653, by rfl⟩ : syracuseStep 4131485 = 1549307) B1549307
theorem B724135 : Blo 642303 724135 := bstep (se 1 (by rfl) ⟨543101, by rfl⟩ : syracuseStep 724135 = 1086203) B1086203
theorem B3673295 : Blo 642303 3673295 := bstep (se 1 (by rfl) ⟨2754971, by rfl⟩ : syracuseStep 3673295 = 5509943) B5509943
theorem B724207 : Blo 642303 724207 := bstep (se 1 (by rfl) ⟨543155, by rfl⟩ : syracuseStep 724207 = 1086311) B1086311
theorem B1445291 : Blo 642303 1445291 := bstep (se 1 (by rfl) ⟨1083968, by rfl⟩ : syracuseStep 1445291 = 2167937) B2167937
theorem B1085663 : Blo 642303 1085663 := bstep (se 1 (by rfl) ⟨814247, by rfl⟩ : syracuseStep 1085663 = 1628495) B1628495
theorem B2167775 : Blo 642303 2167775 := bstep (se 1 (by rfl) ⟨1625831, by rfl⟩ : syracuseStep 2167775 = 3251663) B3251663
theorem B6624665 : Blo 642303 6624665 := bstep (se 2 (by rfl) ⟨2484249, by rfl⟩ : syracuseStep 6624665 = 4968499) B4968499
theorem B1447847 : Blo 642303 1447847 := bstep (se 1 (by rfl) ⟨1085885, by rfl⟩ : syracuseStep 1447847 = 2171771) B2171771
theorem B1447991 : Blo 642303 1447991 := bstep (se 1 (by rfl) ⟨1085993, by rfl⟩ : syracuseStep 1447991 = 2171987) B2171987
theorem B1448063 : Blo 642303 1448063 := bstep (se 1 (by rfl) ⟨1086047, by rfl⟩ : syracuseStep 1448063 = 2172095) B2172095
theorem B2169071 : Blo 642303 2169071 := bstep (se 1 (by rfl) ⟨1626803, by rfl⟩ : syracuseStep 2169071 = 3253607) B3253607
theorem B1546847 : Blo 642303 1546847 := bstep (se 1 (by rfl) ⟨1160135, by rfl⟩ : syracuseStep 1546847 = 2320271) B2320271
theorem B1448639 : Blo 642303 1448639 := bstep (se 1 (by rfl) ⟨1086479, by rfl⟩ : syracuseStep 1448639 = 2172959) B2172959
theorem B1449071 : Blo 642303 1449071 := bstep (se 1 (by rfl) ⟨1086803, by rfl⟩ : syracuseStep 1449071 = 2173607) B2173607
theorem B2170043 : Blo 642303 2170043 := bstep (se 1 (by rfl) ⟨1627532, by rfl⟩ : syracuseStep 2170043 = 3255065) B3255065
theorem B5512607 : Blo 642303 5512607 := bstep (se 1 (by rfl) ⟨4134455, by rfl⟩ : syracuseStep 5512607 = 8268911) B8268911
theorem B1089065 : Blo 642303 1089065 := bstep (se 2 (by rfl) ⟨408399, by rfl⟩ : syracuseStep 1089065 = 816799) B816799
theorem B2825855 : Blo 642303 2825855 := bstep (se 1 (by rfl) ⟨2119391, by rfl⟩ : syracuseStep 2825855 = 4238783) B4238783
theorem B3251987 : Blo 642303 3251987 := bstep (se 1 (by rfl) ⟨2438990, by rfl⟩ : syracuseStep 3251987 = 4877981) B4877981
theorem B1450079 : Blo 642303 1450079 := bstep (se 1 (by rfl) ⟨1087559, by rfl⟩ : syracuseStep 1450079 = 2175119) B2175119
theorem B3252473 : Blo 642303 3252473 := bstep (se 2 (by rfl) ⟨1219677, by rfl⟩ : syracuseStep 3252473 = 2439355) B2439355
theorem B828031 : Blo 642303 828031 := bstep (se 1 (by rfl) ⟨621023, by rfl⟩ : syracuseStep 828031 = 1242047) B1242047
theorem B1221257 : Blo 642303 1221257 := bstep (se 2 (by rfl) ⟨457971, by rfl⟩ : syracuseStep 1221257 = 915943) B915943
theorem B12395369 : Blo 642303 12395369 := bstep (se 2 (by rfl) ⟨4648263, by rfl⟩ : syracuseStep 12395369 = 9296527) B9296527
theorem B37200869 : Blo 642303 37200869 := bstep (se 4 (by rfl) ⟨3487581, by rfl⟩ : syracuseStep 37200869 = 6975163) B6975163
theorem B1451195 : Blo 642303 1451195 := bstep (se 1 (by rfl) ⟨1088396, by rfl⟩ : syracuseStep 1451195 = 2176793) B2176793
theorem B1451231 : Blo 642303 1451231 := bstep (se 1 (by rfl) ⟨1088423, by rfl⟩ : syracuseStep 1451231 = 2176847) B2176847
theorem B3253931 : Blo 642303 3253931 := bstep (se 1 (by rfl) ⟨2440448, by rfl⟩ : syracuseStep 3253931 = 4880897) B4880897
theorem B829135 : Blo 642303 829135 := bstep (se 1 (by rfl) ⟨621851, by rfl⟩ : syracuseStep 829135 = 1243703) B1243703
theorem B1451753 : Blo 642303 1451753 := bstep (se 2 (by rfl) ⟨544407, by rfl⟩ : syracuseStep 1451753 = 1088815) B1088815
theorem B1451897 : Blo 642303 1451897 := bstep (se 2 (by rfl) ⟨544461, by rfl⟩ : syracuseStep 1451897 = 1088923) B1088923
theorem B1452959 : Blo 642303 1452959 := bstep (se 1 (by rfl) ⟨1089719, by rfl⟩ : syracuseStep 1452959 = 2179439) B2179439
theorem B4631543 : Blo 642303 4631543 := bstep (se 1 (by rfl) ⟨3473657, by rfl⟩ : syracuseStep 4631543 = 6947315) B6947315
theorem B2764307 : Blo 642303 2764307 := bstep (se 1 (by rfl) ⟨2073230, by rfl⟩ : syracuseStep 2764307 = 4146461) B4146461
theorem B1224659 : Blo 642303 1224659 := bstep (se 1 (by rfl) ⟨918494, by rfl⟩ : syracuseStep 1224659 = 1836989) B1836989
theorem B1454057 : Blo 642303 1454057 := bstep (se 2 (by rfl) ⟨545271, by rfl⟩ : syracuseStep 1454057 = 1090543) B1090543
theorem B2175983 : Blo 642303 2175983 := bstep (se 1 (by rfl) ⟨1631987, by rfl⟩ : syracuseStep 2175983 = 3263975) B3263975
theorem B964079 : Blo 642303 964079 := bstep (se 1 (by rfl) ⟨723059, by rfl⟩ : syracuseStep 964079 = 1446119) B1446119
theorem B8238671 : Blo 642303 8238671 := bstep (se 1 (by rfl) ⟨6179003, by rfl⟩ : syracuseStep 8238671 = 12358007) B12358007
theorem B10468075 : Blo 642303 10468075 := bstep (se 1 (by rfl) ⟨7851056, by rfl⟩ : syracuseStep 10468075 = 15702113) B15702113
theorem B3260087 : Blo 642303 3260087 := bstep (se 1 (by rfl) ⟨2445065, by rfl⟩ : syracuseStep 3260087 = 4890131) B4890131
theorem B11779931 : Blo 642303 11779931 := bstep (se 1 (by rfl) ⟨8834948, by rfl⟩ : syracuseStep 11779931 = 17669897) B17669897
theorem B967751 : Blo 642303 967751 := bstep (se 1 (by rfl) ⟨725813, by rfl⟩ : syracuseStep 967751 = 1451627) B1451627
theorem B56542697 : Blo 642303 56542697 := bstep (se 2 (by rfl) ⟨21203511, by rfl⟩ : syracuseStep 56542697 = 42407023) B42407023
theorem B968399 : Blo 642303 968399 := bstep (se 1 (by rfl) ⟨726299, by rfl⟩ : syracuseStep 968399 = 1452599) B1452599
theorem B968423 : Blo 642303 968423 := bstep (se 1 (by rfl) ⟨726317, by rfl⟩ : syracuseStep 968423 = 1452635) B1452635
theorem B2180843 : Blo 642303 2180843 := bstep (se 1 (by rfl) ⟨1635632, by rfl⟩ : syracuseStep 2180843 = 3271265) B3271265
theorem B80299781 : Blo 642303 80299781 := bstep (se 4 (by rfl) ⟨7528104, by rfl⟩ : syracuseStep 80299781 = 15056209) B15056209
theorem B968603 : Blo 642303 968603 := bstep (se 1 (by rfl) ⟨726452, by rfl⟩ : syracuseStep 968603 = 1452905) B1452905
theorem B1099711 : Blo 642303 1099711 := bstep (se 1 (by rfl) ⟨824783, by rfl⟩ : syracuseStep 1099711 = 1649567) B1649567
theorem B2181113 : Blo 642303 2181113 := bstep (se 2 (by rfl) ⟨817917, by rfl⟩ : syracuseStep 2181113 = 1635835) B1635835
theorem B968831 : Blo 642303 968831 := bstep (se 1 (by rfl) ⟨726623, by rfl⟩ : syracuseStep 968831 = 1453247) B1453247
theorem B5229107 : Blo 642303 5229107 := bstep (se 1 (by rfl) ⟨3921830, by rfl⟩ : syracuseStep 5229107 = 7843661) B7843661
theorem B969407 : Blo 642303 969407 := bstep (se 1 (by rfl) ⟨727055, by rfl⟩ : syracuseStep 969407 = 1454111) B1454111
theorem B3492773 : Blo 642303 3492773 := bstep (se 4 (by rfl) ⟨327447, by rfl⟩ : syracuseStep 3492773 = 654895) B654895
theorem B773231 : Blo 642303 773231 := bstep (se 1 (by rfl) ⟨579923, by rfl⟩ : syracuseStep 773231 = 1159847) B1159847
theorem B7818457 : Blo 642303 7818457 := bstep (se 2 (by rfl) ⟨2931921, by rfl⟩ : syracuseStep 7818457 = 5863843) B5863843
theorem B11160827 : Blo 642303 11160827 := bstep (se 1 (by rfl) ⟨8370620, by rfl⟩ : syracuseStep 11160827 = 16741241) B16741241
theorem B642407 : Blo 642303 642407 := bstep (se 1 (by rfl) ⟨481805, by rfl⟩ : syracuseStep 642407 = 963611) B963611
theorem B2608681 : Blo 642303 2608681 := bstep (se 2 (by rfl) ⟨978255, by rfl⟩ : syracuseStep 2608681 = 1956511) B1956511
theorem B18534005 : Blo 642303 18534005 := bstep (se 5 (by rfl) ⟨868781, by rfl⟩ : syracuseStep 18534005 = 1737563) B1737563
theorem B642799 : Blo 642303 642799 := bstep (se 1 (by rfl) ⟨482099, by rfl⟩ : syracuseStep 642799 = 964199) B964199
theorem B643311 : Blo 642303 643311 := bstep (se 1 (by rfl) ⟨482483, by rfl⟩ : syracuseStep 643311 = 964967) B964967
theorem B1626875 : Blo 642303 1626875 := bstep (se 1 (by rfl) ⟨1220156, by rfl⟩ : syracuseStep 1626875 = 2440313) B2440313
theorem B24761213 : Blo 642303 24761213 := bstep (se 3 (by rfl) ⟨4642727, by rfl⟩ : syracuseStep 24761213 = 9285455) B9285455
theorem B5231897 : Blo 642303 5231897 := bstep (se 2 (by rfl) ⟨1961961, by rfl⟩ : syracuseStep 5231897 = 3923923) B3923923
theorem B644455 : Blo 642303 644455 := bstep (se 1 (by rfl) ⟨483341, by rfl⟩ : syracuseStep 644455 = 966683) B966683
theorem B644711 : Blo 642303 644711 := bstep (se 1 (by rfl) ⟨483533, by rfl⟩ : syracuseStep 644711 = 967067) B967067
theorem B2315945 : Blo 642303 2315945 := bstep (se 2 (by rfl) ⟨868479, by rfl⟩ : syracuseStep 2315945 = 1736959) B1736959
theorem B645055 : Blo 642303 645055 := bstep (se 1 (by rfl) ⟨483791, by rfl⟩ : syracuseStep 645055 = 967583) B967583
theorem B8345567 : Blo 642303 8345567 := bstep (se 1 (by rfl) ⟨6259175, by rfl⟩ : syracuseStep 8345567 = 12518351) B12518351
theorem B645327 : Blo 642303 645327 := bstep (se 1 (by rfl) ⟨483995, by rfl⟩ : syracuseStep 645327 = 967991) B967991
theorem B10475729 : Blo 642303 10475729 := bstep (se 2 (by rfl) ⟨3928398, by rfl⟩ : syracuseStep 10475729 = 7856797) B7856797
theorem B645375 : Blo 642303 645375 := bstep (se 1 (by rfl) ⟨484031, by rfl⟩ : syracuseStep 645375 = 968063) B968063
theorem B3299969 : Blo 642303 3299969 := bstep (se 2 (by rfl) ⟨1237488, by rfl⟩ : syracuseStep 3299969 = 2474977) B2474977
theorem B3103535 : Blo 642303 3103535 := bstep (se 1 (by rfl) ⟨2327651, by rfl⟩ : syracuseStep 3103535 = 4655303) B4655303
theorem B2351273 : Blo 642303 2351273 := bstep (se 2 (by rfl) ⟨881727, by rfl⟩ : syracuseStep 2351273 = 1763455) B1763455
theorem B4121027 : Blo 642303 4121027 := bstep (se 1 (by rfl) ⟨3090770, by rfl⟩ : syracuseStep 4121027 = 6181541) B6181541
theorem B39641561 : Blo 642303 39641561 := bstep (se 2 (by rfl) ⟨14865585, by rfl⟩ : syracuseStep 39641561 = 29731171) B29731171
theorem B7856747 : Blo 642303 7856747 := bstep (se 1 (by rfl) ⟨5892560, by rfl⟩ : syracuseStep 7856747 = 11785121) B11785121
theorem B154789181 : Blo 642303 154789181 := bstep (se 3 (by rfl) ⟨29022971, by rfl⟩ : syracuseStep 154789181 = 58045943) B58045943
theorem B1304033 : Blo 642303 1304033 := bstep (se 2 (by rfl) ⟨489012, by rfl⟩ : syracuseStep 1304033 = 978025) B978025
theorem B27944939 : Blo 642303 27944939 := bstep (se 1 (by rfl) ⟨20958704, by rfl⟩ : syracuseStep 27944939 = 41917409) B41917409
theorem B1469281 : Blo 642303 1469281 := bstep (se 2 (by rfl) ⟨550980, by rfl⟩ : syracuseStep 1469281 = 1101961) B1101961
theorem B4419119 : Blo 642303 4419119 := bstep (se 1 (by rfl) ⟨3314339, by rfl⟩ : syracuseStep 4419119 = 6628679) B6628679
theorem B1634539 : Blo 642303 1634539 := bstep (se 1 (by rfl) ⟨1225904, by rfl⟩ : syracuseStep 1634539 = 2451809) B2451809
theorem B2748991 : Blo 642303 2748991 := bstep (se 1 (by rfl) ⟨2061743, by rfl⟩ : syracuseStep 2748991 = 4123487) B4123487
theorem B3666505 : Blo 642303 3666505 := bstep (se 2 (by rfl) ⟨1374939, by rfl⟩ : syracuseStep 3666505 = 2749879) B2749879
theorem B815771 : Blo 642303 815771 := bstep (se 1 (by rfl) ⟨611828, by rfl⟩ : syracuseStep 815771 = 1223657) B1223657
theorem B3666779 : Blo 642303 3666779 := bstep (se 1 (by rfl) ⟨2750084, by rfl⟩ : syracuseStep 3666779 = 5500169) B5500169
theorem B6616199 : Blo 642303 6616199 := bstep (se 1 (by rfl) ⟨4962149, by rfl⟩ : syracuseStep 6616199 = 9924299) B9924299
theorem B2618705 : Blo 642303 2618705 := bstep (se 2 (by rfl) ⟨982014, by rfl⟩ : syracuseStep 2618705 = 1964029) B1964029
theorem B9042151 : Blo 642303 9042151 := bstep (se 1 (by rfl) ⟨6781613, by rfl⟩ : syracuseStep 9042151 = 13563227) B13563227
theorem B653951 : Blo 642303 653951 := bstep (se 1 (by rfl) ⟨490463, by rfl⟩ : syracuseStep 653951 = 980927) B980927
theorem B1375231 : Blo 642303 1375231 := bstep (se 1 (by rfl) ⟨1031423, by rfl⟩ : syracuseStep 1375231 = 2062847) B2062847
theorem B26770459 : Blo 642303 26770459 := bstep (se 1 (by rfl) ⟨20077844, by rfl⟩ : syracuseStep 26770459 = 40155689) B40155689
theorem B883919 : Blo 642303 883919 := bstep (se 1 (by rfl) ⟨662939, by rfl⟩ : syracuseStep 883919 = 1325879) B1325879
theorem B11009357 : Blo 642303 11009357 := bstep (se 3 (by rfl) ⟨2064254, by rfl⟩ : syracuseStep 11009357 = 4128509) B4128509
theorem B2753023 : Blo 642303 2753023 := bstep (se 1 (by rfl) ⟨2064767, by rfl⟩ : syracuseStep 2753023 = 4129535) B4129535
theorem B2754323 : Blo 642303 2754323 := bstep (se 1 (by rfl) ⟨2065742, by rfl⟩ : syracuseStep 2754323 = 4131485) B4131485
theorem B2328515 : Blo 642303 2328515 := bstep (se 1 (by rfl) ⟨1746386, by rfl⟩ : syracuseStep 2328515 = 3492773) B3492773
theorem B7440551 : Blo 642303 7440551 := bstep (se 1 (by rfl) ⟨5580413, by rfl⟩ : syracuseStep 7440551 = 11160827) B11160827
theorem B12356003 : Blo 642303 12356003 := bstep (se 1 (by rfl) ⟨9267002, by rfl⟩ : syracuseStep 12356003 = 18534005) B18534005
theorem B723775 : Blo 642303 723775 := bstep (se 1 (by rfl) ⟨542831, by rfl⟩ : syracuseStep 723775 = 1085663) B1085663
theorem B5508233 : Blo 642303 5508233 := bstep (se 2 (by rfl) ⟨2065587, by rfl⟩ : syracuseStep 5508233 = 4131175) B4131175
theorem B1084583 : Blo 642303 1084583 := bstep (se 1 (by rfl) ⟨813437, by rfl⟩ : syracuseStep 1084583 = 1626875) B1626875
theorem B1445183 : Blo 642303 1445183 := bstep (se 1 (by rfl) ⟨1083887, by rfl⟩ : syracuseStep 1445183 = 2167775) B2167775
theorem B1543963 : Blo 642303 1543963 := bstep (se 1 (by rfl) ⟨1157972, by rfl⟩ : syracuseStep 1543963 = 2315945) B2315945
theorem B3477421 : Blo 642303 3477421 := bstep (se 3 (by rfl) ⟨652016, by rfl⟩ : syracuseStep 3477421 = 1304033) B1304033
theorem B6983819 : Blo 642303 6983819 := bstep (se 1 (by rfl) ⟨5237864, by rfl⟩ : syracuseStep 6983819 = 10475729) B10475729
theorem B1446047 : Blo 642303 1446047 := bstep (se 1 (by rfl) ⟨1084535, by rfl⟩ : syracuseStep 1446047 = 2169071) B2169071
theorem B10424609 : Blo 642303 10424609 := bstep (se 2 (by rfl) ⟨3909228, by rfl⟩ : syracuseStep 10424609 = 7818457) B7818457
theorem B2199979 : Blo 642303 2199979 := bstep (se 1 (by rfl) ⟨1649984, by rfl⟩ : syracuseStep 2199979 = 3299969) B3299969
theorem B2069023 : Blo 642303 2069023 := bstep (se 1 (by rfl) ⟨1551767, by rfl⟩ : syracuseStep 2069023 = 3103535) B3103535
theorem B3478241 : Blo 642303 3478241 := bstep (se 2 (by rfl) ⟨1304340, by rfl⟩ : syracuseStep 3478241 = 2608681) B2608681
theorem B1446695 : Blo 642303 1446695 := bstep (se 1 (by rfl) ⟨1085021, by rfl⟩ : syracuseStep 1446695 = 2170043) B2170043
theorem B3675071 : Blo 642303 3675071 := bstep (se 1 (by rfl) ⟨2756303, by rfl⟩ : syracuseStep 3675071 = 5512607) B5512607
theorem B726043 : Blo 642303 726043 := bstep (se 1 (by rfl) ⟨544532, by rfl⟩ : syracuseStep 726043 = 1089065) B1089065
theorem B2167991 : Blo 642303 2167991 := bstep (se 1 (by rfl) ⟨1625993, by rfl⟩ : syracuseStep 2167991 = 3251987) B3251987
theorem B2168315 : Blo 642303 2168315 := bstep (se 1 (by rfl) ⟨1626236, by rfl⟩ : syracuseStep 2168315 = 3252473) B3252473
theorem B8263579 : Blo 642303 8263579 := bstep (se 1 (by rfl) ⟨6197684, by rfl⟩ : syracuseStep 8263579 = 12395369) B12395369
theorem B4888673 : Blo 642303 4888673 := bstep (se 2 (by rfl) ⟨1833252, by rfl⟩ : syracuseStep 4888673 = 3666505) B3666505
theorem B103192787 : Blo 642303 103192787 := bstep (se 1 (by rfl) ⟨77394590, by rfl⟩ : syracuseStep 103192787 = 154789181) B154789181
theorem B2169287 : Blo 642303 2169287 := bstep (se 1 (by rfl) ⟨1626965, by rfl⟩ : syracuseStep 2169287 = 3253931) B3253931
theorem B1743869 : Blo 642303 1743869 := bstep (se 3 (by rfl) ⟨326975, by rfl⟩ : syracuseStep 1743869 = 653951) B653951
theorem B3087695 : Blo 642303 3087695 := bstep (se 1 (by rfl) ⟨2315771, by rfl⟩ : syracuseStep 3087695 = 4631543) B4631543
theorem B1842871 : Blo 642303 1842871 := bstep (se 1 (by rfl) ⟨1382153, by rfl⟩ : syracuseStep 1842871 = 2764307) B2764307
theorem B1450655 : Blo 642303 1450655 := bstep (se 1 (by rfl) ⟨1087991, by rfl⟩ : syracuseStep 1450655 = 2175983) B2175983
theorem B1745803 : Blo 642303 1745803 := bstep (se 1 (by rfl) ⟨1309352, by rfl⟩ : syracuseStep 1745803 = 2618705) B2618705
theorem B35693945 : Blo 642303 35693945 := bstep (se 2 (by rfl) ⟨13385229, by rfl⟩ : syracuseStep 35693945 = 26770459) B26770459
theorem B2173391 : Blo 642303 2173391 := bstep (se 1 (by rfl) ⟨1630043, by rfl⟩ : syracuseStep 2173391 = 3260087) B3260087
theorem B6270061 : Blo 642303 6270061 := bstep (se 3 (by rfl) ⟨1175636, by rfl⟩ : syracuseStep 6270061 = 2351273) B2351273
theorem B37695131 : Blo 642303 37695131 := bstep (se 1 (by rfl) ⟨28271348, by rfl⟩ : syracuseStep 37695131 = 56542697) B56542697
theorem B1453895 : Blo 642303 1453895 := bstep (se 1 (by rfl) ⟨1090421, by rfl⟩ : syracuseStep 1453895 = 2180843) B2180843
theorem B1454075 : Blo 642303 1454075 := bstep (se 1 (by rfl) ⟨1090556, by rfl⟩ : syracuseStep 1454075 = 2181113) B2181113
theorem B3256685 : Blo 642303 3256685 := bstep (se 3 (by rfl) ⟨610628, by rfl⟩ : syracuseStep 3256685 = 1221257) B1221257
theorem B3486071 : Blo 642303 3486071 := bstep (se 1 (by rfl) ⟨2614553, by rfl⟩ : syracuseStep 3486071 = 5229107) B5229107
theorem B2175389 : Blo 642303 2175389 := bstep (se 3 (by rfl) ⟨407885, by rfl⟩ : syracuseStep 2175389 = 815771) B815771
theorem B963527 : Blo 642303 963527 := bstep (se 1 (by rfl) ⟨722645, by rfl⟩ : syracuseStep 963527 = 1445291) B1445291
theorem B17643197 : Blo 642303 17643197 := bstep (se 3 (by rfl) ⟨3308099, by rfl⟩ : syracuseStep 17643197 = 6616199) B6616199
theorem B3487931 : Blo 642303 3487931 := bstep (se 1 (by rfl) ⟨2615948, by rfl⟩ : syracuseStep 3487931 = 5231897) B5231897
theorem B965231 : Blo 642303 965231 := bstep (se 1 (by rfl) ⟨723923, by rfl⟩ : syracuseStep 965231 = 1447847) B1447847
theorem B965327 : Blo 642303 965327 := bstep (se 1 (by rfl) ⟨723995, by rfl⟩ : syracuseStep 965327 = 1447991) B1447991
theorem B965375 : Blo 642303 965375 := bstep (se 1 (by rfl) ⟨724031, by rfl⟩ : syracuseStep 965375 = 1448063) B1448063
theorem B965513 : Blo 642303 965513 := bstep (se 2 (by rfl) ⟨362067, by rfl⟩ : syracuseStep 965513 = 724135) B724135
theorem B965609 : Blo 642303 965609 := bstep (se 2 (by rfl) ⟨362103, by rfl⟩ : syracuseStep 965609 = 724207) B724207
theorem B1031231 : Blo 642303 1031231 := bstep (se 1 (by rfl) ⟨773423, by rfl⟩ : syracuseStep 1031231 = 1546847) B1546847
theorem B965759 : Blo 642303 965759 := bstep (se 1 (by rfl) ⟨724319, by rfl⟩ : syracuseStep 965759 = 1448639) B1448639
theorem B966047 : Blo 642303 966047 := bstep (se 1 (by rfl) ⟨724535, by rfl⟩ : syracuseStep 966047 = 1449071) B1449071
theorem B1883903 : Blo 642303 1883903 := bstep (se 1 (by rfl) ⟨1412927, by rfl⟩ : syracuseStep 1883903 = 2825855) B2825855
theorem B966719 : Blo 642303 966719 := bstep (se 1 (by rfl) ⟨725039, by rfl⟩ : syracuseStep 966719 = 1450079) B1450079
theorem B2179385 : Blo 642303 2179385 := bstep (se 2 (by rfl) ⟨817269, by rfl⟩ : syracuseStep 2179385 = 1634539) B1634539
theorem B26427707 : Blo 642303 26427707 := bstep (se 1 (by rfl) ⟨19820780, by rfl⟩ : syracuseStep 26427707 = 39641561) B39641561
theorem B967463 : Blo 642303 967463 := bstep (se 1 (by rfl) ⟨725597, by rfl⟩ : syracuseStep 967463 = 1451195) B1451195
theorem B967487 : Blo 642303 967487 := bstep (se 1 (by rfl) ⟨725615, by rfl⟩ : syracuseStep 967487 = 1451231) B1451231
theorem B967835 : Blo 642303 967835 := bstep (se 1 (by rfl) ⟨725876, by rfl⟩ : syracuseStep 967835 = 1451753) B1451753
theorem B967931 : Blo 642303 967931 := bstep (se 1 (by rfl) ⟨725948, by rfl⟩ : syracuseStep 967931 = 1451897) B1451897
theorem B18629959 : Blo 642303 18629959 := bstep (se 1 (by rfl) ⟨13972469, by rfl⟩ : syracuseStep 18629959 = 27944939) B27944939
theorem B968639 : Blo 642303 968639 := bstep (se 1 (by rfl) ⟨726479, by rfl⟩ : syracuseStep 968639 = 1452959) B1452959
theorem B969371 : Blo 642303 969371 := bstep (se 1 (by rfl) ⟨727028, by rfl⟩ : syracuseStep 969371 = 1454057) B1454057
theorem B2444519 : Blo 642303 2444519 := bstep (se 1 (by rfl) ⟨1833389, by rfl⟩ : syracuseStep 2444519 = 3666779) B3666779
theorem B642719 : Blo 642303 642719 := bstep (se 1 (by rfl) ⟨482039, by rfl⟩ : syracuseStep 642719 = 964079) B964079
theorem B5492447 : Blo 642303 5492447 := bstep (se 1 (by rfl) ⟨4119335, by rfl⟩ : syracuseStep 5492447 = 8238671) B8238671
theorem B3265757 : Blo 642303 3265757 := bstep (se 3 (by rfl) ⟨612329, by rfl⟩ : syracuseStep 3265757 = 1224659) B1224659
theorem B7853287 : Blo 642303 7853287 := bstep (se 1 (by rfl) ⟨5889965, by rfl⟩ : syracuseStep 7853287 = 11779931) B11779931
theorem B645167 : Blo 642303 645167 := bstep (se 1 (by rfl) ⟨483875, by rfl⟩ : syracuseStep 645167 = 967751) B967751
theorem B1104041 : Blo 642303 1104041 := bstep (se 2 (by rfl) ⟨414015, by rfl⟩ : syracuseStep 1104041 = 828031) B828031
theorem B645599 : Blo 642303 645599 := bstep (se 1 (by rfl) ⟨484199, by rfl⟩ : syracuseStep 645599 = 968399) B968399
theorem B645615 : Blo 642303 645615 := bstep (se 1 (by rfl) ⟨484211, by rfl⟩ : syracuseStep 645615 = 968423) B968423
theorem B53533187 : Blo 642303 53533187 := bstep (se 1 (by rfl) ⟨40149890, by rfl⟩ : syracuseStep 53533187 = 80299781) B80299781
theorem B645735 : Blo 642303 645735 := bstep (se 1 (by rfl) ⟨484301, by rfl⟩ : syracuseStep 645735 = 968603) B968603
theorem B645887 : Blo 642303 645887 := bstep (se 1 (by rfl) ⟨484415, by rfl⟩ : syracuseStep 645887 = 968831) B968831
theorem B646271 : Blo 642303 646271 := bstep (se 1 (by rfl) ⟨484703, by rfl⟩ : syracuseStep 646271 = 969407) B969407
theorem B2448863 : Blo 642303 2448863 := bstep (se 1 (by rfl) ⟨1836647, by rfl⟩ : syracuseStep 2448863 = 3673295) B3673295
theorem B1466281 : Blo 642303 1466281 := bstep (se 2 (by rfl) ⟨549855, by rfl⟩ : syracuseStep 1466281 = 1099711) B1099711
theorem B16507475 : Blo 642303 16507475 := bstep (se 1 (by rfl) ⟨12380606, by rfl⟩ : syracuseStep 16507475 = 24761213) B24761213
theorem B4416443 : Blo 642303 4416443 := bstep (se 1 (by rfl) ⟨3312332, by rfl⟩ : syracuseStep 4416443 = 6624665) B6624665
theorem B1959041 : Blo 642303 1959041 := bstep (se 2 (by rfl) ⟨734640, by rfl⟩ : syracuseStep 1959041 = 1469281) B1469281
theorem B5563711 : Blo 642303 5563711 := bstep (se 1 (by rfl) ⟨4172783, by rfl⟩ : syracuseStep 5563711 = 8345567) B8345567
theorem B2747351 : Blo 642303 2747351 := bstep (se 1 (by rfl) ⟨2060513, by rfl⟩ : syracuseStep 2747351 = 4121027) B4121027
theorem B5237831 : Blo 642303 5237831 := bstep (se 1 (by rfl) ⟨3928373, by rfl⟩ : syracuseStep 5237831 = 7856747) B7856747
theorem B24800579 : Blo 642303 24800579 := bstep (se 1 (by rfl) ⟨18600434, by rfl⟩ : syracuseStep 24800579 = 37200869) B37200869
theorem B3665321 : Blo 642303 3665321 := bstep (se 2 (by rfl) ⟨1374495, by rfl⟩ : syracuseStep 3665321 = 2748991) B2748991
theorem B2946079 : Blo 642303 2946079 := bstep (se 1 (by rfl) ⟨2209559, by rfl⟩ : syracuseStep 2946079 = 4419119) B4419119
theorem B2061949 : Blo 642303 2061949 := bstep (se 3 (by rfl) ⟨386615, by rfl⟩ : syracuseStep 2061949 = 773231) B773231
theorem B12056201 : Blo 642303 12056201 := bstep (se 2 (by rfl) ⟨4521075, by rfl⟩ : syracuseStep 12056201 = 9042151) B9042151
theorem B2357117 : Blo 642303 2357117 := bstep (se 3 (by rfl) ⟨441959, by rfl⟩ : syracuseStep 2357117 = 883919) B883919
theorem B13957433 : Blo 642303 13957433 := bstep (se 2 (by rfl) ⟨5234037, by rfl⟩ : syracuseStep 13957433 = 10468075) B10468075
theorem B4422053 : Blo 642303 4422053 := bstep (se 4 (by rfl) ⟨414567, by rfl⟩ : syracuseStep 4422053 = 829135) B829135
theorem B1833641 : Blo 642303 1833641 := bstep (se 2 (by rfl) ⟨687615, by rfl⟩ : syracuseStep 1833641 = 1375231) B1375231
theorem B7339571 : Blo 642303 7339571 := bstep (se 1 (by rfl) ⟨5504678, by rfl⟩ : syracuseStep 7339571 = 11009357) B11009357
theorem B3670697 : Blo 642303 3670697 := bstep (se 2 (by rfl) ⟨1376511, by rfl⟩ : syracuseStep 3670697 = 2753023) B2753023
theorem B1836215 : Blo 642303 1836215 := bstep (se 1 (by rfl) ⟨1377161, by rfl⟩ : syracuseStep 1836215 = 2754323) B2754323
theorem B24839945 : Blo 642303 24839945 := bstep (se 2 (by rfl) ⟨9314979, by rfl⟩ : syracuseStep 24839945 = 18629959) B18629959
theorem B9275309 : Blo 642303 9275309 := bstep (se 3 (by rfl) ⟨1739120, by rfl⟩ : syracuseStep 9275309 = 3478241) B3478241
theorem B3672155 : Blo 642303 3672155 := bstep (se 1 (by rfl) ⟨2754116, by rfl⟩ : syracuseStep 3672155 = 5508233) B5508233
theorem B723055 : Blo 642303 723055 := bstep (se 1 (by rfl) ⟨542291, by rfl⟩ : syracuseStep 723055 = 1084583) B1084583
theorem B11733221 : Blo 642303 11733221 := bstep (se 4 (by rfl) ⟨1099989, by rfl⟩ : syracuseStep 11733221 = 2199979) B2199979
theorem B4655879 : Blo 642303 4655879 := bstep (se 1 (by rfl) ⟨3491909, by rfl⟩ : syracuseStep 4655879 = 6983819) B6983819
theorem B6949739 : Blo 642303 6949739 := bstep (se 1 (by rfl) ⟨5212304, by rfl⟩ : syracuseStep 6949739 = 10424609) B10424609
theorem B1445327 : Blo 642303 1445327 := bstep (se 1 (by rfl) ⟨1083995, by rfl⟩ : syracuseStep 1445327 = 2167991) B2167991
theorem B1445543 : Blo 642303 1445543 := bstep (se 1 (by rfl) ⟨1084157, by rfl⟩ : syracuseStep 1445543 = 2168315) B2168315
theorem B8360081 : Blo 642303 8360081 := bstep (se 2 (by rfl) ⟨3135030, by rfl⟩ : syracuseStep 8360081 = 6270061) B6270061
theorem B1446191 : Blo 642303 1446191 := bstep (se 1 (by rfl) ⟨1084643, by rfl⟩ : syracuseStep 1446191 = 2169287) B2169287
theorem B35688791 : Blo 642303 35688791 := bstep (se 1 (by rfl) ⟨26766593, by rfl⟩ : syracuseStep 35688791 = 53533187) B53533187
theorem B9310949 : Blo 642303 9310949 := bstep (se 4 (by rfl) ⟨872901, by rfl⟩ : syracuseStep 9310949 = 1745803) B1745803
theorem B2758697 : Blo 642303 2758697 := bstep (se 2 (by rfl) ⟨1034511, by rfl⟩ : syracuseStep 2758697 = 2069023) B2069023
theorem B23795963 : Blo 642303 23795963 := bstep (se 1 (by rfl) ⟨17846972, by rfl⟩ : syracuseStep 23795963 = 35693945) B35693945
theorem B1448927 : Blo 642303 1448927 := bstep (se 1 (by rfl) ⟨1086695, by rfl⟩ : syracuseStep 1448927 = 2173391) B2173391
theorem B11018105 : Blo 642303 11018105 := bstep (se 2 (by rfl) ⟨4131789, by rfl⟩ : syracuseStep 11018105 = 8263579) B8263579
theorem B13967549 : Blo 642303 13967549 := bstep (se 3 (by rfl) ⟨2618915, by rfl⟩ : syracuseStep 13967549 = 5237831) B5237831
theorem B2171123 : Blo 642303 2171123 := bstep (se 1 (by rfl) ⟨1628342, by rfl⟩ : syracuseStep 2171123 = 3256685) B3256685
theorem B1450259 : Blo 642303 1450259 := bstep (se 1 (by rfl) ⟨1087694, by rfl⟩ : syracuseStep 1450259 = 2175389) B2175389
theorem B8037467 : Blo 642303 8037467 := bstep (se 1 (by rfl) ⟨6028100, by rfl⟩ : syracuseStep 8037467 = 12056201) B12056201
theorem B1222427 : Blo 642303 1222427 := bstep (se 1 (by rfl) ⟨916820, by rfl⟩ : syracuseStep 1222427 = 1833641) B1833641
theorem B5023741 : Blo 642303 5023741 := bstep (se 3 (by rfl) ⟨941951, by rfl⟩ : syracuseStep 5023741 = 1883903) B1883903
theorem B4893047 : Blo 642303 4893047 := bstep (se 1 (by rfl) ⟨3669785, by rfl⟩ : syracuseStep 4893047 = 7339571) B7339571
theorem B1452923 : Blo 642303 1452923 := bstep (se 1 (by rfl) ⟨1089692, by rfl⟩ : syracuseStep 1452923 = 2179385) B2179385
theorem B1552343 : Blo 642303 1552343 := bstep (se 1 (by rfl) ⟨1164257, by rfl⟩ : syracuseStep 1552343 = 2328515) B2328515
theorem B4960367 : Blo 642303 4960367 := bstep (se 1 (by rfl) ⟨3720275, by rfl⟩ : syracuseStep 4960367 = 7440551) B7440551
theorem B8237335 : Blo 642303 8237335 := bstep (se 1 (by rfl) ⟨6178001, by rfl⟩ : syracuseStep 8237335 = 12356003) B12356003
theorem B963455 : Blo 642303 963455 := bstep (se 1 (by rfl) ⟨722591, by rfl⟩ : syracuseStep 963455 = 1445183) B1445183
theorem B964031 : Blo 642303 964031 := bstep (se 1 (by rfl) ⟨723023, by rfl⟩ : syracuseStep 964031 = 1446047) B1446047
theorem B964463 : Blo 642303 964463 := bstep (se 1 (by rfl) ⟨723347, by rfl⟩ : syracuseStep 964463 = 1446695) B1446695
theorem B2177171 : Blo 642303 2177171 := bstep (se 1 (by rfl) ⟨1632878, by rfl⟩ : syracuseStep 2177171 = 3265757) B3265757
theorem B965033 : Blo 642303 965033 := bstep (se 2 (by rfl) ⟨361887, by rfl⟩ : syracuseStep 965033 = 723775) B723775
theorem B3259115 : Blo 642303 3259115 := bstep (se 1 (by rfl) ⟨2444336, by rfl⟩ : syracuseStep 3259115 = 4888673) B4888673
theorem B68795191 : Blo 642303 68795191 := bstep (se 1 (by rfl) ⟨51596393, by rfl⟩ : syracuseStep 68795191 = 103192787) B103192787
theorem B1162579 : Blo 642303 1162579 := bstep (se 1 (by rfl) ⟨871934, by rfl⟩ : syracuseStep 1162579 = 1743869) B1743869
theorem B4636561 : Blo 642303 4636561 := bstep (se 2 (by rfl) ⟨1738710, by rfl⟩ : syracuseStep 4636561 = 3477421) B3477421
theorem B967103 : Blo 642303 967103 := bstep (se 1 (by rfl) ⟨725327, by rfl⟩ : syracuseStep 967103 = 1450655) B1450655
theorem B968057 : Blo 642303 968057 := bstep (se 2 (by rfl) ⟨363021, by rfl⟩ : syracuseStep 968057 = 726043) B726043
theorem B10471049 : Blo 642303 10471049 := bstep (se 2 (by rfl) ⟨3926643, by rfl⟩ : syracuseStep 10471049 = 7853287) B7853287
theorem B29673125 : Blo 642303 29673125 := bstep (se 4 (by rfl) ⟨2781855, by rfl⟩ : syracuseStep 29673125 = 5563711) B5563711
theorem B16533719 : Blo 642303 16533719 := bstep (se 1 (by rfl) ⟨12400289, by rfl⟩ : syracuseStep 16533719 = 24800579) B24800579
theorem B2443547 : Blo 642303 2443547 := bstep (se 1 (by rfl) ⟨1832660, by rfl⟩ : syracuseStep 2443547 = 3665321) B3665321
theorem B969263 : Blo 642303 969263 := bstep (se 1 (by rfl) ⟨726947, by rfl⟩ : syracuseStep 969263 = 1453895) B1453895
theorem B969383 : Blo 642303 969383 := bstep (se 1 (by rfl) ⟨727037, by rfl⟩ : syracuseStep 969383 = 1454075) B1454075
theorem B642351 : Blo 642303 642351 := bstep (se 1 (by rfl) ⟨481763, by rfl⟩ : syracuseStep 642351 = 963527) B963527
theorem B643487 : Blo 642303 643487 := bstep (se 1 (by rfl) ⟨482615, by rfl⟩ : syracuseStep 643487 = 965231) B965231
theorem B643551 : Blo 642303 643551 := bstep (se 1 (by rfl) ⟨482663, by rfl⟩ : syracuseStep 643551 = 965327) B965327
theorem B643583 : Blo 642303 643583 := bstep (se 1 (by rfl) ⟨482687, by rfl⟩ : syracuseStep 643583 = 965375) B965375
theorem B643675 : Blo 642303 643675 := bstep (se 1 (by rfl) ⟨482756, by rfl⟩ : syracuseStep 643675 = 965513) B965513
theorem B643739 : Blo 642303 643739 := bstep (se 1 (by rfl) ⟨482804, by rfl⟩ : syracuseStep 643739 = 965609) B965609
theorem B643839 : Blo 642303 643839 := bstep (se 1 (by rfl) ⟨482879, by rfl⟩ : syracuseStep 643839 = 965759) B965759
theorem B7820165 : Blo 642303 7820165 := bstep (se 4 (by rfl) ⟨733140, by rfl⟩ : syracuseStep 7820165 = 1466281) B1466281
theorem B644031 : Blo 642303 644031 := bstep (se 1 (by rfl) ⟨483023, by rfl⟩ : syracuseStep 644031 = 966047) B966047
theorem B644479 : Blo 642303 644479 := bstep (se 1 (by rfl) ⟨483359, by rfl⟩ : syracuseStep 644479 = 966719) B966719
theorem B17618471 : Blo 642303 17618471 := bstep (se 1 (by rfl) ⟨13213853, by rfl⟩ : syracuseStep 17618471 = 26427707) B26427707
theorem B644975 : Blo 642303 644975 := bstep (se 1 (by rfl) ⟨483731, by rfl⟩ : syracuseStep 644975 = 967463) B967463
theorem B644991 : Blo 642303 644991 := bstep (se 1 (by rfl) ⟨483743, by rfl⟩ : syracuseStep 644991 = 967487) B967487
theorem B645223 : Blo 642303 645223 := bstep (se 1 (by rfl) ⟨483917, by rfl⟩ : syracuseStep 645223 = 967835) B967835
theorem B645287 : Blo 642303 645287 := bstep (se 1 (by rfl) ⟨483965, by rfl⟩ : syracuseStep 645287 = 967931) B967931
theorem B645759 : Blo 642303 645759 := bstep (se 1 (by rfl) ⟨484319, by rfl⟩ : syracuseStep 645759 = 968639) B968639
theorem B646247 : Blo 642303 646247 := bstep (se 1 (by rfl) ⟨484685, by rfl⟩ : syracuseStep 646247 = 969371) B969371
theorem B1629679 : Blo 642303 1629679 := bstep (se 1 (by rfl) ⟨1222259, by rfl⟩ : syracuseStep 1629679 = 2444519) B2444519
theorem B3661631 : Blo 642303 3661631 := bstep (se 1 (by rfl) ⟨2746223, by rfl⟩ : syracuseStep 3661631 = 5492447) B5492447
theorem B2450047 : Blo 642303 2450047 := bstep (se 1 (by rfl) ⟨1837535, by rfl⟩ : syracuseStep 2450047 = 3675071) B3675071
theorem B2058463 : Blo 642303 2058463 := bstep (se 1 (by rfl) ⟨1543847, by rfl⟩ : syracuseStep 2058463 = 3087695) B3087695
theorem B1632575 : Blo 642303 1632575 := bstep (se 1 (by rfl) ⟨1224431, by rfl⟩ : syracuseStep 1632575 = 2448863) B2448863
theorem B2058617 : Blo 642303 2058617 := bstep (se 2 (by rfl) ⟨771981, by rfl⟩ : syracuseStep 2058617 = 1543963) B1543963
theorem B11004983 : Blo 642303 11004983 := bstep (se 1 (by rfl) ⟨8253737, by rfl⟩ : syracuseStep 11004983 = 16507475) B16507475
theorem B2944109 : Blo 642303 2944109 := bstep (se 3 (by rfl) ⟨552020, by rfl⟩ : syracuseStep 2944109 = 1104041) B1104041
theorem B2944295 : Blo 642303 2944295 := bstep (se 1 (by rfl) ⟨2208221, by rfl⟩ : syracuseStep 2944295 = 4416443) B4416443
theorem B1306027 : Blo 642303 1306027 := bstep (se 1 (by rfl) ⟨979520, by rfl⟩ : syracuseStep 1306027 = 1959041) B1959041
theorem B3928105 : Blo 642303 3928105 := bstep (se 2 (by rfl) ⟨1473039, by rfl⟩ : syracuseStep 3928105 = 2946079) B2946079
theorem B1831567 : Blo 642303 1831567 := bstep (se 1 (by rfl) ⟨1373675, by rfl⟩ : syracuseStep 1831567 = 2747351) B2747351
theorem B2749265 : Blo 642303 2749265 := bstep (se 2 (by rfl) ⟨1030974, by rfl⟩ : syracuseStep 2749265 = 2061949) B2061949
theorem B25130087 : Blo 642303 25130087 := bstep (se 1 (by rfl) ⟨18847565, by rfl⟩ : syracuseStep 25130087 = 37695131) B37695131
theorem B2749949 : Blo 642303 2749949 := bstep (se 3 (by rfl) ⟨515615, by rfl⟩ : syracuseStep 2749949 = 1031231) B1031231
theorem B2324047 : Blo 642303 2324047 := bstep (se 1 (by rfl) ⟨1743035, by rfl⟩ : syracuseStep 2324047 = 3486071) B3486071
theorem B11762131 : Blo 642303 11762131 := bstep (se 1 (by rfl) ⟨8821598, by rfl⟩ : syracuseStep 11762131 = 17643197) B17643197
theorem B1571411 : Blo 642303 1571411 := bstep (se 1 (by rfl) ⟨1178558, by rfl⟩ : syracuseStep 1571411 = 2357117) B2357117
theorem B2325287 : Blo 642303 2325287 := bstep (se 1 (by rfl) ⟨1743965, by rfl⟩ : syracuseStep 2325287 = 3487931) B3487931
theorem B9304955 : Blo 642303 9304955 := bstep (se 1 (by rfl) ⟨6978716, by rfl⟩ : syracuseStep 9304955 = 13957433) B13957433
theorem B2948035 : Blo 642303 2948035 := bstep (se 1 (by rfl) ⟨2211026, by rfl⟩ : syracuseStep 2948035 = 4422053) B4422053
theorem B2457161 : Blo 642303 2457161 := bstep (se 2 (by rfl) ⟨921435, by rfl⟩ : syracuseStep 2457161 = 1842871) B1842871
theorem B6980699 : Blo 642303 6980699 := bstep (se 1 (by rfl) ⟨5235524, by rfl⟩ : syracuseStep 6980699 = 10471049) B10471049
theorem B5573387 : Blo 642303 5573387 := bstep (se 1 (by rfl) ⟨4180040, by rfl⟩ : syracuseStep 5573387 = 8360081) B8360081
theorem B23792527 : Blo 642303 23792527 := bstep (se 1 (by rfl) ⟨17844395, by rfl⟩ : syracuseStep 23792527 = 35688791) B35688791
theorem B5213443 : Blo 642303 5213443 := bstep (se 1 (by rfl) ⟨3910082, by rfl⟩ : syracuseStep 5213443 = 7820165) B7820165
theorem B1839131 : Blo 642303 1839131 := bstep (se 1 (by rfl) ⟨1379348, by rfl⟩ : syracuseStep 1839131 = 2758697) B2758697
theorem B15863975 : Blo 642303 15863975 := bstep (se 1 (by rfl) ⟨11897981, by rfl⟩ : syracuseStep 15863975 = 23795963) B23795963
theorem B7345403 : Blo 642303 7345403 := bstep (se 1 (by rfl) ⟨5509052, by rfl⟩ : syracuseStep 7345403 = 11018105) B11018105
theorem B9311699 : Blo 642303 9311699 := bstep (se 1 (by rfl) ⟨6983774, by rfl⟩ : syracuseStep 9311699 = 13967549) B13967549
theorem B1447415 : Blo 642303 1447415 := bstep (se 1 (by rfl) ⟨1085561, by rfl⟩ : syracuseStep 1447415 = 2171123) B2171123
theorem B10983113 : Blo 642303 10983113 := bstep (se 2 (by rfl) ⟨4118667, by rfl⟩ : syracuseStep 10983113 = 8237335) B8237335
theorem B1088383 : Blo 642303 1088383 := bstep (se 1 (by rfl) ⟨816287, by rfl⟩ : syracuseStep 1088383 = 1632575) B1632575
theorem B16753391 : Blo 642303 16753391 := bstep (se 1 (by rfl) ⟨12565043, by rfl⟩ : syracuseStep 16753391 = 25130087) B25130087
theorem B91726921 : Blo 642303 91726921 := bstep (se 2 (by rfl) ⟨34397595, by rfl⟩ : syracuseStep 91726921 = 68795191) B68795191
theorem B1451447 : Blo 642303 1451447 := bstep (se 1 (by rfl) ⟨1088585, by rfl⟩ : syracuseStep 1451447 = 2177171) B2177171
theorem B1550105 : Blo 642303 1550105 := bstep (se 2 (by rfl) ⟨581289, by rfl⟩ : syracuseStep 1550105 = 1162579) B1162579
theorem B2172743 : Blo 642303 2172743 := bstep (se 1 (by rfl) ⟨1629557, by rfl⟩ : syracuseStep 2172743 = 3259115) B3259115
theorem B1550191 : Blo 642303 1550191 := bstep (se 1 (by rfl) ⟨1162643, by rfl⟩ : syracuseStep 1550191 = 2325287) B2325287
theorem B6203303 : Blo 642303 6203303 := bstep (se 1 (by rfl) ⟨4652477, by rfl⟩ : syracuseStep 6203303 = 9304955) B9304955
theorem B2172905 : Blo 642303 2172905 := bstep (se 2 (by rfl) ⟨814839, by rfl⟩ : syracuseStep 2172905 = 1629679) B1629679
theorem B4139581 : Blo 642303 4139581 := bstep (se 3 (by rfl) ⟨776171, by rfl⟩ : syracuseStep 4139581 = 1552343) B1552343
theorem B1224143 : Blo 642303 1224143 := bstep (se 1 (by rfl) ⟨918107, by rfl⟩ : syracuseStep 1224143 = 1836215) B1836215
theorem B16559963 : Blo 642303 16559963 := bstep (se 1 (by rfl) ⟨12419972, by rfl⟩ : syracuseStep 16559963 = 24839945) B24839945
theorem B11022479 : Blo 642303 11022479 := bstep (se 1 (by rfl) ⟨8266859, by rfl⟩ : syracuseStep 11022479 = 16533719) B16533719
theorem B4633159 : Blo 642303 4633159 := bstep (se 1 (by rfl) ⟨3474869, by rfl⟩ : syracuseStep 4633159 = 6949739) B6949739
theorem B963551 : Blo 642303 963551 := bstep (se 1 (by rfl) ⟨722663, by rfl⟩ : syracuseStep 963551 = 1445327) B1445327
theorem B963695 : Blo 642303 963695 := bstep (se 1 (by rfl) ⟨722771, by rfl⟩ : syracuseStep 963695 = 1445543) B1445543
theorem B6698321 : Blo 642303 6698321 := bstep (se 2 (by rfl) ⟨2511870, by rfl⟩ : syracuseStep 6698321 = 5023741) B5023741
theorem B964073 : Blo 642303 964073 := bstep (se 2 (by rfl) ⟨361527, by rfl⟩ : syracuseStep 964073 = 723055) B723055
theorem B964127 : Blo 642303 964127 := bstep (se 1 (by rfl) ⟨723095, by rfl⟩ : syracuseStep 964127 = 1446191) B1446191
theorem B6207299 : Blo 642303 6207299 := bstep (se 1 (by rfl) ⟨4655474, by rfl⟩ : syracuseStep 6207299 = 9310949) B9310949
theorem B11745647 : Blo 642303 11745647 := bstep (se 1 (by rfl) ⟨8809235, by rfl⟩ : syracuseStep 11745647 = 17618471) B17618471
theorem B965951 : Blo 642303 965951 := bstep (se 1 (by rfl) ⟨724463, by rfl⟩ : syracuseStep 965951 = 1448927) B1448927
theorem B2441087 : Blo 642303 2441087 := bstep (se 1 (by rfl) ⟨1830815, by rfl⟩ : syracuseStep 2441087 = 3661631) B3661631
theorem B966839 : Blo 642303 966839 := bstep (se 1 (by rfl) ⟨725129, by rfl⟩ : syracuseStep 966839 = 1450259) B1450259
theorem B5358311 : Blo 642303 5358311 := bstep (se 1 (by rfl) ⟨4018733, by rfl⟩ : syracuseStep 5358311 = 8037467) B8037467
theorem B2442089 : Blo 642303 2442089 := bstep (se 2 (by rfl) ⟨915783, by rfl⟩ : syracuseStep 2442089 = 1831567) B1831567
theorem B3262031 : Blo 642303 3262031 := bstep (se 1 (by rfl) ⟨2446523, by rfl⟩ : syracuseStep 3262031 = 4893047) B4893047
theorem B968615 : Blo 642303 968615 := bstep (se 1 (by rfl) ⟨726461, by rfl⟩ : syracuseStep 968615 = 1452923) B1452923
theorem B3098729 : Blo 642303 3098729 := bstep (se 2 (by rfl) ⟨1162023, by rfl⟩ : syracuseStep 3098729 = 2324047) B2324047
theorem B6965477 : Blo 642303 6965477 := bstep (se 4 (by rfl) ⟨653013, by rfl⟩ : syracuseStep 6965477 = 1306027) B1306027
theorem B642303 : Blo 642303 642303 := bstep (se 1 (by rfl) ⟨481727, by rfl⟩ : syracuseStep 642303 = 963455) B963455
theorem B15682841 : Blo 642303 15682841 := bstep (se 2 (by rfl) ⟨5881065, by rfl⟩ : syracuseStep 15682841 = 11762131) B11762131
theorem B642687 : Blo 642303 642687 := bstep (se 1 (by rfl) ⟨482015, by rfl⟩ : syracuseStep 642687 = 964031) B964031
theorem B642975 : Blo 642303 642975 := bstep (se 1 (by rfl) ⟨482231, by rfl⟩ : syracuseStep 642975 = 964463) B964463
theorem B643355 : Blo 642303 643355 := bstep (se 1 (by rfl) ⟨482516, by rfl⟩ : syracuseStep 643355 = 965033) B965033
theorem B6182081 : Blo 642303 6182081 := bstep (se 2 (by rfl) ⟨2318280, by rfl⟩ : syracuseStep 6182081 = 4636561) B4636561
theorem B644735 : Blo 642303 644735 := bstep (se 1 (by rfl) ⟨483551, by rfl⟩ : syracuseStep 644735 = 967103) B967103
theorem B2447131 : Blo 642303 2447131 := bstep (se 1 (by rfl) ⟨1835348, by rfl⟩ : syracuseStep 2447131 = 3670697) B3670697
theorem B3266729 : Blo 642303 3266729 := bstep (se 2 (by rfl) ⟨1225023, by rfl⟩ : syracuseStep 3266729 = 2450047) B2450047
theorem B645371 : Blo 642303 645371 := bstep (se 1 (by rfl) ⟨484028, by rfl⟩ : syracuseStep 645371 = 968057) B968057
theorem B19782083 : Blo 642303 19782083 := bstep (se 1 (by rfl) ⟨14836562, by rfl⟩ : syracuseStep 19782083 = 29673125) B29673125
theorem B6183539 : Blo 642303 6183539 := bstep (se 1 (by rfl) ⟨4637654, by rfl⟩ : syracuseStep 6183539 = 9275309) B9275309
theorem B2448103 : Blo 642303 2448103 := bstep (se 1 (by rfl) ⟨1836077, by rfl⟩ : syracuseStep 2448103 = 3672155) B3672155
theorem B1629031 : Blo 642303 1629031 := bstep (se 1 (by rfl) ⟨1221773, by rfl⟩ : syracuseStep 1629031 = 2443547) B2443547
theorem B646175 : Blo 642303 646175 := bstep (se 1 (by rfl) ⟨484631, by rfl⟩ : syracuseStep 646175 = 969263) B969263
theorem B646255 : Blo 642303 646255 := bstep (se 1 (by rfl) ⟨484691, by rfl⟩ : syracuseStep 646255 = 969383) B969383
theorem B3103919 : Blo 642303 3103919 := bstep (se 1 (by rfl) ⟨2327939, by rfl⟩ : syracuseStep 3103919 = 4655879) B4655879
theorem B2744617 : Blo 642303 2744617 := bstep (se 2 (by rfl) ⟨1029231, by rfl⟩ : syracuseStep 2744617 = 2058463) B2058463
theorem B5237473 : Blo 642303 5237473 := bstep (se 2 (by rfl) ⟨1964052, by rfl⟩ : syracuseStep 5237473 = 3928105) B3928105
theorem B31288589 : Blo 642303 31288589 := bstep (se 3 (by rfl) ⟨5866610, by rfl⟩ : syracuseStep 31288589 = 11733221) B11733221
theorem B814951 : Blo 642303 814951 := bstep (se 1 (by rfl) ⟨611213, by rfl⟩ : syracuseStep 814951 = 1222427) B1222427
theorem B4190429 : Blo 642303 4190429 := bstep (se 3 (by rfl) ⟨785705, by rfl⟩ : syracuseStep 4190429 = 1571411) B1571411
theorem B1372411 : Blo 642303 1372411 := bstep (se 1 (by rfl) ⟨1029308, by rfl⟩ : syracuseStep 1372411 = 2058617) B2058617
theorem B7336655 : Blo 642303 7336655 := bstep (se 1 (by rfl) ⟨5502491, by rfl⟩ : syracuseStep 7336655 = 11004983) B11004983
theorem B1962739 : Blo 642303 1962739 := bstep (se 1 (by rfl) ⟨1472054, by rfl⟩ : syracuseStep 1962739 = 2944109) B2944109
theorem B1962863 : Blo 642303 1962863 := bstep (se 1 (by rfl) ⟨1472147, by rfl⟩ : syracuseStep 1962863 = 2944295) B2944295
theorem B3306911 : Blo 642303 3306911 := bstep (se 1 (by rfl) ⟨2480183, by rfl⟩ : syracuseStep 3306911 = 4960367) B4960367
theorem B1832843 : Blo 642303 1832843 := bstep (se 1 (by rfl) ⟨1374632, by rfl⟩ : syracuseStep 1832843 = 2749265) B2749265
theorem B1833299 : Blo 642303 1833299 := bstep (se 1 (by rfl) ⟨1374974, by rfl⟩ : syracuseStep 1833299 = 2749949) B2749949
theorem B3930713 : Blo 642303 3930713 := bstep (se 2 (by rfl) ⟨1474017, by rfl⟩ : syracuseStep 3930713 = 2948035) B2948035
theorem B1638107 : Blo 642303 1638107 := bstep (se 1 (by rfl) ⟨1228580, by rfl⟩ : syracuseStep 1638107 = 2457161) B2457161
theorem B3572207 : Blo 642303 3572207 := bstep (se 1 (by rfl) ⟨2679155, by rfl⟩ : syracuseStep 3572207 = 5358311) B5358311
theorem B2065819 : Blo 642303 2065819 := bstep (se 1 (by rfl) ⟨1549364, by rfl⟩ : syracuseStep 2065819 = 3098729) B3098729
theorem B10455227 : Blo 642303 10455227 := bstep (se 1 (by rfl) ⟨7841420, by rfl⟩ : syracuseStep 10455227 = 15682841) B15682841
theorem B2066921 : Blo 642303 2066921 := bstep (se 2 (by rfl) ⟨775095, by rfl⟩ : syracuseStep 2066921 = 1550191) B1550191
theorem B18615197 : Blo 642303 18615197 := bstep (se 3 (by rfl) ⟨3490349, by rfl⟩ : syracuseStep 18615197 = 6980699) B6980699
theorem B6983297 : Blo 642303 6983297 := bstep (se 2 (by rfl) ⟨2618736, by rfl⟩ : syracuseStep 6983297 = 5237473) B5237473
theorem B8818429 : Blo 642303 8818429 := bstep (se 3 (by rfl) ⟨1653455, by rfl⟩ : syracuseStep 8818429 = 3306911) B3306911
theorem B31723369 : Blo 642303 31723369 := bstep (se 2 (by rfl) ⟨11896263, by rfl⟩ : syracuseStep 31723369 = 23792527) B23792527
theorem B6951257 : Blo 642303 6951257 := bstep (se 2 (by rfl) ⟨2606721, by rfl⟩ : syracuseStep 6951257 = 5213443) B5213443
theorem B2069279 : Blo 642303 2069279 := bstep (se 1 (by rfl) ⟨1551959, by rfl⟩ : syracuseStep 2069279 = 3103919) B3103919
theorem B1086601 : Blo 642303 1086601 := bstep (se 2 (by rfl) ⟨407475, by rfl⟩ : syracuseStep 1086601 = 814951) B814951
theorem B1448495 : Blo 642303 1448495 := bstep (se 1 (by rfl) ⟨1086371, by rfl⟩ : syracuseStep 1448495 = 2172743) B2172743
theorem B4135535 : Blo 642303 4135535 := bstep (se 1 (by rfl) ⟨3101651, by rfl⟩ : syracuseStep 4135535 = 6203303) B6203303
theorem B1448603 : Blo 642303 1448603 := bstep (se 1 (by rfl) ⟨1086452, by rfl⟩ : syracuseStep 1448603 = 2172905) B2172905
theorem B7348319 : Blo 642303 7348319 := bstep (se 1 (by rfl) ⟨5511239, by rfl⟩ : syracuseStep 7348319 = 11022479) B11022479
theorem B2793619 : Blo 642303 2793619 := bstep (se 1 (by rfl) ⟨2095214, by rfl⟩ : syracuseStep 2793619 = 4190429) B4190429
theorem B4891103 : Blo 642303 4891103 := bstep (se 1 (by rfl) ⟨3668327, by rfl⟩ : syracuseStep 4891103 = 7336655) B7336655
theorem B4465547 : Blo 642303 4465547 := bstep (se 1 (by rfl) ⟨3349160, by rfl⟩ : syracuseStep 4465547 = 6698321) B6698321
theorem B2172041 : Blo 642303 2172041 := bstep (se 2 (by rfl) ⟨814515, by rfl⟩ : syracuseStep 2172041 = 1629031) B1629031
theorem B1451177 : Blo 642303 1451177 := bstep (se 2 (by rfl) ⟨544191, by rfl⟩ : syracuseStep 1451177 = 1088383) B1088383
theorem B4138199 : Blo 642303 4138199 := bstep (se 1 (by rfl) ⟨3103649, by rfl⟩ : syracuseStep 4138199 = 6207299) B6207299
theorem B1221895 : Blo 642303 1221895 := bstep (se 1 (by rfl) ⟨916421, by rfl⟩ : syracuseStep 1221895 = 1832843) B1832843
theorem B1222199 : Blo 642303 1222199 := bstep (se 1 (by rfl) ⟨916649, by rfl⟩ : syracuseStep 1222199 = 1833299) B1833299
theorem B1092071 : Blo 642303 1092071 := bstep (se 1 (by rfl) ⟨819053, by rfl⟩ : syracuseStep 1092071 = 1638107) B1638107
theorem B2174687 : Blo 642303 2174687 := bstep (se 1 (by rfl) ⟨1631015, by rfl⟩ : syracuseStep 2174687 = 3262031) B3262031
theorem B122302561 : Blo 642303 122302561 := bstep (se 2 (by rfl) ⟨45863460, by rfl⟩ : syracuseStep 122302561 = 91726921) B91726921
theorem B3715591 : Blo 642303 3715591 := bstep (se 1 (by rfl) ⟨2786693, by rfl⟩ : syracuseStep 3715591 = 5573387) B5573387
theorem B1226087 : Blo 642303 1226087 := bstep (se 1 (by rfl) ⟨919565, by rfl⟩ : syracuseStep 1226087 = 1839131) B1839131
theorem B5519441 : Blo 642303 5519441 := bstep (se 2 (by rfl) ⟨2069790, by rfl⟩ : syracuseStep 5519441 = 4139581) B4139581
theorem B4896935 : Blo 642303 4896935 := bstep (se 1 (by rfl) ⟨3672701, by rfl⟩ : syracuseStep 4896935 = 7345403) B7345403
theorem B6207799 : Blo 642303 6207799 := bstep (se 1 (by rfl) ⟨4655849, by rfl⟩ : syracuseStep 6207799 = 9311699) B9311699
theorem B964943 : Blo 642303 964943 := bstep (se 1 (by rfl) ⟨723707, by rfl⟩ : syracuseStep 964943 = 1447415) B1447415
theorem B7322075 : Blo 642303 7322075 := bstep (se 1 (by rfl) ⟨5491556, by rfl⟩ : syracuseStep 7322075 = 10983113) B10983113
theorem B2177819 : Blo 642303 2177819 := bstep (se 1 (by rfl) ⟨1633364, by rfl⟩ : syracuseStep 2177819 = 3266729) B3266729
theorem B13188055 : Blo 642303 13188055 := bstep (se 1 (by rfl) ⟨9891041, by rfl⟩ : syracuseStep 13188055 = 19782083) B19782083
theorem B6177545 : Blo 642303 6177545 := bstep (se 2 (by rfl) ⟨2316579, by rfl⟩ : syracuseStep 6177545 = 4633159) B4633159
theorem B967631 : Blo 642303 967631 := bstep (se 1 (by rfl) ⟨725723, by rfl⟩ : syracuseStep 967631 = 1451447) B1451447
theorem B1033403 : Blo 642303 1033403 := bstep (se 1 (by rfl) ⟨775052, by rfl⟩ : syracuseStep 1033403 = 1550105) B1550105
theorem B20859059 : Blo 642303 20859059 := bstep (se 1 (by rfl) ⟨15644294, by rfl⟩ : syracuseStep 20859059 = 31288589) B31288589
theorem B3262841 : Blo 642303 3262841 := bstep (se 2 (by rfl) ⟨1223565, by rfl⟩ : syracuseStep 3262841 = 2447131) B2447131
theorem B642367 : Blo 642303 642367 := bstep (se 1 (by rfl) ⟨481775, by rfl⟩ : syracuseStep 642367 = 963551) B963551
theorem B642463 : Blo 642303 642463 := bstep (se 1 (by rfl) ⟨481847, by rfl⟩ : syracuseStep 642463 = 963695) B963695
theorem B3264137 : Blo 642303 3264137 := bstep (se 2 (by rfl) ⟨1224051, by rfl⟩ : syracuseStep 3264137 = 2448103) B2448103
theorem B642715 : Blo 642303 642715 := bstep (se 1 (by rfl) ⟨482036, by rfl⟩ : syracuseStep 642715 = 964073) B964073
theorem B642751 : Blo 642303 642751 := bstep (se 1 (by rfl) ⟨482063, by rfl⟩ : syracuseStep 642751 = 964127) B964127
theorem B643967 : Blo 642303 643967 := bstep (se 1 (by rfl) ⟨482975, by rfl⟩ : syracuseStep 643967 = 965951) B965951
theorem B1627391 : Blo 642303 1627391 := bstep (se 1 (by rfl) ⟨1220543, by rfl⟩ : syracuseStep 1627391 = 2441087) B2441087
theorem B644559 : Blo 642303 644559 := bstep (se 1 (by rfl) ⟨483419, by rfl⟩ : syracuseStep 644559 = 966839) B966839
theorem B3659489 : Blo 642303 3659489 := bstep (se 2 (by rfl) ⟨1372308, by rfl⟩ : syracuseStep 3659489 = 2744617) B2744617
theorem B1628059 : Blo 642303 1628059 := bstep (se 1 (by rfl) ⟨1221044, by rfl⟩ : syracuseStep 1628059 = 2442089) B2442089
theorem B645743 : Blo 642303 645743 := bstep (se 1 (by rfl) ⟨484307, by rfl⟩ : syracuseStep 645743 = 968615) B968615
theorem B4643651 : Blo 642303 4643651 := bstep (se 1 (by rfl) ⟨3482738, by rfl⟩ : syracuseStep 4643651 = 6965477) B6965477
theorem B10575983 : Blo 642303 10575983 := bstep (se 1 (by rfl) ⟨7931987, by rfl⟩ : syracuseStep 10575983 = 15863975) B15863975
theorem B4121387 : Blo 642303 4121387 := bstep (se 1 (by rfl) ⟨3091040, by rfl⟩ : syracuseStep 4121387 = 6182081) B6182081
theorem B4122359 : Blo 642303 4122359 := bstep (se 1 (by rfl) ⟨3091769, by rfl⟩ : syracuseStep 4122359 = 6183539) B6183539
theorem B1829881 : Blo 642303 1829881 := bstep (se 2 (by rfl) ⟨686205, by rfl⟩ : syracuseStep 1829881 = 1372411) B1372411
theorem B11168927 : Blo 642303 11168927 := bstep (se 1 (by rfl) ⟨8376695, by rfl⟩ : syracuseStep 11168927 = 16753391) B16753391
theorem B2616985 : Blo 642303 2616985 := bstep (se 2 (by rfl) ⟨981369, by rfl⟩ : syracuseStep 2616985 = 1962739) B1962739
theorem B816095 : Blo 642303 816095 := bstep (se 1 (by rfl) ⟨612071, by rfl⟩ : syracuseStep 816095 = 1224143) B1224143
theorem B11039975 : Blo 642303 11039975 := bstep (se 1 (by rfl) ⟨8279981, by rfl⟩ : syracuseStep 11039975 = 16559963) B16559963
theorem B1308575 : Blo 642303 1308575 := bstep (se 1 (by rfl) ⟨981431, by rfl⟩ : syracuseStep 1308575 = 1962863) B1962863
theorem B7830431 : Blo 642303 7830431 := bstep (se 1 (by rfl) ⟨5872823, by rfl⟩ : syracuseStep 7830431 = 11745647) B11745647
theorem B2620475 : Blo 642303 2620475 := bstep (se 1 (by rfl) ⟨1965356, by rfl⟩ : syracuseStep 2620475 = 3930713) B3930713
theorem B1377947 : Blo 642303 1377947 := bstep (se 1 (by rfl) ⟨1033460, by rfl⟩ : syracuseStep 1377947 = 2066921) B2066921
theorem B2754425 : Blo 642303 2754425 := bstep (se 2 (by rfl) ⟨1032909, by rfl⟩ : syracuseStep 2754425 = 2065819) B2065819
theorem B4655531 : Blo 642303 4655531 := bstep (se 1 (by rfl) ⟨3491648, by rfl⟩ : syracuseStep 4655531 = 6983297) B6983297
theorem B2755741 : Blo 642303 2755741 := bstep (se 3 (by rfl) ⟨516701, by rfl⟩ : syracuseStep 2755741 = 1033403) B1033403
theorem B1379519 : Blo 642303 1379519 := bstep (se 1 (by rfl) ⟨1034639, by rfl⟩ : syracuseStep 1379519 = 2069279) B2069279
theorem B1084927 : Blo 642303 1084927 := bstep (se 1 (by rfl) ⟨813695, by rfl⟩ : syracuseStep 1084927 = 1627391) B1627391
theorem B2757023 : Blo 642303 2757023 := bstep (se 1 (by rfl) ⟨2067767, by rfl⟩ : syracuseStep 2757023 = 4135535) B4135535
theorem B7050655 : Blo 642303 7050655 := bstep (se 1 (by rfl) ⟨5287991, by rfl⟩ : syracuseStep 7050655 = 10575983) B10575983
theorem B4954121 : Blo 642303 4954121 := bstep (se 2 (by rfl) ⟨1857795, by rfl⟩ : syracuseStep 4954121 = 3715591) B3715591
theorem B1448027 : Blo 642303 1448027 := bstep (se 1 (by rfl) ⟨1086020, by rfl⟩ : syracuseStep 1448027 = 2172041) B2172041
theorem B2758799 : Blo 642303 2758799 := bstep (se 1 (by rfl) ⟨2069099, by rfl⟩ : syracuseStep 2758799 = 4138199) B4138199
theorem B1448801 : Blo 642303 1448801 := bstep (se 2 (by rfl) ⟨543300, by rfl⟩ : syracuseStep 1448801 = 1086601) B1086601
theorem B728047 : Blo 642303 728047 := bstep (se 1 (by rfl) ⟨546035, by rfl⟩ : syracuseStep 728047 = 1092071) B1092071
theorem B7445951 : Blo 642303 7445951 := bstep (se 1 (by rfl) ⟨5584463, by rfl⟩ : syracuseStep 7445951 = 11168927) B11168927
theorem B676765205 : Blo 642303 676765205 := bstep (se 6 (by rfl) ⟨15861684, by rfl⟩ : syracuseStep 676765205 = 31723369) B31723369
theorem B1449791 : Blo 642303 1449791 := bstep (se 1 (by rfl) ⟨1087343, by rfl⟩ : syracuseStep 1449791 = 2174687) B2174687
theorem B2170745 : Blo 642303 2170745 := bstep (se 2 (by rfl) ⟨814029, by rfl⟩ : syracuseStep 2170745 = 1628059) B1628059
theorem B3679627 : Blo 642303 3679627 := bstep (se 1 (by rfl) ⟨2759720, by rfl⟩ : syracuseStep 3679627 = 5519441) B5519441
theorem B1451879 : Blo 642303 1451879 := bstep (se 1 (by rfl) ⟨1088909, by rfl⟩ : syracuseStep 1451879 = 2177819) B2177819
theorem B5220287 : Blo 642303 5220287 := bstep (se 1 (by rfl) ⟨3915215, by rfl⟩ : syracuseStep 5220287 = 7830431) B7830431
theorem B1746983 : Blo 642303 1746983 := bstep (se 1 (by rfl) ⟨1310237, by rfl⟩ : syracuseStep 1746983 = 2620475) B2620475
theorem B2175227 : Blo 642303 2175227 := bstep (se 1 (by rfl) ⟨1631420, by rfl⟩ : syracuseStep 2175227 = 3262841) B3262841
theorem B2176091 : Blo 642303 2176091 := bstep (se 1 (by rfl) ⟨1632068, by rfl⟩ : syracuseStep 2176091 = 3264137) B3264137
theorem B2176253 : Blo 642303 2176253 := bstep (se 3 (by rfl) ⟨408047, by rfl⟩ : syracuseStep 2176253 = 816095) B816095
theorem B4634171 : Blo 642303 4634171 := bstep (se 1 (by rfl) ⟨3475628, by rfl⟩ : syracuseStep 4634171 = 6951257) B6951257
theorem B2439659 : Blo 642303 2439659 := bstep (se 1 (by rfl) ⟨1829744, by rfl⟩ : syracuseStep 2439659 = 3659489) B3659489
theorem B2439841 : Blo 642303 2439841 := bstep (se 2 (by rfl) ⟨914940, by rfl⟩ : syracuseStep 2439841 = 1829881) B1829881
theorem B965663 : Blo 642303 965663 := bstep (se 1 (by rfl) ⟨724247, by rfl⟩ : syracuseStep 965663 = 1448495) B1448495
theorem B965735 : Blo 642303 965735 := bstep (se 1 (by rfl) ⟨724301, by rfl⟩ : syracuseStep 965735 = 1448603) B1448603
theorem B3095767 : Blo 642303 3095767 := bstep (se 1 (by rfl) ⟨2321825, by rfl⟩ : syracuseStep 3095767 = 4643651) B4643651
theorem B3489313 : Blo 642303 3489313 := bstep (se 2 (by rfl) ⟨1308492, by rfl⟩ : syracuseStep 3489313 = 2616985) B2616985
theorem B4898879 : Blo 642303 4898879 := bstep (se 1 (by rfl) ⟨3674159, by rfl⟩ : syracuseStep 4898879 = 7348319) B7348319
theorem B163070081 : Blo 642303 163070081 := bstep (se 2 (by rfl) ⟨61151280, by rfl⟩ : syracuseStep 163070081 = 122302561) B122302561
theorem B3260735 : Blo 642303 3260735 := bstep (se 1 (by rfl) ⟨2445551, by rfl⟩ : syracuseStep 3260735 = 4891103) B4891103
theorem B55624157 : Blo 642303 55624157 := bstep (se 3 (by rfl) ⟨10429529, by rfl⟩ : syracuseStep 55624157 = 20859059) B20859059
theorem B967451 : Blo 642303 967451 := bstep (se 1 (by rfl) ⟨725588, by rfl⟩ : syracuseStep 967451 = 1451177) B1451177
theorem B8277065 : Blo 642303 8277065 := bstep (se 2 (by rfl) ⟨3103899, by rfl⟩ : syracuseStep 8277065 = 6207799) B6207799
theorem B7359983 : Blo 642303 7359983 := bstep (se 1 (by rfl) ⟨5519987, by rfl⟩ : syracuseStep 7359983 = 11039975) B11039975
theorem B872383 : Blo 642303 872383 := bstep (se 1 (by rfl) ⟨654287, by rfl⟩ : syracuseStep 872383 = 1308575) B1308575
theorem B17584073 : Blo 642303 17584073 := bstep (se 2 (by rfl) ⟨6594027, by rfl⟩ : syracuseStep 17584073 = 13188055) B13188055
theorem B3264623 : Blo 642303 3264623 := bstep (se 1 (by rfl) ⟨2448467, by rfl⟩ : syracuseStep 3264623 = 4896935) B4896935
theorem B643295 : Blo 642303 643295 := bstep (se 1 (by rfl) ⟨482471, by rfl⟩ : syracuseStep 643295 = 964943) B964943
theorem B2381471 : Blo 642303 2381471 := bstep (se 1 (by rfl) ⟨1786103, by rfl⟩ : syracuseStep 2381471 = 3572207) B3572207
theorem B4118363 : Blo 642303 4118363 := bstep (se 1 (by rfl) ⟨3088772, by rfl⟩ : syracuseStep 4118363 = 6177545) B6177545
theorem B645087 : Blo 642303 645087 := bstep (se 1 (by rfl) ⟨483815, by rfl⟩ : syracuseStep 645087 = 967631) B967631
theorem B14899301 : Blo 642303 14899301 := bstep (se 4 (by rfl) ⟨1396809, by rfl⟩ : syracuseStep 14899301 = 2793619) B2793619
theorem B6970151 : Blo 642303 6970151 := bstep (se 1 (by rfl) ⟨5227613, by rfl⟩ : syracuseStep 6970151 = 10455227) B10455227
theorem B1629193 : Blo 642303 1629193 := bstep (se 2 (by rfl) ⟨610947, by rfl⟩ : syracuseStep 1629193 = 1221895) B1221895
theorem B12410131 : Blo 642303 12410131 := bstep (se 1 (by rfl) ⟨9307598, by rfl⟩ : syracuseStep 12410131 = 18615197) B18615197
theorem B11757905 : Blo 642303 11757905 := bstep (se 2 (by rfl) ⟨4409214, by rfl⟩ : syracuseStep 11757905 = 8818429) B8818429
theorem B2747591 : Blo 642303 2747591 := bstep (se 1 (by rfl) ⟨2060693, by rfl⟩ : syracuseStep 2747591 = 4121387) B4121387
theorem B2977031 : Blo 642303 2977031 := bstep (se 1 (by rfl) ⟨2232773, by rfl⟩ : syracuseStep 2977031 = 4465547) B4465547
theorem B814799 : Blo 642303 814799 := bstep (se 1 (by rfl) ⟨611099, by rfl⟩ : syracuseStep 814799 = 1222199) B1222199
theorem B2748239 : Blo 642303 2748239 := bstep (se 1 (by rfl) ⟨2061179, by rfl⟩ : syracuseStep 2748239 = 4122359) B4122359
theorem B817391 : Blo 642303 817391 := bstep (se 1 (by rfl) ⟨613043, by rfl⟩ : syracuseStep 817391 = 1226087) B1226087
theorem B4881383 : Blo 642303 4881383 := bstep (se 1 (by rfl) ⟨3661037, by rfl⟩ : syracuseStep 4881383 = 7322075) B7322075
theorem B918631 : Blo 642303 918631 := bstep (se 1 (by rfl) ⟨688973, by rfl⟩ : syracuseStep 918631 = 1377947) B1377947
theorem B1836283 : Blo 642303 1836283 := bstep (se 1 (by rfl) ⟨1377212, by rfl⟩ : syracuseStep 1836283 = 2754425) B2754425
theorem B919679 : Blo 642303 919679 := bstep (se 1 (by rfl) ⟨689759, by rfl⟩ : syracuseStep 919679 = 1379519) B1379519
theorem B1838015 : Blo 642303 1838015 := bstep (se 1 (by rfl) ⟨1378511, by rfl⟩ : syracuseStep 1838015 = 2757023) B2757023
theorem B9932867 : Blo 642303 9932867 := bstep (se 1 (by rfl) ⟨7449650, by rfl⟩ : syracuseStep 9932867 = 14899301) B14899301
theorem B1839199 : Blo 642303 1839199 := bstep (se 1 (by rfl) ⟨1379399, by rfl⟩ : syracuseStep 1839199 = 2758799) B2758799
theorem B3674321 : Blo 642303 3674321 := bstep (se 2 (by rfl) ⟨1377870, by rfl⟩ : syracuseStep 3674321 = 2755741) B2755741
theorem B1446569 : Blo 642303 1446569 := bstep (se 2 (by rfl) ⟨542463, by rfl⟩ : syracuseStep 1446569 = 1084927) B1084927
theorem B1447163 : Blo 642303 1447163 := bstep (se 1 (by rfl) ⟨1085372, by rfl⟩ : syracuseStep 1447163 = 2170745) B2170745
theorem B3480191 : Blo 642303 3480191 := bstep (se 1 (by rfl) ⟨2610143, by rfl⟩ : syracuseStep 3480191 = 5220287) B5220287
theorem B7838603 : Blo 642303 7838603 := bstep (se 1 (by rfl) ⟨5878952, by rfl⟩ : syracuseStep 7838603 = 11757905) B11757905
theorem B1450151 : Blo 642303 1450151 := bstep (se 1 (by rfl) ⟨1087613, by rfl⟩ : syracuseStep 1450151 = 2175227) B2175227
theorem B7938749 : Blo 642303 7938749 := bstep (se 3 (by rfl) ⟨1488515, by rfl⟩ : syracuseStep 7938749 = 2977031) B2977031
theorem B1450727 : Blo 642303 1450727 := bstep (se 1 (by rfl) ⟨1088045, by rfl⟩ : syracuseStep 1450727 = 2176091) B2176091
theorem B1450835 : Blo 642303 1450835 := bstep (se 1 (by rfl) ⟨1088126, by rfl⟩ : syracuseStep 1450835 = 2176253) B2176253
theorem B3253121 : Blo 642303 3253121 := bstep (se 2 (by rfl) ⟨1219920, by rfl⟩ : syracuseStep 3253121 = 2439841) B2439841
theorem B3089447 : Blo 642303 3089447 := bstep (se 1 (by rfl) ⟨2317085, by rfl⟩ : syracuseStep 3089447 = 4634171) B4634171
theorem B2172257 : Blo 642303 2172257 := bstep (se 2 (by rfl) ⟨814596, by rfl⟩ : syracuseStep 2172257 = 1629193) B1629193
theorem B2172797 : Blo 642303 2172797 := bstep (se 3 (by rfl) ⟨407399, by rfl⟩ : syracuseStep 2172797 = 814799) B814799
theorem B3254255 : Blo 642303 3254255 := bstep (se 1 (by rfl) ⟨2440691, by rfl⟩ : syracuseStep 3254255 = 4881383) B4881383
theorem B2173823 : Blo 642303 2173823 := bstep (se 1 (by rfl) ⟨1630367, by rfl⟩ : syracuseStep 2173823 = 3260735) B3260735
theorem B5518043 : Blo 642303 5518043 := bstep (se 1 (by rfl) ⟨4138532, by rfl⟩ : syracuseStep 5518043 = 8277065) B8277065
theorem B2176415 : Blo 642303 2176415 := bstep (se 1 (by rfl) ⟨1632311, by rfl⟩ : syracuseStep 2176415 = 3264623) B3264623
theorem B1587647 : Blo 642303 1587647 := bstep (se 1 (by rfl) ⟨1190735, by rfl⟩ : syracuseStep 1587647 = 2381471) B2381471
theorem B965351 : Blo 642303 965351 := bstep (se 1 (by rfl) ⟨724013, by rfl⟩ : syracuseStep 965351 = 1448027) B1448027
theorem B965867 : Blo 642303 965867 := bstep (se 1 (by rfl) ⟨724400, by rfl⟩ : syracuseStep 965867 = 1448801) B1448801
theorem B4963967 : Blo 642303 4963967 := bstep (se 1 (by rfl) ⟨3722975, by rfl⟩ : syracuseStep 4963967 = 7445951) B7445951
theorem B966527 : Blo 642303 966527 := bstep (se 1 (by rfl) ⟨724895, by rfl⟩ : syracuseStep 966527 = 1449791) B1449791
theorem B1163177 : Blo 642303 1163177 := bstep (se 2 (by rfl) ⟨436191, by rfl⟩ : syracuseStep 1163177 = 872383) B872383
theorem B2179709 : Blo 642303 2179709 := bstep (se 3 (by rfl) ⟨408695, by rfl⟩ : syracuseStep 2179709 = 817391) B817391
theorem B967919 : Blo 642303 967919 := bstep (se 1 (by rfl) ⟨725939, by rfl⟩ : syracuseStep 967919 = 1451879) B1451879
theorem B1164655 : Blo 642303 1164655 := bstep (se 1 (by rfl) ⟨873491, by rfl⟩ : syracuseStep 1164655 = 1746983) B1746983
theorem B970729 : Blo 642303 970729 := bstep (se 2 (by rfl) ⟨364023, by rfl⟩ : syracuseStep 970729 = 728047) B728047
theorem B1626439 : Blo 642303 1626439 := bstep (se 1 (by rfl) ⟨1219829, by rfl⟩ : syracuseStep 1626439 = 2439659) B2439659
theorem B643775 : Blo 642303 643775 := bstep (se 1 (by rfl) ⟨482831, by rfl⟩ : syracuseStep 643775 = 965663) B965663
theorem B643823 : Blo 642303 643823 := bstep (se 1 (by rfl) ⟨482867, by rfl⟩ : syracuseStep 643823 = 965735) B965735
theorem B3265919 : Blo 642303 3265919 := bstep (se 1 (by rfl) ⟨2449439, by rfl⟩ : syracuseStep 3265919 = 4898879) B4898879
theorem B108713387 : Blo 642303 108713387 := bstep (se 1 (by rfl) ⟨81535040, by rfl⟩ : syracuseStep 108713387 = 163070081) B163070081
theorem B37082771 : Blo 642303 37082771 := bstep (se 1 (by rfl) ⟨27812078, by rfl⟩ : syracuseStep 37082771 = 55624157) B55624157
theorem B644967 : Blo 642303 644967 := bstep (se 1 (by rfl) ⟨483725, by rfl⟩ : syracuseStep 644967 = 967451) B967451
theorem B3103687 : Blo 642303 3103687 := bstep (se 1 (by rfl) ⟨2327765, by rfl⟩ : syracuseStep 3103687 = 4655531) B4655531
theorem B4906169 : Blo 642303 4906169 := bstep (se 2 (by rfl) ⟨1839813, by rfl⟩ : syracuseStep 4906169 = 3679627) B3679627
theorem B4906655 : Blo 642303 4906655 := bstep (se 1 (by rfl) ⟨3679991, by rfl⟩ : syracuseStep 4906655 = 7359983) B7359983
theorem B11722715 : Blo 642303 11722715 := bstep (se 1 (by rfl) ⟨8792036, by rfl⟩ : syracuseStep 11722715 = 17584073) B17584073
theorem B2745575 : Blo 642303 2745575 := bstep (se 1 (by rfl) ⟨2059181, by rfl⟩ : syracuseStep 2745575 = 4118363) B4118363
theorem B3302747 : Blo 642303 3302747 := bstep (se 1 (by rfl) ⟨2477060, by rfl⟩ : syracuseStep 3302747 = 4954121) B4954121
theorem B4646767 : Blo 642303 4646767 := bstep (se 1 (by rfl) ⟨3485075, by rfl⟩ : syracuseStep 4646767 = 6970151) B6970151
theorem B451176803 : Blo 642303 451176803 := bstep (se 1 (by rfl) ⟨338382602, by rfl⟩ : syracuseStep 451176803 = 676765205) B676765205
theorem B9400873 : Blo 642303 9400873 := bstep (se 2 (by rfl) ⟨3525327, by rfl⟩ : syracuseStep 9400873 = 7050655) B7050655
theorem B1831727 : Blo 642303 1831727 := bstep (se 1 (by rfl) ⟨1373795, by rfl⟩ : syracuseStep 1831727 = 2747591) B2747591
theorem B1832159 : Blo 642303 1832159 := bstep (se 1 (by rfl) ⟨1374119, by rfl⟩ : syracuseStep 1832159 = 2748239) B2748239
theorem B4127689 : Blo 642303 4127689 := bstep (se 2 (by rfl) ⟨1547883, by rfl⟩ : syracuseStep 4127689 = 3095767) B3095767
theorem B16546841 : Blo 642303 16546841 := bstep (se 2 (by rfl) ⟨6205065, by rfl⟩ : syracuseStep 16546841 = 12410131) B12410131
theorem B4652417 : Blo 642303 4652417 := bstep (se 2 (by rfl) ⟨1744656, by rfl⟩ : syracuseStep 4652417 = 3489313) B3489313
theorem B6195689 : Blo 642303 6195689 := bstep (se 2 (by rfl) ⟨2323383, by rfl⟩ : syracuseStep 6195689 = 4646767) B4646767
theorem B6621911 : Blo 642303 6621911 := bstep (se 1 (by rfl) ⟨4966433, by rfl⟩ : syracuseStep 6621911 = 9932867) B9932867
theorem B4885757 : Blo 642303 4885757 := bstep (se 3 (by rfl) ⟨916079, by rfl⟩ : syracuseStep 4885757 = 1832159) B1832159
theorem B289902365 : Blo 642303 289902365 := bstep (se 3 (by rfl) ⟨54356693, by rfl⟩ : syracuseStep 289902365 = 108713387) B108713387
theorem B2168585 : Blo 642303 2168585 := bstep (se 2 (by rfl) ⟨813219, by rfl⟩ : syracuseStep 2168585 = 1626439) B1626439
theorem B2168747 : Blo 642303 2168747 := bstep (se 1 (by rfl) ⟨1626560, by rfl⟩ : syracuseStep 2168747 = 3253121) B3253121
theorem B2201831 : Blo 642303 2201831 := bstep (se 1 (by rfl) ⟨1651373, by rfl⟩ : syracuseStep 2201831 = 3302747) B3302747
theorem B1448171 : Blo 642303 1448171 := bstep (se 1 (by rfl) ⟨1086128, by rfl⟩ : syracuseStep 1448171 = 2172257) B2172257
theorem B4233725 : Blo 642303 4233725 := bstep (se 3 (by rfl) ⟨793823, by rfl⟩ : syracuseStep 4233725 = 1587647) B1587647
theorem B1448531 : Blo 642303 1448531 := bstep (se 1 (by rfl) ⟨1086398, by rfl⟩ : syracuseStep 1448531 = 2172797) B2172797
theorem B2169503 : Blo 642303 2169503 := bstep (se 1 (by rfl) ⟨1627127, by rfl⟩ : syracuseStep 2169503 = 3254255) B3254255
theorem B300784535 : Blo 642303 300784535 := bstep (se 1 (by rfl) ⟨225588401, by rfl⟩ : syracuseStep 300784535 = 451176803) B451176803
theorem B1449215 : Blo 642303 1449215 := bstep (se 1 (by rfl) ⟨1086911, by rfl⟩ : syracuseStep 1449215 = 2173823) B2173823
theorem B3678695 : Blo 642303 3678695 := bstep (se 1 (by rfl) ⟨2759021, by rfl⟩ : syracuseStep 3678695 = 5518043) B5518043
theorem B1221151 : Blo 642303 1221151 := bstep (se 1 (by rfl) ⟨915863, by rfl⟩ : syracuseStep 1221151 = 1831727) B1831727
theorem B1450943 : Blo 642303 1450943 := bstep (se 1 (by rfl) ⟨1088207, by rfl⟩ : syracuseStep 1450943 = 2176415) B2176415
theorem B4138249 : Blo 642303 4138249 := bstep (se 2 (by rfl) ⟨1551843, by rfl⟩ : syracuseStep 4138249 = 3103687) B3103687
theorem B1453139 : Blo 642303 1453139 := bstep (se 1 (by rfl) ⟨1089854, by rfl⟩ : syracuseStep 1453139 = 2179709) B2179709
theorem B1552873 : Blo 642303 1552873 := bstep (se 2 (by rfl) ⟨582327, by rfl⟩ : syracuseStep 1552873 = 1164655) B1164655
theorem B1225343 : Blo 642303 1225343 := bstep (se 1 (by rfl) ⟨919007, by rfl⟩ : syracuseStep 1225343 = 1838015) B1838015
theorem B964379 : Blo 642303 964379 := bstep (se 1 (by rfl) ⟨723284, by rfl⟩ : syracuseStep 964379 = 1446569) B1446569
theorem B964775 : Blo 642303 964775 := bstep (se 1 (by rfl) ⟨723581, by rfl⟩ : syracuseStep 964775 = 1447163) B1447163
theorem B2177279 : Blo 642303 2177279 := bstep (se 1 (by rfl) ⟨1632959, by rfl⟩ : syracuseStep 2177279 = 3265919) B3265919
theorem B24721847 : Blo 642303 24721847 := bstep (se 1 (by rfl) ⟨18541385, by rfl⟩ : syracuseStep 24721847 = 37082771) B37082771
theorem B5225735 : Blo 642303 5225735 := bstep (se 1 (by rfl) ⟨3919301, by rfl⟩ : syracuseStep 5225735 = 7838603) B7838603
theorem B7815143 : Blo 642303 7815143 := bstep (se 1 (by rfl) ⟨5861357, by rfl⟩ : syracuseStep 7815143 = 11722715) B11722715
theorem B966767 : Blo 642303 966767 := bstep (se 1 (by rfl) ⟨725075, by rfl⟩ : syracuseStep 966767 = 1450151) B1450151
theorem B5292499 : Blo 642303 5292499 := bstep (se 1 (by rfl) ⟨3969374, by rfl⟩ : syracuseStep 5292499 = 7938749) B7938749
theorem B967151 : Blo 642303 967151 := bstep (se 1 (by rfl) ⟨725363, by rfl⟩ : syracuseStep 967151 = 1450727) B1450727
theorem B4899365 : Blo 642303 4899365 := bstep (se 4 (by rfl) ⟨459315, by rfl⟩ : syracuseStep 4899365 = 918631) B918631
theorem B967223 : Blo 642303 967223 := bstep (se 1 (by rfl) ⟨725417, by rfl⟩ : syracuseStep 967223 = 1450835) B1450835
theorem B12534497 : Blo 642303 12534497 := bstep (se 2 (by rfl) ⟨4700436, by rfl⟩ : syracuseStep 12534497 = 9400873) B9400873
theorem B643567 : Blo 642303 643567 := bstep (se 1 (by rfl) ⟨482675, by rfl⟩ : syracuseStep 643567 = 965351) B965351
theorem B11031227 : Blo 642303 11031227 := bstep (se 1 (by rfl) ⟨8273420, by rfl⟩ : syracuseStep 11031227 = 16546841) B16546841
theorem B643911 : Blo 642303 643911 := bstep (se 1 (by rfl) ⟨482933, by rfl⟩ : syracuseStep 643911 = 965867) B965867
theorem B3101611 : Blo 642303 3101611 := bstep (se 1 (by rfl) ⟨2326208, by rfl⟩ : syracuseStep 3101611 = 4652417) B4652417
theorem B644351 : Blo 642303 644351 := bstep (se 1 (by rfl) ⟨483263, by rfl⟩ : syracuseStep 644351 = 966527) B966527
theorem B775451 : Blo 642303 775451 := bstep (se 1 (by rfl) ⟨581588, by rfl⟩ : syracuseStep 775451 = 1163177) B1163177
theorem B645279 : Blo 642303 645279 := bstep (se 1 (by rfl) ⟨483959, by rfl⟩ : syracuseStep 645279 = 967919) B967919
theorem B2448377 : Blo 642303 2448377 := bstep (se 2 (by rfl) ⟨918141, by rfl⟩ : syracuseStep 2448377 = 1836283) B1836283
theorem B2449547 : Blo 642303 2449547 := bstep (se 1 (by rfl) ⟨1837160, by rfl⟩ : syracuseStep 2449547 = 3674321) B3674321
theorem B2320127 : Blo 642303 2320127 := bstep (se 1 (by rfl) ⟨1740095, by rfl⟩ : syracuseStep 2320127 = 3480191) B3480191
theorem B3270779 : Blo 642303 3270779 := bstep (se 1 (by rfl) ⟨2453084, by rfl⟩ : syracuseStep 3270779 = 4906169) B4906169
theorem B3271103 : Blo 642303 3271103 := bstep (se 1 (by rfl) ⟨2453327, by rfl⟩ : syracuseStep 3271103 = 4906655) B4906655
theorem B2452265 : Blo 642303 2452265 := bstep (se 2 (by rfl) ⟨919599, by rfl⟩ : syracuseStep 2452265 = 1839199) B1839199
theorem B2452477 : Blo 642303 2452477 := bstep (se 3 (by rfl) ⟨459839, by rfl⟩ : syracuseStep 2452477 = 919679) B919679
theorem B2059631 : Blo 642303 2059631 := bstep (se 1 (by rfl) ⟨1544723, by rfl⟩ : syracuseStep 2059631 = 3089447) B3089447
theorem B1830383 : Blo 642303 1830383 := bstep (se 1 (by rfl) ⟨1372787, by rfl⟩ : syracuseStep 1830383 = 2745575) B2745575
theorem B5503585 : Blo 642303 5503585 := bstep (se 2 (by rfl) ⟨2063844, by rfl⟩ : syracuseStep 5503585 = 4127689) B4127689
theorem B20708885 : Blo 642303 20708885 := bstep (se 6 (by rfl) ⟨485364, by rfl⟩ : syracuseStep 20708885 = 970729) B970729
theorem B3309311 : Blo 642303 3309311 := bstep (se 1 (by rfl) ⟨2481983, by rfl⟩ : syracuseStep 3309311 = 4963967) B4963967
theorem B8356331 : Blo 642303 8356331 := bstep (se 1 (by rfl) ⟨6267248, by rfl⟩ : syracuseStep 8356331 = 12534497) B12534497
theorem B4130459 : Blo 642303 4130459 := bstep (se 1 (by rfl) ⟨3097844, by rfl⟩ : syracuseStep 4130459 = 6195689) B6195689
theorem B193268243 : Blo 642303 193268243 := bstep (se 1 (by rfl) ⟨144951182, by rfl⟩ : syracuseStep 193268243 = 289902365) B289902365
theorem B2067869 : Blo 642303 2067869 := bstep (se 3 (by rfl) ⟨387725, by rfl⟩ : syracuseStep 2067869 = 775451) B775451
theorem B1445723 : Blo 642303 1445723 := bstep (se 1 (by rfl) ⟨1084292, by rfl⟩ : syracuseStep 1445723 = 2168585) B2168585
theorem B1445831 : Blo 642303 1445831 := bstep (se 1 (by rfl) ⟨1084373, by rfl⟩ : syracuseStep 1445831 = 2168747) B2168747
theorem B2822483 : Blo 642303 2822483 := bstep (se 1 (by rfl) ⟨2116862, by rfl⟩ : syracuseStep 2822483 = 4233725) B4233725
theorem B1446335 : Blo 642303 1446335 := bstep (se 1 (by rfl) ⟨1084751, by rfl⟩ : syracuseStep 1446335 = 2169503) B2169503
theorem B2070497 : Blo 642303 2070497 := bstep (se 2 (by rfl) ⟨776436, by rfl⟩ : syracuseStep 2070497 = 1552873) B1552873
theorem B1546751 : Blo 642303 1546751 := bstep (se 1 (by rfl) ⟨1160063, by rfl⟩ : syracuseStep 1546751 = 2320127) B2320127
theorem B4135481 : Blo 642303 4135481 := bstep (se 2 (by rfl) ⟨1550805, by rfl⟩ : syracuseStep 4135481 = 3101611) B3101611
theorem B1220255 : Blo 642303 1220255 := bstep (se 1 (by rfl) ⟨915191, by rfl⟩ : syracuseStep 1220255 = 1830383) B1830383
theorem B1451519 : Blo 642303 1451519 := bstep (se 1 (by rfl) ⟨1088639, by rfl⟩ : syracuseStep 1451519 = 2177279) B2177279
theorem B3483823 : Blo 642303 3483823 := bstep (se 1 (by rfl) ⟨2612867, by rfl⟩ : syracuseStep 3483823 = 5225735) B5225735
theorem B13805923 : Blo 642303 13805923 := bstep (se 1 (by rfl) ⟨10354442, by rfl⟩ : syracuseStep 13805923 = 20708885) B20708885
theorem B2206207 : Blo 642303 2206207 := bstep (se 1 (by rfl) ⟨1654655, by rfl⟩ : syracuseStep 2206207 = 3309311) B3309311
theorem B7056665 : Blo 642303 7056665 := bstep (se 2 (by rfl) ⟨2646249, by rfl⟩ : syracuseStep 7056665 = 5292499) B5292499
theorem B5517665 : Blo 642303 5517665 := bstep (se 2 (by rfl) ⟨2069124, by rfl⟩ : syracuseStep 5517665 = 4138249) B4138249
theorem B3257171 : Blo 642303 3257171 := bstep (se 1 (by rfl) ⟨2442878, by rfl⟩ : syracuseStep 3257171 = 4885757) B4885757
theorem B7354151 : Blo 642303 7354151 := bstep (se 1 (by rfl) ⟨5515613, by rfl⟩ : syracuseStep 7354151 = 11031227) B11031227
theorem B965447 : Blo 642303 965447 := bstep (se 1 (by rfl) ⟨724085, by rfl⟩ : syracuseStep 965447 = 1448171) B1448171
theorem B965687 : Blo 642303 965687 := bstep (se 1 (by rfl) ⟨724265, by rfl⟩ : syracuseStep 965687 = 1448531) B1448531
theorem B200523023 : Blo 642303 200523023 := bstep (se 1 (by rfl) ⟨150392267, by rfl⟩ : syracuseStep 200523023 = 300784535) B300784535
theorem B966143 : Blo 642303 966143 := bstep (se 1 (by rfl) ⟨724607, by rfl⟩ : syracuseStep 966143 = 1449215) B1449215
theorem B967295 : Blo 642303 967295 := bstep (se 1 (by rfl) ⟨725471, by rfl⟩ : syracuseStep 967295 = 1450943) B1450943
theorem B2180519 : Blo 642303 2180519 := bstep (se 1 (by rfl) ⟨1635389, by rfl⟩ : syracuseStep 2180519 = 3270779) B3270779
theorem B2180735 : Blo 642303 2180735 := bstep (se 1 (by rfl) ⟨1635551, by rfl⟩ : syracuseStep 2180735 = 3271103) B3271103
theorem B968759 : Blo 642303 968759 := bstep (se 1 (by rfl) ⟨726569, by rfl⟩ : syracuseStep 968759 = 1453139) B1453139
theorem B642919 : Blo 642303 642919 := bstep (se 1 (by rfl) ⟨482189, by rfl⟩ : syracuseStep 642919 = 964379) B964379
theorem B643183 : Blo 642303 643183 := bstep (se 1 (by rfl) ⟨482387, by rfl⟩ : syracuseStep 643183 = 964775) B964775
theorem B644511 : Blo 642303 644511 := bstep (se 1 (by rfl) ⟨483383, by rfl⟩ : syracuseStep 644511 = 966767) B966767
theorem B644767 : Blo 642303 644767 := bstep (se 1 (by rfl) ⟨483575, by rfl⟩ : syracuseStep 644767 = 967151) B967151
theorem B3266243 : Blo 642303 3266243 := bstep (se 1 (by rfl) ⟨2449682, by rfl⟩ : syracuseStep 3266243 = 4899365) B4899365
theorem B644815 : Blo 642303 644815 := bstep (se 1 (by rfl) ⟨483611, by rfl⟩ : syracuseStep 644815 = 967223) B967223
theorem B1628201 : Blo 642303 1628201 := bstep (se 2 (by rfl) ⟨610575, by rfl⟩ : syracuseStep 1628201 = 1221151) B1221151
theorem B4414607 : Blo 642303 4414607 := bstep (se 1 (by rfl) ⟨3310955, by rfl⟩ : syracuseStep 4414607 = 6621911) B6621911
theorem B3269969 : Blo 642303 3269969 := bstep (se 2 (by rfl) ⟨1226238, by rfl⟩ : syracuseStep 3269969 = 2452477) B2452477
theorem B1467887 : Blo 642303 1467887 := bstep (se 1 (by rfl) ⟨1100915, by rfl⟩ : syracuseStep 1467887 = 2201831) B2201831
theorem B1632251 : Blo 642303 1632251 := bstep (se 1 (by rfl) ⟨1224188, by rfl⟩ : syracuseStep 1632251 = 2448377) B2448377
theorem B1633031 : Blo 642303 1633031 := bstep (se 1 (by rfl) ⟨1224773, by rfl⟩ : syracuseStep 1633031 = 2449547) B2449547
theorem B2452463 : Blo 642303 2452463 := bstep (se 1 (by rfl) ⟨1839347, by rfl⟩ : syracuseStep 2452463 = 3678695) B3678695
theorem B1634843 : Blo 642303 1634843 := bstep (se 1 (by rfl) ⟨1226132, by rfl⟩ : syracuseStep 1634843 = 2452265) B2452265
theorem B1373087 : Blo 642303 1373087 := bstep (se 1 (by rfl) ⟨1029815, by rfl⟩ : syracuseStep 1373087 = 2059631) B2059631
theorem B816895 : Blo 642303 816895 := bstep (se 1 (by rfl) ⟨612671, by rfl⟩ : syracuseStep 816895 = 1225343) B1225343
theorem B7338113 : Blo 642303 7338113 := bstep (se 2 (by rfl) ⟨2751792, by rfl⟩ : syracuseStep 7338113 = 5503585) B5503585
theorem B16481231 : Blo 642303 16481231 := bstep (se 1 (by rfl) ⟨12360923, by rfl⟩ : syracuseStep 16481231 = 24721847) B24721847
theorem B5210095 : Blo 642303 5210095 := bstep (se 1 (by rfl) ⟨3907571, by rfl⟩ : syracuseStep 5210095 = 7815143) B7815143
theorem B2753639 : Blo 642303 2753639 := bstep (se 1 (by rfl) ⟨2065229, by rfl⟩ : syracuseStep 2753639 = 4130459) B4130459
theorem B22283549 : Blo 642303 22283549 := bstep (se 3 (by rfl) ⟨4178165, by rfl⟩ : syracuseStep 22283549 = 8356331) B8356331
theorem B128845495 : Blo 642303 128845495 := bstep (se 1 (by rfl) ⟨96634121, by rfl⟩ : syracuseStep 128845495 = 193268243) B193268243
theorem B11766437 : Blo 642303 11766437 := bstep (se 4 (by rfl) ⟨1103103, by rfl⟩ : syracuseStep 11766437 = 2206207) B2206207
theorem B1380331 : Blo 642303 1380331 := bstep (se 1 (by rfl) ⟨1035248, by rfl⟩ : syracuseStep 1380331 = 2070497) B2070497
theorem B1085467 : Blo 642303 1085467 := bstep (se 1 (by rfl) ⟨814100, by rfl⟩ : syracuseStep 1085467 = 1628201) B1628201
theorem B2756987 : Blo 642303 2756987 := bstep (se 1 (by rfl) ⟨2067740, by rfl⟩ : syracuseStep 2756987 = 4135481) B4135481
theorem B1088167 : Blo 642303 1088167 := bstep (se 1 (by rfl) ⟨816125, by rfl⟩ : syracuseStep 1088167 = 1632251) B1632251
theorem B1088687 : Blo 642303 1088687 := bstep (se 1 (by rfl) ⟨816515, by rfl⟩ : syracuseStep 1088687 = 1633031) B1633031
theorem B1089193 : Blo 642303 1089193 := bstep (se 2 (by rfl) ⟨408447, by rfl⟩ : syracuseStep 1089193 = 816895) B816895
theorem B3678443 : Blo 642303 3678443 := bstep (se 1 (by rfl) ⟨2758832, by rfl⟩ : syracuseStep 3678443 = 5517665) B5517665
theorem B1089895 : Blo 642303 1089895 := bstep (se 1 (by rfl) ⟨817421, by rfl⟩ : syracuseStep 1089895 = 1634843) B1634843
theorem B2171447 : Blo 642303 2171447 := bstep (se 1 (by rfl) ⟨1628585, by rfl⟩ : syracuseStep 2171447 = 3257171) B3257171
theorem B5514317 : Blo 642303 5514317 := bstep (se 3 (by rfl) ⟨1033934, by rfl⟩ : syracuseStep 5514317 = 2067869) B2067869
theorem B4892075 : Blo 642303 4892075 := bstep (se 1 (by rfl) ⟨3669056, by rfl⟩ : syracuseStep 4892075 = 7338113) B7338113
theorem B10987487 : Blo 642303 10987487 := bstep (se 1 (by rfl) ⟨8240615, by rfl⟩ : syracuseStep 10987487 = 16481231) B16481231
theorem B1453679 : Blo 642303 1453679 := bstep (se 1 (by rfl) ⟨1090259, by rfl⟩ : syracuseStep 1453679 = 2180519) B2180519
theorem B1453823 : Blo 642303 1453823 := bstep (se 1 (by rfl) ⟨1090367, by rfl⟩ : syracuseStep 1453823 = 2180735) B2180735
theorem B963815 : Blo 642303 963815 := bstep (se 1 (by rfl) ⟨722861, by rfl⟩ : syracuseStep 963815 = 1445723) B1445723
theorem B963887 : Blo 642303 963887 := bstep (se 1 (by rfl) ⟨722915, by rfl⟩ : syracuseStep 963887 = 1445831) B1445831
theorem B964223 : Blo 642303 964223 := bstep (se 1 (by rfl) ⟨723167, by rfl⟩ : syracuseStep 964223 = 1446335) B1446335
theorem B2177495 : Blo 642303 2177495 := bstep (se 1 (by rfl) ⟨1633121, by rfl⟩ : syracuseStep 2177495 = 3266243) B3266243
theorem B3914365 : Blo 642303 3914365 := bstep (se 3 (by rfl) ⟨733943, by rfl⟩ : syracuseStep 3914365 = 1467887) B1467887
theorem B1031167 : Blo 642303 1031167 := bstep (se 1 (by rfl) ⟨773375, by rfl⟩ : syracuseStep 1031167 = 1546751) B1546751
theorem B2179979 : Blo 642303 2179979 := bstep (se 1 (by rfl) ⟨1634984, by rfl⟩ : syracuseStep 2179979 = 3269969) B3269969
theorem B967679 : Blo 642303 967679 := bstep (se 1 (by rfl) ⟨725759, by rfl⟩ : syracuseStep 967679 = 1451519) B1451519
theorem B4704443 : Blo 642303 4704443 := bstep (se 1 (by rfl) ⟨3528332, by rfl⟩ : syracuseStep 4704443 = 7056665) B7056665
theorem B4902767 : Blo 642303 4902767 := bstep (se 1 (by rfl) ⟨3677075, by rfl⟩ : syracuseStep 4902767 = 7354151) B7354151
theorem B643631 : Blo 642303 643631 := bstep (se 1 (by rfl) ⟨482723, by rfl⟩ : syracuseStep 643631 = 965447) B965447
theorem B643791 : Blo 642303 643791 := bstep (se 1 (by rfl) ⟨482843, by rfl⟩ : syracuseStep 643791 = 965687) B965687
theorem B133682015 : Blo 642303 133682015 := bstep (se 1 (by rfl) ⟨100261511, by rfl⟩ : syracuseStep 133682015 = 200523023) B200523023
theorem B644095 : Blo 642303 644095 := bstep (se 1 (by rfl) ⟨483071, by rfl⟩ : syracuseStep 644095 = 966143) B966143
theorem B644863 : Blo 642303 644863 := bstep (se 1 (by rfl) ⟨483647, by rfl⟩ : syracuseStep 644863 = 967295) B967295
theorem B7526621 : Blo 642303 7526621 := bstep (se 3 (by rfl) ⟨1411241, by rfl⟩ : syracuseStep 7526621 = 2822483) B2822483
theorem B645839 : Blo 642303 645839 := bstep (se 1 (by rfl) ⟨484379, by rfl⟩ : syracuseStep 645839 = 968759) B968759
theorem B4645097 : Blo 642303 4645097 := bstep (se 2 (by rfl) ⟨1741911, by rfl⟩ : syracuseStep 4645097 = 3483823) B3483823
theorem B18407897 : Blo 642303 18407897 := bstep (se 2 (by rfl) ⟨6902961, by rfl⟩ : syracuseStep 18407897 = 13805923) B13805923
theorem B2943071 : Blo 642303 2943071 := bstep (se 1 (by rfl) ⟨2207303, by rfl⟩ : syracuseStep 2943071 = 4414607) B4414607
theorem B813503 : Blo 642303 813503 := bstep (se 1 (by rfl) ⟨610127, by rfl⟩ : syracuseStep 813503 = 1220255) B1220255
theorem B1634975 : Blo 642303 1634975 := bstep (se 1 (by rfl) ⟨1226231, by rfl⟩ : syracuseStep 1634975 = 2452463) B2452463
theorem B915391 : Blo 642303 915391 := bstep (se 1 (by rfl) ⟨686543, by rfl⟩ : syracuseStep 915391 = 1373087) B1373087
theorem B6946793 : Blo 642303 6946793 := bstep (se 2 (by rfl) ⟨2605047, by rfl⟩ : syracuseStep 6946793 = 5210095) B5210095
theorem B1835759 : Blo 642303 1835759 := bstep (se 1 (by rfl) ⟨1376819, by rfl⟩ : syracuseStep 1835759 = 2753639) B2753639
theorem B1837991 : Blo 642303 1837991 := bstep (se 1 (by rfl) ⟨1378493, by rfl⟩ : syracuseStep 1837991 = 2756987) B2756987
theorem B725791 : Blo 642303 725791 := bstep (se 1 (by rfl) ⟨544343, by rfl⟩ : syracuseStep 725791 = 1088687) B1088687
theorem B1840441 : Blo 642303 1840441 := bstep (se 2 (by rfl) ⟨690165, by rfl⟩ : syracuseStep 1840441 = 1380331) B1380331
theorem B1447289 : Blo 642303 1447289 := bstep (se 2 (by rfl) ⟨542733, by rfl⟩ : syracuseStep 1447289 = 1085467) B1085467
theorem B1447631 : Blo 642303 1447631 := bstep (se 1 (by rfl) ⟨1085723, by rfl⟩ : syracuseStep 1447631 = 2171447) B2171447
theorem B3676211 : Blo 642303 3676211 := bstep (se 1 (by rfl) ⟨2757158, by rfl⟩ : syracuseStep 3676211 = 5514317) B5514317
theorem B2169341 : Blo 642303 2169341 := bstep (se 3 (by rfl) ⟨406751, by rfl⟩ : syracuseStep 2169341 = 813503) B813503
theorem B1220521 : Blo 642303 1220521 := bstep (se 2 (by rfl) ⟨457695, by rfl⟩ : syracuseStep 1220521 = 915391) B915391
theorem B1089983 : Blo 642303 1089983 := bstep (se 1 (by rfl) ⟨817487, by rfl⟩ : syracuseStep 1089983 = 1634975) B1634975
theorem B5219153 : Blo 642303 5219153 := bstep (se 2 (by rfl) ⟨1957182, by rfl⟩ : syracuseStep 5219153 = 3914365) B3914365
theorem B1450889 : Blo 642303 1450889 := bstep (se 2 (by rfl) ⟨544083, by rfl⟩ : syracuseStep 1450889 = 1088167) B1088167
theorem B1451663 : Blo 642303 1451663 := bstep (se 1 (by rfl) ⟨1088747, by rfl⟩ : syracuseStep 1451663 = 2177495) B2177495
theorem B1452257 : Blo 642303 1452257 := bstep (se 2 (by rfl) ⟨544596, by rfl⟩ : syracuseStep 1452257 = 1089193) B1089193
theorem B4631195 : Blo 642303 4631195 := bstep (se 1 (by rfl) ⟨3473396, by rfl⟩ : syracuseStep 4631195 = 6946793) B6946793
theorem B1453193 : Blo 642303 1453193 := bstep (se 2 (by rfl) ⟨544947, by rfl⟩ : syracuseStep 1453193 = 1089895) B1089895
theorem B1453319 : Blo 642303 1453319 := bstep (se 1 (by rfl) ⟨1089989, by rfl⟩ : syracuseStep 1453319 = 2179979) B2179979
theorem B14855699 : Blo 642303 14855699 := bstep (se 1 (by rfl) ⟨11141774, by rfl⟩ : syracuseStep 14855699 = 22283549) B22283549
theorem B7844291 : Blo 642303 7844291 := bstep (se 1 (by rfl) ⟨5883218, by rfl⟩ : syracuseStep 7844291 = 11766437) B11766437
theorem B3096731 : Blo 642303 3096731 := bstep (se 1 (by rfl) ⟨2322548, by rfl⟩ : syracuseStep 3096731 = 4645097) B4645097
theorem B12271931 : Blo 642303 12271931 := bstep (se 1 (by rfl) ⟨9203948, by rfl⟩ : syracuseStep 12271931 = 18407897) B18407897
theorem B20070989 : Blo 642303 20070989 := bstep (se 3 (by rfl) ⟨3763310, by rfl⟩ : syracuseStep 20070989 = 7526621) B7526621
theorem B3261383 : Blo 642303 3261383 := bstep (se 1 (by rfl) ⟨2446037, by rfl⟩ : syracuseStep 3261383 = 4892075) B4892075
theorem B7324991 : Blo 642303 7324991 := bstep (se 1 (by rfl) ⟨5493743, by rfl⟩ : syracuseStep 7324991 = 10987487) B10987487
theorem B969119 : Blo 642303 969119 := bstep (se 1 (by rfl) ⟨726839, by rfl⟩ : syracuseStep 969119 = 1453679) B1453679
theorem B969215 : Blo 642303 969215 := bstep (se 1 (by rfl) ⟨726911, by rfl⟩ : syracuseStep 969215 = 1453823) B1453823
theorem B642543 : Blo 642303 642543 := bstep (se 1 (by rfl) ⟨481907, by rfl⟩ : syracuseStep 642543 = 963815) B963815
theorem B642591 : Blo 642303 642591 := bstep (se 1 (by rfl) ⟨481943, by rfl⟩ : syracuseStep 642591 = 963887) B963887
theorem B642815 : Blo 642303 642815 := bstep (se 1 (by rfl) ⟨482111, by rfl⟩ : syracuseStep 642815 = 964223) B964223
theorem B645119 : Blo 642303 645119 := bstep (se 1 (by rfl) ⟨483839, by rfl⟩ : syracuseStep 645119 = 967679) B967679
theorem B3136295 : Blo 642303 3136295 := bstep (se 1 (by rfl) ⟨2352221, by rfl⟩ : syracuseStep 3136295 = 4704443) B4704443
theorem B3268511 : Blo 642303 3268511 := bstep (se 1 (by rfl) ⟨2451383, by rfl⟩ : syracuseStep 3268511 = 4902767) B4902767
theorem B89121343 : Blo 642303 89121343 := bstep (se 1 (by rfl) ⟨66841007, by rfl⟩ : syracuseStep 89121343 = 133682015) B133682015
theorem B2452295 : Blo 642303 2452295 := bstep (se 1 (by rfl) ⟨1839221, by rfl⟩ : syracuseStep 2452295 = 3678443) B3678443
theorem B1962047 : Blo 642303 1962047 := bstep (se 1 (by rfl) ⟨1471535, by rfl⟩ : syracuseStep 1962047 = 2943071) B2943071
theorem B687175973 : Blo 642303 687175973 := bstep (se 4 (by rfl) ⟨64422747, by rfl⟩ : syracuseStep 687175973 = 128845495) B128845495
theorem B1374889 : Blo 642303 1374889 := bstep (se 2 (by rfl) ⟨515583, by rfl⟩ : syracuseStep 1374889 = 1031167) B1031167
theorem B2064487 : Blo 642303 2064487 := bstep (se 1 (by rfl) ⟨1548365, by rfl⟩ : syracuseStep 2064487 = 3096731) B3096731
theorem B4883327 : Blo 642303 4883327 := bstep (se 1 (by rfl) ⟨3662495, by rfl⟩ : syracuseStep 4883327 = 7324991) B7324991
theorem B1446227 : Blo 642303 1446227 := bstep (se 1 (by rfl) ⟨1084670, by rfl⟩ : syracuseStep 1446227 = 2169341) B2169341
theorem B726655 : Blo 642303 726655 := bstep (se 1 (by rfl) ⟨544991, by rfl⟩ : syracuseStep 726655 = 1089983) B1089983
theorem B3479435 : Blo 642303 3479435 := bstep (se 1 (by rfl) ⟨2609576, by rfl⟩ : syracuseStep 3479435 = 5219153) B5219153
theorem B9903799 : Blo 642303 9903799 := bstep (se 1 (by rfl) ⟨7427849, by rfl⟩ : syracuseStep 9903799 = 14855699) B14855699
theorem B13380659 : Blo 642303 13380659 := bstep (se 1 (by rfl) ⟨10035494, by rfl⟩ : syracuseStep 13380659 = 20070989) B20070989
theorem B1223839 : Blo 642303 1223839 := bstep (se 1 (by rfl) ⟨917879, by rfl⟩ : syracuseStep 1223839 = 1835759) B1835759
theorem B2174255 : Blo 642303 2174255 := bstep (se 1 (by rfl) ⟨1630691, by rfl⟩ : syracuseStep 2174255 = 3261383) B3261383
theorem B118828457 : Blo 642303 118828457 := bstep (se 2 (by rfl) ⟨44560671, by rfl⟩ : syracuseStep 118828457 = 89121343) B89121343
theorem B964859 : Blo 642303 964859 := bstep (se 1 (by rfl) ⟨723644, by rfl⟩ : syracuseStep 964859 = 1447289) B1447289
theorem B965087 : Blo 642303 965087 := bstep (se 1 (by rfl) ⟨723815, by rfl⟩ : syracuseStep 965087 = 1447631) B1447631
theorem B2179007 : Blo 642303 2179007 := bstep (se 1 (by rfl) ⟨1634255, by rfl⟩ : syracuseStep 2179007 = 3268511) B3268511
theorem B967259 : Blo 642303 967259 := bstep (se 1 (by rfl) ⟨725444, by rfl⟩ : syracuseStep 967259 = 1450889) B1450889
theorem B967721 : Blo 642303 967721 := bstep (se 2 (by rfl) ⟨362895, by rfl⟩ : syracuseStep 967721 = 725791) B725791
theorem B967775 : Blo 642303 967775 := bstep (se 1 (by rfl) ⟨725831, by rfl⟩ : syracuseStep 967775 = 1451663) B1451663
theorem B968171 : Blo 642303 968171 := bstep (se 1 (by rfl) ⟨726128, by rfl⟩ : syracuseStep 968171 = 1452257) B1452257
theorem B968795 : Blo 642303 968795 := bstep (se 1 (by rfl) ⟨726596, by rfl⟩ : syracuseStep 968795 = 1453193) B1453193
theorem B968879 : Blo 642303 968879 := bstep (se 1 (by rfl) ⟨726659, by rfl⟩ : syracuseStep 968879 = 1453319) B1453319
theorem B4901309 : Blo 642303 4901309 := bstep (se 3 (by rfl) ⟨918995, by rfl⟩ : syracuseStep 4901309 = 1837991) B1837991
theorem B5229527 : Blo 642303 5229527 := bstep (se 1 (by rfl) ⟨3922145, by rfl⟩ : syracuseStep 5229527 = 7844291) B7844291
theorem B458117315 : Blo 642303 458117315 := bstep (se 1 (by rfl) ⟨343587986, by rfl⟩ : syracuseStep 458117315 = 687175973) B687175973
theorem B1627361 : Blo 642303 1627361 := bstep (se 2 (by rfl) ⟨610260, by rfl⟩ : syracuseStep 1627361 = 1220521) B1220521
theorem B8181287 : Blo 642303 8181287 := bstep (se 1 (by rfl) ⟨6135965, by rfl⟩ : syracuseStep 8181287 = 12271931) B12271931
theorem B646079 : Blo 642303 646079 := bstep (se 1 (by rfl) ⟨484559, by rfl⟩ : syracuseStep 646079 = 969119) B969119
theorem B646143 : Blo 642303 646143 := bstep (se 1 (by rfl) ⟨484607, by rfl⟩ : syracuseStep 646143 = 969215) B969215
theorem B2450807 : Blo 642303 2450807 := bstep (se 1 (by rfl) ⟨1838105, by rfl⟩ : syracuseStep 2450807 = 3676211) B3676211
theorem B2090863 : Blo 642303 2090863 := bstep (se 1 (by rfl) ⟨1568147, by rfl⟩ : syracuseStep 2090863 = 3136295) B3136295
theorem B12349853 : Blo 642303 12349853 := bstep (se 3 (by rfl) ⟨2315597, by rfl⟩ : syracuseStep 12349853 = 4631195) B4631195
theorem B2453921 : Blo 642303 2453921 := bstep (se 2 (by rfl) ⟨920220, by rfl⟩ : syracuseStep 2453921 = 1840441) B1840441
theorem B1634863 : Blo 642303 1634863 := bstep (se 1 (by rfl) ⟨1226147, by rfl⟩ : syracuseStep 1634863 = 2452295) B2452295
theorem B1308031 : Blo 642303 1308031 := bstep (se 1 (by rfl) ⟨981023, by rfl⟩ : syracuseStep 1308031 = 1962047) B1962047
theorem B1833185 : Blo 642303 1833185 := bstep (se 2 (by rfl) ⟨687444, by rfl⟩ : syracuseStep 1833185 = 1374889) B1374889
theorem B2752649 : Blo 642303 2752649 := bstep (se 2 (by rfl) ⟨1032243, by rfl⟩ : syracuseStep 2752649 = 2064487) B2064487
theorem B1084907 : Blo 642303 1084907 := bstep (se 1 (by rfl) ⟨813680, by rfl⟩ : syracuseStep 1084907 = 1627361) B1627361
theorem B8920439 : Blo 642303 8920439 := bstep (se 1 (by rfl) ⟨6690329, by rfl⟩ : syracuseStep 8920439 = 13380659) B13380659
theorem B1449503 : Blo 642303 1449503 := bstep (se 1 (by rfl) ⟨1087127, by rfl⟩ : syracuseStep 1449503 = 2174255) B2174255
theorem B8233235 : Blo 642303 8233235 := bstep (se 1 (by rfl) ⟨6174926, by rfl⟩ : syracuseStep 8233235 = 12349853) B12349853
theorem B1222123 : Blo 642303 1222123 := bstep (se 1 (by rfl) ⟨916592, by rfl⟩ : syracuseStep 1222123 = 1833185) B1833185
theorem B11151269 : Blo 642303 11151269 := bstep (se 4 (by rfl) ⟨1045431, by rfl⟩ : syracuseStep 11151269 = 2090863) B2090863
theorem B1452671 : Blo 642303 1452671 := bstep (se 1 (by rfl) ⟨1089503, by rfl⟩ : syracuseStep 1452671 = 2179007) B2179007
theorem B3255551 : Blo 642303 3255551 := bstep (se 1 (by rfl) ⟨2441663, by rfl⟩ : syracuseStep 3255551 = 4883327) B4883327
theorem B305411543 : Blo 642303 305411543 := bstep (se 1 (by rfl) ⟨229058657, by rfl⟩ : syracuseStep 305411543 = 458117315) B458117315
theorem B964151 : Blo 642303 964151 := bstep (se 1 (by rfl) ⟨723113, by rfl⟩ : syracuseStep 964151 = 1446227) B1446227
theorem B5454191 : Blo 642303 5454191 := bstep (se 1 (by rfl) ⟨4090643, by rfl⟩ : syracuseStep 5454191 = 8181287) B8181287
theorem B2179817 : Blo 642303 2179817 := bstep (se 2 (by rfl) ⟨817431, by rfl⟩ : syracuseStep 2179817 = 1634863) B1634863
theorem B968873 : Blo 642303 968873 := bstep (se 2 (by rfl) ⟨363327, by rfl⟩ : syracuseStep 968873 = 726655) B726655
theorem B79218971 : Blo 642303 79218971 := bstep (se 1 (by rfl) ⟨59414228, by rfl⟩ : syracuseStep 79218971 = 118828457) B118828457
theorem B13945405 : Blo 642303 13945405 := bstep (se 3 (by rfl) ⟨2614763, by rfl⟩ : syracuseStep 13945405 = 5229527) B5229527
theorem B643239 : Blo 642303 643239 := bstep (se 1 (by rfl) ⟨482429, by rfl⟩ : syracuseStep 643239 = 964859) B964859
theorem B643391 : Blo 642303 643391 := bstep (se 1 (by rfl) ⟨482543, by rfl⟩ : syracuseStep 643391 = 965087) B965087
theorem B644839 : Blo 642303 644839 := bstep (se 1 (by rfl) ⟨483629, by rfl⟩ : syracuseStep 644839 = 967259) B967259
theorem B645147 : Blo 642303 645147 := bstep (se 1 (by rfl) ⟨483860, by rfl⟩ : syracuseStep 645147 = 967721) B967721
theorem B645183 : Blo 642303 645183 := bstep (se 1 (by rfl) ⟨483887, by rfl⟩ : syracuseStep 645183 = 967775) B967775
theorem B645447 : Blo 642303 645447 := bstep (se 1 (by rfl) ⟨484085, by rfl⟩ : syracuseStep 645447 = 968171) B968171
theorem B645863 : Blo 642303 645863 := bstep (se 1 (by rfl) ⟨484397, by rfl⟩ : syracuseStep 645863 = 968795) B968795
theorem B645919 : Blo 642303 645919 := bstep (se 1 (by rfl) ⟨484439, by rfl⟩ : syracuseStep 645919 = 968879) B968879
theorem B3267539 : Blo 642303 3267539 := bstep (se 1 (by rfl) ⟨2450654, by rfl⟩ : syracuseStep 3267539 = 4901309) B4901309
theorem B2319623 : Blo 642303 2319623 := bstep (se 1 (by rfl) ⟨1739717, by rfl⟩ : syracuseStep 2319623 = 3479435) B3479435
theorem B1631785 : Blo 642303 1631785 := bstep (se 2 (by rfl) ⟨611919, by rfl⟩ : syracuseStep 1631785 = 1223839) B1223839
theorem B1633871 : Blo 642303 1633871 := bstep (se 1 (by rfl) ⟨1225403, by rfl⟩ : syracuseStep 1633871 = 2450807) B2450807
theorem B6976165 : Blo 642303 6976165 := bstep (se 4 (by rfl) ⟨654015, by rfl⟩ : syracuseStep 6976165 = 1308031) B1308031
theorem B1635947 : Blo 642303 1635947 := bstep (se 1 (by rfl) ⟨1226960, by rfl⟩ : syracuseStep 1635947 = 2453921) B2453921
theorem B13205065 : Blo 642303 13205065 := bstep (se 2 (by rfl) ⟨4951899, by rfl⟩ : syracuseStep 13205065 = 9903799) B9903799
theorem B1835099 : Blo 642303 1835099 := bstep (se 1 (by rfl) ⟨1376324, by rfl⟩ : syracuseStep 1835099 = 2752649) B2752649
theorem B723271 : Blo 642303 723271 := bstep (se 1 (by rfl) ⟨542453, by rfl⟩ : syracuseStep 723271 = 1084907) B1084907
theorem B1546415 : Blo 642303 1546415 := bstep (se 1 (by rfl) ⟨1159811, by rfl⟩ : syracuseStep 1546415 = 2319623) B2319623
theorem B2170367 : Blo 642303 2170367 := bstep (se 1 (by rfl) ⟨1627775, by rfl⟩ : syracuseStep 2170367 = 3255551) B3255551
theorem B1089247 : Blo 642303 1089247 := bstep (se 1 (by rfl) ⟨816935, by rfl⟩ : syracuseStep 1089247 = 1633871) B1633871
theorem B1090631 : Blo 642303 1090631 := bstep (se 1 (by rfl) ⟨817973, by rfl⟩ : syracuseStep 1090631 = 1635947) B1635947
theorem B17606753 : Blo 642303 17606753 := bstep (se 2 (by rfl) ⟨6602532, by rfl⟩ : syracuseStep 17606753 = 13205065) B13205065
theorem B1453211 : Blo 642303 1453211 := bstep (se 1 (by rfl) ⟨1089908, by rfl⟩ : syracuseStep 1453211 = 2179817) B2179817
theorem B2175713 : Blo 642303 2175713 := bstep (se 2 (by rfl) ⟨815892, by rfl⟩ : syracuseStep 2175713 = 1631785) B1631785
theorem B18593873 : Blo 642303 18593873 := bstep (se 2 (by rfl) ⟨6972702, by rfl⟩ : syracuseStep 18593873 = 13945405) B13945405
theorem B2178359 : Blo 642303 2178359 := bstep (se 1 (by rfl) ⟨1633769, by rfl⟩ : syracuseStep 2178359 = 3267539) B3267539
theorem B5946959 : Blo 642303 5946959 := bstep (se 1 (by rfl) ⟨4460219, by rfl⟩ : syracuseStep 5946959 = 8920439) B8920439
theorem B966335 : Blo 642303 966335 := bstep (se 1 (by rfl) ⟨724751, by rfl⟩ : syracuseStep 966335 = 1449503) B1449503
theorem B5488823 : Blo 642303 5488823 := bstep (se 1 (by rfl) ⟨4116617, by rfl⟩ : syracuseStep 5488823 = 8233235) B8233235
theorem B968447 : Blo 642303 968447 := bstep (se 1 (by rfl) ⟨726335, by rfl⟩ : syracuseStep 968447 = 1452671) B1452671
theorem B203607695 : Blo 642303 203607695 := bstep (se 1 (by rfl) ⟨152705771, by rfl⟩ : syracuseStep 203607695 = 305411543) B305411543
theorem B642767 : Blo 642303 642767 := bstep (se 1 (by rfl) ⟨482075, by rfl⟩ : syracuseStep 642767 = 964151) B964151
theorem B645915 : Blo 642303 645915 := bstep (se 1 (by rfl) ⟨484436, by rfl⟩ : syracuseStep 645915 = 968873) B968873
theorem B52812647 : Blo 642303 52812647 := bstep (se 1 (by rfl) ⟨39609485, by rfl⟩ : syracuseStep 52812647 = 79218971) B79218971
theorem B1629497 : Blo 642303 1629497 := bstep (se 2 (by rfl) ⟨611061, by rfl⟩ : syracuseStep 1629497 = 1222123) B1222123
theorem B9301553 : Blo 642303 9301553 := bstep (se 2 (by rfl) ⟨3488082, by rfl⟩ : syracuseStep 9301553 = 6976165) B6976165
theorem B7434179 : Blo 642303 7434179 := bstep (se 1 (by rfl) ⟨5575634, by rfl⟩ : syracuseStep 7434179 = 11151269) B11151269
theorem B3636127 : Blo 642303 3636127 := bstep (se 1 (by rfl) ⟨2727095, by rfl⟩ : syracuseStep 3636127 = 5454191) B5454191
theorem B1086331 : Blo 642303 1086331 := bstep (se 1 (by rfl) ⟨814748, by rfl⟩ : syracuseStep 1086331 = 1629497) B1629497
theorem B1446911 : Blo 642303 1446911 := bstep (se 1 (by rfl) ⟨1085183, by rfl⟩ : syracuseStep 1446911 = 2170367) B2170367
theorem B727087 : Blo 642303 727087 := bstep (se 1 (by rfl) ⟨545315, by rfl⟩ : syracuseStep 727087 = 1090631) B1090631
theorem B11737835 : Blo 642303 11737835 := bstep (se 1 (by rfl) ⟨8803376, by rfl⟩ : syracuseStep 11737835 = 17606753) B17606753
theorem B6201035 : Blo 642303 6201035 := bstep (se 1 (by rfl) ⟨4650776, by rfl⟩ : syracuseStep 6201035 = 9301553) B9301553
theorem B4956119 : Blo 642303 4956119 := bstep (se 1 (by rfl) ⟨3717089, by rfl⟩ : syracuseStep 4956119 = 7434179) B7434179
theorem B1450475 : Blo 642303 1450475 := bstep (se 1 (by rfl) ⟨1087856, by rfl⟩ : syracuseStep 1450475 = 2175713) B2175713
theorem B12395915 : Blo 642303 12395915 := bstep (se 1 (by rfl) ⟨9296936, by rfl⟩ : syracuseStep 12395915 = 18593873) B18593873
theorem B1452239 : Blo 642303 1452239 := bstep (se 1 (by rfl) ⟨1089179, by rfl⟩ : syracuseStep 1452239 = 2178359) B2178359
theorem B1452329 : Blo 642303 1452329 := bstep (se 2 (by rfl) ⟨544623, by rfl⟩ : syracuseStep 1452329 = 1089247) B1089247
theorem B1223399 : Blo 642303 1223399 := bstep (se 1 (by rfl) ⟨917549, by rfl⟩ : syracuseStep 1223399 = 1835099) B1835099
theorem B135738463 : Blo 642303 135738463 := bstep (se 1 (by rfl) ⟨101803847, by rfl⟩ : syracuseStep 135738463 = 203607695) B203607695
theorem B964361 : Blo 642303 964361 := bstep (se 2 (by rfl) ⟨361635, by rfl⟩ : syracuseStep 964361 = 723271) B723271
theorem B1030943 : Blo 642303 1030943 := bstep (se 1 (by rfl) ⟨773207, by rfl⟩ : syracuseStep 1030943 = 1546415) B1546415
theorem B35208431 : Blo 642303 35208431 := bstep (se 1 (by rfl) ⟨26406323, by rfl⟩ : syracuseStep 35208431 = 52812647) B52812647
theorem B968807 : Blo 642303 968807 := bstep (se 1 (by rfl) ⟨726605, by rfl⟩ : syracuseStep 968807 = 1453211) B1453211
theorem B644223 : Blo 642303 644223 := bstep (se 1 (by rfl) ⟨483167, by rfl⟩ : syracuseStep 644223 = 966335) B966335
theorem B3659215 : Blo 642303 3659215 := bstep (se 1 (by rfl) ⟨2744411, by rfl⟩ : syracuseStep 3659215 = 5488823) B5488823
theorem B645631 : Blo 642303 645631 := bstep (se 1 (by rfl) ⟨484223, by rfl⟩ : syracuseStep 645631 = 968447) B968447
theorem B4848169 : Blo 642303 4848169 := bstep (se 2 (by rfl) ⟨1818063, by rfl⟩ : syracuseStep 4848169 = 3636127) B3636127
theorem B3964639 : Blo 642303 3964639 := bstep (se 1 (by rfl) ⟨2973479, by rfl⟩ : syracuseStep 3964639 = 5946959) B5946959
theorem B4134023 : Blo 642303 4134023 := bstep (se 1 (by rfl) ⟨3100517, by rfl⟩ : syracuseStep 4134023 = 6201035) B6201035
theorem B8263943 : Blo 642303 8263943 := bstep (se 1 (by rfl) ⟨6197957, by rfl⟩ : syracuseStep 8263943 = 12395915) B12395915
theorem B1448441 : Blo 642303 1448441 := bstep (se 2 (by rfl) ⟨543165, by rfl⟩ : syracuseStep 1448441 = 1086331) B1086331
theorem B180984617 : Blo 642303 180984617 := bstep (se 2 (by rfl) ⟨67869231, by rfl⟩ : syracuseStep 180984617 = 135738463) B135738463
theorem B6464225 : Blo 642303 6464225 := bstep (se 2 (by rfl) ⟨2424084, by rfl⟩ : syracuseStep 6464225 = 4848169) B4848169
theorem B23472287 : Blo 642303 23472287 := bstep (se 1 (by rfl) ⟨17604215, by rfl⟩ : syracuseStep 23472287 = 35208431) B35208431
theorem B5286185 : Blo 642303 5286185 := bstep (se 2 (by rfl) ⟨1982319, by rfl⟩ : syracuseStep 5286185 = 3964639) B3964639
theorem B964607 : Blo 642303 964607 := bstep (se 1 (by rfl) ⟨723455, by rfl⟩ : syracuseStep 964607 = 1446911) B1446911
theorem B966983 : Blo 642303 966983 := bstep (se 1 (by rfl) ⟨725237, by rfl⟩ : syracuseStep 966983 = 1450475) B1450475
theorem B968159 : Blo 642303 968159 := bstep (se 1 (by rfl) ⟨726119, by rfl⟩ : syracuseStep 968159 = 1452239) B1452239
theorem B968219 : Blo 642303 968219 := bstep (se 1 (by rfl) ⟨726164, by rfl⟩ : syracuseStep 968219 = 1452329) B1452329
theorem B969449 : Blo 642303 969449 := bstep (se 2 (by rfl) ⟨363543, by rfl⟩ : syracuseStep 969449 = 727087) B727087
theorem B642907 : Blo 642303 642907 := bstep (se 1 (by rfl) ⟨482180, by rfl⟩ : syracuseStep 642907 = 964361) B964361
theorem B645871 : Blo 642303 645871 := bstep (se 1 (by rfl) ⟨484403, by rfl⟩ : syracuseStep 645871 = 968807) B968807
theorem B7825223 : Blo 642303 7825223 := bstep (se 1 (by rfl) ⟨5868917, by rfl⟩ : syracuseStep 7825223 = 11737835) B11737835
theorem B3304079 : Blo 642303 3304079 := bstep (se 1 (by rfl) ⟨2478059, by rfl⟩ : syracuseStep 3304079 = 4956119) B4956119
theorem B815599 : Blo 642303 815599 := bstep (se 1 (by rfl) ⟨611699, by rfl⟩ : syracuseStep 815599 = 1223399) B1223399
theorem B4878953 : Blo 642303 4878953 := bstep (se 2 (by rfl) ⟨1829607, by rfl⟩ : syracuseStep 4878953 = 3659215) B3659215
theorem B687295 : Blo 642303 687295 := bstep (se 1 (by rfl) ⟨515471, by rfl⟩ : syracuseStep 687295 = 1030943) B1030943
theorem B17237933 : Blo 642303 17237933 := bstep (se 3 (by rfl) ⟨3232112, by rfl⟩ : syracuseStep 17237933 = 6464225) B6464225
theorem B2756015 : Blo 642303 2756015 := bstep (se 1 (by rfl) ⟨2067011, by rfl⟩ : syracuseStep 2756015 = 4134023) B4134023
theorem B5509295 : Blo 642303 5509295 := bstep (se 1 (by rfl) ⟨4131971, by rfl⟩ : syracuseStep 5509295 = 8263943) B8263943
theorem B120656411 : Blo 642303 120656411 := bstep (se 1 (by rfl) ⟨90492308, by rfl⟩ : syracuseStep 120656411 = 180984617) B180984617
theorem B1087465 : Blo 642303 1087465 := bstep (se 2 (by rfl) ⟨407799, by rfl⟩ : syracuseStep 1087465 = 815599) B815599
theorem B5216815 : Blo 642303 5216815 := bstep (se 1 (by rfl) ⟨3912611, by rfl⟩ : syracuseStep 5216815 = 7825223) B7825223
theorem B2202719 : Blo 642303 2202719 := bstep (se 1 (by rfl) ⟨1652039, by rfl⟩ : syracuseStep 2202719 = 3304079) B3304079
theorem B3252635 : Blo 642303 3252635 := bstep (se 1 (by rfl) ⟨2439476, by rfl⟩ : syracuseStep 3252635 = 4878953) B4878953
theorem B965627 : Blo 642303 965627 := bstep (se 1 (by rfl) ⟨724220, by rfl⟩ : syracuseStep 965627 = 1448441) B1448441
theorem B15648191 : Blo 642303 15648191 := bstep (se 1 (by rfl) ⟨11736143, by rfl⟩ : syracuseStep 15648191 = 23472287) B23472287
theorem B3524123 : Blo 642303 3524123 := bstep (se 1 (by rfl) ⟨2643092, by rfl⟩ : syracuseStep 3524123 = 5286185) B5286185
theorem B643071 : Blo 642303 643071 := bstep (se 1 (by rfl) ⟨482303, by rfl⟩ : syracuseStep 643071 = 964607) B964607
theorem B644655 : Blo 642303 644655 := bstep (se 1 (by rfl) ⟨483491, by rfl⟩ : syracuseStep 644655 = 966983) B966983
theorem B645439 : Blo 642303 645439 := bstep (se 1 (by rfl) ⟨484079, by rfl⟩ : syracuseStep 645439 = 968159) B968159
theorem B645479 : Blo 642303 645479 := bstep (se 1 (by rfl) ⟨484109, by rfl⟩ : syracuseStep 645479 = 968219) B968219
theorem B646299 : Blo 642303 646299 := bstep (se 1 (by rfl) ⟨484724, by rfl⟩ : syracuseStep 646299 = 969449) B969449
theorem B3665573 : Blo 642303 3665573 := bstep (se 4 (by rfl) ⟨343647, by rfl⟩ : syracuseStep 3665573 = 687295) B687295
theorem B1837343 : Blo 642303 1837343 := bstep (se 1 (by rfl) ⟨1378007, by rfl⟩ : syracuseStep 1837343 = 2756015) B2756015
theorem B3672863 : Blo 642303 3672863 := bstep (se 1 (by rfl) ⟨2754647, by rfl⟩ : syracuseStep 3672863 = 5509295) B5509295
theorem B2168423 : Blo 642303 2168423 := bstep (se 1 (by rfl) ⟨1626317, by rfl⟩ : syracuseStep 2168423 = 3252635) B3252635
theorem B1449953 : Blo 642303 1449953 := bstep (se 2 (by rfl) ⟨543732, by rfl⟩ : syracuseStep 1449953 = 1087465) B1087465
theorem B5873917 : Blo 642303 5873917 := bstep (se 3 (by rfl) ⟨1101359, by rfl⟩ : syracuseStep 5873917 = 2202719) B2202719
theorem B6955753 : Blo 642303 6955753 := bstep (se 2 (by rfl) ⟨2608407, by rfl⟩ : syracuseStep 6955753 = 5216815) B5216815
theorem B10432127 : Blo 642303 10432127 := bstep (se 1 (by rfl) ⟨7824095, by rfl⟩ : syracuseStep 10432127 = 15648191) B15648191
theorem B2443715 : Blo 642303 2443715 := bstep (se 1 (by rfl) ⟨1832786, by rfl⟩ : syracuseStep 2443715 = 3665573) B3665573
theorem B643751 : Blo 642303 643751 := bstep (se 1 (by rfl) ⟨482813, by rfl⟩ : syracuseStep 643751 = 965627) B965627
theorem B2349415 : Blo 642303 2349415 := bstep (se 1 (by rfl) ⟨1762061, by rfl⟩ : syracuseStep 2349415 = 3524123) B3524123
theorem B11491955 : Blo 642303 11491955 := bstep (se 1 (by rfl) ⟨8618966, by rfl⟩ : syracuseStep 11491955 = 17237933) B17237933
theorem B80437607 : Blo 642303 80437607 := bstep (se 1 (by rfl) ⟨60328205, by rfl⟩ : syracuseStep 80437607 = 120656411) B120656411
theorem B7831889 : Blo 642303 7831889 := bstep (se 2 (by rfl) ⟨2936958, by rfl⟩ : syracuseStep 7831889 = 5873917) B5873917
theorem B9274337 : Blo 642303 9274337 := bstep (se 2 (by rfl) ⟨3477876, by rfl⟩ : syracuseStep 9274337 = 6955753) B6955753
theorem B1445615 : Blo 642303 1445615 := bstep (se 1 (by rfl) ⟨1084211, by rfl⟩ : syracuseStep 1445615 = 2168423) B2168423
theorem B6954751 : Blo 642303 6954751 := bstep (se 1 (by rfl) ⟨5216063, by rfl⟩ : syracuseStep 6954751 = 10432127) B10432127
theorem B1224895 : Blo 642303 1224895 := bstep (se 1 (by rfl) ⟨918671, by rfl⟩ : syracuseStep 1224895 = 1837343) B1837343
theorem B12530213 : Blo 642303 12530213 := bstep (se 4 (by rfl) ⟨1174707, by rfl⟩ : syracuseStep 12530213 = 2349415) B2349415
theorem B966635 : Blo 642303 966635 := bstep (se 1 (by rfl) ⟨724976, by rfl⟩ : syracuseStep 966635 = 1449953) B1449953
theorem B53625071 : Blo 642303 53625071 := bstep (se 1 (by rfl) ⟨40218803, by rfl⟩ : syracuseStep 53625071 = 80437607) B80437607
theorem B1629143 : Blo 642303 1629143 := bstep (se 1 (by rfl) ⟨1221857, by rfl⟩ : syracuseStep 1629143 = 2443715) B2443715
theorem B2448575 : Blo 642303 2448575 := bstep (se 1 (by rfl) ⟨1836431, by rfl⟩ : syracuseStep 2448575 = 3672863) B3672863
theorem B7661303 : Blo 642303 7661303 := bstep (se 1 (by rfl) ⟨5745977, by rfl⟩ : syracuseStep 7661303 = 11491955) B11491955
theorem B35750047 : Blo 642303 35750047 := bstep (se 1 (by rfl) ⟨26812535, by rfl⟩ : syracuseStep 35750047 = 53625071) B53625071
theorem B1086095 : Blo 642303 1086095 := bstep (se 1 (by rfl) ⟨814571, by rfl⟩ : syracuseStep 1086095 = 1629143) B1629143
theorem B5221259 : Blo 642303 5221259 := bstep (se 1 (by rfl) ⟨3915944, by rfl⟩ : syracuseStep 5221259 = 7831889) B7831889
theorem B963743 : Blo 642303 963743 := bstep (se 1 (by rfl) ⟨722807, by rfl⟩ : syracuseStep 963743 = 1445615) B1445615
theorem B644423 : Blo 642303 644423 := bstep (se 1 (by rfl) ⟨483317, by rfl⟩ : syracuseStep 644423 = 966635) B966635
theorem B6182891 : Blo 642303 6182891 := bstep (se 1 (by rfl) ⟨4637168, by rfl⟩ : syracuseStep 6182891 = 9274337) B9274337
theorem B1632383 : Blo 642303 1632383 := bstep (se 1 (by rfl) ⟨1224287, by rfl⟩ : syracuseStep 1632383 = 2448575) B2448575
theorem B1633193 : Blo 642303 1633193 := bstep (se 2 (by rfl) ⟨612447, by rfl⟩ : syracuseStep 1633193 = 1224895) B1224895
theorem B5107535 : Blo 642303 5107535 := bstep (se 1 (by rfl) ⟨3830651, by rfl⟩ : syracuseStep 5107535 = 7661303) B7661303
theorem B8353475 : Blo 642303 8353475 := bstep (se 1 (by rfl) ⟨6265106, by rfl⟩ : syracuseStep 8353475 = 12530213) B12530213
theorem B9273001 : Blo 642303 9273001 := bstep (se 2 (by rfl) ⟨3477375, by rfl⟩ : syracuseStep 9273001 = 6954751) B6954751
theorem B724063 : Blo 642303 724063 := bstep (se 1 (by rfl) ⟨543047, by rfl⟩ : syracuseStep 724063 = 1086095) B1086095
theorem B1088255 : Blo 642303 1088255 := bstep (se 1 (by rfl) ⟨816191, by rfl⟩ : syracuseStep 1088255 = 1632383) B1632383
theorem B3480839 : Blo 642303 3480839 := bstep (se 1 (by rfl) ⟨2610629, by rfl⟩ : syracuseStep 3480839 = 5221259) B5221259
theorem B1088795 : Blo 642303 1088795 := bstep (se 1 (by rfl) ⟨816596, by rfl⟩ : syracuseStep 1088795 = 1633193) B1633193
theorem B12364001 : Blo 642303 12364001 := bstep (se 2 (by rfl) ⟨4636500, by rfl⟩ : syracuseStep 12364001 = 9273001) B9273001
theorem B642495 : Blo 642303 642495 := bstep (se 1 (by rfl) ⟨481871, by rfl⟩ : syracuseStep 642495 = 963743) B963743
theorem B47666729 : Blo 642303 47666729 := bstep (se 2 (by rfl) ⟨17875023, by rfl⟩ : syracuseStep 47666729 = 35750047) B35750047
theorem B4121927 : Blo 642303 4121927 := bstep (se 1 (by rfl) ⟨3091445, by rfl⟩ : syracuseStep 4121927 = 6182891) B6182891
theorem B3405023 : Blo 642303 3405023 := bstep (se 1 (by rfl) ⟨2553767, by rfl⟩ : syracuseStep 3405023 = 5107535) B5107535
theorem B5568983 : Blo 642303 5568983 := bstep (se 1 (by rfl) ⟨4176737, by rfl⟩ : syracuseStep 5568983 = 8353475) B8353475
theorem B127111277 : Blo 642303 127111277 := bstep (se 3 (by rfl) ⟨23833364, by rfl⟩ : syracuseStep 127111277 = 47666729) B47666729
theorem B725503 : Blo 642303 725503 := bstep (se 1 (by rfl) ⟨544127, by rfl⟩ : syracuseStep 725503 = 1088255) B1088255
theorem B725863 : Blo 642303 725863 := bstep (se 1 (by rfl) ⟨544397, by rfl⟩ : syracuseStep 725863 = 1088795) B1088795
theorem B2270015 : Blo 642303 2270015 := bstep (se 1 (by rfl) ⟨1702511, by rfl⟩ : syracuseStep 2270015 = 3405023) B3405023
theorem B3712655 : Blo 642303 3712655 := bstep (se 1 (by rfl) ⟨2784491, by rfl⟩ : syracuseStep 3712655 = 5568983) B5568983
theorem B965417 : Blo 642303 965417 := bstep (se 2 (by rfl) ⟨362031, by rfl⟩ : syracuseStep 965417 = 724063) B724063
theorem B8242667 : Blo 642303 8242667 := bstep (se 1 (by rfl) ⟨6182000, by rfl⟩ : syracuseStep 8242667 = 12364001) B12364001
theorem B2320559 : Blo 642303 2320559 := bstep (se 1 (by rfl) ⟨1740419, by rfl⟩ : syracuseStep 2320559 = 3480839) B3480839
theorem B2747951 : Blo 642303 2747951 := bstep (se 1 (by rfl) ⟨2060963, by rfl⟩ : syracuseStep 2747951 = 4121927) B4121927
theorem B84740851 : Blo 642303 84740851 := bstep (se 1 (by rfl) ⟨63555638, by rfl⟩ : syracuseStep 84740851 = 127111277) B127111277
theorem B9900413 : Blo 642303 9900413 := bstep (se 3 (by rfl) ⟨1856327, by rfl⟩ : syracuseStep 9900413 = 3712655) B3712655
theorem B1513343 : Blo 642303 1513343 := bstep (se 1 (by rfl) ⟨1135007, by rfl⟩ : syracuseStep 1513343 = 2270015) B2270015
theorem B1547039 : Blo 642303 1547039 := bstep (se 1 (by rfl) ⟨1160279, by rfl⟩ : syracuseStep 1547039 = 2320559) B2320559
theorem B967337 : Blo 642303 967337 := bstep (se 2 (by rfl) ⟨362751, by rfl⟩ : syracuseStep 967337 = 725503) B725503
theorem B967817 : Blo 642303 967817 := bstep (se 2 (by rfl) ⟨362931, by rfl⟩ : syracuseStep 967817 = 725863) B725863
theorem B643611 : Blo 642303 643611 := bstep (se 1 (by rfl) ⟨482708, by rfl⟩ : syracuseStep 643611 = 965417) B965417
theorem B5495111 : Blo 642303 5495111 := bstep (se 1 (by rfl) ⟨4121333, by rfl⟩ : syracuseStep 5495111 = 8242667) B8242667
theorem B1831967 : Blo 642303 1831967 := bstep (se 1 (by rfl) ⟨1373975, by rfl⟩ : syracuseStep 1831967 = 2747951) B2747951
theorem B112987801 : Blo 642303 112987801 := bstep (se 2 (by rfl) ⟨42370425, by rfl⟩ : syracuseStep 112987801 = 84740851) B84740851
theorem B4035581 : Blo 642303 4035581 := bstep (se 3 (by rfl) ⟨756671, by rfl⟩ : syracuseStep 4035581 = 1513343) B1513343
theorem B1221311 : Blo 642303 1221311 := bstep (se 1 (by rfl) ⟨915983, by rfl⟩ : syracuseStep 1221311 = 1831967) B1831967
theorem B6600275 : Blo 642303 6600275 := bstep (se 1 (by rfl) ⟨4950206, by rfl⟩ : syracuseStep 6600275 = 9900413) B9900413
theorem B1031359 : Blo 642303 1031359 := bstep (se 1 (by rfl) ⟨773519, by rfl⟩ : syracuseStep 1031359 = 1547039) B1547039
theorem B644891 : Blo 642303 644891 := bstep (se 1 (by rfl) ⟨483668, by rfl⟩ : syracuseStep 644891 = 967337) B967337
theorem B645211 : Blo 642303 645211 := bstep (se 1 (by rfl) ⟨483908, by rfl⟩ : syracuseStep 645211 = 967817) B967817
theorem B3663407 : Blo 642303 3663407 := bstep (se 1 (by rfl) ⟨2747555, by rfl⟩ : syracuseStep 3663407 = 5495111) B5495111
theorem B2690387 : Blo 642303 2690387 := bstep (se 1 (by rfl) ⟨2017790, by rfl⟩ : syracuseStep 2690387 = 4035581) B4035581
theorem B4400183 : Blo 642303 4400183 := bstep (se 1 (by rfl) ⟨3300137, by rfl⟩ : syracuseStep 4400183 = 6600275) B6600275
theorem B150650401 : Blo 642303 150650401 := bstep (se 2 (by rfl) ⟨56493900, by rfl⟩ : syracuseStep 150650401 = 112987801) B112987801
theorem B2442271 : Blo 642303 2442271 := bstep (se 1 (by rfl) ⟨1831703, by rfl⟩ : syracuseStep 2442271 = 3663407) B3663407
theorem B814207 : Blo 642303 814207 := bstep (se 1 (by rfl) ⟨610655, by rfl⟩ : syracuseStep 814207 = 1221311) B1221311
theorem B1375145 : Blo 642303 1375145 := bstep (se 2 (by rfl) ⟨515679, by rfl⟩ : syracuseStep 1375145 = 1031359) B1031359
theorem B1085609 : Blo 642303 1085609 := bstep (se 2 (by rfl) ⟨407103, by rfl⟩ : syracuseStep 1085609 = 814207) B814207
theorem B3256361 : Blo 642303 3256361 := bstep (se 2 (by rfl) ⟨1221135, by rfl⟩ : syracuseStep 3256361 = 2442271) B2442271
theorem B2933455 : Blo 642303 2933455 := bstep (se 1 (by rfl) ⟨2200091, by rfl⟩ : syracuseStep 2933455 = 4400183) B4400183
theorem B1793591 : Blo 642303 1793591 := bstep (se 1 (by rfl) ⟨1345193, by rfl⟩ : syracuseStep 1793591 = 2690387) B2690387
theorem B916763 : Blo 642303 916763 := bstep (se 1 (by rfl) ⟨687572, by rfl⟩ : syracuseStep 916763 = 1375145) B1375145
theorem B200867201 : Blo 642303 200867201 := bstep (se 2 (by rfl) ⟨75325200, by rfl⟩ : syracuseStep 200867201 = 150650401) B150650401
theorem B723739 : Blo 642303 723739 := bstep (se 1 (by rfl) ⟨542804, by rfl⟩ : syracuseStep 723739 = 1085609) B1085609
theorem B2170907 : Blo 642303 2170907 := bstep (se 1 (by rfl) ⟨1628180, by rfl⟩ : syracuseStep 2170907 = 3256361) B3256361
theorem B3911273 : Blo 642303 3911273 := bstep (se 2 (by rfl) ⟨1466727, by rfl⟩ : syracuseStep 3911273 = 2933455) B2933455
theorem B1195727 : Blo 642303 1195727 := bstep (se 1 (by rfl) ⟨896795, by rfl⟩ : syracuseStep 1195727 = 1793591) B1793591
theorem B2444701 : Blo 642303 2444701 := bstep (se 3 (by rfl) ⟨458381, by rfl⟩ : syracuseStep 2444701 = 916763) B916763
theorem B133911467 : Blo 642303 133911467 := bstep (se 1 (by rfl) ⟨100433600, by rfl⟩ : syracuseStep 133911467 = 200867201) B200867201
theorem B1447271 : Blo 642303 1447271 := bstep (se 1 (by rfl) ⟨1085453, by rfl⟩ : syracuseStep 1447271 = 2170907) B2170907
theorem B3188605 : Blo 642303 3188605 := bstep (se 3 (by rfl) ⟨597863, by rfl⟩ : syracuseStep 3188605 = 1195727) B1195727
theorem B89274311 : Blo 642303 89274311 := bstep (se 1 (by rfl) ⟨66955733, by rfl⟩ : syracuseStep 89274311 = 133911467) B133911467
theorem B964985 : Blo 642303 964985 := bstep (se 2 (by rfl) ⟨361869, by rfl⟩ : syracuseStep 964985 = 723739) B723739
theorem B3259601 : Blo 642303 3259601 := bstep (se 2 (by rfl) ⟨1222350, by rfl⟩ : syracuseStep 3259601 = 2444701) B2444701
theorem B2607515 : Blo 642303 2607515 := bstep (se 1 (by rfl) ⟨1955636, by rfl⟩ : syracuseStep 2607515 = 3911273) B3911273
theorem B1738343 : Blo 642303 1738343 := bstep (se 1 (by rfl) ⟨1303757, by rfl⟩ : syracuseStep 1738343 = 2607515) B2607515
theorem B59516207 : Blo 642303 59516207 := bstep (se 1 (by rfl) ⟨44637155, by rfl⟩ : syracuseStep 59516207 = 89274311) B89274311
theorem B2173067 : Blo 642303 2173067 := bstep (se 1 (by rfl) ⟨1629800, by rfl⟩ : syracuseStep 2173067 = 3259601) B3259601
theorem B964847 : Blo 642303 964847 := bstep (se 1 (by rfl) ⟨723635, by rfl⟩ : syracuseStep 964847 = 1447271) B1447271
theorem B643323 : Blo 642303 643323 := bstep (se 1 (by rfl) ⟨482492, by rfl⟩ : syracuseStep 643323 = 964985) B964985
theorem B4251473 : Blo 642303 4251473 := bstep (se 2 (by rfl) ⟨1594302, by rfl⟩ : syracuseStep 4251473 = 3188605) B3188605
theorem B1448711 : Blo 642303 1448711 := bstep (se 1 (by rfl) ⟨1086533, by rfl⟩ : syracuseStep 1448711 = 2173067) B2173067
theorem B1158895 : Blo 642303 1158895 := bstep (se 1 (by rfl) ⟨869171, by rfl⟩ : syracuseStep 1158895 = 1738343) B1738343
theorem B2834315 : Blo 642303 2834315 := bstep (se 1 (by rfl) ⟨2125736, by rfl⟩ : syracuseStep 2834315 = 4251473) B4251473
theorem B643231 : Blo 642303 643231 := bstep (se 1 (by rfl) ⟨482423, by rfl⟩ : syracuseStep 643231 = 964847) B964847
theorem B39677471 : Blo 642303 39677471 := bstep (se 1 (by rfl) ⟨29758103, by rfl⟩ : syracuseStep 39677471 = 59516207) B59516207
theorem B1545193 : Blo 642303 1545193 := bstep (se 2 (by rfl) ⟨579447, by rfl⟩ : syracuseStep 1545193 = 1158895) B1158895
theorem B26451647 : Blo 642303 26451647 := bstep (se 1 (by rfl) ⟨19838735, by rfl⟩ : syracuseStep 26451647 = 39677471) B39677471
theorem B965807 : Blo 642303 965807 := bstep (se 1 (by rfl) ⟨724355, by rfl⟩ : syracuseStep 965807 = 1448711) B1448711
theorem B1889543 : Blo 642303 1889543 := bstep (se 1 (by rfl) ⟨1417157, by rfl⟩ : syracuseStep 1889543 = 2834315) B2834315
theorem B17634431 : Blo 642303 17634431 := bstep (se 1 (by rfl) ⟨13225823, by rfl⟩ : syracuseStep 17634431 = 26451647) B26451647
theorem B1259695 : Blo 642303 1259695 := bstep (se 1 (by rfl) ⟨944771, by rfl⟩ : syracuseStep 1259695 = 1889543) B1889543
theorem B643871 : Blo 642303 643871 := bstep (se 1 (by rfl) ⟨482903, by rfl⟩ : syracuseStep 643871 = 965807) B965807
theorem B2060257 : Blo 642303 2060257 := bstep (se 2 (by rfl) ⟨772596, by rfl⟩ : syracuseStep 2060257 = 1545193) B1545193
theorem B6718373 : Blo 642303 6718373 := bstep (se 4 (by rfl) ⟨629847, by rfl⟩ : syracuseStep 6718373 = 1259695) B1259695
theorem B11756287 : Blo 642303 11756287 := bstep (se 1 (by rfl) ⟨8817215, by rfl⟩ : syracuseStep 11756287 = 17634431) B17634431
theorem B2747009 : Blo 642303 2747009 := bstep (se 2 (by rfl) ⟨1030128, by rfl⟩ : syracuseStep 2747009 = 2060257) B2060257
theorem B15675049 : Blo 642303 15675049 := bstep (se 2 (by rfl) ⟨5878143, by rfl⟩ : syracuseStep 15675049 = 11756287) B11756287
theorem B4478915 : Blo 642303 4478915 := bstep (se 1 (by rfl) ⟨3359186, by rfl⟩ : syracuseStep 4478915 = 6718373) B6718373
theorem B1831339 : Blo 642303 1831339 := bstep (se 1 (by rfl) ⟨1373504, by rfl⟩ : syracuseStep 1831339 = 2747009) B2747009
theorem B11943773 : Blo 642303 11943773 := bstep (se 3 (by rfl) ⟨2239457, by rfl⟩ : syracuseStep 11943773 = 4478915) B4478915
theorem B2441785 : Blo 642303 2441785 := bstep (se 2 (by rfl) ⟨915669, by rfl⟩ : syracuseStep 2441785 = 1831339) B1831339
theorem B20900065 : Blo 642303 20900065 := bstep (se 2 (by rfl) ⟨7837524, by rfl⟩ : syracuseStep 20900065 = 15675049) B15675049
theorem B3255713 : Blo 642303 3255713 := bstep (se 2 (by rfl) ⟨1220892, by rfl⟩ : syracuseStep 3255713 = 2441785) B2441785
theorem B27866753 : Blo 642303 27866753 := bstep (se 2 (by rfl) ⟨10450032, by rfl⟩ : syracuseStep 27866753 = 20900065) B20900065
theorem B7962515 : Blo 642303 7962515 := bstep (se 1 (by rfl) ⟨5971886, by rfl⟩ : syracuseStep 7962515 = 11943773) B11943773
theorem B2170475 : Blo 642303 2170475 := bstep (se 1 (by rfl) ⟨1627856, by rfl⟩ : syracuseStep 2170475 = 3255713) B3255713
theorem B18577835 : Blo 642303 18577835 := bstep (se 1 (by rfl) ⟨13933376, by rfl⟩ : syracuseStep 18577835 = 27866753) B27866753
theorem B5308343 : Blo 642303 5308343 := bstep (se 1 (by rfl) ⟨3981257, by rfl⟩ : syracuseStep 5308343 = 7962515) B7962515
theorem B1446983 : Blo 642303 1446983 := bstep (se 1 (by rfl) ⟨1085237, by rfl⟩ : syracuseStep 1446983 = 2170475) B2170475
theorem B12385223 : Blo 642303 12385223 := bstep (se 1 (by rfl) ⟨9288917, by rfl⟩ : syracuseStep 12385223 = 18577835) B18577835
theorem B3538895 : Blo 642303 3538895 := bstep (se 1 (by rfl) ⟨2654171, by rfl⟩ : syracuseStep 3538895 = 5308343) B5308343
theorem B964655 : Blo 642303 964655 := bstep (se 1 (by rfl) ⟨723491, by rfl⟩ : syracuseStep 964655 = 1446983) B1446983
theorem B8256815 : Blo 642303 8256815 := bstep (se 1 (by rfl) ⟨6192611, by rfl⟩ : syracuseStep 8256815 = 12385223) B12385223
theorem B37748213 : Blo 642303 37748213 := bstep (se 5 (by rfl) ⟨1769447, by rfl⟩ : syracuseStep 37748213 = 3538895) B3538895
theorem B643103 : Blo 642303 643103 := bstep (se 1 (by rfl) ⟨482327, by rfl⟩ : syracuseStep 643103 = 964655) B964655
theorem B5504543 : Blo 642303 5504543 := bstep (se 1 (by rfl) ⟨4128407, by rfl⟩ : syracuseStep 5504543 = 8256815) B8256815
theorem B25165475 : Blo 642303 25165475 := bstep (se 1 (by rfl) ⟨18874106, by rfl⟩ : syracuseStep 25165475 = 37748213) B37748213
theorem B3669695 : Blo 642303 3669695 := bstep (se 1 (by rfl) ⟨2752271, by rfl⟩ : syracuseStep 3669695 = 5504543) B5504543
theorem B16776983 : Blo 642303 16776983 := bstep (se 1 (by rfl) ⟨12582737, by rfl⟩ : syracuseStep 16776983 = 25165475) B25165475
theorem B11184655 : Blo 642303 11184655 := bstep (se 1 (by rfl) ⟨8388491, by rfl⟩ : syracuseStep 11184655 = 16776983) B16776983
theorem B2446463 : Blo 642303 2446463 := bstep (se 1 (by rfl) ⟨1834847, by rfl⟩ : syracuseStep 2446463 = 3669695) B3669695
theorem B14912873 : Blo 642303 14912873 := bstep (se 2 (by rfl) ⟨5592327, by rfl⟩ : syracuseStep 14912873 = 11184655) B11184655
theorem B1630975 : Blo 642303 1630975 := bstep (se 1 (by rfl) ⟨1223231, by rfl⟩ : syracuseStep 1630975 = 2446463) B2446463
theorem B2174633 : Blo 642303 2174633 := bstep (se 2 (by rfl) ⟨815487, by rfl⟩ : syracuseStep 2174633 = 1630975) B1630975
theorem B9941915 : Blo 642303 9941915 := bstep (se 1 (by rfl) ⟨7456436, by rfl⟩ : syracuseStep 9941915 = 14912873) B14912873
theorem B1449755 : Blo 642303 1449755 := bstep (se 1 (by rfl) ⟨1087316, by rfl⟩ : syracuseStep 1449755 = 2174633) B2174633
theorem B6627943 : Blo 642303 6627943 := bstep (se 1 (by rfl) ⟨4970957, by rfl⟩ : syracuseStep 6627943 = 9941915) B9941915
theorem B966503 : Blo 642303 966503 := bstep (se 1 (by rfl) ⟨724877, by rfl⟩ : syracuseStep 966503 = 1449755) B1449755
theorem B8837257 : Blo 642303 8837257 := bstep (se 2 (by rfl) ⟨3313971, by rfl⟩ : syracuseStep 8837257 = 6627943) B6627943
theorem B11783009 : Blo 642303 11783009 := bstep (se 2 (by rfl) ⟨4418628, by rfl⟩ : syracuseStep 11783009 = 8837257) B8837257
theorem B644335 : Blo 642303 644335 := bstep (se 1 (by rfl) ⟨483251, by rfl⟩ : syracuseStep 644335 = 966503) B966503
theorem B7855339 : Blo 642303 7855339 := bstep (se 1 (by rfl) ⟨5891504, by rfl⟩ : syracuseStep 7855339 = 11783009) B11783009
theorem B10473785 : Blo 642303 10473785 := bstep (se 2 (by rfl) ⟨3927669, by rfl⟩ : syracuseStep 10473785 = 7855339) B7855339
theorem B6982523 : Blo 642303 6982523 := bstep (se 1 (by rfl) ⟨5236892, by rfl⟩ : syracuseStep 6982523 = 10473785) B10473785
theorem B4655015 : Blo 642303 4655015 := bstep (se 1 (by rfl) ⟨3491261, by rfl⟩ : syracuseStep 4655015 = 6982523) B6982523
theorem B3103343 : Blo 642303 3103343 := bstep (se 1 (by rfl) ⟨2327507, by rfl⟩ : syracuseStep 3103343 = 4655015) B4655015
theorem B2068895 : Blo 642303 2068895 := bstep (se 1 (by rfl) ⟨1551671, by rfl⟩ : syracuseStep 2068895 = 3103343) B3103343
theorem B1379263 : Blo 642303 1379263 := bstep (se 1 (by rfl) ⟨1034447, by rfl⟩ : syracuseStep 1379263 = 2068895) B2068895
theorem B1839017 : Blo 642303 1839017 := bstep (se 2 (by rfl) ⟨689631, by rfl⟩ : syracuseStep 1839017 = 1379263) B1379263
theorem B1226011 : Blo 642303 1226011 := bstep (se 1 (by rfl) ⟨919508, by rfl⟩ : syracuseStep 1226011 = 1839017) B1839017
theorem B1634681 : Blo 642303 1634681 := bstep (se 2 (by rfl) ⟨613005, by rfl⟩ : syracuseStep 1634681 = 1226011) B1226011
theorem B1089787 : Blo 642303 1089787 := bstep (se 1 (by rfl) ⟨817340, by rfl⟩ : syracuseStep 1089787 = 1634681) B1634681
theorem B1453049 : Blo 642303 1453049 := bstep (se 2 (by rfl) ⟨544893, by rfl⟩ : syracuseStep 1453049 = 1089787) B1089787
theorem B968699 : Blo 642303 968699 := bstep (se 1 (by rfl) ⟨726524, by rfl⟩ : syracuseStep 968699 = 1453049) B1453049
theorem B645799 : Blo 642303 645799 := bstep (se 1 (by rfl) ⟨484349, by rfl⟩ : syracuseStep 645799 = 968699) B968699

theorem C0 (j : ℕ) (h1 : 160575 ≤ j) (h2 : j ≤ 161274) : Blo 642303 (4 * j + 3) := by
  interval_cases j
  · exact B642303
  · exact B642307
  · exact B642311
  · exact B642315
  · exact B642319
  · exact B642323
  · exact B642327
  · exact B642331
  · exact B642335
  · exact B642339
  · exact B642343
  · exact B642347
  · exact B642351
  · exact B642355
  · exact B642359
  · exact B642363
  · exact B642367
  · exact B642371
  · exact B642375
  · exact B642379
  · exact B642383
  · exact B642387
  · exact B642391
  · exact B642395
  · exact B642399
  · exact B642403
  · exact B642407
  · exact B642411
  · exact B642415
  · exact B642419
  · exact B642423
  · exact B642427
  · exact B642431
  · exact B642435
  · exact B642439
  · exact B642443
  · exact B642447
  · exact B642451
  · exact B642455
  · exact B642459
  · exact B642463
  · exact B642467
  · exact B642471
  · exact B642475
  · exact B642479
  · exact B642483
  · exact B642487
  · exact B642491
  · exact B642495
  · exact B642499
  · exact B642503
  · exact B642507
  · exact B642511
  · exact B642515
  · exact B642519
  · exact B642523
  · exact B642527
  · exact B642531
  · exact B642535
  · exact B642539
  · exact B642543
  · exact B642547
  · exact B642551
  · exact B642555
  · exact B642559
  · exact B642563
  · exact B642567
  · exact B642571
  · exact B642575
  · exact B642579
  · exact B642583
  · exact B642587
  · exact B642591
  · exact B642595
  · exact B642599
  · exact B642603
  · exact B642607
  · exact B642611
  · exact B642615
  · exact B642619
  · exact B642623
  · exact B642627
  · exact B642631
  · exact B642635
  · exact B642639
  · exact B642643
  · exact B642647
  · exact B642651
  · exact B642655
  · exact B642659
  · exact B642663
  · exact B642667
  · exact B642671
  · exact B642675
  · exact B642679
  · exact B642683
  · exact B642687
  · exact B642691
  · exact B642695
  · exact B642699
  · exact B642703
  · exact B642707
  · exact B642711
  · exact B642715
  · exact B642719
  · exact B642723
  · exact B642727
  · exact B642731
  · exact B642735
  · exact B642739
  · exact B642743
  · exact B642747
  · exact B642751
  · exact B642755
  · exact B642759
  · exact B642763
  · exact B642767
  · exact B642771
  · exact B642775
  · exact B642779
  · exact B642783
  · exact B642787
  · exact B642791
  · exact B642795
  · exact B642799
  · exact B642803
  · exact B642807
  · exact B642811
  · exact B642815
  · exact B642819
  · exact B642823
  · exact B642827
  · exact B642831
  · exact B642835
  · exact B642839
  · exact B642843
  · exact B642847
  · exact B642851
  · exact B642855
  · exact B642859
  · exact B642863
  · exact B642867
  · exact B642871
  · exact B642875
  · exact B642879
  · exact B642883
  · exact B642887
  · exact B642891
  · exact B642895
  · exact B642899
  · exact B642903
  · exact B642907
  · exact B642911
  · exact B642915
  · exact B642919
  · exact B642923
  · exact B642927
  · exact B642931
  · exact B642935
  · exact B642939
  · exact B642943
  · exact B642947
  · exact B642951
  · exact B642955
  · exact B642959
  · exact B642963
  · exact B642967
  · exact B642971
  · exact B642975
  · exact B642979
  · exact B642983
  · exact B642987
  · exact B642991
  · exact B642995
  · exact B642999
  · exact B643003
  · exact B643007
  · exact B643011
  · exact B643015
  · exact B643019
  · exact B643023
  · exact B643027
  · exact B643031
  · exact B643035
  · exact B643039
  · exact B643043
  · exact B643047
  · exact B643051
  · exact B643055
  · exact B643059
  · exact B643063
  · exact B643067
  · exact B643071
  · exact B643075
  · exact B643079
  · exact B643083
  · exact B643087
  · exact B643091
  · exact B643095
  · exact B643099
  · exact B643103
  · exact B643107
  · exact B643111
  · exact B643115
  · exact B643119
  · exact B643123
  · exact B643127
  · exact B643131
  · exact B643135
  · exact B643139
  · exact B643143
  · exact B643147
  · exact B643151
  · exact B643155
  · exact B643159
  · exact B643163
  · exact B643167
  · exact B643171
  · exact B643175
  · exact B643179
  · exact B643183
  · exact B643187
  · exact B643191
  · exact B643195
  · exact B643199
  · exact B643203
  · exact B643207
  · exact B643211
  · exact B643215
  · exact B643219
  · exact B643223
  · exact B643227
  · exact B643231
  · exact B643235
  · exact B643239
  · exact B643243
  · exact B643247
  · exact B643251
  · exact B643255
  · exact B643259
  · exact B643263
  · exact B643267
  · exact B643271
  · exact B643275
  · exact B643279
  · exact B643283
  · exact B643287
  · exact B643291
  · exact B643295
  · exact B643299
  · exact B643303
  · exact B643307
  · exact B643311
  · exact B643315
  · exact B643319
  · exact B643323
  · exact B643327
  · exact B643331
  · exact B643335
  · exact B643339
  · exact B643343
  · exact B643347
  · exact B643351
  · exact B643355
  · exact B643359
  · exact B643363
  · exact B643367
  · exact B643371
  · exact B643375
  · exact B643379
  · exact B643383
  · exact B643387
  · exact B643391
  · exact B643395
  · exact B643399
  · exact B643403
  · exact B643407
  · exact B643411
  · exact B643415
  · exact B643419
  · exact B643423
  · exact B643427
  · exact B643431
  · exact B643435
  · exact B643439
  · exact B643443
  · exact B643447
  · exact B643451
  · exact B643455
  · exact B643459
  · exact B643463
  · exact B643467
  · exact B643471
  · exact B643475
  · exact B643479
  · exact B643483
  · exact B643487
  · exact B643491
  · exact B643495
  · exact B643499
  · exact B643503
  · exact B643507
  · exact B643511
  · exact B643515
  · exact B643519
  · exact B643523
  · exact B643527
  · exact B643531
  · exact B643535
  · exact B643539
  · exact B643543
  · exact B643547
  · exact B643551
  · exact B643555
  · exact B643559
  · exact B643563
  · exact B643567
  · exact B643571
  · exact B643575
  · exact B643579
  · exact B643583
  · exact B643587
  · exact B643591
  · exact B643595
  · exact B643599
  · exact B643603
  · exact B643607
  · exact B643611
  · exact B643615
  · exact B643619
  · exact B643623
  · exact B643627
  · exact B643631
  · exact B643635
  · exact B643639
  · exact B643643
  · exact B643647
  · exact B643651
  · exact B643655
  · exact B643659
  · exact B643663
  · exact B643667
  · exact B643671
  · exact B643675
  · exact B643679
  · exact B643683
  · exact B643687
  · exact B643691
  · exact B643695
  · exact B643699
  · exact B643703
  · exact B643707
  · exact B643711
  · exact B643715
  · exact B643719
  · exact B643723
  · exact B643727
  · exact B643731
  · exact B643735
  · exact B643739
  · exact B643743
  · exact B643747
  · exact B643751
  · exact B643755
  · exact B643759
  · exact B643763
  · exact B643767
  · exact B643771
  · exact B643775
  · exact B643779
  · exact B643783
  · exact B643787
  · exact B643791
  · exact B643795
  · exact B643799
  · exact B643803
  · exact B643807
  · exact B643811
  · exact B643815
  · exact B643819
  · exact B643823
  · exact B643827
  · exact B643831
  · exact B643835
  · exact B643839
  · exact B643843
  · exact B643847
  · exact B643851
  · exact B643855
  · exact B643859
  · exact B643863
  · exact B643867
  · exact B643871
  · exact B643875
  · exact B643879
  · exact B643883
  · exact B643887
  · exact B643891
  · exact B643895
  · exact B643899
  · exact B643903
  · exact B643907
  · exact B643911
  · exact B643915
  · exact B643919
  · exact B643923
  · exact B643927
  · exact B643931
  · exact B643935
  · exact B643939
  · exact B643943
  · exact B643947
  · exact B643951
  · exact B643955
  · exact B643959
  · exact B643963
  · exact B643967
  · exact B643971
  · exact B643975
  · exact B643979
  · exact B643983
  · exact B643987
  · exact B643991
  · exact B643995
  · exact B643999
  · exact B644003
  · exact B644007
  · exact B644011
  · exact B644015
  · exact B644019
  · exact B644023
  · exact B644027
  · exact B644031
  · exact B644035
  · exact B644039
  · exact B644043
  · exact B644047
  · exact B644051
  · exact B644055
  · exact B644059
  · exact B644063
  · exact B644067
  · exact B644071
  · exact B644075
  · exact B644079
  · exact B644083
  · exact B644087
  · exact B644091
  · exact B644095
  · exact B644099
  · exact B644103
  · exact B644107
  · exact B644111
  · exact B644115
  · exact B644119
  · exact B644123
  · exact B644127
  · exact B644131
  · exact B644135
  · exact B644139
  · exact B644143
  · exact B644147
  · exact B644151
  · exact B644155
  · exact B644159
  · exact B644163
  · exact B644167
  · exact B644171
  · exact B644175
  · exact B644179
  · exact B644183
  · exact B644187
  · exact B644191
  · exact B644195
  · exact B644199
  · exact B644203
  · exact B644207
  · exact B644211
  · exact B644215
  · exact B644219
  · exact B644223
  · exact B644227
  · exact B644231
  · exact B644235
  · exact B644239
  · exact B644243
  · exact B644247
  · exact B644251
  · exact B644255
  · exact B644259
  · exact B644263
  · exact B644267
  · exact B644271
  · exact B644275
  · exact B644279
  · exact B644283
  · exact B644287
  · exact B644291
  · exact B644295
  · exact B644299
  · exact B644303
  · exact B644307
  · exact B644311
  · exact B644315
  · exact B644319
  · exact B644323
  · exact B644327
  · exact B644331
  · exact B644335
  · exact B644339
  · exact B644343
  · exact B644347
  · exact B644351
  · exact B644355
  · exact B644359
  · exact B644363
  · exact B644367
  · exact B644371
  · exact B644375
  · exact B644379
  · exact B644383
  · exact B644387
  · exact B644391
  · exact B644395
  · exact B644399
  · exact B644403
  · exact B644407
  · exact B644411
  · exact B644415
  · exact B644419
  · exact B644423
  · exact B644427
  · exact B644431
  · exact B644435
  · exact B644439
  · exact B644443
  · exact B644447
  · exact B644451
  · exact B644455
  · exact B644459
  · exact B644463
  · exact B644467
  · exact B644471
  · exact B644475
  · exact B644479
  · exact B644483
  · exact B644487
  · exact B644491
  · exact B644495
  · exact B644499
  · exact B644503
  · exact B644507
  · exact B644511
  · exact B644515
  · exact B644519
  · exact B644523
  · exact B644527
  · exact B644531
  · exact B644535
  · exact B644539
  · exact B644543
  · exact B644547
  · exact B644551
  · exact B644555
  · exact B644559
  · exact B644563
  · exact B644567
  · exact B644571
  · exact B644575
  · exact B644579
  · exact B644583
  · exact B644587
  · exact B644591
  · exact B644595
  · exact B644599
  · exact B644603
  · exact B644607
  · exact B644611
  · exact B644615
  · exact B644619
  · exact B644623
  · exact B644627
  · exact B644631
  · exact B644635
  · exact B644639
  · exact B644643
  · exact B644647
  · exact B644651
  · exact B644655
  · exact B644659
  · exact B644663
  · exact B644667
  · exact B644671
  · exact B644675
  · exact B644679
  · exact B644683
  · exact B644687
  · exact B644691
  · exact B644695
  · exact B644699
  · exact B644703
  · exact B644707
  · exact B644711
  · exact B644715
  · exact B644719
  · exact B644723
  · exact B644727
  · exact B644731
  · exact B644735
  · exact B644739
  · exact B644743
  · exact B644747
  · exact B644751
  · exact B644755
  · exact B644759
  · exact B644763
  · exact B644767
  · exact B644771
  · exact B644775
  · exact B644779
  · exact B644783
  · exact B644787
  · exact B644791
  · exact B644795
  · exact B644799
  · exact B644803
  · exact B644807
  · exact B644811
  · exact B644815
  · exact B644819
  · exact B644823
  · exact B644827
  · exact B644831
  · exact B644835
  · exact B644839
  · exact B644843
  · exact B644847
  · exact B644851
  · exact B644855
  · exact B644859
  · exact B644863
  · exact B644867
  · exact B644871
  · exact B644875
  · exact B644879
  · exact B644883
  · exact B644887
  · exact B644891
  · exact B644895
  · exact B644899
  · exact B644903
  · exact B644907
  · exact B644911
  · exact B644915
  · exact B644919
  · exact B644923
  · exact B644927
  · exact B644931
  · exact B644935
  · exact B644939
  · exact B644943
  · exact B644947
  · exact B644951
  · exact B644955
  · exact B644959
  · exact B644963
  · exact B644967
  · exact B644971
  · exact B644975
  · exact B644979
  · exact B644983
  · exact B644987
  · exact B644991
  · exact B644995
  · exact B644999
  · exact B645003
  · exact B645007
  · exact B645011
  · exact B645015
  · exact B645019
  · exact B645023
  · exact B645027
  · exact B645031
  · exact B645035
  · exact B645039
  · exact B645043
  · exact B645047
  · exact B645051
  · exact B645055
  · exact B645059
  · exact B645063
  · exact B645067
  · exact B645071
  · exact B645075
  · exact B645079
  · exact B645083
  · exact B645087
  · exact B645091
  · exact B645095
  · exact B645099

theorem C1 (j : ℕ) (h1 : 161275 ≤ j) (h2 : j ≤ 161575) : Blo 642303 (4 * j + 3) := by
  interval_cases j
  · exact B645103
  · exact B645107
  · exact B645111
  · exact B645115
  · exact B645119
  · exact B645123
  · exact B645127
  · exact B645131
  · exact B645135
  · exact B645139
  · exact B645143
  · exact B645147
  · exact B645151
  · exact B645155
  · exact B645159
  · exact B645163
  · exact B645167
  · exact B645171
  · exact B645175
  · exact B645179
  · exact B645183
  · exact B645187
  · exact B645191
  · exact B645195
  · exact B645199
  · exact B645203
  · exact B645207
  · exact B645211
  · exact B645215
  · exact B645219
  · exact B645223
  · exact B645227
  · exact B645231
  · exact B645235
  · exact B645239
  · exact B645243
  · exact B645247
  · exact B645251
  · exact B645255
  · exact B645259
  · exact B645263
  · exact B645267
  · exact B645271
  · exact B645275
  · exact B645279
  · exact B645283
  · exact B645287
  · exact B645291
  · exact B645295
  · exact B645299
  · exact B645303
  · exact B645307
  · exact B645311
  · exact B645315
  · exact B645319
  · exact B645323
  · exact B645327
  · exact B645331
  · exact B645335
  · exact B645339
  · exact B645343
  · exact B645347
  · exact B645351
  · exact B645355
  · exact B645359
  · exact B645363
  · exact B645367
  · exact B645371
  · exact B645375
  · exact B645379
  · exact B645383
  · exact B645387
  · exact B645391
  · exact B645395
  · exact B645399
  · exact B645403
  · exact B645407
  · exact B645411
  · exact B645415
  · exact B645419
  · exact B645423
  · exact B645427
  · exact B645431
  · exact B645435
  · exact B645439
  · exact B645443
  · exact B645447
  · exact B645451
  · exact B645455
  · exact B645459
  · exact B645463
  · exact B645467
  · exact B645471
  · exact B645475
  · exact B645479
  · exact B645483
  · exact B645487
  · exact B645491
  · exact B645495
  · exact B645499
  · exact B645503
  · exact B645507
  · exact B645511
  · exact B645515
  · exact B645519
  · exact B645523
  · exact B645527
  · exact B645531
  · exact B645535
  · exact B645539
  · exact B645543
  · exact B645547
  · exact B645551
  · exact B645555
  · exact B645559
  · exact B645563
  · exact B645567
  · exact B645571
  · exact B645575
  · exact B645579
  · exact B645583
  · exact B645587
  · exact B645591
  · exact B645595
  · exact B645599
  · exact B645603
  · exact B645607
  · exact B645611
  · exact B645615
  · exact B645619
  · exact B645623
  · exact B645627
  · exact B645631
  · exact B645635
  · exact B645639
  · exact B645643
  · exact B645647
  · exact B645651
  · exact B645655
  · exact B645659
  · exact B645663
  · exact B645667
  · exact B645671
  · exact B645675
  · exact B645679
  · exact B645683
  · exact B645687
  · exact B645691
  · exact B645695
  · exact B645699
  · exact B645703
  · exact B645707
  · exact B645711
  · exact B645715
  · exact B645719
  · exact B645723
  · exact B645727
  · exact B645731
  · exact B645735
  · exact B645739
  · exact B645743
  · exact B645747
  · exact B645751
  · exact B645755
  · exact B645759
  · exact B645763
  · exact B645767
  · exact B645771
  · exact B645775
  · exact B645779
  · exact B645783
  · exact B645787
  · exact B645791
  · exact B645795
  · exact B645799
  · exact B645803
  · exact B645807
  · exact B645811
  · exact B645815
  · exact B645819
  · exact B645823
  · exact B645827
  · exact B645831
  · exact B645835
  · exact B645839
  · exact B645843
  · exact B645847
  · exact B645851
  · exact B645855
  · exact B645859
  · exact B645863
  · exact B645867
  · exact B645871
  · exact B645875
  · exact B645879
  · exact B645883
  · exact B645887
  · exact B645891
  · exact B645895
  · exact B645899
  · exact B645903
  · exact B645907
  · exact B645911
  · exact B645915
  · exact B645919
  · exact B645923
  · exact B645927
  · exact B645931
  · exact B645935
  · exact B645939
  · exact B645943
  · exact B645947
  · exact B645951
  · exact B645955
  · exact B645959
  · exact B645963
  · exact B645967
  · exact B645971
  · exact B645975
  · exact B645979
  · exact B645983
  · exact B645987
  · exact B645991
  · exact B645995
  · exact B645999
  · exact B646003
  · exact B646007
  · exact B646011
  · exact B646015
  · exact B646019
  · exact B646023
  · exact B646027
  · exact B646031
  · exact B646035
  · exact B646039
  · exact B646043
  · exact B646047
  · exact B646051
  · exact B646055
  · exact B646059
  · exact B646063
  · exact B646067
  · exact B646071
  · exact B646075
  · exact B646079
  · exact B646083
  · exact B646087
  · exact B646091
  · exact B646095
  · exact B646099
  · exact B646103
  · exact B646107
  · exact B646111
  · exact B646115
  · exact B646119
  · exact B646123
  · exact B646127
  · exact B646131
  · exact B646135
  · exact B646139
  · exact B646143
  · exact B646147
  · exact B646151
  · exact B646155
  · exact B646159
  · exact B646163
  · exact B646167
  · exact B646171
  · exact B646175
  · exact B646179
  · exact B646183
  · exact B646187
  · exact B646191
  · exact B646195
  · exact B646199
  · exact B646203
  · exact B646207
  · exact B646211
  · exact B646215
  · exact B646219
  · exact B646223
  · exact B646227
  · exact B646231
  · exact B646235
  · exact B646239
  · exact B646243
  · exact B646247
  · exact B646251
  · exact B646255
  · exact B646259
  · exact B646263
  · exact B646267
  · exact B646271
  · exact B646275
  · exact B646279
  · exact B646283
  · exact B646287
  · exact B646291
  · exact B646295
  · exact B646299
  · exact B646303

theorem solution (m : ℕ) (hlo : 642303 ≤ m) (hhi : m ≤ 646303) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 160575 ≤ j := by omega
    have hj2 : j ≤ 161575 := by omega
    have hb : Blo 642303 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 161275 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
