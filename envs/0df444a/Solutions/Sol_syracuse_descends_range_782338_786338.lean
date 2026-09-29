-- Prove2me | solution 1 for syracuse_descends_range_782338_786338
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:31.994047+00:00
-- url     : https://prove2.me/submissions/899ae50c-3376-4362-8cc1-5ec233be856e

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


theorem B3964949 : Blo 782338 3964949 := bbase (se 6 (by rfl) ⟨92928, by rfl⟩ : syracuseStep 3964949 = 185857) (by norm_num)
theorem B2982005 : Blo 782338 2982005 := bbase (se 5 (by rfl) ⟨139781, by rfl⟩ : syracuseStep 2982005 = 279563) (by norm_num)
theorem B2228485 : Blo 782338 2228485 := bbase (se 4 (by rfl) ⟨208920, by rfl⟩ : syracuseStep 2228485 = 417841) (by norm_num)
theorem B1114573 : Blo 782338 1114573 := bbase (se 3 (by rfl) ⟨208982, by rfl⟩ : syracuseStep 1114573 = 417965) (by norm_num)
theorem B1671749 : Blo 782338 1671749 := bbase (se 4 (by rfl) ⟨156726, by rfl⟩ : syracuseStep 1671749 = 313453) (by norm_num)
theorem B5374549 : Blo 782338 5374549 := bbase (se 8 (by rfl) ⟨31491, by rfl⟩ : syracuseStep 5374549 = 62983) (by norm_num)
theorem B15074261 : Blo 782338 15074261 := bbase (se 7 (by rfl) ⟨176651, by rfl⟩ : syracuseStep 15074261 = 353303) (by norm_num)
theorem B14320597 : Blo 782338 14320597 := bbase (se 7 (by rfl) ⟨167819, by rfl⟩ : syracuseStep 14320597 = 335639) (by norm_num)
theorem B10322965 : Blo 782338 10322965 := bbase (se 6 (by rfl) ⟨241944, by rfl⟩ : syracuseStep 10322965 = 483889) (by norm_num)
theorem B1115165 : Blo 782338 1115165 := bbase (se 3 (by rfl) ⟨209093, by rfl⟩ : syracuseStep 1115165 = 418187) (by norm_num)
theorem B4523093 : Blo 782338 4523093 := bbase (se 8 (by rfl) ⟨26502, by rfl⟩ : syracuseStep 4523093 = 53005) (by norm_num)
theorem B1115245 : Blo 782338 1115245 := bbase (se 3 (by rfl) ⟨209108, by rfl⟩ : syracuseStep 1115245 = 418217) (by norm_num)
theorem B5014709 : Blo 782338 5014709 := bbase (se 5 (by rfl) ⟨235064, by rfl⟩ : syracuseStep 5014709 = 470129) (by norm_num)
theorem B1115365 : Blo 782338 1115365 := bbase (se 4 (by rfl) ⟨104565, by rfl⟩ : syracuseStep 1115365 = 209131) (by norm_num)
theorem B2983189 : Blo 782338 2983189 := bbase (se 6 (by rfl) ⟨69918, by rfl⟩ : syracuseStep 2983189 = 139837) (by norm_num)
theorem B3966245 : Blo 782338 3966245 := bbase (se 4 (by rfl) ⟨371835, by rfl⟩ : syracuseStep 3966245 = 743671) (by norm_num)
theorem B1672501 : Blo 782338 1672501 := bbase (se 5 (by rfl) ⟨78398, by rfl⟩ : syracuseStep 1672501 = 156797) (by norm_num)
theorem B1115461 : Blo 782338 1115461 := bbase (se 4 (by rfl) ⟨104574, by rfl⟩ : syracuseStep 1115461 = 209149) (by norm_num)
theorem B1672645 : Blo 782338 1672645 := bbase (se 4 (by rfl) ⟨156810, by rfl⟩ : syracuseStep 1672645 = 313621) (by norm_num)
theorem B3179989 : Blo 782338 3179989 := bbase (se 7 (by rfl) ⟨37265, by rfl⟩ : syracuseStep 3179989 = 74531) (by norm_num)
theorem B1050085 : Blo 782338 1050085 := bbase (se 4 (by rfl) ⟨98445, by rfl⟩ : syracuseStep 1050085 = 196891) (by norm_num)
theorem B2983493 : Blo 782338 2983493 := bbase (se 4 (by rfl) ⟨279702, by rfl⟩ : syracuseStep 2983493 = 559405) (by norm_num)
theorem B2819765 : Blo 782338 2819765 := bbase (se 5 (by rfl) ⟨132176, by rfl⟩ : syracuseStep 2819765 = 264353) (by norm_num)
theorem B2623205 : Blo 782338 2623205 := bbase (se 4 (by rfl) ⟨245925, by rfl⟩ : syracuseStep 2623205 = 491851) (by norm_num)
theorem B1410805 : Blo 782338 1410805 := bbase (se 5 (by rfl) ⟨66131, by rfl⟩ : syracuseStep 1410805 = 132263) (by norm_num)
theorem B1115957 : Blo 782338 1115957 := bbase (se 5 (by rfl) ⟨52310, by rfl⟩ : syracuseStep 1115957 = 104621) (by norm_num)
theorem B1673021 : Blo 782338 1673021 := bbase (se 3 (by rfl) ⟨313691, by rfl⟩ : syracuseStep 1673021 = 627383) (by norm_num)
theorem B6686549 : Blo 782338 6686549 := bbase (se 9 (by rfl) ⟨19589, by rfl⟩ : syracuseStep 6686549 = 39179) (by norm_num)
theorem B1509421 : Blo 782338 1509421 := bbase (se 3 (by rfl) ⟨283016, by rfl⟩ : syracuseStep 1509421 = 566033) (by norm_num)
theorem B2820197 : Blo 782338 2820197 := bbase (se 4 (by rfl) ⟨264393, by rfl⟩ : syracuseStep 2820197 = 528787) (by norm_num)
theorem B1673389 : Blo 782338 1673389 := bbase (se 3 (by rfl) ⟨313760, by rfl⟩ : syracuseStep 1673389 = 627521) (by norm_num)
theorem B1116509 : Blo 782338 1116509 := bbase (se 3 (by rfl) ⟨209345, by rfl⟩ : syracuseStep 1116509 = 418691) (by norm_num)
theorem B1018217 : Blo 782338 1018217 := bbase (se 2 (by rfl) ⟨381831, by rfl⟩ : syracuseStep 1018217 = 763663) (by norm_num)
theorem B8063381 : Blo 782338 8063381 := bbase (se 6 (by rfl) ⟨188985, by rfl⟩ : syracuseStep 8063381 = 377971) (by norm_num)
theorem B2263477 : Blo 782338 2263477 := bbase (se 5 (by rfl) ⟨106100, by rfl⟩ : syracuseStep 2263477 = 212201) (by norm_num)
theorem B1411525 : Blo 782338 1411525 := bbase (se 4 (by rfl) ⟨132330, by rfl⟩ : syracuseStep 1411525 = 264661) (by norm_num)
theorem B3574277 : Blo 782338 3574277 := bbase (se 4 (by rfl) ⟨335088, by rfl⟩ : syracuseStep 3574277 = 670177) (by norm_num)
theorem B3967541 : Blo 782338 3967541 := bbase (se 5 (by rfl) ⟨185978, by rfl⟩ : syracuseStep 3967541 = 371957) (by norm_num)
theorem B1608317 : Blo 782338 1608317 := bbase (se 3 (by rfl) ⟨301559, by rfl⟩ : syracuseStep 1608317 = 603119) (by norm_num)
theorem B3181189 : Blo 782338 3181189 := bbase (se 4 (by rfl) ⟨298236, by rfl⟩ : syracuseStep 3181189 = 596473) (by norm_num)
theorem B4459157 : Blo 782338 4459157 := bbase (se 6 (by rfl) ⟨104511, by rfl⟩ : syracuseStep 4459157 = 209023) (by norm_num)
theorem B8915669 : Blo 782338 8915669 := bbase (se 7 (by rfl) ⟨104480, by rfl⟩ : syracuseStep 8915669 = 208961) (by norm_num)
theorem B2722693 : Blo 782338 2722693 := bbase (se 4 (by rfl) ⟨255252, by rfl⟩ : syracuseStep 2722693 = 510505) (by norm_num)
theorem B2231333 : Blo 782338 2231333 := bbase (se 4 (by rfl) ⟨209187, by rfl⟩ : syracuseStep 2231333 = 418375) (by norm_num)
theorem B1117261 : Blo 782338 1117261 := bbase (se 3 (by rfl) ⟨209486, by rfl⟩ : syracuseStep 1117261 = 418973) (by norm_num)
theorem B2821205 : Blo 782338 2821205 := bbase (se 8 (by rfl) ⟨16530, by rfl⟩ : syracuseStep 2821205 = 33061) (by norm_num)
theorem B1412333 : Blo 782338 1412333 := bbase (se 3 (by rfl) ⟨264812, by rfl⟩ : syracuseStep 1412333 = 529625) (by norm_num)
theorem B953749 : Blo 782338 953749 := bbase (se 6 (by rfl) ⟨22353, by rfl⟩ : syracuseStep 953749 = 44707) (by norm_num)
theorem B2035109 : Blo 782338 2035109 := bbase (se 4 (by rfl) ⟨190791, by rfl⟩ : syracuseStep 2035109 = 381583) (by norm_num)
theorem B1609205 : Blo 782338 1609205 := bbase (se 5 (by rfl) ⟨75431, by rfl⟩ : syracuseStep 1609205 = 150863) (by norm_num)
theorem B3018293 : Blo 782338 3018293 := bbase (se 5 (by rfl) ⟨141482, by rfl⟩ : syracuseStep 3018293 = 282965) (by norm_num)
theorem B2985605 : Blo 782338 2985605 := bbase (se 4 (by rfl) ⟨279900, by rfl⟩ : syracuseStep 2985605 = 559801) (by norm_num)
theorem B1674893 : Blo 782338 1674893 := bbase (se 3 (by rfl) ⟨314042, by rfl⟩ : syracuseStep 1674893 = 628085) (by norm_num)
theorem B1675037 : Blo 782338 1675037 := bbase (se 3 (by rfl) ⟨314069, by rfl⟩ : syracuseStep 1675037 = 628139) (by norm_num)
theorem B5639989 : Blo 782338 5639989 := bbase (se 5 (by rfl) ⟨264374, by rfl⟩ : syracuseStep 5639989 = 528749) (by norm_num)
theorem B3968837 : Blo 782338 3968837 := bbase (se 4 (by rfl) ⟨372078, by rfl⟩ : syracuseStep 3968837 = 744157) (by norm_num)
theorem B1118053 : Blo 782338 1118053 := bbase (se 4 (by rfl) ⟨104817, by rfl⟩ : syracuseStep 1118053 = 209635) (by norm_num)
theorem B1675397 : Blo 782338 1675397 := bbase (se 4 (by rfl) ⟨157068, by rfl⟩ : syracuseStep 1675397 = 314137) (by norm_num)
theorem B3772565 : Blo 782338 3772565 := bbase (se 6 (by rfl) ⟨88419, by rfl⟩ : syracuseStep 3772565 = 176839) (by norm_num)
theorem B1118389 : Blo 782338 1118389 := bbase (se 5 (by rfl) ⟨52424, by rfl⟩ : syracuseStep 1118389 = 104849) (by norm_num)
theorem B2232517 : Blo 782338 2232517 := bbase (se 4 (by rfl) ⟨209298, by rfl⟩ : syracuseStep 2232517 = 418597) (by norm_num)
theorem B3772757 : Blo 782338 3772757 := bbase (se 10 (by rfl) ⟨5526, by rfl⟩ : syracuseStep 3772757 = 11053) (by norm_num)
theorem B2232677 : Blo 782338 2232677 := bbase (se 4 (by rfl) ⟨209313, by rfl⟩ : syracuseStep 2232677 = 418627) (by norm_num)
theorem B1118605 : Blo 782338 1118605 := bbase (se 3 (by rfl) ⟨209738, by rfl⟩ : syracuseStep 1118605 = 419477) (by norm_num)
theorem B2232917 : Blo 782338 2232917 := bbase (se 8 (by rfl) ⟨13083, by rfl⟩ : syracuseStep 2232917 = 26167) (by norm_num)
theorem B5968565 : Blo 782338 5968565 := bbase (se 5 (by rfl) ⟨279776, by rfl⟩ : syracuseStep 5968565 = 559553) (by norm_num)
theorem B3773141 : Blo 782338 3773141 := bbase (se 7 (by rfl) ⟨44216, by rfl⟩ : syracuseStep 3773141 = 88433) (by norm_num)
theorem B3347189 : Blo 782338 3347189 := bbase (se 5 (by rfl) ⟨156899, by rfl⟩ : syracuseStep 3347189 = 313799) (by norm_num)
theorem B1118981 : Blo 782338 1118981 := bbase (se 4 (by rfl) ⟨104904, by rfl⟩ : syracuseStep 1118981 = 209809) (by norm_num)
theorem B2233109 : Blo 782338 2233109 := bbase (se 6 (by rfl) ⟨52338, by rfl⟩ : syracuseStep 2233109 = 104677) (by norm_num)
theorem B1413941 : Blo 782338 1413941 := bbase (se 5 (by rfl) ⟨66278, by rfl⟩ : syracuseStep 1413941 = 132557) (by norm_num)
theorem B1676285 : Blo 782338 1676285 := bbase (se 3 (by rfl) ⟨314303, by rfl⟩ : syracuseStep 1676285 = 628607) (by norm_num)
theorem B3347477 : Blo 782338 3347477 := bbase (se 6 (by rfl) ⟨78456, by rfl⟩ : syracuseStep 3347477 = 156913) (by norm_num)
theorem B3970133 : Blo 782338 3970133 := bbase (se 8 (by rfl) ⟨23262, by rfl⟩ : syracuseStep 3970133 = 46525) (by norm_num)
theorem B1676533 : Blo 782338 1676533 := bbase (se 5 (by rfl) ⟨78587, by rfl⟩ : syracuseStep 1676533 = 157175) (by norm_num)
theorem B1512869 : Blo 782338 1512869 := bbase (se 4 (by rfl) ⟨141831, by rfl⟩ : syracuseStep 1512869 = 283663) (by norm_num)
theorem B1414597 : Blo 782338 1414597 := bbase (se 4 (by rfl) ⟨132618, by rfl⟩ : syracuseStep 1414597 = 265237) (by norm_num)
theorem B1677037 : Blo 782338 1677037 := bbase (se 3 (by rfl) ⟨314444, by rfl⟩ : syracuseStep 1677037 = 628889) (by norm_num)
theorem B2234101 : Blo 782338 2234101 := bbase (se 5 (by rfl) ⟨104723, by rfl⟩ : syracuseStep 2234101 = 209447) (by norm_num)
theorem B3348229 : Blo 782338 3348229 := bbase (se 4 (by rfl) ⟨313896, by rfl⟩ : syracuseStep 3348229 = 627793) (by norm_num)
theorem B9050069 : Blo 782338 9050069 := bbase (se 7 (by rfl) ⟨106055, by rfl⟩ : syracuseStep 9050069 = 212111) (by norm_num)
theorem B1415389 : Blo 782338 1415389 := bbase (se 3 (by rfl) ⟨265385, by rfl⟩ : syracuseStep 1415389 = 530771) (by norm_num)
theorem B3971429 : Blo 782338 3971429 := bbase (se 4 (by rfl) ⟨372321, by rfl⟩ : syracuseStep 3971429 = 744643) (by norm_num)
theorem B3578309 : Blo 782338 3578309 := bbase (se 4 (by rfl) ⟨335466, by rfl⟩ : syracuseStep 3578309 = 670933) (by norm_num)
theorem B3348965 : Blo 782338 3348965 := bbase (se 4 (by rfl) ⟨313965, by rfl⟩ : syracuseStep 3348965 = 627931) (by norm_num)
theorem B1677925 : Blo 782338 1677925 := bbase (se 4 (by rfl) ⟨157305, by rfl⟩ : syracuseStep 1677925 = 314611) (by norm_num)
theorem B2235205 : Blo 782338 2235205 := bbase (se 4 (by rfl) ⟨209550, by rfl⟩ : syracuseStep 2235205 = 419101) (by norm_num)
theorem B957305 : Blo 782338 957305 := bbase (se 2 (by rfl) ⟨358989, by rfl⟩ : syracuseStep 957305 = 717979) (by norm_num)
theorem B1416197 : Blo 782338 1416197 := bbase (se 4 (by rfl) ⟨132768, by rfl⟩ : syracuseStep 1416197 = 265537) (by norm_num)
theorem B990245 : Blo 782338 990245 := bbase (se 4 (by rfl) ⟨92835, by rfl⟩ : syracuseStep 990245 = 185671) (by norm_num)
theorem B1678421 : Blo 782338 1678421 := bbase (se 8 (by rfl) ⟨9834, by rfl⟩ : syracuseStep 1678421 = 19669) (by norm_num)
theorem B990301 : Blo 782338 990301 := bbase (se 3 (by rfl) ⟨185681, by rfl⟩ : syracuseStep 990301 = 371363) (by norm_num)
theorem B859229 : Blo 782338 859229 := bbase (se 3 (by rfl) ⟨161105, by rfl⟩ : syracuseStep 859229 = 322211) (by norm_num)
theorem B1416341 : Blo 782338 1416341 := bbase (se 6 (by rfl) ⟨33195, by rfl⟩ : syracuseStep 1416341 = 66391) (by norm_num)
theorem B990397 : Blo 782338 990397 := bbase (se 3 (by rfl) ⟨185699, by rfl⟩ : syracuseStep 990397 = 371399) (by norm_num)
theorem B990569 : Blo 782338 990569 := bbase (se 2 (by rfl) ⟨371463, by rfl⟩ : syracuseStep 990569 = 742927) (by norm_num)
theorem B990625 : Blo 782338 990625 := bbase (se 2 (by rfl) ⟨371484, by rfl⟩ : syracuseStep 990625 = 742969) (by norm_num)
theorem B990721 : Blo 782338 990721 := bbase (se 2 (by rfl) ⟨371520, by rfl⟩ : syracuseStep 990721 = 743041) (by norm_num)
theorem B2039357 : Blo 782338 2039357 := bbase (se 3 (by rfl) ⟨382379, by rfl⟩ : syracuseStep 2039357 = 764759) (by norm_num)
theorem B3972725 : Blo 782338 3972725 := bbase (se 5 (by rfl) ⟨186221, by rfl⟩ : syracuseStep 3972725 = 372443) (by norm_num)
theorem B990893 : Blo 782338 990893 := bbase (se 3 (by rfl) ⟨185792, by rfl⟩ : syracuseStep 990893 = 371585) (by norm_num)
theorem B990949 : Blo 782338 990949 := bbase (se 4 (by rfl) ⟨92901, by rfl⟩ : syracuseStep 990949 = 185803) (by norm_num)
theorem B794381 : Blo 782338 794381 := bbase (se 3 (by rfl) ⟨148946, by rfl⟩ : syracuseStep 794381 = 297893) (by norm_num)
theorem B794413 : Blo 782338 794413 := bbase (se 3 (by rfl) ⟨148952, by rfl⟩ : syracuseStep 794413 = 297905) (by norm_num)
theorem B991045 : Blo 782338 991045 := bbase (se 4 (by rfl) ⟨92910, by rfl⟩ : syracuseStep 991045 = 185821) (by norm_num)
theorem B892849 : Blo 782338 892849 := bbase (se 2 (by rfl) ⟨334818, by rfl⟩ : syracuseStep 892849 = 669637) (by norm_num)
theorem B1679309 : Blo 782338 1679309 := bbase (se 3 (by rfl) ⟨314870, by rfl⟩ : syracuseStep 1679309 = 629741) (by norm_num)
theorem B991217 : Blo 782338 991217 := bbase (se 2 (by rfl) ⟨371706, by rfl⟩ : syracuseStep 991217 = 743413) (by norm_num)
theorem B991273 : Blo 782338 991273 := bbase (se 2 (by rfl) ⟨371727, by rfl⟩ : syracuseStep 991273 = 743455) (by norm_num)
theorem B1253485 : Blo 782338 1253485 := bbase (se 3 (by rfl) ⟨235028, by rfl⟩ : syracuseStep 1253485 = 470057) (by norm_num)
theorem B991369 : Blo 782338 991369 := bbase (se 2 (by rfl) ⟨371763, by rfl⟩ : syracuseStep 991369 = 743527) (by norm_num)
theorem B10035413 : Blo 782338 10035413 := bbase (se 7 (by rfl) ⟨117602, by rfl⟩ : syracuseStep 10035413 = 235205) (by norm_num)
theorem B2236709 : Blo 782338 2236709 := bbase (se 4 (by rfl) ⟨209691, by rfl⟩ : syracuseStep 2236709 = 419383) (by norm_num)
theorem B991541 : Blo 782338 991541 := bbase (se 5 (by rfl) ⟨46478, by rfl⟩ : syracuseStep 991541 = 92957) (by norm_num)
theorem B991597 : Blo 782338 991597 := bbase (se 3 (by rfl) ⟨185924, by rfl⟩ : syracuseStep 991597 = 371849) (by norm_num)
theorem B991693 : Blo 782338 991693 := bbase (se 3 (by rfl) ⟨185942, by rfl⟩ : syracuseStep 991693 = 371885) (by norm_num)
theorem B6365749 : Blo 782338 6365749 := bbase (se 5 (by rfl) ⟨298394, by rfl⟩ : syracuseStep 6365749 = 596789) (by norm_num)
theorem B2040437 : Blo 782338 2040437 := bbase (se 5 (by rfl) ⟨95645, by rfl⟩ : syracuseStep 2040437 = 191291) (by norm_num)
theorem B991865 : Blo 782338 991865 := bbase (se 2 (by rfl) ⟨371949, by rfl⟩ : syracuseStep 991865 = 743899) (by norm_num)
theorem B991921 : Blo 782338 991921 := bbase (se 2 (by rfl) ⟨371970, by rfl⟩ : syracuseStep 991921 = 743941) (by norm_num)
theorem B1614557 : Blo 782338 1614557 := bbase (se 3 (by rfl) ⟨302729, by rfl⟩ : syracuseStep 1614557 = 605459) (by norm_num)
theorem B992017 : Blo 782338 992017 := bbase (se 2 (by rfl) ⟨372006, by rfl⟩ : syracuseStep 992017 = 744013) (by norm_num)
theorem B3974021 : Blo 782338 3974021 := bbase (se 4 (by rfl) ⟨372564, by rfl⟩ : syracuseStep 3974021 = 745129) (by norm_num)
theorem B1057693 : Blo 782338 1057693 := bbase (se 3 (by rfl) ⟨198317, by rfl⟩ : syracuseStep 1057693 = 396635) (by norm_num)
theorem B3777445 : Blo 782338 3777445 := bbase (se 4 (by rfl) ⟨354135, by rfl⟩ : syracuseStep 3777445 = 708271) (by norm_num)
theorem B992189 : Blo 782338 992189 := bbase (se 3 (by rfl) ⟨186035, by rfl⟩ : syracuseStep 992189 = 372071) (by norm_num)
theorem B893921 : Blo 782338 893921 := bbase (se 2 (by rfl) ⟨335220, by rfl⟩ : syracuseStep 893921 = 670441) (by norm_num)
theorem B992245 : Blo 782338 992245 := bbase (se 5 (by rfl) ⟨46511, by rfl⟩ : syracuseStep 992245 = 93023) (by norm_num)
theorem B992341 : Blo 782338 992341 := bbase (se 8 (by rfl) ⟨5814, by rfl⟩ : syracuseStep 992341 = 11629) (by norm_num)
theorem B1057909 : Blo 782338 1057909 := bbase (se 5 (by rfl) ⟨49589, by rfl⟩ : syracuseStep 1057909 = 99179) (by norm_num)
theorem B795893 : Blo 782338 795893 := bbase (se 5 (by rfl) ⟨37307, by rfl⟩ : syracuseStep 795893 = 74615) (by norm_num)
theorem B992513 : Blo 782338 992513 := bbase (se 2 (by rfl) ⟨372192, by rfl⟩ : syracuseStep 992513 = 744385) (by norm_num)
theorem B1320205 : Blo 782338 1320205 := bbase (se 3 (by rfl) ⟨247538, by rfl⟩ : syracuseStep 1320205 = 495077) (by norm_num)
theorem B992569 : Blo 782338 992569 := bbase (se 2 (by rfl) ⟨372213, by rfl⟩ : syracuseStep 992569 = 744427) (by norm_num)
theorem B1320293 : Blo 782338 1320293 := bbase (se 4 (by rfl) ⟨123777, by rfl⟩ : syracuseStep 1320293 = 247555) (by norm_num)
theorem B4760981 : Blo 782338 4760981 := bbase (se 6 (by rfl) ⟨111585, by rfl⟩ : syracuseStep 4760981 = 223171) (by norm_num)
theorem B992665 : Blo 782338 992665 := bbase (se 2 (by rfl) ⟨372249, by rfl⟩ : syracuseStep 992665 = 744499) (by norm_num)
theorem B1254869 : Blo 782338 1254869 := bbase (se 7 (by rfl) ⟨14705, by rfl⟩ : syracuseStep 1254869 = 29411) (by norm_num)
theorem B1320421 : Blo 782338 1320421 := bbase (se 4 (by rfl) ⟨123789, by rfl⟩ : syracuseStep 1320421 = 247579) (by norm_num)
theorem B2827781 : Blo 782338 2827781 := bbase (se 4 (by rfl) ⟨265104, by rfl⟩ : syracuseStep 2827781 = 530209) (by norm_num)
theorem B1320509 : Blo 782338 1320509 := bbase (se 3 (by rfl) ⟨247595, by rfl⟩ : syracuseStep 1320509 = 495191) (by norm_num)
theorem B992837 : Blo 782338 992837 := bbase (se 4 (by rfl) ⟨93078, by rfl⟩ : syracuseStep 992837 = 186157) (by norm_num)
theorem B4761173 : Blo 782338 4761173 := bbase (se 8 (by rfl) ⟨27897, by rfl⟩ : syracuseStep 4761173 = 55795) (by norm_num)
theorem B6530645 : Blo 782338 6530645 := bbase (se 8 (by rfl) ⟨38265, by rfl⟩ : syracuseStep 6530645 = 76531) (by norm_num)
theorem B992893 : Blo 782338 992893 := bbase (se 3 (by rfl) ⟨186167, by rfl⟩ : syracuseStep 992893 = 372335) (by norm_num)
theorem B1255061 : Blo 782338 1255061 := bbase (se 6 (by rfl) ⟨29415, by rfl⟩ : syracuseStep 1255061 = 58831) (by norm_num)
theorem B1320637 : Blo 782338 1320637 := bbase (se 3 (by rfl) ⟨247619, by rfl⟩ : syracuseStep 1320637 = 495239) (by norm_num)
theorem B3352261 : Blo 782338 3352261 := bbase (se 4 (by rfl) ⟨314274, by rfl⟩ : syracuseStep 3352261 = 628549) (by norm_num)
theorem B992989 : Blo 782338 992989 := bbase (se 3 (by rfl) ⟨186185, by rfl⟩ : syracuseStep 992989 = 372371) (by norm_num)
theorem B1320725 : Blo 782338 1320725 := bbase (se 6 (by rfl) ⟨30954, by rfl⟩ : syracuseStep 1320725 = 61909) (by norm_num)
theorem B829225 : Blo 782338 829225 := bbase (se 2 (by rfl) ⟨310959, by rfl⟩ : syracuseStep 829225 = 621919) (by norm_num)
theorem B2238293 : Blo 782338 2238293 := bbase (se 9 (by rfl) ⟨6557, by rfl⟩ : syracuseStep 2238293 = 13115) (by norm_num)
theorem B993161 : Blo 782338 993161 := bbase (se 2 (by rfl) ⟨372435, by rfl⟩ : syracuseStep 993161 = 744871) (by norm_num)
theorem B1320853 : Blo 782338 1320853 := bbase (se 6 (by rfl) ⟨30957, by rfl⟩ : syracuseStep 1320853 = 61915) (by norm_num)
theorem B993217 : Blo 782338 993217 := bbase (se 2 (by rfl) ⟨372456, by rfl⟩ : syracuseStep 993217 = 744913) (by norm_num)
theorem B1320941 : Blo 782338 1320941 := bbase (se 3 (by rfl) ⟨247676, by rfl⟩ : syracuseStep 1320941 = 495353) (by norm_num)
theorem B993313 : Blo 782338 993313 := bbase (se 2 (by rfl) ⟨372492, by rfl⟩ : syracuseStep 993313 = 744985) (by norm_num)
theorem B2828357 : Blo 782338 2828357 := bbase (se 4 (by rfl) ⟨265158, by rfl⟩ : syracuseStep 2828357 = 530317) (by norm_num)
theorem B1321069 : Blo 782338 1321069 := bbase (se 3 (by rfl) ⟨247700, by rfl⟩ : syracuseStep 1321069 = 495401) (by norm_num)
theorem B3975317 : Blo 782338 3975317 := bbase (se 6 (by rfl) ⟨93171, by rfl⟩ : syracuseStep 3975317 = 186343) (by norm_num)
theorem B1321157 : Blo 782338 1321157 := bbase (se 4 (by rfl) ⟨123858, by rfl⟩ : syracuseStep 1321157 = 247717) (by norm_num)
theorem B993485 : Blo 782338 993485 := bbase (se 3 (by rfl) ⟨186278, by rfl⟩ : syracuseStep 993485 = 372557) (by norm_num)
theorem B3221765 : Blo 782338 3221765 := bbase (se 4 (by rfl) ⟨302040, by rfl⟩ : syracuseStep 3221765 = 604081) (by norm_num)
theorem B993541 : Blo 782338 993541 := bbase (se 4 (by rfl) ⟨93144, by rfl⟩ : syracuseStep 993541 = 186289) (by norm_num)
theorem B1321285 : Blo 782338 1321285 := bbase (se 4 (by rfl) ⟨123870, by rfl⟩ : syracuseStep 1321285 = 247741) (by norm_num)
theorem B993637 : Blo 782338 993637 := bbase (se 4 (by rfl) ⟨93153, by rfl⟩ : syracuseStep 993637 = 186307) (by norm_num)
theorem B1321373 : Blo 782338 1321373 := bbase (se 3 (by rfl) ⟨247757, by rfl⟩ : syracuseStep 1321373 = 495515) (by norm_num)
theorem B1550765 : Blo 782338 1550765 := bbase (se 3 (by rfl) ⟨290768, by rfl⟩ : syracuseStep 1550765 = 581537) (by norm_num)
theorem B895421 : Blo 782338 895421 := bbase (se 3 (by rfl) ⟨167891, by rfl⟩ : syracuseStep 895421 = 335783) (by norm_num)
theorem B11446741 : Blo 782338 11446741 := bbase (se 7 (by rfl) ⟨134141, by rfl⟩ : syracuseStep 11446741 = 268283) (by norm_num)
theorem B2238965 : Blo 782338 2238965 := bbase (se 5 (by rfl) ⟨104951, by rfl⟩ : syracuseStep 2238965 = 209903) (by norm_num)
theorem B993809 : Blo 782338 993809 := bbase (se 2 (by rfl) ⟨372678, by rfl⟩ : syracuseStep 993809 = 745357) (by norm_num)
theorem B4467221 : Blo 782338 4467221 := bbase (se 6 (by rfl) ⟨104700, by rfl⟩ : syracuseStep 4467221 = 209401) (by norm_num)
theorem B1321501 : Blo 782338 1321501 := bbase (se 3 (by rfl) ⟨247781, by rfl⟩ : syracuseStep 1321501 = 495563) (by norm_num)
theorem B993865 : Blo 782338 993865 := bbase (se 2 (by rfl) ⟨372699, by rfl⟩ : syracuseStep 993865 = 745399) (by norm_num)
theorem B3025493 : Blo 782338 3025493 := bbase (se 8 (by rfl) ⟨17727, by rfl⟩ : syracuseStep 3025493 = 35455) (by norm_num)
theorem B1321589 : Blo 782338 1321589 := bbase (se 5 (by rfl) ⟨61949, by rfl⟩ : syracuseStep 1321589 = 123899) (by norm_num)
theorem B993961 : Blo 782338 993961 := bbase (se 2 (by rfl) ⟨372735, by rfl⟩ : syracuseStep 993961 = 745471) (by norm_num)
theorem B1321717 : Blo 782338 1321717 := bbase (se 5 (by rfl) ⟨61955, by rfl⟩ : syracuseStep 1321717 = 123911) (by norm_num)
theorem B1321805 : Blo 782338 1321805 := bbase (se 3 (by rfl) ⟨247838, by rfl⟩ : syracuseStep 1321805 = 495677) (by norm_num)
theorem B994133 : Blo 782338 994133 := bbase (se 9 (by rfl) ⟨2912, by rfl⟩ : syracuseStep 994133 = 5825) (by norm_num)
theorem B994189 : Blo 782338 994189 := bbase (se 3 (by rfl) ⟨186410, by rfl⟩ : syracuseStep 994189 = 372821) (by norm_num)
theorem B1256381 : Blo 782338 1256381 := bbase (se 3 (by rfl) ⟨235571, by rfl⟩ : syracuseStep 1256381 = 471143) (by norm_num)
theorem B1321933 : Blo 782338 1321933 := bbase (se 3 (by rfl) ⟨247862, by rfl⟩ : syracuseStep 1321933 = 495725) (by norm_num)
theorem B994285 : Blo 782338 994285 := bbase (se 3 (by rfl) ⟨186428, by rfl⟩ : syracuseStep 994285 = 372857) (by norm_num)
theorem B1256477 : Blo 782338 1256477 := bbase (se 3 (by rfl) ⟨235589, by rfl⟩ : syracuseStep 1256477 = 471179) (by norm_num)
theorem B1322021 : Blo 782338 1322021 := bbase (se 4 (by rfl) ⟨123939, by rfl⟩ : syracuseStep 1322021 = 247879) (by norm_num)
theorem B1485877 : Blo 782338 1485877 := bbase (se 5 (by rfl) ⟨69650, by rfl⟩ : syracuseStep 1485877 = 139301) (by norm_num)
theorem B1256509 : Blo 782338 1256509 := bbase (se 3 (by rfl) ⟨235595, by rfl⟩ : syracuseStep 1256509 = 471191) (by norm_num)
theorem B994457 : Blo 782338 994457 := bbase (se 2 (by rfl) ⟨372921, by rfl⟩ : syracuseStep 994457 = 745843) (by norm_num)
theorem B1322149 : Blo 782338 1322149 := bbase (se 4 (by rfl) ⟨123951, by rfl⟩ : syracuseStep 1322149 = 247903) (by norm_num)
theorem B1486021 : Blo 782338 1486021 := bbase (se 4 (by rfl) ⟨139314, by rfl⟩ : syracuseStep 1486021 = 278629) (by norm_num)
theorem B2829509 : Blo 782338 2829509 := bbase (se 4 (by rfl) ⟨265266, by rfl⟩ : syracuseStep 2829509 = 530533) (by norm_num)
theorem B994513 : Blo 782338 994513 := bbase (se 2 (by rfl) ⟨372942, by rfl⟩ : syracuseStep 994513 = 745885) (by norm_num)
theorem B1322237 : Blo 782338 1322237 := bbase (se 3 (by rfl) ⟨247919, by rfl⟩ : syracuseStep 1322237 = 495839) (by norm_num)
theorem B994609 : Blo 782338 994609 := bbase (se 2 (by rfl) ⟨372978, by rfl⟩ : syracuseStep 994609 = 745957) (by norm_num)
theorem B4828501 : Blo 782338 4828501 := bbase (se 11 (by rfl) ⟨3536, by rfl⟩ : syracuseStep 4828501 = 7073) (by norm_num)
theorem B1486181 : Blo 782338 1486181 := bbase (se 4 (by rfl) ⟨139329, by rfl⟩ : syracuseStep 1486181 = 278659) (by norm_num)
theorem B896369 : Blo 782338 896369 := bbase (se 2 (by rfl) ⟨336138, by rfl⟩ : syracuseStep 896369 = 672277) (by norm_num)
theorem B1322365 : Blo 782338 1322365 := bbase (se 3 (by rfl) ⟨247943, by rfl⟩ : syracuseStep 1322365 = 495887) (by norm_num)
theorem B3976613 : Blo 782338 3976613 := bbase (se 4 (by rfl) ⟨372807, by rfl⟩ : syracuseStep 3976613 = 745615) (by norm_num)
theorem B1191365 : Blo 782338 1191365 := bbase (se 4 (by rfl) ⟨111690, by rfl⟩ : syracuseStep 1191365 = 223381) (by norm_num)
theorem B1322453 : Blo 782338 1322453 := bbase (se 7 (by rfl) ⟨15497, by rfl⟩ : syracuseStep 1322453 = 30995) (by norm_num)
theorem B994781 : Blo 782338 994781 := bbase (se 3 (by rfl) ⟨186521, by rfl⟩ : syracuseStep 994781 = 373043) (by norm_num)
theorem B1486325 : Blo 782338 1486325 := bbase (se 5 (by rfl) ⟨69671, by rfl⟩ : syracuseStep 1486325 = 139343) (by norm_num)
theorem B994837 : Blo 782338 994837 := bbase (se 6 (by rfl) ⟨23316, by rfl⟩ : syracuseStep 994837 = 46633) (by norm_num)
theorem B1322581 : Blo 782338 1322581 := bbase (se 8 (by rfl) ⟨7749, by rfl⟩ : syracuseStep 1322581 = 15499) (by norm_num)
theorem B994933 : Blo 782338 994933 := bbase (se 5 (by rfl) ⟨46637, by rfl⟩ : syracuseStep 994933 = 93275) (by norm_num)
theorem B1322669 : Blo 782338 1322669 := bbase (se 3 (by rfl) ⟨248000, by rfl⟩ : syracuseStep 1322669 = 496001) (by norm_num)
theorem B4468405 : Blo 782338 4468405 := bbase (se 5 (by rfl) ⟨209456, by rfl⟩ : syracuseStep 4468405 = 418913) (by norm_num)
theorem B1486613 : Blo 782338 1486613 := bbase (se 6 (by rfl) ⟨34842, by rfl⟩ : syracuseStep 1486613 = 69685) (by norm_num)
theorem B995105 : Blo 782338 995105 := bbase (se 2 (by rfl) ⟨373164, by rfl⟩ : syracuseStep 995105 = 746329) (by norm_num)
theorem B1322797 : Blo 782338 1322797 := bbase (se 3 (by rfl) ⟨248024, by rfl⟩ : syracuseStep 1322797 = 496049) (by norm_num)
theorem B2862917 : Blo 782338 2862917 := bbase (se 4 (by rfl) ⟨268398, by rfl⟩ : syracuseStep 2862917 = 536797) (by norm_num)
theorem B995161 : Blo 782338 995161 := bbase (se 2 (by rfl) ⟨373185, by rfl⟩ : syracuseStep 995161 = 746371) (by norm_num)
theorem B1322885 : Blo 782338 1322885 := bbase (se 4 (by rfl) ⟨124020, by rfl⟩ : syracuseStep 1322885 = 248041) (by norm_num)
theorem B1879949 : Blo 782338 1879949 := bbase (se 3 (by rfl) ⟨352490, by rfl⟩ : syracuseStep 1879949 = 704981) (by norm_num)
theorem B1486765 : Blo 782338 1486765 := bbase (se 3 (by rfl) ⟨278768, by rfl⟩ : syracuseStep 1486765 = 557537) (by norm_num)
theorem B1323013 : Blo 782338 1323013 := bbase (se 4 (by rfl) ⟨124032, by rfl⟩ : syracuseStep 1323013 = 248065) (by norm_num)
theorem B1323101 : Blo 782338 1323101 := bbase (se 3 (by rfl) ⟨248081, by rfl⟩ : syracuseStep 1323101 = 496163) (by norm_num)
theorem B1192045 : Blo 782338 1192045 := bbase (se 3 (by rfl) ⟨223508, by rfl⟩ : syracuseStep 1192045 = 447017) (by norm_num)
theorem B1880189 : Blo 782338 1880189 := bbase (se 3 (by rfl) ⟨352535, by rfl⟩ : syracuseStep 1880189 = 705071) (by norm_num)
theorem B1487069 : Blo 782338 1487069 := bbase (se 3 (by rfl) ⟨278825, by rfl⟩ : syracuseStep 1487069 = 557651) (by norm_num)
theorem B1323229 : Blo 782338 1323229 := bbase (se 3 (by rfl) ⟨248105, by rfl⟩ : syracuseStep 1323229 = 496211) (by norm_num)
theorem B1323317 : Blo 782338 1323317 := bbase (se 5 (by rfl) ⟨62030, by rfl⟩ : syracuseStep 1323317 = 124061) (by norm_num)
theorem B1323445 : Blo 782338 1323445 := bbase (se 5 (by rfl) ⟨62036, by rfl⟩ : syracuseStep 1323445 = 124073) (by norm_num)
theorem B1323533 : Blo 782338 1323533 := bbase (se 3 (by rfl) ⟨248162, by rfl⟩ : syracuseStep 1323533 = 496325) (by norm_num)
theorem B1258021 : Blo 782338 1258021 := bbase (se 4 (by rfl) ⟨117939, by rfl⟩ : syracuseStep 1258021 = 235879) (by norm_num)
theorem B3355253 : Blo 782338 3355253 := bbase (se 5 (by rfl) ⟨157277, by rfl⟩ : syracuseStep 3355253 = 314555) (by norm_num)
theorem B1323661 : Blo 782338 1323661 := bbase (se 3 (by rfl) ⟨248186, by rfl⟩ : syracuseStep 1323661 = 496373) (by norm_num)
theorem B3977909 : Blo 782338 3977909 := bbase (se 5 (by rfl) ⟨186464, by rfl⟩ : syracuseStep 3977909 = 372929) (by norm_num)
theorem B1323749 : Blo 782338 1323749 := bbase (se 4 (by rfl) ⟨124101, by rfl⟩ : syracuseStep 1323749 = 248203) (by norm_num)
theorem B1913597 : Blo 782338 1913597 := bbase (se 3 (by rfl) ⟨358799, by rfl⟩ : syracuseStep 1913597 = 717599) (by norm_num)
theorem B1323877 : Blo 782338 1323877 := bbase (se 4 (by rfl) ⟨124113, by rfl⟩ : syracuseStep 1323877 = 248227) (by norm_num)
theorem B2831269 : Blo 782338 2831269 := bbase (se 4 (by rfl) ⟨265431, by rfl⟩ : syracuseStep 2831269 = 530863) (by norm_num)
theorem B1323965 : Blo 782338 1323965 := bbase (se 3 (by rfl) ⟨248243, by rfl⟩ : syracuseStep 1323965 = 496487) (by norm_num)
theorem B1487821 : Blo 782338 1487821 := bbase (se 3 (by rfl) ⟨278966, by rfl⟩ : syracuseStep 1487821 = 557933) (by norm_num)
theorem B5026805 : Blo 782338 5026805 := bbase (se 5 (by rfl) ⟨235631, by rfl⟩ : syracuseStep 5026805 = 471263) (by norm_num)
theorem B6042613 : Blo 782338 6042613 := bbase (se 5 (by rfl) ⟨283247, by rfl⟩ : syracuseStep 6042613 = 566495) (by norm_num)
theorem B1324093 : Blo 782338 1324093 := bbase (se 3 (by rfl) ⟨248267, by rfl⟩ : syracuseStep 1324093 = 496535) (by norm_num)
theorem B1487965 : Blo 782338 1487965 := bbase (se 3 (by rfl) ⟨278993, by rfl⟩ : syracuseStep 1487965 = 557987) (by norm_num)
theorem B1324181 : Blo 782338 1324181 := bbase (se 6 (by rfl) ⟨31035, by rfl⟩ : syracuseStep 1324181 = 62071) (by norm_num)
theorem B2831573 : Blo 782338 2831573 := bbase (se 7 (by rfl) ⟨33182, by rfl⟩ : syracuseStep 2831573 = 66365) (by norm_num)
theorem B1258733 : Blo 782338 1258733 := bbase (se 3 (by rfl) ⟨236012, by rfl⟩ : syracuseStep 1258733 = 472025) (by norm_num)
theorem B1488125 : Blo 782338 1488125 := bbase (se 3 (by rfl) ⟨279023, by rfl⟩ : syracuseStep 1488125 = 558047) (by norm_num)
theorem B1324309 : Blo 782338 1324309 := bbase (se 6 (by rfl) ⟨31038, by rfl⟩ : syracuseStep 1324309 = 62077) (by norm_num)
theorem B1062229 : Blo 782338 1062229 := bbase (se 13 (by rfl) ⟨194, by rfl⟩ : syracuseStep 1062229 = 389) (by norm_num)
theorem B1324397 : Blo 782338 1324397 := bbase (se 3 (by rfl) ⟨248324, by rfl⟩ : syracuseStep 1324397 = 496649) (by norm_num)
theorem B1488269 : Blo 782338 1488269 := bbase (se 3 (by rfl) ⟨279050, by rfl⟩ : syracuseStep 1488269 = 558101) (by norm_num)
theorem B1324525 : Blo 782338 1324525 := bbase (se 3 (by rfl) ⟨248348, by rfl⟩ : syracuseStep 1324525 = 496697) (by norm_num)
theorem B1324613 : Blo 782338 1324613 := bbase (se 4 (by rfl) ⟨124182, by rfl⟩ : syracuseStep 1324613 = 248365) (by norm_num)
theorem B3356261 : Blo 782338 3356261 := bbase (se 4 (by rfl) ⟨314649, by rfl⟩ : syracuseStep 3356261 = 629299) (by norm_num)
theorem B4470389 : Blo 782338 4470389 := bbase (se 5 (by rfl) ⟨209549, by rfl⟩ : syracuseStep 4470389 = 419099) (by norm_num)
theorem B6698645 : Blo 782338 6698645 := bbase (se 6 (by rfl) ⟨156999, by rfl⟩ : syracuseStep 6698645 = 313999) (by norm_num)
theorem B1488557 : Blo 782338 1488557 := bbase (se 3 (by rfl) ⟨279104, by rfl⟩ : syracuseStep 1488557 = 558209) (by norm_num)
theorem B1324741 : Blo 782338 1324741 := bbase (se 4 (by rfl) ⟨124194, by rfl⟩ : syracuseStep 1324741 = 248389) (by norm_num)
theorem B1324829 : Blo 782338 1324829 := bbase (se 3 (by rfl) ⟨248405, by rfl⟩ : syracuseStep 1324829 = 496811) (by norm_num)
theorem B1193773 : Blo 782338 1193773 := bbase (se 3 (by rfl) ⟨223832, by rfl⟩ : syracuseStep 1193773 = 447665) (by norm_num)
theorem B1488709 : Blo 782338 1488709 := bbase (se 4 (by rfl) ⟨139566, by rfl⟩ : syracuseStep 1488709 = 279133) (by norm_num)
theorem B1718101 : Blo 782338 1718101 := bbase (se 9 (by rfl) ⟨5033, by rfl⟩ : syracuseStep 1718101 = 10067) (by norm_num)
theorem B1259405 : Blo 782338 1259405 := bbase (se 3 (by rfl) ⟨236138, by rfl⟩ : syracuseStep 1259405 = 472277) (by norm_num)
theorem B5945237 : Blo 782338 5945237 := bbase (se 6 (by rfl) ⟨139341, by rfl⟩ : syracuseStep 5945237 = 278683) (by norm_num)
theorem B1324957 : Blo 782338 1324957 := bbase (se 3 (by rfl) ⟨248429, by rfl⟩ : syracuseStep 1324957 = 496859) (by norm_num)
theorem B3979205 : Blo 782338 3979205 := bbase (se 4 (by rfl) ⟨373050, by rfl⟩ : syracuseStep 3979205 = 746101) (by norm_num)
theorem B1980389 : Blo 782338 1980389 := bbase (se 4 (by rfl) ⟨185661, by rfl⟩ : syracuseStep 1980389 = 371323) (by norm_num)
theorem B1325045 : Blo 782338 1325045 := bbase (se 5 (by rfl) ⟨62111, by rfl⟩ : syracuseStep 1325045 = 124223) (by norm_num)
theorem B1587317 : Blo 782338 1587317 := bbase (se 5 (by rfl) ⟨74405, by rfl⟩ : syracuseStep 1587317 = 148811) (by norm_num)
theorem B1489013 : Blo 782338 1489013 := bbase (se 5 (by rfl) ⟨69797, by rfl⟩ : syracuseStep 1489013 = 139595) (by norm_num)
theorem B1325173 : Blo 782338 1325173 := bbase (se 5 (by rfl) ⟨62117, by rfl⟩ : syracuseStep 1325173 = 124235) (by norm_num)
theorem B1325261 : Blo 782338 1325261 := bbase (se 3 (by rfl) ⟨248486, by rfl⟩ : syracuseStep 1325261 = 496973) (by norm_num)
theorem B1980733 : Blo 782338 1980733 := bbase (se 3 (by rfl) ⟨371387, by rfl⟩ : syracuseStep 1980733 = 742775) (by norm_num)
theorem B1325389 : Blo 782338 1325389 := bbase (se 3 (by rfl) ⟨248510, by rfl⟩ : syracuseStep 1325389 = 497021) (by norm_num)
theorem B1325477 : Blo 782338 1325477 := bbase (se 4 (by rfl) ⟨124263, by rfl⟩ : syracuseStep 1325477 = 248527) (by norm_num)
theorem B1980845 : Blo 782338 1980845 := bbase (se 3 (by rfl) ⟨371408, by rfl⟩ : syracuseStep 1980845 = 742817) (by norm_num)
theorem B1325605 : Blo 782338 1325605 := bbase (se 4 (by rfl) ⟨124275, by rfl⟩ : syracuseStep 1325605 = 248551) (by norm_num)
theorem B1981037 : Blo 782338 1981037 := bbase (se 3 (by rfl) ⟨371444, by rfl⟩ : syracuseStep 1981037 = 742889) (by norm_num)
theorem B1325693 : Blo 782338 1325693 := bbase (se 3 (by rfl) ⟨248567, by rfl⟩ : syracuseStep 1325693 = 497135) (by norm_num)
theorem B1325821 : Blo 782338 1325821 := bbase (se 3 (by rfl) ⟨248591, by rfl⟩ : syracuseStep 1325821 = 497183) (by norm_num)
theorem B1325909 : Blo 782338 1325909 := bbase (se 9 (by rfl) ⟨3884, by rfl⟩ : syracuseStep 1325909 = 7769) (by norm_num)
theorem B1489765 : Blo 782338 1489765 := bbase (se 4 (by rfl) ⟨139665, by rfl⟩ : syracuseStep 1489765 = 279331) (by norm_num)
theorem B7551893 : Blo 782338 7551893 := bbase (se 6 (by rfl) ⟨176997, by rfl⟩ : syracuseStep 7551893 = 353995) (by norm_num)
theorem B1981381 : Blo 782338 1981381 := bbase (se 4 (by rfl) ⟨185754, by rfl⟩ : syracuseStep 1981381 = 371509) (by norm_num)
theorem B1326037 : Blo 782338 1326037 := bbase (se 7 (by rfl) ⟨15539, by rfl⟩ : syracuseStep 1326037 = 31079) (by norm_num)
theorem B1489909 : Blo 782338 1489909 := bbase (se 5 (by rfl) ⟨69839, by rfl⟩ : syracuseStep 1489909 = 139679) (by norm_num)
theorem B1326125 : Blo 782338 1326125 := bbase (se 3 (by rfl) ⟨248648, by rfl⟩ : syracuseStep 1326125 = 497297) (by norm_num)
theorem B1981493 : Blo 782338 1981493 := bbase (se 5 (by rfl) ⟨92882, by rfl⟩ : syracuseStep 1981493 = 185765) (by norm_num)
theorem B1490069 : Blo 782338 1490069 := bbase (se 6 (by rfl) ⟨34923, by rfl⟩ : syracuseStep 1490069 = 69847) (by norm_num)
theorem B1326253 : Blo 782338 1326253 := bbase (se 3 (by rfl) ⟨248672, by rfl⟩ : syracuseStep 1326253 = 497345) (by norm_num)
theorem B1883341 : Blo 782338 1883341 := bbase (se 3 (by rfl) ⟨353126, by rfl⟩ : syracuseStep 1883341 = 706253) (by norm_num)
theorem B3980501 : Blo 782338 3980501 := bbase (se 7 (by rfl) ⟨46646, by rfl⟩ : syracuseStep 3980501 = 93293) (by norm_num)
theorem B1981685 : Blo 782338 1981685 := bbase (se 5 (by rfl) ⟨92891, by rfl⟩ : syracuseStep 1981685 = 185783) (by norm_num)
theorem B2866421 : Blo 782338 2866421 := bbase (se 5 (by rfl) ⟨134363, by rfl⟩ : syracuseStep 2866421 = 268727) (by norm_num)
theorem B1326341 : Blo 782338 1326341 := bbase (se 4 (by rfl) ⟨124344, by rfl⟩ : syracuseStep 1326341 = 248689) (by norm_num)
theorem B1490213 : Blo 782338 1490213 := bbase (se 4 (by rfl) ⟨139707, by rfl⟩ : syracuseStep 1490213 = 279415) (by norm_num)
theorem B3358037 : Blo 782338 3358037 := bbase (se 11 (by rfl) ⟨2459, by rfl⟩ : syracuseStep 3358037 = 4919) (by norm_num)
theorem B1326469 : Blo 782338 1326469 := bbase (se 4 (by rfl) ⟨124356, by rfl⟩ : syracuseStep 1326469 = 248713) (by norm_num)
theorem B1326557 : Blo 782338 1326557 := bbase (se 3 (by rfl) ⟨248729, by rfl⟩ : syracuseStep 1326557 = 497459) (by norm_num)
theorem B1490501 : Blo 782338 1490501 := bbase (se 4 (by rfl) ⟨139734, by rfl⟩ : syracuseStep 1490501 = 279469) (by norm_num)
theorem B1982029 : Blo 782338 1982029 := bbase (se 3 (by rfl) ⟨371630, by rfl⟩ : syracuseStep 1982029 = 743261) (by norm_num)
theorem B1326685 : Blo 782338 1326685 := bbase (se 3 (by rfl) ⟨248753, by rfl⟩ : syracuseStep 1326685 = 497507) (by norm_num)
theorem B2506405 : Blo 782338 2506405 := bbase (se 4 (by rfl) ⟨234975, by rfl⟩ : syracuseStep 2506405 = 469951) (by norm_num)
theorem B1326773 : Blo 782338 1326773 := bbase (se 5 (by rfl) ⟨62192, by rfl⟩ : syracuseStep 1326773 = 124385) (by norm_num)
theorem B1982141 : Blo 782338 1982141 := bbase (se 3 (by rfl) ⟨371651, by rfl⟩ : syracuseStep 1982141 = 743303) (by norm_num)
theorem B1490653 : Blo 782338 1490653 := bbase (se 3 (by rfl) ⟨279497, by rfl⟩ : syracuseStep 1490653 = 558995) (by norm_num)
theorem B4472597 : Blo 782338 4472597 := bbase (se 6 (by rfl) ⟨104826, by rfl⟩ : syracuseStep 4472597 = 209653) (by norm_num)
theorem B1326901 : Blo 782338 1326901 := bbase (se 5 (by rfl) ⟨62198, by rfl⟩ : syracuseStep 1326901 = 124397) (by norm_num)
theorem B1982333 : Blo 782338 1982333 := bbase (se 3 (by rfl) ⟨371687, by rfl⟩ : syracuseStep 1982333 = 743375) (by norm_num)
theorem B2015189 : Blo 782338 2015189 := bbase (se 7 (by rfl) ⟨23615, by rfl⟩ : syracuseStep 2015189 = 47231) (by norm_num)
theorem B1490957 : Blo 782338 1490957 := bbase (se 3 (by rfl) ⟨279554, by rfl⟩ : syracuseStep 1490957 = 559109) (by norm_num)
theorem B835601 : Blo 782338 835601 := bbase (se 2 (by rfl) ⟨313350, by rfl⟩ : syracuseStep 835601 = 626701) (by norm_num)
theorem B1982677 : Blo 782338 1982677 := bbase (se 7 (by rfl) ⟨23234, by rfl⟩ : syracuseStep 1982677 = 46469) (by norm_num)
theorem B1589557 : Blo 782338 1589557 := bbase (se 5 (by rfl) ⟨74510, by rfl⟩ : syracuseStep 1589557 = 149021) (by norm_num)
theorem B1982789 : Blo 782338 1982789 := bbase (se 4 (by rfl) ⟨185886, by rfl⟩ : syracuseStep 1982789 = 371773) (by norm_num)
theorem B1982981 : Blo 782338 1982981 := bbase (se 4 (by rfl) ⟨185904, by rfl⟩ : syracuseStep 1982981 = 371809) (by norm_num)
theorem B1884725 : Blo 782338 1884725 := bbase (se 5 (by rfl) ⟨88346, by rfl⟩ : syracuseStep 1884725 = 176693) (by norm_num)
theorem B1884917 : Blo 782338 1884917 := bbase (se 5 (by rfl) ⟨88355, by rfl⟩ : syracuseStep 1884917 = 176711) (by norm_num)
theorem B1491709 : Blo 782338 1491709 := bbase (se 3 (by rfl) ⟨279695, by rfl⟩ : syracuseStep 1491709 = 559391) (by norm_num)
theorem B836353 : Blo 782338 836353 := bbase (se 2 (by rfl) ⟨313632, by rfl⟩ : syracuseStep 836353 = 627265) (by norm_num)
theorem B15319829 : Blo 782338 15319829 := bbase (se 6 (by rfl) ⟨359058, by rfl⟩ : syracuseStep 15319829 = 718117) (by norm_num)
theorem B836425 : Blo 782338 836425 := bbase (se 2 (by rfl) ⟨313659, by rfl⟩ : syracuseStep 836425 = 627319) (by norm_num)
theorem B1983325 : Blo 782338 1983325 := bbase (se 3 (by rfl) ⟨371873, by rfl⟩ : syracuseStep 1983325 = 743747) (by norm_num)
theorem B1491853 : Blo 782338 1491853 := bbase (se 3 (by rfl) ⟨279722, by rfl⟩ : syracuseStep 1491853 = 559445) (by norm_num)
theorem B1983437 : Blo 782338 1983437 := bbase (se 3 (by rfl) ⟨371894, by rfl⟩ : syracuseStep 1983437 = 743789) (by norm_num)
theorem B836605 : Blo 782338 836605 := bbase (se 3 (by rfl) ⟨156863, by rfl⟩ : syracuseStep 836605 = 313727) (by norm_num)
theorem B8471573 : Blo 782338 8471573 := bbase (se 6 (by rfl) ⟨198552, by rfl⟩ : syracuseStep 8471573 = 397105) (by norm_num)
theorem B1492013 : Blo 782338 1492013 := bbase (se 3 (by rfl) ⟨279752, by rfl⟩ : syracuseStep 1492013 = 559505) (by norm_num)
theorem B1983629 : Blo 782338 1983629 := bbase (se 3 (by rfl) ⟨371930, by rfl⟩ : syracuseStep 1983629 = 743861) (by norm_num)
theorem B1492157 : Blo 782338 1492157 := bbase (se 3 (by rfl) ⟨279779, by rfl⟩ : syracuseStep 1492157 = 559559) (by norm_num)
theorem B837049 : Blo 782338 837049 := bbase (se 2 (by rfl) ⟨313893, by rfl⟩ : syracuseStep 837049 = 627787) (by norm_num)
theorem B1590749 : Blo 782338 1590749 := bbase (se 3 (by rfl) ⟨298265, by rfl⟩ : syracuseStep 1590749 = 596531) (by norm_num)
theorem B1492445 : Blo 782338 1492445 := bbase (se 3 (by rfl) ⟨279833, by rfl⟩ : syracuseStep 1492445 = 559667) (by norm_num)
theorem B1983973 : Blo 782338 1983973 := bbase (se 4 (by rfl) ⟨185997, by rfl⟩ : syracuseStep 1983973 = 371995) (by norm_num)
theorem B1590821 : Blo 782338 1590821 := bbase (se 4 (by rfl) ⟨149139, by rfl⟩ : syracuseStep 1590821 = 298279) (by norm_num)
theorem B837173 : Blo 782338 837173 := bbase (se 5 (by rfl) ⟨39242, by rfl⟩ : syracuseStep 837173 = 78485) (by norm_num)
theorem B1984085 : Blo 782338 1984085 := bbase (se 8 (by rfl) ⟨11625, by rfl⟩ : syracuseStep 1984085 = 23251) (by norm_num)
theorem B1492597 : Blo 782338 1492597 := bbase (se 5 (by rfl) ⟨69965, by rfl⟩ : syracuseStep 1492597 = 139931) (by norm_num)
theorem B1787557 : Blo 782338 1787557 := bbase (se 4 (by rfl) ⟨167583, by rfl⟩ : syracuseStep 1787557 = 335167) (by norm_num)
theorem B4245173 : Blo 782338 4245173 := bbase (se 5 (by rfl) ⟨198992, by rfl⟩ : syracuseStep 4245173 = 397985) (by norm_num)
theorem B1984277 : Blo 782338 1984277 := bbase (se 6 (by rfl) ⟨46506, by rfl⟩ : syracuseStep 1984277 = 93013) (by norm_num)
theorem B4015909 : Blo 782338 4015909 := bbase (se 4 (by rfl) ⟨376491, by rfl⟩ : syracuseStep 4015909 = 752983) (by norm_num)
theorem B837425 : Blo 782338 837425 := bbase (se 2 (by rfl) ⟨314034, by rfl⟩ : syracuseStep 837425 = 628069) (by norm_num)
theorem B4245301 : Blo 782338 4245301 := bbase (se 5 (by rfl) ⟨198998, by rfl⟩ : syracuseStep 4245301 = 397997) (by norm_num)
theorem B1984621 : Blo 782338 1984621 := bbase (se 3 (by rfl) ⟨372116, by rfl⟩ : syracuseStep 1984621 = 744233) (by norm_num)
theorem B1984733 : Blo 782338 1984733 := bbase (se 3 (by rfl) ⟨372137, by rfl⟩ : syracuseStep 1984733 = 744275) (by norm_num)
theorem B837869 : Blo 782338 837869 := bbase (se 3 (by rfl) ⟨157100, by rfl⟩ : syracuseStep 837869 = 314201) (by norm_num)
theorem B1886485 : Blo 782338 1886485 := bbase (se 6 (by rfl) ⟨44214, by rfl⟩ : syracuseStep 1886485 = 88429) (by norm_num)
theorem B8472917 : Blo 782338 8472917 := bbase (se 10 (by rfl) ⟨12411, by rfl⟩ : syracuseStep 8472917 = 24823) (by norm_num)
theorem B8046965 : Blo 782338 8046965 := bbase (se 5 (by rfl) ⟨377201, by rfl⟩ : syracuseStep 8046965 = 754403) (by norm_num)
theorem B1984925 : Blo 782338 1984925 := bbase (se 3 (by rfl) ⟨372173, by rfl⟩ : syracuseStep 1984925 = 744347) (by norm_num)
theorem B838117 : Blo 782338 838117 := bbase (se 4 (by rfl) ⟨78573, by rfl⟩ : syracuseStep 838117 = 157147) (by norm_num)
theorem B2542085 : Blo 782338 2542085 := bbase (se 4 (by rfl) ⟨238320, by rfl⟩ : syracuseStep 2542085 = 476641) (by norm_num)
theorem B5032469 : Blo 782338 5032469 := bbase (se 6 (by rfl) ⟨117948, by rfl⟩ : syracuseStep 5032469 = 235897) (by norm_num)
theorem B2640437 : Blo 782338 2640437 := bbase (se 5 (by rfl) ⟨123770, by rfl⟩ : syracuseStep 2640437 = 247541) (by norm_num)
theorem B2116165 : Blo 782338 2116165 := bbase (se 4 (by rfl) ⟨198390, by rfl⟩ : syracuseStep 2116165 = 396781) (by norm_num)
theorem B1985269 : Blo 782338 1985269 := bbase (se 5 (by rfl) ⟨93059, by rfl⟩ : syracuseStep 1985269 = 186119) (by norm_num)
theorem B1985381 : Blo 782338 1985381 := bbase (se 4 (by rfl) ⟨186129, by rfl⟩ : syracuseStep 1985381 = 372259) (by norm_num)
theorem B1887101 : Blo 782338 1887101 := bbase (se 3 (by rfl) ⟨353831, by rfl⟩ : syracuseStep 1887101 = 707663) (by norm_num)
theorem B838561 : Blo 782338 838561 := bbase (se 2 (by rfl) ⟨314460, by rfl⟩ : syracuseStep 838561 = 628921) (by norm_num)
theorem B838621 : Blo 782338 838621 := bbase (se 3 (by rfl) ⟨157241, by rfl⟩ : syracuseStep 838621 = 314483) (by norm_num)
theorem B2640869 : Blo 782338 2640869 := bbase (se 4 (by rfl) ⟨247581, by rfl⟩ : syracuseStep 2640869 = 495163) (by norm_num)
theorem B1985573 : Blo 782338 1985573 := bbase (se 4 (by rfl) ⟨186147, by rfl⟩ : syracuseStep 1985573 = 372295) (by norm_num)
theorem B838937 : Blo 782338 838937 := bbase (se 2 (by rfl) ⟨314601, by rfl⟩ : syracuseStep 838937 = 629203) (by norm_num)
theorem B1985917 : Blo 782338 1985917 := bbase (se 3 (by rfl) ⟨372359, by rfl⟩ : syracuseStep 1985917 = 744719) (by norm_num)
theorem B2641301 : Blo 782338 2641301 := bbase (se 6 (by rfl) ⟨61905, by rfl⟩ : syracuseStep 2641301 = 123811) (by norm_num)
theorem B1986029 : Blo 782338 1986029 := bbase (se 3 (by rfl) ⟨372380, by rfl⟩ : syracuseStep 1986029 = 744761) (by norm_num)
theorem B1887877 : Blo 782338 1887877 := bbase (se 4 (by rfl) ⟨176988, by rfl⟩ : syracuseStep 1887877 = 353977) (by norm_num)
theorem B1986221 : Blo 782338 1986221 := bbase (se 3 (by rfl) ⟨372416, by rfl⟩ : syracuseStep 1986221 = 744833) (by norm_num)
theorem B839381 : Blo 782338 839381 := bbase (se 7 (by rfl) ⟨9836, by rfl⟩ : syracuseStep 839381 = 19673) (by norm_num)
theorem B839441 : Blo 782338 839441 := bbase (se 2 (by rfl) ⟨314790, by rfl⟩ : syracuseStep 839441 = 629581) (by norm_num)
theorem B2641733 : Blo 782338 2641733 := bbase (se 4 (by rfl) ⟨247662, by rfl⟩ : syracuseStep 2641733 = 495325) (by norm_num)
theorem B839569 : Blo 782338 839569 := bbase (se 2 (by rfl) ⟨314838, by rfl⟩ : syracuseStep 839569 = 629677) (by norm_num)
theorem B1789885 : Blo 782338 1789885 := bbase (se 3 (by rfl) ⟨335603, by rfl⟩ : syracuseStep 1789885 = 671207) (by norm_num)
theorem B1429469 : Blo 782338 1429469 := bbase (se 3 (by rfl) ⟨268025, by rfl⟩ : syracuseStep 1429469 = 536051) (by norm_num)
theorem B1986565 : Blo 782338 1986565 := bbase (se 4 (by rfl) ⟨186240, by rfl⟩ : syracuseStep 1986565 = 372481) (by norm_num)
theorem B1986677 : Blo 782338 1986677 := bbase (se 5 (by rfl) ⟨93125, by rfl⟩ : syracuseStep 1986677 = 186251) (by norm_num)
theorem B2117765 : Blo 782338 2117765 := bbase (se 4 (by rfl) ⟨198540, by rfl⟩ : syracuseStep 2117765 = 397081) (by norm_num)
theorem B2642165 : Blo 782338 2642165 := bbase (se 5 (by rfl) ⟨123851, by rfl⟩ : syracuseStep 2642165 = 247703) (by norm_num)
theorem B1986869 : Blo 782338 1986869 := bbase (se 5 (by rfl) ⟨93134, by rfl⟩ : syracuseStep 1986869 = 186269) (by norm_num)
theorem B1888589 : Blo 782338 1888589 := bbase (se 3 (by rfl) ⟨354110, by rfl⟩ : syracuseStep 1888589 = 708221) (by norm_num)
theorem B1593773 : Blo 782338 1593773 := bbase (se 3 (by rfl) ⟨298832, by rfl⟩ : syracuseStep 1593773 = 597665) (by norm_num)
theorem B807545 : Blo 782338 807545 := bbase (se 2 (by rfl) ⟨302829, by rfl⟩ : syracuseStep 807545 = 605659) (by norm_num)
theorem B1987213 : Blo 782338 1987213 := bbase (se 3 (by rfl) ⟨372602, by rfl⟩ : syracuseStep 1987213 = 745205) (by norm_num)
theorem B2642597 : Blo 782338 2642597 := bbase (se 4 (by rfl) ⟨247743, by rfl⟩ : syracuseStep 2642597 = 495487) (by norm_num)
theorem B2511557 : Blo 782338 2511557 := bbase (se 4 (by rfl) ⟨235458, by rfl⟩ : syracuseStep 2511557 = 470917) (by norm_num)
theorem B1987325 : Blo 782338 1987325 := bbase (se 3 (by rfl) ⟨372623, by rfl⟩ : syracuseStep 1987325 = 745247) (by norm_num)
theorem B1987517 : Blo 782338 1987517 := bbase (se 3 (by rfl) ⟨372659, by rfl⟩ : syracuseStep 1987517 = 745319) (by norm_num)
theorem B1889261 : Blo 782338 1889261 := bbase (se 3 (by rfl) ⟨354236, by rfl⟩ : syracuseStep 1889261 = 708473) (by norm_num)
theorem B1004609 : Blo 782338 1004609 := bbase (se 2 (by rfl) ⟨376728, by rfl⟩ : syracuseStep 1004609 = 753457) (by norm_num)
theorem B2643029 : Blo 782338 2643029 := bbase (se 8 (by rfl) ⟨15486, by rfl⟩ : syracuseStep 2643029 = 30973) (by norm_num)
theorem B1987861 : Blo 782338 1987861 := bbase (se 6 (by rfl) ⟨46590, by rfl⟩ : syracuseStep 1987861 = 93181) (by norm_num)
theorem B1987973 : Blo 782338 1987973 := bbase (se 4 (by rfl) ⟨186372, by rfl⟩ : syracuseStep 1987973 = 372745) (by norm_num)
theorem B5953013 : Blo 782338 5953013 := bbase (se 5 (by rfl) ⟨279047, by rfl⟩ : syracuseStep 5953013 = 558095) (by norm_num)
theorem B2643461 : Blo 782338 2643461 := bbase (se 4 (by rfl) ⟨247824, by rfl⟩ : syracuseStep 2643461 = 495649) (by norm_num)
theorem B6706709 : Blo 782338 6706709 := bbase (se 6 (by rfl) ⟨157188, by rfl⟩ : syracuseStep 6706709 = 314377) (by norm_num)
theorem B1988165 : Blo 782338 1988165 := bbase (se 4 (by rfl) ⟨186390, by rfl⟩ : syracuseStep 1988165 = 372781) (by norm_num)
theorem B2512453 : Blo 782338 2512453 := bbase (se 4 (by rfl) ⟨235542, by rfl⟩ : syracuseStep 2512453 = 471085) (by norm_num)
theorem B2971525 : Blo 782338 2971525 := bbase (se 4 (by rfl) ⟨278580, by rfl⟩ : syracuseStep 2971525 = 557161) (by norm_num)
theorem B1988509 : Blo 782338 1988509 := bbase (se 3 (by rfl) ⟨372845, by rfl⟩ : syracuseStep 1988509 = 745691) (by norm_num)
theorem B2643893 : Blo 782338 2643893 := bbase (se 5 (by rfl) ⟨123932, by rfl⟩ : syracuseStep 2643893 = 247865) (by norm_num)
theorem B2512853 : Blo 782338 2512853 := bbase (se 7 (by rfl) ⟨29447, by rfl⟩ : syracuseStep 2512853 = 58895) (by norm_num)
theorem B3397621 : Blo 782338 3397621 := bbase (se 5 (by rfl) ⟨159263, by rfl⟩ : syracuseStep 3397621 = 318527) (by norm_num)
theorem B1988621 : Blo 782338 1988621 := bbase (se 3 (by rfl) ⟨372866, by rfl⟩ : syracuseStep 1988621 = 745733) (by norm_num)
theorem B2414645 : Blo 782338 2414645 := bbase (se 5 (by rfl) ⟨113186, by rfl⟩ : syracuseStep 2414645 = 226373) (by norm_num)
theorem B1005625 : Blo 782338 1005625 := bbase (se 2 (by rfl) ⟨377109, by rfl⟩ : syracuseStep 1005625 = 754219) (by norm_num)
theorem B940133 : Blo 782338 940133 := bbase (se 4 (by rfl) ⟨88137, by rfl⟩ : syracuseStep 940133 = 176275) (by norm_num)
theorem B940205 : Blo 782338 940205 := bbase (se 3 (by rfl) ⟨176288, by rfl⟩ : syracuseStep 940205 = 352577) (by norm_num)
theorem B2971829 : Blo 782338 2971829 := bbase (se 5 (by rfl) ⟨139304, by rfl⟩ : syracuseStep 2971829 = 278609) (by norm_num)
theorem B1988813 : Blo 782338 1988813 := bbase (se 3 (by rfl) ⟨372902, by rfl⟩ : syracuseStep 1988813 = 745805) (by norm_num)
theorem B2644325 : Blo 782338 2644325 := bbase (se 4 (by rfl) ⟨247905, by rfl⟩ : syracuseStep 2644325 = 495811) (by norm_num)
theorem B940513 : Blo 782338 940513 := bbase (se 2 (by rfl) ⟨352692, by rfl⟩ : syracuseStep 940513 = 705385) (by norm_num)
theorem B1989157 : Blo 782338 1989157 := bbase (se 4 (by rfl) ⟨186483, by rfl⟩ : syracuseStep 1989157 = 372967) (by norm_num)
theorem B940681 : Blo 782338 940681 := bbase (se 2 (by rfl) ⟨352755, by rfl⟩ : syracuseStep 940681 = 705511) (by norm_num)
theorem B1989269 : Blo 782338 1989269 := bbase (se 6 (by rfl) ⟨46623, by rfl⟩ : syracuseStep 1989269 = 93247) (by norm_num)
theorem B940729 : Blo 782338 940729 := bbase (se 2 (by rfl) ⟨352773, by rfl⟩ : syracuseStep 940729 = 705547) (by norm_num)
theorem B2644757 : Blo 782338 2644757 := bbase (se 6 (by rfl) ⟨61986, by rfl⟩ : syracuseStep 2644757 = 123973) (by norm_num)
theorem B940825 : Blo 782338 940825 := bbase (se 2 (by rfl) ⟨352809, by rfl⟩ : syracuseStep 940825 = 705619) (by norm_num)
theorem B32168789 : Blo 782338 32168789 := bbase (se 9 (by rfl) ⟨94244, by rfl⟩ : syracuseStep 32168789 = 188489) (by norm_num)
theorem B1989461 : Blo 782338 1989461 := bbase (se 9 (by rfl) ⟨5828, by rfl⟩ : syracuseStep 1989461 = 11657) (by norm_num)
theorem B908137 : Blo 782338 908137 := bbase (se 2 (by rfl) ⟨340551, by rfl⟩ : syracuseStep 908137 = 681103) (by norm_num)
theorem B1760309 : Blo 782338 1760309 := bbase (se 5 (by rfl) ⟨82514, by rfl⟩ : syracuseStep 1760309 = 165029) (by norm_num)
theorem B1760381 : Blo 782338 1760381 := bbase (se 3 (by rfl) ⟨330071, by rfl⟩ : syracuseStep 1760381 = 660143) (by norm_num)
theorem B1989805 : Blo 782338 1989805 := bbase (se 3 (by rfl) ⟨373088, by rfl⟩ : syracuseStep 1989805 = 746177) (by norm_num)
theorem B5364917 : Blo 782338 5364917 := bbase (se 5 (by rfl) ⟨251480, by rfl⟩ : syracuseStep 5364917 = 502961) (by norm_num)
theorem B1760453 : Blo 782338 1760453 := bbase (se 4 (by rfl) ⟨165042, by rfl⟩ : syracuseStep 1760453 = 330085) (by norm_num)
theorem B2645189 : Blo 782338 2645189 := bbase (se 4 (by rfl) ⟨247986, by rfl⟩ : syracuseStep 2645189 = 495973) (by norm_num)
theorem B1760525 : Blo 782338 1760525 := bbase (se 3 (by rfl) ⟨330098, by rfl⟩ : syracuseStep 1760525 = 660197) (by norm_num)
theorem B1989917 : Blo 782338 1989917 := bbase (se 3 (by rfl) ⟨373109, by rfl⟩ : syracuseStep 1989917 = 746219) (by norm_num)
theorem B1760597 : Blo 782338 1760597 := bbase (se 11 (by rfl) ⟨1289, by rfl⟩ : syracuseStep 1760597 = 2579) (by norm_num)
theorem B941401 : Blo 782338 941401 := bbase (se 2 (by rfl) ⟨353025, by rfl⟩ : syracuseStep 941401 = 706051) (by norm_num)
theorem B1760669 : Blo 782338 1760669 := bbase (se 3 (by rfl) ⟨330125, by rfl⟩ : syracuseStep 1760669 = 660251) (by norm_num)
theorem B1990109 : Blo 782338 1990109 := bbase (se 3 (by rfl) ⟨373145, by rfl⟩ : syracuseStep 1990109 = 746291) (by norm_num)
theorem B1760741 : Blo 782338 1760741 := bbase (se 4 (by rfl) ⟨165069, by rfl⟩ : syracuseStep 1760741 = 330139) (by norm_num)
theorem B1760813 : Blo 782338 1760813 := bbase (se 3 (by rfl) ⟨330152, by rfl⟩ : syracuseStep 1760813 = 660305) (by norm_num)
theorem B1531469 : Blo 782338 1531469 := bbase (se 3 (by rfl) ⟨287150, by rfl⟩ : syracuseStep 1531469 = 574301) (by norm_num)
theorem B1760885 : Blo 782338 1760885 := bbase (se 5 (by rfl) ⟨82541, by rfl⟩ : syracuseStep 1760885 = 165083) (by norm_num)
theorem B2645621 : Blo 782338 2645621 := bbase (se 5 (by rfl) ⟨124013, by rfl⟩ : syracuseStep 2645621 = 248027) (by norm_num)
theorem B1760957 : Blo 782338 1760957 := bbase (se 3 (by rfl) ⟨330179, by rfl⟩ : syracuseStep 1760957 = 660359) (by norm_num)
theorem B1761029 : Blo 782338 1761029 := bbase (se 4 (by rfl) ⟨165096, by rfl⟩ : syracuseStep 1761029 = 330193) (by norm_num)
theorem B1761101 : Blo 782338 1761101 := bbase (se 3 (by rfl) ⟨330206, by rfl⟩ : syracuseStep 1761101 = 660413) (by norm_num)
theorem B5103445 : Blo 782338 5103445 := bbase (se 9 (by rfl) ⟨14951, by rfl⟩ : syracuseStep 5103445 = 29903) (by norm_num)
theorem B1761173 : Blo 782338 1761173 := bbase (se 6 (by rfl) ⟨41277, by rfl⟩ : syracuseStep 1761173 = 82555) (by norm_num)
theorem B1761245 : Blo 782338 1761245 := bbase (se 3 (by rfl) ⟨330233, by rfl⟩ : syracuseStep 1761245 = 660467) (by norm_num)
theorem B1761317 : Blo 782338 1761317 := bbase (se 4 (by rfl) ⟨165123, by rfl⟩ : syracuseStep 1761317 = 330247) (by norm_num)
theorem B2646053 : Blo 782338 2646053 := bbase (se 4 (by rfl) ⟨248067, by rfl⟩ : syracuseStep 2646053 = 496135) (by norm_num)
theorem B1761389 : Blo 782338 1761389 := bbase (se 3 (by rfl) ⟨330260, by rfl⟩ : syracuseStep 1761389 = 660521) (by norm_num)
theorem B1761461 : Blo 782338 1761461 := bbase (se 5 (by rfl) ⟨82568, by rfl⟩ : syracuseStep 1761461 = 165137) (by norm_num)
theorem B2973941 : Blo 782338 2973941 := bbase (se 5 (by rfl) ⟨139403, by rfl⟩ : syracuseStep 2973941 = 278807) (by norm_num)
theorem B1761533 : Blo 782338 1761533 := bbase (se 3 (by rfl) ⟨330287, by rfl⟩ : syracuseStep 1761533 = 660575) (by norm_num)
theorem B942401 : Blo 782338 942401 := bbase (se 2 (by rfl) ⟨353400, by rfl⟩ : syracuseStep 942401 = 706801) (by norm_num)
theorem B1761605 : Blo 782338 1761605 := bbase (se 4 (by rfl) ⟨165150, by rfl⟩ : syracuseStep 1761605 = 330301) (by norm_num)
theorem B942449 : Blo 782338 942449 := bbase (se 2 (by rfl) ⟨353418, by rfl⟩ : syracuseStep 942449 = 706837) (by norm_num)
theorem B1761677 : Blo 782338 1761677 := bbase (se 3 (by rfl) ⟨330314, by rfl⟩ : syracuseStep 1761677 = 660629) (by norm_num)
theorem B1761749 : Blo 782338 1761749 := bbase (se 7 (by rfl) ⟨20645, by rfl⟩ : syracuseStep 1761749 = 41291) (by norm_num)
theorem B2646485 : Blo 782338 2646485 := bbase (se 7 (by rfl) ⟨31013, by rfl⟩ : syracuseStep 2646485 = 62027) (by norm_num)
theorem B2974229 : Blo 782338 2974229 := bbase (se 6 (by rfl) ⟨69708, by rfl⟩ : syracuseStep 2974229 = 139417) (by norm_num)
theorem B1761821 : Blo 782338 1761821 := bbase (se 3 (by rfl) ⟨330341, by rfl⟩ : syracuseStep 1761821 = 660683) (by norm_num)
theorem B1008169 : Blo 782338 1008169 := bbase (se 2 (by rfl) ⟨378063, by rfl⟩ : syracuseStep 1008169 = 756127) (by norm_num)
theorem B1761893 : Blo 782338 1761893 := bbase (se 4 (by rfl) ⟨165177, by rfl⟩ : syracuseStep 1761893 = 330355) (by norm_num)
theorem B1761965 : Blo 782338 1761965 := bbase (se 3 (by rfl) ⟨330368, by rfl⟩ : syracuseStep 1761965 = 660737) (by norm_num)
theorem B1762037 : Blo 782338 1762037 := bbase (se 5 (by rfl) ⟨82595, by rfl⟩ : syracuseStep 1762037 = 165191) (by norm_num)
theorem B1762109 : Blo 782338 1762109 := bbase (se 3 (by rfl) ⟨330395, by rfl⟩ : syracuseStep 1762109 = 660791) (by norm_num)
theorem B1762181 : Blo 782338 1762181 := bbase (se 4 (by rfl) ⟨165204, by rfl⟩ : syracuseStep 1762181 = 330409) (by norm_num)
theorem B2646917 : Blo 782338 2646917 := bbase (se 4 (by rfl) ⟨248148, by rfl⟩ : syracuseStep 2646917 = 496297) (by norm_num)
theorem B942997 : Blo 782338 942997 := bbase (se 6 (by rfl) ⟨22101, by rfl⟩ : syracuseStep 942997 = 44203) (by norm_num)
theorem B1762253 : Blo 782338 1762253 := bbase (se 3 (by rfl) ⟨330422, by rfl⟩ : syracuseStep 1762253 = 660845) (by norm_num)
theorem B1762325 : Blo 782338 1762325 := bbase (se 6 (by rfl) ⟨41304, by rfl⟩ : syracuseStep 1762325 = 82609) (by norm_num)
theorem B1762397 : Blo 782338 1762397 := bbase (se 3 (by rfl) ⟨330449, by rfl⟩ : syracuseStep 1762397 = 660899) (by norm_num)
theorem B1762469 : Blo 782338 1762469 := bbase (se 4 (by rfl) ⟨165231, by rfl⟩ : syracuseStep 1762469 = 330463) (by norm_num)
theorem B1762541 : Blo 782338 1762541 := bbase (se 3 (by rfl) ⟨330476, by rfl⟩ : syracuseStep 1762541 = 660953) (by norm_num)
theorem B1762613 : Blo 782338 1762613 := bbase (se 5 (by rfl) ⟨82622, by rfl⟩ : syracuseStep 1762613 = 165245) (by norm_num)
theorem B2647349 : Blo 782338 2647349 := bbase (se 5 (by rfl) ⟨124094, by rfl⟩ : syracuseStep 2647349 = 248189) (by norm_num)
theorem B943477 : Blo 782338 943477 := bbase (se 5 (by rfl) ⟨44225, by rfl⟩ : syracuseStep 943477 = 88451) (by norm_num)
theorem B1762685 : Blo 782338 1762685 := bbase (se 3 (by rfl) ⟨330503, by rfl⟩ : syracuseStep 1762685 = 661007) (by norm_num)
theorem B1860989 : Blo 782338 1860989 := bbase (se 3 (by rfl) ⟨348935, by rfl⟩ : syracuseStep 1860989 = 697871) (by norm_num)
theorem B2680229 : Blo 782338 2680229 := bbase (se 4 (by rfl) ⟨251271, by rfl⟩ : syracuseStep 2680229 = 502543) (by norm_num)
theorem B5662133 : Blo 782338 5662133 := bbase (se 5 (by rfl) ⟨265412, by rfl⟩ : syracuseStep 5662133 = 530825) (by norm_num)
theorem B1762757 : Blo 782338 1762757 := bbase (se 4 (by rfl) ⟨165258, by rfl⟩ : syracuseStep 1762757 = 330517) (by norm_num)
theorem B3401189 : Blo 782338 3401189 := bbase (se 4 (by rfl) ⟨318861, by rfl⟩ : syracuseStep 3401189 = 637723) (by norm_num)
theorem B1762829 : Blo 782338 1762829 := bbase (se 3 (by rfl) ⟨330530, by rfl⟩ : syracuseStep 1762829 = 661061) (by norm_num)
theorem B1762901 : Blo 782338 1762901 := bbase (se 8 (by rfl) ⟨10329, by rfl⟩ : syracuseStep 1762901 = 20659) (by norm_num)
theorem B1762973 : Blo 782338 1762973 := bbase (se 3 (by rfl) ⟨330557, by rfl⟩ : syracuseStep 1762973 = 661115) (by norm_num)
theorem B2516645 : Blo 782338 2516645 := bbase (se 4 (by rfl) ⟨235935, by rfl⟩ : syracuseStep 2516645 = 471871) (by norm_num)
theorem B2123429 : Blo 782338 2123429 := bbase (se 4 (by rfl) ⟨199071, by rfl⟩ : syracuseStep 2123429 = 398143) (by norm_num)
theorem B2975413 : Blo 782338 2975413 := bbase (se 5 (by rfl) ⟨139472, by rfl⟩ : syracuseStep 2975413 = 278945) (by norm_num)
theorem B1763045 : Blo 782338 1763045 := bbase (se 4 (by rfl) ⟨165285, by rfl⟩ : syracuseStep 1763045 = 330571) (by norm_num)
theorem B2647781 : Blo 782338 2647781 := bbase (se 4 (by rfl) ⟨248229, by rfl⟩ : syracuseStep 2647781 = 496459) (by norm_num)
theorem B1763117 : Blo 782338 1763117 := bbase (se 3 (by rfl) ⟨330584, by rfl⟩ : syracuseStep 1763117 = 661169) (by norm_num)
theorem B1763189 : Blo 782338 1763189 := bbase (se 5 (by rfl) ⟨82649, by rfl⟩ : syracuseStep 1763189 = 165299) (by norm_num)
theorem B1763261 : Blo 782338 1763261 := bbase (se 3 (by rfl) ⟨330611, by rfl⟩ : syracuseStep 1763261 = 661223) (by norm_num)
theorem B2975717 : Blo 782338 2975717 := bbase (se 4 (by rfl) ⟨278973, by rfl⟩ : syracuseStep 2975717 = 557947) (by norm_num)
theorem B5662709 : Blo 782338 5662709 := bbase (se 5 (by rfl) ⟨265439, by rfl⟩ : syracuseStep 5662709 = 530879) (by norm_num)
theorem B1173509 : Blo 782338 1173509 := bbase (se 4 (by rfl) ⟨110016, by rfl⟩ : syracuseStep 1173509 = 220033) (by norm_num)
theorem B1763333 : Blo 782338 1763333 := bbase (se 4 (by rfl) ⟨165312, by rfl⟩ : syracuseStep 1763333 = 330625) (by norm_num)
theorem B1173533 : Blo 782338 1173533 := bbase (se 3 (by rfl) ⟨220037, by rfl⟩ : syracuseStep 1173533 = 440075) (by norm_num)
theorem B1173557 : Blo 782338 1173557 := bbase (se 5 (by rfl) ⟨55010, by rfl⟩ : syracuseStep 1173557 = 110021) (by norm_num)
theorem B1173581 : Blo 782338 1173581 := bbase (se 3 (by rfl) ⟨220046, by rfl⟩ : syracuseStep 1173581 = 440093) (by norm_num)
theorem B1763405 : Blo 782338 1763405 := bbase (se 3 (by rfl) ⟨330638, by rfl⟩ : syracuseStep 1763405 = 661277) (by norm_num)
theorem B1173605 : Blo 782338 1173605 := bbase (se 4 (by rfl) ⟨110025, by rfl⟩ : syracuseStep 1173605 = 220051) (by norm_num)
theorem B2386037 : Blo 782338 2386037 := bbase (se 5 (by rfl) ⟨111845, by rfl⟩ : syracuseStep 2386037 = 223691) (by norm_num)
theorem B1173629 : Blo 782338 1173629 := bbase (se 3 (by rfl) ⟨220055, by rfl⟩ : syracuseStep 1173629 = 440111) (by norm_num)
theorem B1173653 : Blo 782338 1173653 := bbase (se 6 (by rfl) ⟨27507, by rfl⟩ : syracuseStep 1173653 = 55015) (by norm_num)
theorem B1763477 : Blo 782338 1763477 := bbase (se 6 (by rfl) ⟨41331, by rfl⟩ : syracuseStep 1763477 = 82663) (by norm_num)
theorem B2648213 : Blo 782338 2648213 := bbase (se 6 (by rfl) ⟨62067, by rfl⟩ : syracuseStep 2648213 = 124135) (by norm_num)
theorem B1271965 : Blo 782338 1271965 := bbase (se 3 (by rfl) ⟨238493, by rfl⟩ : syracuseStep 1271965 = 476987) (by norm_num)
theorem B1173677 : Blo 782338 1173677 := bbase (se 3 (by rfl) ⟨220064, by rfl⟩ : syracuseStep 1173677 = 440129) (by norm_num)
theorem B1173701 : Blo 782338 1173701 := bbase (se 4 (by rfl) ⟨110034, by rfl⟩ : syracuseStep 1173701 = 220069) (by norm_num)
theorem B1173725 : Blo 782338 1173725 := bbase (se 3 (by rfl) ⟨220073, by rfl⟩ : syracuseStep 1173725 = 440147) (by norm_num)
theorem B1763549 : Blo 782338 1763549 := bbase (se 3 (by rfl) ⟨330665, by rfl⟩ : syracuseStep 1763549 = 661331) (by norm_num)
theorem B944357 : Blo 782338 944357 := bbase (se 4 (by rfl) ⟨88533, by rfl⟩ : syracuseStep 944357 = 177067) (by norm_num)
theorem B1173749 : Blo 782338 1173749 := bbase (se 5 (by rfl) ⟨55019, by rfl⟩ : syracuseStep 1173749 = 110039) (by norm_num)
theorem B1173773 : Blo 782338 1173773 := bbase (se 3 (by rfl) ⟨220082, by rfl⟩ : syracuseStep 1173773 = 440165) (by norm_num)
theorem B1173797 : Blo 782338 1173797 := bbase (se 4 (by rfl) ⟨110043, by rfl⟩ : syracuseStep 1173797 = 220087) (by norm_num)
theorem B1763621 : Blo 782338 1763621 := bbase (se 4 (by rfl) ⟨165339, by rfl⟩ : syracuseStep 1763621 = 330679) (by norm_num)
theorem B1173821 : Blo 782338 1173821 := bbase (se 3 (by rfl) ⟨220091, by rfl⟩ : syracuseStep 1173821 = 440183) (by norm_num)
theorem B1173845 : Blo 782338 1173845 := bbase (se 10 (by rfl) ⟨1719, by rfl⟩ : syracuseStep 1173845 = 3439) (by norm_num)
theorem B944473 : Blo 782338 944473 := bbase (se 2 (by rfl) ⟨354177, by rfl⟩ : syracuseStep 944473 = 708355) (by norm_num)
theorem B1173869 : Blo 782338 1173869 := bbase (se 3 (by rfl) ⟨220100, by rfl⟩ : syracuseStep 1173869 = 440201) (by norm_num)
theorem B1763693 : Blo 782338 1763693 := bbase (se 3 (by rfl) ⟨330692, by rfl⟩ : syracuseStep 1763693 = 661385) (by norm_num)
theorem B1173893 : Blo 782338 1173893 := bbase (se 4 (by rfl) ⟨110052, by rfl⟩ : syracuseStep 1173893 = 220105) (by norm_num)
theorem B1173917 : Blo 782338 1173917 := bbase (se 3 (by rfl) ⟨220109, by rfl⟩ : syracuseStep 1173917 = 440219) (by norm_num)
theorem B1173941 : Blo 782338 1173941 := bbase (se 5 (by rfl) ⟨55028, by rfl⟩ : syracuseStep 1173941 = 110057) (by norm_num)
theorem B1763765 : Blo 782338 1763765 := bbase (se 5 (by rfl) ⟨82676, by rfl⟩ : syracuseStep 1763765 = 165353) (by norm_num)
theorem B1173965 : Blo 782338 1173965 := bbase (se 3 (by rfl) ⟨220118, by rfl⟩ : syracuseStep 1173965 = 440237) (by norm_num)
theorem B1272277 : Blo 782338 1272277 := bbase (se 7 (by rfl) ⟨14909, by rfl⟩ : syracuseStep 1272277 = 29819) (by norm_num)
theorem B1173989 : Blo 782338 1173989 := bbase (se 4 (by rfl) ⟨110061, by rfl⟩ : syracuseStep 1173989 = 220123) (by norm_num)
theorem B1174013 : Blo 782338 1174013 := bbase (se 3 (by rfl) ⟨220127, by rfl⟩ : syracuseStep 1174013 = 440255) (by norm_num)
theorem B1763837 : Blo 782338 1763837 := bbase (se 3 (by rfl) ⟨330719, by rfl⟩ : syracuseStep 1763837 = 661439) (by norm_num)
theorem B1174037 : Blo 782338 1174037 := bbase (se 6 (by rfl) ⟨27516, by rfl⟩ : syracuseStep 1174037 = 55033) (by norm_num)
theorem B944669 : Blo 782338 944669 := bbase (se 3 (by rfl) ⟨177125, by rfl⟩ : syracuseStep 944669 = 354251) (by norm_num)
theorem B1174061 : Blo 782338 1174061 := bbase (se 3 (by rfl) ⟨220136, by rfl⟩ : syracuseStep 1174061 = 440273) (by norm_num)
theorem B1174085 : Blo 782338 1174085 := bbase (se 4 (by rfl) ⟨110070, by rfl⟩ : syracuseStep 1174085 = 220141) (by norm_num)
theorem B1763909 : Blo 782338 1763909 := bbase (se 4 (by rfl) ⟨165366, by rfl⟩ : syracuseStep 1763909 = 330733) (by norm_num)
theorem B2648645 : Blo 782338 2648645 := bbase (se 4 (by rfl) ⟨248310, by rfl⟩ : syracuseStep 2648645 = 496621) (by norm_num)
theorem B1174109 : Blo 782338 1174109 := bbase (se 3 (by rfl) ⟨220145, by rfl⟩ : syracuseStep 1174109 = 440291) (by norm_num)
theorem B1174133 : Blo 782338 1174133 := bbase (se 5 (by rfl) ⟨55037, by rfl⟩ : syracuseStep 1174133 = 110075) (by norm_num)
theorem B1174157 : Blo 782338 1174157 := bbase (se 3 (by rfl) ⟨220154, by rfl⟩ : syracuseStep 1174157 = 440309) (by norm_num)
theorem B1763981 : Blo 782338 1763981 := bbase (se 3 (by rfl) ⟨330746, by rfl⟩ : syracuseStep 1763981 = 661493) (by norm_num)
theorem B1174181 : Blo 782338 1174181 := bbase (se 4 (by rfl) ⟨110079, by rfl⟩ : syracuseStep 1174181 = 220159) (by norm_num)
theorem B1174205 : Blo 782338 1174205 := bbase (se 3 (by rfl) ⟨220163, by rfl⟩ : syracuseStep 1174205 = 440327) (by norm_num)
theorem B1174229 : Blo 782338 1174229 := bbase (se 7 (by rfl) ⟨13760, by rfl⟩ : syracuseStep 1174229 = 27521) (by norm_num)
theorem B1764053 : Blo 782338 1764053 := bbase (se 7 (by rfl) ⟨20672, by rfl⟩ : syracuseStep 1764053 = 41345) (by norm_num)
theorem B2517733 : Blo 782338 2517733 := bbase (se 4 (by rfl) ⟨236037, by rfl⟩ : syracuseStep 2517733 = 472075) (by norm_num)
theorem B1174253 : Blo 782338 1174253 := bbase (se 3 (by rfl) ⟨220172, by rfl⟩ : syracuseStep 1174253 = 440345) (by norm_num)
theorem B1174277 : Blo 782338 1174277 := bbase (se 4 (by rfl) ⟨110088, by rfl⟩ : syracuseStep 1174277 = 220177) (by norm_num)
theorem B1174301 : Blo 782338 1174301 := bbase (se 3 (by rfl) ⟨220181, by rfl⟩ : syracuseStep 1174301 = 440363) (by norm_num)
theorem B1764125 : Blo 782338 1764125 := bbase (se 3 (by rfl) ⟨330773, by rfl⟩ : syracuseStep 1764125 = 661547) (by norm_num)
theorem B1174325 : Blo 782338 1174325 := bbase (se 5 (by rfl) ⟨55046, by rfl⟩ : syracuseStep 1174325 = 110093) (by norm_num)
theorem B1174349 : Blo 782338 1174349 := bbase (se 3 (by rfl) ⟨220190, by rfl⟩ : syracuseStep 1174349 = 440381) (by norm_num)
theorem B1174373 : Blo 782338 1174373 := bbase (se 4 (by rfl) ⟨110097, by rfl⟩ : syracuseStep 1174373 = 220195) (by norm_num)
theorem B1764197 : Blo 782338 1764197 := bbase (se 4 (by rfl) ⟨165393, by rfl⟩ : syracuseStep 1764197 = 330787) (by norm_num)
theorem B1174397 : Blo 782338 1174397 := bbase (se 3 (by rfl) ⟨220199, by rfl⟩ : syracuseStep 1174397 = 440399) (by norm_num)
theorem B1174421 : Blo 782338 1174421 := bbase (se 6 (by rfl) ⟨27525, by rfl⟩ : syracuseStep 1174421 = 55051) (by norm_num)
theorem B1174445 : Blo 782338 1174445 := bbase (se 3 (by rfl) ⟨220208, by rfl⟩ : syracuseStep 1174445 = 440417) (by norm_num)
theorem B1764269 : Blo 782338 1764269 := bbase (se 3 (by rfl) ⟨330800, by rfl⟩ : syracuseStep 1764269 = 661601) (by norm_num)
theorem B1174469 : Blo 782338 1174469 := bbase (se 4 (by rfl) ⟨110106, by rfl⟩ : syracuseStep 1174469 = 220213) (by norm_num)
theorem B1174493 : Blo 782338 1174493 := bbase (se 3 (by rfl) ⟨220217, by rfl⟩ : syracuseStep 1174493 = 440435) (by norm_num)
theorem B1174517 : Blo 782338 1174517 := bbase (se 5 (by rfl) ⟨55055, by rfl⟩ : syracuseStep 1174517 = 110111) (by norm_num)
theorem B1764341 : Blo 782338 1764341 := bbase (se 5 (by rfl) ⟨82703, by rfl⟩ : syracuseStep 1764341 = 165407) (by norm_num)
theorem B2649077 : Blo 782338 2649077 := bbase (se 5 (by rfl) ⟨124175, by rfl⟩ : syracuseStep 2649077 = 248351) (by norm_num)
theorem B1174541 : Blo 782338 1174541 := bbase (se 3 (by rfl) ⟨220226, by rfl⟩ : syracuseStep 1174541 = 440453) (by norm_num)
theorem B846865 : Blo 782338 846865 := bbase (se 2 (by rfl) ⟨317574, by rfl⟩ : syracuseStep 846865 = 635149) (by norm_num)
theorem B1174565 : Blo 782338 1174565 := bbase (se 4 (by rfl) ⟨110115, by rfl⟩ : syracuseStep 1174565 = 220231) (by norm_num)
theorem B1174589 : Blo 782338 1174589 := bbase (se 3 (by rfl) ⟨220235, by rfl⟩ : syracuseStep 1174589 = 440471) (by norm_num)
theorem B1764413 : Blo 782338 1764413 := bbase (se 3 (by rfl) ⟨330827, by rfl⟩ : syracuseStep 1764413 = 661655) (by norm_num)
theorem B1174613 : Blo 782338 1174613 := bbase (se 8 (by rfl) ⟨6882, by rfl⟩ : syracuseStep 1174613 = 13765) (by norm_num)
theorem B1174637 : Blo 782338 1174637 := bbase (se 3 (by rfl) ⟨220244, by rfl⟩ : syracuseStep 1174637 = 440489) (by norm_num)
theorem B1174661 : Blo 782338 1174661 := bbase (se 4 (by rfl) ⟨110124, by rfl⟩ : syracuseStep 1174661 = 220249) (by norm_num)
theorem B1764485 : Blo 782338 1764485 := bbase (se 4 (by rfl) ⟨165420, by rfl⟩ : syracuseStep 1764485 = 330841) (by norm_num)
theorem B1174685 : Blo 782338 1174685 := bbase (se 3 (by rfl) ⟨220253, by rfl⟩ : syracuseStep 1174685 = 440507) (by norm_num)
theorem B1174709 : Blo 782338 1174709 := bbase (se 5 (by rfl) ⟨55064, by rfl⟩ : syracuseStep 1174709 = 110129) (by norm_num)
theorem B1174733 : Blo 782338 1174733 := bbase (se 3 (by rfl) ⟨220262, by rfl⟩ : syracuseStep 1174733 = 440525) (by norm_num)
theorem B1764557 : Blo 782338 1764557 := bbase (se 3 (by rfl) ⟨330854, by rfl⟩ : syracuseStep 1764557 = 661709) (by norm_num)
theorem B1174757 : Blo 782338 1174757 := bbase (se 4 (by rfl) ⟨110133, by rfl⟩ : syracuseStep 1174757 = 220267) (by norm_num)
theorem B1174781 : Blo 782338 1174781 := bbase (se 3 (by rfl) ⟨220271, by rfl⟩ : syracuseStep 1174781 = 440543) (by norm_num)
theorem B1174805 : Blo 782338 1174805 := bbase (se 6 (by rfl) ⟨27534, by rfl⟩ : syracuseStep 1174805 = 55069) (by norm_num)
theorem B1764629 : Blo 782338 1764629 := bbase (se 6 (by rfl) ⟨41358, by rfl⟩ : syracuseStep 1764629 = 82717) (by norm_num)
theorem B3763493 : Blo 782338 3763493 := bbase (se 4 (by rfl) ⟨352827, by rfl⟩ : syracuseStep 3763493 = 705655) (by norm_num)
theorem B1174829 : Blo 782338 1174829 := bbase (se 3 (by rfl) ⟨220280, by rfl⟩ : syracuseStep 1174829 = 440561) (by norm_num)
theorem B1174853 : Blo 782338 1174853 := bbase (se 4 (by rfl) ⟨110142, by rfl⟩ : syracuseStep 1174853 = 220285) (by norm_num)
theorem B1174877 : Blo 782338 1174877 := bbase (se 3 (by rfl) ⟨220289, by rfl⟩ : syracuseStep 1174877 = 440579) (by norm_num)
theorem B1764701 : Blo 782338 1764701 := bbase (se 3 (by rfl) ⟨330881, by rfl⟩ : syracuseStep 1764701 = 661763) (by norm_num)
theorem B1174901 : Blo 782338 1174901 := bbase (se 5 (by rfl) ⟨55073, by rfl⟩ : syracuseStep 1174901 = 110147) (by norm_num)
theorem B1174925 : Blo 782338 1174925 := bbase (se 3 (by rfl) ⟨220298, by rfl⟩ : syracuseStep 1174925 = 440597) (by norm_num)
theorem B1174949 : Blo 782338 1174949 := bbase (se 4 (by rfl) ⟨110151, by rfl⟩ : syracuseStep 1174949 = 220303) (by norm_num)
theorem B1764773 : Blo 782338 1764773 := bbase (se 4 (by rfl) ⟨165447, by rfl⟩ : syracuseStep 1764773 = 330895) (by norm_num)
theorem B2649509 : Blo 782338 2649509 := bbase (se 4 (by rfl) ⟨248391, by rfl⟩ : syracuseStep 2649509 = 496783) (by norm_num)
theorem B1174973 : Blo 782338 1174973 := bbase (se 3 (by rfl) ⟨220307, by rfl⟩ : syracuseStep 1174973 = 440615) (by norm_num)
theorem B1174997 : Blo 782338 1174997 := bbase (se 7 (by rfl) ⟨13769, by rfl⟩ : syracuseStep 1174997 = 27539) (by norm_num)
theorem B1175021 : Blo 782338 1175021 := bbase (se 3 (by rfl) ⟨220316, by rfl⟩ : syracuseStep 1175021 = 440633) (by norm_num)
theorem B1764845 : Blo 782338 1764845 := bbase (se 3 (by rfl) ⟨330908, by rfl⟩ : syracuseStep 1764845 = 661817) (by norm_num)
theorem B1175045 : Blo 782338 1175045 := bbase (se 4 (by rfl) ⟨110160, by rfl⟩ : syracuseStep 1175045 = 220321) (by norm_num)
theorem B880141 : Blo 782338 880141 := bbase (se 3 (by rfl) ⟨165026, by rfl⟩ : syracuseStep 880141 = 330053) (by norm_num)
theorem B1175069 : Blo 782338 1175069 := bbase (se 3 (by rfl) ⟨220325, by rfl⟩ : syracuseStep 1175069 = 440651) (by norm_num)
theorem B880177 : Blo 782338 880177 := bbase (se 2 (by rfl) ⟨330066, by rfl⟩ : syracuseStep 880177 = 660133) (by norm_num)
theorem B1175093 : Blo 782338 1175093 := bbase (se 5 (by rfl) ⟨55082, by rfl⟩ : syracuseStep 1175093 = 110165) (by norm_num)
theorem B1764917 : Blo 782338 1764917 := bbase (se 5 (by rfl) ⟨82730, by rfl⟩ : syracuseStep 1764917 = 165461) (by norm_num)
theorem B1175117 : Blo 782338 1175117 := bbase (se 3 (by rfl) ⟨220334, by rfl⟩ : syracuseStep 1175117 = 440669) (by norm_num)
theorem B880213 : Blo 782338 880213 := bbase (se 8 (by rfl) ⟨5157, by rfl⟩ : syracuseStep 880213 = 10315) (by norm_num)
theorem B1175141 : Blo 782338 1175141 := bbase (se 4 (by rfl) ⟨110169, by rfl⟩ : syracuseStep 1175141 = 220339) (by norm_num)
theorem B880249 : Blo 782338 880249 := bbase (se 2 (by rfl) ⟨330093, by rfl⟩ : syracuseStep 880249 = 660187) (by norm_num)
theorem B1175165 : Blo 782338 1175165 := bbase (se 3 (by rfl) ⟨220343, by rfl⟩ : syracuseStep 1175165 = 440687) (by norm_num)
theorem B1764989 : Blo 782338 1764989 := bbase (se 3 (by rfl) ⟨330935, by rfl⟩ : syracuseStep 1764989 = 661871) (by norm_num)
theorem B1175189 : Blo 782338 1175189 := bbase (se 6 (by rfl) ⟨27543, by rfl⟩ : syracuseStep 1175189 = 55087) (by norm_num)
theorem B880285 : Blo 782338 880285 := bbase (se 3 (by rfl) ⟨165053, by rfl⟩ : syracuseStep 880285 = 330107) (by norm_num)
theorem B1175213 : Blo 782338 1175213 := bbase (se 3 (by rfl) ⟨220352, by rfl⟩ : syracuseStep 1175213 = 440705) (by norm_num)
theorem B880321 : Blo 782338 880321 := bbase (se 2 (by rfl) ⟨330120, by rfl⟩ : syracuseStep 880321 = 660241) (by norm_num)
theorem B1175237 : Blo 782338 1175237 := bbase (se 4 (by rfl) ⟨110178, by rfl⟩ : syracuseStep 1175237 = 220357) (by norm_num)
theorem B1765061 : Blo 782338 1765061 := bbase (se 4 (by rfl) ⟨165474, by rfl⟩ : syracuseStep 1765061 = 330949) (by norm_num)
theorem B1175261 : Blo 782338 1175261 := bbase (se 3 (by rfl) ⟨220361, by rfl⟩ : syracuseStep 1175261 = 440723) (by norm_num)
theorem B880357 : Blo 782338 880357 := bbase (se 4 (by rfl) ⟨82533, by rfl⟩ : syracuseStep 880357 = 165067) (by norm_num)
theorem B1175285 : Blo 782338 1175285 := bbase (se 5 (by rfl) ⟨55091, by rfl⟩ : syracuseStep 1175285 = 110183) (by norm_num)
theorem B880393 : Blo 782338 880393 := bbase (se 2 (by rfl) ⟨330147, by rfl⟩ : syracuseStep 880393 = 660295) (by norm_num)
theorem B1175309 : Blo 782338 1175309 := bbase (se 3 (by rfl) ⟨220370, by rfl⟩ : syracuseStep 1175309 = 440741) (by norm_num)
theorem B1765133 : Blo 782338 1765133 := bbase (se 3 (by rfl) ⟨330962, by rfl⟩ : syracuseStep 1765133 = 661925) (by norm_num)
theorem B1175333 : Blo 782338 1175333 := bbase (se 4 (by rfl) ⟨110187, by rfl⟩ : syracuseStep 1175333 = 220375) (by norm_num)
theorem B880429 : Blo 782338 880429 := bbase (se 3 (by rfl) ⟨165080, by rfl⟩ : syracuseStep 880429 = 330161) (by norm_num)
theorem B1175357 : Blo 782338 1175357 := bbase (se 3 (by rfl) ⟨220379, by rfl⟩ : syracuseStep 1175357 = 440759) (by norm_num)
theorem B880465 : Blo 782338 880465 := bbase (se 2 (by rfl) ⟨330174, by rfl⟩ : syracuseStep 880465 = 660349) (by norm_num)
theorem B1175381 : Blo 782338 1175381 := bbase (se 9 (by rfl) ⟨3443, by rfl⟩ : syracuseStep 1175381 = 6887) (by norm_num)
theorem B1765205 : Blo 782338 1765205 := bbase (se 9 (by rfl) ⟨5171, by rfl⟩ : syracuseStep 1765205 = 10343) (by norm_num)
theorem B2649941 : Blo 782338 2649941 := bbase (se 9 (by rfl) ⟨7763, by rfl⟩ : syracuseStep 2649941 = 15527) (by norm_num)
theorem B1175405 : Blo 782338 1175405 := bbase (se 3 (by rfl) ⟨220388, by rfl⟩ : syracuseStep 1175405 = 440777) (by norm_num)
theorem B880501 : Blo 782338 880501 := bbase (se 5 (by rfl) ⟨41273, by rfl⟩ : syracuseStep 880501 = 82547) (by norm_num)
theorem B2518901 : Blo 782338 2518901 := bbase (se 5 (by rfl) ⟨118073, by rfl⟩ : syracuseStep 2518901 = 236147) (by norm_num)
theorem B1175429 : Blo 782338 1175429 := bbase (se 4 (by rfl) ⟨110196, by rfl⟩ : syracuseStep 1175429 = 220393) (by norm_num)
theorem B880537 : Blo 782338 880537 := bbase (se 2 (by rfl) ⟨330201, by rfl⟩ : syracuseStep 880537 = 660403) (by norm_num)
theorem B1175453 : Blo 782338 1175453 := bbase (se 3 (by rfl) ⟨220397, by rfl⟩ : syracuseStep 1175453 = 440795) (by norm_num)
theorem B1765277 : Blo 782338 1765277 := bbase (se 3 (by rfl) ⟨330989, by rfl⟩ : syracuseStep 1765277 = 661979) (by norm_num)
theorem B1175477 : Blo 782338 1175477 := bbase (se 5 (by rfl) ⟨55100, by rfl⟩ : syracuseStep 1175477 = 110201) (by norm_num)
theorem B880573 : Blo 782338 880573 := bbase (se 3 (by rfl) ⟨165107, by rfl⟩ : syracuseStep 880573 = 330215) (by norm_num)
theorem B1175501 : Blo 782338 1175501 := bbase (se 3 (by rfl) ⟨220406, by rfl⟩ : syracuseStep 1175501 = 440813) (by norm_num)
theorem B880609 : Blo 782338 880609 := bbase (se 2 (by rfl) ⟨330228, by rfl⟩ : syracuseStep 880609 = 660457) (by norm_num)
theorem B1175525 : Blo 782338 1175525 := bbase (se 4 (by rfl) ⟨110205, by rfl⟩ : syracuseStep 1175525 = 220411) (by norm_num)
theorem B1765349 : Blo 782338 1765349 := bbase (se 4 (by rfl) ⟨165501, by rfl⟩ : syracuseStep 1765349 = 331003) (by norm_num)
theorem B1175549 : Blo 782338 1175549 := bbase (se 3 (by rfl) ⟨220415, by rfl⟩ : syracuseStep 1175549 = 440831) (by norm_num)
theorem B880645 : Blo 782338 880645 := bbase (se 4 (by rfl) ⟨82560, by rfl⟩ : syracuseStep 880645 = 165121) (by norm_num)
theorem B1175573 : Blo 782338 1175573 := bbase (se 6 (by rfl) ⟨27552, by rfl⟩ : syracuseStep 1175573 = 55105) (by norm_num)
theorem B2977829 : Blo 782338 2977829 := bbase (se 4 (by rfl) ⟨279171, by rfl⟩ : syracuseStep 2977829 = 558343) (by norm_num)
theorem B880681 : Blo 782338 880681 := bbase (se 2 (by rfl) ⟨330255, by rfl⟩ : syracuseStep 880681 = 660511) (by norm_num)
theorem B1175597 : Blo 782338 1175597 := bbase (se 3 (by rfl) ⟨220424, by rfl⟩ : syracuseStep 1175597 = 440849) (by norm_num)
theorem B1765421 : Blo 782338 1765421 := bbase (se 3 (by rfl) ⟨331016, by rfl⟩ : syracuseStep 1765421 = 662033) (by norm_num)
theorem B1175621 : Blo 782338 1175621 := bbase (se 4 (by rfl) ⟨110214, by rfl⟩ : syracuseStep 1175621 = 220429) (by norm_num)
theorem B880717 : Blo 782338 880717 := bbase (se 3 (by rfl) ⟨165134, by rfl⟩ : syracuseStep 880717 = 330269) (by norm_num)
theorem B1175645 : Blo 782338 1175645 := bbase (se 3 (by rfl) ⟨220433, by rfl⟩ : syracuseStep 1175645 = 440867) (by norm_num)
theorem B880753 : Blo 782338 880753 := bbase (se 2 (by rfl) ⟨330282, by rfl⟩ : syracuseStep 880753 = 660565) (by norm_num)
theorem B1175669 : Blo 782338 1175669 := bbase (se 5 (by rfl) ⟨55109, by rfl⟩ : syracuseStep 1175669 = 110219) (by norm_num)
theorem B1765493 : Blo 782338 1765493 := bbase (se 5 (by rfl) ⟨82757, by rfl⟩ : syracuseStep 1765493 = 165515) (by norm_num)
theorem B1175693 : Blo 782338 1175693 := bbase (se 3 (by rfl) ⟨220442, by rfl⟩ : syracuseStep 1175693 = 440885) (by norm_num)
theorem B880789 : Blo 782338 880789 := bbase (se 6 (by rfl) ⟨20643, by rfl⟩ : syracuseStep 880789 = 41287) (by norm_num)
theorem B1175717 : Blo 782338 1175717 := bbase (se 4 (by rfl) ⟨110223, by rfl⟩ : syracuseStep 1175717 = 220447) (by norm_num)
theorem B880825 : Blo 782338 880825 := bbase (se 2 (by rfl) ⟨330309, by rfl⟩ : syracuseStep 880825 = 660619) (by norm_num)
theorem B1175741 : Blo 782338 1175741 := bbase (se 3 (by rfl) ⟨220451, by rfl⟩ : syracuseStep 1175741 = 440903) (by norm_num)
theorem B1765565 : Blo 782338 1765565 := bbase (se 3 (by rfl) ⟨331043, by rfl⟩ : syracuseStep 1765565 = 662087) (by norm_num)
theorem B1175765 : Blo 782338 1175765 := bbase (se 7 (by rfl) ⟨13778, by rfl⟩ : syracuseStep 1175765 = 27557) (by norm_num)
theorem B880861 : Blo 782338 880861 := bbase (se 3 (by rfl) ⟨165161, by rfl⟩ : syracuseStep 880861 = 330323) (by norm_num)
theorem B3961061 : Blo 782338 3961061 := bbase (se 4 (by rfl) ⟨371349, by rfl⟩ : syracuseStep 3961061 = 742699) (by norm_num)
theorem B1175789 : Blo 782338 1175789 := bbase (se 3 (by rfl) ⟨220460, by rfl⟩ : syracuseStep 1175789 = 440921) (by norm_num)
theorem B880897 : Blo 782338 880897 := bbase (se 2 (by rfl) ⟨330336, by rfl⟩ : syracuseStep 880897 = 660673) (by norm_num)
theorem B1175813 : Blo 782338 1175813 := bbase (se 4 (by rfl) ⟨110232, by rfl⟩ : syracuseStep 1175813 = 220465) (by norm_num)
theorem B1765637 : Blo 782338 1765637 := bbase (se 4 (by rfl) ⟨165528, by rfl⟩ : syracuseStep 1765637 = 331057) (by norm_num)
theorem B2650373 : Blo 782338 2650373 := bbase (se 4 (by rfl) ⟨248472, by rfl⟩ : syracuseStep 2650373 = 496945) (by norm_num)
theorem B1175837 : Blo 782338 1175837 := bbase (se 3 (by rfl) ⟨220469, by rfl⟩ : syracuseStep 1175837 = 440939) (by norm_num)
theorem B880933 : Blo 782338 880933 := bbase (se 4 (by rfl) ⟨82587, by rfl⟩ : syracuseStep 880933 = 165175) (by norm_num)
theorem B1175861 : Blo 782338 1175861 := bbase (se 5 (by rfl) ⟨55118, by rfl⟩ : syracuseStep 1175861 = 110237) (by norm_num)
theorem B2978117 : Blo 782338 2978117 := bbase (se 4 (by rfl) ⟨279198, by rfl⟩ : syracuseStep 2978117 = 558397) (by norm_num)
theorem B880969 : Blo 782338 880969 := bbase (se 2 (by rfl) ⟨330363, by rfl⟩ : syracuseStep 880969 = 660727) (by norm_num)
theorem B1175885 : Blo 782338 1175885 := bbase (se 3 (by rfl) ⟨220478, by rfl⟩ : syracuseStep 1175885 = 440957) (by norm_num)
theorem B1765709 : Blo 782338 1765709 := bbase (se 3 (by rfl) ⟨331070, by rfl⟩ : syracuseStep 1765709 = 662141) (by norm_num)
theorem B48329045 : Blo 782338 48329045 := bbase (se 10 (by rfl) ⟨70794, by rfl⟩ : syracuseStep 48329045 = 141589) (by norm_num)
theorem B1175909 : Blo 782338 1175909 := bbase (se 4 (by rfl) ⟨110241, by rfl⟩ : syracuseStep 1175909 = 220483) (by norm_num)
theorem B2388325 : Blo 782338 2388325 := bbase (se 4 (by rfl) ⟨223905, by rfl⟩ : syracuseStep 2388325 = 447811) (by norm_num)
theorem B881005 : Blo 782338 881005 := bbase (se 3 (by rfl) ⟨165188, by rfl⟩ : syracuseStep 881005 = 330377) (by norm_num)
theorem B1175933 : Blo 782338 1175933 := bbase (se 3 (by rfl) ⟨220487, by rfl⟩ : syracuseStep 1175933 = 440975) (by norm_num)
theorem B881041 : Blo 782338 881041 := bbase (se 2 (by rfl) ⟨330390, by rfl⟩ : syracuseStep 881041 = 660781) (by norm_num)
theorem B1175957 : Blo 782338 1175957 := bbase (se 6 (by rfl) ⟨27561, by rfl⟩ : syracuseStep 1175957 = 55123) (by norm_num)
theorem B1765781 : Blo 782338 1765781 := bbase (se 6 (by rfl) ⟨41385, by rfl⟩ : syracuseStep 1765781 = 82771) (by norm_num)
theorem B1175981 : Blo 782338 1175981 := bbase (se 3 (by rfl) ⟨220496, by rfl⟩ : syracuseStep 1175981 = 440993) (by norm_num)
theorem B881077 : Blo 782338 881077 := bbase (se 5 (by rfl) ⟨41300, by rfl⟩ : syracuseStep 881077 = 82601) (by norm_num)
theorem B1176005 : Blo 782338 1176005 := bbase (se 4 (by rfl) ⟨110250, by rfl⟩ : syracuseStep 1176005 = 220501) (by norm_num)
theorem B881113 : Blo 782338 881113 := bbase (se 2 (by rfl) ⟨330417, by rfl⟩ : syracuseStep 881113 = 660835) (by norm_num)
theorem B1176029 : Blo 782338 1176029 := bbase (se 3 (by rfl) ⟨220505, by rfl⟩ : syracuseStep 1176029 = 441011) (by norm_num)
theorem B1765853 : Blo 782338 1765853 := bbase (se 3 (by rfl) ⟨331097, by rfl⟩ : syracuseStep 1765853 = 662195) (by norm_num)
theorem B1176053 : Blo 782338 1176053 := bbase (se 5 (by rfl) ⟨55127, by rfl⟩ : syracuseStep 1176053 = 110255) (by norm_num)
theorem B881149 : Blo 782338 881149 := bbase (se 3 (by rfl) ⟨165215, by rfl⟩ : syracuseStep 881149 = 330431) (by norm_num)
theorem B1176077 : Blo 782338 1176077 := bbase (se 3 (by rfl) ⟨220514, by rfl⟩ : syracuseStep 1176077 = 441029) (by norm_num)
theorem B881185 : Blo 782338 881185 := bbase (se 2 (by rfl) ⟨330444, by rfl⟩ : syracuseStep 881185 = 660889) (by norm_num)
theorem B1176101 : Blo 782338 1176101 := bbase (se 4 (by rfl) ⟨110259, by rfl⟩ : syracuseStep 1176101 = 220519) (by norm_num)
theorem B1765925 : Blo 782338 1765925 := bbase (se 4 (by rfl) ⟨165555, by rfl⟩ : syracuseStep 1765925 = 331111) (by norm_num)
theorem B1274405 : Blo 782338 1274405 := bbase (se 4 (by rfl) ⟨119475, by rfl⟩ : syracuseStep 1274405 = 238951) (by norm_num)
theorem B1176125 : Blo 782338 1176125 := bbase (se 3 (by rfl) ⟨220523, by rfl⟩ : syracuseStep 1176125 = 441047) (by norm_num)
theorem B881221 : Blo 782338 881221 := bbase (se 4 (by rfl) ⟨82614, by rfl⟩ : syracuseStep 881221 = 165229) (by norm_num)
theorem B1176149 : Blo 782338 1176149 := bbase (se 8 (by rfl) ⟨6891, by rfl⟩ : syracuseStep 1176149 = 13783) (by norm_num)
theorem B1340005 : Blo 782338 1340005 := bbase (se 4 (by rfl) ⟨125625, by rfl⟩ : syracuseStep 1340005 = 251251) (by norm_num)
theorem B881257 : Blo 782338 881257 := bbase (se 2 (by rfl) ⟨330471, by rfl⟩ : syracuseStep 881257 = 660943) (by norm_num)
theorem B1176173 : Blo 782338 1176173 := bbase (se 3 (by rfl) ⟨220532, by rfl⟩ : syracuseStep 1176173 = 441065) (by norm_num)
theorem B1765997 : Blo 782338 1765997 := bbase (se 3 (by rfl) ⟨331124, by rfl⟩ : syracuseStep 1765997 = 662249) (by norm_num)
theorem B1176197 : Blo 782338 1176197 := bbase (se 4 (by rfl) ⟨110268, by rfl⟩ : syracuseStep 1176197 = 220537) (by norm_num)
theorem B881293 : Blo 782338 881293 := bbase (se 3 (by rfl) ⟨165242, by rfl⟩ : syracuseStep 881293 = 330485) (by norm_num)
theorem B1176221 : Blo 782338 1176221 := bbase (se 3 (by rfl) ⟨220541, by rfl⟩ : syracuseStep 1176221 = 441083) (by norm_num)
theorem B881329 : Blo 782338 881329 := bbase (se 2 (by rfl) ⟨330498, by rfl⟩ : syracuseStep 881329 = 660997) (by norm_num)
theorem B1176245 : Blo 782338 1176245 := bbase (se 5 (by rfl) ⟨55136, by rfl⟩ : syracuseStep 1176245 = 110273) (by norm_num)
theorem B1766069 : Blo 782338 1766069 := bbase (se 5 (by rfl) ⟨82784, by rfl⟩ : syracuseStep 1766069 = 165569) (by norm_num)
theorem B2650805 : Blo 782338 2650805 := bbase (se 5 (by rfl) ⟨124256, by rfl⟩ : syracuseStep 2650805 = 248513) (by norm_num)
theorem B1176269 : Blo 782338 1176269 := bbase (se 3 (by rfl) ⟨220550, by rfl⟩ : syracuseStep 1176269 = 441101) (by norm_num)
theorem B881365 : Blo 782338 881365 := bbase (se 7 (by rfl) ⟨10328, by rfl⟩ : syracuseStep 881365 = 20657) (by norm_num)
theorem B1176293 : Blo 782338 1176293 := bbase (se 4 (by rfl) ⟨110277, by rfl⟩ : syracuseStep 1176293 = 220555) (by norm_num)
theorem B881401 : Blo 782338 881401 := bbase (se 2 (by rfl) ⟨330525, by rfl⟩ : syracuseStep 881401 = 661051) (by norm_num)
theorem B1176317 : Blo 782338 1176317 := bbase (se 3 (by rfl) ⟨220559, by rfl⟩ : syracuseStep 1176317 = 441119) (by norm_num)
theorem B1766141 : Blo 782338 1766141 := bbase (se 3 (by rfl) ⟨331151, by rfl⟩ : syracuseStep 1766141 = 662303) (by norm_num)
theorem B1176341 : Blo 782338 1176341 := bbase (se 6 (by rfl) ⟨27570, by rfl⟩ : syracuseStep 1176341 = 55141) (by norm_num)
theorem B881437 : Blo 782338 881437 := bbase (se 3 (by rfl) ⟨165269, by rfl⟩ : syracuseStep 881437 = 330539) (by norm_num)
theorem B1176365 : Blo 782338 1176365 := bbase (se 3 (by rfl) ⟨220568, by rfl⟩ : syracuseStep 1176365 = 441137) (by norm_num)
theorem B881473 : Blo 782338 881473 := bbase (se 2 (by rfl) ⟨330552, by rfl⟩ : syracuseStep 881473 = 661105) (by norm_num)
theorem B1176389 : Blo 782338 1176389 := bbase (se 4 (by rfl) ⟨110286, by rfl⟩ : syracuseStep 1176389 = 220573) (by norm_num)
theorem B1766213 : Blo 782338 1766213 := bbase (se 4 (by rfl) ⟨165582, by rfl⟩ : syracuseStep 1766213 = 331165) (by norm_num)
theorem B1176413 : Blo 782338 1176413 := bbase (se 3 (by rfl) ⟨220577, by rfl⟩ : syracuseStep 1176413 = 441155) (by norm_num)
theorem B881509 : Blo 782338 881509 := bbase (se 4 (by rfl) ⟨82641, by rfl⟩ : syracuseStep 881509 = 165283) (by norm_num)
theorem B1176437 : Blo 782338 1176437 := bbase (se 5 (by rfl) ⟨55145, by rfl⟩ : syracuseStep 1176437 = 110291) (by norm_num)
theorem B881545 : Blo 782338 881545 := bbase (se 2 (by rfl) ⟨330579, by rfl⟩ : syracuseStep 881545 = 661159) (by norm_num)
theorem B1176461 : Blo 782338 1176461 := bbase (se 3 (by rfl) ⟨220586, by rfl⟩ : syracuseStep 1176461 = 441173) (by norm_num)
theorem B1766285 : Blo 782338 1766285 := bbase (se 3 (by rfl) ⟨331178, by rfl⟩ : syracuseStep 1766285 = 662357) (by norm_num)
theorem B1176485 : Blo 782338 1176485 := bbase (se 4 (by rfl) ⟨110295, by rfl⟩ : syracuseStep 1176485 = 220591) (by norm_num)
theorem B881581 : Blo 782338 881581 := bbase (se 3 (by rfl) ⟨165296, by rfl⟩ : syracuseStep 881581 = 330593) (by norm_num)
theorem B1176509 : Blo 782338 1176509 := bbase (se 3 (by rfl) ⟨220595, by rfl⟩ : syracuseStep 1176509 = 441191) (by norm_num)
theorem B881617 : Blo 782338 881617 := bbase (se 2 (by rfl) ⟨330606, by rfl⟩ : syracuseStep 881617 = 661213) (by norm_num)
theorem B1176533 : Blo 782338 1176533 := bbase (se 7 (by rfl) ⟨13787, by rfl⟩ : syracuseStep 1176533 = 27575) (by norm_num)
theorem B1766357 : Blo 782338 1766357 := bbase (se 7 (by rfl) ⟨20699, by rfl⟩ : syracuseStep 1766357 = 41399) (by norm_num)
theorem B1176557 : Blo 782338 1176557 := bbase (se 3 (by rfl) ⟨220604, by rfl⟩ : syracuseStep 1176557 = 441209) (by norm_num)
theorem B881653 : Blo 782338 881653 := bbase (se 5 (by rfl) ⟨41327, by rfl⟩ : syracuseStep 881653 = 82655) (by norm_num)
theorem B1176581 : Blo 782338 1176581 := bbase (se 4 (by rfl) ⟨110304, by rfl⟩ : syracuseStep 1176581 = 220609) (by norm_num)
theorem B881689 : Blo 782338 881689 := bbase (se 2 (by rfl) ⟨330633, by rfl⟩ : syracuseStep 881689 = 661267) (by norm_num)
theorem B1176605 : Blo 782338 1176605 := bbase (se 3 (by rfl) ⟨220613, by rfl⟩ : syracuseStep 1176605 = 441227) (by norm_num)
theorem B1766429 : Blo 782338 1766429 := bbase (se 3 (by rfl) ⟨331205, by rfl⟩ : syracuseStep 1766429 = 662411) (by norm_num)
theorem B1176629 : Blo 782338 1176629 := bbase (se 5 (by rfl) ⟨55154, by rfl⟩ : syracuseStep 1176629 = 110309) (by norm_num)
theorem B881725 : Blo 782338 881725 := bbase (se 3 (by rfl) ⟨165323, by rfl⟩ : syracuseStep 881725 = 330647) (by norm_num)
theorem B1176653 : Blo 782338 1176653 := bbase (se 3 (by rfl) ⟨220622, by rfl⟩ : syracuseStep 1176653 = 441245) (by norm_num)
theorem B5960789 : Blo 782338 5960789 := bbase (se 8 (by rfl) ⟨34926, by rfl⟩ : syracuseStep 5960789 = 69853) (by norm_num)
theorem B881761 : Blo 782338 881761 := bbase (se 2 (by rfl) ⟨330660, by rfl⟩ : syracuseStep 881761 = 661321) (by norm_num)
theorem B2651237 : Blo 782338 2651237 := bbase (se 4 (by rfl) ⟨248553, by rfl⟩ : syracuseStep 2651237 = 497107) (by norm_num)
theorem B1176677 : Blo 782338 1176677 := bbase (se 4 (by rfl) ⟨110313, by rfl⟩ : syracuseStep 1176677 = 220627) (by norm_num)
theorem B1766501 : Blo 782338 1766501 := bbase (se 4 (by rfl) ⟨165609, by rfl⟩ : syracuseStep 1766501 = 331219) (by norm_num)
theorem B1176701 : Blo 782338 1176701 := bbase (se 3 (by rfl) ⟨220631, by rfl⟩ : syracuseStep 1176701 = 441263) (by norm_num)
theorem B881797 : Blo 782338 881797 := bbase (se 4 (by rfl) ⟨82668, by rfl⟩ : syracuseStep 881797 = 165337) (by norm_num)
theorem B1176725 : Blo 782338 1176725 := bbase (se 6 (by rfl) ⟨27579, by rfl⟩ : syracuseStep 1176725 = 55159) (by norm_num)
theorem B881833 : Blo 782338 881833 := bbase (se 2 (by rfl) ⟨330687, by rfl⟩ : syracuseStep 881833 = 661375) (by norm_num)
theorem B1176749 : Blo 782338 1176749 := bbase (se 3 (by rfl) ⟨220640, by rfl⟩ : syracuseStep 1176749 = 441281) (by norm_num)
theorem B1766573 : Blo 782338 1766573 := bbase (se 3 (by rfl) ⟨331232, by rfl⟩ : syracuseStep 1766573 = 662465) (by norm_num)
theorem B1176773 : Blo 782338 1176773 := bbase (se 4 (by rfl) ⟨110322, by rfl⟩ : syracuseStep 1176773 = 220645) (by norm_num)
theorem B4027589 : Blo 782338 4027589 := bbase (se 4 (by rfl) ⟨377586, by rfl⟩ : syracuseStep 4027589 = 755173) (by norm_num)
theorem B881869 : Blo 782338 881869 := bbase (se 3 (by rfl) ⟨165350, by rfl⟩ : syracuseStep 881869 = 330701) (by norm_num)
theorem B1176797 : Blo 782338 1176797 := bbase (se 3 (by rfl) ⟨220649, by rfl⟩ : syracuseStep 1176797 = 441299) (by norm_num)
theorem B881905 : Blo 782338 881905 := bbase (se 2 (by rfl) ⟨330714, by rfl⟩ : syracuseStep 881905 = 661429) (by norm_num)
theorem B1176821 : Blo 782338 1176821 := bbase (se 5 (by rfl) ⟨55163, by rfl⟩ : syracuseStep 1176821 = 110327) (by norm_num)
theorem B1766645 : Blo 782338 1766645 := bbase (se 5 (by rfl) ⟨82811, by rfl⟩ : syracuseStep 1766645 = 165623) (by norm_num)
theorem B1176845 : Blo 782338 1176845 := bbase (se 3 (by rfl) ⟨220658, by rfl⟩ : syracuseStep 1176845 = 441317) (by norm_num)
theorem B881941 : Blo 782338 881941 := bbase (se 6 (by rfl) ⟨20670, by rfl⟩ : syracuseStep 881941 = 41341) (by norm_num)
theorem B1176869 : Blo 782338 1176869 := bbase (se 4 (by rfl) ⟨110331, by rfl⟩ : syracuseStep 1176869 = 220663) (by norm_num)
theorem B881977 : Blo 782338 881977 := bbase (se 2 (by rfl) ⟨330741, by rfl⟩ : syracuseStep 881977 = 661483) (by norm_num)
theorem B1176893 : Blo 782338 1176893 := bbase (se 3 (by rfl) ⟨220667, by rfl⟩ : syracuseStep 1176893 = 441335) (by norm_num)
theorem B1766717 : Blo 782338 1766717 := bbase (se 3 (by rfl) ⟨331259, by rfl⟩ : syracuseStep 1766717 = 662519) (by norm_num)
theorem B1176917 : Blo 782338 1176917 := bbase (se 13 (by rfl) ⟨215, by rfl⟩ : syracuseStep 1176917 = 431) (by norm_num)
theorem B882013 : Blo 782338 882013 := bbase (se 3 (by rfl) ⟨165377, by rfl⟩ : syracuseStep 882013 = 330755) (by norm_num)
theorem B1176941 : Blo 782338 1176941 := bbase (se 3 (by rfl) ⟨220676, by rfl⟩ : syracuseStep 1176941 = 441353) (by norm_num)
theorem B882049 : Blo 782338 882049 := bbase (se 2 (by rfl) ⟨330768, by rfl⟩ : syracuseStep 882049 = 661537) (by norm_num)
theorem B1176965 : Blo 782338 1176965 := bbase (se 4 (by rfl) ⟨110340, by rfl⟩ : syracuseStep 1176965 = 220681) (by norm_num)
theorem B1766789 : Blo 782338 1766789 := bbase (se 4 (by rfl) ⟨165636, by rfl⟩ : syracuseStep 1766789 = 331273) (by norm_num)
theorem B1176989 : Blo 782338 1176989 := bbase (se 3 (by rfl) ⟨220685, by rfl⟩ : syracuseStep 1176989 = 441371) (by norm_num)
theorem B882085 : Blo 782338 882085 := bbase (se 4 (by rfl) ⟨82695, by rfl⟩ : syracuseStep 882085 = 165391) (by norm_num)
theorem B1177013 : Blo 782338 1177013 := bbase (se 5 (by rfl) ⟨55172, by rfl⟩ : syracuseStep 1177013 = 110345) (by norm_num)
theorem B882121 : Blo 782338 882121 := bbase (se 2 (by rfl) ⟨330795, by rfl⟩ : syracuseStep 882121 = 661591) (by norm_num)
theorem B1177037 : Blo 782338 1177037 := bbase (se 3 (by rfl) ⟨220694, by rfl⟩ : syracuseStep 1177037 = 441389) (by norm_num)
theorem B1766861 : Blo 782338 1766861 := bbase (se 3 (by rfl) ⟨331286, by rfl⟩ : syracuseStep 1766861 = 662573) (by norm_num)
theorem B2979301 : Blo 782338 2979301 := bbase (se 4 (by rfl) ⟨279309, by rfl⟩ : syracuseStep 2979301 = 558619) (by norm_num)
theorem B1177061 : Blo 782338 1177061 := bbase (se 4 (by rfl) ⟨110349, by rfl⟩ : syracuseStep 1177061 = 220699) (by norm_num)
theorem B882157 : Blo 782338 882157 := bbase (se 3 (by rfl) ⟨165404, by rfl⟩ : syracuseStep 882157 = 330809) (by norm_num)
theorem B3962357 : Blo 782338 3962357 := bbase (se 5 (by rfl) ⟨185735, by rfl⟩ : syracuseStep 3962357 = 371471) (by norm_num)
theorem B1177085 : Blo 782338 1177085 := bbase (se 3 (by rfl) ⟨220703, by rfl⟩ : syracuseStep 1177085 = 441407) (by norm_num)
theorem B882193 : Blo 782338 882193 := bbase (se 2 (by rfl) ⟨330822, by rfl⟩ : syracuseStep 882193 = 661645) (by norm_num)
theorem B1177109 : Blo 782338 1177109 := bbase (se 6 (by rfl) ⟨27588, by rfl⟩ : syracuseStep 1177109 = 55177) (by norm_num)
theorem B1766933 : Blo 782338 1766933 := bbase (se 6 (by rfl) ⟨41412, by rfl⟩ : syracuseStep 1766933 = 82825) (by norm_num)
theorem B2651669 : Blo 782338 2651669 := bbase (se 6 (by rfl) ⟨62148, by rfl⟩ : syracuseStep 2651669 = 124297) (by norm_num)
theorem B1177133 : Blo 782338 1177133 := bbase (se 3 (by rfl) ⟨220712, by rfl⟩ : syracuseStep 1177133 = 441425) (by norm_num)
theorem B7534133 : Blo 782338 7534133 := bbase (se 5 (by rfl) ⟨353162, by rfl⟩ : syracuseStep 7534133 = 706325) (by norm_num)
theorem B882229 : Blo 782338 882229 := bbase (se 5 (by rfl) ⟨41354, by rfl⟩ : syracuseStep 882229 = 82709) (by norm_num)
theorem B1177157 : Blo 782338 1177157 := bbase (se 4 (by rfl) ⟨110358, by rfl⟩ : syracuseStep 1177157 = 220717) (by norm_num)
theorem B882265 : Blo 782338 882265 := bbase (se 2 (by rfl) ⟨330849, by rfl⟩ : syracuseStep 882265 = 661699) (by norm_num)
theorem B1177181 : Blo 782338 1177181 := bbase (se 3 (by rfl) ⟨220721, by rfl⟩ : syracuseStep 1177181 = 441443) (by norm_num)
theorem B1767005 : Blo 782338 1767005 := bbase (se 3 (by rfl) ⟨331313, by rfl⟩ : syracuseStep 1767005 = 662627) (by norm_num)
theorem B1177205 : Blo 782338 1177205 := bbase (se 5 (by rfl) ⟨55181, by rfl⟩ : syracuseStep 1177205 = 110363) (by norm_num)
theorem B882301 : Blo 782338 882301 := bbase (se 3 (by rfl) ⟨165431, by rfl⟩ : syracuseStep 882301 = 330863) (by norm_num)
theorem B2389637 : Blo 782338 2389637 := bbase (se 4 (by rfl) ⟨224028, by rfl⟩ : syracuseStep 2389637 = 448057) (by norm_num)
theorem B1177229 : Blo 782338 1177229 := bbase (se 3 (by rfl) ⟨220730, by rfl⟩ : syracuseStep 1177229 = 441461) (by norm_num)
theorem B882337 : Blo 782338 882337 := bbase (se 2 (by rfl) ⟨330876, by rfl⟩ : syracuseStep 882337 = 661753) (by norm_num)
theorem B1177253 : Blo 782338 1177253 := bbase (se 4 (by rfl) ⟨110367, by rfl⟩ : syracuseStep 1177253 = 220735) (by norm_num)
theorem B1767077 : Blo 782338 1767077 := bbase (se 4 (by rfl) ⟨165663, by rfl⟩ : syracuseStep 1767077 = 331327) (by norm_num)
theorem B5732021 : Blo 782338 5732021 := bbase (se 5 (by rfl) ⟨268688, by rfl⟩ : syracuseStep 5732021 = 537377) (by norm_num)
theorem B1177277 : Blo 782338 1177277 := bbase (se 3 (by rfl) ⟨220739, by rfl⟩ : syracuseStep 1177277 = 441479) (by norm_num)
theorem B882373 : Blo 782338 882373 := bbase (se 4 (by rfl) ⟨82722, by rfl⟩ : syracuseStep 882373 = 165445) (by norm_num)
theorem B1177301 : Blo 782338 1177301 := bbase (se 7 (by rfl) ⟨13796, by rfl⟩ : syracuseStep 1177301 = 27593) (by norm_num)
theorem B882409 : Blo 782338 882409 := bbase (se 2 (by rfl) ⟨330903, by rfl⟩ : syracuseStep 882409 = 661807) (by norm_num)
theorem B1177325 : Blo 782338 1177325 := bbase (se 3 (by rfl) ⟨220748, by rfl⟩ : syracuseStep 1177325 = 441497) (by norm_num)
theorem B1767149 : Blo 782338 1767149 := bbase (se 3 (by rfl) ⟨331340, by rfl⟩ : syracuseStep 1767149 = 662681) (by norm_num)
theorem B1177349 : Blo 782338 1177349 := bbase (se 4 (by rfl) ⟨110376, by rfl⟩ : syracuseStep 1177349 = 220753) (by norm_num)
theorem B882445 : Blo 782338 882445 := bbase (se 3 (by rfl) ⟨165458, by rfl⟩ : syracuseStep 882445 = 330917) (by norm_num)
theorem B2979605 : Blo 782338 2979605 := bbase (se 6 (by rfl) ⟨69834, by rfl⟩ : syracuseStep 2979605 = 139669) (by norm_num)
theorem B1177373 : Blo 782338 1177373 := bbase (se 3 (by rfl) ⟨220757, by rfl⟩ : syracuseStep 1177373 = 441515) (by norm_num)
theorem B882481 : Blo 782338 882481 := bbase (se 2 (by rfl) ⟨330930, by rfl⟩ : syracuseStep 882481 = 661861) (by norm_num)
theorem B1177397 : Blo 782338 1177397 := bbase (se 5 (by rfl) ⟨55190, by rfl⟩ : syracuseStep 1177397 = 110381) (by norm_num)
theorem B1767221 : Blo 782338 1767221 := bbase (se 5 (by rfl) ⟨82838, by rfl⟩ : syracuseStep 1767221 = 165677) (by norm_num)
theorem B1177421 : Blo 782338 1177421 := bbase (se 3 (by rfl) ⟨220766, by rfl⟩ : syracuseStep 1177421 = 441533) (by norm_num)
theorem B882517 : Blo 782338 882517 := bbase (se 9 (by rfl) ⟨2585, by rfl⟩ : syracuseStep 882517 = 5171) (by norm_num)
theorem B1177445 : Blo 782338 1177445 := bbase (se 4 (by rfl) ⟨110385, by rfl⟩ : syracuseStep 1177445 = 220771) (by norm_num)
theorem B849773 : Blo 782338 849773 := bbase (se 3 (by rfl) ⟨159332, by rfl⟩ : syracuseStep 849773 = 318665) (by norm_num)
theorem B882553 : Blo 782338 882553 := bbase (se 2 (by rfl) ⟨330957, by rfl⟩ : syracuseStep 882553 = 661915) (by norm_num)
theorem B1177469 : Blo 782338 1177469 := bbase (se 3 (by rfl) ⟨220775, by rfl⟩ : syracuseStep 1177469 = 441551) (by norm_num)
theorem B1767293 : Blo 782338 1767293 := bbase (se 3 (by rfl) ⟨331367, by rfl⟩ : syracuseStep 1767293 = 662735) (by norm_num)
theorem B1177493 : Blo 782338 1177493 := bbase (se 6 (by rfl) ⟨27597, by rfl⟩ : syracuseStep 1177493 = 55195) (by norm_num)
theorem B882589 : Blo 782338 882589 := bbase (se 3 (by rfl) ⟨165485, by rfl⟩ : syracuseStep 882589 = 330971) (by norm_num)
theorem B1177517 : Blo 782338 1177517 := bbase (se 3 (by rfl) ⟨220784, by rfl⟩ : syracuseStep 1177517 = 441569) (by norm_num)
theorem B882625 : Blo 782338 882625 := bbase (se 2 (by rfl) ⟨330984, by rfl⟩ : syracuseStep 882625 = 661969) (by norm_num)
theorem B1177541 : Blo 782338 1177541 := bbase (se 4 (by rfl) ⟨110394, by rfl⟩ : syracuseStep 1177541 = 220789) (by norm_num)
theorem B1767365 : Blo 782338 1767365 := bbase (se 4 (by rfl) ⟨165690, by rfl⟩ : syracuseStep 1767365 = 331381) (by norm_num)
theorem B2652101 : Blo 782338 2652101 := bbase (se 4 (by rfl) ⟨248634, by rfl⟩ : syracuseStep 2652101 = 497269) (by norm_num)
theorem B1177565 : Blo 782338 1177565 := bbase (se 3 (by rfl) ⟨220793, by rfl⟩ : syracuseStep 1177565 = 441587) (by norm_num)
theorem B882661 : Blo 782338 882661 := bbase (se 4 (by rfl) ⟨82749, by rfl⟩ : syracuseStep 882661 = 165499) (by norm_num)
theorem B1177589 : Blo 782338 1177589 := bbase (se 5 (by rfl) ⟨55199, by rfl⟩ : syracuseStep 1177589 = 110399) (by norm_num)
theorem B882697 : Blo 782338 882697 := bbase (se 2 (by rfl) ⟨331011, by rfl⟩ : syracuseStep 882697 = 662023) (by norm_num)
theorem B1177613 : Blo 782338 1177613 := bbase (se 3 (by rfl) ⟨220802, by rfl⟩ : syracuseStep 1177613 = 441605) (by norm_num)
theorem B1767437 : Blo 782338 1767437 := bbase (se 3 (by rfl) ⟨331394, by rfl⟩ : syracuseStep 1767437 = 662789) (by norm_num)
theorem B1177637 : Blo 782338 1177637 := bbase (se 4 (by rfl) ⟨110403, by rfl⟩ : syracuseStep 1177637 = 220807) (by norm_num)
theorem B882733 : Blo 782338 882733 := bbase (se 3 (by rfl) ⟨165512, by rfl⟩ : syracuseStep 882733 = 331025) (by norm_num)
theorem B1177661 : Blo 782338 1177661 := bbase (se 3 (by rfl) ⟨220811, by rfl⟩ : syracuseStep 1177661 = 441623) (by norm_num)
theorem B882769 : Blo 782338 882769 := bbase (se 2 (by rfl) ⟨331038, by rfl⟩ : syracuseStep 882769 = 662077) (by norm_num)
theorem B1177685 : Blo 782338 1177685 := bbase (se 8 (by rfl) ⟨6900, by rfl⟩ : syracuseStep 1177685 = 13801) (by norm_num)
theorem B1767509 : Blo 782338 1767509 := bbase (se 8 (by rfl) ⟨10356, by rfl⟩ : syracuseStep 1767509 = 20713) (by norm_num)
theorem B1177709 : Blo 782338 1177709 := bbase (se 3 (by rfl) ⟨220820, by rfl⟩ : syracuseStep 1177709 = 441641) (by norm_num)
theorem B882805 : Blo 782338 882805 := bbase (se 5 (by rfl) ⟨41381, by rfl⟩ : syracuseStep 882805 = 82763) (by norm_num)
theorem B1177733 : Blo 782338 1177733 := bbase (se 4 (by rfl) ⟨110412, by rfl⟩ : syracuseStep 1177733 = 220825) (by norm_num)
theorem B882841 : Blo 782338 882841 := bbase (se 2 (by rfl) ⟨331065, by rfl⟩ : syracuseStep 882841 = 662131) (by norm_num)
theorem B1177757 : Blo 782338 1177757 := bbase (se 3 (by rfl) ⟨220829, by rfl⟩ : syracuseStep 1177757 = 441659) (by norm_num)
theorem B1767581 : Blo 782338 1767581 := bbase (se 3 (by rfl) ⟨331421, by rfl⟩ : syracuseStep 1767581 = 662843) (by norm_num)
theorem B1177781 : Blo 782338 1177781 := bbase (se 5 (by rfl) ⟨55208, by rfl⟩ : syracuseStep 1177781 = 110417) (by norm_num)
theorem B882877 : Blo 782338 882877 := bbase (se 3 (by rfl) ⟨165539, by rfl⟩ : syracuseStep 882877 = 331079) (by norm_num)
theorem B1177805 : Blo 782338 1177805 := bbase (se 3 (by rfl) ⟨220838, by rfl⟩ : syracuseStep 1177805 = 441677) (by norm_num)
theorem B882913 : Blo 782338 882913 := bbase (se 2 (by rfl) ⟨331092, by rfl⟩ : syracuseStep 882913 = 662185) (by norm_num)
theorem B1177829 : Blo 782338 1177829 := bbase (se 4 (by rfl) ⟨110421, by rfl⟩ : syracuseStep 1177829 = 220843) (by norm_num)
theorem B1767653 : Blo 782338 1767653 := bbase (se 4 (by rfl) ⟨165717, by rfl⟩ : syracuseStep 1767653 = 331435) (by norm_num)
theorem B1177853 : Blo 782338 1177853 := bbase (se 3 (by rfl) ⟨220847, by rfl⟩ : syracuseStep 1177853 = 441695) (by norm_num)
theorem B3012869 : Blo 782338 3012869 := bbase (se 4 (by rfl) ⟨282456, by rfl⟩ : syracuseStep 3012869 = 564913) (by norm_num)
theorem B882949 : Blo 782338 882949 := bbase (se 4 (by rfl) ⟨82776, by rfl⟩ : syracuseStep 882949 = 165553) (by norm_num)
theorem B1177877 : Blo 782338 1177877 := bbase (se 6 (by rfl) ⟨27606, by rfl⟩ : syracuseStep 1177877 = 55213) (by norm_num)
theorem B882985 : Blo 782338 882985 := bbase (se 2 (by rfl) ⟨331119, by rfl⟩ : syracuseStep 882985 = 662239) (by norm_num)
theorem B1177901 : Blo 782338 1177901 := bbase (se 3 (by rfl) ⟨220856, by rfl⟩ : syracuseStep 1177901 = 441713) (by norm_num)
theorem B1767725 : Blo 782338 1767725 := bbase (se 3 (by rfl) ⟨331448, by rfl⟩ : syracuseStep 1767725 = 662897) (by norm_num)
theorem B1177925 : Blo 782338 1177925 := bbase (se 4 (by rfl) ⟨110430, by rfl⟩ : syracuseStep 1177925 = 220861) (by norm_num)
theorem B883021 : Blo 782338 883021 := bbase (se 3 (by rfl) ⟨165566, by rfl⟩ : syracuseStep 883021 = 331133) (by norm_num)
theorem B1505621 : Blo 782338 1505621 := bbase (se 10 (by rfl) ⟨2205, by rfl⟩ : syracuseStep 1505621 = 4411) (by norm_num)
theorem B1177949 : Blo 782338 1177949 := bbase (se 3 (by rfl) ⟨220865, by rfl⟩ : syracuseStep 1177949 = 441731) (by norm_num)
theorem B883057 : Blo 782338 883057 := bbase (se 2 (by rfl) ⟨331146, by rfl⟩ : syracuseStep 883057 = 662293) (by norm_num)
theorem B1177973 : Blo 782338 1177973 := bbase (se 5 (by rfl) ⟨55217, by rfl⟩ : syracuseStep 1177973 = 110435) (by norm_num)
theorem B1767797 : Blo 782338 1767797 := bbase (se 5 (by rfl) ⟨82865, by rfl⟩ : syracuseStep 1767797 = 165731) (by norm_num)
theorem B2652533 : Blo 782338 2652533 := bbase (se 5 (by rfl) ⟨124337, by rfl⟩ : syracuseStep 2652533 = 248675) (by norm_num)
theorem B1177997 : Blo 782338 1177997 := bbase (se 3 (by rfl) ⟨220874, by rfl⟩ : syracuseStep 1177997 = 441749) (by norm_num)
theorem B883093 : Blo 782338 883093 := bbase (se 6 (by rfl) ⟨20697, by rfl⟩ : syracuseStep 883093 = 41395) (by norm_num)
theorem B1178021 : Blo 782338 1178021 := bbase (se 4 (by rfl) ⟨110439, by rfl⟩ : syracuseStep 1178021 = 220879) (by norm_num)
theorem B883129 : Blo 782338 883129 := bbase (se 2 (by rfl) ⟨331173, by rfl⟩ : syracuseStep 883129 = 662347) (by norm_num)
theorem B1178045 : Blo 782338 1178045 := bbase (se 3 (by rfl) ⟨220883, by rfl⟩ : syracuseStep 1178045 = 441767) (by norm_num)
theorem B1767869 : Blo 782338 1767869 := bbase (se 3 (by rfl) ⟨331475, by rfl⟩ : syracuseStep 1767869 = 662951) (by norm_num)
theorem B1178069 : Blo 782338 1178069 := bbase (se 7 (by rfl) ⟨13805, by rfl⟩ : syracuseStep 1178069 = 27611) (by norm_num)
theorem B883165 : Blo 782338 883165 := bbase (se 3 (by rfl) ⟨165593, by rfl⟩ : syracuseStep 883165 = 331187) (by norm_num)
theorem B1178093 : Blo 782338 1178093 := bbase (se 3 (by rfl) ⟨220892, by rfl⟩ : syracuseStep 1178093 = 441785) (by norm_num)
theorem B883201 : Blo 782338 883201 := bbase (se 2 (by rfl) ⟨331200, by rfl⟩ : syracuseStep 883201 = 662401) (by norm_num)
theorem B1178117 : Blo 782338 1178117 := bbase (se 4 (by rfl) ⟨110448, by rfl⟩ : syracuseStep 1178117 = 220897) (by norm_num)
theorem B1767941 : Blo 782338 1767941 := bbase (se 4 (by rfl) ⟨165744, by rfl⟩ : syracuseStep 1767941 = 331489) (by norm_num)
theorem B1178141 : Blo 782338 1178141 := bbase (se 3 (by rfl) ⟨220901, by rfl⟩ : syracuseStep 1178141 = 441803) (by norm_num)
theorem B883237 : Blo 782338 883237 := bbase (se 4 (by rfl) ⟨82803, by rfl⟩ : syracuseStep 883237 = 165607) (by norm_num)
theorem B1178165 : Blo 782338 1178165 := bbase (se 5 (by rfl) ⟨55226, by rfl⟩ : syracuseStep 1178165 = 110453) (by norm_num)
theorem B883273 : Blo 782338 883273 := bbase (se 2 (by rfl) ⟨331227, by rfl⟩ : syracuseStep 883273 = 662455) (by norm_num)
theorem B1178189 : Blo 782338 1178189 := bbase (se 3 (by rfl) ⟨220910, by rfl⟩ : syracuseStep 1178189 = 441821) (by norm_num)
theorem B1768013 : Blo 782338 1768013 := bbase (se 3 (by rfl) ⟨331502, by rfl⟩ : syracuseStep 1768013 = 663005) (by norm_num)
theorem B1178213 : Blo 782338 1178213 := bbase (se 4 (by rfl) ⟨110457, by rfl⟩ : syracuseStep 1178213 = 220915) (by norm_num)
theorem B883309 : Blo 782338 883309 := bbase (se 3 (by rfl) ⟨165620, by rfl⟩ : syracuseStep 883309 = 331241) (by norm_num)
theorem B1178237 : Blo 782338 1178237 := bbase (se 3 (by rfl) ⟨220919, by rfl⟩ : syracuseStep 1178237 = 441839) (by norm_num)
theorem B883345 : Blo 782338 883345 := bbase (se 2 (by rfl) ⟨331254, by rfl⟩ : syracuseStep 883345 = 662509) (by norm_num)
theorem B1178261 : Blo 782338 1178261 := bbase (se 6 (by rfl) ⟨27615, by rfl⟩ : syracuseStep 1178261 = 55231) (by norm_num)
theorem B1768085 : Blo 782338 1768085 := bbase (se 6 (by rfl) ⟨41439, by rfl⟩ : syracuseStep 1768085 = 82879) (by norm_num)
theorem B1178285 : Blo 782338 1178285 := bbase (se 3 (by rfl) ⟨220928, by rfl⟩ : syracuseStep 1178285 = 441857) (by norm_num)
theorem B883381 : Blo 782338 883381 := bbase (se 5 (by rfl) ⟨41408, by rfl⟩ : syracuseStep 883381 = 82817) (by norm_num)
theorem B1178309 : Blo 782338 1178309 := bbase (se 4 (by rfl) ⟨110466, by rfl⟩ : syracuseStep 1178309 = 220933) (by norm_num)
theorem B883417 : Blo 782338 883417 := bbase (se 2 (by rfl) ⟨331281, by rfl⟩ : syracuseStep 883417 = 662563) (by norm_num)
theorem B1178333 : Blo 782338 1178333 := bbase (se 3 (by rfl) ⟨220937, by rfl⟩ : syracuseStep 1178333 = 441875) (by norm_num)
theorem B1768157 : Blo 782338 1768157 := bbase (se 3 (by rfl) ⟨331529, by rfl⟩ : syracuseStep 1768157 = 663059) (by norm_num)
theorem B1178357 : Blo 782338 1178357 := bbase (se 5 (by rfl) ⟨55235, by rfl⟩ : syracuseStep 1178357 = 110471) (by norm_num)
theorem B883453 : Blo 782338 883453 := bbase (se 3 (by rfl) ⟨165647, by rfl⟩ : syracuseStep 883453 = 331295) (by norm_num)
theorem B3963653 : Blo 782338 3963653 := bbase (se 4 (by rfl) ⟨371592, by rfl⟩ : syracuseStep 3963653 = 743185) (by norm_num)
theorem B1178381 : Blo 782338 1178381 := bbase (se 3 (by rfl) ⟨220946, by rfl⟩ : syracuseStep 1178381 = 441893) (by norm_num)
theorem B883489 : Blo 782338 883489 := bbase (se 2 (by rfl) ⟨331308, by rfl⟩ : syracuseStep 883489 = 662617) (by norm_num)
theorem B1178405 : Blo 782338 1178405 := bbase (se 4 (by rfl) ⟨110475, by rfl⟩ : syracuseStep 1178405 = 220951) (by norm_num)
theorem B1768229 : Blo 782338 1768229 := bbase (se 4 (by rfl) ⟨165771, by rfl⟩ : syracuseStep 1768229 = 331543) (by norm_num)
theorem B2652965 : Blo 782338 2652965 := bbase (se 4 (by rfl) ⟨248715, by rfl⟩ : syracuseStep 2652965 = 497431) (by norm_num)
theorem B1178429 : Blo 782338 1178429 := bbase (se 3 (by rfl) ⟨220955, by rfl⟩ : syracuseStep 1178429 = 441911) (by norm_num)
theorem B883525 : Blo 782338 883525 := bbase (se 4 (by rfl) ⟨82830, by rfl⟩ : syracuseStep 883525 = 165661) (by norm_num)
theorem B1178453 : Blo 782338 1178453 := bbase (se 9 (by rfl) ⟨3452, by rfl⟩ : syracuseStep 1178453 = 6905) (by norm_num)
theorem B883561 : Blo 782338 883561 := bbase (se 2 (by rfl) ⟨331335, by rfl⟩ : syracuseStep 883561 = 662671) (by norm_num)
theorem B1178477 : Blo 782338 1178477 := bbase (se 3 (by rfl) ⟨220964, by rfl⟩ : syracuseStep 1178477 = 441929) (by norm_num)
theorem B1768301 : Blo 782338 1768301 := bbase (se 3 (by rfl) ⟨331556, by rfl⟩ : syracuseStep 1768301 = 663113) (by norm_num)
theorem B1342325 : Blo 782338 1342325 := bbase (se 5 (by rfl) ⟨62921, by rfl⟩ : syracuseStep 1342325 = 125843) (by norm_num)
theorem B1178501 : Blo 782338 1178501 := bbase (se 4 (by rfl) ⟨110484, by rfl⟩ : syracuseStep 1178501 = 220969) (by norm_num)
theorem B883597 : Blo 782338 883597 := bbase (se 3 (by rfl) ⟨165674, by rfl⟩ : syracuseStep 883597 = 331349) (by norm_num)
theorem B2063261 : Blo 782338 2063261 := bbase (se 3 (by rfl) ⟨386861, by rfl⟩ : syracuseStep 2063261 = 773723) (by norm_num)
theorem B1178525 : Blo 782338 1178525 := bbase (se 3 (by rfl) ⟨220973, by rfl⟩ : syracuseStep 1178525 = 441947) (by norm_num)
theorem B883633 : Blo 782338 883633 := bbase (se 2 (by rfl) ⟨331362, by rfl⟩ : syracuseStep 883633 = 662725) (by norm_num)
theorem B1178549 : Blo 782338 1178549 := bbase (se 5 (by rfl) ⟨55244, by rfl⟩ : syracuseStep 1178549 = 110489) (by norm_num)
theorem B1768373 : Blo 782338 1768373 := bbase (se 5 (by rfl) ⟨82892, by rfl⟩ : syracuseStep 1768373 = 165785) (by norm_num)
theorem B1178573 : Blo 782338 1178573 := bbase (se 3 (by rfl) ⟨220982, by rfl⟩ : syracuseStep 1178573 = 441965) (by norm_num)
theorem B883669 : Blo 782338 883669 := bbase (se 7 (by rfl) ⟨10355, by rfl⟩ : syracuseStep 883669 = 20711) (by norm_num)
theorem B1178597 : Blo 782338 1178597 := bbase (se 4 (by rfl) ⟨110493, by rfl⟩ : syracuseStep 1178597 = 220987) (by norm_num)
theorem B883705 : Blo 782338 883705 := bbase (se 2 (by rfl) ⟨331389, by rfl⟩ : syracuseStep 883705 = 662779) (by norm_num)
theorem B1178621 : Blo 782338 1178621 := bbase (se 3 (by rfl) ⟨220991, by rfl⟩ : syracuseStep 1178621 = 441983) (by norm_num)
theorem B1768445 : Blo 782338 1768445 := bbase (se 3 (by rfl) ⟨331583, by rfl⟩ : syracuseStep 1768445 = 663167) (by norm_num)
theorem B1178645 : Blo 782338 1178645 := bbase (se 6 (by rfl) ⟨27624, by rfl⟩ : syracuseStep 1178645 = 55249) (by norm_num)
theorem B883741 : Blo 782338 883741 := bbase (se 3 (by rfl) ⟨165701, by rfl⟩ : syracuseStep 883741 = 331403) (by norm_num)
theorem B3013669 : Blo 782338 3013669 := bbase (se 4 (by rfl) ⟨282531, by rfl⟩ : syracuseStep 3013669 = 565063) (by norm_num)
theorem B1178669 : Blo 782338 1178669 := bbase (se 3 (by rfl) ⟨221000, by rfl⟩ : syracuseStep 1178669 = 442001) (by norm_num)
theorem B883777 : Blo 782338 883777 := bbase (se 2 (by rfl) ⟨331416, by rfl⟩ : syracuseStep 883777 = 662833) (by norm_num)
theorem B1178693 : Blo 782338 1178693 := bbase (se 4 (by rfl) ⟨110502, by rfl⟩ : syracuseStep 1178693 = 221005) (by norm_num)
theorem B1768517 : Blo 782338 1768517 := bbase (se 4 (by rfl) ⟨165798, by rfl⟩ : syracuseStep 1768517 = 331597) (by norm_num)
theorem B1178717 : Blo 782338 1178717 := bbase (se 3 (by rfl) ⟨221009, by rfl⟩ : syracuseStep 1178717 = 442019) (by norm_num)
theorem B883813 : Blo 782338 883813 := bbase (se 4 (by rfl) ⟨82857, by rfl⟩ : syracuseStep 883813 = 165715) (by norm_num)
theorem B1178741 : Blo 782338 1178741 := bbase (se 5 (by rfl) ⟨55253, by rfl⟩ : syracuseStep 1178741 = 110507) (by norm_num)
theorem B883849 : Blo 782338 883849 := bbase (se 2 (by rfl) ⟨331443, by rfl⟩ : syracuseStep 883849 = 662887) (by norm_num)
theorem B1178765 : Blo 782338 1178765 := bbase (se 3 (by rfl) ⟨221018, by rfl⟩ : syracuseStep 1178765 = 442037) (by norm_num)
theorem B1768589 : Blo 782338 1768589 := bbase (se 3 (by rfl) ⟨331610, by rfl⟩ : syracuseStep 1768589 = 663221) (by norm_num)
theorem B1178789 : Blo 782338 1178789 := bbase (se 4 (by rfl) ⟨110511, by rfl⟩ : syracuseStep 1178789 = 221023) (by norm_num)
theorem B883885 : Blo 782338 883885 := bbase (se 3 (by rfl) ⟨165728, by rfl⟩ : syracuseStep 883885 = 331457) (by norm_num)
theorem B1178813 : Blo 782338 1178813 := bbase (se 3 (by rfl) ⟨221027, by rfl⟩ : syracuseStep 1178813 = 442055) (by norm_num)
theorem B883921 : Blo 782338 883921 := bbase (se 2 (by rfl) ⟨331470, by rfl⟩ : syracuseStep 883921 = 662941) (by norm_num)
theorem B1178837 : Blo 782338 1178837 := bbase (se 7 (by rfl) ⟨13814, by rfl⟩ : syracuseStep 1178837 = 27629) (by norm_num)
theorem B1768661 : Blo 782338 1768661 := bbase (se 7 (by rfl) ⟨20726, by rfl⟩ : syracuseStep 1768661 = 41453) (by norm_num)
theorem B2653397 : Blo 782338 2653397 := bbase (se 7 (by rfl) ⟨31094, by rfl⟩ : syracuseStep 2653397 = 62189) (by norm_num)
theorem B1178861 : Blo 782338 1178861 := bbase (se 3 (by rfl) ⟨221036, by rfl⟩ : syracuseStep 1178861 = 442073) (by norm_num)
theorem B883957 : Blo 782338 883957 := bbase (se 5 (by rfl) ⟨41435, by rfl⟩ : syracuseStep 883957 = 82871) (by norm_num)
theorem B1178885 : Blo 782338 1178885 := bbase (se 4 (by rfl) ⟨110520, by rfl⟩ : syracuseStep 1178885 = 221041) (by norm_num)
theorem B883993 : Blo 782338 883993 := bbase (se 2 (by rfl) ⟨331497, by rfl⟩ : syracuseStep 883993 = 662995) (by norm_num)
theorem B1178909 : Blo 782338 1178909 := bbase (se 3 (by rfl) ⟨221045, by rfl⟩ : syracuseStep 1178909 = 442091) (by norm_num)
theorem B1768733 : Blo 782338 1768733 := bbase (se 3 (by rfl) ⟨331637, by rfl⟩ : syracuseStep 1768733 = 663275) (by norm_num)
theorem B1178933 : Blo 782338 1178933 := bbase (se 5 (by rfl) ⟨55262, by rfl⟩ : syracuseStep 1178933 = 110525) (by norm_num)
theorem B884029 : Blo 782338 884029 := bbase (se 3 (by rfl) ⟨165755, by rfl⟩ : syracuseStep 884029 = 331511) (by norm_num)
theorem B1178957 : Blo 782338 1178957 := bbase (se 3 (by rfl) ⟨221054, by rfl⟩ : syracuseStep 1178957 = 442109) (by norm_num)
theorem B884065 : Blo 782338 884065 := bbase (se 2 (by rfl) ⟨331524, by rfl⟩ : syracuseStep 884065 = 663049) (by norm_num)
theorem B1178981 : Blo 782338 1178981 := bbase (se 4 (by rfl) ⟨110529, by rfl⟩ : syracuseStep 1178981 = 221059) (by norm_num)
theorem B1768805 : Blo 782338 1768805 := bbase (se 4 (by rfl) ⟨165825, by rfl⟩ : syracuseStep 1768805 = 331651) (by norm_num)
theorem B1179005 : Blo 782338 1179005 := bbase (se 3 (by rfl) ⟨221063, by rfl⟩ : syracuseStep 1179005 = 442127) (by norm_num)
theorem B884101 : Blo 782338 884101 := bbase (se 4 (by rfl) ⟨82884, by rfl⟩ : syracuseStep 884101 = 165769) (by norm_num)
theorem B1179029 : Blo 782338 1179029 := bbase (se 6 (by rfl) ⟨27633, by rfl⟩ : syracuseStep 1179029 = 55267) (by norm_num)
theorem B884137 : Blo 782338 884137 := bbase (se 2 (by rfl) ⟨331551, by rfl⟩ : syracuseStep 884137 = 663103) (by norm_num)
theorem B1179053 : Blo 782338 1179053 := bbase (se 3 (by rfl) ⟨221072, by rfl⟩ : syracuseStep 1179053 = 442145) (by norm_num)
theorem B1768877 : Blo 782338 1768877 := bbase (se 3 (by rfl) ⟨331664, by rfl⟩ : syracuseStep 1768877 = 663329) (by norm_num)
theorem B1179077 : Blo 782338 1179077 := bbase (se 4 (by rfl) ⟨110538, by rfl⟩ : syracuseStep 1179077 = 221077) (by norm_num)
theorem B884173 : Blo 782338 884173 := bbase (se 3 (by rfl) ⟨165782, by rfl⟩ : syracuseStep 884173 = 331565) (by norm_num)
theorem B1179101 : Blo 782338 1179101 := bbase (se 3 (by rfl) ⟨221081, by rfl⟩ : syracuseStep 1179101 = 442163) (by norm_num)
theorem B884209 : Blo 782338 884209 := bbase (se 2 (by rfl) ⟨331578, by rfl⟩ : syracuseStep 884209 = 663157) (by norm_num)
theorem B1179125 : Blo 782338 1179125 := bbase (se 5 (by rfl) ⟨55271, by rfl⟩ : syracuseStep 1179125 = 110543) (by norm_num)
theorem B1768949 : Blo 782338 1768949 := bbase (se 5 (by rfl) ⟨82919, by rfl⟩ : syracuseStep 1768949 = 165839) (by norm_num)
theorem B1179149 : Blo 782338 1179149 := bbase (se 3 (by rfl) ⟨221090, by rfl⟩ : syracuseStep 1179149 = 442181) (by norm_num)
theorem B884245 : Blo 782338 884245 := bbase (se 6 (by rfl) ⟨20724, by rfl⟩ : syracuseStep 884245 = 41449) (by norm_num)
theorem B1179173 : Blo 782338 1179173 := bbase (se 4 (by rfl) ⟨110547, by rfl⟩ : syracuseStep 1179173 = 221095) (by norm_num)
theorem B884281 : Blo 782338 884281 := bbase (se 2 (by rfl) ⟨331605, by rfl⟩ : syracuseStep 884281 = 663211) (by norm_num)
theorem B1179197 : Blo 782338 1179197 := bbase (se 3 (by rfl) ⟨221099, by rfl⟩ : syracuseStep 1179197 = 442199) (by norm_num)
theorem B1769021 : Blo 782338 1769021 := bbase (se 3 (by rfl) ⟨331691, by rfl⟩ : syracuseStep 1769021 = 663383) (by norm_num)
theorem B1179221 : Blo 782338 1179221 := bbase (se 8 (by rfl) ⟨6909, by rfl⟩ : syracuseStep 1179221 = 13819) (by norm_num)
theorem B884317 : Blo 782338 884317 := bbase (se 3 (by rfl) ⟨165809, by rfl⟩ : syracuseStep 884317 = 331619) (by norm_num)
theorem B1179245 : Blo 782338 1179245 := bbase (se 3 (by rfl) ⟨221108, by rfl⟩ : syracuseStep 1179245 = 442217) (by norm_num)
theorem B884353 : Blo 782338 884353 := bbase (se 2 (by rfl) ⟨331632, by rfl⟩ : syracuseStep 884353 = 663265) (by norm_num)
theorem B1179269 : Blo 782338 1179269 := bbase (se 4 (by rfl) ⟨110556, by rfl⟩ : syracuseStep 1179269 = 221113) (by norm_num)
theorem B1769093 : Blo 782338 1769093 := bbase (se 4 (by rfl) ⟨165852, by rfl⟩ : syracuseStep 1769093 = 331705) (by norm_num)
theorem B2653829 : Blo 782338 2653829 := bbase (se 4 (by rfl) ⟨248796, by rfl⟩ : syracuseStep 2653829 = 497593) (by norm_num)
theorem B1179293 : Blo 782338 1179293 := bbase (se 3 (by rfl) ⟨221117, by rfl⟩ : syracuseStep 1179293 = 442235) (by norm_num)
theorem B884389 : Blo 782338 884389 := bbase (se 4 (by rfl) ⟨82911, by rfl⟩ : syracuseStep 884389 = 165823) (by norm_num)
theorem B1179317 : Blo 782338 1179317 := bbase (se 5 (by rfl) ⟨55280, by rfl⟩ : syracuseStep 1179317 = 110561) (by norm_num)
theorem B884425 : Blo 782338 884425 := bbase (se 2 (by rfl) ⟨331659, by rfl⟩ : syracuseStep 884425 = 663319) (by norm_num)
theorem B1179341 : Blo 782338 1179341 := bbase (se 3 (by rfl) ⟨221126, by rfl⟩ : syracuseStep 1179341 = 442253) (by norm_num)
theorem B1769165 : Blo 782338 1769165 := bbase (se 3 (by rfl) ⟨331718, by rfl⟩ : syracuseStep 1769165 = 663437) (by norm_num)
theorem B1179365 : Blo 782338 1179365 := bbase (se 4 (by rfl) ⟨110565, by rfl⟩ : syracuseStep 1179365 = 221131) (by norm_num)
theorem B884461 : Blo 782338 884461 := bbase (se 3 (by rfl) ⟨165836, by rfl⟩ : syracuseStep 884461 = 331673) (by norm_num)
theorem B1179389 : Blo 782338 1179389 := bbase (se 3 (by rfl) ⟨221135, by rfl⟩ : syracuseStep 1179389 = 442271) (by norm_num)
theorem B884497 : Blo 782338 884497 := bbase (se 2 (by rfl) ⟨331686, by rfl⟩ : syracuseStep 884497 = 663373) (by norm_num)
theorem B1179413 : Blo 782338 1179413 := bbase (se 6 (by rfl) ⟨27642, by rfl⟩ : syracuseStep 1179413 = 55285) (by norm_num)
theorem B1769237 : Blo 782338 1769237 := bbase (se 6 (by rfl) ⟨41466, by rfl⟩ : syracuseStep 1769237 = 82933) (by norm_num)
theorem B1179437 : Blo 782338 1179437 := bbase (se 3 (by rfl) ⟨221144, by rfl⟩ : syracuseStep 1179437 = 442289) (by norm_num)
theorem B7143221 : Blo 782338 7143221 := bbase (se 5 (by rfl) ⟨334838, by rfl⟩ : syracuseStep 7143221 = 669677) (by norm_num)
theorem B884533 : Blo 782338 884533 := bbase (se 5 (by rfl) ⟨41462, by rfl⟩ : syracuseStep 884533 = 82925) (by norm_num)
theorem B1179461 : Blo 782338 1179461 := bbase (se 4 (by rfl) ⟨110574, by rfl⟩ : syracuseStep 1179461 = 221149) (by norm_num)
theorem B2981717 : Blo 782338 2981717 := bbase (se 9 (by rfl) ⟨8735, by rfl⟩ : syracuseStep 2981717 = 17471) (by norm_num)
theorem B884569 : Blo 782338 884569 := bbase (se 2 (by rfl) ⟨331713, by rfl⟩ : syracuseStep 884569 = 663427) (by norm_num)
theorem B1671005 : Blo 782338 1671005 := bbase (se 3 (by rfl) ⟨313313, by rfl⟩ : syracuseStep 1671005 = 626627) (by norm_num)
theorem B1179485 : Blo 782338 1179485 := bbase (se 3 (by rfl) ⟨221153, by rfl⟩ : syracuseStep 1179485 = 442307) (by norm_num)
theorem B3342181 : Blo 782338 3342181 := bbase (se 4 (by rfl) ⟨313329, by rfl⟩ : syracuseStep 3342181 = 626659) (by norm_num)
theorem B884605 : Blo 782338 884605 := bbase (se 3 (by rfl) ⟨165863, by rfl⟩ : syracuseStep 884605 = 331727) (by norm_num)
theorem B6684565 : Blo 782338 6684565 := bbase (se 6 (by rfl) ⟨156669, by rfl⟩ : syracuseStep 6684565 = 313339) (by norm_num)
theorem B2228269 : Blo 782338 2228269 := bstep (se 3 (by rfl) ⟨417800, by rfl⟩ : syracuseStep 2228269 = 835601) B835601
theorem B1671313 : Blo 782338 1671313 := bstep (se 2 (by rfl) ⟨626742, by rfl⟩ : syracuseStep 1671313 = 1253485) B1253485
theorem B1114499 : Blo 782338 1114499 := bstep (se 1 (by rfl) ⟨835874, by rfl⟩ : syracuseStep 1114499 = 1671749) B1671749
theorem B3015395 : Blo 782338 3015395 := bstep (se 1 (by rfl) ⟨2261546, by rfl⟩ : syracuseStep 3015395 = 4523093) B4523093
theorem B8487665 : Blo 782338 8487665 := bstep (se 2 (by rfl) ⟨3182874, by rfl⟩ : syracuseStep 8487665 = 6365749) B6365749
theorem B3343139 : Blo 782338 3343139 := bstep (se 1 (by rfl) ⟨2507354, by rfl⟩ : syracuseStep 3343139 = 5014709) B5014709
theorem B1115137 : Blo 782338 1115137 := bstep (se 2 (by rfl) ⟨418176, by rfl⟩ : syracuseStep 1115137 = 836353) B836353
theorem B1410257 : Blo 782338 1410257 := bstep (se 2 (by rfl) ⟨528846, by rfl⟩ : syracuseStep 1410257 = 1057693) B1057693
theorem B4457699 : Blo 782338 4457699 := bstep (se 1 (by rfl) ⟨3343274, by rfl⟩ : syracuseStep 4457699 = 6686549) B6686549
theorem B1115473 : Blo 782338 1115473 := bstep (se 2 (by rfl) ⟨418302, by rfl⟩ : syracuseStep 1115473 = 836605) B836605
theorem B13763953 : Blo 782338 13763953 := bstep (se 2 (by rfl) ⟨5161482, by rfl⟩ : syracuseStep 13763953 = 10322965) B10322965
theorem B1410545 : Blo 782338 1410545 := bstep (se 2 (by rfl) ⟨528954, by rfl⟩ : syracuseStep 1410545 = 1057909) B1057909
theorem B5375587 : Blo 782338 5375587 := bstep (se 1 (by rfl) ⟨4031690, by rfl⟩ : syracuseStep 5375587 = 8063381) B8063381
theorem B5441165 : Blo 782338 5441165 := bstep (se 3 (by rfl) ⟨1020218, by rfl⟩ : syracuseStep 5441165 = 2040437) B2040437
theorem B2230001 : Blo 782338 2230001 := bstep (se 2 (by rfl) ⟨836250, by rfl⟩ : syracuseStep 2230001 = 1672501) B1672501
theorem B1116065 : Blo 782338 1116065 := bstep (se 2 (by rfl) ⟨418524, by rfl⟩ : syracuseStep 1116065 = 837049) B837049
theorem B2230193 : Blo 782338 2230193 := bstep (se 2 (by rfl) ⟨836322, by rfl⟩ : syracuseStep 2230193 = 1672645) B1672645
theorem B2983949 : Blo 782338 2983949 := bstep (se 3 (by rfl) ⟨559490, by rfl⟩ : syracuseStep 2983949 = 1118981) B1118981
theorem B3770509 : Blo 782338 3770509 := bstep (se 3 (by rfl) ⟨706970, by rfl⟩ : syracuseStep 3770509 = 1413941) B1413941
theorem B3967217 : Blo 782338 3967217 := bstep (se 2 (by rfl) ⟨1487706, by rfl⟩ : syracuseStep 3967217 = 2975413) B2975413
theorem B1116595 : Blo 782338 1116595 := bstep (se 1 (by rfl) ⟨837446, by rfl⟩ : syracuseStep 1116595 = 1674893) B1674893
theorem B61049285 : Blo 782338 61049285 := bstep (se 4 (by rfl) ⟨5723370, by rfl⟩ : syracuseStep 61049285 = 11446741) B11446741
theorem B6785477 : Blo 782338 6785477 := bstep (se 4 (by rfl) ⟨636138, by rfl⟩ : syracuseStep 6785477 = 1272277) B1272277
theorem B952979 : Blo 782338 952979 := bstep (se 1 (by rfl) ⟨714734, by rfl⟩ : syracuseStep 952979 = 1429469) B1429469
theorem B1411843 : Blo 782338 1411843 := bstep (se 1 (by rfl) ⟨1058882, by rfl⟩ : syracuseStep 1411843 = 2117765) B2117765
theorem B1116931 : Blo 782338 1116931 := bstep (se 1 (by rfl) ⟨837698, by rfl⟩ : syracuseStep 1116931 = 1675397) B1675397
theorem B5376901 : Blo 782338 5376901 := bstep (se 4 (by rfl) ⟨504084, by rfl⟩ : syracuseStep 5376901 = 1008169) B1008169
theorem B2231185 : Blo 782338 2231185 := bstep (se 2 (by rfl) ⟨836694, by rfl⟩ : syracuseStep 2231185 = 1673389) B1673389
theorem B1674371 : Blo 782338 1674371 := bstep (se 1 (by rfl) ⟨1255778, by rfl⟩ : syracuseStep 1674371 = 2511557) B2511557
theorem B2231459 : Blo 782338 2231459 := bstep (se 1 (by rfl) ⟨1673594, by rfl⟩ : syracuseStep 2231459 = 3347189) B3347189
theorem B3017969 : Blo 782338 3017969 := bstep (se 2 (by rfl) ⟨1131738, by rfl⟩ : syracuseStep 3017969 = 2263477) B2263477
theorem B1117489 : Blo 782338 1117489 := bstep (se 2 (by rfl) ⟨419058, by rfl⟩ : syracuseStep 1117489 = 838117) B838117
theorem B1117523 : Blo 782338 1117523 := bstep (se 1 (by rfl) ⟨838142, by rfl⟩ : syracuseStep 1117523 = 1676285) B1676285
theorem B2231651 : Blo 782338 2231651 := bstep (se 1 (by rfl) ⟨1673738, by rfl⟩ : syracuseStep 2231651 = 3347477) B3347477
theorem B2821553 : Blo 782338 2821553 := bstep (se 2 (by rfl) ⟨1058082, by rfl⟩ : syracuseStep 2821553 = 2116165) B2116165
theorem B3968675 : Blo 782338 3968675 := bstep (se 1 (by rfl) ⟨2976506, by rfl⟩ : syracuseStep 3968675 = 5953013) B5953013
theorem B7147277 : Blo 782338 7147277 := bstep (se 3 (by rfl) ⟨1340114, by rfl⟩ : syracuseStep 7147277 = 2680229) B2680229
theorem B4034317 : Blo 782338 4034317 := bstep (se 3 (by rfl) ⟨756434, by rfl⟩ : syracuseStep 4034317 = 1512869) B1512869
theorem B1118081 : Blo 782338 1118081 := bstep (se 2 (by rfl) ⟨419280, by rfl⟩ : syracuseStep 1118081 = 838561) B838561
theorem B1118161 : Blo 782338 1118161 := bstep (se 2 (by rfl) ⟨419310, by rfl⟩ : syracuseStep 1118161 = 838621) B838621
theorem B6033379 : Blo 782338 6033379 := bstep (se 1 (by rfl) ⟨4525034, by rfl⟩ : syracuseStep 6033379 = 9050069) B9050069
theorem B1675235 : Blo 782338 1675235 := bstep (se 1 (by rfl) ⟨1256426, by rfl⟩ : syracuseStep 1675235 = 2512853) B2512853
theorem B1609763 : Blo 782338 1609763 := bstep (se 1 (by rfl) ⟨1207322, by rfl⟩ : syracuseStep 1609763 = 2414645) B2414645
theorem B1675345 : Blo 782338 1675345 := bstep (se 2 (by rfl) ⟨628254, by rfl⟩ : syracuseStep 1675345 = 1256509) B1256509
theorem B2232461 : Blo 782338 2232461 := bstep (se 3 (by rfl) ⟨418586, by rfl⟩ : syracuseStep 2232461 = 837173) B837173
theorem B2232643 : Blo 782338 2232643 := bstep (se 1 (by rfl) ⟨1674482, by rfl⟩ : syracuseStep 2232643 = 3348965) B3348965
theorem B4460933 : Blo 782338 4460933 := bstep (se 4 (by rfl) ⟨418212, by rfl⟩ : syracuseStep 4460933 = 836425) B836425
theorem B3346829 : Blo 782338 3346829 := bstep (se 3 (by rfl) ⟨627530, by rfl⟩ : syracuseStep 3346829 = 1255061) B1255061
theorem B3969485 : Blo 782338 3969485 := bstep (se 3 (by rfl) ⟨744278, by rfl⟩ : syracuseStep 3969485 = 1488557) B1488557
theorem B1118947 : Blo 782338 1118947 := bstep (se 1 (by rfl) ⟨839210, by rfl⟩ : syracuseStep 1118947 = 1678421) B1678421
theorem B3576611 : Blo 782338 3576611 := bstep (se 1 (by rfl) ⟨2682458, by rfl⟩ : syracuseStep 3576611 = 5364917) B5364917
theorem B2233133 : Blo 782338 2233133 := bstep (se 3 (by rfl) ⟨418712, by rfl⟩ : syracuseStep 2233133 = 837425) B837425
theorem B4461389 : Blo 782338 4461389 := bstep (se 3 (by rfl) ⟨836510, by rfl⟩ : syracuseStep 4461389 = 1673021) B1673021
theorem B2266061 : Blo 782338 2266061 := bstep (se 3 (by rfl) ⟨424886, by rfl⟩ : syracuseStep 2266061 = 849773) B849773
theorem B1020979 : Blo 782338 1020979 := bstep (se 1 (by rfl) ⟨765734, by rfl⟩ : syracuseStep 1020979 = 1531469) B1531469
theorem B1119425 : Blo 782338 1119425 := bstep (se 2 (by rfl) ⟨419784, by rfl⟩ : syracuseStep 1119425 = 839569) B839569
theorem B1119539 : Blo 782338 1119539 := bstep (se 1 (by rfl) ⟨839654, by rfl⟩ : syracuseStep 1119539 = 1679309) B1679309
theorem B6690275 : Blo 782338 6690275 := bstep (se 1 (by rfl) ⟨5017706, by rfl⟩ : syracuseStep 6690275 = 10035413) B10035413
theorem B4232845 : Blo 782338 4232845 := bstep (se 3 (by rfl) ⟨793658, by rfl⟩ : syracuseStep 4232845 = 1587317) B1587317
theorem B3184433 : Blo 782338 3184433 := bstep (se 2 (by rfl) ⟨1194162, by rfl⟩ : syracuseStep 3184433 = 2388325) B2388325
theorem B2234317 : Blo 782338 2234317 := bstep (se 3 (by rfl) ⟨418934, by rfl⟩ : syracuseStep 2234317 = 837869) B837869
theorem B8034317 : Blo 782338 8034317 := bstep (se 3 (by rfl) ⟨1506434, by rfl⟩ : syracuseStep 8034317 = 3012869) B3012869
theorem B1677361 : Blo 782338 1677361 := bstep (se 2 (by rfl) ⟨629010, by rfl⟩ : syracuseStep 1677361 = 1258021) B1258021
theorem B3774755 : Blo 782338 3774755 := bstep (se 1 (by rfl) ⟨2831066, by rfl⟩ : syracuseStep 3774755 = 5662133) B5662133
theorem B2267459 : Blo 782338 2267459 := bstep (se 1 (by rfl) ⟨1700594, by rfl⟩ : syracuseStep 2267459 = 3401189) B3401189
theorem B1677763 : Blo 782338 1677763 := bstep (se 1 (by rfl) ⟨1258322, by rfl⟩ : syracuseStep 1677763 = 2516645) B2516645
theorem B4135373 : Blo 782338 4135373 := bstep (se 3 (by rfl) ⟨775382, by rfl⟩ : syracuseStep 4135373 = 1550765) B1550765
theorem B3775025 : Blo 782338 3775025 := bstep (se 2 (by rfl) ⟨1415634, by rfl⟩ : syracuseStep 3775025 = 2831269) B2831269
theorem B3775139 : Blo 782338 3775139 := bstep (se 1 (by rfl) ⟨2831354, by rfl⟩ : syracuseStep 3775139 = 5662709) B5662709
theorem B2235377 : Blo 782338 2235377 := bstep (se 2 (by rfl) ⟨838266, by rfl⟩ : syracuseStep 2235377 = 1676533) B1676533
theorem B1416305 : Blo 782338 1416305 := bstep (se 2 (by rfl) ⟨531114, by rfl⟩ : syracuseStep 1416305 = 1062229) B1062229
theorem B5020805 : Blo 782338 5020805 := bstep (se 4 (by rfl) ⟨470700, by rfl⟩ : syracuseStep 5020805 = 941401) B941401
theorem B3972401 : Blo 782338 3972401 := bstep (se 2 (by rfl) ⟨1489650, by rfl⟩ : syracuseStep 3972401 = 2979301) B2979301
theorem B3349937 : Blo 782338 3349937 := bstep (se 2 (by rfl) ⟨1256226, by rfl⟩ : syracuseStep 3349937 = 2512453) B2512453
theorem B990787 : Blo 782338 990787 := bstep (se 1 (by rfl) ⟨743090, by rfl⟩ : syracuseStep 990787 = 1486181) B1486181
theorem B794243 : Blo 782338 794243 := bstep (se 1 (by rfl) ⟨595682, by rfl⟩ : syracuseStep 794243 = 1191365) B1191365
theorem B2236049 : Blo 782338 2236049 := bstep (se 2 (by rfl) ⟨838518, by rfl⟩ : syracuseStep 2236049 = 1677037) B1677037
theorem B990883 : Blo 782338 990883 := bstep (se 1 (by rfl) ⟨743162, by rfl⟩ : syracuseStep 990883 = 1486325) B1486325
theorem B4464305 : Blo 782338 4464305 := bstep (se 2 (by rfl) ⟨1674114, by rfl⟩ : syracuseStep 4464305 = 3348229) B3348229
theorem B1908611 : Blo 782338 1908611 := bstep (se 1 (by rfl) ⟨1431458, by rfl⟩ : syracuseStep 1908611 = 2862917) B2862917
theorem B1679267 : Blo 782338 1679267 := bstep (se 1 (by rfl) ⟨1259450, by rfl⟩ : syracuseStep 1679267 = 2518901) B2518901
theorem B4530161 : Blo 782338 4530161 := bstep (se 2 (by rfl) ⟨1698810, by rfl⟩ : syracuseStep 4530161 = 3397621) B3397621
theorem B3350605 : Blo 782338 3350605 := bstep (se 3 (by rfl) ⟨628238, by rfl⟩ : syracuseStep 3350605 = 1256477) B1256477
theorem B1253459 : Blo 782338 1253459 := bstep (se 1 (by rfl) ⟨940094, by rfl⟩ : syracuseStep 1253459 = 1880189) B1880189
theorem B991379 : Blo 782338 991379 := bstep (se 1 (by rfl) ⟨743534, by rfl⟩ : syracuseStep 991379 = 1487069) B1487069
theorem B32219363 : Blo 782338 32219363 := bstep (se 1 (by rfl) ⟨24164522, by rfl⟩ : syracuseStep 32219363 = 48329045) B48329045
theorem B2236835 : Blo 782338 2236835 := bstep (se 1 (by rfl) ⟨1677626, by rfl⟩ : syracuseStep 2236835 = 3355253) B3355253
theorem B1254017 : Blo 782338 1254017 := bstep (se 2 (by rfl) ⟨470256, by rfl⟩ : syracuseStep 1254017 = 940513) B940513
theorem B3351203 : Blo 782338 3351203 := bstep (se 1 (by rfl) ⟨2513402, by rfl⟩ : syracuseStep 3351203 = 5026805) B5026805
theorem B3973859 : Blo 782338 3973859 := bstep (se 1 (by rfl) ⟨2980394, by rfl⟩ : syracuseStep 3973859 = 5960789) B5960789
theorem B2237165 : Blo 782338 2237165 := bstep (se 3 (by rfl) ⟨419468, by rfl⟩ : syracuseStep 2237165 = 838937) B838937
theorem B2237233 : Blo 782338 2237233 := bstep (se 2 (by rfl) ⟨838962, by rfl⟩ : syracuseStep 2237233 = 1677925) B1677925
theorem B992083 : Blo 782338 992083 := bstep (se 1 (by rfl) ⟨744062, by rfl⟩ : syracuseStep 992083 = 1488125) B1488125
theorem B1254241 : Blo 782338 1254241 := bstep (se 2 (by rfl) ⟨470340, by rfl⟩ : syracuseStep 1254241 = 940681) B940681
theorem B1254305 : Blo 782338 1254305 := bstep (se 2 (by rfl) ⟨470364, by rfl⟩ : syracuseStep 1254305 = 940729) B940729
theorem B992179 : Blo 782338 992179 := bstep (se 1 (by rfl) ⟨744134, by rfl⟩ : syracuseStep 992179 = 1488269) B1488269
theorem B1254433 : Blo 782338 1254433 := bstep (se 2 (by rfl) ⟨470412, by rfl⟩ : syracuseStep 1254433 = 940825) B940825
theorem B5022755 : Blo 782338 5022755 := bstep (se 1 (by rfl) ⟨3767066, by rfl⟩ : syracuseStep 5022755 = 7534133) B7534133
theorem B2237507 : Blo 782338 2237507 := bstep (se 1 (by rfl) ⟨1678130, by rfl⟩ : syracuseStep 2237507 = 3356261) B3356261
theorem B4465763 : Blo 782338 4465763 := bstep (se 1 (by rfl) ⟨3349322, by rfl⟩ : syracuseStep 4465763 = 6698645) B6698645
theorem B1320259 : Blo 782338 1320259 := bstep (se 1 (by rfl) ⟨990194, by rfl⟩ : syracuseStep 1320259 = 1980389) B1980389
theorem B992675 : Blo 782338 992675 := bstep (se 1 (by rfl) ⟨744506, by rfl⟩ : syracuseStep 992675 = 1489013) B1489013
theorem B1320401 : Blo 782338 1320401 := bstep (se 2 (by rfl) ⟨495150, by rfl⟩ : syracuseStep 1320401 = 990301) B990301
theorem B3974669 : Blo 782338 3974669 := bstep (se 3 (by rfl) ⟨745250, by rfl⟩ : syracuseStep 3974669 = 1490501) B1490501
theorem B4236869 : Blo 782338 4236869 := bstep (se 4 (by rfl) ⟨397206, by rfl⟩ : syracuseStep 4236869 = 794413) B794413
theorem B1320529 : Blo 782338 1320529 := bstep (se 2 (by rfl) ⟨495198, by rfl⟩ : syracuseStep 1320529 = 990397) B990397
theorem B1320563 : Blo 782338 1320563 := bstep (se 1 (by rfl) ⟨990422, by rfl⟩ : syracuseStep 1320563 = 1980845) B1980845
theorem B1320691 : Blo 782338 1320691 := bstep (se 1 (by rfl) ⟨990518, by rfl⟩ : syracuseStep 1320691 = 1981037) B1981037
theorem B1320833 : Blo 782338 1320833 := bstep (se 2 (by rfl) ⟨495312, by rfl⟩ : syracuseStep 1320833 = 990625) B990625
theorem B2238349 : Blo 782338 2238349 := bstep (se 3 (by rfl) ⟨419690, by rfl⟩ : syracuseStep 2238349 = 839381) B839381
theorem B894883 : Blo 782338 894883 := bstep (se 1 (by rfl) ⟨671162, by rfl⟩ : syracuseStep 894883 = 1342325) B1342325
theorem B1320961 : Blo 782338 1320961 := bstep (se 2 (by rfl) ⟨495360, by rfl⟩ : syracuseStep 1320961 = 990721) B990721
theorem B1320995 : Blo 782338 1320995 := bstep (se 1 (by rfl) ⟨990746, by rfl⟩ : syracuseStep 1320995 = 1981493) B1981493
theorem B2238509 : Blo 782338 2238509 := bstep (se 3 (by rfl) ⟨419720, by rfl⟩ : syracuseStep 2238509 = 839441) B839441
theorem B4466765 : Blo 782338 4466765 := bstep (se 3 (by rfl) ⟨837518, by rfl⟩ : syracuseStep 4466765 = 1675037) B1675037
theorem B993379 : Blo 782338 993379 := bstep (se 1 (by rfl) ⟨745034, by rfl⟩ : syracuseStep 993379 = 1490069) B1490069
theorem B1321123 : Blo 782338 1321123 := bstep (se 1 (by rfl) ⟨990842, by rfl⟩ : syracuseStep 1321123 = 1981685) B1981685
theorem B1910947 : Blo 782338 1910947 := bstep (se 1 (by rfl) ⟨1433210, by rfl⟩ : syracuseStep 1910947 = 2866421) B2866421
theorem B993475 : Blo 782338 993475 := bstep (se 1 (by rfl) ⟨745106, by rfl⟩ : syracuseStep 993475 = 1490213) B1490213
theorem B2238691 : Blo 782338 2238691 := bstep (se 1 (by rfl) ⟨1679018, by rfl⟩ : syracuseStep 2238691 = 3358037) B3358037
theorem B1321265 : Blo 782338 1321265 := bstep (se 2 (by rfl) ⟨495474, by rfl⟩ : syracuseStep 1321265 = 990949) B990949
theorem B1321393 : Blo 782338 1321393 := bstep (se 2 (by rfl) ⟨495522, by rfl⟩ : syracuseStep 1321393 = 991045) B991045
theorem B1321427 : Blo 782338 1321427 := bstep (se 1 (by rfl) ⟨991070, by rfl⟩ : syracuseStep 1321427 = 1982141) B1982141
theorem B4762147 : Blo 782338 4762147 := bstep (se 1 (by rfl) ⟨3571610, by rfl⟩ : syracuseStep 4762147 = 7143221) B7143221
theorem B1190465 : Blo 782338 1190465 := bstep (se 2 (by rfl) ⟨446424, by rfl⟩ : syracuseStep 1190465 = 892849) B892849
theorem B1321555 : Blo 782338 1321555 := bstep (se 1 (by rfl) ⟨991166, by rfl⟩ : syracuseStep 1321555 = 1982333) B1982333
theorem B993971 : Blo 782338 993971 := bstep (se 1 (by rfl) ⟨745478, by rfl⟩ : syracuseStep 993971 = 1490957) B1490957
theorem B1321697 : Blo 782338 1321697 := bstep (se 2 (by rfl) ⟨495636, by rfl⟩ : syracuseStep 1321697 = 991273) B991273
theorem B1321825 : Blo 782338 1321825 := bstep (se 2 (by rfl) ⟨495684, by rfl⟩ : syracuseStep 1321825 = 991369) B991369
theorem B1321859 : Blo 782338 1321859 := bstep (se 1 (by rfl) ⟨991394, by rfl⟩ : syracuseStep 1321859 = 1982789) B1982789
theorem B1321987 : Blo 782338 1321987 := bstep (se 1 (by rfl) ⟨991490, by rfl⟩ : syracuseStep 1321987 = 1982981) B1982981
theorem B1256483 : Blo 782338 1256483 := bstep (se 1 (by rfl) ⟨942362, by rfl⟩ : syracuseStep 1256483 = 1884725) B1884725
theorem B1322129 : Blo 782338 1322129 := bstep (se 2 (by rfl) ⟨495798, by rfl⟩ : syracuseStep 1322129 = 991597) B991597
theorem B1486097 : Blo 782338 1486097 := bstep (se 2 (by rfl) ⟨557286, by rfl⟩ : syracuseStep 1486097 = 1114573) B1114573
theorem B1322257 : Blo 782338 1322257 := bstep (se 2 (by rfl) ⟨495846, by rfl⟩ : syracuseStep 1322257 = 991693) B991693
theorem B1322291 : Blo 782338 1322291 := bstep (se 1 (by rfl) ⟨991718, by rfl⟩ : syracuseStep 1322291 = 1983437) B1983437
theorem B5647715 : Blo 782338 5647715 := bstep (se 1 (by rfl) ⟨4235786, by rfl⟩ : syracuseStep 5647715 = 8471573) B8471573
theorem B994675 : Blo 782338 994675 := bstep (se 1 (by rfl) ⟨746006, by rfl⟩ : syracuseStep 994675 = 1492013) B1492013
theorem B1322419 : Blo 782338 1322419 := bstep (se 1 (by rfl) ⟨991814, by rfl⟩ : syracuseStep 1322419 = 1983629) B1983629
theorem B994771 : Blo 782338 994771 := bstep (se 1 (by rfl) ⟨746078, by rfl⟩ : syracuseStep 994771 = 1492157) B1492157
theorem B1322561 : Blo 782338 1322561 := bstep (se 2 (by rfl) ⟨495960, by rfl⟩ : syracuseStep 1322561 = 991921) B991921
theorem B1060499 : Blo 782338 1060499 := bstep (se 1 (by rfl) ⟨795374, by rfl⟩ : syracuseStep 1060499 = 1590749) B1590749
theorem B1322689 : Blo 782338 1322689 := bstep (se 2 (by rfl) ⟨496008, by rfl⟩ : syracuseStep 1322689 = 992017) B992017
theorem B1060547 : Blo 782338 1060547 := bstep (se 1 (by rfl) ⟨795410, by rfl⟩ : syracuseStep 1060547 = 1590821) B1590821
theorem B1322723 : Blo 782338 1322723 := bstep (se 1 (by rfl) ⟨992042, by rfl⟩ : syracuseStep 1322723 = 1984085) B1984085
theorem B1879843 : Blo 782338 1879843 := bstep (se 1 (by rfl) ⟨1409882, by rfl⟩ : syracuseStep 1879843 = 2819765) B2819765
theorem B2830115 : Blo 782338 2830115 := bstep (se 1 (by rfl) ⟨2122586, by rfl⟩ : syracuseStep 2830115 = 4245173) B4245173
theorem B1748803 : Blo 782338 1748803 := bstep (se 1 (by rfl) ⟨1311602, by rfl⟩ : syracuseStep 1748803 = 2623205) B2623205
theorem B1322851 : Blo 782338 1322851 := bstep (se 1 (by rfl) ⟨992138, by rfl⟩ : syracuseStep 1322851 = 1984277) B1984277
theorem B1257329 : Blo 782338 1257329 := bstep (se 2 (by rfl) ⟨471498, by rfl⟩ : syracuseStep 1257329 = 942997) B942997
theorem B1322993 : Blo 782338 1322993 := bstep (se 2 (by rfl) ⟨496122, by rfl⟩ : syracuseStep 1322993 = 992245) B992245
theorem B1323121 : Blo 782338 1323121 := bstep (se 2 (by rfl) ⟨496170, by rfl⟩ : syracuseStep 1323121 = 992341) B992341
theorem B1486993 : Blo 782338 1486993 := bstep (se 2 (by rfl) ⟨557622, by rfl⟩ : syracuseStep 1486993 = 1115245) B1115245
theorem B1323155 : Blo 782338 1323155 := bstep (se 1 (by rfl) ⟨992366, by rfl⟩ : syracuseStep 1323155 = 1984733) B1984733
theorem B5648611 : Blo 782338 5648611 := bstep (se 1 (by rfl) ⟨4236458, by rfl⟩ : syracuseStep 5648611 = 8472917) B8472917
theorem B1323283 : Blo 782338 1323283 := bstep (se 1 (by rfl) ⟨992462, by rfl⟩ : syracuseStep 1323283 = 1984925) B1984925
theorem B1487153 : Blo 782338 1487153 := bstep (se 2 (by rfl) ⟨557682, by rfl⟩ : syracuseStep 1487153 = 1115365) B1115365
theorem B3354979 : Blo 782338 3354979 := bstep (se 1 (by rfl) ⟨2516234, by rfl⟩ : syracuseStep 3354979 = 5032469) B5032469
theorem B3977585 : Blo 782338 3977585 := bstep (se 2 (by rfl) ⟨1491594, by rfl⟩ : syracuseStep 3977585 = 2983189) B2983189
theorem B1323425 : Blo 782338 1323425 := bstep (se 2 (by rfl) ⟨496284, by rfl⟩ : syracuseStep 1323425 = 992569) B992569
theorem B5943779 : Blo 782338 5943779 := bstep (se 1 (by rfl) ⟨4457834, by rfl⟩ : syracuseStep 5943779 = 8915669) B8915669
theorem B1323553 : Blo 782338 1323553 := bstep (se 2 (by rfl) ⟨496332, by rfl⟩ : syracuseStep 1323553 = 992665) B992665
theorem B1323587 : Blo 782338 1323587 := bstep (se 1 (by rfl) ⟨992690, by rfl⟩ : syracuseStep 1323587 = 1985381) B1985381
theorem B1258067 : Blo 782338 1258067 := bstep (se 1 (by rfl) ⟨943550, by rfl⟩ : syracuseStep 1258067 = 1887101) B1887101
theorem B4239985 : Blo 782338 4239985 := bstep (se 2 (by rfl) ⟨1589994, by rfl⟩ : syracuseStep 4239985 = 3179989) B3179989
theorem B5026445 : Blo 782338 5026445 := bstep (se 3 (by rfl) ⟨942458, by rfl⟩ : syracuseStep 5026445 = 1884917) B1884917
theorem B1487555 : Blo 782338 1487555 := bstep (se 1 (by rfl) ⟨1115666, by rfl⟩ : syracuseStep 1487555 = 2231333) B2231333
theorem B1323715 : Blo 782338 1323715 := bstep (se 1 (by rfl) ⟨992786, by rfl⟩ : syracuseStep 1323715 = 1985573) B1985573
theorem B1880803 : Blo 782338 1880803 := bstep (se 1 (by rfl) ⟨1410602, by rfl⟩ : syracuseStep 1880803 = 2821205) B2821205
theorem B1323857 : Blo 782338 1323857 := bstep (se 2 (by rfl) ⟨496446, by rfl⟩ : syracuseStep 1323857 = 992893) B992893
theorem B4469681 : Blo 782338 4469681 := bstep (se 2 (by rfl) ⟨1676130, by rfl⟩ : syracuseStep 4469681 = 3352261) B3352261
theorem B1323985 : Blo 782338 1323985 := bstep (se 2 (by rfl) ⟨496494, by rfl⟩ : syracuseStep 1323985 = 992989) B992989
theorem B1881073 : Blo 782338 1881073 := bstep (se 2 (by rfl) ⟨705402, by rfl⟩ : syracuseStep 1881073 = 1410805) B1410805
theorem B1324019 : Blo 782338 1324019 := bstep (se 1 (by rfl) ⟨993014, by rfl⟩ : syracuseStep 1324019 = 1986029) B1986029
theorem B2012195 : Blo 782338 2012195 := bstep (se 1 (by rfl) ⟨1509146, by rfl⟩ : syracuseStep 2012195 = 3018293) B3018293
theorem B1324147 : Blo 782338 1324147 := bstep (se 1 (by rfl) ⟨993110, by rfl⟩ : syracuseStep 1324147 = 1986221) B1986221
theorem B1324289 : Blo 782338 1324289 := bstep (se 2 (by rfl) ⟨496608, by rfl⟩ : syracuseStep 1324289 = 993217) B993217
theorem B1324417 : Blo 782338 1324417 := bstep (se 2 (by rfl) ⟨496656, by rfl⟩ : syracuseStep 1324417 = 993313) B993313
theorem B2012561 : Blo 782338 2012561 := bstep (se 2 (by rfl) ⟨754710, by rfl⟩ : syracuseStep 2012561 = 1509421) B1509421
theorem B1324451 : Blo 782338 1324451 := bstep (se 1 (by rfl) ⟨993338, by rfl⟩ : syracuseStep 1324451 = 1986677) B1986677
theorem B1324579 : Blo 782338 1324579 := bstep (se 1 (by rfl) ⟨993434, by rfl⟩ : syracuseStep 1324579 = 1986869) B1986869
theorem B1259059 : Blo 782338 1259059 := bstep (se 1 (by rfl) ⟨944294, by rfl⟩ : syracuseStep 1259059 = 1888589) B1888589
theorem B1488451 : Blo 782338 1488451 := bstep (se 1 (by rfl) ⟨1116338, by rfl⟩ : syracuseStep 1488451 = 2232677) B2232677
theorem B1062515 : Blo 782338 1062515 := bstep (se 1 (by rfl) ⟨796886, by rfl⟩ : syracuseStep 1062515 = 1593773) B1593773
theorem B1324721 : Blo 782338 1324721 := bstep (se 2 (by rfl) ⟨496770, by rfl⟩ : syracuseStep 1324721 = 993541) B993541
theorem B1488611 : Blo 782338 1488611 := bstep (se 1 (by rfl) ⟨1116458, by rfl⟩ : syracuseStep 1488611 = 2232917) B2232917
theorem B1259297 : Blo 782338 1259297 := bstep (se 2 (by rfl) ⟨472236, by rfl⟩ : syracuseStep 1259297 = 944473) B944473
theorem B3979043 : Blo 782338 3979043 := bstep (se 1 (by rfl) ⟨2984282, by rfl⟩ : syracuseStep 3979043 = 5968565) B5968565
theorem B1324849 : Blo 782338 1324849 := bstep (se 2 (by rfl) ⟨496818, by rfl⟩ : syracuseStep 1324849 = 993637) B993637
theorem B1324883 : Blo 782338 1324883 := bstep (se 1 (by rfl) ⟨993662, by rfl⟩ : syracuseStep 1324883 = 1987325) B1987325
theorem B1325011 : Blo 782338 1325011 := bstep (se 1 (by rfl) ⟨993758, by rfl⟩ : syracuseStep 1325011 = 1987517) B1987517
theorem B1259507 : Blo 782338 1259507 := bstep (se 1 (by rfl) ⟨944630, by rfl⟩ : syracuseStep 1259507 = 1889261) B1889261
theorem B1325153 : Blo 782338 1325153 := bstep (se 2 (by rfl) ⟨496932, by rfl⟩ : syracuseStep 1325153 = 993865) B993865
theorem B4241585 : Blo 782338 4241585 := bstep (se 2 (by rfl) ⟨1590594, by rfl⟩ : syracuseStep 4241585 = 3181189) B3181189
theorem B1325281 : Blo 782338 1325281 := bstep (se 2 (by rfl) ⟨496980, by rfl⟩ : syracuseStep 1325281 = 993961) B993961
theorem B1325315 : Blo 782338 1325315 := bstep (se 1 (by rfl) ⟨993986, by rfl⟩ : syracuseStep 1325315 = 1987973) B1987973
theorem B3356977 : Blo 782338 3356977 := bstep (se 2 (by rfl) ⟨1258866, by rfl⟩ : syracuseStep 3356977 = 2517733) B2517733
theorem B4962637 : Blo 782338 4962637 := bstep (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) B1860989
theorem B4471139 : Blo 782338 4471139 := bstep (se 1 (by rfl) ⟨3353354, by rfl⟩ : syracuseStep 4471139 = 6706709) B6706709
theorem B1325443 : Blo 782338 1325443 := bstep (se 1 (by rfl) ⟨994082, by rfl⟩ : syracuseStep 1325443 = 1988165) B1988165
theorem B1325585 : Blo 782338 1325585 := bstep (se 2 (by rfl) ⟨497094, by rfl⟩ : syracuseStep 1325585 = 994189) B994189
theorem B3979853 : Blo 782338 3979853 := bstep (se 3 (by rfl) ⟨746222, by rfl⟩ : syracuseStep 3979853 = 1492445) B1492445
theorem B1325713 : Blo 782338 1325713 := bstep (se 2 (by rfl) ⟨497142, by rfl⟩ : syracuseStep 1325713 = 994285) B994285
theorem B1325747 : Blo 782338 1325747 := bstep (se 1 (by rfl) ⟨994310, by rfl⟩ : syracuseStep 1325747 = 1988621) B1988621
theorem B1129153 : Blo 782338 1129153 := bstep (se 2 (by rfl) ⟨423432, by rfl⟩ : syracuseStep 1129153 = 846865) B846865
theorem B1981169 : Blo 782338 1981169 := bstep (se 2 (by rfl) ⟨742938, by rfl⟩ : syracuseStep 1981169 = 1485877) B1485877
theorem B1489681 : Blo 782338 1489681 := bstep (se 2 (by rfl) ⟨558630, by rfl⟩ : syracuseStep 1489681 = 1117261) B1117261
theorem B1981219 : Blo 782338 1981219 := bstep (se 1 (by rfl) ⟨1485914, by rfl⟩ : syracuseStep 1981219 = 2971829) B2971829
theorem B1325875 : Blo 782338 1325875 := bstep (se 1 (by rfl) ⟨994406, by rfl⟩ : syracuseStep 1325875 = 1988813) B1988813
theorem B1981361 : Blo 782338 1981361 := bstep (se 2 (by rfl) ⟨743010, by rfl⟩ : syracuseStep 1981361 = 1486021) B1486021
theorem B1326017 : Blo 782338 1326017 := bstep (se 2 (by rfl) ⟨497256, by rfl⟩ : syracuseStep 1326017 = 994513) B994513
theorem B1326145 : Blo 782338 1326145 := bstep (se 2 (by rfl) ⟨497304, by rfl⟩ : syracuseStep 1326145 = 994609) B994609
theorem B1326179 : Blo 782338 1326179 := bstep (se 1 (by rfl) ⟨994634, by rfl⟩ : syracuseStep 1326179 = 1989269) B1989269
theorem B6438001 : Blo 782338 6438001 := bstep (se 2 (by rfl) ⟨2414250, by rfl⟩ : syracuseStep 6438001 = 4828501) B4828501
theorem B21445859 : Blo 782338 21445859 := bstep (se 1 (by rfl) ⟨16084394, by rfl⟩ : syracuseStep 21445859 = 32168789) B32168789
theorem B1326307 : Blo 782338 1326307 := bstep (se 1 (by rfl) ⟨994730, by rfl⟩ : syracuseStep 1326307 = 1989461) B1989461
theorem B1326449 : Blo 782338 1326449 := bstep (se 2 (by rfl) ⟨497418, by rfl⟩ : syracuseStep 1326449 = 994837) B994837
theorem B1326577 : Blo 782338 1326577 := bstep (se 2 (by rfl) ⟨497466, by rfl⟩ : syracuseStep 1326577 = 994933) B994933
theorem B1326611 : Blo 782338 1326611 := bstep (se 1 (by rfl) ⟨994958, by rfl⟩ : syracuseStep 1326611 = 1989917) B1989917
theorem B1326739 : Blo 782338 1326739 := bstep (se 1 (by rfl) ⟨995054, by rfl⟩ : syracuseStep 1326739 = 1990109) B1990109
theorem B7519985 : Blo 782338 7519985 := bstep (se 2 (by rfl) ⟨2819994, by rfl⟩ : syracuseStep 7519985 = 5639989) B5639989
theorem B1326881 : Blo 782338 1326881 := bstep (se 2 (by rfl) ⟨497580, by rfl⟩ : syracuseStep 1326881 = 995161) B995161
theorem B1490737 : Blo 782338 1490737 := bstep (se 2 (by rfl) ⟨559026, by rfl⟩ : syracuseStep 1490737 = 1118053) B1118053
theorem B1982353 : Blo 782338 1982353 := bstep (se 2 (by rfl) ⟨743382, by rfl⟩ : syracuseStep 1982353 = 1486765) B1486765
theorem B1589393 : Blo 782338 1589393 := bstep (se 2 (by rfl) ⟨596022, by rfl⟩ : syracuseStep 1589393 = 1192045) B1192045
theorem B1982627 : Blo 782338 1982627 := bstep (se 1 (by rfl) ⟨1486970, by rfl⟩ : syracuseStep 1982627 = 2973941) B2973941
theorem B1491139 : Blo 782338 1491139 := bstep (se 1 (by rfl) ⟨1118354, by rfl⟩ : syracuseStep 1491139 = 2236709) B2236709
theorem B16072901 : Blo 782338 16072901 := bstep (se 4 (by rfl) ⟨1506834, by rfl⟩ : syracuseStep 16072901 = 3013669) B3013669
theorem B1491185 : Blo 782338 1491185 := bstep (se 2 (by rfl) ⟨559194, by rfl⟩ : syracuseStep 1491185 = 1118389) B1118389
theorem B7520525 : Blo 782338 7520525 := bstep (se 3 (by rfl) ⟨1410098, by rfl⟩ : syracuseStep 7520525 = 2820197) B2820197
theorem B2507021 : Blo 782338 2507021 := bstep (se 3 (by rfl) ⟨470066, by rfl⟩ : syracuseStep 2507021 = 940133) B940133
theorem B1982819 : Blo 782338 1982819 := bstep (se 1 (by rfl) ⟨1487114, by rfl⟩ : syracuseStep 1982819 = 2974229) B2974229
theorem B2507213 : Blo 782338 2507213 := bstep (se 3 (by rfl) ⟨470102, by rfl⟩ : syracuseStep 2507213 = 940205) B940205
theorem B1491473 : Blo 782338 1491473 := bstep (se 2 (by rfl) ⟨559302, by rfl⟩ : syracuseStep 1491473 = 1118605) B1118605
theorem B1786673 : Blo 782338 1786673 := bstep (se 2 (by rfl) ⟨670002, by rfl⟩ : syracuseStep 1786673 = 1340005) B1340005
theorem B836579 : Blo 782338 836579 := bstep (se 1 (by rfl) ⟨627434, by rfl⟩ : syracuseStep 836579 = 1254869) B1254869
theorem B1885187 : Blo 782338 1885187 := bstep (se 1 (by rfl) ⟨1413890, by rfl⟩ : syracuseStep 1885187 = 2827781) B2827781
theorem B1492195 : Blo 782338 1492195 := bstep (se 1 (by rfl) ⟨1119146, by rfl⟩ : syracuseStep 1492195 = 2238293) B2238293
theorem B1983761 : Blo 782338 1983761 := bstep (se 2 (by rfl) ⟨743910, by rfl⟩ : syracuseStep 1983761 = 1487821) B1487821
theorem B1983811 : Blo 782338 1983811 := bstep (se 1 (by rfl) ⟨1487858, by rfl⟩ : syracuseStep 1983811 = 2975717) B2975717
theorem B1885571 : Blo 782338 1885571 := bstep (se 1 (by rfl) ⟨1414178, by rfl⟩ : syracuseStep 1885571 = 2828357) B2828357
theorem B1590691 : Blo 782338 1590691 := bstep (se 1 (by rfl) ⟨1193018, by rfl⟩ : syracuseStep 1590691 = 2386037) B2386037
theorem B1983953 : Blo 782338 1983953 := bstep (se 2 (by rfl) ⟨743982, by rfl⟩ : syracuseStep 1983953 = 1487965) B1487965
theorem B2147843 : Blo 782338 2147843 := bstep (se 1 (by rfl) ⟨1610882, by rfl⟩ : syracuseStep 2147843 = 3221765) B3221765
theorem B1492643 : Blo 782338 1492643 := bstep (se 1 (by rfl) ⟨1119482, by rfl⟩ : syracuseStep 1492643 = 2238965) B2238965
theorem B5949125 : Blo 782338 5949125 := bstep (se 4 (by rfl) ⟨557730, by rfl⟩ : syracuseStep 5949125 = 1115461) B1115461
theorem B2016995 : Blo 782338 2016995 := bstep (se 1 (by rfl) ⟨1512746, by rfl⟩ : syracuseStep 2016995 = 3025493) B3025493
theorem B1886129 : Blo 782338 1886129 := bstep (se 2 (by rfl) ⟨707298, by rfl⟩ : syracuseStep 1886129 = 1414597) B1414597
theorem B5031877 : Blo 782338 5031877 := bstep (se 4 (by rfl) ⟨471738, by rfl⟩ : syracuseStep 5031877 = 943477) B943477
theorem B837587 : Blo 782338 837587 := bstep (se 1 (by rfl) ⟨628190, by rfl⟩ : syracuseStep 837587 = 1256381) B1256381
theorem B1886339 : Blo 782338 1886339 := bstep (se 1 (by rfl) ⟨1414754, by rfl⟩ : syracuseStep 1886339 = 2829509) B2829509
theorem B2508995 : Blo 782338 2508995 := bstep (se 1 (by rfl) ⟨1881746, by rfl⟩ : syracuseStep 2508995 = 3763493) B3763493
theorem B1591697 : Blo 782338 1591697 := bstep (se 2 (by rfl) ⟨596886, by rfl⟩ : syracuseStep 1591697 = 1193773) B1193773
theorem B1984945 : Blo 782338 1984945 := bstep (se 2 (by rfl) ⟨744354, by rfl⟩ : syracuseStep 1984945 = 1488709) B1488709
theorem B1985219 : Blo 782338 1985219 := bstep (se 1 (by rfl) ⟨1488914, by rfl⟩ : syracuseStep 1985219 = 2977829) B2977829
theorem B2640653 : Blo 782338 2640653 := bstep (se 3 (by rfl) ⟨495122, by rfl⟩ : syracuseStep 2640653 = 990245) B990245
theorem B2640707 : Blo 782338 2640707 := bstep (se 1 (by rfl) ⟨1980530, by rfl⟩ : syracuseStep 2640707 = 3961061) B3961061
theorem B1985411 : Blo 782338 1985411 := bstep (se 1 (by rfl) ⟨1489058, by rfl⟩ : syracuseStep 1985411 = 2978117) B2978117
theorem B1887185 : Blo 782338 1887185 := bstep (se 2 (by rfl) ⟨707694, by rfl⟩ : syracuseStep 1887185 = 1415389) B1415389
theorem B2640977 : Blo 782338 2640977 := bstep (se 2 (by rfl) ⟨990366, by rfl⟩ : syracuseStep 2640977 = 1980733) B1980733
theorem B1887715 : Blo 782338 1887715 := bstep (se 1 (by rfl) ⟨1415786, by rfl⟩ : syracuseStep 1887715 = 2831573) B2831573
theorem B839155 : Blo 782338 839155 := bstep (se 1 (by rfl) ⟨629366, by rfl⟩ : syracuseStep 839155 = 1258733) B1258733
theorem B2641517 : Blo 782338 2641517 := bstep (se 3 (by rfl) ⟨495284, by rfl⟩ : syracuseStep 2641517 = 990569) B990569
theorem B2641571 : Blo 782338 2641571 := bstep (se 1 (by rfl) ⟨1981178, by rfl⟩ : syracuseStep 2641571 = 3962357) B3962357
theorem B1593091 : Blo 782338 1593091 := bstep (se 1 (by rfl) ⟨1194818, by rfl⟩ : syracuseStep 1593091 = 2389637) B2389637
theorem B5426957 : Blo 782338 5426957 := bstep (se 3 (by rfl) ⟨1017554, by rfl⟩ : syracuseStep 5426957 = 2035109) B2035109
theorem B3821347 : Blo 782338 3821347 := bstep (se 1 (by rfl) ⟨2866010, by rfl⟩ : syracuseStep 3821347 = 5732021) B5732021
theorem B1986353 : Blo 782338 1986353 := bstep (se 2 (by rfl) ⟨744882, by rfl⟩ : syracuseStep 1986353 = 1489765) B1489765
theorem B1986403 : Blo 782338 1986403 := bstep (se 1 (by rfl) ⟨1489802, by rfl⟩ : syracuseStep 1986403 = 2979605) B2979605
theorem B2641841 : Blo 782338 2641841 := bstep (se 2 (by rfl) ⟨990690, by rfl⟩ : syracuseStep 2641841 = 1981381) B1981381
theorem B839603 : Blo 782338 839603 := bstep (se 1 (by rfl) ⟨629702, by rfl⟩ : syracuseStep 839603 = 1259405) B1259405
theorem B1986545 : Blo 782338 1986545 := bstep (se 2 (by rfl) ⟨744954, by rfl⟩ : syracuseStep 1986545 = 1489909) B1489909
theorem B21418181 : Blo 782338 21418181 := bstep (se 4 (by rfl) ⟨2007954, by rfl⟩ : syracuseStep 21418181 = 4015909) B4015909
theorem B1003747 : Blo 782338 1003747 := bstep (se 1 (by rfl) ⟨752810, by rfl⟩ : syracuseStep 1003747 = 1505621) B1505621
theorem B2511121 : Blo 782338 2511121 := bstep (se 2 (by rfl) ⟨941670, by rfl⟩ : syracuseStep 2511121 = 1883341) B1883341
theorem B2642381 : Blo 782338 2642381 := bstep (se 3 (by rfl) ⟨495446, by rfl⟩ : syracuseStep 2642381 = 990893) B990893
theorem B2642435 : Blo 782338 2642435 := bstep (se 1 (by rfl) ⟨1981826, by rfl⟩ : syracuseStep 2642435 = 3963653) B3963653
theorem B5034595 : Blo 782338 5034595 := bstep (se 1 (by rfl) ⟨3775946, by rfl⟩ : syracuseStep 5034595 = 7551893) B7551893
theorem B2118349 : Blo 782338 2118349 := bstep (se 3 (by rfl) ⟨397190, by rfl⟩ : syracuseStep 2118349 = 794381) B794381
theorem B2642705 : Blo 782338 2642705 := bstep (se 2 (by rfl) ⟨991014, by rfl⟩ : syracuseStep 2642705 = 1982029) B1982029
theorem B1987537 : Blo 782338 1987537 := bstep (se 2 (by rfl) ⟨745326, by rfl⟩ : syracuseStep 1987537 = 1490653) B1490653
theorem B6804593 : Blo 782338 6804593 := bstep (se 2 (by rfl) ⟨2551722, by rfl⟩ : syracuseStep 6804593 = 5103445) B5103445
theorem B1987811 : Blo 782338 1987811 := bstep (se 1 (by rfl) ⟨1490858, by rfl⟩ : syracuseStep 1987811 = 2981717) B2981717
theorem B2643245 : Blo 782338 2643245 := bstep (se 3 (by rfl) ⟨495608, by rfl⟩ : syracuseStep 2643245 = 991217) B991217
theorem B2643299 : Blo 782338 2643299 := bstep (se 1 (by rfl) ⟨1982474, by rfl⟩ : syracuseStep 2643299 = 3964949) B3964949
theorem B1988003 : Blo 782338 1988003 := bstep (se 1 (by rfl) ⟨1491002, by rfl⟩ : syracuseStep 1988003 = 2982005) B2982005
theorem B2643569 : Blo 782338 2643569 := bstep (se 2 (by rfl) ⟨991338, by rfl⟩ : syracuseStep 2643569 = 1982677) B1982677
theorem B2971313 : Blo 782338 2971313 := bstep (se 2 (by rfl) ⟨1114242, by rfl⟩ : syracuseStep 2971313 = 2228485) B2228485
theorem B2119409 : Blo 782338 2119409 := bstep (se 2 (by rfl) ⟨794778, by rfl⟩ : syracuseStep 2119409 = 1589557) B1589557
theorem B10213219 : Blo 782338 10213219 := bstep (se 1 (by rfl) ⟨7659914, by rfl⟩ : syracuseStep 10213219 = 15319829) B15319829
theorem B10049507 : Blo 782338 10049507 := bstep (se 1 (by rfl) ⟨7537130, by rfl⟩ : syracuseStep 10049507 = 15074261) B15074261
theorem B7166065 : Blo 782338 7166065 := bstep (se 2 (by rfl) ⟨2687274, by rfl⟩ : syracuseStep 7166065 = 5374549) B5374549
theorem B2644109 : Blo 782338 2644109 := bstep (se 3 (by rfl) ⟨495770, by rfl⟩ : syracuseStep 2644109 = 991541) B991541
theorem B2513069 : Blo 782338 2513069 := bstep (se 3 (by rfl) ⟨471200, by rfl⟩ : syracuseStep 2513069 = 942401) B942401
theorem B2644163 : Blo 782338 2644163 := bstep (se 1 (by rfl) ⟨1983122, by rfl⟩ : syracuseStep 2644163 = 3966245) B3966245
theorem B2513197 : Blo 782338 2513197 := bstep (se 3 (by rfl) ⟨471224, by rfl⟩ : syracuseStep 2513197 = 942449) B942449
theorem B1988945 : Blo 782338 1988945 := bstep (se 2 (by rfl) ⟨745854, by rfl⟩ : syracuseStep 1988945 = 1491709) B1491709
theorem B1988995 : Blo 782338 1988995 := bstep (se 1 (by rfl) ⟨1491746, by rfl⟩ : syracuseStep 1988995 = 2983493) B2983493
theorem B2644433 : Blo 782338 2644433 := bstep (se 2 (by rfl) ⟨991662, by rfl⟩ : syracuseStep 2644433 = 1983325) B1983325
theorem B1989137 : Blo 782338 1989137 := bstep (se 2 (by rfl) ⟨745926, by rfl⟩ : syracuseStep 1989137 = 1491853) B1491853
theorem B5036593 : Blo 782338 5036593 := bstep (se 2 (by rfl) ⟨1888722, by rfl⟩ : syracuseStep 5036593 = 3777445) B3777445
theorem B19094129 : Blo 782338 19094129 := bstep (se 2 (by rfl) ⟨7160298, by rfl⟩ : syracuseStep 19094129 = 14320597) B14320597
theorem B5364643 : Blo 782338 5364643 := bstep (se 1 (by rfl) ⟨4023482, by rfl⟩ : syracuseStep 5364643 = 8046965) B8046965
theorem B2644973 : Blo 782338 2644973 := bstep (se 3 (by rfl) ⟨495932, by rfl⟩ : syracuseStep 2644973 = 991865) B991865
theorem B2153453 : Blo 782338 2153453 := bstep (se 3 (by rfl) ⟨403772, by rfl⟩ : syracuseStep 2153453 = 807545) B807545
theorem B1694723 : Blo 782338 1694723 := bstep (se 1 (by rfl) ⟨1271042, by rfl⟩ : syracuseStep 1694723 = 2542085) B2542085
theorem B2382851 : Blo 782338 2382851 := bstep (se 1 (by rfl) ⟨1787138, by rfl⟩ : syracuseStep 2382851 = 3574277) B3574277
theorem B1760273 : Blo 782338 1760273 := bstep (se 2 (by rfl) ⟨660102, by rfl⟩ : syracuseStep 1760273 = 1320205) B1320205
theorem B1760291 : Blo 782338 1760291 := bstep (se 1 (by rfl) ⟨1320218, by rfl⟩ : syracuseStep 1760291 = 2640437) B2640437
theorem B2645027 : Blo 782338 2645027 := bstep (se 1 (by rfl) ⟨1983770, by rfl⟩ : syracuseStep 2645027 = 3967541) B3967541
theorem B1072211 : Blo 782338 1072211 := bstep (se 1 (by rfl) ⟨804158, by rfl⟩ : syracuseStep 1072211 = 1608317) B1608317
theorem B2972771 : Blo 782338 2972771 := bstep (se 1 (by rfl) ⟨2229578, by rfl⟩ : syracuseStep 2972771 = 4459157) B4459157
theorem B1760561 : Blo 782338 1760561 := bstep (se 2 (by rfl) ⟨660210, by rfl⟩ : syracuseStep 1760561 = 1320421) B1320421
theorem B2645297 : Blo 782338 2645297 := bstep (se 2 (by rfl) ⟨991986, by rfl⟩ : syracuseStep 2645297 = 1983973) B1983973
theorem B1400113 : Blo 782338 1400113 := bstep (se 2 (by rfl) ⟨525042, by rfl⟩ : syracuseStep 1400113 = 1050085) B1050085
theorem B1760579 : Blo 782338 1760579 := bstep (se 1 (by rfl) ⟨1320434, by rfl⟩ : syracuseStep 1760579 = 2640869) B2640869
theorem B5954957 : Blo 782338 5954957 := bstep (se 3 (by rfl) ⟨1116554, by rfl⟩ : syracuseStep 5954957 = 2233109) B2233109
theorem B1990129 : Blo 782338 1990129 := bstep (se 2 (by rfl) ⟨746298, by rfl⟩ : syracuseStep 1990129 = 1492597) B1492597
theorem B941555 : Blo 782338 941555 := bstep (se 1 (by rfl) ⟨706166, by rfl⟩ : syracuseStep 941555 = 1412333) B1412333
theorem B2383409 : Blo 782338 2383409 := bstep (se 2 (by rfl) ⟨893778, by rfl⟩ : syracuseStep 2383409 = 1787557) B1787557
theorem B1760849 : Blo 782338 1760849 := bstep (se 2 (by rfl) ⟨660318, by rfl⟩ : syracuseStep 1760849 = 1320637) B1320637
theorem B1760867 : Blo 782338 1760867 := bstep (se 1 (by rfl) ⟨1320650, by rfl⟩ : syracuseStep 1760867 = 2641301) B2641301
theorem B7528133 : Blo 782338 7528133 := bstep (se 4 (by rfl) ⟨705762, by rfl⟩ : syracuseStep 7528133 = 1411525) B1411525
theorem B1105633 : Blo 782338 1105633 := bstep (se 2 (by rfl) ⟨414612, by rfl⟩ : syracuseStep 1105633 = 829225) B829225
theorem B5660401 : Blo 782338 5660401 := bstep (se 2 (by rfl) ⟨2122650, by rfl⟩ : syracuseStep 5660401 = 4245301) B4245301
theorem B1990403 : Blo 782338 1990403 := bstep (se 1 (by rfl) ⟨1492802, by rfl⟩ : syracuseStep 1990403 = 2985605) B2985605
theorem B2645837 : Blo 782338 2645837 := bstep (se 3 (by rfl) ⟨496094, by rfl⟩ : syracuseStep 2645837 = 992189) B992189
theorem B1761137 : Blo 782338 1761137 := bstep (se 2 (by rfl) ⟨660426, by rfl⟩ : syracuseStep 1761137 = 1320853) B1320853
theorem B1761155 : Blo 782338 1761155 := bstep (se 1 (by rfl) ⟨1320866, by rfl⟩ : syracuseStep 1761155 = 2641733) B2641733
theorem B2645891 : Blo 782338 2645891 := bstep (se 1 (by rfl) ⟨1984418, by rfl⟩ : syracuseStep 2645891 = 3968837) B3968837
theorem B2383789 : Blo 782338 2383789 := bstep (se 3 (by rfl) ⟨446960, by rfl⟩ : syracuseStep 2383789 = 893921) B893921
theorem B2973773 : Blo 782338 2973773 := bstep (se 3 (by rfl) ⟨557582, by rfl⟩ : syracuseStep 2973773 = 1115165) B1115165
theorem B2515043 : Blo 782338 2515043 := bstep (se 1 (by rfl) ⟨1886282, by rfl⟩ : syracuseStep 2515043 = 3772565) B3772565
theorem B1761425 : Blo 782338 1761425 := bstep (se 2 (by rfl) ⟨660534, by rfl⟩ : syracuseStep 1761425 = 1321069) B1321069
theorem B2646161 : Blo 782338 2646161 := bstep (se 2 (by rfl) ⟨992310, by rfl⟩ : syracuseStep 2646161 = 1984621) B1984621
theorem B1761443 : Blo 782338 1761443 := bstep (se 1 (by rfl) ⟨1321082, by rfl⟩ : syracuseStep 1761443 = 2642165) B2642165
theorem B2678957 : Blo 782338 2678957 := bstep (se 3 (by rfl) ⟨502304, by rfl⟩ : syracuseStep 2678957 = 1004609) B1004609
theorem B1695953 : Blo 782338 1695953 := bstep (se 2 (by rfl) ⟨635982, by rfl⟩ : syracuseStep 1695953 = 1271965) B1271965
theorem B2515171 : Blo 782338 2515171 := bstep (se 1 (by rfl) ⟨1886378, by rfl⟩ : syracuseStep 2515171 = 3772757) B3772757
theorem B2515313 : Blo 782338 2515313 := bstep (se 2 (by rfl) ⟨943242, by rfl⟩ : syracuseStep 2515313 = 1886485) B1886485
theorem B1761713 : Blo 782338 1761713 := bstep (se 2 (by rfl) ⟨660642, by rfl⟩ : syracuseStep 1761713 = 1321285) B1321285
theorem B1761731 : Blo 782338 1761731 := bstep (se 1 (by rfl) ⟨1321298, by rfl⟩ : syracuseStep 1761731 = 2642597) B2642597
theorem B2515427 : Blo 782338 2515427 := bstep (se 1 (by rfl) ⟨1886570, by rfl⟩ : syracuseStep 2515427 = 3773141) B3773141
theorem B2122381 : Blo 782338 2122381 := bstep (se 3 (by rfl) ⟨397946, by rfl⟩ : syracuseStep 2122381 = 795893) B795893
theorem B2646701 : Blo 782338 2646701 := bstep (se 3 (by rfl) ⟨496256, by rfl⟩ : syracuseStep 2646701 = 992513) B992513
theorem B1762001 : Blo 782338 1762001 := bstep (se 2 (by rfl) ⟨660750, by rfl⟩ : syracuseStep 1762001 = 1321501) B1321501
theorem B1762019 : Blo 782338 1762019 := bstep (se 1 (by rfl) ⟨1321514, by rfl⟩ : syracuseStep 1762019 = 2643029) B2643029
theorem B2646755 : Blo 782338 2646755 := bstep (se 1 (by rfl) ⟨1985066, by rfl⟩ : syracuseStep 2646755 = 3970133) B3970133
theorem B1762289 : Blo 782338 1762289 := bstep (se 2 (by rfl) ⟨660858, by rfl⟩ : syracuseStep 1762289 = 1321717) B1321717
theorem B2647025 : Blo 782338 2647025 := bstep (se 2 (by rfl) ⟨992634, by rfl⟩ : syracuseStep 2647025 = 1985269) B1985269
theorem B1762307 : Blo 782338 1762307 := bstep (se 1 (by rfl) ⟨1321730, by rfl⟩ : syracuseStep 1762307 = 2643461) B2643461
theorem B3630257 : Blo 782338 3630257 := bstep (se 2 (by rfl) ⟨1361346, by rfl⟩ : syracuseStep 3630257 = 2722693) B2722693
theorem B36660437 : Blo 782338 36660437 := bstep (se 7 (by rfl) ⟨429614, by rfl⟩ : syracuseStep 36660437 = 859229) B859229
theorem B1762577 : Blo 782338 1762577 := bstep (se 2 (by rfl) ⟨660966, by rfl⟩ : syracuseStep 1762577 = 1321933) B1321933
theorem B1762595 : Blo 782338 1762595 := bstep (se 1 (by rfl) ⟨1321946, by rfl⟩ : syracuseStep 1762595 = 2643893) B2643893
theorem B2647565 : Blo 782338 2647565 := bstep (se 3 (by rfl) ⟨496418, by rfl⟩ : syracuseStep 2647565 = 992837) B992837
theorem B1762865 : Blo 782338 1762865 := bstep (se 2 (by rfl) ⟨661074, by rfl⟩ : syracuseStep 1762865 = 1322149) B1322149
theorem B1762883 : Blo 782338 1762883 := bstep (se 1 (by rfl) ⟨1322162, by rfl⟩ : syracuseStep 1762883 = 2644325) B2644325
theorem B2647619 : Blo 782338 2647619 := bstep (se 1 (by rfl) ⟨1985714, by rfl⟩ : syracuseStep 2647619 = 3971429) B3971429
theorem B2385539 : Blo 782338 2385539 := bstep (se 1 (by rfl) ⟨1789154, by rfl⟩ : syracuseStep 2385539 = 3578309) B3578309
theorem B5662477 : Blo 782338 5662477 := bstep (se 3 (by rfl) ⟨1061714, by rfl⟩ : syracuseStep 5662477 = 2123429) B2123429
theorem B1763153 : Blo 782338 1763153 := bstep (se 2 (by rfl) ⟨661182, by rfl⟩ : syracuseStep 1763153 = 1322365) B1322365
theorem B2647889 : Blo 782338 2647889 := bstep (se 2 (by rfl) ⟨992958, by rfl⟩ : syracuseStep 2647889 = 1985917) B1985917
theorem B1763171 : Blo 782338 1763171 := bstep (se 1 (by rfl) ⟨1322378, by rfl⟩ : syracuseStep 1763171 = 2644757) B2644757
theorem B1271665 : Blo 782338 1271665 := bstep (se 2 (by rfl) ⟨476874, by rfl⟩ : syracuseStep 1271665 = 953749) B953749
theorem B4843397 : Blo 782338 4843397 := bstep (se 4 (by rfl) ⟨454068, by rfl⟩ : syracuseStep 4843397 = 908137) B908137
theorem B944131 : Blo 782338 944131 := bstep (se 1 (by rfl) ⟨708098, by rfl⟩ : syracuseStep 944131 = 1416197) B1416197
theorem B1173521 : Blo 782338 1173521 := bstep (se 2 (by rfl) ⟨440070, by rfl⟩ : syracuseStep 1173521 = 880141) B880141
theorem B1173539 : Blo 782338 1173539 := bstep (se 1 (by rfl) ⟨880154, by rfl⟩ : syracuseStep 1173539 = 1760309) B1760309
theorem B1173569 : Blo 782338 1173569 := bstep (se 2 (by rfl) ⟨440088, by rfl⟩ : syracuseStep 1173569 = 880177) B880177
theorem B1173587 : Blo 782338 1173587 := bstep (se 1 (by rfl) ⟨880190, by rfl⟩ : syracuseStep 1173587 = 1760381) B1760381
theorem B944227 : Blo 782338 944227 := bstep (se 1 (by rfl) ⟨708170, by rfl⟩ : syracuseStep 944227 = 1416341) B1416341
theorem B1173617 : Blo 782338 1173617 := bstep (se 2 (by rfl) ⟨440106, by rfl⟩ : syracuseStep 1173617 = 880213) B880213
theorem B1763441 : Blo 782338 1763441 := bstep (se 2 (by rfl) ⟨661290, by rfl⟩ : syracuseStep 1763441 = 1322581) B1322581
theorem B1173635 : Blo 782338 1173635 := bstep (se 1 (by rfl) ⟨880226, by rfl⟩ : syracuseStep 1173635 = 1760453) B1760453
theorem B1763459 : Blo 782338 1763459 := bstep (se 1 (by rfl) ⟨1322594, by rfl⟩ : syracuseStep 1763459 = 2645189) B2645189
theorem B2975885 : Blo 782338 2975885 := bstep (se 3 (by rfl) ⟨557978, by rfl⟩ : syracuseStep 2975885 = 1115957) B1115957
theorem B1173665 : Blo 782338 1173665 := bstep (se 2 (by rfl) ⟨440124, by rfl⟩ : syracuseStep 1173665 = 880249) B880249
theorem B2517169 : Blo 782338 2517169 := bstep (se 2 (by rfl) ⟨943938, by rfl⟩ : syracuseStep 2517169 = 1887877) B1887877
theorem B1173683 : Blo 782338 1173683 := bstep (se 1 (by rfl) ⟨880262, by rfl⟩ : syracuseStep 1173683 = 1760525) B1760525
theorem B1173713 : Blo 782338 1173713 := bstep (se 2 (by rfl) ⟨440142, by rfl⟩ : syracuseStep 1173713 = 880285) B880285
theorem B1173731 : Blo 782338 1173731 := bstep (se 1 (by rfl) ⟨880298, by rfl⟩ : syracuseStep 1173731 = 1760597) B1760597
theorem B5957873 : Blo 782338 5957873 := bstep (se 2 (by rfl) ⟨2234202, by rfl⟩ : syracuseStep 5957873 = 4468405) B4468405
theorem B1173761 : Blo 782338 1173761 := bstep (se 2 (by rfl) ⟨440160, by rfl⟩ : syracuseStep 1173761 = 880321) B880321
theorem B1173779 : Blo 782338 1173779 := bstep (se 1 (by rfl) ⟨880334, by rfl⟩ : syracuseStep 1173779 = 1760669) B1760669
theorem B1173809 : Blo 782338 1173809 := bstep (se 2 (by rfl) ⟨440178, by rfl⟩ : syracuseStep 1173809 = 880357) B880357
theorem B1173827 : Blo 782338 1173827 := bstep (se 1 (by rfl) ⟨880370, by rfl⟩ : syracuseStep 1173827 = 1760741) B1760741
theorem B1173857 : Blo 782338 1173857 := bstep (se 2 (by rfl) ⟨440196, by rfl⟩ : syracuseStep 1173857 = 880393) B880393
theorem B2648429 : Blo 782338 2648429 := bstep (se 3 (by rfl) ⟨496580, by rfl⟩ : syracuseStep 2648429 = 993161) B993161
theorem B1173875 : Blo 782338 1173875 := bstep (se 1 (by rfl) ⟨880406, by rfl⟩ : syracuseStep 1173875 = 1760813) B1760813
theorem B1173905 : Blo 782338 1173905 := bstep (se 2 (by rfl) ⟨440214, by rfl⟩ : syracuseStep 1173905 = 880429) B880429
theorem B1763729 : Blo 782338 1763729 := bstep (se 2 (by rfl) ⟨661398, by rfl⟩ : syracuseStep 1763729 = 1322797) B1322797
theorem B1173923 : Blo 782338 1173923 := bstep (se 1 (by rfl) ⟨880442, by rfl⟩ : syracuseStep 1173923 = 1760885) B1760885
theorem B1763747 : Blo 782338 1763747 := bstep (se 1 (by rfl) ⟨1322810, by rfl⟩ : syracuseStep 1763747 = 2645621) B2645621
theorem B2648483 : Blo 782338 2648483 := bstep (se 1 (by rfl) ⟨1986362, by rfl⟩ : syracuseStep 2648483 = 3972725) B3972725
theorem B1173953 : Blo 782338 1173953 := bstep (se 2 (by rfl) ⟨440232, by rfl⟩ : syracuseStep 1173953 = 880465) B880465
theorem B1173971 : Blo 782338 1173971 := bstep (se 1 (by rfl) ⟨880478, by rfl⟩ : syracuseStep 1173971 = 1760957) B1760957
theorem B1174001 : Blo 782338 1174001 := bstep (se 2 (by rfl) ⟨440250, by rfl⟩ : syracuseStep 1174001 = 880501) B880501
theorem B1174019 : Blo 782338 1174019 := bstep (se 1 (by rfl) ⟨880514, by rfl⟩ : syracuseStep 1174019 = 1761029) B1761029
theorem B1174049 : Blo 782338 1174049 := bstep (se 2 (by rfl) ⟨440268, by rfl⟩ : syracuseStep 1174049 = 880537) B880537
theorem B1174067 : Blo 782338 1174067 := bstep (se 1 (by rfl) ⟨880550, by rfl⟩ : syracuseStep 1174067 = 1761101) B1761101
theorem B1174097 : Blo 782338 1174097 := bstep (se 2 (by rfl) ⟨440286, by rfl⟩ : syracuseStep 1174097 = 880573) B880573
theorem B2386513 : Blo 782338 2386513 := bstep (se 2 (by rfl) ⟨894942, by rfl⟩ : syracuseStep 2386513 = 1789885) B1789885
theorem B1174115 : Blo 782338 1174115 := bstep (se 1 (by rfl) ⟨880586, by rfl⟩ : syracuseStep 1174115 = 1761173) B1761173
theorem B1174145 : Blo 782338 1174145 := bstep (se 2 (by rfl) ⟨440304, by rfl⟩ : syracuseStep 1174145 = 880609) B880609
theorem B1174163 : Blo 782338 1174163 := bstep (se 1 (by rfl) ⟨880622, by rfl⟩ : syracuseStep 1174163 = 1761245) B1761245
theorem B1174193 : Blo 782338 1174193 := bstep (se 2 (by rfl) ⟨440322, by rfl⟩ : syracuseStep 1174193 = 880645) B880645
theorem B1764017 : Blo 782338 1764017 := bstep (se 2 (by rfl) ⟨661506, by rfl⟩ : syracuseStep 1764017 = 1323013) B1323013
theorem B2648753 : Blo 782338 2648753 := bstep (se 2 (by rfl) ⟨993282, by rfl⟩ : syracuseStep 2648753 = 1986565) B1986565
theorem B1174211 : Blo 782338 1174211 := bstep (se 1 (by rfl) ⟨880658, by rfl⟩ : syracuseStep 1174211 = 1761317) B1761317
theorem B1764035 : Blo 782338 1764035 := bstep (se 1 (by rfl) ⟨1323026, by rfl⟩ : syracuseStep 1764035 = 2646053) B2646053
theorem B1174241 : Blo 782338 1174241 := bstep (se 2 (by rfl) ⟨440340, by rfl⟩ : syracuseStep 1174241 = 880681) B880681
theorem B1174259 : Blo 782338 1174259 := bstep (se 1 (by rfl) ⟨880694, by rfl⟩ : syracuseStep 1174259 = 1761389) B1761389
theorem B1174289 : Blo 782338 1174289 := bstep (se 2 (by rfl) ⟨440358, by rfl⟩ : syracuseStep 1174289 = 880717) B880717
theorem B1174307 : Blo 782338 1174307 := bstep (se 1 (by rfl) ⟨880730, by rfl⟩ : syracuseStep 1174307 = 1761461) B1761461
theorem B1174337 : Blo 782338 1174337 := bstep (se 2 (by rfl) ⟨440376, by rfl⟩ : syracuseStep 1174337 = 880753) B880753
theorem B1174355 : Blo 782338 1174355 := bstep (se 1 (by rfl) ⟨880766, by rfl⟩ : syracuseStep 1174355 = 1761533) B1761533
theorem B1174385 : Blo 782338 1174385 := bstep (se 2 (by rfl) ⟨440394, by rfl⟩ : syracuseStep 1174385 = 880789) B880789
theorem B1174403 : Blo 782338 1174403 := bstep (se 1 (by rfl) ⟨880802, by rfl⟩ : syracuseStep 1174403 = 1761605) B1761605
theorem B1174433 : Blo 782338 1174433 := bstep (se 2 (by rfl) ⟨440412, by rfl⟩ : syracuseStep 1174433 = 880825) B880825
theorem B2976689 : Blo 782338 2976689 := bstep (se 2 (by rfl) ⟨1116258, by rfl⟩ : syracuseStep 2976689 = 2232517) B2232517
theorem B1174451 : Blo 782338 1174451 := bstep (se 1 (by rfl) ⟨880838, by rfl⟩ : syracuseStep 1174451 = 1761677) B1761677
theorem B1174481 : Blo 782338 1174481 := bstep (se 2 (by rfl) ⟨440430, by rfl⟩ : syracuseStep 1174481 = 880861) B880861
theorem B1764305 : Blo 782338 1764305 := bstep (se 2 (by rfl) ⟨661614, by rfl⟩ : syracuseStep 1764305 = 1323229) B1323229
theorem B1174499 : Blo 782338 1174499 := bstep (se 1 (by rfl) ⟨880874, by rfl⟩ : syracuseStep 1174499 = 1761749) B1761749
theorem B1764323 : Blo 782338 1764323 := bstep (se 1 (by rfl) ⟨1323242, by rfl⟩ : syracuseStep 1764323 = 2646485) B2646485
theorem B1174529 : Blo 782338 1174529 := bstep (se 2 (by rfl) ⟨440448, by rfl⟩ : syracuseStep 1174529 = 880897) B880897
theorem B1174547 : Blo 782338 1174547 := bstep (se 1 (by rfl) ⟨880910, by rfl⟩ : syracuseStep 1174547 = 1761821) B1761821
theorem B1174577 : Blo 782338 1174577 := bstep (se 2 (by rfl) ⟨440466, by rfl⟩ : syracuseStep 1174577 = 880933) B880933
theorem B13593653 : Blo 782338 13593653 := bstep (se 5 (by rfl) ⟨637202, by rfl⟩ : syracuseStep 13593653 = 1274405) B1274405
theorem B1174595 : Blo 782338 1174595 := bstep (se 1 (by rfl) ⟨880946, by rfl⟩ : syracuseStep 1174595 = 1761893) B1761893
theorem B1174625 : Blo 782338 1174625 := bstep (se 2 (by rfl) ⟨440484, by rfl⟩ : syracuseStep 1174625 = 880969) B880969
theorem B1174643 : Blo 782338 1174643 := bstep (se 1 (by rfl) ⟨880982, by rfl⟩ : syracuseStep 1174643 = 1761965) B1761965
theorem B1174673 : Blo 782338 1174673 := bstep (se 2 (by rfl) ⟨440502, by rfl⟩ : syracuseStep 1174673 = 881005) B881005
theorem B1076371 : Blo 782338 1076371 := bstep (se 1 (by rfl) ⟨807278, by rfl⟩ : syracuseStep 1076371 = 1614557) B1614557
theorem B1174691 : Blo 782338 1174691 := bstep (se 1 (by rfl) ⟨881018, by rfl⟩ : syracuseStep 1174691 = 1762037) B1762037
theorem B1174721 : Blo 782338 1174721 := bstep (se 2 (by rfl) ⟨440520, by rfl⟩ : syracuseStep 1174721 = 881041) B881041
theorem B2649293 : Blo 782338 2649293 := bstep (se 3 (by rfl) ⟨496742, by rfl⟩ : syracuseStep 2649293 = 993485) B993485
theorem B1174739 : Blo 782338 1174739 := bstep (se 1 (by rfl) ⟨881054, by rfl⟩ : syracuseStep 1174739 = 1762109) B1762109
theorem B1174769 : Blo 782338 1174769 := bstep (se 2 (by rfl) ⟨440538, by rfl⟩ : syracuseStep 1174769 = 881077) B881077
theorem B1764593 : Blo 782338 1764593 := bstep (se 2 (by rfl) ⟨661722, by rfl⟩ : syracuseStep 1764593 = 1323445) B1323445
theorem B1174787 : Blo 782338 1174787 := bstep (se 1 (by rfl) ⟨881090, by rfl⟩ : syracuseStep 1174787 = 1762181) B1762181
theorem B1764611 : Blo 782338 1764611 := bstep (se 1 (by rfl) ⟨1323458, by rfl⟩ : syracuseStep 1764611 = 2646917) B2646917
theorem B2649347 : Blo 782338 2649347 := bstep (se 1 (by rfl) ⟨1987010, by rfl⟩ : syracuseStep 2649347 = 3974021) B3974021
theorem B2518285 : Blo 782338 2518285 := bstep (se 3 (by rfl) ⟨472178, by rfl⟩ : syracuseStep 2518285 = 944357) B944357
theorem B1174817 : Blo 782338 1174817 := bstep (se 2 (by rfl) ⟨440556, by rfl⟩ : syracuseStep 1174817 = 881113) B881113
theorem B1174835 : Blo 782338 1174835 := bstep (se 1 (by rfl) ⟨881126, by rfl⟩ : syracuseStep 1174835 = 1762253) B1762253
theorem B1174865 : Blo 782338 1174865 := bstep (se 2 (by rfl) ⟨440574, by rfl⟩ : syracuseStep 1174865 = 881149) B881149
theorem B1174883 : Blo 782338 1174883 := bstep (se 1 (by rfl) ⟨881162, by rfl⟩ : syracuseStep 1174883 = 1762325) B1762325
theorem B1174913 : Blo 782338 1174913 := bstep (se 2 (by rfl) ⟨440592, by rfl⟩ : syracuseStep 1174913 = 881185) B881185
theorem B1174931 : Blo 782338 1174931 := bstep (se 1 (by rfl) ⟨881198, by rfl⟩ : syracuseStep 1174931 = 1762397) B1762397
theorem B1174961 : Blo 782338 1174961 := bstep (se 2 (by rfl) ⟨440610, by rfl⟩ : syracuseStep 1174961 = 881221) B881221
theorem B1174979 : Blo 782338 1174979 := bstep (se 1 (by rfl) ⟨881234, by rfl⟩ : syracuseStep 1174979 = 1762469) B1762469
theorem B1175009 : Blo 782338 1175009 := bstep (se 2 (by rfl) ⟨440628, by rfl⟩ : syracuseStep 1175009 = 881257) B881257
theorem B1175027 : Blo 782338 1175027 := bstep (se 1 (by rfl) ⟨881270, by rfl⟩ : syracuseStep 1175027 = 1762541) B1762541
theorem B1175057 : Blo 782338 1175057 := bstep (se 2 (by rfl) ⟨440646, by rfl⟩ : syracuseStep 1175057 = 881293) B881293
theorem B1764881 : Blo 782338 1764881 := bstep (se 2 (by rfl) ⟨661830, by rfl⟩ : syracuseStep 1764881 = 1323661) B1323661
theorem B2649617 : Blo 782338 2649617 := bstep (se 2 (by rfl) ⟨993606, by rfl⟩ : syracuseStep 2649617 = 1987213) B1987213
theorem B1175075 : Blo 782338 1175075 := bstep (se 1 (by rfl) ⟨881306, by rfl⟩ : syracuseStep 1175075 = 1762613) B1762613
theorem B1764899 : Blo 782338 1764899 := bstep (se 1 (by rfl) ⟨1323674, by rfl⟩ : syracuseStep 1764899 = 2647349) B2647349
theorem B1175105 : Blo 782338 1175105 := bstep (se 2 (by rfl) ⟨440664, by rfl⟩ : syracuseStep 1175105 = 881329) B881329
theorem B880195 : Blo 782338 880195 := bstep (se 1 (by rfl) ⟨660146, by rfl⟩ : syracuseStep 880195 = 1320293) B1320293
theorem B2977357 : Blo 782338 2977357 := bstep (se 3 (by rfl) ⟨558254, by rfl⟩ : syracuseStep 2977357 = 1116509) B1116509
theorem B1175123 : Blo 782338 1175123 := bstep (se 1 (by rfl) ⟨881342, by rfl⟩ : syracuseStep 1175123 = 1762685) B1762685
theorem B3173987 : Blo 782338 3173987 := bstep (se 1 (by rfl) ⟨2380490, by rfl⟩ : syracuseStep 3173987 = 4760981) B4760981
theorem B2715245 : Blo 782338 2715245 := bstep (se 3 (by rfl) ⟨509108, by rfl⟩ : syracuseStep 2715245 = 1018217) B1018217
theorem B1175153 : Blo 782338 1175153 := bstep (se 2 (by rfl) ⟨440682, by rfl⟩ : syracuseStep 1175153 = 881365) B881365
theorem B1175171 : Blo 782338 1175171 := bstep (se 1 (by rfl) ⟨881378, by rfl⟩ : syracuseStep 1175171 = 1762757) B1762757
theorem B1175201 : Blo 782338 1175201 := bstep (se 2 (by rfl) ⟨440700, by rfl⟩ : syracuseStep 1175201 = 881401) B881401
theorem B1175219 : Blo 782338 1175219 := bstep (se 1 (by rfl) ⟨881414, by rfl⟩ : syracuseStep 1175219 = 1762829) B1762829
theorem B1175249 : Blo 782338 1175249 := bstep (se 2 (by rfl) ⟨440718, by rfl⟩ : syracuseStep 1175249 = 881437) B881437
theorem B880339 : Blo 782338 880339 := bstep (se 1 (by rfl) ⟨660254, by rfl⟩ : syracuseStep 880339 = 1320509) B1320509
theorem B3174115 : Blo 782338 3174115 := bstep (se 1 (by rfl) ⟨2380586, by rfl⟩ : syracuseStep 3174115 = 4761173) B4761173
theorem B1175267 : Blo 782338 1175267 := bstep (se 1 (by rfl) ⟨881450, by rfl⟩ : syracuseStep 1175267 = 1762901) B1762901
theorem B4353763 : Blo 782338 4353763 := bstep (se 1 (by rfl) ⟨3265322, by rfl⟩ : syracuseStep 4353763 = 6530645) B6530645
theorem B1175297 : Blo 782338 1175297 := bstep (se 2 (by rfl) ⟨440736, by rfl⟩ : syracuseStep 1175297 = 881473) B881473
theorem B1175315 : Blo 782338 1175315 := bstep (se 1 (by rfl) ⟨881486, by rfl⟩ : syracuseStep 1175315 = 1762973) B1762973
theorem B1175345 : Blo 782338 1175345 := bstep (se 2 (by rfl) ⟨440754, by rfl⟩ : syracuseStep 1175345 = 881509) B881509
theorem B1765169 : Blo 782338 1765169 := bstep (se 2 (by rfl) ⟨661938, by rfl⟩ : syracuseStep 1765169 = 1323877) B1323877
theorem B1175363 : Blo 782338 1175363 := bstep (se 1 (by rfl) ⟨881522, by rfl⟩ : syracuseStep 1175363 = 1763045) B1763045
theorem B1765187 : Blo 782338 1765187 := bstep (se 1 (by rfl) ⟨1323890, by rfl⟩ : syracuseStep 1765187 = 2647781) B2647781
theorem B2387789 : Blo 782338 2387789 := bstep (se 3 (by rfl) ⟨447710, by rfl⟩ : syracuseStep 2387789 = 895421) B895421
theorem B1175393 : Blo 782338 1175393 := bstep (se 2 (by rfl) ⟨440772, by rfl⟩ : syracuseStep 1175393 = 881545) B881545
theorem B880483 : Blo 782338 880483 := bstep (se 1 (by rfl) ⟨660362, by rfl⟩ : syracuseStep 880483 = 1320725) B1320725
theorem B1175411 : Blo 782338 1175411 := bstep (se 1 (by rfl) ⟨881558, by rfl⟩ : syracuseStep 1175411 = 1763117) B1763117
theorem B1175441 : Blo 782338 1175441 := bstep (se 2 (by rfl) ⟨440790, by rfl⟩ : syracuseStep 1175441 = 881581) B881581
theorem B1175459 : Blo 782338 1175459 := bstep (se 1 (by rfl) ⟨881594, by rfl⟩ : syracuseStep 1175459 = 1763189) B1763189
theorem B1175489 : Blo 782338 1175489 := bstep (se 2 (by rfl) ⟨440808, by rfl⟩ : syracuseStep 1175489 = 881617) B881617
theorem B1175507 : Blo 782338 1175507 := bstep (se 1 (by rfl) ⟨881630, by rfl⟩ : syracuseStep 1175507 = 1763261) B1763261
theorem B1175537 : Blo 782338 1175537 := bstep (se 2 (by rfl) ⟨440826, by rfl⟩ : syracuseStep 1175537 = 881653) B881653
theorem B8056817 : Blo 782338 8056817 := bstep (se 2 (by rfl) ⟨3021306, by rfl⟩ : syracuseStep 8056817 = 6042613) B6042613
theorem B880627 : Blo 782338 880627 := bstep (se 1 (by rfl) ⟨660470, by rfl⟩ : syracuseStep 880627 = 1320941) B1320941
theorem B782339 : Blo 782338 782339 := bstep (se 1 (by rfl) ⟨586754, by rfl⟩ : syracuseStep 782339 = 1173509) B1173509
theorem B1175555 : Blo 782338 1175555 := bstep (se 1 (by rfl) ⟨881666, by rfl⟩ : syracuseStep 1175555 = 1763333) B1763333
theorem B782355 : Blo 782338 782355 := bstep (se 1 (by rfl) ⟨586766, by rfl⟩ : syracuseStep 782355 = 1173533) B1173533
theorem B1175585 : Blo 782338 1175585 := bstep (se 2 (by rfl) ⟨440844, by rfl⟩ : syracuseStep 1175585 = 881689) B881689
theorem B782371 : Blo 782338 782371 := bstep (se 1 (by rfl) ⟨586778, by rfl⟩ : syracuseStep 782371 = 1173557) B1173557
theorem B2650157 : Blo 782338 2650157 := bstep (se 3 (by rfl) ⟨496904, by rfl⟩ : syracuseStep 2650157 = 993809) B993809
theorem B782387 : Blo 782338 782387 := bstep (se 1 (by rfl) ⟨586790, by rfl⟩ : syracuseStep 782387 = 1173581) B1173581
theorem B1175603 : Blo 782338 1175603 := bstep (se 1 (by rfl) ⟨881702, by rfl⟩ : syracuseStep 1175603 = 1763405) B1763405
theorem B782403 : Blo 782338 782403 := bstep (se 1 (by rfl) ⟨586802, by rfl⟩ : syracuseStep 782403 = 1173605) B1173605
theorem B2519117 : Blo 782338 2519117 := bstep (se 3 (by rfl) ⟨472334, by rfl⟩ : syracuseStep 2519117 = 944669) B944669
theorem B1175633 : Blo 782338 1175633 := bstep (se 2 (by rfl) ⟨440862, by rfl⟩ : syracuseStep 1175633 = 881725) B881725
theorem B1765457 : Blo 782338 1765457 := bstep (se 2 (by rfl) ⟨662046, by rfl⟩ : syracuseStep 1765457 = 1324093) B1324093
theorem B782419 : Blo 782338 782419 := bstep (se 1 (by rfl) ⟨586814, by rfl⟩ : syracuseStep 782419 = 1173629) B1173629
theorem B782435 : Blo 782338 782435 := bstep (se 1 (by rfl) ⟨586826, by rfl⟩ : syracuseStep 782435 = 1173653) B1173653
theorem B1175651 : Blo 782338 1175651 := bstep (se 1 (by rfl) ⟨881738, by rfl⟩ : syracuseStep 1175651 = 1763477) B1763477
theorem B1765475 : Blo 782338 1765475 := bstep (se 1 (by rfl) ⟨1324106, by rfl⟩ : syracuseStep 1765475 = 2648213) B2648213
theorem B2650211 : Blo 782338 2650211 := bstep (se 1 (by rfl) ⟨1987658, by rfl⟩ : syracuseStep 2650211 = 3975317) B3975317
theorem B782451 : Blo 782338 782451 := bstep (se 1 (by rfl) ⟨586838, by rfl⟩ : syracuseStep 782451 = 1173677) B1173677
theorem B1175681 : Blo 782338 1175681 := bstep (se 2 (by rfl) ⟨440880, by rfl⟩ : syracuseStep 1175681 = 881761) B881761
theorem B782467 : Blo 782338 782467 := bstep (se 1 (by rfl) ⟨586850, by rfl⟩ : syracuseStep 782467 = 1173701) B1173701
theorem B880771 : Blo 782338 880771 := bstep (se 1 (by rfl) ⟨660578, by rfl⟩ : syracuseStep 880771 = 1321157) B1321157
theorem B782483 : Blo 782338 782483 := bstep (se 1 (by rfl) ⟨586862, by rfl⟩ : syracuseStep 782483 = 1173725) B1173725
theorem B1175699 : Blo 782338 1175699 := bstep (se 1 (by rfl) ⟨881774, by rfl⟩ : syracuseStep 1175699 = 1763549) B1763549
theorem B782499 : Blo 782338 782499 := bstep (se 1 (by rfl) ⟨586874, by rfl⟩ : syracuseStep 782499 = 1173749) B1173749
theorem B1175729 : Blo 782338 1175729 := bstep (se 2 (by rfl) ⟨440898, by rfl⟩ : syracuseStep 1175729 = 881797) B881797
theorem B782515 : Blo 782338 782515 := bstep (se 1 (by rfl) ⟨586886, by rfl⟩ : syracuseStep 782515 = 1173773) B1173773
theorem B782531 : Blo 782338 782531 := bstep (se 1 (by rfl) ⟨586898, by rfl⟩ : syracuseStep 782531 = 1173797) B1173797
theorem B1175747 : Blo 782338 1175747 := bstep (se 1 (by rfl) ⟨881810, by rfl⟩ : syracuseStep 1175747 = 1763621) B1763621
theorem B782547 : Blo 782338 782547 := bstep (se 1 (by rfl) ⟨586910, by rfl⟩ : syracuseStep 782547 = 1173821) B1173821
theorem B1175777 : Blo 782338 1175777 := bstep (se 2 (by rfl) ⟨440916, by rfl⟩ : syracuseStep 1175777 = 881833) B881833
theorem B782563 : Blo 782338 782563 := bstep (se 1 (by rfl) ⟨586922, by rfl⟩ : syracuseStep 782563 = 1173845) B1173845
theorem B782579 : Blo 782338 782579 := bstep (se 1 (by rfl) ⟨586934, by rfl⟩ : syracuseStep 782579 = 1173869) B1173869
theorem B1175795 : Blo 782338 1175795 := bstep (se 1 (by rfl) ⟨881846, by rfl⟩ : syracuseStep 1175795 = 1763693) B1763693
theorem B782595 : Blo 782338 782595 := bstep (se 1 (by rfl) ⟨586946, by rfl⟩ : syracuseStep 782595 = 1173893) B1173893
theorem B1175825 : Blo 782338 1175825 := bstep (se 2 (by rfl) ⟨440934, by rfl⟩ : syracuseStep 1175825 = 881869) B881869
theorem B782611 : Blo 782338 782611 := bstep (se 1 (by rfl) ⟨586958, by rfl⟩ : syracuseStep 782611 = 1173917) B1173917
theorem B880915 : Blo 782338 880915 := bstep (se 1 (by rfl) ⟨660686, by rfl⟩ : syracuseStep 880915 = 1321373) B1321373
theorem B782627 : Blo 782338 782627 := bstep (se 1 (by rfl) ⟨586970, by rfl⟩ : syracuseStep 782627 = 1173941) B1173941
theorem B1175843 : Blo 782338 1175843 := bstep (se 1 (by rfl) ⟨881882, by rfl⟩ : syracuseStep 1175843 = 1763765) B1763765
theorem B782643 : Blo 782338 782643 := bstep (se 1 (by rfl) ⟨586982, by rfl⟩ : syracuseStep 782643 = 1173965) B1173965
theorem B1175873 : Blo 782338 1175873 := bstep (se 2 (by rfl) ⟨440952, by rfl⟩ : syracuseStep 1175873 = 881905) B881905
theorem B782659 : Blo 782338 782659 := bstep (se 1 (by rfl) ⟨586994, by rfl⟩ : syracuseStep 782659 = 1173989) B1173989
theorem B782675 : Blo 782338 782675 := bstep (se 1 (by rfl) ⟨587006, by rfl⟩ : syracuseStep 782675 = 1174013) B1174013
theorem B1175891 : Blo 782338 1175891 := bstep (se 1 (by rfl) ⟨881918, by rfl⟩ : syracuseStep 1175891 = 1763837) B1763837
theorem B782691 : Blo 782338 782691 := bstep (se 1 (by rfl) ⟨587018, by rfl⟩ : syracuseStep 782691 = 1174037) B1174037
theorem B2978147 : Blo 782338 2978147 := bstep (se 1 (by rfl) ⟨2233610, by rfl⟩ : syracuseStep 2978147 = 4467221) B4467221
theorem B1175921 : Blo 782338 1175921 := bstep (se 2 (by rfl) ⟨440970, by rfl⟩ : syracuseStep 1175921 = 881941) B881941
theorem B1765745 : Blo 782338 1765745 := bstep (se 2 (by rfl) ⟨662154, by rfl⟩ : syracuseStep 1765745 = 1324309) B1324309
theorem B782707 : Blo 782338 782707 := bstep (se 1 (by rfl) ⟨587030, by rfl⟩ : syracuseStep 782707 = 1174061) B1174061
theorem B2650481 : Blo 782338 2650481 := bstep (se 2 (by rfl) ⟨993930, by rfl⟩ : syracuseStep 2650481 = 1987861) B1987861
theorem B782723 : Blo 782338 782723 := bstep (se 1 (by rfl) ⟨587042, by rfl⟩ : syracuseStep 782723 = 1174085) B1174085
theorem B1175939 : Blo 782338 1175939 := bstep (se 1 (by rfl) ⟨881954, by rfl⟩ : syracuseStep 1175939 = 1763909) B1763909
theorem B1765763 : Blo 782338 1765763 := bstep (se 1 (by rfl) ⟨1324322, by rfl⟩ : syracuseStep 1765763 = 2648645) B2648645
theorem B782739 : Blo 782338 782739 := bstep (se 1 (by rfl) ⟨587054, by rfl⟩ : syracuseStep 782739 = 1174109) B1174109
theorem B1175969 : Blo 782338 1175969 := bstep (se 2 (by rfl) ⟨440988, by rfl⟩ : syracuseStep 1175969 = 881977) B881977
theorem B782755 : Blo 782338 782755 := bstep (se 1 (by rfl) ⟨587066, by rfl⟩ : syracuseStep 782755 = 1174133) B1174133
theorem B881059 : Blo 782338 881059 := bstep (se 1 (by rfl) ⟨660794, by rfl⟩ : syracuseStep 881059 = 1321589) B1321589
theorem B782771 : Blo 782338 782771 := bstep (se 1 (by rfl) ⟨587078, by rfl⟩ : syracuseStep 782771 = 1174157) B1174157
theorem B1175987 : Blo 782338 1175987 := bstep (se 1 (by rfl) ⟨881990, by rfl⟩ : syracuseStep 1175987 = 1763981) B1763981
theorem B782787 : Blo 782338 782787 := bstep (se 1 (by rfl) ⟨587090, by rfl⟩ : syracuseStep 782787 = 1174181) B1174181
theorem B1176017 : Blo 782338 1176017 := bstep (se 2 (by rfl) ⟨441006, by rfl⟩ : syracuseStep 1176017 = 882013) B882013
theorem B782803 : Blo 782338 782803 := bstep (se 1 (by rfl) ⟨587102, by rfl⟩ : syracuseStep 782803 = 1174205) B1174205
theorem B782819 : Blo 782338 782819 := bstep (se 1 (by rfl) ⟨587114, by rfl⟩ : syracuseStep 782819 = 1174229) B1174229
theorem B1176035 : Blo 782338 1176035 := bstep (se 1 (by rfl) ⟨882026, by rfl⟩ : syracuseStep 1176035 = 1764053) B1764053
theorem B782835 : Blo 782338 782835 := bstep (se 1 (by rfl) ⟨587126, by rfl⟩ : syracuseStep 782835 = 1174253) B1174253
theorem B1176065 : Blo 782338 1176065 := bstep (se 2 (by rfl) ⟨441024, by rfl⟩ : syracuseStep 1176065 = 882049) B882049
theorem B782851 : Blo 782338 782851 := bstep (se 1 (by rfl) ⟨587138, by rfl⟩ : syracuseStep 782851 = 1174277) B1174277
theorem B782867 : Blo 782338 782867 := bstep (se 1 (by rfl) ⟨587150, by rfl⟩ : syracuseStep 782867 = 1174301) B1174301
theorem B1176083 : Blo 782338 1176083 := bstep (se 1 (by rfl) ⟨882062, by rfl⟩ : syracuseStep 1176083 = 1764125) B1764125
theorem B782883 : Blo 782338 782883 := bstep (se 1 (by rfl) ⟨587162, by rfl⟩ : syracuseStep 782883 = 1174325) B1174325
theorem B1176113 : Blo 782338 1176113 := bstep (se 2 (by rfl) ⟨441042, by rfl⟩ : syracuseStep 1176113 = 882085) B882085
theorem B782899 : Blo 782338 782899 := bstep (se 1 (by rfl) ⟨587174, by rfl⟩ : syracuseStep 782899 = 1174349) B1174349
theorem B881203 : Blo 782338 881203 := bstep (se 1 (by rfl) ⟨660902, by rfl⟩ : syracuseStep 881203 = 1321805) B1321805
theorem B782915 : Blo 782338 782915 := bstep (se 1 (by rfl) ⟨587186, by rfl⟩ : syracuseStep 782915 = 1174373) B1174373
theorem B1176131 : Blo 782338 1176131 := bstep (se 1 (by rfl) ⟨882098, by rfl⟩ : syracuseStep 1176131 = 1764197) B1764197
theorem B782931 : Blo 782338 782931 := bstep (se 1 (by rfl) ⟨587198, by rfl⟩ : syracuseStep 782931 = 1174397) B1174397
theorem B1176161 : Blo 782338 1176161 := bstep (se 2 (by rfl) ⟨441060, by rfl⟩ : syracuseStep 1176161 = 882121) B882121
theorem B782947 : Blo 782338 782947 := bstep (se 1 (by rfl) ⟨587210, by rfl⟩ : syracuseStep 782947 = 1174421) B1174421
theorem B782963 : Blo 782338 782963 := bstep (se 1 (by rfl) ⟨587222, by rfl⟩ : syracuseStep 782963 = 1174445) B1174445
theorem B1176179 : Blo 782338 1176179 := bstep (se 1 (by rfl) ⟨882134, by rfl⟩ : syracuseStep 1176179 = 1764269) B1764269
theorem B782979 : Blo 782338 782979 := bstep (se 1 (by rfl) ⟨587234, by rfl⟩ : syracuseStep 782979 = 1174469) B1174469
theorem B1176209 : Blo 782338 1176209 := bstep (se 2 (by rfl) ⟨441078, by rfl⟩ : syracuseStep 1176209 = 882157) B882157
theorem B1766033 : Blo 782338 1766033 := bstep (se 2 (by rfl) ⟨662262, by rfl⟩ : syracuseStep 1766033 = 1324525) B1324525
theorem B782995 : Blo 782338 782995 := bstep (se 1 (by rfl) ⟨587246, by rfl⟩ : syracuseStep 782995 = 1174493) B1174493
theorem B783011 : Blo 782338 783011 := bstep (se 1 (by rfl) ⟨587258, by rfl⟩ : syracuseStep 783011 = 1174517) B1174517
theorem B1176227 : Blo 782338 1176227 := bstep (se 1 (by rfl) ⟨882170, by rfl⟩ : syracuseStep 1176227 = 1764341) B1764341
theorem B1766051 : Blo 782338 1766051 := bstep (se 1 (by rfl) ⟨1324538, by rfl⟩ : syracuseStep 1766051 = 2649077) B2649077
theorem B783027 : Blo 782338 783027 := bstep (se 1 (by rfl) ⟨587270, by rfl⟩ : syracuseStep 783027 = 1174541) B1174541
theorem B1176257 : Blo 782338 1176257 := bstep (se 2 (by rfl) ⟨441096, by rfl⟩ : syracuseStep 1176257 = 882193) B882193
theorem B783043 : Blo 782338 783043 := bstep (se 1 (by rfl) ⟨587282, by rfl⟩ : syracuseStep 783043 = 1174565) B1174565
theorem B881347 : Blo 782338 881347 := bstep (se 1 (by rfl) ⟨661010, by rfl⟩ : syracuseStep 881347 = 1322021) B1322021
theorem B783059 : Blo 782338 783059 := bstep (se 1 (by rfl) ⟨587294, by rfl⟩ : syracuseStep 783059 = 1174589) B1174589
theorem B1176275 : Blo 782338 1176275 := bstep (se 1 (by rfl) ⟨882206, by rfl⟩ : syracuseStep 1176275 = 1764413) B1764413
theorem B783075 : Blo 782338 783075 := bstep (se 1 (by rfl) ⟨587306, by rfl⟩ : syracuseStep 783075 = 1174613) B1174613
theorem B1176305 : Blo 782338 1176305 := bstep (se 2 (by rfl) ⟨441114, by rfl⟩ : syracuseStep 1176305 = 882229) B882229
theorem B783091 : Blo 782338 783091 := bstep (se 1 (by rfl) ⟨587318, by rfl⟩ : syracuseStep 783091 = 1174637) B1174637
theorem B783107 : Blo 782338 783107 := bstep (se 1 (by rfl) ⟨587330, by rfl⟩ : syracuseStep 783107 = 1174661) B1174661
theorem B1176323 : Blo 782338 1176323 := bstep (se 1 (by rfl) ⟨882242, by rfl⟩ : syracuseStep 1176323 = 1764485) B1764485
theorem B783123 : Blo 782338 783123 := bstep (se 1 (by rfl) ⟨587342, by rfl⟩ : syracuseStep 783123 = 1174685) B1174685
theorem B1176353 : Blo 782338 1176353 := bstep (se 2 (by rfl) ⟨441132, by rfl⟩ : syracuseStep 1176353 = 882265) B882265
theorem B783139 : Blo 782338 783139 := bstep (se 1 (by rfl) ⟨587354, by rfl⟩ : syracuseStep 783139 = 1174709) B1174709
theorem B783155 : Blo 782338 783155 := bstep (se 1 (by rfl) ⟨587366, by rfl⟩ : syracuseStep 783155 = 1174733) B1174733
theorem B1176371 : Blo 782338 1176371 := bstep (se 1 (by rfl) ⟨882278, by rfl⟩ : syracuseStep 1176371 = 1764557) B1764557
theorem B783171 : Blo 782338 783171 := bstep (se 1 (by rfl) ⟨587378, by rfl⟩ : syracuseStep 783171 = 1174757) B1174757
theorem B1176401 : Blo 782338 1176401 := bstep (se 2 (by rfl) ⟨441150, by rfl⟩ : syracuseStep 1176401 = 882301) B882301
theorem B783187 : Blo 782338 783187 := bstep (se 1 (by rfl) ⟨587390, by rfl⟩ : syracuseStep 783187 = 1174781) B1174781
theorem B881491 : Blo 782338 881491 := bstep (se 1 (by rfl) ⟨661118, by rfl⟩ : syracuseStep 881491 = 1322237) B1322237
theorem B783203 : Blo 782338 783203 := bstep (se 1 (by rfl) ⟨587402, by rfl⟩ : syracuseStep 783203 = 1174805) B1174805
theorem B1176419 : Blo 782338 1176419 := bstep (se 1 (by rfl) ⟨882314, by rfl⟩ : syracuseStep 1176419 = 1764629) B1764629
theorem B783219 : Blo 782338 783219 := bstep (se 1 (by rfl) ⟨587414, by rfl⟩ : syracuseStep 783219 = 1174829) B1174829
theorem B1176449 : Blo 782338 1176449 := bstep (se 2 (by rfl) ⟨441168, by rfl⟩ : syracuseStep 1176449 = 882337) B882337
theorem B783235 : Blo 782338 783235 := bstep (se 1 (by rfl) ⟨587426, by rfl⟩ : syracuseStep 783235 = 1174853) B1174853
theorem B2651021 : Blo 782338 2651021 := bstep (se 3 (by rfl) ⟨497066, by rfl⟩ : syracuseStep 2651021 = 994133) B994133
theorem B783251 : Blo 782338 783251 := bstep (se 1 (by rfl) ⟨587438, by rfl⟩ : syracuseStep 783251 = 1174877) B1174877
theorem B1176467 : Blo 782338 1176467 := bstep (se 1 (by rfl) ⟨882350, by rfl⟩ : syracuseStep 1176467 = 1764701) B1764701
theorem B783267 : Blo 782338 783267 := bstep (se 1 (by rfl) ⟨587450, by rfl⟩ : syracuseStep 783267 = 1174901) B1174901
theorem B1176497 : Blo 782338 1176497 := bstep (se 2 (by rfl) ⟨441186, by rfl⟩ : syracuseStep 1176497 = 882373) B882373
theorem B1766321 : Blo 782338 1766321 := bstep (se 2 (by rfl) ⟨662370, by rfl⟩ : syracuseStep 1766321 = 1324741) B1324741
theorem B783283 : Blo 782338 783283 := bstep (se 1 (by rfl) ⟨587462, by rfl⟩ : syracuseStep 783283 = 1174925) B1174925
theorem B783299 : Blo 782338 783299 := bstep (se 1 (by rfl) ⟨587474, by rfl⟩ : syracuseStep 783299 = 1174949) B1174949
theorem B1176515 : Blo 782338 1176515 := bstep (se 1 (by rfl) ⟨882386, by rfl⟩ : syracuseStep 1176515 = 1764773) B1764773
theorem B1766339 : Blo 782338 1766339 := bstep (se 1 (by rfl) ⟨1324754, by rfl⟩ : syracuseStep 1766339 = 2649509) B2649509
theorem B2651075 : Blo 782338 2651075 := bstep (se 1 (by rfl) ⟨1988306, by rfl⟩ : syracuseStep 2651075 = 3976613) B3976613
theorem B783315 : Blo 782338 783315 := bstep (se 1 (by rfl) ⟨587486, by rfl⟩ : syracuseStep 783315 = 1174973) B1174973
theorem B1176545 : Blo 782338 1176545 := bstep (se 2 (by rfl) ⟨441204, by rfl⟩ : syracuseStep 1176545 = 882409) B882409
theorem B783331 : Blo 782338 783331 := bstep (se 1 (by rfl) ⟨587498, by rfl⟩ : syracuseStep 783331 = 1174997) B1174997
theorem B881635 : Blo 782338 881635 := bstep (se 1 (by rfl) ⟨661226, by rfl⟩ : syracuseStep 881635 = 1322453) B1322453
theorem B2552813 : Blo 782338 2552813 := bstep (se 3 (by rfl) ⟨478652, by rfl⟩ : syracuseStep 2552813 = 957305) B957305
theorem B2978801 : Blo 782338 2978801 := bstep (se 2 (by rfl) ⟨1117050, by rfl⟩ : syracuseStep 2978801 = 2234101) B2234101
theorem B783347 : Blo 782338 783347 := bstep (se 1 (by rfl) ⟨587510, by rfl⟩ : syracuseStep 783347 = 1175021) B1175021
theorem B1176563 : Blo 782338 1176563 := bstep (se 1 (by rfl) ⟨882422, by rfl⟩ : syracuseStep 1176563 = 1764845) B1764845
theorem B783363 : Blo 782338 783363 := bstep (se 1 (by rfl) ⟨587522, by rfl⟩ : syracuseStep 783363 = 1175045) B1175045
theorem B1176593 : Blo 782338 1176593 := bstep (se 2 (by rfl) ⟨441222, by rfl⟩ : syracuseStep 1176593 = 882445) B882445
theorem B783379 : Blo 782338 783379 := bstep (se 1 (by rfl) ⟨587534, by rfl⟩ : syracuseStep 783379 = 1175069) B1175069
theorem B783395 : Blo 782338 783395 := bstep (se 1 (by rfl) ⟨587546, by rfl⟩ : syracuseStep 783395 = 1175093) B1175093
theorem B1176611 : Blo 782338 1176611 := bstep (se 1 (by rfl) ⟨882458, by rfl⟩ : syracuseStep 1176611 = 1764917) B1764917
theorem B783411 : Blo 782338 783411 := bstep (se 1 (by rfl) ⟨587558, by rfl⟩ : syracuseStep 783411 = 1175117) B1175117
theorem B1176641 : Blo 782338 1176641 := bstep (se 2 (by rfl) ⟨441240, by rfl⟩ : syracuseStep 1176641 = 882481) B882481
theorem B783427 : Blo 782338 783427 := bstep (se 1 (by rfl) ⟨587570, by rfl⟩ : syracuseStep 783427 = 1175141) B1175141
theorem B783443 : Blo 782338 783443 := bstep (se 1 (by rfl) ⟨587582, by rfl⟩ : syracuseStep 783443 = 1175165) B1175165
theorem B1176659 : Blo 782338 1176659 := bstep (se 1 (by rfl) ⟨882494, by rfl⟩ : syracuseStep 1176659 = 1764989) B1764989
theorem B783459 : Blo 782338 783459 := bstep (se 1 (by rfl) ⟨587594, by rfl⟩ : syracuseStep 783459 = 1175189) B1175189
theorem B2290801 : Blo 782338 2290801 := bstep (se 2 (by rfl) ⟨859050, by rfl⟩ : syracuseStep 2290801 = 1718101) B1718101
theorem B1176689 : Blo 782338 1176689 := bstep (se 2 (by rfl) ⟨441258, by rfl⟩ : syracuseStep 1176689 = 882517) B882517
theorem B783475 : Blo 782338 783475 := bstep (se 1 (by rfl) ⟨587606, by rfl⟩ : syracuseStep 783475 = 1175213) B1175213
theorem B881779 : Blo 782338 881779 := bstep (se 1 (by rfl) ⟨661334, by rfl⟩ : syracuseStep 881779 = 1322669) B1322669
theorem B783491 : Blo 782338 783491 := bstep (se 1 (by rfl) ⟨587618, by rfl⟩ : syracuseStep 783491 = 1175237) B1175237
theorem B1176707 : Blo 782338 1176707 := bstep (se 1 (by rfl) ⟨882530, by rfl⟩ : syracuseStep 1176707 = 1765061) B1765061
theorem B783507 : Blo 782338 783507 := bstep (se 1 (by rfl) ⟨587630, by rfl⟩ : syracuseStep 783507 = 1175261) B1175261
theorem B1176737 : Blo 782338 1176737 := bstep (se 2 (by rfl) ⟨441276, by rfl⟩ : syracuseStep 1176737 = 882553) B882553
theorem B783523 : Blo 782338 783523 := bstep (se 1 (by rfl) ⟨587642, by rfl⟩ : syracuseStep 783523 = 1175285) B1175285
theorem B3962033 : Blo 782338 3962033 := bstep (se 2 (by rfl) ⟨1485762, by rfl⟩ : syracuseStep 3962033 = 2971525) B2971525
theorem B783539 : Blo 782338 783539 := bstep (se 1 (by rfl) ⟨587654, by rfl⟩ : syracuseStep 783539 = 1175309) B1175309
theorem B1176755 : Blo 782338 1176755 := bstep (se 1 (by rfl) ⟨882566, by rfl⟩ : syracuseStep 1176755 = 1765133) B1765133
theorem B783555 : Blo 782338 783555 := bstep (se 1 (by rfl) ⟨587666, by rfl⟩ : syracuseStep 783555 = 1175333) B1175333
theorem B1176785 : Blo 782338 1176785 := bstep (se 2 (by rfl) ⟨441294, by rfl⟩ : syracuseStep 1176785 = 882589) B882589
theorem B1766609 : Blo 782338 1766609 := bstep (se 2 (by rfl) ⟨662478, by rfl⟩ : syracuseStep 1766609 = 1324957) B1324957
theorem B783571 : Blo 782338 783571 := bstep (se 1 (by rfl) ⟨587678, by rfl⟩ : syracuseStep 783571 = 1175357) B1175357
theorem B2651345 : Blo 782338 2651345 := bstep (se 2 (by rfl) ⟨994254, by rfl⟩ : syracuseStep 2651345 = 1988509) B1988509
theorem B783587 : Blo 782338 783587 := bstep (se 1 (by rfl) ⟨587690, by rfl⟩ : syracuseStep 783587 = 1175381) B1175381
theorem B1176803 : Blo 782338 1176803 := bstep (se 1 (by rfl) ⟨882602, by rfl⟩ : syracuseStep 1176803 = 1765205) B1765205
theorem B1766627 : Blo 782338 1766627 := bstep (se 1 (by rfl) ⟨1324970, by rfl⟩ : syracuseStep 1766627 = 2649941) B2649941
theorem B783603 : Blo 782338 783603 := bstep (se 1 (by rfl) ⟨587702, by rfl⟩ : syracuseStep 783603 = 1175405) B1175405
theorem B1176833 : Blo 782338 1176833 := bstep (se 2 (by rfl) ⟨441312, by rfl⟩ : syracuseStep 1176833 = 882625) B882625
theorem B783619 : Blo 782338 783619 := bstep (se 1 (by rfl) ⟨587714, by rfl⟩ : syracuseStep 783619 = 1175429) B1175429
theorem B881923 : Blo 782338 881923 := bstep (se 1 (by rfl) ⟨661442, by rfl⟩ : syracuseStep 881923 = 1322885) B1322885
theorem B783635 : Blo 782338 783635 := bstep (se 1 (by rfl) ⟨587726, by rfl⟩ : syracuseStep 783635 = 1175453) B1175453
theorem B1176851 : Blo 782338 1176851 := bstep (se 1 (by rfl) ⟨882638, by rfl⟩ : syracuseStep 1176851 = 1765277) B1765277
theorem B783651 : Blo 782338 783651 := bstep (se 1 (by rfl) ⟨587738, by rfl⟩ : syracuseStep 783651 = 1175477) B1175477
theorem B1176881 : Blo 782338 1176881 := bstep (se 2 (by rfl) ⟨441330, by rfl⟩ : syracuseStep 1176881 = 882661) B882661
theorem B783667 : Blo 782338 783667 := bstep (se 1 (by rfl) ⟨587750, by rfl⟩ : syracuseStep 783667 = 1175501) B1175501
theorem B783683 : Blo 782338 783683 := bstep (se 1 (by rfl) ⟨587762, by rfl⟩ : syracuseStep 783683 = 1175525) B1175525
theorem B1176899 : Blo 782338 1176899 := bstep (se 1 (by rfl) ⟨882674, by rfl⟩ : syracuseStep 1176899 = 1765349) B1765349
theorem B783699 : Blo 782338 783699 := bstep (se 1 (by rfl) ⟨587774, by rfl⟩ : syracuseStep 783699 = 1175549) B1175549
theorem B1176929 : Blo 782338 1176929 := bstep (se 2 (by rfl) ⟨441348, by rfl⟩ : syracuseStep 1176929 = 882697) B882697
theorem B783715 : Blo 782338 783715 := bstep (se 1 (by rfl) ⟨587786, by rfl⟩ : syracuseStep 783715 = 1175573) B1175573
theorem B783731 : Blo 782338 783731 := bstep (se 1 (by rfl) ⟨587798, by rfl⟩ : syracuseStep 783731 = 1175597) B1175597
theorem B1176947 : Blo 782338 1176947 := bstep (se 1 (by rfl) ⟨882710, by rfl⟩ : syracuseStep 1176947 = 1765421) B1765421
theorem B783747 : Blo 782338 783747 := bstep (se 1 (by rfl) ⟨587810, by rfl⟩ : syracuseStep 783747 = 1175621) B1175621
theorem B1176977 : Blo 782338 1176977 := bstep (se 2 (by rfl) ⟨441366, by rfl⟩ : syracuseStep 1176977 = 882733) B882733
theorem B783763 : Blo 782338 783763 := bstep (se 1 (by rfl) ⟨587822, by rfl⟩ : syracuseStep 783763 = 1175645) B1175645
theorem B882067 : Blo 782338 882067 := bstep (se 1 (by rfl) ⟨661550, by rfl⟩ : syracuseStep 882067 = 1323101) B1323101
theorem B1340833 : Blo 782338 1340833 := bstep (se 2 (by rfl) ⟨502812, by rfl⟩ : syracuseStep 1340833 = 1005625) B1005625
theorem B783779 : Blo 782338 783779 := bstep (se 1 (by rfl) ⟨587834, by rfl⟩ : syracuseStep 783779 = 1175669) B1175669
theorem B1176995 : Blo 782338 1176995 := bstep (se 1 (by rfl) ⟨882746, by rfl⟩ : syracuseStep 1176995 = 1765493) B1765493
theorem B783795 : Blo 782338 783795 := bstep (se 1 (by rfl) ⟨587846, by rfl⟩ : syracuseStep 783795 = 1175693) B1175693
theorem B1177025 : Blo 782338 1177025 := bstep (se 2 (by rfl) ⟨441384, by rfl⟩ : syracuseStep 1177025 = 882769) B882769
theorem B783811 : Blo 782338 783811 := bstep (se 1 (by rfl) ⟨587858, by rfl⟩ : syracuseStep 783811 = 1175717) B1175717
theorem B783827 : Blo 782338 783827 := bstep (se 1 (by rfl) ⟨587870, by rfl⟩ : syracuseStep 783827 = 1175741) B1175741
theorem B1177043 : Blo 782338 1177043 := bstep (se 1 (by rfl) ⟨882782, by rfl⟩ : syracuseStep 1177043 = 1765565) B1765565
theorem B783843 : Blo 782338 783843 := bstep (se 1 (by rfl) ⟨587882, by rfl⟩ : syracuseStep 783843 = 1175765) B1175765
theorem B1177073 : Blo 782338 1177073 := bstep (se 2 (by rfl) ⟨441402, by rfl⟩ : syracuseStep 1177073 = 882805) B882805
theorem B1766897 : Blo 782338 1766897 := bstep (se 2 (by rfl) ⟨662586, by rfl⟩ : syracuseStep 1766897 = 1325173) B1325173
theorem B783859 : Blo 782338 783859 := bstep (se 1 (by rfl) ⟨587894, by rfl⟩ : syracuseStep 783859 = 1175789) B1175789
theorem B783875 : Blo 782338 783875 := bstep (se 1 (by rfl) ⟨587906, by rfl⟩ : syracuseStep 783875 = 1175813) B1175813
theorem B1177091 : Blo 782338 1177091 := bstep (se 1 (by rfl) ⟨882818, by rfl⟩ : syracuseStep 1177091 = 1765637) B1765637
theorem B1766915 : Blo 782338 1766915 := bstep (se 1 (by rfl) ⟨1325186, by rfl⟩ : syracuseStep 1766915 = 2650373) B2650373
theorem B783891 : Blo 782338 783891 := bstep (se 1 (by rfl) ⟨587918, by rfl⟩ : syracuseStep 783891 = 1175837) B1175837
theorem B1177121 : Blo 782338 1177121 := bstep (se 2 (by rfl) ⟨441420, by rfl⟩ : syracuseStep 1177121 = 882841) B882841
theorem B783907 : Blo 782338 783907 := bstep (se 1 (by rfl) ⟨587930, by rfl⟩ : syracuseStep 783907 = 1175861) B1175861
theorem B882211 : Blo 782338 882211 := bstep (se 1 (by rfl) ⟨661658, by rfl⟩ : syracuseStep 882211 = 1323317) B1323317
theorem B783923 : Blo 782338 783923 := bstep (se 1 (by rfl) ⟨587942, by rfl⟩ : syracuseStep 783923 = 1175885) B1175885
theorem B1177139 : Blo 782338 1177139 := bstep (se 1 (by rfl) ⟨882854, by rfl⟩ : syracuseStep 1177139 = 1765709) B1765709
theorem B783939 : Blo 782338 783939 := bstep (se 1 (by rfl) ⟨587954, by rfl⟩ : syracuseStep 783939 = 1175909) B1175909
theorem B1177169 : Blo 782338 1177169 := bstep (se 2 (by rfl) ⟨441438, by rfl⟩ : syracuseStep 1177169 = 882877) B882877
theorem B783955 : Blo 782338 783955 := bstep (se 1 (by rfl) ⟨587966, by rfl⟩ : syracuseStep 783955 = 1175933) B1175933
theorem B783971 : Blo 782338 783971 := bstep (se 1 (by rfl) ⟨587978, by rfl⟩ : syracuseStep 783971 = 1175957) B1175957
theorem B1177187 : Blo 782338 1177187 := bstep (se 1 (by rfl) ⟨882890, by rfl⟩ : syracuseStep 1177187 = 1765781) B1765781
theorem B783987 : Blo 782338 783987 := bstep (se 1 (by rfl) ⟨587990, by rfl⟩ : syracuseStep 783987 = 1175981) B1175981
theorem B1177217 : Blo 782338 1177217 := bstep (se 2 (by rfl) ⟨441456, by rfl⟩ : syracuseStep 1177217 = 882913) B882913
theorem B784003 : Blo 782338 784003 := bstep (se 1 (by rfl) ⟨588002, by rfl⟩ : syracuseStep 784003 = 1176005) B1176005
theorem B784019 : Blo 782338 784019 := bstep (se 1 (by rfl) ⟨588014, by rfl⟩ : syracuseStep 784019 = 1176029) B1176029
theorem B1177235 : Blo 782338 1177235 := bstep (se 1 (by rfl) ⟨882926, by rfl⟩ : syracuseStep 1177235 = 1765853) B1765853
theorem B784035 : Blo 782338 784035 := bstep (se 1 (by rfl) ⟨588026, by rfl⟩ : syracuseStep 784035 = 1176053) B1176053
theorem B1177265 : Blo 782338 1177265 := bstep (se 2 (by rfl) ⟨441474, by rfl⟩ : syracuseStep 1177265 = 882949) B882949
theorem B784051 : Blo 782338 784051 := bstep (se 1 (by rfl) ⟨588038, by rfl⟩ : syracuseStep 784051 = 1176077) B1176077
theorem B882355 : Blo 782338 882355 := bstep (se 1 (by rfl) ⟨661766, by rfl⟩ : syracuseStep 882355 = 1323533) B1323533
theorem B784067 : Blo 782338 784067 := bstep (se 1 (by rfl) ⟨588050, by rfl⟩ : syracuseStep 784067 = 1176101) B1176101
theorem B1177283 : Blo 782338 1177283 := bstep (se 1 (by rfl) ⟨882962, by rfl⟩ : syracuseStep 1177283 = 1765925) B1765925
theorem B784083 : Blo 782338 784083 := bstep (se 1 (by rfl) ⟨588062, by rfl⟩ : syracuseStep 784083 = 1176125) B1176125
theorem B1177313 : Blo 782338 1177313 := bstep (se 2 (by rfl) ⟨441492, by rfl⟩ : syracuseStep 1177313 = 882985) B882985
theorem B784099 : Blo 782338 784099 := bstep (se 1 (by rfl) ⟨588074, by rfl⟩ : syracuseStep 784099 = 1176149) B1176149
theorem B2651885 : Blo 782338 2651885 := bstep (se 3 (by rfl) ⟨497228, by rfl⟩ : syracuseStep 2651885 = 994457) B994457
theorem B784115 : Blo 782338 784115 := bstep (se 1 (by rfl) ⟨588086, by rfl⟩ : syracuseStep 784115 = 1176173) B1176173
theorem B1177331 : Blo 782338 1177331 := bstep (se 1 (by rfl) ⟨882998, by rfl⟩ : syracuseStep 1177331 = 1765997) B1765997
theorem B784131 : Blo 782338 784131 := bstep (se 1 (by rfl) ⟨588098, by rfl⟩ : syracuseStep 784131 = 1176197) B1176197
theorem B1177361 : Blo 782338 1177361 := bstep (se 2 (by rfl) ⟨441510, by rfl⟩ : syracuseStep 1177361 = 883021) B883021
theorem B784147 : Blo 782338 784147 := bstep (se 1 (by rfl) ⟨588110, by rfl⟩ : syracuseStep 784147 = 1176221) B1176221
theorem B1767185 : Blo 782338 1767185 := bstep (se 2 (by rfl) ⟨662694, by rfl⟩ : syracuseStep 1767185 = 1325389) B1325389
theorem B784163 : Blo 782338 784163 := bstep (se 1 (by rfl) ⟨588122, by rfl⟩ : syracuseStep 784163 = 1176245) B1176245
theorem B1177379 : Blo 782338 1177379 := bstep (se 1 (by rfl) ⟨883034, by rfl⟩ : syracuseStep 1177379 = 1766069) B1766069
theorem B1767203 : Blo 782338 1767203 := bstep (se 1 (by rfl) ⟨1325402, by rfl⟩ : syracuseStep 1767203 = 2650805) B2650805
theorem B2651939 : Blo 782338 2651939 := bstep (se 1 (by rfl) ⟨1988954, by rfl⟩ : syracuseStep 2651939 = 3977909) B3977909
theorem B784179 : Blo 782338 784179 := bstep (se 1 (by rfl) ⟨588134, by rfl⟩ : syracuseStep 784179 = 1176269) B1176269
theorem B1177409 : Blo 782338 1177409 := bstep (se 2 (by rfl) ⟨441528, by rfl⟩ : syracuseStep 1177409 = 883057) B883057
theorem B784195 : Blo 782338 784195 := bstep (se 1 (by rfl) ⟨588146, by rfl⟩ : syracuseStep 784195 = 1176293) B1176293
theorem B882499 : Blo 782338 882499 := bstep (se 1 (by rfl) ⟨661874, by rfl⟩ : syracuseStep 882499 = 1323749) B1323749
theorem B784211 : Blo 782338 784211 := bstep (se 1 (by rfl) ⟨588158, by rfl⟩ : syracuseStep 784211 = 1176317) B1176317
theorem B1177427 : Blo 782338 1177427 := bstep (se 1 (by rfl) ⟨883070, by rfl⟩ : syracuseStep 1177427 = 1766141) B1766141
theorem B1275731 : Blo 782338 1275731 := bstep (se 1 (by rfl) ⟨956798, by rfl⟩ : syracuseStep 1275731 = 1913597) B1913597
theorem B784227 : Blo 782338 784227 := bstep (se 1 (by rfl) ⟨588170, by rfl⟩ : syracuseStep 784227 = 1176341) B1176341
theorem B1177457 : Blo 782338 1177457 := bstep (se 2 (by rfl) ⟨441546, by rfl⟩ : syracuseStep 1177457 = 883093) B883093
theorem B784243 : Blo 782338 784243 := bstep (se 1 (by rfl) ⟨588182, by rfl⟩ : syracuseStep 784243 = 1176365) B1176365
theorem B784259 : Blo 782338 784259 := bstep (se 1 (by rfl) ⟨588194, by rfl⟩ : syracuseStep 784259 = 1176389) B1176389
theorem B1177475 : Blo 782338 1177475 := bstep (se 1 (by rfl) ⟨883106, by rfl⟩ : syracuseStep 1177475 = 1766213) B1766213
theorem B784275 : Blo 782338 784275 := bstep (se 1 (by rfl) ⟨588206, by rfl⟩ : syracuseStep 784275 = 1176413) B1176413
theorem B1177505 : Blo 782338 1177505 := bstep (se 2 (by rfl) ⟨441564, by rfl⟩ : syracuseStep 1177505 = 883129) B883129
theorem B784291 : Blo 782338 784291 := bstep (se 1 (by rfl) ⟨588218, by rfl⟩ : syracuseStep 784291 = 1176437) B1176437
theorem B784307 : Blo 782338 784307 := bstep (se 1 (by rfl) ⟨588230, by rfl⟩ : syracuseStep 784307 = 1176461) B1176461
theorem B1177523 : Blo 782338 1177523 := bstep (se 1 (by rfl) ⟨883142, by rfl⟩ : syracuseStep 1177523 = 1766285) B1766285
theorem B784323 : Blo 782338 784323 := bstep (se 1 (by rfl) ⟨588242, by rfl⟩ : syracuseStep 784323 = 1176485) B1176485
theorem B1177553 : Blo 782338 1177553 := bstep (se 2 (by rfl) ⟨441582, by rfl⟩ : syracuseStep 1177553 = 883165) B883165
theorem B784339 : Blo 782338 784339 := bstep (se 1 (by rfl) ⟨588254, by rfl⟩ : syracuseStep 784339 = 1176509) B1176509
theorem B882643 : Blo 782338 882643 := bstep (se 1 (by rfl) ⟨661982, by rfl⟩ : syracuseStep 882643 = 1323965) B1323965
theorem B784355 : Blo 782338 784355 := bstep (se 1 (by rfl) ⟨588266, by rfl⟩ : syracuseStep 784355 = 1176533) B1176533
theorem B1177571 : Blo 782338 1177571 := bstep (se 1 (by rfl) ⟨883178, by rfl⟩ : syracuseStep 1177571 = 1766357) B1766357
theorem B784371 : Blo 782338 784371 := bstep (se 1 (by rfl) ⟨588278, by rfl⟩ : syracuseStep 784371 = 1176557) B1176557
theorem B1177601 : Blo 782338 1177601 := bstep (se 2 (by rfl) ⟨441600, by rfl⟩ : syracuseStep 1177601 = 883201) B883201
theorem B784387 : Blo 782338 784387 := bstep (se 1 (by rfl) ⟨588290, by rfl⟩ : syracuseStep 784387 = 1176581) B1176581
theorem B784403 : Blo 782338 784403 := bstep (se 1 (by rfl) ⟨588302, by rfl⟩ : syracuseStep 784403 = 1176605) B1176605
theorem B1177619 : Blo 782338 1177619 := bstep (se 1 (by rfl) ⟨883214, by rfl⟩ : syracuseStep 1177619 = 1766429) B1766429
theorem B784419 : Blo 782338 784419 := bstep (se 1 (by rfl) ⟨588314, by rfl⟩ : syracuseStep 784419 = 1176629) B1176629
theorem B1177649 : Blo 782338 1177649 := bstep (se 2 (by rfl) ⟨441618, by rfl⟩ : syracuseStep 1177649 = 883237) B883237
theorem B1767473 : Blo 782338 1767473 := bstep (se 2 (by rfl) ⟨662802, by rfl⟩ : syracuseStep 1767473 = 1325605) B1325605
theorem B784435 : Blo 782338 784435 := bstep (se 1 (by rfl) ⟨588326, by rfl⟩ : syracuseStep 784435 = 1176653) B1176653
theorem B2652209 : Blo 782338 2652209 := bstep (se 2 (by rfl) ⟨994578, by rfl⟩ : syracuseStep 2652209 = 1989157) B1989157
theorem B784451 : Blo 782338 784451 := bstep (se 1 (by rfl) ⟨588338, by rfl⟩ : syracuseStep 784451 = 1176677) B1176677
theorem B1177667 : Blo 782338 1177667 := bstep (se 1 (by rfl) ⟨883250, by rfl⟩ : syracuseStep 1177667 = 1766501) B1766501
theorem B1767491 : Blo 782338 1767491 := bstep (se 1 (by rfl) ⟨1325618, by rfl⟩ : syracuseStep 1767491 = 2651237) B2651237
theorem B784467 : Blo 782338 784467 := bstep (se 1 (by rfl) ⟨588350, by rfl⟩ : syracuseStep 784467 = 1176701) B1176701
theorem B1177697 : Blo 782338 1177697 := bstep (se 2 (by rfl) ⟨441636, by rfl⟩ : syracuseStep 1177697 = 883273) B883273
theorem B784483 : Blo 782338 784483 := bstep (se 1 (by rfl) ⟨588362, by rfl⟩ : syracuseStep 784483 = 1176725) B1176725
theorem B882787 : Blo 782338 882787 := bstep (se 1 (by rfl) ⟨662090, by rfl⟩ : syracuseStep 882787 = 1324181) B1324181
theorem B784499 : Blo 782338 784499 := bstep (se 1 (by rfl) ⟨588374, by rfl⟩ : syracuseStep 784499 = 1176749) B1176749
theorem B1177715 : Blo 782338 1177715 := bstep (se 1 (by rfl) ⟨883286, by rfl⟩ : syracuseStep 1177715 = 1766573) B1766573
theorem B784515 : Blo 782338 784515 := bstep (se 1 (by rfl) ⟨588386, by rfl⟩ : syracuseStep 784515 = 1176773) B1176773
theorem B2685059 : Blo 782338 2685059 := bstep (se 1 (by rfl) ⟨2013794, by rfl⟩ : syracuseStep 2685059 = 4027589) B4027589
theorem B1177745 : Blo 782338 1177745 := bstep (se 2 (by rfl) ⟨441654, by rfl⟩ : syracuseStep 1177745 = 883309) B883309
theorem B784531 : Blo 782338 784531 := bstep (se 1 (by rfl) ⟨588398, by rfl⟩ : syracuseStep 784531 = 1176797) B1176797
theorem B784547 : Blo 782338 784547 := bstep (se 1 (by rfl) ⟨588410, by rfl⟩ : syracuseStep 784547 = 1176821) B1176821
theorem B1177763 : Blo 782338 1177763 := bstep (se 1 (by rfl) ⟨883322, by rfl⟩ : syracuseStep 1177763 = 1766645) B1766645
theorem B784563 : Blo 782338 784563 := bstep (se 1 (by rfl) ⟨588422, by rfl⟩ : syracuseStep 784563 = 1176845) B1176845
theorem B1177793 : Blo 782338 1177793 := bstep (se 2 (by rfl) ⟨441672, by rfl⟩ : syracuseStep 1177793 = 883345) B883345
theorem B784579 : Blo 782338 784579 := bstep (se 1 (by rfl) ⟨588434, by rfl⟩ : syracuseStep 784579 = 1176869) B1176869
theorem B784595 : Blo 782338 784595 := bstep (se 1 (by rfl) ⟨588446, by rfl⟩ : syracuseStep 784595 = 1176893) B1176893
theorem B1177811 : Blo 782338 1177811 := bstep (se 1 (by rfl) ⟨883358, by rfl⟩ : syracuseStep 1177811 = 1766717) B1766717
theorem B784611 : Blo 782338 784611 := bstep (se 1 (by rfl) ⟨588458, by rfl⟩ : syracuseStep 784611 = 1176917) B1176917
theorem B1177841 : Blo 782338 1177841 := bstep (se 2 (by rfl) ⟨441690, by rfl⟩ : syracuseStep 1177841 = 883381) B883381
theorem B784627 : Blo 782338 784627 := bstep (se 1 (by rfl) ⟨588470, by rfl⟩ : syracuseStep 784627 = 1176941) B1176941
theorem B882931 : Blo 782338 882931 := bstep (se 1 (by rfl) ⟨662198, by rfl⟩ : syracuseStep 882931 = 1324397) B1324397
theorem B784643 : Blo 782338 784643 := bstep (se 1 (by rfl) ⟨588482, by rfl⟩ : syracuseStep 784643 = 1176965) B1176965
theorem B1177859 : Blo 782338 1177859 := bstep (se 1 (by rfl) ⟨883394, by rfl⟩ : syracuseStep 1177859 = 1766789) B1766789
theorem B784659 : Blo 782338 784659 := bstep (se 1 (by rfl) ⟨588494, by rfl⟩ : syracuseStep 784659 = 1176989) B1176989
theorem B1177889 : Blo 782338 1177889 := bstep (se 2 (by rfl) ⟨441708, by rfl⟩ : syracuseStep 1177889 = 883417) B883417
theorem B784675 : Blo 782338 784675 := bstep (se 1 (by rfl) ⟨588506, by rfl⟩ : syracuseStep 784675 = 1177013) B1177013
theorem B2390317 : Blo 782338 2390317 := bstep (se 3 (by rfl) ⟨448184, by rfl⟩ : syracuseStep 2390317 = 896369) B896369
theorem B784691 : Blo 782338 784691 := bstep (se 1 (by rfl) ⟨588518, by rfl⟩ : syracuseStep 784691 = 1177037) B1177037
theorem B1177907 : Blo 782338 1177907 := bstep (se 1 (by rfl) ⟨883430, by rfl⟩ : syracuseStep 1177907 = 1766861) B1766861
theorem B784707 : Blo 782338 784707 := bstep (se 1 (by rfl) ⟨588530, by rfl⟩ : syracuseStep 784707 = 1177061) B1177061
theorem B1767761 : Blo 782338 1767761 := bstep (se 2 (by rfl) ⟨662910, by rfl⟩ : syracuseStep 1767761 = 1325821) B1325821
theorem B784723 : Blo 782338 784723 := bstep (se 1 (by rfl) ⟨588542, by rfl⟩ : syracuseStep 784723 = 1177085) B1177085
theorem B1177937 : Blo 782338 1177937 := bstep (se 2 (by rfl) ⟨441726, by rfl⟩ : syracuseStep 1177937 = 883453) B883453
theorem B784739 : Blo 782338 784739 := bstep (se 1 (by rfl) ⟨588554, by rfl⟩ : syracuseStep 784739 = 1177109) B1177109
theorem B1177955 : Blo 782338 1177955 := bstep (se 1 (by rfl) ⟨883466, by rfl⟩ : syracuseStep 1177955 = 1766933) B1766933
theorem B1767779 : Blo 782338 1767779 := bstep (se 1 (by rfl) ⟨1325834, by rfl⟩ : syracuseStep 1767779 = 2651669) B2651669
theorem B784755 : Blo 782338 784755 := bstep (se 1 (by rfl) ⟨588566, by rfl⟩ : syracuseStep 784755 = 1177133) B1177133
theorem B1177985 : Blo 782338 1177985 := bstep (se 2 (by rfl) ⟨441744, by rfl⟩ : syracuseStep 1177985 = 883489) B883489
theorem B784771 : Blo 782338 784771 := bstep (se 1 (by rfl) ⟨588578, by rfl⟩ : syracuseStep 784771 = 1177157) B1177157
theorem B883075 : Blo 782338 883075 := bstep (se 1 (by rfl) ⟨662306, by rfl⟩ : syracuseStep 883075 = 1324613) B1324613
theorem B784787 : Blo 782338 784787 := bstep (se 1 (by rfl) ⟨588590, by rfl⟩ : syracuseStep 784787 = 1177181) B1177181
theorem B1178003 : Blo 782338 1178003 := bstep (se 1 (by rfl) ⟨883502, by rfl⟩ : syracuseStep 1178003 = 1767005) B1767005
theorem B784803 : Blo 782338 784803 := bstep (se 1 (by rfl) ⟨588602, by rfl⟩ : syracuseStep 784803 = 1177205) B1177205
theorem B2980259 : Blo 782338 2980259 := bstep (se 1 (by rfl) ⟨2235194, by rfl⟩ : syracuseStep 2980259 = 4470389) B4470389
theorem B2980273 : Blo 782338 2980273 := bstep (se 2 (by rfl) ⟨1117602, by rfl⟩ : syracuseStep 2980273 = 2235205) B2235205
theorem B1178033 : Blo 782338 1178033 := bstep (se 2 (by rfl) ⟨441762, by rfl⟩ : syracuseStep 1178033 = 883525) B883525
theorem B784819 : Blo 782338 784819 := bstep (se 1 (by rfl) ⟨588614, by rfl⟩ : syracuseStep 784819 = 1177229) B1177229
theorem B784835 : Blo 782338 784835 := bstep (se 1 (by rfl) ⟨588626, by rfl⟩ : syracuseStep 784835 = 1177253) B1177253
theorem B1178051 : Blo 782338 1178051 := bstep (se 1 (by rfl) ⟨883538, by rfl⟩ : syracuseStep 1178051 = 1767077) B1767077
theorem B784851 : Blo 782338 784851 := bstep (se 1 (by rfl) ⟨588638, by rfl⟩ : syracuseStep 784851 = 1177277) B1177277
theorem B1178081 : Blo 782338 1178081 := bstep (se 2 (by rfl) ⟨441780, by rfl⟩ : syracuseStep 1178081 = 883561) B883561
theorem B784867 : Blo 782338 784867 := bstep (se 1 (by rfl) ⟨588650, by rfl⟩ : syracuseStep 784867 = 1177301) B1177301
theorem B784883 : Blo 782338 784883 := bstep (se 1 (by rfl) ⟨588662, by rfl⟩ : syracuseStep 784883 = 1177325) B1177325
theorem B1178099 : Blo 782338 1178099 := bstep (se 1 (by rfl) ⟨883574, by rfl⟩ : syracuseStep 1178099 = 1767149) B1767149
theorem B784899 : Blo 782338 784899 := bstep (se 1 (by rfl) ⟨588674, by rfl⟩ : syracuseStep 784899 = 1177349) B1177349
theorem B1178129 : Blo 782338 1178129 := bstep (se 2 (by rfl) ⟨441798, by rfl⟩ : syracuseStep 1178129 = 883597) B883597
theorem B784915 : Blo 782338 784915 := bstep (se 1 (by rfl) ⟨588686, by rfl⟩ : syracuseStep 784915 = 1177373) B1177373
theorem B883219 : Blo 782338 883219 := bstep (se 1 (by rfl) ⟨662414, by rfl⟩ : syracuseStep 883219 = 1324829) B1324829
theorem B784931 : Blo 782338 784931 := bstep (se 1 (by rfl) ⟨588698, by rfl⟩ : syracuseStep 784931 = 1177397) B1177397
theorem B1178147 : Blo 782338 1178147 := bstep (se 1 (by rfl) ⟨883610, by rfl⟩ : syracuseStep 1178147 = 1767221) B1767221
theorem B784947 : Blo 782338 784947 := bstep (se 1 (by rfl) ⟨588710, by rfl⟩ : syracuseStep 784947 = 1177421) B1177421
theorem B1178177 : Blo 782338 1178177 := bstep (se 2 (by rfl) ⟨441816, by rfl⟩ : syracuseStep 1178177 = 883633) B883633
theorem B784963 : Blo 782338 784963 := bstep (se 1 (by rfl) ⟨588722, by rfl⟩ : syracuseStep 784963 = 1177445) B1177445
theorem B2652749 : Blo 782338 2652749 := bstep (se 3 (by rfl) ⟨497390, by rfl⟩ : syracuseStep 2652749 = 994781) B994781
theorem B784979 : Blo 782338 784979 := bstep (se 1 (by rfl) ⟨588734, by rfl⟩ : syracuseStep 784979 = 1177469) B1177469
theorem B1178195 : Blo 782338 1178195 := bstep (se 1 (by rfl) ⟨883646, by rfl⟩ : syracuseStep 1178195 = 1767293) B1767293
theorem B3963491 : Blo 782338 3963491 := bstep (se 1 (by rfl) ⟨2972618, by rfl⟩ : syracuseStep 3963491 = 5945237) B5945237
theorem B784995 : Blo 782338 784995 := bstep (se 1 (by rfl) ⟨588746, by rfl⟩ : syracuseStep 784995 = 1177493) B1177493
theorem B1178225 : Blo 782338 1178225 := bstep (se 2 (by rfl) ⟨441834, by rfl⟩ : syracuseStep 1178225 = 883669) B883669
theorem B1768049 : Blo 782338 1768049 := bstep (se 2 (by rfl) ⟨663018, by rfl⟩ : syracuseStep 1768049 = 1326037) B1326037
theorem B785011 : Blo 782338 785011 := bstep (se 1 (by rfl) ⟨588758, by rfl⟩ : syracuseStep 785011 = 1177517) B1177517
theorem B785027 : Blo 782338 785027 := bstep (se 1 (by rfl) ⟨588770, by rfl⟩ : syracuseStep 785027 = 1177541) B1177541
theorem B1178243 : Blo 782338 1178243 := bstep (se 1 (by rfl) ⟨883682, by rfl⟩ : syracuseStep 1178243 = 1767365) B1767365
theorem B1768067 : Blo 782338 1768067 := bstep (se 1 (by rfl) ⟨1326050, by rfl⟩ : syracuseStep 1768067 = 2652101) B2652101
theorem B2652803 : Blo 782338 2652803 := bstep (se 1 (by rfl) ⟨1989602, by rfl⟩ : syracuseStep 2652803 = 3979205) B3979205
theorem B4291213 : Blo 782338 4291213 := bstep (se 3 (by rfl) ⟨804602, by rfl⟩ : syracuseStep 4291213 = 1609205) B1609205
theorem B785043 : Blo 782338 785043 := bstep (se 1 (by rfl) ⟨588782, by rfl⟩ : syracuseStep 785043 = 1177565) B1177565
theorem B1178273 : Blo 782338 1178273 := bstep (se 2 (by rfl) ⟨441852, by rfl⟩ : syracuseStep 1178273 = 883705) B883705
theorem B785059 : Blo 782338 785059 := bstep (se 1 (by rfl) ⟨588794, by rfl⟩ : syracuseStep 785059 = 1177589) B1177589
theorem B883363 : Blo 782338 883363 := bstep (se 1 (by rfl) ⟨662522, by rfl⟩ : syracuseStep 883363 = 1325045) B1325045
theorem B785075 : Blo 782338 785075 := bstep (se 1 (by rfl) ⟨588806, by rfl⟩ : syracuseStep 785075 = 1177613) B1177613
theorem B1178291 : Blo 782338 1178291 := bstep (se 1 (by rfl) ⟨883718, by rfl⟩ : syracuseStep 1178291 = 1767437) B1767437
theorem B785091 : Blo 782338 785091 := bstep (se 1 (by rfl) ⟨588818, by rfl⟩ : syracuseStep 785091 = 1177637) B1177637
theorem B1178321 : Blo 782338 1178321 := bstep (se 2 (by rfl) ⟨441870, by rfl⟩ : syracuseStep 1178321 = 883741) B883741
theorem B785107 : Blo 782338 785107 := bstep (se 1 (by rfl) ⟨588830, by rfl⟩ : syracuseStep 785107 = 1177661) B1177661
theorem B785123 : Blo 782338 785123 := bstep (se 1 (by rfl) ⟨588842, by rfl⟩ : syracuseStep 785123 = 1177685) B1177685
theorem B1178339 : Blo 782338 1178339 := bstep (se 1 (by rfl) ⟨883754, by rfl⟩ : syracuseStep 1178339 = 1767509) B1767509
theorem B785139 : Blo 782338 785139 := bstep (se 1 (by rfl) ⟨588854, by rfl⟩ : syracuseStep 785139 = 1177709) B1177709
theorem B1178369 : Blo 782338 1178369 := bstep (se 2 (by rfl) ⟨441888, by rfl⟩ : syracuseStep 1178369 = 883777) B883777
theorem B785155 : Blo 782338 785155 := bstep (se 1 (by rfl) ⟨588866, by rfl⟩ : syracuseStep 785155 = 1177733) B1177733
theorem B785171 : Blo 782338 785171 := bstep (se 1 (by rfl) ⟨588878, by rfl⟩ : syracuseStep 785171 = 1177757) B1177757
theorem B1178387 : Blo 782338 1178387 := bstep (se 1 (by rfl) ⟨883790, by rfl⟩ : syracuseStep 1178387 = 1767581) B1767581
theorem B785187 : Blo 782338 785187 := bstep (se 1 (by rfl) ⟨588890, by rfl⟩ : syracuseStep 785187 = 1177781) B1177781
theorem B1178417 : Blo 782338 1178417 := bstep (se 2 (by rfl) ⟨441906, by rfl⟩ : syracuseStep 1178417 = 883813) B883813
theorem B785203 : Blo 782338 785203 := bstep (se 1 (by rfl) ⟨588902, by rfl⟩ : syracuseStep 785203 = 1177805) B1177805
theorem B883507 : Blo 782338 883507 := bstep (se 1 (by rfl) ⟨662630, by rfl⟩ : syracuseStep 883507 = 1325261) B1325261
theorem B785219 : Blo 782338 785219 := bstep (se 1 (by rfl) ⟨588914, by rfl⟩ : syracuseStep 785219 = 1177829) B1177829
theorem B1178435 : Blo 782338 1178435 := bstep (se 1 (by rfl) ⟨883826, by rfl⟩ : syracuseStep 1178435 = 1767653) B1767653
theorem B5438285 : Blo 782338 5438285 := bstep (se 3 (by rfl) ⟨1019678, by rfl⟩ : syracuseStep 5438285 = 2039357) B2039357
theorem B785235 : Blo 782338 785235 := bstep (se 1 (by rfl) ⟨588926, by rfl⟩ : syracuseStep 785235 = 1177853) B1177853
theorem B1178465 : Blo 782338 1178465 := bstep (se 2 (by rfl) ⟨441924, by rfl⟩ : syracuseStep 1178465 = 883849) B883849
theorem B785251 : Blo 782338 785251 := bstep (se 1 (by rfl) ⟨588938, by rfl⟩ : syracuseStep 785251 = 1177877) B1177877
theorem B785267 : Blo 782338 785267 := bstep (se 1 (by rfl) ⟨588950, by rfl⟩ : syracuseStep 785267 = 1177901) B1177901
theorem B1178483 : Blo 782338 1178483 := bstep (se 1 (by rfl) ⟨883862, by rfl⟩ : syracuseStep 1178483 = 1767725) B1767725
theorem B785283 : Blo 782338 785283 := bstep (se 1 (by rfl) ⟨588962, by rfl⟩ : syracuseStep 785283 = 1177925) B1177925
theorem B1178513 : Blo 782338 1178513 := bstep (se 2 (by rfl) ⟨441942, by rfl⟩ : syracuseStep 1178513 = 883885) B883885
theorem B1768337 : Blo 782338 1768337 := bstep (se 2 (by rfl) ⟨663126, by rfl⟩ : syracuseStep 1768337 = 1326253) B1326253
theorem B785299 : Blo 782338 785299 := bstep (se 1 (by rfl) ⟨588974, by rfl⟩ : syracuseStep 785299 = 1177949) B1177949
theorem B2653073 : Blo 782338 2653073 := bstep (se 2 (by rfl) ⟨994902, by rfl⟩ : syracuseStep 2653073 = 1989805) B1989805
theorem B785315 : Blo 782338 785315 := bstep (se 1 (by rfl) ⟨588986, by rfl⟩ : syracuseStep 785315 = 1177973) B1177973
theorem B1178531 : Blo 782338 1178531 := bstep (se 1 (by rfl) ⟨883898, by rfl⟩ : syracuseStep 1178531 = 1767797) B1767797
theorem B1768355 : Blo 782338 1768355 := bstep (se 1 (by rfl) ⟨1326266, by rfl⟩ : syracuseStep 1768355 = 2652533) B2652533
theorem B785331 : Blo 782338 785331 := bstep (se 1 (by rfl) ⟨588998, by rfl⟩ : syracuseStep 785331 = 1177997) B1177997
theorem B1178561 : Blo 782338 1178561 := bstep (se 2 (by rfl) ⟨441960, by rfl⟩ : syracuseStep 1178561 = 883921) B883921
theorem B785347 : Blo 782338 785347 := bstep (se 1 (by rfl) ⟨589010, by rfl⟩ : syracuseStep 785347 = 1178021) B1178021
theorem B883651 : Blo 782338 883651 := bstep (se 1 (by rfl) ⟨662738, by rfl⟩ : syracuseStep 883651 = 1325477) B1325477
theorem B785363 : Blo 782338 785363 := bstep (se 1 (by rfl) ⟨589022, by rfl⟩ : syracuseStep 785363 = 1178045) B1178045
theorem B1178579 : Blo 782338 1178579 := bstep (se 1 (by rfl) ⟨883934, by rfl⟩ : syracuseStep 1178579 = 1767869) B1767869
theorem B785379 : Blo 782338 785379 := bstep (se 1 (by rfl) ⟨589034, by rfl⟩ : syracuseStep 785379 = 1178069) B1178069
theorem B1178609 : Blo 782338 1178609 := bstep (se 2 (by rfl) ⟨441978, by rfl⟩ : syracuseStep 1178609 = 883957) B883957
theorem B785395 : Blo 782338 785395 := bstep (se 1 (by rfl) ⟨589046, by rfl⟩ : syracuseStep 785395 = 1178093) B1178093
theorem B785411 : Blo 782338 785411 := bstep (se 1 (by rfl) ⟨589058, by rfl⟩ : syracuseStep 785411 = 1178117) B1178117
theorem B1178627 : Blo 782338 1178627 := bstep (se 1 (by rfl) ⟨883970, by rfl⟩ : syracuseStep 1178627 = 1767941) B1767941
theorem B785427 : Blo 782338 785427 := bstep (se 1 (by rfl) ⟨589070, by rfl⟩ : syracuseStep 785427 = 1178141) B1178141
theorem B1178657 : Blo 782338 1178657 := bstep (se 2 (by rfl) ⟨441996, by rfl⟩ : syracuseStep 1178657 = 883993) B883993
theorem B785443 : Blo 782338 785443 := bstep (se 1 (by rfl) ⟨589082, by rfl⟩ : syracuseStep 785443 = 1178165) B1178165
theorem B785459 : Blo 782338 785459 := bstep (se 1 (by rfl) ⟨589094, by rfl⟩ : syracuseStep 785459 = 1178189) B1178189
theorem B1178675 : Blo 782338 1178675 := bstep (se 1 (by rfl) ⟨884006, by rfl⟩ : syracuseStep 1178675 = 1768013) B1768013
theorem B785475 : Blo 782338 785475 := bstep (se 1 (by rfl) ⟨589106, by rfl⟩ : syracuseStep 785475 = 1178213) B1178213
theorem B1178705 : Blo 782338 1178705 := bstep (se 2 (by rfl) ⟨442014, by rfl⟩ : syracuseStep 1178705 = 884029) B884029
theorem B785491 : Blo 782338 785491 := bstep (se 1 (by rfl) ⟨589118, by rfl⟩ : syracuseStep 785491 = 1178237) B1178237
theorem B883795 : Blo 782338 883795 := bstep (se 1 (by rfl) ⟨662846, by rfl⟩ : syracuseStep 883795 = 1325693) B1325693
theorem B785507 : Blo 782338 785507 := bstep (se 1 (by rfl) ⟨589130, by rfl⟩ : syracuseStep 785507 = 1178261) B1178261
theorem B1178723 : Blo 782338 1178723 := bstep (se 1 (by rfl) ⟨884042, by rfl⟩ : syracuseStep 1178723 = 1768085) B1768085
theorem B785523 : Blo 782338 785523 := bstep (se 1 (by rfl) ⟨589142, by rfl⟩ : syracuseStep 785523 = 1178285) B1178285
theorem B1178753 : Blo 782338 1178753 := bstep (se 2 (by rfl) ⟨442032, by rfl⟩ : syracuseStep 1178753 = 884065) B884065
theorem B785539 : Blo 782338 785539 := bstep (se 1 (by rfl) ⟨589154, by rfl⟩ : syracuseStep 785539 = 1178309) B1178309
theorem B785555 : Blo 782338 785555 := bstep (se 1 (by rfl) ⟨589166, by rfl⟩ : syracuseStep 785555 = 1178333) B1178333
theorem B1178771 : Blo 782338 1178771 := bstep (se 1 (by rfl) ⟨884078, by rfl⟩ : syracuseStep 1178771 = 1768157) B1768157
theorem B785571 : Blo 782338 785571 := bstep (se 1 (by rfl) ⟨589178, by rfl⟩ : syracuseStep 785571 = 1178357) B1178357
theorem B1178801 : Blo 782338 1178801 := bstep (se 2 (by rfl) ⟨442050, by rfl⟩ : syracuseStep 1178801 = 884101) B884101
theorem B1768625 : Blo 782338 1768625 := bstep (se 2 (by rfl) ⟨663234, by rfl⟩ : syracuseStep 1768625 = 1326469) B1326469
theorem B785587 : Blo 782338 785587 := bstep (se 1 (by rfl) ⟨589190, by rfl⟩ : syracuseStep 785587 = 1178381) B1178381
theorem B785603 : Blo 782338 785603 := bstep (se 1 (by rfl) ⟨589202, by rfl⟩ : syracuseStep 785603 = 1178405) B1178405
theorem B1178819 : Blo 782338 1178819 := bstep (se 1 (by rfl) ⟨884114, by rfl⟩ : syracuseStep 1178819 = 1768229) B1768229
theorem B1768643 : Blo 782338 1768643 := bstep (se 1 (by rfl) ⟨1326482, by rfl⟩ : syracuseStep 1768643 = 2652965) B2652965
theorem B785619 : Blo 782338 785619 := bstep (se 1 (by rfl) ⟨589214, by rfl⟩ : syracuseStep 785619 = 1178429) B1178429
theorem B1178849 : Blo 782338 1178849 := bstep (se 2 (by rfl) ⟨442068, by rfl⟩ : syracuseStep 1178849 = 884137) B884137
theorem B785635 : Blo 782338 785635 := bstep (se 1 (by rfl) ⟨589226, by rfl⟩ : syracuseStep 785635 = 1178453) B1178453
theorem B883939 : Blo 782338 883939 := bstep (se 1 (by rfl) ⟨662954, by rfl⟩ : syracuseStep 883939 = 1325909) B1325909
theorem B785651 : Blo 782338 785651 := bstep (se 1 (by rfl) ⟨589238, by rfl⟩ : syracuseStep 785651 = 1178477) B1178477
theorem B1178867 : Blo 782338 1178867 := bstep (se 1 (by rfl) ⟨884150, by rfl⟩ : syracuseStep 1178867 = 1768301) B1768301
theorem B785667 : Blo 782338 785667 := bstep (se 1 (by rfl) ⟨589250, by rfl⟩ : syracuseStep 785667 = 1178501) B1178501
theorem B1178897 : Blo 782338 1178897 := bstep (se 2 (by rfl) ⟨442086, by rfl⟩ : syracuseStep 1178897 = 884173) B884173
theorem B1375507 : Blo 782338 1375507 := bstep (se 1 (by rfl) ⟨1031630, by rfl⟩ : syracuseStep 1375507 = 2063261) B2063261
theorem B785683 : Blo 782338 785683 := bstep (se 1 (by rfl) ⟨589262, by rfl⟩ : syracuseStep 785683 = 1178525) B1178525
theorem B785699 : Blo 782338 785699 := bstep (se 1 (by rfl) ⟨589274, by rfl⟩ : syracuseStep 785699 = 1178549) B1178549
theorem B1178915 : Blo 782338 1178915 := bstep (se 1 (by rfl) ⟨884186, by rfl⟩ : syracuseStep 1178915 = 1768373) B1768373
theorem B785715 : Blo 782338 785715 := bstep (se 1 (by rfl) ⟨589286, by rfl⟩ : syracuseStep 785715 = 1178573) B1178573
theorem B1178945 : Blo 782338 1178945 := bstep (se 2 (by rfl) ⟨442104, by rfl⟩ : syracuseStep 1178945 = 884209) B884209
theorem B785731 : Blo 782338 785731 := bstep (se 1 (by rfl) ⟨589298, by rfl⟩ : syracuseStep 785731 = 1178597) B1178597
theorem B785747 : Blo 782338 785747 := bstep (se 1 (by rfl) ⟨589310, by rfl⟩ : syracuseStep 785747 = 1178621) B1178621
theorem B1178963 : Blo 782338 1178963 := bstep (se 1 (by rfl) ⟨884222, by rfl⟩ : syracuseStep 1178963 = 1768445) B1768445
theorem B785763 : Blo 782338 785763 := bstep (se 1 (by rfl) ⟨589322, by rfl⟩ : syracuseStep 785763 = 1178645) B1178645
theorem B1178993 : Blo 782338 1178993 := bstep (se 2 (by rfl) ⟨442122, by rfl⟩ : syracuseStep 1178993 = 884245) B884245
theorem B785779 : Blo 782338 785779 := bstep (se 1 (by rfl) ⟨589334, by rfl⟩ : syracuseStep 785779 = 1178669) B1178669
theorem B884083 : Blo 782338 884083 := bstep (se 1 (by rfl) ⟨663062, by rfl⟩ : syracuseStep 884083 = 1326125) B1326125
theorem B785795 : Blo 782338 785795 := bstep (se 1 (by rfl) ⟨589346, by rfl⟩ : syracuseStep 785795 = 1178693) B1178693
theorem B1179011 : Blo 782338 1179011 := bstep (se 1 (by rfl) ⟨884258, by rfl⟩ : syracuseStep 1179011 = 1768517) B1768517
theorem B3964301 : Blo 782338 3964301 := bstep (se 3 (by rfl) ⟨743306, by rfl⟩ : syracuseStep 3964301 = 1486613) B1486613
theorem B785811 : Blo 782338 785811 := bstep (se 1 (by rfl) ⟨589358, by rfl⟩ : syracuseStep 785811 = 1178717) B1178717
theorem B1179041 : Blo 782338 1179041 := bstep (se 2 (by rfl) ⟨442140, by rfl⟩ : syracuseStep 1179041 = 884281) B884281
theorem B785827 : Blo 782338 785827 := bstep (se 1 (by rfl) ⟨589370, by rfl⟩ : syracuseStep 785827 = 1178741) B1178741
theorem B2653613 : Blo 782338 2653613 := bstep (se 3 (by rfl) ⟨497552, by rfl⟩ : syracuseStep 2653613 = 995105) B995105
theorem B785843 : Blo 782338 785843 := bstep (se 1 (by rfl) ⟨589382, by rfl⟩ : syracuseStep 785843 = 1178765) B1178765
theorem B1179059 : Blo 782338 1179059 := bstep (se 1 (by rfl) ⟨884294, by rfl⟩ : syracuseStep 1179059 = 1768589) B1768589
theorem B785859 : Blo 782338 785859 := bstep (se 1 (by rfl) ⟨589394, by rfl⟩ : syracuseStep 785859 = 1178789) B1178789
theorem B1179089 : Blo 782338 1179089 := bstep (se 2 (by rfl) ⟨442158, by rfl⟩ : syracuseStep 1179089 = 884317) B884317
theorem B1768913 : Blo 782338 1768913 := bstep (se 2 (by rfl) ⟨663342, by rfl⟩ : syracuseStep 1768913 = 1326685) B1326685
theorem B785875 : Blo 782338 785875 := bstep (se 1 (by rfl) ⟨589406, by rfl⟩ : syracuseStep 785875 = 1178813) B1178813
theorem B785891 : Blo 782338 785891 := bstep (se 1 (by rfl) ⟨589418, by rfl⟩ : syracuseStep 785891 = 1178837) B1178837
theorem B1179107 : Blo 782338 1179107 := bstep (se 1 (by rfl) ⟨884330, by rfl⟩ : syracuseStep 1179107 = 1768661) B1768661
theorem B1768931 : Blo 782338 1768931 := bstep (se 1 (by rfl) ⟨1326698, by rfl⟩ : syracuseStep 1768931 = 2653397) B2653397
theorem B2653667 : Blo 782338 2653667 := bstep (se 1 (by rfl) ⟨1990250, by rfl⟩ : syracuseStep 2653667 = 3980501) B3980501
theorem B785907 : Blo 782338 785907 := bstep (se 1 (by rfl) ⟨589430, by rfl⟩ : syracuseStep 785907 = 1178861) B1178861
theorem B1179137 : Blo 782338 1179137 := bstep (se 2 (by rfl) ⟨442176, by rfl⟩ : syracuseStep 1179137 = 884353) B884353
theorem B785923 : Blo 782338 785923 := bstep (se 1 (by rfl) ⟨589442, by rfl⟩ : syracuseStep 785923 = 1178885) B1178885
theorem B884227 : Blo 782338 884227 := bstep (se 1 (by rfl) ⟨663170, by rfl⟩ : syracuseStep 884227 = 1326341) B1326341
theorem B785939 : Blo 782338 785939 := bstep (se 1 (by rfl) ⟨589454, by rfl⟩ : syracuseStep 785939 = 1178909) B1178909
theorem B1179155 : Blo 782338 1179155 := bstep (se 1 (by rfl) ⟨884366, by rfl⟩ : syracuseStep 1179155 = 1768733) B1768733
theorem B785955 : Blo 782338 785955 := bstep (se 1 (by rfl) ⟨589466, by rfl⟩ : syracuseStep 785955 = 1178933) B1178933
theorem B3341873 : Blo 782338 3341873 := bstep (se 2 (by rfl) ⟨1253202, by rfl⟩ : syracuseStep 3341873 = 2506405) B2506405
theorem B1179185 : Blo 782338 1179185 := bstep (se 2 (by rfl) ⟨442194, by rfl⟩ : syracuseStep 1179185 = 884389) B884389
theorem B785971 : Blo 782338 785971 := bstep (se 1 (by rfl) ⟨589478, by rfl⟩ : syracuseStep 785971 = 1178957) B1178957
theorem B785987 : Blo 782338 785987 := bstep (se 1 (by rfl) ⟨589490, by rfl⟩ : syracuseStep 785987 = 1178981) B1178981
theorem B1179203 : Blo 782338 1179203 := bstep (se 1 (by rfl) ⟨884402, by rfl⟩ : syracuseStep 1179203 = 1768805) B1768805
theorem B786003 : Blo 782338 786003 := bstep (se 1 (by rfl) ⟨589502, by rfl⟩ : syracuseStep 786003 = 1179005) B1179005
theorem B1179233 : Blo 782338 1179233 := bstep (se 2 (by rfl) ⟨442212, by rfl⟩ : syracuseStep 1179233 = 884425) B884425
theorem B786019 : Blo 782338 786019 := bstep (se 1 (by rfl) ⟨589514, by rfl⟩ : syracuseStep 786019 = 1179029) B1179029
theorem B786035 : Blo 782338 786035 := bstep (se 1 (by rfl) ⟨589526, by rfl⟩ : syracuseStep 786035 = 1179053) B1179053
theorem B1179251 : Blo 782338 1179251 := bstep (se 1 (by rfl) ⟨884438, by rfl⟩ : syracuseStep 1179251 = 1768877) B1768877
theorem B786051 : Blo 782338 786051 := bstep (se 1 (by rfl) ⟨589538, by rfl⟩ : syracuseStep 786051 = 1179077) B1179077
theorem B1179281 : Blo 782338 1179281 := bstep (se 2 (by rfl) ⟨442230, by rfl⟩ : syracuseStep 1179281 = 884461) B884461
theorem B786067 : Blo 782338 786067 := bstep (se 1 (by rfl) ⟨589550, by rfl⟩ : syracuseStep 786067 = 1179101) B1179101
theorem B884371 : Blo 782338 884371 := bstep (se 1 (by rfl) ⟨663278, by rfl⟩ : syracuseStep 884371 = 1326557) B1326557
theorem B786083 : Blo 782338 786083 := bstep (se 1 (by rfl) ⟨589562, by rfl⟩ : syracuseStep 786083 = 1179125) B1179125
theorem B1179299 : Blo 782338 1179299 := bstep (se 1 (by rfl) ⟨884474, by rfl⟩ : syracuseStep 1179299 = 1768949) B1768949
theorem B786099 : Blo 782338 786099 := bstep (se 1 (by rfl) ⟨589574, by rfl⟩ : syracuseStep 786099 = 1179149) B1179149
theorem B1179329 : Blo 782338 1179329 := bstep (se 2 (by rfl) ⟨442248, by rfl⟩ : syracuseStep 1179329 = 884497) B884497
theorem B786115 : Blo 782338 786115 := bstep (se 1 (by rfl) ⟨589586, by rfl⟩ : syracuseStep 786115 = 1179173) B1179173
theorem B5013197 : Blo 782338 5013197 := bstep (se 3 (by rfl) ⟨939974, by rfl⟩ : syracuseStep 5013197 = 1879949) B1879949
theorem B786131 : Blo 782338 786131 := bstep (se 1 (by rfl) ⟨589598, by rfl⟩ : syracuseStep 786131 = 1179197) B1179197
theorem B1179347 : Blo 782338 1179347 := bstep (se 1 (by rfl) ⟨884510, by rfl⟩ : syracuseStep 1179347 = 1769021) B1769021
theorem B786147 : Blo 782338 786147 := bstep (se 1 (by rfl) ⟨589610, by rfl⟩ : syracuseStep 786147 = 1179221) B1179221
theorem B1179377 : Blo 782338 1179377 := bstep (se 2 (by rfl) ⟨442266, by rfl⟩ : syracuseStep 1179377 = 884533) B884533
theorem B1769201 : Blo 782338 1769201 := bstep (se 2 (by rfl) ⟨663450, by rfl⟩ : syracuseStep 1769201 = 1326901) B1326901
theorem B786163 : Blo 782338 786163 := bstep (se 1 (by rfl) ⟨589622, by rfl⟩ : syracuseStep 786163 = 1179245) B1179245
theorem B786179 : Blo 782338 786179 := bstep (se 1 (by rfl) ⟨589634, by rfl⟩ : syracuseStep 786179 = 1179269) B1179269
theorem B1179395 : Blo 782338 1179395 := bstep (se 1 (by rfl) ⟨884546, by rfl⟩ : syracuseStep 1179395 = 1769093) B1769093
theorem B1769219 : Blo 782338 1769219 := bstep (se 1 (by rfl) ⟨1326914, by rfl⟩ : syracuseStep 1769219 = 2653829) B2653829
theorem B786195 : Blo 782338 786195 := bstep (se 1 (by rfl) ⟨589646, by rfl⟩ : syracuseStep 786195 = 1179293) B1179293
theorem B1179425 : Blo 782338 1179425 := bstep (se 2 (by rfl) ⟨442284, by rfl⟩ : syracuseStep 1179425 = 884569) B884569
theorem B786211 : Blo 782338 786211 := bstep (se 1 (by rfl) ⟨589658, by rfl⟩ : syracuseStep 786211 = 1179317) B1179317
theorem B884515 : Blo 782338 884515 := bstep (se 1 (by rfl) ⟨663386, by rfl⟩ : syracuseStep 884515 = 1326773) B1326773
theorem B4456241 : Blo 782338 4456241 := bstep (se 2 (by rfl) ⟨1671090, by rfl⟩ : syracuseStep 4456241 = 3342181) B3342181
theorem B786227 : Blo 782338 786227 := bstep (se 1 (by rfl) ⟨589670, by rfl⟩ : syracuseStep 786227 = 1179341) B1179341
theorem B1179443 : Blo 782338 1179443 := bstep (se 1 (by rfl) ⟨884582, by rfl⟩ : syracuseStep 1179443 = 1769165) B1769165
theorem B786243 : Blo 782338 786243 := bstep (se 1 (by rfl) ⟨589682, by rfl⟩ : syracuseStep 786243 = 1179365) B1179365
theorem B1179473 : Blo 782338 1179473 := bstep (se 2 (by rfl) ⟨442302, by rfl⟩ : syracuseStep 1179473 = 884605) B884605
theorem B786259 : Blo 782338 786259 := bstep (se 1 (by rfl) ⟨589694, by rfl⟩ : syracuseStep 786259 = 1179389) B1179389
theorem B2981731 : Blo 782338 2981731 := bstep (se 1 (by rfl) ⟨2236298, by rfl⟩ : syracuseStep 2981731 = 4472597) B4472597
theorem B786275 : Blo 782338 786275 := bstep (se 1 (by rfl) ⟨589706, by rfl⟩ : syracuseStep 786275 = 1179413) B1179413
theorem B1179491 : Blo 782338 1179491 := bstep (se 1 (by rfl) ⟨884618, by rfl⟩ : syracuseStep 1179491 = 1769237) B1769237
theorem B8912753 : Blo 782338 8912753 := bstep (se 2 (by rfl) ⟨3342282, by rfl⟩ : syracuseStep 8912753 = 6684565) B6684565
theorem B786291 : Blo 782338 786291 := bstep (se 1 (by rfl) ⟨589718, by rfl⟩ : syracuseStep 786291 = 1179437) B1179437
theorem B786307 : Blo 782338 786307 := bstep (se 1 (by rfl) ⟨589730, by rfl⟩ : syracuseStep 786307 = 1179461) B1179461
theorem B1114003 : Blo 782338 1114003 := bstep (se 1 (by rfl) ⟨835502, by rfl⟩ : syracuseStep 1114003 = 1671005) B1671005
theorem B786323 : Blo 782338 786323 := bstep (se 1 (by rfl) ⟨589742, by rfl⟩ : syracuseStep 786323 = 1179485) B1179485
theorem B1343459 : Blo 782338 1343459 := bstep (se 1 (by rfl) ⟨1007594, by rfl⟩ : syracuseStep 1343459 = 2015189) B2015189
theorem B10715267 : Blo 782338 10715267 := bstep (se 1 (by rfl) ⟨8036450, by rfl⟩ : syracuseStep 10715267 = 16072901) B16072901
theorem B5013683 : Blo 782338 5013683 := bstep (se 1 (by rfl) ⟨3760262, by rfl⟩ : syracuseStep 5013683 = 7520525) B7520525
theorem B1671347 : Blo 782338 1671347 := bstep (se 1 (by rfl) ⟨1253510, by rfl⟩ : syracuseStep 1671347 = 2507021) B2507021
theorem B2228417 : Blo 782338 2228417 := bstep (se 2 (by rfl) ⟨835656, by rfl⟩ : syracuseStep 2228417 = 1671313) B1671313
theorem B17170805 : Blo 782338 17170805 := bstep (se 5 (by rfl) ⟨804881, by rfl⟩ : syracuseStep 17170805 = 1609763) B1609763
theorem B2228759 : Blo 782338 2228759 := bstep (se 1 (by rfl) ⟨1671569, by rfl⟩ : syracuseStep 2228759 = 3343139) B3343139
theorem B2982977 : Blo 782338 2982977 := bstep (se 2 (by rfl) ⟨1118616, by rfl⟩ : syracuseStep 2982977 = 2237233) B2237233
theorem B1672321 : Blo 782338 1672321 := bstep (se 2 (by rfl) ⟨627120, by rfl⟩ : syracuseStep 1672321 = 1254241) B1254241
theorem B3966083 : Blo 782338 3966083 := bstep (se 1 (by rfl) ⟨2974562, by rfl⟩ : syracuseStep 3966083 = 5949125) B5949125
theorem B6685901 : Blo 782338 6685901 := bstep (se 3 (by rfl) ⟨1253606, by rfl⟩ : syracuseStep 6685901 = 2507213) B2507213
theorem B1672577 : Blo 782338 1672577 := bstep (se 2 (by rfl) ⟨627216, by rfl⟩ : syracuseStep 1672577 = 1254433) B1254433
theorem B1672663 : Blo 782338 1672663 := bstep (se 1 (by rfl) ⟨1254497, by rfl⟩ : syracuseStep 1672663 = 2508995) B2508995
theorem B12748357 : Blo 782338 12748357 := bstep (se 4 (by rfl) ⟨1195158, by rfl⟩ : syracuseStep 12748357 = 2390317) B2390317
theorem B40699523 : Blo 782338 40699523 := bstep (se 1 (by rfl) ⟨30524642, by rfl⟩ : syracuseStep 40699523 = 61049285) B61049285
theorem B4523651 : Blo 782338 4523651 := bstep (se 1 (by rfl) ⟨3392738, by rfl⟩ : syracuseStep 4523651 = 6785477) B6785477
theorem B18351937 : Blo 782338 18351937 := bstep (se 2 (by rfl) ⟨6881976, by rfl⟩ : syracuseStep 18351937 = 13763953) B13763953
theorem B3344813 : Blo 782338 3344813 := bstep (se 3 (by rfl) ⟨627152, by rfl⟩ : syracuseStep 3344813 = 1254305) B1254305
theorem B2984465 : Blo 782338 2984465 := bstep (se 2 (by rfl) ⟨1119174, by rfl⟩ : syracuseStep 2984465 = 2238349) B2238349
theorem B2230877 : Blo 782338 2230877 := bstep (se 3 (by rfl) ⟨418289, by rfl⟩ : syracuseStep 2230877 = 836579) B836579
theorem B1116823 : Blo 782338 1116823 := bstep (se 1 (by rfl) ⟨837617, by rfl⟩ : syracuseStep 1116823 = 1675235) B1675235
theorem B2231219 : Blo 782338 2231219 := bstep (se 1 (by rfl) ⟨1673414, by rfl⟩ : syracuseStep 2231219 = 3346829) B3346829
theorem B2984921 : Blo 782338 2984921 := bstep (se 2 (by rfl) ⟨1119345, by rfl⟩ : syracuseStep 2984921 = 2238691) B2238691
theorem B2985133 : Blo 782338 2985133 := bstep (se 3 (by rfl) ⟨559712, by rfl⟩ : syracuseStep 2985133 = 1119425) B1119425
theorem B3182017 : Blo 782338 3182017 := bstep (se 2 (by rfl) ⟨1193256, by rfl⟩ : syracuseStep 3182017 = 2386513) B2386513
theorem B2985437 : Blo 782338 2985437 := bstep (se 3 (by rfl) ⟨559769, by rfl⟩ : syracuseStep 2985437 = 1119539) B1119539
theorem B4460183 : Blo 782338 4460183 := bstep (se 1 (by rfl) ⟨3345137, by rfl⟩ : syracuseStep 4460183 = 6690275) B6690275
theorem B1412939 : Blo 782338 1412939 := bstep (se 1 (by rfl) ⟨1059704, by rfl⟩ : syracuseStep 1412939 = 2119409) B2119409
theorem B10030949 : Blo 782338 10030949 := bstep (se 4 (by rfl) ⟨940401, by rfl⟩ : syracuseStep 10030949 = 1880803) B1880803
theorem B1675379 : Blo 782338 1675379 := bstep (se 1 (by rfl) ⟨1256534, by rfl⟩ : syracuseStep 1675379 = 2513069) B2513069
theorem B1511639 : Blo 782338 1511639 := bstep (se 1 (by rfl) ⟨1133729, by rfl⟩ : syracuseStep 1511639 = 2267459) B2267459
theorem B2756915 : Blo 782338 2756915 := bstep (se 1 (by rfl) ⟨2067686, by rfl⟩ : syracuseStep 2756915 = 4135373) B4135373
theorem B5378653 : Blo 782338 5378653 := bstep (se 3 (by rfl) ⟨1008497, by rfl⟩ : syracuseStep 5378653 = 2016995) B2016995
theorem B1118873 : Blo 782338 1118873 := bstep (se 2 (by rfl) ⟨419577, by rfl⟩ : syracuseStep 1118873 = 839155) B839155
theorem B3969809 : Blo 782338 3969809 := bstep (se 2 (by rfl) ⟨1488678, by rfl⟩ : syracuseStep 3969809 = 2977357) B2977357
theorem B3969971 : Blo 782338 3969971 := bstep (se 1 (by rfl) ⟨2977478, by rfl⟩ : syracuseStep 3969971 = 5954957) B5954957
theorem B4232153 : Blo 782338 4232153 := bstep (se 2 (by rfl) ⟨1587057, by rfl⟩ : syracuseStep 4232153 = 3174115) B3174115
theorem B5805017 : Blo 782338 5805017 := bstep (se 2 (by rfl) ⟨2176881, by rfl⟩ : syracuseStep 5805017 = 4353763) B4353763
theorem B5379089 : Blo 782338 5379089 := bstep (se 2 (by rfl) ⟨2017158, by rfl⟩ : syracuseStep 5379089 = 4034317) B4034317
theorem B2331737 : Blo 782338 2331737 := bstep (se 2 (by rfl) ⟨874401, by rfl⟩ : syracuseStep 2331737 = 1748803) B1748803
theorem B5018755 : Blo 782338 5018755 := bstep (se 1 (by rfl) ⟨3764066, by rfl⟩ : syracuseStep 5018755 = 7528133) B7528133
theorem B2233565 : Blo 782338 2233565 := bstep (se 3 (by rfl) ⟨418793, by rfl⟩ : syracuseStep 2233565 = 837587) B837587
theorem B1119511 : Blo 782338 1119511 := bstep (se 1 (by rfl) ⟨839633, by rfl⟩ : syracuseStep 1119511 = 1679267) B1679267
theorem B3020107 : Blo 782338 3020107 := bstep (se 1 (by rfl) ⟨2265080, by rfl⟩ : syracuseStep 3020107 = 4530161) B4530161
theorem B1676695 : Blo 782338 1676695 := bstep (se 1 (by rfl) ⟨1257521, by rfl⟩ : syracuseStep 1676695 = 2515043) B2515043
theorem B2233793 : Blo 782338 2233793 := bstep (se 2 (by rfl) ⟨837672, by rfl⟩ : syracuseStep 2233793 = 1675345) B1675345
theorem B1676875 : Blo 782338 1676875 := bstep (se 1 (by rfl) ⟨1257656, by rfl⟩ : syracuseStep 1676875 = 2515313) B2515313
theorem B1676951 : Blo 782338 1676951 := bstep (se 1 (by rfl) ⟨1257713, by rfl⟩ : syracuseStep 1676951 = 2515427) B2515427
theorem B3348161 : Blo 782338 3348161 := bstep (se 2 (by rfl) ⟨1255560, by rfl⟩ : syracuseStep 3348161 = 2511121) B2511121
theorem B2234135 : Blo 782338 2234135 := bstep (se 1 (by rfl) ⟨1675601, by rfl⟩ : syracuseStep 2234135 = 3351203) B3351203
theorem B3348503 : Blo 782338 3348503 := bstep (se 1 (by rfl) ⟨2511377, by rfl⟩ : syracuseStep 3348503 = 5022755) B5022755
theorem B5740645 : Blo 782338 5740645 := bstep (se 4 (by rfl) ⟨538185, by rfl⟩ : syracuseStep 5740645 = 1076371) B1076371
theorem B2824465 : Blo 782338 2824465 := bstep (se 2 (by rfl) ⟨1059174, by rfl⟩ : syracuseStep 2824465 = 2118349) B2118349
theorem B2824579 : Blo 782338 2824579 := bstep (se 1 (by rfl) ⟨2118434, by rfl⟩ : syracuseStep 2824579 = 4236869) B4236869
theorem B3054401 : Blo 782338 3054401 := bstep (se 2 (by rfl) ⟨1145400, by rfl⟩ : syracuseStep 3054401 = 2290801) B2290801
theorem B3971915 : Blo 782338 3971915 := bstep (se 1 (by rfl) ⟨2978936, by rfl⟩ : syracuseStep 3971915 = 5957873) B5957873
theorem B793643 : Blo 782338 793643 := bstep (se 1 (by rfl) ⟨595232, by rfl⟩ : syracuseStep 793643 = 1190465) B1190465
theorem B1678745 : Blo 782338 1678745 := bstep (se 2 (by rfl) ⟨629529, by rfl⟩ : syracuseStep 1678745 = 1259059) B1259059
theorem B990731 : Blo 782338 990731 := bstep (se 1 (by rfl) ⟨743048, by rfl⟩ : syracuseStep 990731 = 1486097) B1486097
theorem B5643793 : Blo 782338 5643793 := bstep (se 2 (by rfl) ⟨2116422, by rfl⟩ : syracuseStep 5643793 = 4232845) B4232845
theorem B1810163 : Blo 782338 1810163 := bstep (se 1 (by rfl) ⟨1357622, by rfl⟩ : syracuseStep 1810163 = 2715245) B2715245
theorem B5742541 : Blo 782338 5742541 := bstep (se 3 (by rfl) ⟨1076726, by rfl⟩ : syracuseStep 5742541 = 2153453) B2153453
theorem B1679411 : Blo 782338 1679411 := bstep (se 1 (by rfl) ⟨1259558, by rfl⟩ : syracuseStep 1679411 = 2519117) B2519117
theorem B2236481 : Blo 782338 2236481 := bstep (se 2 (by rfl) ⟨838680, by rfl⟩ : syracuseStep 2236481 = 1677361) B1677361
theorem B3350621 : Blo 782338 3350621 := bstep (se 3 (by rfl) ⟨628241, by rfl⟩ : syracuseStep 3350621 = 1256483) B1256483
theorem B991435 : Blo 782338 991435 := bstep (se 1 (by rfl) ⟨743576, by rfl⟩ : syracuseStep 991435 = 1487153) B1487153
theorem B2859229 : Blo 782338 2859229 := bstep (se 3 (by rfl) ⟨536105, by rfl⟩ : syracuseStep 2859229 = 1072211) B1072211
theorem B3776813 : Blo 782338 3776813 := bstep (se 3 (by rfl) ⟨708152, by rfl⟩ : syracuseStep 3776813 = 1416305) B1416305
theorem B4464989 : Blo 782338 4464989 := bstep (se 3 (by rfl) ⟨837185, by rfl⟩ : syracuseStep 4464989 = 1674371) B1674371
theorem B3350929 : Blo 782338 3350929 := bstep (se 2 (by rfl) ⟨1256598, by rfl⟩ : syracuseStep 3350929 = 2513197) B2513197
theorem B3350963 : Blo 782338 3350963 := bstep (se 1 (by rfl) ⟨2513222, by rfl⟩ : syracuseStep 3350963 = 5026445) B5026445
theorem B991703 : Blo 782338 991703 := bstep (se 1 (by rfl) ⟨743777, by rfl⟩ : syracuseStep 991703 = 1487555) B1487555
theorem B3973697 : Blo 782338 3973697 := bstep (se 2 (by rfl) ⟨1490136, by rfl⟩ : syracuseStep 3973697 = 2980273) B2980273
theorem B2237017 : Blo 782338 2237017 := bstep (se 2 (by rfl) ⟨838881, by rfl⟩ : syracuseStep 2237017 = 1677763) B1677763
theorem B13607797 : Blo 782338 13607797 := bstep (se 5 (by rfl) ⟨637865, by rfl⟩ : syracuseStep 13607797 = 1275731) B1275731
theorem B992407 : Blo 782338 992407 := bstep (se 1 (by rfl) ⟨744305, by rfl⟩ : syracuseStep 992407 = 1488611) B1488611
theorem B7152857 : Blo 782338 7152857 := bstep (se 2 (by rfl) ⟨2682321, by rfl⟩ : syracuseStep 7152857 = 5364643) B5364643
theorem B8496485 : Blo 782338 8496485 := bstep (se 4 (by rfl) ⟨796545, by rfl⟩ : syracuseStep 8496485 = 1593091) B1593091
theorem B2827723 : Blo 782338 2827723 := bstep (se 1 (by rfl) ⟨2120792, by rfl⟩ : syracuseStep 2827723 = 4241585) B4241585
theorem B2827997 : Blo 782338 2827997 := bstep (se 3 (by rfl) ⟨530249, by rfl⟩ : syracuseStep 2827997 = 1060499) B1060499
theorem B1320779 : Blo 782338 1320779 := bstep (se 1 (by rfl) ⟨990584, by rfl⟩ : syracuseStep 1320779 = 1981169) B1981169
theorem B2828125 : Blo 782338 2828125 := bstep (se 3 (by rfl) ⟨530273, by rfl⟩ : syracuseStep 2828125 = 1060547) B1060547
theorem B54470501 : Blo 782338 54470501 := bstep (se 4 (by rfl) ⟨5106609, by rfl⟩ : syracuseStep 54470501 = 10213219) B10213219
theorem B1320907 : Blo 782338 1320907 := bstep (se 1 (by rfl) ⟨990680, by rfl⟩ : syracuseStep 1320907 = 1981361) B1981361
theorem B1321049 : Blo 782338 1321049 := bstep (se 2 (by rfl) ⟨495393, by rfl⟩ : syracuseStep 1321049 = 990787) B990787
theorem B5941349 : Blo 782338 5941349 := bstep (se 4 (by rfl) ⟨557001, by rfl⟩ : syracuseStep 5941349 = 1114003) B1114003
theorem B14297239 : Blo 782338 14297239 := bstep (se 1 (by rfl) ⟨10722929, by rfl⟩ : syracuseStep 14297239 = 21445859) B21445859
theorem B1321177 : Blo 782338 1321177 := bstep (se 2 (by rfl) ⟨495441, by rfl⟩ : syracuseStep 1321177 = 990883) B990883
theorem B3352877 : Blo 782338 3352877 := bstep (se 3 (by rfl) ⟨628664, by rfl⟩ : syracuseStep 3352877 = 1257329) B1257329
theorem B7547201 : Blo 782338 7547201 := bstep (se 2 (by rfl) ⟨2830200, by rfl⟩ : syracuseStep 7547201 = 5660401) B5660401
theorem B3975641 : Blo 782338 3975641 := bstep (se 2 (by rfl) ⟨1490865, by rfl⟩ : syracuseStep 3975641 = 2981731) B2981731
theorem B2238941 : Blo 782338 2238941 := bstep (se 3 (by rfl) ⟨419801, by rfl⟩ : syracuseStep 2238941 = 839603) B839603
theorem B5941835 : Blo 782338 5941835 := bstep (se 1 (by rfl) ⟨4456376, by rfl⟩ : syracuseStep 5941835 = 8912753) B8912753
theorem B895639 : Blo 782338 895639 := bstep (se 1 (by rfl) ⟨671729, by rfl⟩ : syracuseStep 895639 = 1343459) B1343459
theorem B4467473 : Blo 782338 4467473 := bstep (se 2 (by rfl) ⟨1675302, by rfl⟩ : syracuseStep 4467473 = 3350605) B3350605
theorem B1321751 : Blo 782338 1321751 := bstep (se 1 (by rfl) ⟨991313, by rfl⟩ : syracuseStep 1321751 = 1982627) B1982627
theorem B994123 : Blo 782338 994123 := bstep (se 1 (by rfl) ⟨745592, by rfl⟩ : syracuseStep 994123 = 1491185) B1491185
theorem B1321879 : Blo 782338 1321879 := bstep (se 1 (by rfl) ⟨991409, by rfl⟩ : syracuseStep 1321879 = 1982819) B1982819
theorem B3353561 : Blo 782338 3353561 := bstep (se 2 (by rfl) ⟨1257585, by rfl⟩ : syracuseStep 3353561 = 2515171) B2515171
theorem B4238381 : Blo 782338 4238381 := bstep (se 3 (by rfl) ⟨794696, by rfl⟩ : syracuseStep 4238381 = 1589393) B1589393
theorem B2010263 : Blo 782338 2010263 := bstep (se 1 (by rfl) ⟨1507697, by rfl⟩ : syracuseStep 2010263 = 3015395) B3015395
theorem B1191115 : Blo 782338 1191115 := bstep (se 1 (by rfl) ⟨893336, by rfl⟩ : syracuseStep 1191115 = 1786673) B1786673
theorem B1256791 : Blo 782338 1256791 := bstep (se 1 (by rfl) ⟨942593, by rfl⟩ : syracuseStep 1256791 = 1885187) B1885187
theorem B1322507 : Blo 782338 1322507 := bstep (se 1 (by rfl) ⟨991880, by rfl⟩ : syracuseStep 1322507 = 1983761) B1983761
theorem B1257047 : Blo 782338 1257047 := bstep (se 1 (by rfl) ⟨942785, by rfl⟩ : syracuseStep 1257047 = 1885571) B1885571
theorem B1322635 : Blo 782338 1322635 := bstep (se 1 (by rfl) ⟨991976, by rfl⟩ : syracuseStep 1322635 = 1983953) B1983953
theorem B995095 : Blo 782338 995095 := bstep (se 1 (by rfl) ⟨746321, by rfl⟩ : syracuseStep 995095 = 1492643) B1492643
theorem B1322777 : Blo 782338 1322777 := bstep (se 2 (by rfl) ⟨496041, by rfl⟩ : syracuseStep 1322777 = 992083) B992083
theorem B1486667 : Blo 782338 1486667 := bstep (se 1 (by rfl) ⟨1115000, by rfl⟩ : syracuseStep 1486667 = 2230001) B2230001
theorem B1322905 : Blo 782338 1322905 := bstep (se 2 (by rfl) ⟨496089, by rfl⟩ : syracuseStep 1322905 = 992179) B992179
theorem B1257419 : Blo 782338 1257419 := bstep (se 1 (by rfl) ⟨943064, by rfl⟩ : syracuseStep 1257419 = 1886129) B1886129
theorem B1486849 : Blo 782338 1486849 := bstep (se 2 (by rfl) ⟨557568, by rfl⟩ : syracuseStep 1486849 = 1115137) B1115137
theorem B3977261 : Blo 782338 3977261 := bstep (se 3 (by rfl) ⟨745736, by rfl⟩ : syracuseStep 3977261 = 1491473) B1491473
theorem B1061131 : Blo 782338 1061131 := bstep (se 1 (by rfl) ⟨795848, by rfl⟩ : syracuseStep 1061131 = 1591697) B1591697
theorem B1487297 : Blo 782338 1487297 := bstep (se 2 (by rfl) ⟨557736, by rfl⟩ : syracuseStep 1487297 = 1115473) B1115473
theorem B1323479 : Blo 782338 1323479 := bstep (se 1 (by rfl) ⟨992609, by rfl⟩ : syracuseStep 1323479 = 1985219) B1985219
theorem B1323607 : Blo 782338 1323607 := bstep (se 1 (by rfl) ⟨992705, by rfl⟩ : syracuseStep 1323607 = 1985411) B1985411
theorem B1487639 : Blo 782338 1487639 := bstep (se 1 (by rfl) ⟨1115729, by rfl⟩ : syracuseStep 1487639 = 2231459) B2231459
theorem B2011979 : Blo 782338 2011979 := bstep (se 1 (by rfl) ⟨1508984, by rfl⟩ : syracuseStep 2011979 = 3017969) B3017969
theorem B1881035 : Blo 782338 1881035 := bstep (se 1 (by rfl) ⟨1410776, by rfl⟩ : syracuseStep 1881035 = 2821553) B2821553
theorem B7549969 : Blo 782338 7549969 := bstep (se 2 (by rfl) ⟨2831238, by rfl⟩ : syracuseStep 7549969 = 5662477) B5662477
theorem B4764851 : Blo 782338 4764851 := bstep (se 1 (by rfl) ⟨3573638, by rfl⟩ : syracuseStep 4764851 = 7147277) B7147277
theorem B1324235 : Blo 782338 1324235 := bstep (se 1 (by rfl) ⟨993176, by rfl⟩ : syracuseStep 1324235 = 1986353) B1986353
theorem B1193177 : Blo 782338 1193177 := bstep (se 2 (by rfl) ⟨447441, by rfl⟩ : syracuseStep 1193177 = 894883) B894883
theorem B1324363 : Blo 782338 1324363 := bstep (se 1 (by rfl) ⟨993272, by rfl⟩ : syracuseStep 1324363 = 1986545) B1986545
theorem B1258841 : Blo 782338 1258841 := bstep (se 2 (by rfl) ⟨472065, by rfl⟩ : syracuseStep 1258841 = 944131) B944131
theorem B1488307 : Blo 782338 1488307 := bstep (se 1 (by rfl) ⟨1116230, by rfl⟩ : syracuseStep 1488307 = 2232461) B2232461
theorem B1324505 : Blo 782338 1324505 := bstep (se 2 (by rfl) ⟨496689, by rfl⟩ : syracuseStep 1324505 = 993379) B993379
theorem B5027345 : Blo 782338 5027345 := bstep (se 2 (by rfl) ⟨1885254, by rfl⟩ : syracuseStep 5027345 = 3770509) B3770509
theorem B3356225 : Blo 782338 3356225 := bstep (se 2 (by rfl) ⟨1258584, by rfl⟩ : syracuseStep 3356225 = 2517169) B2517169
theorem B1324633 : Blo 782338 1324633 := bstep (se 2 (by rfl) ⟨496737, by rfl⟩ : syracuseStep 1324633 = 993475) B993475
theorem B1488755 : Blo 782338 1488755 := bstep (se 1 (by rfl) ⟨1116566, by rfl⟩ : syracuseStep 1488755 = 2233133) B2233133
theorem B1488793 : Blo 782338 1488793 := bstep (se 2 (by rfl) ⟨558297, by rfl⟩ : syracuseStep 1488793 = 1116595) B1116595
theorem B11319365 : Blo 782338 11319365 := bstep (se 4 (by rfl) ⟨1061190, by rfl⟩ : syracuseStep 11319365 = 2122381) B2122381
theorem B4536395 : Blo 782338 4536395 := bstep (se 1 (by rfl) ⟨3402296, by rfl⟩ : syracuseStep 4536395 = 6804593) B6804593
theorem B1325207 : Blo 782338 1325207 := bstep (se 1 (by rfl) ⟨993905, by rfl⟩ : syracuseStep 1325207 = 1987811) B1987811
theorem B1325335 : Blo 782338 1325335 := bstep (se 1 (by rfl) ⟨994001, by rfl⟩ : syracuseStep 1325335 = 1988003) B1988003
theorem B1882457 : Blo 782338 1882457 := bstep (se 2 (by rfl) ⟨705921, by rfl⟩ : syracuseStep 1882457 = 1411843) B1411843
theorem B1489241 : Blo 782338 1489241 := bstep (se 2 (by rfl) ⟨558465, by rfl⟩ : syracuseStep 1489241 = 1116931) B1116931
theorem B1980875 : Blo 782338 1980875 := bstep (se 1 (by rfl) ⟨1485656, by rfl⟩ : syracuseStep 1980875 = 2971313) B2971313
theorem B6699671 : Blo 782338 6699671 := bstep (se 1 (by rfl) ⟨5024753, by rfl⟩ : syracuseStep 6699671 = 10049507) B10049507
theorem B5356211 : Blo 782338 5356211 := bstep (se 1 (by rfl) ⟨4017158, by rfl⟩ : syracuseStep 5356211 = 8034317) B8034317
theorem B1325963 : Blo 782338 1325963 := bstep (se 1 (by rfl) ⟨994472, by rfl⟩ : syracuseStep 1325963 = 1988945) B1988945
theorem B2833373 : Blo 782338 2833373 := bstep (se 3 (by rfl) ⟨531257, by rfl⟩ : syracuseStep 2833373 = 1062515) B1062515
theorem B1326091 : Blo 782338 1326091 := bstep (se 1 (by rfl) ⟨994568, by rfl⟩ : syracuseStep 1326091 = 1989137) B1989137
theorem B3357713 : Blo 782338 3357713 := bstep (se 2 (by rfl) ⟨1259142, by rfl⟩ : syracuseStep 3357713 = 2518285) B2518285
theorem B1489985 : Blo 782338 1489985 := bstep (se 2 (by rfl) ⟨558744, by rfl⟩ : syracuseStep 1489985 = 1117489) B1117489
theorem B12729419 : Blo 782338 12729419 := bstep (se 1 (by rfl) ⟨9547064, by rfl⟩ : syracuseStep 12729419 = 19094129) B19094129
theorem B1326233 : Blo 782338 1326233 := bstep (se 2 (by rfl) ⟨497337, by rfl⟩ : syracuseStep 1326233 = 994675) B994675
theorem B1326361 : Blo 782338 1326361 := bstep (se 2 (by rfl) ⟨497385, by rfl⟩ : syracuseStep 1326361 = 994771) B994771
theorem B1490251 : Blo 782338 1490251 := bstep (se 1 (by rfl) ⟨1117688, by rfl⟩ : syracuseStep 1490251 = 2235377) B2235377
theorem B1588567 : Blo 782338 1588567 := bstep (se 1 (by rfl) ⟨1191425, by rfl⟩ : syracuseStep 1588567 = 2382851) B2382851
theorem B1981847 : Blo 782338 1981847 := bstep (se 1 (by rfl) ⟨1486385, by rfl⟩ : syracuseStep 1981847 = 2972771) B2972771
theorem B1588939 : Blo 782338 1588939 := bstep (se 1 (by rfl) ⟨1191704, by rfl⟩ : syracuseStep 1588939 = 2383409) B2383409
theorem B2506457 : Blo 782338 2506457 := bstep (se 2 (by rfl) ⟨939921, by rfl⟩ : syracuseStep 2506457 = 1879843) B1879843
theorem B1490699 : Blo 782338 1490699 := bstep (se 1 (by rfl) ⟨1118024, by rfl⟩ : syracuseStep 1490699 = 2236049) B2236049
theorem B5947181 : Blo 782338 5947181 := bstep (se 3 (by rfl) ⟨1115096, by rfl⟩ : syracuseStep 5947181 = 2230193) B2230193
theorem B1326935 : Blo 782338 1326935 := bstep (se 1 (by rfl) ⟨995201, by rfl⟩ : syracuseStep 1326935 = 1990403) B1990403
theorem B1490881 : Blo 782338 1490881 := bstep (se 2 (by rfl) ⟨559080, by rfl⟩ : syracuseStep 1490881 = 1118161) B1118161
theorem B8044505 : Blo 782338 8044505 := bstep (se 2 (by rfl) ⟨3016689, by rfl⟩ : syracuseStep 8044505 = 6033379) B6033379
theorem B3358685 : Blo 782338 3358685 := bstep (se 3 (by rfl) ⟨629753, by rfl⟩ : syracuseStep 3358685 = 1259507) B1259507
theorem B1982515 : Blo 782338 1982515 := bstep (se 1 (by rfl) ⟨1486886, by rfl⟩ : syracuseStep 1982515 = 2973773) B2973773
theorem B835639 : Blo 782338 835639 := bstep (se 1 (by rfl) ⟨626729, by rfl⟩ : syracuseStep 835639 = 1253459) B1253459
theorem B1785971 : Blo 782338 1785971 := bstep (se 1 (by rfl) ⟨1339478, by rfl⟩ : syracuseStep 1785971 = 2678957) B2678957
theorem B1130635 : Blo 782338 1130635 := bstep (se 1 (by rfl) ⟨847976, by rfl⟩ : syracuseStep 1130635 = 1695953) B1695953
theorem B21479575 : Blo 782338 21479575 := bstep (se 1 (by rfl) ⟨16109681, by rfl⟩ : syracuseStep 21479575 = 32219363) B32219363
theorem B1982657 : Blo 782338 1982657 := bstep (se 2 (by rfl) ⟨743496, by rfl⟩ : syracuseStep 1982657 = 1486993) B1486993
theorem B1491223 : Blo 782338 1491223 := bstep (se 1 (by rfl) ⟨1118417, by rfl⟩ : syracuseStep 1491223 = 2236835) B2236835
theorem B5030237 : Blo 782338 5030237 := bstep (se 3 (by rfl) ⟨943169, by rfl⟩ : syracuseStep 5030237 = 1886339) B1886339
theorem B836011 : Blo 782338 836011 := bstep (se 1 (by rfl) ⟨627008, by rfl⟩ : syracuseStep 836011 = 1254017) B1254017
theorem B4473305 : Blo 782338 4473305 := bstep (se 2 (by rfl) ⟨1677489, by rfl⟩ : syracuseStep 4473305 = 3354979) B3354979
theorem B1491443 : Blo 782338 1491443 := bstep (se 1 (by rfl) ⟨1118582, by rfl⟩ : syracuseStep 1491443 = 2237165) B2237165
theorem B1491671 : Blo 782338 1491671 := bstep (se 1 (by rfl) ⟨1118753, by rfl⟩ : syracuseStep 1491671 = 2237507) B2237507
theorem B5653313 : Blo 782338 5653313 := bstep (se 2 (by rfl) ⟨2119992, by rfl⟩ : syracuseStep 5653313 = 4239985) B4239985
theorem B1491929 : Blo 782338 1491929 := bstep (se 2 (by rfl) ⟨559473, by rfl⟩ : syracuseStep 1491929 = 1118947) B1118947
theorem B1590359 : Blo 782338 1590359 := bstep (se 1 (by rfl) ⟨1192769, by rfl⟩ : syracuseStep 1590359 = 2385539) B2385539
theorem B3228931 : Blo 782338 3228931 := bstep (se 1 (by rfl) ⟨2421698, by rfl⟩ : syracuseStep 3228931 = 4843397) B4843397
theorem B2508097 : Blo 782338 2508097 := bstep (se 2 (by rfl) ⟨940536, by rfl⟩ : syracuseStep 2508097 = 1881073) B1881073
theorem B1492339 : Blo 782338 1492339 := bstep (se 1 (by rfl) ⟨1119254, by rfl⟩ : syracuseStep 1492339 = 2238509) B2238509
theorem B1361305 : Blo 782338 1361305 := bstep (se 2 (by rfl) ⟨510489, by rfl⟩ : syracuseStep 1361305 = 1020979) B1020979
theorem B1983923 : Blo 782338 1983923 := bstep (se 1 (by rfl) ⟨1487942, by rfl⟩ : syracuseStep 1983923 = 2975885) B2975885
theorem B2541277 : Blo 782338 2541277 := bstep (se 3 (by rfl) ⟨476489, by rfl⟩ : syracuseStep 2541277 = 952979) B952979
theorem B1787777 : Blo 782338 1787777 := bstep (se 2 (by rfl) ⟨670416, by rfl⟩ : syracuseStep 1787777 = 1340833) B1340833
theorem B1984459 : Blo 782338 1984459 := bstep (se 1 (by rfl) ⟨1488344, by rfl⟩ : syracuseStep 1984459 = 2976689) B2976689
theorem B9062435 : Blo 782338 9062435 := bstep (se 1 (by rfl) ⟨6796826, by rfl⟩ : syracuseStep 9062435 = 13593653) B13593653
theorem B1984601 : Blo 782338 1984601 := bstep (se 2 (by rfl) ⟨744225, by rfl⟩ : syracuseStep 1984601 = 1488451) B1488451
theorem B2115991 : Blo 782338 2115991 := bstep (se 1 (by rfl) ⟨1586993, by rfl⟩ : syracuseStep 2115991 = 3173987) B3173987
theorem B1886743 : Blo 782338 1886743 := bstep (se 1 (by rfl) ⟨1415057, by rfl⟩ : syracuseStep 1886743 = 2830115) B2830115
theorem B5032493 : Blo 782338 5032493 := bstep (se 3 (by rfl) ⟨943592, by rfl⟩ : syracuseStep 5032493 = 1887185) B1887185
theorem B1591859 : Blo 782338 1591859 := bstep (se 1 (by rfl) ⟨1193894, by rfl⟩ : syracuseStep 1591859 = 2387789) B2387789
theorem B9554753 : Blo 782338 9554753 := bstep (se 2 (by rfl) ⟨3583032, by rfl⟩ : syracuseStep 9554753 = 7166065) B7166065
theorem B1985431 : Blo 782338 1985431 := bstep (se 1 (by rfl) ⟨1489073, by rfl⟩ : syracuseStep 1985431 = 2978147) B2978147
theorem B13388813 : Blo 782338 13388813 := bstep (se 3 (by rfl) ⟨2510402, by rfl⟩ : syracuseStep 13388813 = 5020805) B5020805
theorem B838711 : Blo 782338 838711 := bstep (se 1 (by rfl) ⟨629033, by rfl⟩ : syracuseStep 838711 = 1258067) B1258067
theorem B4475969 : Blo 782338 4475969 := bstep (se 2 (by rfl) ⟨1678488, by rfl⟩ : syracuseStep 4475969 = 3356977) B3356977
theorem B1985867 : Blo 782338 1985867 := bstep (se 1 (by rfl) ⟨1489400, by rfl⟩ : syracuseStep 1985867 = 2978801) B2978801
theorem B2641355 : Blo 782338 2641355 := bstep (se 1 (by rfl) ⟨1981016, by rfl⟩ : syracuseStep 2641355 = 3962033) B3962033
theorem B5721617 : Blo 782338 5721617 := bstep (se 2 (by rfl) ⟨2145606, by rfl⟩ : syracuseStep 5721617 = 4291213) B4291213
theorem B5951069 : Blo 782338 5951069 := bstep (se 3 (by rfl) ⟨1115825, by rfl⟩ : syracuseStep 5951069 = 2231651) B2231651
theorem B1986241 : Blo 782338 1986241 := bstep (se 2 (by rfl) ⟨744840, by rfl⟩ : syracuseStep 1986241 = 1489681) B1489681
theorem B2641625 : Blo 782338 2641625 := bstep (se 2 (by rfl) ⟨990609, by rfl⟩ : syracuseStep 2641625 = 1981219) B1981219
theorem B8933165 : Blo 782338 8933165 := bstep (se 3 (by rfl) ⟨1674968, by rfl⟩ : syracuseStep 8933165 = 3349937) B3349937
theorem B839531 : Blo 782338 839531 := bstep (se 1 (by rfl) ⟨629648, by rfl⟩ : syracuseStep 839531 = 1259297) B1259297
theorem B2510813 : Blo 782338 2510813 := bstep (se 3 (by rfl) ⟨470777, by rfl⟩ : syracuseStep 2510813 = 941555) B941555
theorem B1790039 : Blo 782338 1790039 := bstep (se 1 (by rfl) ⟨1342529, by rfl⟩ : syracuseStep 1790039 = 2685059) B2685059
theorem B1986839 : Blo 782338 1986839 := bstep (se 1 (by rfl) ⟨1490129, by rfl⟩ : syracuseStep 1986839 = 2980259) B2980259
theorem B2117981 : Blo 782338 2117981 := bstep (se 3 (by rfl) ⟨397121, by rfl⟩ : syracuseStep 2117981 = 794243) B794243
theorem B2642327 : Blo 782338 2642327 := bstep (se 1 (by rfl) ⟨1981745, by rfl⟩ : syracuseStep 2642327 = 3963491) B3963491
theorem B3625523 : Blo 782338 3625523 := bstep (se 1 (by rfl) ⟨2719142, by rfl⟩ : syracuseStep 3625523 = 5438285) B5438285
theorem B14471885 : Blo 782338 14471885 := bstep (se 3 (by rfl) ⟨2713478, by rfl⟩ : syracuseStep 14471885 = 5426957) B5426957
theorem B24171317 : Blo 782338 24171317 := bstep (se 5 (by rfl) ⟨1133030, by rfl⟩ : syracuseStep 24171317 = 2266061) B2266061
theorem B2642867 : Blo 782338 2642867 := bstep (se 1 (by rfl) ⟨1982150, by rfl⟩ : syracuseStep 2642867 = 3964301) B3964301
theorem B1987649 : Blo 782338 1987649 := bstep (se 2 (by rfl) ⟨745368, by rfl⟩ : syracuseStep 1987649 = 1490737) B1490737
theorem B2643137 : Blo 782338 2643137 := bstep (se 2 (by rfl) ⟨991176, by rfl⟩ : syracuseStep 2643137 = 1982353) B1982353
theorem B2970827 : Blo 782338 2970827 := bstep (se 1 (by rfl) ⟨2228120, by rfl⟩ : syracuseStep 2970827 = 4456241) B4456241
theorem B2971025 : Blo 782338 2971025 := bstep (se 2 (by rfl) ⟨1114134, by rfl⟩ : syracuseStep 2971025 = 2228269) B2228269
theorem B1988185 : Blo 782338 1988185 := bstep (se 2 (by rfl) ⟨745569, by rfl⟩ : syracuseStep 1988185 = 1491139) B1491139
theorem B2643677 : Blo 782338 2643677 := bstep (se 3 (by rfl) ⟨495689, by rfl⟩ : syracuseStep 2643677 = 991379) B991379
theorem B5658443 : Blo 782338 5658443 := bstep (se 1 (by rfl) ⟨4243832, by rfl⟩ : syracuseStep 5658443 = 8487665) B8487665
theorem B5035877 : Blo 782338 5035877 := bstep (se 4 (by rfl) ⟨472113, by rfl⟩ : syracuseStep 5035877 = 944227) B944227
theorem B940171 : Blo 782338 940171 := bstep (se 1 (by rfl) ⟨705128, by rfl⟩ : syracuseStep 940171 = 1410257) B1410257
theorem B2971799 : Blo 782338 2971799 := bstep (se 1 (by rfl) ⟨2228849, by rfl⟩ : syracuseStep 2971799 = 4457699) B4457699
theorem B2971997 : Blo 782338 2971997 := bstep (se 3 (by rfl) ⟨557249, by rfl⟩ : syracuseStep 2971997 = 1114499) B1114499
theorem B3627443 : Blo 782338 3627443 := bstep (se 1 (by rfl) ⟨2720582, by rfl⟩ : syracuseStep 3627443 = 5441165) B5441165
theorem B1989299 : Blo 782338 1989299 := bstep (se 1 (by rfl) ⟨1491974, by rfl⟩ : syracuseStep 1989299 = 2983949) B2983949
theorem B2644811 : Blo 782338 2644811 := bstep (se 1 (by rfl) ⟨1983608, by rfl⟩ : syracuseStep 2644811 = 3967217) B3967217
theorem B1989593 : Blo 782338 1989593 := bstep (se 2 (by rfl) ⟨746097, by rfl⟩ : syracuseStep 1989593 = 1492195) B1492195
theorem B1760345 : Blo 782338 1760345 := bstep (se 2 (by rfl) ⟨660129, by rfl⟩ : syracuseStep 1760345 = 1320259) B1320259
theorem B2645081 : Blo 782338 2645081 := bstep (se 2 (by rfl) ⟨991905, by rfl⟩ : syracuseStep 2645081 = 1983811) B1983811
theorem B1760435 : Blo 782338 1760435 := bstep (se 1 (by rfl) ⟨1320326, by rfl⟩ : syracuseStep 1760435 = 2640653) B2640653
theorem B1760471 : Blo 782338 1760471 := bstep (se 1 (by rfl) ⟨1320353, by rfl⟩ : syracuseStep 1760471 = 2640707) B2640707
theorem B2120921 : Blo 782338 2120921 := bstep (se 2 (by rfl) ⟨795345, by rfl⟩ : syracuseStep 2120921 = 1590691) B1590691
theorem B1760651 : Blo 782338 1760651 := bstep (se 1 (by rfl) ⟨1320488, by rfl⟩ : syracuseStep 1760651 = 2640977) B2640977
theorem B1760705 : Blo 782338 1760705 := bstep (se 2 (by rfl) ⟨660264, by rfl⟩ : syracuseStep 1760705 = 1320529) B1320529
theorem B7167449 : Blo 782338 7167449 := bstep (se 2 (by rfl) ⟨2687793, by rfl⟩ : syracuseStep 7167449 = 5375587) B5375587
theorem B1760921 : Blo 782338 1760921 := bstep (se 2 (by rfl) ⟨660345, by rfl⟩ : syracuseStep 1760921 = 1320691) B1320691
theorem B1761011 : Blo 782338 1761011 := bstep (se 1 (by rfl) ⟨1320758, by rfl⟩ : syracuseStep 1761011 = 2641517) B2641517
theorem B1761047 : Blo 782338 1761047 := bstep (se 1 (by rfl) ⟨1320785, by rfl⟩ : syracuseStep 1761047 = 2641571) B2641571
theorem B2645783 : Blo 782338 2645783 := bstep (se 1 (by rfl) ⟨1984337, by rfl⟩ : syracuseStep 2645783 = 3968675) B3968675
theorem B1695553 : Blo 782338 1695553 := bstep (se 2 (by rfl) ⟨635832, by rfl⟩ : syracuseStep 1695553 = 1271665) B1271665
theorem B6709169 : Blo 782338 6709169 := bstep (se 2 (by rfl) ⟨2515938, by rfl⟩ : syracuseStep 6709169 = 5031877) B5031877
theorem B1761227 : Blo 782338 1761227 := bstep (se 1 (by rfl) ⟨1320920, by rfl⟩ : syracuseStep 1761227 = 2641841) B2641841
theorem B1761281 : Blo 782338 1761281 := bstep (se 2 (by rfl) ⟨660480, by rfl⟩ : syracuseStep 1761281 = 1320961) B1320961
theorem B14278787 : Blo 782338 14278787 := bstep (se 1 (by rfl) ⟨10709090, by rfl⟩ : syracuseStep 14278787 = 21418181) B21418181
theorem B1761497 : Blo 782338 1761497 := bstep (se 2 (by rfl) ⟨660561, by rfl⟩ : syracuseStep 1761497 = 1321123) B1321123
theorem B2547929 : Blo 782338 2547929 := bstep (se 2 (by rfl) ⟨955473, by rfl⟩ : syracuseStep 2547929 = 1910947) B1910947
theorem B2973955 : Blo 782338 2973955 := bstep (se 1 (by rfl) ⟨2230466, by rfl⟩ : syracuseStep 2973955 = 4460933) B4460933
theorem B1761587 : Blo 782338 1761587 := bstep (se 1 (by rfl) ⟨1321190, by rfl⟩ : syracuseStep 1761587 = 2642381) B2642381
theorem B2646323 : Blo 782338 2646323 := bstep (se 1 (by rfl) ⟨1984742, by rfl⟩ : syracuseStep 2646323 = 3969485) B3969485
theorem B1761623 : Blo 782338 1761623 := bstep (se 1 (by rfl) ⟨1321217, by rfl⟩ : syracuseStep 1761623 = 2642435) B2642435
theorem B1761803 : Blo 782338 1761803 := bstep (se 1 (by rfl) ⟨1321352, by rfl⟩ : syracuseStep 1761803 = 2642705) B2642705
theorem B2384407 : Blo 782338 2384407 := bstep (se 1 (by rfl) ⟨1788305, by rfl⟩ : syracuseStep 2384407 = 3576611) B3576611
theorem B2974259 : Blo 782338 2974259 := bstep (se 1 (by rfl) ⟨2230694, by rfl⟩ : syracuseStep 2974259 = 4461389) B4461389
theorem B1761857 : Blo 782338 1761857 := bstep (se 2 (by rfl) ⟨660696, by rfl⟩ : syracuseStep 1761857 = 1321393) B1321393
theorem B2646593 : Blo 782338 2646593 := bstep (se 2 (by rfl) ⟨992472, by rfl⟩ : syracuseStep 2646593 = 1984945) B1984945
theorem B6349529 : Blo 782338 6349529 := bstep (se 2 (by rfl) ⟨2381073, by rfl⟩ : syracuseStep 6349529 = 4762147) B4762147
theorem B1762073 : Blo 782338 1762073 := bstep (se 2 (by rfl) ⟨660777, by rfl⟩ : syracuseStep 1762073 = 1321555) B1321555
theorem B1762163 : Blo 782338 1762163 := bstep (se 1 (by rfl) ⟨1321622, by rfl⟩ : syracuseStep 1762163 = 2643245) B2643245
theorem B1762199 : Blo 782338 1762199 := bstep (se 1 (by rfl) ⟨1321649, by rfl⟩ : syracuseStep 1762199 = 2643299) B2643299
theorem B1762379 : Blo 782338 1762379 := bstep (se 1 (by rfl) ⟨1321784, by rfl⟩ : syracuseStep 1762379 = 2643569) B2643569
theorem B2647133 : Blo 782338 2647133 := bstep (se 3 (by rfl) ⟨496337, by rfl⟩ : syracuseStep 2647133 = 992675) B992675
theorem B1762433 : Blo 782338 1762433 := bstep (se 2 (by rfl) ⟨660912, by rfl⟩ : syracuseStep 1762433 = 1321825) B1321825
theorem B7169201 : Blo 782338 7169201 := bstep (se 2 (by rfl) ⟨2688450, by rfl⟩ : syracuseStep 7169201 = 5376901) B5376901
theorem B2974913 : Blo 782338 2974913 := bstep (se 2 (by rfl) ⟨1115592, by rfl⟩ : syracuseStep 2974913 = 2231185) B2231185
theorem B2122955 : Blo 782338 2122955 := bstep (se 1 (by rfl) ⟨1592216, by rfl⟩ : syracuseStep 2122955 = 3184433) B3184433
theorem B3761453 : Blo 782338 3761453 := bstep (se 3 (by rfl) ⟨705272, by rfl⟩ : syracuseStep 3761453 = 1410545) B1410545
theorem B1762649 : Blo 782338 1762649 := bstep (se 2 (by rfl) ⟨660993, by rfl⟩ : syracuseStep 1762649 = 1321987) B1321987
theorem B5727581 : Blo 782338 5727581 := bstep (se 3 (by rfl) ⟨1073921, by rfl⟩ : syracuseStep 5727581 = 2147843) B2147843
theorem B1762739 : Blo 782338 1762739 := bstep (se 1 (by rfl) ⟨1322054, by rfl⟩ : syracuseStep 1762739 = 2644109) B2644109
theorem B1762775 : Blo 782338 1762775 := bstep (se 1 (by rfl) ⟨1322081, by rfl⟩ : syracuseStep 1762775 = 2644163) B2644163
theorem B2516503 : Blo 782338 2516503 := bstep (se 1 (by rfl) ⟨1887377, by rfl⟩ : syracuseStep 2516503 = 3774755) B3774755
theorem B1762955 : Blo 782338 1762955 := bstep (se 1 (by rfl) ⟨1322216, by rfl⟩ : syracuseStep 1762955 = 2644433) B2644433
theorem B1763009 : Blo 782338 1763009 := bstep (se 2 (by rfl) ⟨661128, by rfl⟩ : syracuseStep 1763009 = 1322257) B1322257
theorem B2516683 : Blo 782338 2516683 := bstep (se 1 (by rfl) ⟨1887512, by rfl⟩ : syracuseStep 2516683 = 3775025) B3775025
theorem B2516759 : Blo 782338 2516759 := bstep (se 1 (by rfl) ⟨1887569, by rfl⟩ : syracuseStep 2516759 = 3775139) B3775139
theorem B1763225 : Blo 782338 1763225 := bstep (se 2 (by rfl) ⟨661209, by rfl⟩ : syracuseStep 1763225 = 1322419) B1322419
theorem B2516953 : Blo 782338 2516953 := bstep (se 2 (by rfl) ⟨943857, by rfl⟩ : syracuseStep 2516953 = 1887715) B1887715
theorem B1763315 : Blo 782338 1763315 := bstep (se 1 (by rfl) ⟨1322486, by rfl⟩ : syracuseStep 1763315 = 2644973) B2644973
theorem B1173515 : Blo 782338 1173515 := bstep (se 1 (by rfl) ⟨880136, by rfl⟩ : syracuseStep 1173515 = 1760273) B1760273
theorem B1173527 : Blo 782338 1173527 := bstep (se 1 (by rfl) ⟨880145, by rfl⟩ : syracuseStep 1173527 = 1760291) B1760291
theorem B1763351 : Blo 782338 1763351 := bstep (se 1 (by rfl) ⟨1322513, by rfl⟩ : syracuseStep 1763351 = 2645027) B2645027
theorem B1173593 : Blo 782338 1173593 := bstep (se 2 (by rfl) ⟨440097, by rfl⟩ : syracuseStep 1173593 = 880195) B880195
theorem B1173707 : Blo 782338 1173707 := bstep (se 1 (by rfl) ⟨880280, by rfl⟩ : syracuseStep 1173707 = 1760561) B1760561
theorem B1763531 : Blo 782338 1763531 := bstep (se 1 (by rfl) ⟨1322648, by rfl⟩ : syracuseStep 1763531 = 2645297) B2645297
theorem B2648267 : Blo 782338 2648267 := bstep (se 1 (by rfl) ⟨1986200, by rfl⟩ : syracuseStep 2648267 = 3972401) B3972401
theorem B1173719 : Blo 782338 1173719 := bstep (se 1 (by rfl) ⟨880289, by rfl⟩ : syracuseStep 1173719 = 1760579) B1760579
theorem B1763585 : Blo 782338 1763585 := bstep (se 2 (by rfl) ⟨661344, by rfl⟩ : syracuseStep 1763585 = 1322689) B1322689
theorem B1173785 : Blo 782338 1173785 := bstep (se 2 (by rfl) ⟨440169, by rfl⟩ : syracuseStep 1173785 = 880339) B880339
theorem B1173899 : Blo 782338 1173899 := bstep (se 1 (by rfl) ⟨880424, by rfl⟩ : syracuseStep 1173899 = 1760849) B1760849
theorem B1173911 : Blo 782338 1173911 := bstep (se 1 (by rfl) ⟨880433, by rfl⟩ : syracuseStep 1173911 = 1760867) B1760867
theorem B2976173 : Blo 782338 2976173 := bstep (se 3 (by rfl) ⟨558032, by rfl⟩ : syracuseStep 2976173 = 1116065) B1116065
theorem B2976203 : Blo 782338 2976203 := bstep (se 1 (by rfl) ⟨2232152, by rfl⟩ : syracuseStep 2976203 = 4464305) B4464305
theorem B1173977 : Blo 782338 1173977 := bstep (se 2 (by rfl) ⟨440241, by rfl⟩ : syracuseStep 1173977 = 880483) B880483
theorem B1763801 : Blo 782338 1763801 := bstep (se 2 (by rfl) ⟨661425, by rfl⟩ : syracuseStep 1763801 = 1322851) B1322851
theorem B2648537 : Blo 782338 2648537 := bstep (se 2 (by rfl) ⟨993201, by rfl⟩ : syracuseStep 2648537 = 1986403) B1986403
theorem B1763891 : Blo 782338 1763891 := bstep (se 1 (by rfl) ⟨1322918, by rfl⟩ : syracuseStep 1763891 = 2645837) B2645837
theorem B1174091 : Blo 782338 1174091 := bstep (se 1 (by rfl) ⟨880568, by rfl⟩ : syracuseStep 1174091 = 1761137) B1761137
theorem B1174103 : Blo 782338 1174103 := bstep (se 1 (by rfl) ⟨880577, by rfl⟩ : syracuseStep 1174103 = 1761155) B1761155
theorem B1272407 : Blo 782338 1272407 := bstep (se 1 (by rfl) ⟨954305, by rfl⟩ : syracuseStep 1272407 = 1908611) B1908611
theorem B1763927 : Blo 782338 1763927 := bstep (se 1 (by rfl) ⟨1322945, by rfl⟩ : syracuseStep 1763927 = 2645891) B2645891
theorem B1174169 : Blo 782338 1174169 := bstep (se 2 (by rfl) ⟨440313, by rfl⟩ : syracuseStep 1174169 = 880627) B880627
theorem B1174283 : Blo 782338 1174283 := bstep (se 1 (by rfl) ⟨880712, by rfl⟩ : syracuseStep 1174283 = 1761425) B1761425
theorem B1764107 : Blo 782338 1764107 := bstep (se 1 (by rfl) ⟨1323080, by rfl⟩ : syracuseStep 1764107 = 2646161) B2646161
theorem B1174295 : Blo 782338 1174295 := bstep (se 1 (by rfl) ⟨880721, by rfl⟩ : syracuseStep 1174295 = 1761443) B1761443
theorem B1764161 : Blo 782338 1764161 := bstep (se 2 (by rfl) ⟨661560, by rfl⟩ : syracuseStep 1764161 = 1323121) B1323121
theorem B1174361 : Blo 782338 1174361 := bstep (se 2 (by rfl) ⟨440385, by rfl⟩ : syracuseStep 1174361 = 880771) B880771
theorem B1174475 : Blo 782338 1174475 := bstep (se 1 (by rfl) ⟨880856, by rfl⟩ : syracuseStep 1174475 = 1761713) B1761713
theorem B1174487 : Blo 782338 1174487 := bstep (se 1 (by rfl) ⟨880865, by rfl⟩ : syracuseStep 1174487 = 1761731) B1761731
theorem B1338329 : Blo 782338 1338329 := bstep (se 2 (by rfl) ⟨501873, by rfl⟩ : syracuseStep 1338329 = 1003747) B1003747
theorem B7531481 : Blo 782338 7531481 := bstep (se 2 (by rfl) ⟨2824305, by rfl⟩ : syracuseStep 7531481 = 5648611) B5648611
theorem B1174553 : Blo 782338 1174553 := bstep (se 2 (by rfl) ⟨440457, by rfl⟩ : syracuseStep 1174553 = 880915) B880915
theorem B1764377 : Blo 782338 1764377 := bstep (se 2 (by rfl) ⟨661641, by rfl⟩ : syracuseStep 1764377 = 1323283) B1323283
theorem B2976857 : Blo 782338 2976857 := bstep (se 2 (by rfl) ⟨1116321, by rfl⟩ : syracuseStep 2976857 = 2232643) B2232643
theorem B1764467 : Blo 782338 1764467 := bstep (se 1 (by rfl) ⟨1323350, by rfl⟩ : syracuseStep 1764467 = 2646701) B2646701
theorem B1174667 : Blo 782338 1174667 := bstep (se 1 (by rfl) ⟨881000, by rfl⟩ : syracuseStep 1174667 = 1762001) B1762001
theorem B1174679 : Blo 782338 1174679 := bstep (se 1 (by rfl) ⟨881009, by rfl⟩ : syracuseStep 1174679 = 1762019) B1762019
theorem B1764503 : Blo 782338 1764503 := bstep (se 1 (by rfl) ⟨1323377, by rfl⟩ : syracuseStep 1764503 = 2646755) B2646755
theorem B2649239 : Blo 782338 2649239 := bstep (se 1 (by rfl) ⟨1986929, by rfl⟩ : syracuseStep 2649239 = 3973859) B3973859
theorem B1174745 : Blo 782338 1174745 := bstep (se 2 (by rfl) ⟨440529, by rfl⟩ : syracuseStep 1174745 = 881059) B881059
theorem B1174859 : Blo 782338 1174859 := bstep (se 1 (by rfl) ⟨881144, by rfl⟩ : syracuseStep 1174859 = 1762289) B1762289
theorem B1764683 : Blo 782338 1764683 := bstep (se 1 (by rfl) ⟨1323512, by rfl⟩ : syracuseStep 1764683 = 2647025) B2647025
theorem B1174871 : Blo 782338 1174871 := bstep (se 1 (by rfl) ⟨881153, by rfl⟩ : syracuseStep 1174871 = 1762307) B1762307
theorem B1764737 : Blo 782338 1764737 := bstep (se 2 (by rfl) ⟨661776, by rfl⟩ : syracuseStep 1764737 = 1323553) B1323553
theorem B2977175 : Blo 782338 2977175 := bstep (se 1 (by rfl) ⟨2232881, by rfl⟩ : syracuseStep 2977175 = 4465763) B4465763
theorem B1174937 : Blo 782338 1174937 := bstep (se 2 (by rfl) ⟨440601, by rfl⟩ : syracuseStep 1174937 = 881203) B881203
theorem B2420171 : Blo 782338 2420171 := bstep (se 1 (by rfl) ⟨1815128, by rfl⟩ : syracuseStep 2420171 = 3630257) B3630257
theorem B6712793 : Blo 782338 6712793 := bstep (se 2 (by rfl) ⟨2517297, by rfl⟩ : syracuseStep 6712793 = 5034595) B5034595
theorem B24440291 : Blo 782338 24440291 := bstep (se 1 (by rfl) ⟨18330218, by rfl⟩ : syracuseStep 24440291 = 36660437) B36660437
theorem B1175051 : Blo 782338 1175051 := bstep (se 1 (by rfl) ⟨881288, by rfl⟩ : syracuseStep 1175051 = 1762577) B1762577
theorem B1175063 : Blo 782338 1175063 := bstep (se 1 (by rfl) ⟨881297, by rfl⟩ : syracuseStep 1175063 = 1762595) B1762595
theorem B1175129 : Blo 782338 1175129 := bstep (se 2 (by rfl) ⟨440673, by rfl⟩ : syracuseStep 1175129 = 881347) B881347
theorem B1764953 : Blo 782338 1764953 := bstep (se 2 (by rfl) ⟨661857, by rfl⟩ : syracuseStep 1764953 = 1323715) B1323715
theorem B880267 : Blo 782338 880267 := bstep (se 1 (by rfl) ⟨660200, by rfl⟩ : syracuseStep 880267 = 1320401) B1320401
theorem B1765043 : Blo 782338 1765043 := bstep (se 1 (by rfl) ⟨1323782, by rfl⟩ : syracuseStep 1765043 = 2647565) B2647565
theorem B2649779 : Blo 782338 2649779 := bstep (se 1 (by rfl) ⟨1987334, by rfl⟩ : syracuseStep 2649779 = 3974669) B3974669
theorem B1175243 : Blo 782338 1175243 := bstep (se 1 (by rfl) ⟨881432, by rfl⟩ : syracuseStep 1175243 = 1762865) B1762865
theorem B1175255 : Blo 782338 1175255 := bstep (se 1 (by rfl) ⟨881441, by rfl⟩ : syracuseStep 1175255 = 1762883) B1762883
theorem B1765079 : Blo 782338 1765079 := bstep (se 1 (by rfl) ⟨1323809, by rfl⟩ : syracuseStep 1765079 = 2647619) B2647619
theorem B880375 : Blo 782338 880375 := bstep (se 1 (by rfl) ⟨660281, by rfl⟩ : syracuseStep 880375 = 1320563) B1320563
theorem B1175321 : Blo 782338 1175321 := bstep (se 2 (by rfl) ⟨440745, by rfl⟩ : syracuseStep 1175321 = 881491) B881491
theorem B1175435 : Blo 782338 1175435 := bstep (se 1 (by rfl) ⟨881576, by rfl⟩ : syracuseStep 1175435 = 1763153) B1763153
theorem B1765259 : Blo 782338 1765259 := bstep (se 1 (by rfl) ⟨1323944, by rfl⟩ : syracuseStep 1765259 = 2647889) B2647889
theorem B1175447 : Blo 782338 1175447 := bstep (se 1 (by rfl) ⟨881585, by rfl⟩ : syracuseStep 1175447 = 1763171) B1763171
theorem B880555 : Blo 782338 880555 := bstep (se 1 (by rfl) ⟨660416, by rfl⟩ : syracuseStep 880555 = 1320833) B1320833
theorem B1765313 : Blo 782338 1765313 := bstep (se 2 (by rfl) ⟨661992, by rfl⟩ : syracuseStep 1765313 = 1323985) B1323985
theorem B2650049 : Blo 782338 2650049 := bstep (se 2 (by rfl) ⟨993768, by rfl⟩ : syracuseStep 2650049 = 1987537) B1987537
theorem B1175513 : Blo 782338 1175513 := bstep (se 2 (by rfl) ⟨440817, by rfl⟩ : syracuseStep 1175513 = 881635) B881635
theorem B782347 : Blo 782338 782347 := bstep (se 1 (by rfl) ⟨586760, by rfl⟩ : syracuseStep 782347 = 1173521) B1173521
theorem B782359 : Blo 782338 782359 := bstep (se 1 (by rfl) ⟨586769, by rfl⟩ : syracuseStep 782359 = 1173539) B1173539
theorem B880663 : Blo 782338 880663 := bstep (se 1 (by rfl) ⟨660497, by rfl⟩ : syracuseStep 880663 = 1320995) B1320995
theorem B782379 : Blo 782338 782379 := bstep (se 1 (by rfl) ⟨586784, by rfl⟩ : syracuseStep 782379 = 1173569) B1173569
theorem B2977843 : Blo 782338 2977843 := bstep (se 1 (by rfl) ⟨2233382, by rfl⟩ : syracuseStep 2977843 = 4466765) B4466765
theorem B782391 : Blo 782338 782391 := bstep (se 1 (by rfl) ⟨586793, by rfl⟩ : syracuseStep 782391 = 1173587) B1173587
theorem B782411 : Blo 782338 782411 := bstep (se 1 (by rfl) ⟨586808, by rfl⟩ : syracuseStep 782411 = 1173617) B1173617
theorem B1175627 : Blo 782338 1175627 := bstep (se 1 (by rfl) ⟨881720, by rfl⟩ : syracuseStep 1175627 = 1763441) B1763441
theorem B782423 : Blo 782338 782423 := bstep (se 1 (by rfl) ⟨586817, by rfl⟩ : syracuseStep 782423 = 1173635) B1173635
theorem B1175639 : Blo 782338 1175639 := bstep (se 1 (by rfl) ⟨881729, by rfl⟩ : syracuseStep 1175639 = 1763459) B1763459
theorem B7336037 : Blo 782338 7336037 := bstep (se 4 (by rfl) ⟨687753, by rfl⟩ : syracuseStep 7336037 = 1375507) B1375507
theorem B782443 : Blo 782338 782443 := bstep (se 1 (by rfl) ⟨586832, by rfl⟩ : syracuseStep 782443 = 1173665) B1173665
theorem B782455 : Blo 782338 782455 := bstep (se 1 (by rfl) ⟨586841, by rfl⟩ : syracuseStep 782455 = 1173683) B1173683
theorem B782475 : Blo 782338 782475 := bstep (se 1 (by rfl) ⟨586856, by rfl⟩ : syracuseStep 782475 = 1173713) B1173713
theorem B782487 : Blo 782338 782487 := bstep (se 1 (by rfl) ⟨586865, by rfl⟩ : syracuseStep 782487 = 1173731) B1173731
theorem B1175705 : Blo 782338 1175705 := bstep (se 2 (by rfl) ⟨440889, by rfl⟩ : syracuseStep 1175705 = 881779) B881779
theorem B1765529 : Blo 782338 1765529 := bstep (se 2 (by rfl) ⟨662073, by rfl⟩ : syracuseStep 1765529 = 1324147) B1324147
theorem B782507 : Blo 782338 782507 := bstep (se 1 (by rfl) ⟨586880, by rfl⟩ : syracuseStep 782507 = 1173761) B1173761
theorem B782519 : Blo 782338 782519 := bstep (se 1 (by rfl) ⟨586889, by rfl⟩ : syracuseStep 782519 = 1173779) B1173779
theorem B782539 : Blo 782338 782539 := bstep (se 1 (by rfl) ⟨586904, by rfl⟩ : syracuseStep 782539 = 1173809) B1173809
theorem B880843 : Blo 782338 880843 := bstep (se 1 (by rfl) ⟨660632, by rfl⟩ : syracuseStep 880843 = 1321265) B1321265
theorem B782551 : Blo 782338 782551 := bstep (se 1 (by rfl) ⟨586913, by rfl⟩ : syracuseStep 782551 = 1173827) B1173827
theorem B782571 : Blo 782338 782571 := bstep (se 1 (by rfl) ⟨586928, by rfl⟩ : syracuseStep 782571 = 1173857) B1173857
theorem B1765619 : Blo 782338 1765619 := bstep (se 1 (by rfl) ⟨1324214, by rfl⟩ : syracuseStep 1765619 = 2648429) B2648429
theorem B782583 : Blo 782338 782583 := bstep (se 1 (by rfl) ⟨586937, by rfl⟩ : syracuseStep 782583 = 1173875) B1173875
theorem B782603 : Blo 782338 782603 := bstep (se 1 (by rfl) ⟨586952, by rfl⟩ : syracuseStep 782603 = 1173905) B1173905
theorem B1175819 : Blo 782338 1175819 := bstep (se 1 (by rfl) ⟨881864, by rfl⟩ : syracuseStep 1175819 = 1763729) B1763729
theorem B782615 : Blo 782338 782615 := bstep (se 1 (by rfl) ⟨586961, by rfl⟩ : syracuseStep 782615 = 1173923) B1173923
theorem B1175831 : Blo 782338 1175831 := bstep (se 1 (by rfl) ⟨881873, by rfl⟩ : syracuseStep 1175831 = 1763747) B1763747
theorem B1765655 : Blo 782338 1765655 := bstep (se 1 (by rfl) ⟨1324241, by rfl⟩ : syracuseStep 1765655 = 2648483) B2648483
theorem B782635 : Blo 782338 782635 := bstep (se 1 (by rfl) ⟨586976, by rfl⟩ : syracuseStep 782635 = 1173953) B1173953
theorem B782647 : Blo 782338 782647 := bstep (se 1 (by rfl) ⟨586985, by rfl⟩ : syracuseStep 782647 = 1173971) B1173971
theorem B880951 : Blo 782338 880951 := bstep (se 1 (by rfl) ⟨660713, by rfl⟩ : syracuseStep 880951 = 1321427) B1321427
theorem B782667 : Blo 782338 782667 := bstep (se 1 (by rfl) ⟨587000, by rfl⟩ : syracuseStep 782667 = 1174001) B1174001
theorem B782679 : Blo 782338 782679 := bstep (se 1 (by rfl) ⟨587009, by rfl⟩ : syracuseStep 782679 = 1174019) B1174019
theorem B1175897 : Blo 782338 1175897 := bstep (se 2 (by rfl) ⟨440961, by rfl⟩ : syracuseStep 1175897 = 881923) B881923
theorem B782699 : Blo 782338 782699 := bstep (se 1 (by rfl) ⟨587024, by rfl⟩ : syracuseStep 782699 = 1174049) B1174049
theorem B782711 : Blo 782338 782711 := bstep (se 1 (by rfl) ⟨587033, by rfl⟩ : syracuseStep 782711 = 1174067) B1174067
theorem B782731 : Blo 782338 782731 := bstep (se 1 (by rfl) ⟨587048, by rfl⟩ : syracuseStep 782731 = 1174097) B1174097
theorem B782743 : Blo 782338 782743 := bstep (se 1 (by rfl) ⟨587057, by rfl⟩ : syracuseStep 782743 = 1174115) B1174115
theorem B782763 : Blo 782338 782763 := bstep (se 1 (by rfl) ⟨587072, by rfl⟩ : syracuseStep 782763 = 1174145) B1174145
theorem B782775 : Blo 782338 782775 := bstep (se 1 (by rfl) ⟨587081, by rfl⟩ : syracuseStep 782775 = 1174163) B1174163
theorem B782795 : Blo 782338 782795 := bstep (se 1 (by rfl) ⟨587096, by rfl⟩ : syracuseStep 782795 = 1174193) B1174193
theorem B1176011 : Blo 782338 1176011 := bstep (se 1 (by rfl) ⟨882008, by rfl⟩ : syracuseStep 1176011 = 1764017) B1764017
theorem B1765835 : Blo 782338 1765835 := bstep (se 1 (by rfl) ⟨1324376, by rfl⟩ : syracuseStep 1765835 = 2648753) B2648753
theorem B782807 : Blo 782338 782807 := bstep (se 1 (by rfl) ⟨587105, by rfl⟩ : syracuseStep 782807 = 1174211) B1174211
theorem B1176023 : Blo 782338 1176023 := bstep (se 1 (by rfl) ⟨882017, by rfl⟩ : syracuseStep 1176023 = 1764035) B1764035
theorem B2650589 : Blo 782338 2650589 := bstep (se 3 (by rfl) ⟨496985, by rfl⟩ : syracuseStep 2650589 = 993971) B993971
theorem B782827 : Blo 782338 782827 := bstep (se 1 (by rfl) ⟨587120, by rfl⟩ : syracuseStep 782827 = 1174241) B1174241
theorem B881131 : Blo 782338 881131 := bstep (se 1 (by rfl) ⟨660848, by rfl⟩ : syracuseStep 881131 = 1321697) B1321697
theorem B782839 : Blo 782338 782839 := bstep (se 1 (by rfl) ⟨587129, by rfl⟩ : syracuseStep 782839 = 1174259) B1174259
theorem B1765889 : Blo 782338 1765889 := bstep (se 2 (by rfl) ⟨662208, by rfl⟩ : syracuseStep 1765889 = 1324417) B1324417
theorem B782859 : Blo 782338 782859 := bstep (se 1 (by rfl) ⟨587144, by rfl⟩ : syracuseStep 782859 = 1174289) B1174289
theorem B782871 : Blo 782338 782871 := bstep (se 1 (by rfl) ⟨587153, by rfl⟩ : syracuseStep 782871 = 1174307) B1174307
theorem B1176089 : Blo 782338 1176089 := bstep (se 2 (by rfl) ⟨441033, by rfl⟩ : syracuseStep 1176089 = 882067) B882067
theorem B782891 : Blo 782338 782891 := bstep (se 1 (by rfl) ⟨587168, by rfl⟩ : syracuseStep 782891 = 1174337) B1174337
theorem B782903 : Blo 782338 782903 := bstep (se 1 (by rfl) ⟨587177, by rfl⟩ : syracuseStep 782903 = 1174355) B1174355
theorem B782923 : Blo 782338 782923 := bstep (se 1 (by rfl) ⟨587192, by rfl⟩ : syracuseStep 782923 = 1174385) B1174385
theorem B782935 : Blo 782338 782935 := bstep (se 1 (by rfl) ⟨587201, by rfl⟩ : syracuseStep 782935 = 1174403) B1174403
theorem B881239 : Blo 782338 881239 := bstep (se 1 (by rfl) ⟨660929, by rfl⟩ : syracuseStep 881239 = 1321859) B1321859
theorem B782955 : Blo 782338 782955 := bstep (se 1 (by rfl) ⟨587216, by rfl⟩ : syracuseStep 782955 = 1174433) B1174433
theorem B782967 : Blo 782338 782967 := bstep (se 1 (by rfl) ⟨587225, by rfl⟩ : syracuseStep 782967 = 1174451) B1174451
theorem B782987 : Blo 782338 782987 := bstep (se 1 (by rfl) ⟨587240, by rfl⟩ : syracuseStep 782987 = 1174481) B1174481
theorem B1176203 : Blo 782338 1176203 := bstep (se 1 (by rfl) ⟨882152, by rfl⟩ : syracuseStep 1176203 = 1764305) B1764305
theorem B782999 : Blo 782338 782999 := bstep (se 1 (by rfl) ⟨587249, by rfl⟩ : syracuseStep 782999 = 1174499) B1174499
theorem B1176215 : Blo 782338 1176215 := bstep (se 1 (by rfl) ⟨882161, by rfl⟩ : syracuseStep 1176215 = 1764323) B1764323
theorem B783019 : Blo 782338 783019 := bstep (se 1 (by rfl) ⟨587264, by rfl⟩ : syracuseStep 783019 = 1174529) B1174529
theorem B783031 : Blo 782338 783031 := bstep (se 1 (by rfl) ⟨587273, by rfl⟩ : syracuseStep 783031 = 1174547) B1174547
theorem B783051 : Blo 782338 783051 := bstep (se 1 (by rfl) ⟨587288, by rfl⟩ : syracuseStep 783051 = 1174577) B1174577
theorem B783063 : Blo 782338 783063 := bstep (se 1 (by rfl) ⟨587297, by rfl⟩ : syracuseStep 783063 = 1174595) B1174595
theorem B1176281 : Blo 782338 1176281 := bstep (se 2 (by rfl) ⟨441105, by rfl⟩ : syracuseStep 1176281 = 882211) B882211
theorem B1766105 : Blo 782338 1766105 := bstep (se 2 (by rfl) ⟨662289, by rfl⟩ : syracuseStep 1766105 = 1324579) B1324579
theorem B783083 : Blo 782338 783083 := bstep (se 1 (by rfl) ⟨587312, by rfl⟩ : syracuseStep 783083 = 1174625) B1174625
theorem B783095 : Blo 782338 783095 := bstep (se 1 (by rfl) ⟨587321, by rfl⟩ : syracuseStep 783095 = 1174643) B1174643
theorem B783115 : Blo 782338 783115 := bstep (se 1 (by rfl) ⟨587336, by rfl⟩ : syracuseStep 783115 = 1174673) B1174673
theorem B881419 : Blo 782338 881419 := bstep (se 1 (by rfl) ⟨661064, by rfl⟩ : syracuseStep 881419 = 1322129) B1322129
theorem B783127 : Blo 782338 783127 := bstep (se 1 (by rfl) ⟨587345, by rfl⟩ : syracuseStep 783127 = 1174691) B1174691
theorem B783147 : Blo 782338 783147 := bstep (se 1 (by rfl) ⟨587360, by rfl⟩ : syracuseStep 783147 = 1174721) B1174721
theorem B1766195 : Blo 782338 1766195 := bstep (se 1 (by rfl) ⟨1324646, by rfl⟩ : syracuseStep 1766195 = 2649293) B2649293
theorem B783159 : Blo 782338 783159 := bstep (se 1 (by rfl) ⟨587369, by rfl⟩ : syracuseStep 783159 = 1174739) B1174739
theorem B783179 : Blo 782338 783179 := bstep (se 1 (by rfl) ⟨587384, by rfl⟩ : syracuseStep 783179 = 1174769) B1174769
theorem B1176395 : Blo 782338 1176395 := bstep (se 1 (by rfl) ⟨882296, by rfl⟩ : syracuseStep 1176395 = 1764593) B1764593
theorem B783191 : Blo 782338 783191 := bstep (se 1 (by rfl) ⟨587393, by rfl⟩ : syracuseStep 783191 = 1174787) B1174787
theorem B1176407 : Blo 782338 1176407 := bstep (se 1 (by rfl) ⟨882305, by rfl⟩ : syracuseStep 1176407 = 1764611) B1764611
theorem B1766231 : Blo 782338 1766231 := bstep (se 1 (by rfl) ⟨1324673, by rfl⟩ : syracuseStep 1766231 = 2649347) B2649347
theorem B783211 : Blo 782338 783211 := bstep (se 1 (by rfl) ⟨587408, by rfl⟩ : syracuseStep 783211 = 1174817) B1174817
theorem B783223 : Blo 782338 783223 := bstep (se 1 (by rfl) ⟨587417, by rfl⟩ : syracuseStep 783223 = 1174835) B1174835
theorem B881527 : Blo 782338 881527 := bstep (se 1 (by rfl) ⟨661145, by rfl⟩ : syracuseStep 881527 = 1322291) B1322291
theorem B783243 : Blo 782338 783243 := bstep (se 1 (by rfl) ⟨587432, by rfl⟩ : syracuseStep 783243 = 1174865) B1174865
theorem B783255 : Blo 782338 783255 := bstep (se 1 (by rfl) ⟨587441, by rfl⟩ : syracuseStep 783255 = 1174883) B1174883
theorem B3765143 : Blo 782338 3765143 := bstep (se 1 (by rfl) ⟨2823857, by rfl⟩ : syracuseStep 3765143 = 5647715) B5647715
theorem B1176473 : Blo 782338 1176473 := bstep (se 2 (by rfl) ⟨441177, by rfl⟩ : syracuseStep 1176473 = 882355) B882355
theorem B783275 : Blo 782338 783275 := bstep (se 1 (by rfl) ⟨587456, by rfl⟩ : syracuseStep 783275 = 1174913) B1174913
theorem B783287 : Blo 782338 783287 := bstep (se 1 (by rfl) ⟨587465, by rfl⟩ : syracuseStep 783287 = 1174931) B1174931
theorem B783307 : Blo 782338 783307 := bstep (se 1 (by rfl) ⟨587480, by rfl⟩ : syracuseStep 783307 = 1174961) B1174961
theorem B783319 : Blo 782338 783319 := bstep (se 1 (by rfl) ⟨587489, by rfl⟩ : syracuseStep 783319 = 1174979) B1174979
theorem B783339 : Blo 782338 783339 := bstep (se 1 (by rfl) ⟨587504, by rfl⟩ : syracuseStep 783339 = 1175009) B1175009
theorem B783351 : Blo 782338 783351 := bstep (se 1 (by rfl) ⟨587513, by rfl⟩ : syracuseStep 783351 = 1175027) B1175027
theorem B783371 : Blo 782338 783371 := bstep (se 1 (by rfl) ⟨587528, by rfl⟩ : syracuseStep 783371 = 1175057) B1175057
theorem B1176587 : Blo 782338 1176587 := bstep (se 1 (by rfl) ⟨882440, by rfl⟩ : syracuseStep 1176587 = 1764881) B1764881
theorem B1766411 : Blo 782338 1766411 := bstep (se 1 (by rfl) ⟨1324808, by rfl⟩ : syracuseStep 1766411 = 2649617) B2649617
theorem B783383 : Blo 782338 783383 := bstep (se 1 (by rfl) ⟨587537, by rfl⟩ : syracuseStep 783383 = 1175075) B1175075
theorem B1176599 : Blo 782338 1176599 := bstep (se 1 (by rfl) ⟨882449, by rfl⟩ : syracuseStep 1176599 = 1764899) B1764899
theorem B783403 : Blo 782338 783403 := bstep (se 1 (by rfl) ⟨587552, by rfl⟩ : syracuseStep 783403 = 1175105) B1175105
theorem B881707 : Blo 782338 881707 := bstep (se 1 (by rfl) ⟨661280, by rfl⟩ : syracuseStep 881707 = 1322561) B1322561
theorem B783415 : Blo 782338 783415 := bstep (se 1 (by rfl) ⟨587561, by rfl⟩ : syracuseStep 783415 = 1175123) B1175123
theorem B1766465 : Blo 782338 1766465 := bstep (se 2 (by rfl) ⟨662424, by rfl⟩ : syracuseStep 1766465 = 1324849) B1324849
theorem B783435 : Blo 782338 783435 := bstep (se 1 (by rfl) ⟨587576, by rfl⟩ : syracuseStep 783435 = 1175153) B1175153
theorem B783447 : Blo 782338 783447 := bstep (se 1 (by rfl) ⟨587585, by rfl⟩ : syracuseStep 783447 = 1175171) B1175171
theorem B1176665 : Blo 782338 1176665 := bstep (se 2 (by rfl) ⟨441249, by rfl⟩ : syracuseStep 1176665 = 882499) B882499
theorem B783467 : Blo 782338 783467 := bstep (se 1 (by rfl) ⟨587600, by rfl⟩ : syracuseStep 783467 = 1175201) B1175201
theorem B783479 : Blo 782338 783479 := bstep (se 1 (by rfl) ⟨587609, by rfl⟩ : syracuseStep 783479 = 1175219) B1175219
theorem B783499 : Blo 782338 783499 := bstep (se 1 (by rfl) ⟨587624, by rfl⟩ : syracuseStep 783499 = 1175249) B1175249
theorem B783511 : Blo 782338 783511 := bstep (se 1 (by rfl) ⟨587633, by rfl⟩ : syracuseStep 783511 = 1175267) B1175267
theorem B881815 : Blo 782338 881815 := bstep (se 1 (by rfl) ⟨661361, by rfl⟩ : syracuseStep 881815 = 1322723) B1322723
theorem B783531 : Blo 782338 783531 := bstep (se 1 (by rfl) ⟨587648, by rfl⟩ : syracuseStep 783531 = 1175297) B1175297
theorem B783543 : Blo 782338 783543 := bstep (se 1 (by rfl) ⟨587657, by rfl⟩ : syracuseStep 783543 = 1175315) B1175315
theorem B783563 : Blo 782338 783563 := bstep (se 1 (by rfl) ⟨587672, by rfl⟩ : syracuseStep 783563 = 1175345) B1175345
theorem B1176779 : Blo 782338 1176779 := bstep (se 1 (by rfl) ⟨882584, by rfl⟩ : syracuseStep 1176779 = 1765169) B1765169
theorem B783575 : Blo 782338 783575 := bstep (se 1 (by rfl) ⟨587681, by rfl⟩ : syracuseStep 783575 = 1175363) B1175363
theorem B1176791 : Blo 782338 1176791 := bstep (se 1 (by rfl) ⟨882593, by rfl⟩ : syracuseStep 1176791 = 1765187) B1765187
theorem B783595 : Blo 782338 783595 := bstep (se 1 (by rfl) ⟨587696, by rfl⟩ : syracuseStep 783595 = 1175393) B1175393
theorem B783607 : Blo 782338 783607 := bstep (se 1 (by rfl) ⟨587705, by rfl⟩ : syracuseStep 783607 = 1175411) B1175411
theorem B783627 : Blo 782338 783627 := bstep (se 1 (by rfl) ⟨587720, by rfl⟩ : syracuseStep 783627 = 1175441) B1175441
theorem B2979089 : Blo 782338 2979089 := bstep (se 2 (by rfl) ⟨1117158, by rfl⟩ : syracuseStep 2979089 = 2234317) B2234317
theorem B783639 : Blo 782338 783639 := bstep (se 1 (by rfl) ⟨587729, by rfl⟩ : syracuseStep 783639 = 1175459) B1175459
theorem B1176857 : Blo 782338 1176857 := bstep (se 2 (by rfl) ⟨441321, by rfl⟩ : syracuseStep 1176857 = 882643) B882643
theorem B1766681 : Blo 782338 1766681 := bstep (se 2 (by rfl) ⟨662505, by rfl⟩ : syracuseStep 1766681 = 1325011) B1325011
theorem B783659 : Blo 782338 783659 := bstep (se 1 (by rfl) ⟨587744, by rfl⟩ : syracuseStep 783659 = 1175489) B1175489
theorem B783671 : Blo 782338 783671 := bstep (se 1 (by rfl) ⟨587753, by rfl⟩ : syracuseStep 783671 = 1175507) B1175507
theorem B783691 : Blo 782338 783691 := bstep (se 1 (by rfl) ⟨587768, by rfl⟩ : syracuseStep 783691 = 1175537) B1175537
theorem B881995 : Blo 782338 881995 := bstep (se 1 (by rfl) ⟨661496, by rfl⟩ : syracuseStep 881995 = 1322993) B1322993
theorem B5371211 : Blo 782338 5371211 := bstep (se 1 (by rfl) ⟨4028408, by rfl⟩ : syracuseStep 5371211 = 8056817) B8056817
theorem B783703 : Blo 782338 783703 := bstep (se 1 (by rfl) ⟨587777, by rfl⟩ : syracuseStep 783703 = 1175555) B1175555
theorem B4519261 : Blo 782338 4519261 := bstep (se 3 (by rfl) ⟨847361, by rfl⟩ : syracuseStep 4519261 = 1694723) B1694723
theorem B783723 : Blo 782338 783723 := bstep (se 1 (by rfl) ⟨587792, by rfl⟩ : syracuseStep 783723 = 1175585) B1175585
theorem B1766771 : Blo 782338 1766771 := bstep (se 1 (by rfl) ⟨1325078, by rfl⟩ : syracuseStep 1766771 = 2650157) B2650157
theorem B783735 : Blo 782338 783735 := bstep (se 1 (by rfl) ⟨587801, by rfl⟩ : syracuseStep 783735 = 1175603) B1175603
theorem B783755 : Blo 782338 783755 := bstep (se 1 (by rfl) ⟨587816, by rfl⟩ : syracuseStep 783755 = 1175633) B1175633
theorem B1176971 : Blo 782338 1176971 := bstep (se 1 (by rfl) ⟨882728, by rfl⟩ : syracuseStep 1176971 = 1765457) B1765457
theorem B783767 : Blo 782338 783767 := bstep (se 1 (by rfl) ⟨587825, by rfl⟩ : syracuseStep 783767 = 1175651) B1175651
theorem B1176983 : Blo 782338 1176983 := bstep (se 1 (by rfl) ⟨882737, by rfl⟩ : syracuseStep 1176983 = 1765475) B1765475
theorem B1766807 : Blo 782338 1766807 := bstep (se 1 (by rfl) ⟨1325105, by rfl⟩ : syracuseStep 1766807 = 2650211) B2650211
theorem B783787 : Blo 782338 783787 := bstep (se 1 (by rfl) ⟨587840, by rfl⟩ : syracuseStep 783787 = 1175681) B1175681
theorem B783799 : Blo 782338 783799 := bstep (se 1 (by rfl) ⟨587849, by rfl⟩ : syracuseStep 783799 = 1175699) B1175699
theorem B882103 : Blo 782338 882103 := bstep (se 1 (by rfl) ⟨661577, by rfl⟩ : syracuseStep 882103 = 1323155) B1323155
theorem B783819 : Blo 782338 783819 := bstep (se 1 (by rfl) ⟨587864, by rfl⟩ : syracuseStep 783819 = 1175729) B1175729
theorem B783831 : Blo 782338 783831 := bstep (se 1 (by rfl) ⟨587873, by rfl⟩ : syracuseStep 783831 = 1175747) B1175747
theorem B1177049 : Blo 782338 1177049 := bstep (se 2 (by rfl) ⟨441393, by rfl⟩ : syracuseStep 1177049 = 882787) B882787
theorem B783851 : Blo 782338 783851 := bstep (se 1 (by rfl) ⟨587888, by rfl⟩ : syracuseStep 783851 = 1175777) B1175777
theorem B783863 : Blo 782338 783863 := bstep (se 1 (by rfl) ⟨587897, by rfl⟩ : syracuseStep 783863 = 1175795) B1175795
theorem B783883 : Blo 782338 783883 := bstep (se 1 (by rfl) ⟨587912, by rfl⟩ : syracuseStep 783883 = 1175825) B1175825
theorem B783895 : Blo 782338 783895 := bstep (se 1 (by rfl) ⟨587921, by rfl⟩ : syracuseStep 783895 = 1175843) B1175843
theorem B783915 : Blo 782338 783915 := bstep (se 1 (by rfl) ⟨587936, by rfl⟩ : syracuseStep 783915 = 1175873) B1175873
theorem B783927 : Blo 782338 783927 := bstep (se 1 (by rfl) ⟨587945, by rfl⟩ : syracuseStep 783927 = 1175891) B1175891
theorem B783947 : Blo 782338 783947 := bstep (se 1 (by rfl) ⟨587960, by rfl⟩ : syracuseStep 783947 = 1175921) B1175921
theorem B1177163 : Blo 782338 1177163 := bstep (se 1 (by rfl) ⟨882872, by rfl⟩ : syracuseStep 1177163 = 1765745) B1765745
theorem B1766987 : Blo 782338 1766987 := bstep (se 1 (by rfl) ⟨1325240, by rfl⟩ : syracuseStep 1766987 = 2650481) B2650481
theorem B2651723 : Blo 782338 2651723 := bstep (se 1 (by rfl) ⟨1988792, by rfl⟩ : syracuseStep 2651723 = 3977585) B3977585
theorem B783959 : Blo 782338 783959 := bstep (se 1 (by rfl) ⟨587969, by rfl⟩ : syracuseStep 783959 = 1175939) B1175939
theorem B1177175 : Blo 782338 1177175 := bstep (se 1 (by rfl) ⟨882881, by rfl⟩ : syracuseStep 1177175 = 1765763) B1765763
theorem B783979 : Blo 782338 783979 := bstep (se 1 (by rfl) ⟨587984, by rfl⟩ : syracuseStep 783979 = 1175969) B1175969
theorem B882283 : Blo 782338 882283 := bstep (se 1 (by rfl) ⟨661712, by rfl⟩ : syracuseStep 882283 = 1323425) B1323425
theorem B783991 : Blo 782338 783991 := bstep (se 1 (by rfl) ⟨587993, by rfl⟩ : syracuseStep 783991 = 1175987) B1175987
theorem B1767041 : Blo 782338 1767041 := bstep (se 2 (by rfl) ⟨662640, by rfl⟩ : syracuseStep 1767041 = 1325281) B1325281
theorem B784011 : Blo 782338 784011 := bstep (se 1 (by rfl) ⟨588008, by rfl⟩ : syracuseStep 784011 = 1176017) B1176017
theorem B3962519 : Blo 782338 3962519 := bstep (se 1 (by rfl) ⟨2971889, by rfl⟩ : syracuseStep 3962519 = 5943779) B5943779
theorem B784023 : Blo 782338 784023 := bstep (se 1 (by rfl) ⟨588017, by rfl⟩ : syracuseStep 784023 = 1176035) B1176035
theorem B1177241 : Blo 782338 1177241 := bstep (se 2 (by rfl) ⟨441465, by rfl⟩ : syracuseStep 1177241 = 882931) B882931
theorem B784043 : Blo 782338 784043 := bstep (se 1 (by rfl) ⟨588032, by rfl⟩ : syracuseStep 784043 = 1176065) B1176065
theorem B784055 : Blo 782338 784055 := bstep (se 1 (by rfl) ⟨588041, by rfl⟩ : syracuseStep 784055 = 1176083) B1176083
theorem B784075 : Blo 782338 784075 := bstep (se 1 (by rfl) ⟨588056, by rfl⟩ : syracuseStep 784075 = 1176113) B1176113
theorem B784087 : Blo 782338 784087 := bstep (se 1 (by rfl) ⟨588065, by rfl⟩ : syracuseStep 784087 = 1176131) B1176131
theorem B882391 : Blo 782338 882391 := bstep (se 1 (by rfl) ⟨661793, by rfl⟩ : syracuseStep 882391 = 1323587) B1323587
theorem B784107 : Blo 782338 784107 := bstep (se 1 (by rfl) ⟨588080, by rfl⟩ : syracuseStep 784107 = 1176161) B1176161
theorem B784119 : Blo 782338 784119 := bstep (se 1 (by rfl) ⟨588089, by rfl⟩ : syracuseStep 784119 = 1176179) B1176179
theorem B784139 : Blo 782338 784139 := bstep (se 1 (by rfl) ⟨588104, by rfl⟩ : syracuseStep 784139 = 1176209) B1176209
theorem B1177355 : Blo 782338 1177355 := bstep (se 1 (by rfl) ⟨883016, by rfl⟩ : syracuseStep 1177355 = 1766033) B1766033
theorem B6616849 : Blo 782338 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B784151 : Blo 782338 784151 := bstep (se 1 (by rfl) ⟨588113, by rfl⟩ : syracuseStep 784151 = 1176227) B1176227
theorem B1177367 : Blo 782338 1177367 := bstep (se 1 (by rfl) ⟨883025, by rfl⟩ : syracuseStep 1177367 = 1766051) B1766051
theorem B784171 : Blo 782338 784171 := bstep (se 1 (by rfl) ⟨588128, by rfl⟩ : syracuseStep 784171 = 1176257) B1176257
theorem B784183 : Blo 782338 784183 := bstep (se 1 (by rfl) ⟨588137, by rfl⟩ : syracuseStep 784183 = 1176275) B1176275
theorem B784203 : Blo 782338 784203 := bstep (se 1 (by rfl) ⟨588152, by rfl⟩ : syracuseStep 784203 = 1176305) B1176305
theorem B784215 : Blo 782338 784215 := bstep (se 1 (by rfl) ⟨588161, by rfl⟩ : syracuseStep 784215 = 1176323) B1176323
theorem B1177433 : Blo 782338 1177433 := bstep (se 2 (by rfl) ⟨441537, by rfl⟩ : syracuseStep 1177433 = 883075) B883075
theorem B1767257 : Blo 782338 1767257 := bstep (se 2 (by rfl) ⟨662721, by rfl⟩ : syracuseStep 1767257 = 1325443) B1325443
theorem B2651993 : Blo 782338 2651993 := bstep (se 2 (by rfl) ⟨994497, by rfl⟩ : syracuseStep 2651993 = 1988995) B1988995
theorem B784235 : Blo 782338 784235 := bstep (se 1 (by rfl) ⟨588176, by rfl⟩ : syracuseStep 784235 = 1176353) B1176353
theorem B784247 : Blo 782338 784247 := bstep (se 1 (by rfl) ⟨588185, by rfl⟩ : syracuseStep 784247 = 1176371) B1176371
theorem B784267 : Blo 782338 784267 := bstep (se 1 (by rfl) ⟨588200, by rfl⟩ : syracuseStep 784267 = 1176401) B1176401
theorem B882571 : Blo 782338 882571 := bstep (se 1 (by rfl) ⟨661928, by rfl⟩ : syracuseStep 882571 = 1323857) B1323857
theorem B784279 : Blo 782338 784279 := bstep (se 1 (by rfl) ⟨588209, by rfl⟩ : syracuseStep 784279 = 1176419) B1176419
theorem B784299 : Blo 782338 784299 := bstep (se 1 (by rfl) ⟨588224, by rfl⟩ : syracuseStep 784299 = 1176449) B1176449
theorem B1767347 : Blo 782338 1767347 := bstep (se 1 (by rfl) ⟨1325510, by rfl⟩ : syracuseStep 1767347 = 2651021) B2651021
theorem B784311 : Blo 782338 784311 := bstep (se 1 (by rfl) ⟨588233, by rfl⟩ : syracuseStep 784311 = 1176467) B1176467
theorem B784331 : Blo 782338 784331 := bstep (se 1 (by rfl) ⟨588248, by rfl⟩ : syracuseStep 784331 = 1176497) B1176497
theorem B2979787 : Blo 782338 2979787 := bstep (se 1 (by rfl) ⟨2234840, by rfl⟩ : syracuseStep 2979787 = 4469681) B4469681
theorem B1177547 : Blo 782338 1177547 := bstep (se 1 (by rfl) ⟨883160, by rfl⟩ : syracuseStep 1177547 = 1766321) B1766321
theorem B1767383 : Blo 782338 1767383 := bstep (se 1 (by rfl) ⟨1325537, by rfl⟩ : syracuseStep 1767383 = 2651075) B2651075
theorem B784343 : Blo 782338 784343 := bstep (se 1 (by rfl) ⟨588257, by rfl⟩ : syracuseStep 784343 = 1176515) B1176515
theorem B1177559 : Blo 782338 1177559 := bstep (se 1 (by rfl) ⟨883169, by rfl⟩ : syracuseStep 1177559 = 1766339) B1766339
theorem B784363 : Blo 782338 784363 := bstep (se 1 (by rfl) ⟨588272, by rfl⟩ : syracuseStep 784363 = 1176545) B1176545
theorem B1701875 : Blo 782338 1701875 := bstep (se 1 (by rfl) ⟨1276406, by rfl⟩ : syracuseStep 1701875 = 2552813) B2552813
theorem B784375 : Blo 782338 784375 := bstep (se 1 (by rfl) ⟨588281, by rfl⟩ : syracuseStep 784375 = 1176563) B1176563
theorem B882679 : Blo 782338 882679 := bstep (se 1 (by rfl) ⟨662009, by rfl⟩ : syracuseStep 882679 = 1324019) B1324019
theorem B784395 : Blo 782338 784395 := bstep (se 1 (by rfl) ⟨588296, by rfl⟩ : syracuseStep 784395 = 1176593) B1176593
theorem B1341463 : Blo 782338 1341463 := bstep (se 1 (by rfl) ⟨1006097, by rfl⟩ : syracuseStep 1341463 = 2012195) B2012195
theorem B784407 : Blo 782338 784407 := bstep (se 1 (by rfl) ⟨588305, by rfl⟩ : syracuseStep 784407 = 1176611) B1176611
theorem B1177625 : Blo 782338 1177625 := bstep (se 2 (by rfl) ⟨441609, by rfl⟩ : syracuseStep 1177625 = 883219) B883219
theorem B784427 : Blo 782338 784427 := bstep (se 1 (by rfl) ⟨588320, by rfl⟩ : syracuseStep 784427 = 1176641) B1176641
theorem B784439 : Blo 782338 784439 := bstep (se 1 (by rfl) ⟨588329, by rfl⟩ : syracuseStep 784439 = 1176659) B1176659
theorem B6715457 : Blo 782338 6715457 := bstep (se 2 (by rfl) ⟨2518296, by rfl⟩ : syracuseStep 6715457 = 5036593) B5036593
theorem B784459 : Blo 782338 784459 := bstep (se 1 (by rfl) ⟨588344, by rfl⟩ : syracuseStep 784459 = 1176689) B1176689
theorem B784471 : Blo 782338 784471 := bstep (se 1 (by rfl) ⟨588353, by rfl⟩ : syracuseStep 784471 = 1176707) B1176707
theorem B784491 : Blo 782338 784491 := bstep (se 1 (by rfl) ⟨588368, by rfl⟩ : syracuseStep 784491 = 1176737) B1176737
theorem B784503 : Blo 782338 784503 := bstep (se 1 (by rfl) ⟨588377, by rfl⟩ : syracuseStep 784503 = 1176755) B1176755
theorem B784523 : Blo 782338 784523 := bstep (se 1 (by rfl) ⟨588392, by rfl⟩ : syracuseStep 784523 = 1176785) B1176785
theorem B1177739 : Blo 782338 1177739 := bstep (se 1 (by rfl) ⟨883304, by rfl⟩ : syracuseStep 1177739 = 1766609) B1766609
theorem B1767563 : Blo 782338 1767563 := bstep (se 1 (by rfl) ⟨1325672, by rfl⟩ : syracuseStep 1767563 = 2651345) B2651345
theorem B784535 : Blo 782338 784535 := bstep (se 1 (by rfl) ⟨588401, by rfl⟩ : syracuseStep 784535 = 1176803) B1176803
theorem B1177751 : Blo 782338 1177751 := bstep (se 1 (by rfl) ⟨883313, by rfl⟩ : syracuseStep 1177751 = 1766627) B1766627
theorem B784555 : Blo 782338 784555 := bstep (se 1 (by rfl) ⟨588416, by rfl⟩ : syracuseStep 784555 = 1176833) B1176833
theorem B882859 : Blo 782338 882859 := bstep (se 1 (by rfl) ⟨662144, by rfl⟩ : syracuseStep 882859 = 1324289) B1324289
theorem B784567 : Blo 782338 784567 := bstep (se 1 (by rfl) ⟨588425, by rfl⟩ : syracuseStep 784567 = 1176851) B1176851
theorem B1767617 : Blo 782338 1767617 := bstep (se 2 (by rfl) ⟨662856, by rfl⟩ : syracuseStep 1767617 = 1325713) B1325713
theorem B784587 : Blo 782338 784587 := bstep (se 1 (by rfl) ⟨588440, by rfl⟩ : syracuseStep 784587 = 1176881) B1176881
theorem B784599 : Blo 782338 784599 := bstep (se 1 (by rfl) ⟨588449, by rfl⟩ : syracuseStep 784599 = 1176899) B1176899
theorem B1177817 : Blo 782338 1177817 := bstep (se 2 (by rfl) ⟨441681, by rfl⟩ : syracuseStep 1177817 = 883363) B883363
theorem B2980061 : Blo 782338 2980061 := bstep (se 3 (by rfl) ⟨558761, by rfl⟩ : syracuseStep 2980061 = 1117523) B1117523
theorem B784619 : Blo 782338 784619 := bstep (se 1 (by rfl) ⟨588464, by rfl⟩ : syracuseStep 784619 = 1176929) B1176929
theorem B784631 : Blo 782338 784631 := bstep (se 1 (by rfl) ⟨588473, by rfl⟩ : syracuseStep 784631 = 1176947) B1176947
theorem B1505537 : Blo 782338 1505537 := bstep (se 2 (by rfl) ⟨564576, by rfl⟩ : syracuseStep 1505537 = 1129153) B1129153
theorem B1341707 : Blo 782338 1341707 := bstep (se 1 (by rfl) ⟨1006280, by rfl⟩ : syracuseStep 1341707 = 2012561) B2012561
theorem B784651 : Blo 782338 784651 := bstep (se 1 (by rfl) ⟨588488, by rfl⟩ : syracuseStep 784651 = 1176977) B1176977
theorem B784663 : Blo 782338 784663 := bstep (se 1 (by rfl) ⟨588497, by rfl⟩ : syracuseStep 784663 = 1176995) B1176995
theorem B882967 : Blo 782338 882967 := bstep (se 1 (by rfl) ⟨662225, by rfl⟩ : syracuseStep 882967 = 1324451) B1324451
theorem B784683 : Blo 782338 784683 := bstep (se 1 (by rfl) ⟨588512, by rfl⟩ : syracuseStep 784683 = 1177025) B1177025
theorem B784695 : Blo 782338 784695 := bstep (se 1 (by rfl) ⟨588521, by rfl⟩ : syracuseStep 784695 = 1177043) B1177043
theorem B784715 : Blo 782338 784715 := bstep (se 1 (by rfl) ⟨588536, by rfl⟩ : syracuseStep 784715 = 1177073) B1177073
theorem B1177931 : Blo 782338 1177931 := bstep (se 1 (by rfl) ⟨883448, by rfl⟩ : syracuseStep 1177931 = 1766897) B1766897
theorem B784727 : Blo 782338 784727 := bstep (se 1 (by rfl) ⟨588545, by rfl⟩ : syracuseStep 784727 = 1177091) B1177091
theorem B1177943 : Blo 782338 1177943 := bstep (se 1 (by rfl) ⟨883457, by rfl⟩ : syracuseStep 1177943 = 1766915) B1766915
theorem B784747 : Blo 782338 784747 := bstep (se 1 (by rfl) ⟨588560, by rfl⟩ : syracuseStep 784747 = 1177121) B1177121
theorem B784759 : Blo 782338 784759 := bstep (se 1 (by rfl) ⟨588569, by rfl⟩ : syracuseStep 784759 = 1177139) B1177139
theorem B784779 : Blo 782338 784779 := bstep (se 1 (by rfl) ⟨588584, by rfl⟩ : syracuseStep 784779 = 1177169) B1177169
theorem B784791 : Blo 782338 784791 := bstep (se 1 (by rfl) ⟨588593, by rfl⟩ : syracuseStep 784791 = 1177187) B1177187
theorem B1178009 : Blo 782338 1178009 := bstep (se 2 (by rfl) ⟨441753, by rfl⟩ : syracuseStep 1178009 = 883507) B883507
theorem B1767833 : Blo 782338 1767833 := bstep (se 2 (by rfl) ⟨662937, by rfl⟩ : syracuseStep 1767833 = 1325875) B1325875
theorem B784811 : Blo 782338 784811 := bstep (se 1 (by rfl) ⟨588608, by rfl⟩ : syracuseStep 784811 = 1177217) B1177217
theorem B784823 : Blo 782338 784823 := bstep (se 1 (by rfl) ⟨588617, by rfl⟩ : syracuseStep 784823 = 1177235) B1177235
theorem B784843 : Blo 782338 784843 := bstep (se 1 (by rfl) ⟨588632, by rfl⟩ : syracuseStep 784843 = 1177265) B1177265
theorem B883147 : Blo 782338 883147 := bstep (se 1 (by rfl) ⟨662360, by rfl⟩ : syracuseStep 883147 = 1324721) B1324721
theorem B784855 : Blo 782338 784855 := bstep (se 1 (by rfl) ⟨588641, by rfl⟩ : syracuseStep 784855 = 1177283) B1177283
theorem B784875 : Blo 782338 784875 := bstep (se 1 (by rfl) ⟨588656, by rfl⟩ : syracuseStep 784875 = 1177313) B1177313
theorem B1767923 : Blo 782338 1767923 := bstep (se 1 (by rfl) ⟨1325942, by rfl⟩ : syracuseStep 1767923 = 2651885) B2651885
theorem B784887 : Blo 782338 784887 := bstep (se 1 (by rfl) ⟨588665, by rfl⟩ : syracuseStep 784887 = 1177331) B1177331
theorem B5896709 : Blo 782338 5896709 := bstep (se 4 (by rfl) ⟨552816, by rfl⟩ : syracuseStep 5896709 = 1105633) B1105633
theorem B784907 : Blo 782338 784907 := bstep (se 1 (by rfl) ⟨588680, by rfl⟩ : syracuseStep 784907 = 1177361) B1177361
theorem B1178123 : Blo 782338 1178123 := bstep (se 1 (by rfl) ⟨883592, by rfl⟩ : syracuseStep 1178123 = 1767185) B1767185
theorem B784919 : Blo 782338 784919 := bstep (se 1 (by rfl) ⟨588689, by rfl⟩ : syracuseStep 784919 = 1177379) B1177379
theorem B1178135 : Blo 782338 1178135 := bstep (se 1 (by rfl) ⟨883601, by rfl⟩ : syracuseStep 1178135 = 1767203) B1767203
theorem B1767959 : Blo 782338 1767959 := bstep (se 1 (by rfl) ⟨1325969, by rfl⟩ : syracuseStep 1767959 = 2651939) B2651939
theorem B2652695 : Blo 782338 2652695 := bstep (se 1 (by rfl) ⟨1989521, by rfl⟩ : syracuseStep 2652695 = 3979043) B3979043
theorem B784939 : Blo 782338 784939 := bstep (se 1 (by rfl) ⟨588704, by rfl⟩ : syracuseStep 784939 = 1177409) B1177409
theorem B784951 : Blo 782338 784951 := bstep (se 1 (by rfl) ⟨588713, by rfl⟩ : syracuseStep 784951 = 1177427) B1177427
theorem B883255 : Blo 782338 883255 := bstep (se 1 (by rfl) ⟨662441, by rfl⟩ : syracuseStep 883255 = 1324883) B1324883
theorem B784971 : Blo 782338 784971 := bstep (se 1 (by rfl) ⟨588728, by rfl⟩ : syracuseStep 784971 = 1177457) B1177457
theorem B784983 : Blo 782338 784983 := bstep (se 1 (by rfl) ⟨588737, by rfl⟩ : syracuseStep 784983 = 1177475) B1177475
theorem B1178201 : Blo 782338 1178201 := bstep (se 2 (by rfl) ⟨441825, by rfl⟩ : syracuseStep 1178201 = 883651) B883651
theorem B785003 : Blo 782338 785003 := bstep (se 1 (by rfl) ⟨588752, by rfl⟩ : syracuseStep 785003 = 1177505) B1177505
theorem B785015 : Blo 782338 785015 := bstep (se 1 (by rfl) ⟨588761, by rfl⟩ : syracuseStep 785015 = 1177523) B1177523
theorem B785035 : Blo 782338 785035 := bstep (se 1 (by rfl) ⟨588776, by rfl⟩ : syracuseStep 785035 = 1177553) B1177553
theorem B785047 : Blo 782338 785047 := bstep (se 1 (by rfl) ⟨588785, by rfl⟩ : syracuseStep 785047 = 1177571) B1177571
theorem B785067 : Blo 782338 785067 := bstep (se 1 (by rfl) ⟨588800, by rfl⟩ : syracuseStep 785067 = 1177601) B1177601
theorem B785079 : Blo 782338 785079 := bstep (se 1 (by rfl) ⟨588809, by rfl⟩ : syracuseStep 785079 = 1177619) B1177619
theorem B785099 : Blo 782338 785099 := bstep (se 1 (by rfl) ⟨588824, by rfl⟩ : syracuseStep 785099 = 1177649) B1177649
theorem B1178315 : Blo 782338 1178315 := bstep (se 1 (by rfl) ⟨883736, by rfl⟩ : syracuseStep 1178315 = 1767473) B1767473
theorem B1768139 : Blo 782338 1768139 := bstep (se 1 (by rfl) ⟨1326104, by rfl⟩ : syracuseStep 1768139 = 2652209) B2652209
theorem B785111 : Blo 782338 785111 := bstep (se 1 (by rfl) ⟨588833, by rfl⟩ : syracuseStep 785111 = 1177667) B1177667
theorem B1178327 : Blo 782338 1178327 := bstep (se 1 (by rfl) ⟨883745, by rfl⟩ : syracuseStep 1178327 = 1767491) B1767491
theorem B785131 : Blo 782338 785131 := bstep (se 1 (by rfl) ⟨588848, by rfl⟩ : syracuseStep 785131 = 1177697) B1177697
theorem B883435 : Blo 782338 883435 := bstep (se 1 (by rfl) ⟨662576, by rfl⟩ : syracuseStep 883435 = 1325153) B1325153
theorem B785143 : Blo 782338 785143 := bstep (se 1 (by rfl) ⟨588857, by rfl⟩ : syracuseStep 785143 = 1177715) B1177715
theorem B1768193 : Blo 782338 1768193 := bstep (se 2 (by rfl) ⟨663072, by rfl⟩ : syracuseStep 1768193 = 1326145) B1326145
theorem B785163 : Blo 782338 785163 := bstep (se 1 (by rfl) ⟨588872, by rfl⟩ : syracuseStep 785163 = 1177745) B1177745
theorem B785175 : Blo 782338 785175 := bstep (se 1 (by rfl) ⟨588881, by rfl⟩ : syracuseStep 785175 = 1177763) B1177763
theorem B1178393 : Blo 782338 1178393 := bstep (se 2 (by rfl) ⟨441897, by rfl⟩ : syracuseStep 1178393 = 883795) B883795
theorem B785195 : Blo 782338 785195 := bstep (se 1 (by rfl) ⟨588896, by rfl⟩ : syracuseStep 785195 = 1177793) B1177793
theorem B785207 : Blo 782338 785207 := bstep (se 1 (by rfl) ⟨588905, by rfl⟩ : syracuseStep 785207 = 1177811) B1177811
theorem B8584001 : Blo 782338 8584001 := bstep (se 2 (by rfl) ⟨3219000, by rfl⟩ : syracuseStep 8584001 = 6438001) B6438001
theorem B785227 : Blo 782338 785227 := bstep (se 1 (by rfl) ⟨588920, by rfl⟩ : syracuseStep 785227 = 1177841) B1177841
theorem B785239 : Blo 782338 785239 := bstep (se 1 (by rfl) ⟨588929, by rfl⟩ : syracuseStep 785239 = 1177859) B1177859
theorem B883543 : Blo 782338 883543 := bstep (se 1 (by rfl) ⟨662657, by rfl⟩ : syracuseStep 883543 = 1325315) B1325315
theorem B20380517 : Blo 782338 20380517 := bstep (se 4 (by rfl) ⟨1910673, by rfl⟩ : syracuseStep 20380517 = 3821347) B3821347
theorem B785259 : Blo 782338 785259 := bstep (se 1 (by rfl) ⟨588944, by rfl⟩ : syracuseStep 785259 = 1177889) B1177889
theorem B785271 : Blo 782338 785271 := bstep (se 1 (by rfl) ⟨588953, by rfl⟩ : syracuseStep 785271 = 1177907) B1177907
theorem B785291 : Blo 782338 785291 := bstep (se 1 (by rfl) ⟨588968, by rfl⟩ : syracuseStep 785291 = 1177937) B1177937
theorem B1178507 : Blo 782338 1178507 := bstep (se 1 (by rfl) ⟨883880, by rfl⟩ : syracuseStep 1178507 = 1767761) B1767761
theorem B2980759 : Blo 782338 2980759 := bstep (se 1 (by rfl) ⟨2235569, by rfl⟩ : syracuseStep 2980759 = 4471139) B4471139
theorem B785303 : Blo 782338 785303 := bstep (se 1 (by rfl) ⟨588977, by rfl⟩ : syracuseStep 785303 = 1177955) B1177955
theorem B1178519 : Blo 782338 1178519 := bstep (se 1 (by rfl) ⟨883889, by rfl⟩ : syracuseStep 1178519 = 1767779) B1767779
theorem B785323 : Blo 782338 785323 := bstep (se 1 (by rfl) ⟨588992, by rfl⟩ : syracuseStep 785323 = 1177985) B1177985
theorem B785335 : Blo 782338 785335 := bstep (se 1 (by rfl) ⟨589001, by rfl⟩ : syracuseStep 785335 = 1178003) B1178003
theorem B785355 : Blo 782338 785355 := bstep (se 1 (by rfl) ⟨589016, by rfl⟩ : syracuseStep 785355 = 1178033) B1178033
theorem B785367 : Blo 782338 785367 := bstep (se 1 (by rfl) ⟨589025, by rfl⟩ : syracuseStep 785367 = 1178051) B1178051
theorem B1178585 : Blo 782338 1178585 := bstep (se 2 (by rfl) ⟨441969, by rfl⟩ : syracuseStep 1178585 = 883939) B883939
theorem B1768409 : Blo 782338 1768409 := bstep (se 2 (by rfl) ⟨663153, by rfl⟩ : syracuseStep 1768409 = 1326307) B1326307
theorem B785387 : Blo 782338 785387 := bstep (se 1 (by rfl) ⟨589040, by rfl⟩ : syracuseStep 785387 = 1178081) B1178081
theorem B785399 : Blo 782338 785399 := bstep (se 1 (by rfl) ⟨589049, by rfl⟩ : syracuseStep 785399 = 1178099) B1178099
theorem B785419 : Blo 782338 785419 := bstep (se 1 (by rfl) ⟨589064, by rfl⟩ : syracuseStep 785419 = 1178129) B1178129
theorem B883723 : Blo 782338 883723 := bstep (se 1 (by rfl) ⟨662792, by rfl⟩ : syracuseStep 883723 = 1325585) B1325585
theorem B785431 : Blo 782338 785431 := bstep (se 1 (by rfl) ⟨589073, by rfl⟩ : syracuseStep 785431 = 1178147) B1178147
theorem B785451 : Blo 782338 785451 := bstep (se 1 (by rfl) ⟨589088, by rfl⟩ : syracuseStep 785451 = 1178177) B1178177
theorem B1768499 : Blo 782338 1768499 := bstep (se 1 (by rfl) ⟨1326374, by rfl⟩ : syracuseStep 1768499 = 2652749) B2652749
theorem B2653235 : Blo 782338 2653235 := bstep (se 1 (by rfl) ⟨1989926, by rfl⟩ : syracuseStep 2653235 = 3979853) B3979853
theorem B785463 : Blo 782338 785463 := bstep (se 1 (by rfl) ⟨589097, by rfl⟩ : syracuseStep 785463 = 1178195) B1178195
theorem B1866817 : Blo 782338 1866817 := bstep (se 2 (by rfl) ⟨700056, by rfl⟩ : syracuseStep 1866817 = 1400113) B1400113
theorem B785483 : Blo 782338 785483 := bstep (se 1 (by rfl) ⟨589112, by rfl⟩ : syracuseStep 785483 = 1178225) B1178225
theorem B1178699 : Blo 782338 1178699 := bstep (se 1 (by rfl) ⟨884024, by rfl⟩ : syracuseStep 1178699 = 1768049) B1768049
theorem B785495 : Blo 782338 785495 := bstep (se 1 (by rfl) ⟨589121, by rfl⟩ : syracuseStep 785495 = 1178243) B1178243
theorem B1178711 : Blo 782338 1178711 := bstep (se 1 (by rfl) ⟨884033, by rfl⟩ : syracuseStep 1178711 = 1768067) B1768067
theorem B1768535 : Blo 782338 1768535 := bstep (se 1 (by rfl) ⟨1326401, by rfl⟩ : syracuseStep 1768535 = 2652803) B2652803
theorem B785515 : Blo 782338 785515 := bstep (se 1 (by rfl) ⟨589136, by rfl⟩ : syracuseStep 785515 = 1178273) B1178273
theorem B785527 : Blo 782338 785527 := bstep (se 1 (by rfl) ⟨589145, by rfl⟩ : syracuseStep 785527 = 1178291) B1178291
theorem B883831 : Blo 782338 883831 := bstep (se 1 (by rfl) ⟨662873, by rfl⟩ : syracuseStep 883831 = 1325747) B1325747
theorem B785547 : Blo 782338 785547 := bstep (se 1 (by rfl) ⟨589160, by rfl⟩ : syracuseStep 785547 = 1178321) B1178321
theorem B785559 : Blo 782338 785559 := bstep (se 1 (by rfl) ⟨589169, by rfl⟩ : syracuseStep 785559 = 1178339) B1178339
theorem B1178777 : Blo 782338 1178777 := bstep (se 2 (by rfl) ⟨442041, by rfl⟩ : syracuseStep 1178777 = 884083) B884083
theorem B785579 : Blo 782338 785579 := bstep (se 1 (by rfl) ⟨589184, by rfl⟩ : syracuseStep 785579 = 1178369) B1178369
theorem B785591 : Blo 782338 785591 := bstep (se 1 (by rfl) ⟨589193, by rfl⟩ : syracuseStep 785591 = 1178387) B1178387
theorem B785611 : Blo 782338 785611 := bstep (se 1 (by rfl) ⟨589208, by rfl⟩ : syracuseStep 785611 = 1178417) B1178417
theorem B785623 : Blo 782338 785623 := bstep (se 1 (by rfl) ⟨589217, by rfl⟩ : syracuseStep 785623 = 1178435) B1178435
theorem B785643 : Blo 782338 785643 := bstep (se 1 (by rfl) ⟨589232, by rfl⟩ : syracuseStep 785643 = 1178465) B1178465
theorem B785655 : Blo 782338 785655 := bstep (se 1 (by rfl) ⟨589241, by rfl⟩ : syracuseStep 785655 = 1178483) B1178483
theorem B785675 : Blo 782338 785675 := bstep (se 1 (by rfl) ⟨589256, by rfl⟩ : syracuseStep 785675 = 1178513) B1178513
theorem B1178891 : Blo 782338 1178891 := bstep (se 1 (by rfl) ⟨884168, by rfl⟩ : syracuseStep 1178891 = 1768337) B1768337
theorem B1768715 : Blo 782338 1768715 := bstep (se 1 (by rfl) ⟨1326536, by rfl⟩ : syracuseStep 1768715 = 2653073) B2653073
theorem B785687 : Blo 782338 785687 := bstep (se 1 (by rfl) ⟨589265, by rfl⟩ : syracuseStep 785687 = 1178531) B1178531
theorem B1178903 : Blo 782338 1178903 := bstep (se 1 (by rfl) ⟨884177, by rfl⟩ : syracuseStep 1178903 = 1768355) B1768355
theorem B785707 : Blo 782338 785707 := bstep (se 1 (by rfl) ⟨589280, by rfl⟩ : syracuseStep 785707 = 1178561) B1178561
theorem B884011 : Blo 782338 884011 := bstep (se 1 (by rfl) ⟨663008, by rfl⟩ : syracuseStep 884011 = 1326017) B1326017
theorem B785719 : Blo 782338 785719 := bstep (se 1 (by rfl) ⟨589289, by rfl⟩ : syracuseStep 785719 = 1178579) B1178579
theorem B1768769 : Blo 782338 1768769 := bstep (se 2 (by rfl) ⟨663288, by rfl⟩ : syracuseStep 1768769 = 1326577) B1326577
theorem B2653505 : Blo 782338 2653505 := bstep (se 2 (by rfl) ⟨995064, by rfl⟩ : syracuseStep 2653505 = 1990129) B1990129
theorem B785739 : Blo 782338 785739 := bstep (se 1 (by rfl) ⟨589304, by rfl⟩ : syracuseStep 785739 = 1178609) B1178609
theorem B785751 : Blo 782338 785751 := bstep (se 1 (by rfl) ⟨589313, by rfl⟩ : syracuseStep 785751 = 1178627) B1178627
theorem B1178969 : Blo 782338 1178969 := bstep (se 2 (by rfl) ⟨442113, by rfl⟩ : syracuseStep 1178969 = 884227) B884227
theorem B785771 : Blo 782338 785771 := bstep (se 1 (by rfl) ⟨589328, by rfl⟩ : syracuseStep 785771 = 1178657) B1178657
theorem B785783 : Blo 782338 785783 := bstep (se 1 (by rfl) ⟨589337, by rfl⟩ : syracuseStep 785783 = 1178675) B1178675
theorem B785803 : Blo 782338 785803 := bstep (se 1 (by rfl) ⟨589352, by rfl⟩ : syracuseStep 785803 = 1178705) B1178705
theorem B785815 : Blo 782338 785815 := bstep (se 1 (by rfl) ⟨589361, by rfl⟩ : syracuseStep 785815 = 1178723) B1178723
theorem B884119 : Blo 782338 884119 := bstep (se 1 (by rfl) ⟨663089, by rfl⟩ : syracuseStep 884119 = 1326179) B1326179
theorem B785835 : Blo 782338 785835 := bstep (se 1 (by rfl) ⟨589376, by rfl⟩ : syracuseStep 785835 = 1178753) B1178753
theorem B785847 : Blo 782338 785847 := bstep (se 1 (by rfl) ⟨589385, by rfl⟩ : syracuseStep 785847 = 1178771) B1178771
theorem B785867 : Blo 782338 785867 := bstep (se 1 (by rfl) ⟨589400, by rfl⟩ : syracuseStep 785867 = 1178801) B1178801
theorem B1179083 : Blo 782338 1179083 := bstep (se 1 (by rfl) ⟨884312, by rfl⟩ : syracuseStep 1179083 = 1768625) B1768625
theorem B785879 : Blo 782338 785879 := bstep (se 1 (by rfl) ⟨589409, by rfl⟩ : syracuseStep 785879 = 1178819) B1178819
theorem B1179095 : Blo 782338 1179095 := bstep (se 1 (by rfl) ⟨884321, by rfl⟩ : syracuseStep 1179095 = 1768643) B1768643
theorem B785899 : Blo 782338 785899 := bstep (se 1 (by rfl) ⟨589424, by rfl⟩ : syracuseStep 785899 = 1178849) B1178849
theorem B785911 : Blo 782338 785911 := bstep (se 1 (by rfl) ⟨589433, by rfl⟩ : syracuseStep 785911 = 1178867) B1178867
theorem B785931 : Blo 782338 785931 := bstep (se 1 (by rfl) ⟨589448, by rfl⟩ : syracuseStep 785931 = 1178897) B1178897
theorem B785943 : Blo 782338 785943 := bstep (se 1 (by rfl) ⟨589457, by rfl⟩ : syracuseStep 785943 = 1178915) B1178915
theorem B1179161 : Blo 782338 1179161 := bstep (se 2 (by rfl) ⟨442185, by rfl⟩ : syracuseStep 1179161 = 884371) B884371
theorem B1768985 : Blo 782338 1768985 := bstep (se 2 (by rfl) ⟨663369, by rfl⟩ : syracuseStep 1768985 = 1326739) B1326739
theorem B785963 : Blo 782338 785963 := bstep (se 1 (by rfl) ⟨589472, by rfl⟩ : syracuseStep 785963 = 1178945) B1178945
theorem B785975 : Blo 782338 785975 := bstep (se 1 (by rfl) ⟨589481, by rfl⟩ : syracuseStep 785975 = 1178963) B1178963
theorem B785995 : Blo 782338 785995 := bstep (se 1 (by rfl) ⟨589496, by rfl⟩ : syracuseStep 785995 = 1178993) B1178993
theorem B884299 : Blo 782338 884299 := bstep (se 1 (by rfl) ⟨663224, by rfl⟩ : syracuseStep 884299 = 1326449) B1326449
theorem B786007 : Blo 782338 786007 := bstep (se 1 (by rfl) ⟨589505, by rfl⟩ : syracuseStep 786007 = 1179011) B1179011
theorem B786027 : Blo 782338 786027 := bstep (se 1 (by rfl) ⟨589520, by rfl⟩ : syracuseStep 786027 = 1179041) B1179041
theorem B1769075 : Blo 782338 1769075 := bstep (se 1 (by rfl) ⟨1326806, by rfl⟩ : syracuseStep 1769075 = 2653613) B2653613
theorem B786039 : Blo 782338 786039 := bstep (se 1 (by rfl) ⟨589529, by rfl⟩ : syracuseStep 786039 = 1179059) B1179059
theorem B786059 : Blo 782338 786059 := bstep (se 1 (by rfl) ⟨589544, by rfl⟩ : syracuseStep 786059 = 1179089) B1179089
theorem B1179275 : Blo 782338 1179275 := bstep (se 1 (by rfl) ⟨884456, by rfl⟩ : syracuseStep 1179275 = 1768913) B1768913
theorem B786071 : Blo 782338 786071 := bstep (se 1 (by rfl) ⟨589553, by rfl⟩ : syracuseStep 786071 = 1179107) B1179107
theorem B1179287 : Blo 782338 1179287 := bstep (se 1 (by rfl) ⟨884465, by rfl⟩ : syracuseStep 1179287 = 1768931) B1768931
theorem B1769111 : Blo 782338 1769111 := bstep (se 1 (by rfl) ⟨1326833, by rfl⟩ : syracuseStep 1769111 = 2653667) B2653667
theorem B786091 : Blo 782338 786091 := bstep (se 1 (by rfl) ⟨589568, by rfl⟩ : syracuseStep 786091 = 1179137) B1179137
theorem B2981549 : Blo 782338 2981549 := bstep (se 3 (by rfl) ⟨559040, by rfl⟩ : syracuseStep 2981549 = 1118081) B1118081
theorem B786103 : Blo 782338 786103 := bstep (se 1 (by rfl) ⟨589577, by rfl⟩ : syracuseStep 786103 = 1179155) B1179155
theorem B884407 : Blo 782338 884407 := bstep (se 1 (by rfl) ⟨663305, by rfl⟩ : syracuseStep 884407 = 1326611) B1326611
theorem B2227915 : Blo 782338 2227915 := bstep (se 1 (by rfl) ⟨1670936, by rfl⟩ : syracuseStep 2227915 = 3341873) B3341873
theorem B786123 : Blo 782338 786123 := bstep (se 1 (by rfl) ⟨589592, by rfl⟩ : syracuseStep 786123 = 1179185) B1179185
theorem B786135 : Blo 782338 786135 := bstep (se 1 (by rfl) ⟨589601, by rfl⟩ : syracuseStep 786135 = 1179203) B1179203
theorem B1179353 : Blo 782338 1179353 := bstep (se 2 (by rfl) ⟨442257, by rfl⟩ : syracuseStep 1179353 = 884515) B884515
theorem B786155 : Blo 782338 786155 := bstep (se 1 (by rfl) ⟨589616, by rfl⟩ : syracuseStep 786155 = 1179233) B1179233
theorem B786167 : Blo 782338 786167 := bstep (se 1 (by rfl) ⟨589625, by rfl⟩ : syracuseStep 786167 = 1179251) B1179251
theorem B786187 : Blo 782338 786187 := bstep (se 1 (by rfl) ⟨589640, by rfl⟩ : syracuseStep 786187 = 1179281) B1179281
theorem B786199 : Blo 782338 786199 := bstep (se 1 (by rfl) ⟨589649, by rfl⟩ : syracuseStep 786199 = 1179299) B1179299
theorem B786219 : Blo 782338 786219 := bstep (se 1 (by rfl) ⟨589664, by rfl⟩ : syracuseStep 786219 = 1179329) B1179329
theorem B3342131 : Blo 782338 3342131 := bstep (se 1 (by rfl) ⟨2506598, by rfl⟩ : syracuseStep 3342131 = 5013197) B5013197
theorem B786231 : Blo 782338 786231 := bstep (se 1 (by rfl) ⟨589673, by rfl⟩ : syracuseStep 786231 = 1179347) B1179347
theorem B5013323 : Blo 782338 5013323 := bstep (se 1 (by rfl) ⟨3759992, by rfl⟩ : syracuseStep 5013323 = 7519985) B7519985
theorem B786251 : Blo 782338 786251 := bstep (se 1 (by rfl) ⟨589688, by rfl⟩ : syracuseStep 786251 = 1179377) B1179377
theorem B1179467 : Blo 782338 1179467 := bstep (se 1 (by rfl) ⟨884600, by rfl⟩ : syracuseStep 1179467 = 1769201) B1769201
theorem B786263 : Blo 782338 786263 := bstep (se 1 (by rfl) ⟨589697, by rfl⟩ : syracuseStep 786263 = 1179395) B1179395
theorem B1179479 : Blo 782338 1179479 := bstep (se 1 (by rfl) ⟨884609, by rfl⟩ : syracuseStep 1179479 = 1769219) B1769219
theorem B786283 : Blo 782338 786283 := bstep (se 1 (by rfl) ⟨589712, by rfl⟩ : syracuseStep 786283 = 1179425) B1179425
theorem B884587 : Blo 782338 884587 := bstep (se 1 (by rfl) ⟨663440, by rfl⟩ : syracuseStep 884587 = 1326881) B1326881
theorem B786295 : Blo 782338 786295 := bstep (se 1 (by rfl) ⟨589721, by rfl⟩ : syracuseStep 786295 = 1179443) B1179443
theorem B786315 : Blo 782338 786315 := bstep (se 1 (by rfl) ⟨589736, by rfl⟩ : syracuseStep 786315 = 1179473) B1179473
theorem B3178385 : Blo 782338 3178385 := bstep (se 2 (by rfl) ⟨1191894, by rfl⟩ : syracuseStep 3178385 = 2383789) B2383789
theorem B786327 : Blo 782338 786327 := bstep (se 1 (by rfl) ⟨589745, by rfl⟩ : syracuseStep 786327 = 1179491) B1179491
theorem B3342455 : Blo 782338 3342455 := bstep (se 1 (by rfl) ⟨2506841, by rfl⟩ : syracuseStep 3342455 = 5013683) B5013683
theorem B1114231 : Blo 782338 1114231 := bstep (se 1 (by rfl) ⟨835673, by rfl⟩ : syracuseStep 1114231 = 1671347) B1671347
theorem B1507513 : Blo 782338 1507513 := bstep (se 2 (by rfl) ⟨565317, by rfl⟩ : syracuseStep 1507513 = 1130635) B1130635
theorem B28639433 : Blo 782338 28639433 := bstep (se 2 (by rfl) ⟨10739787, by rfl⟩ : syracuseStep 28639433 = 21479575) B21479575
theorem B4456741 : Blo 782338 4456741 := bstep (se 4 (by rfl) ⟨417819, by rfl⟩ : syracuseStep 4456741 = 835639) B835639
theorem B2982203 : Blo 782338 2982203 := bstep (se 1 (by rfl) ⟨2236652, by rfl⟩ : syracuseStep 2982203 = 4473305) B4473305
theorem B3965273 : Blo 782338 3965273 := bstep (se 2 (by rfl) ⟨1486977, by rfl⟩ : syracuseStep 3965273 = 2973955) B2973955
theorem B28574045 : Blo 782338 28574045 := bstep (se 3 (by rfl) ⟨5357633, by rfl⟩ : syracuseStep 28574045 = 10715267) B10715267
theorem B3768875 : Blo 782338 3768875 := bstep (se 1 (by rfl) ⟨2826656, by rfl⟩ : syracuseStep 3768875 = 5653313) B5653313
theorem B2982689 : Blo 782338 2982689 := bstep (se 2 (by rfl) ⟨1118508, by rfl⟩ : syracuseStep 2982689 = 2237017) B2237017
theorem B76251941 : Blo 782338 76251941 := bstep (se 4 (by rfl) ⟨7148619, by rfl⟩ : syracuseStep 76251941 = 14297239) B14297239
theorem B4457267 : Blo 782338 4457267 := bstep (se 1 (by rfl) ⟨3342950, by rfl⟩ : syracuseStep 4457267 = 6685901) B6685901
theorem B1115051 : Blo 782338 1115051 := bstep (se 1 (by rfl) ⟨836288, by rfl⟩ : syracuseStep 1115051 = 1672577) B1672577
theorem B3015767 : Blo 782338 3015767 := bstep (se 1 (by rfl) ⟨2261825, by rfl⟩ : syracuseStep 3015767 = 4523651) B4523651
theorem B2229761 : Blo 782338 2229761 := bstep (se 2 (by rfl) ⟨836160, by rfl⟩ : syracuseStep 2229761 = 1672321) B1672321
theorem B2229875 : Blo 782338 2229875 := bstep (se 1 (by rfl) ⟨1672406, by rfl⟩ : syracuseStep 2229875 = 3344813) B3344813
theorem B2983661 : Blo 782338 2983661 := bstep (se 3 (by rfl) ⟨559436, by rfl⟩ : syracuseStep 2983661 = 1118873) B1118873
theorem B3344129 : Blo 782338 3344129 := bstep (se 2 (by rfl) ⟨1254048, by rfl⟩ : syracuseStep 3344129 = 2508097) B2508097
theorem B3770297 : Blo 782338 3770297 := bstep (se 2 (by rfl) ⟨1413861, by rfl⟩ : syracuseStep 3770297 = 2827723) B2827723
theorem B2230217 : Blo 782338 2230217 := bstep (se 2 (by rfl) ⟨836331, by rfl⟩ : syracuseStep 2230217 = 1672663) B1672663
theorem B2983979 : Blo 782338 2983979 := bstep (se 1 (by rfl) ⟨2237984, by rfl⟩ : syracuseStep 2983979 = 4475969) B4475969
theorem B4458725 : Blo 782338 4458725 := bstep (se 4 (by rfl) ⟨418005, by rfl⟩ : syracuseStep 4458725 = 836011) B836011
theorem B3967379 : Blo 782338 3967379 := bstep (se 1 (by rfl) ⟨2975534, by rfl⟩ : syracuseStep 3967379 = 5951069) B5951069
theorem B3770833 : Blo 782338 3770833 := bstep (se 2 (by rfl) ⟨1414062, by rfl⟩ : syracuseStep 3770833 = 2828125) B2828125
theorem B6687299 : Blo 782338 6687299 := bstep (se 1 (by rfl) ⟨5015474, by rfl⟩ : syracuseStep 6687299 = 10030949) B10030949
theorem B1673875 : Blo 782338 1673875 := bstep (se 1 (by rfl) ⟨1255406, by rfl⟩ : syracuseStep 1673875 = 2510813) B2510813
theorem B1116919 : Blo 782338 1116919 := bstep (se 1 (by rfl) ⟨837689, by rfl⟩ : syracuseStep 1116919 = 1675379) B1675379
theorem B12716837 : Blo 782338 12716837 := bstep (se 4 (by rfl) ⟨1192203, by rfl⟩ : syracuseStep 12716837 = 2384407) B2384407
theorem B10062629 : Blo 782338 10062629 := bstep (se 4 (by rfl) ⟨943371, by rfl⟩ : syracuseStep 10062629 = 1886743) B1886743
theorem B1411987 : Blo 782338 1411987 := bstep (se 1 (by rfl) ⟨1058990, by rfl⟩ : syracuseStep 1411987 = 2117981) B2117981
theorem B19106965 : Blo 782338 19106965 := bstep (se 6 (by rfl) ⟨447819, by rfl⟩ : syracuseStep 19106965 = 895639) B895639
theorem B2821321 : Blo 782338 2821321 := bstep (se 2 (by rfl) ⟨1057995, by rfl⟩ : syracuseStep 2821321 = 2115991) B2115991
theorem B3181805 : Blo 782338 3181805 := bstep (se 3 (by rfl) ⟨596588, by rfl⟩ : syracuseStep 3181805 = 1193177) B1193177
theorem B2821435 : Blo 782338 2821435 := bstep (se 1 (by rfl) ⟨2116076, by rfl⟩ : syracuseStep 2821435 = 4232153) B4232153
theorem B3870011 : Blo 782338 3870011 := bstep (se 1 (by rfl) ⟨2902508, by rfl⟩ : syracuseStep 3870011 = 5805017) B5805017
theorem B1117967 : Blo 782338 1117967 := bstep (se 1 (by rfl) ⟨838475, by rfl⟩ : syracuseStep 1117967 = 1676951) B1676951
theorem B2232107 : Blo 782338 2232107 := bstep (se 1 (by rfl) ⟨1674080, by rfl⟩ : syracuseStep 2232107 = 3348161) B3348161
theorem B3772295 : Blo 782338 3772295 := bstep (se 1 (by rfl) ⟨2829221, by rfl⟩ : syracuseStep 3772295 = 5658443) B5658443
theorem B2232335 : Blo 782338 2232335 := bstep (se 1 (by rfl) ⟨1674251, by rfl⟩ : syracuseStep 2232335 = 3348503) B3348503
theorem B1118281 : Blo 782338 1118281 := bstep (se 2 (by rfl) ⟨419355, by rfl⟩ : syracuseStep 1118281 = 838711) B838711
theorem B108532061 : Blo 782338 108532061 := bstep (se 3 (by rfl) ⟨20349761, by rfl⟩ : syracuseStep 108532061 = 40699523) B40699523
theorem B1675721 : Blo 782338 1675721 := bstep (se 2 (by rfl) ⟨628395, by rfl⟩ : syracuseStep 1675721 = 1256791) B1256791
theorem B2036267 : Blo 782338 2036267 := bstep (se 1 (by rfl) ⟨1527200, by rfl⟩ : syracuseStep 2036267 = 3054401) B3054401
theorem B1413947 : Blo 782338 1413947 := bstep (se 1 (by rfl) ⟨1060460, by rfl⟩ : syracuseStep 1413947 = 2120921) B2120921
theorem B2233747 : Blo 782338 2233747 := bstep (se 1 (by rfl) ⟨1675310, by rfl⟩ : syracuseStep 2233747 = 3350621) B3350621
theorem B3970457 : Blo 782338 3970457 := bstep (se 2 (by rfl) ⟨1488921, by rfl⟩ : syracuseStep 3970457 = 2977843) B2977843
theorem B2233975 : Blo 782338 2233975 := bstep (se 1 (by rfl) ⟨1675481, by rfl⟩ : syracuseStep 2233975 = 3350963) B3350963
theorem B1414841 : Blo 782338 1414841 := bstep (se 2 (by rfl) ⟨530565, by rfl⟩ : syracuseStep 1414841 = 1061131) B1061131
theorem B4233019 : Blo 782338 4233019 := bstep (se 1 (by rfl) ⟨3174764, by rfl⟩ : syracuseStep 4233019 = 6349529) B6349529
theorem B1415303 : Blo 782338 1415303 := bstep (se 1 (by rfl) ⟨1061477, by rfl⟩ : syracuseStep 1415303 = 2122955) B2122955
theorem B1677839 : Blo 782338 1677839 := bstep (se 1 (by rfl) ⟨1258379, by rfl⟩ : syracuseStep 1677839 = 2516759) B2516759
theorem B36313667 : Blo 782338 36313667 := bstep (se 1 (by rfl) ⟨27235250, by rfl⟩ : syracuseStep 36313667 = 54470501) B54470501
theorem B5970509 : Blo 782338 5970509 := bstep (se 3 (by rfl) ⟨1119470, by rfl⟩ : syracuseStep 5970509 = 2238941) B2238941
theorem B10066625 : Blo 782338 10066625 := bstep (se 2 (by rfl) ⟨3774984, by rfl⟩ : syracuseStep 10066625 = 7549969) B7549969
theorem B6691673 : Blo 782338 6691673 := bstep (se 2 (by rfl) ⟨2509377, by rfl⟩ : syracuseStep 6691673 = 5018755) B5018755
theorem B2235251 : Blo 782338 2235251 := bstep (se 1 (by rfl) ⟨1676438, by rfl⟩ : syracuseStep 2235251 = 3352877) B3352877
theorem B2235593 : Blo 782338 2235593 := bstep (se 2 (by rfl) ⟨838347, by rfl⟩ : syracuseStep 2235593 = 1676695) B1676695
theorem B5020987 : Blo 782338 5020987 := bstep (se 1 (by rfl) ⟨3765740, by rfl⟩ : syracuseStep 5020987 = 7531481) B7531481
theorem B2235707 : Blo 782338 2235707 := bstep (se 1 (by rfl) ⟨1676780, by rfl⟩ : syracuseStep 2235707 = 3353561) B3353561
theorem B2825587 : Blo 782338 2825587 := bstep (se 1 (by rfl) ⟨2119190, by rfl⟩ : syracuseStep 2825587 = 4238381) B4238381
theorem B2235833 : Blo 782338 2235833 := bstep (se 2 (by rfl) ⟨838437, by rfl⟩ : syracuseStep 2235833 = 1676875) B1676875
theorem B1613447 : Blo 782338 1613447 := bstep (se 1 (by rfl) ⟨1210085, by rfl⟩ : syracuseStep 1613447 = 2420171) B2420171
theorem B16293527 : Blo 782338 16293527 := bstep (se 1 (by rfl) ⟨12220145, by rfl⟩ : syracuseStep 16293527 = 24440291) B24440291
theorem B8822465 : Blo 782338 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B991111 : Blo 782338 991111 := bstep (se 1 (by rfl) ⟨743333, by rfl⟩ : syracuseStep 991111 = 1486667) B1486667
theorem B3973049 : Blo 782338 3973049 := bstep (se 2 (by rfl) ⟨1489893, by rfl⟩ : syracuseStep 3973049 = 2979787) B2979787
theorem B4890691 : Blo 782338 4890691 := bstep (se 1 (by rfl) ⟨3668018, by rfl⟩ : syracuseStep 4890691 = 7336037) B7336037
theorem B1253561 : Blo 782338 1253561 := bstep (se 2 (by rfl) ⟨470085, by rfl⟩ : syracuseStep 1253561 = 940171) B940171
theorem B991531 : Blo 782338 991531 := bstep (se 1 (by rfl) ⟨743648, by rfl⟩ : syracuseStep 991531 = 1487297) B1487297
theorem B991759 : Blo 782338 991759 := bstep (se 1 (by rfl) ⟨743819, by rfl⟩ : syracuseStep 991759 = 1487639) B1487639
theorem B1254023 : Blo 782338 1254023 := bstep (se 1 (by rfl) ⟨940517, by rfl⟩ : syracuseStep 1254023 = 1881035) B1881035
theorem B3580807 : Blo 782338 3580807 := bstep (se 1 (by rfl) ⟨2685605, by rfl⟩ : syracuseStep 3580807 = 5371211) B5371211
theorem B3351563 : Blo 782338 3351563 := bstep (se 1 (by rfl) ⟨2513672, by rfl⟩ : syracuseStep 3351563 = 5027345) B5027345
theorem B2237483 : Blo 782338 2237483 := bstep (se 1 (by rfl) ⟨1678112, by rfl⟩ : syracuseStep 2237483 = 3356225) B3356225
theorem B3974345 : Blo 782338 3974345 := bstep (se 2 (by rfl) ⟨1490379, by rfl⟩ : syracuseStep 3974345 = 2980759) B2980759
theorem B992503 : Blo 782338 992503 := bstep (se 1 (by rfl) ⟨744377, by rfl⟩ : syracuseStep 992503 = 1488755) B1488755
theorem B7546243 : Blo 782338 7546243 := bstep (se 1 (by rfl) ⟨5659682, by rfl⟩ : syracuseStep 7546243 = 11319365) B11319365
theorem B3024263 : Blo 782338 3024263 := bstep (se 1 (by rfl) ⟨2268197, by rfl⟩ : syracuseStep 3024263 = 4536395) B4536395
theorem B1254971 : Blo 782338 1254971 := bstep (se 1 (by rfl) ⟨941228, by rfl⟩ : syracuseStep 1254971 = 1882457) B1882457
theorem B992827 : Blo 782338 992827 := bstep (se 1 (by rfl) ⟨744620, by rfl⟩ : syracuseStep 992827 = 1489241) B1489241
theorem B1320583 : Blo 782338 1320583 := bstep (se 1 (by rfl) ⟨990437, by rfl⟩ : syracuseStep 1320583 = 1980875) B1980875
theorem B4466447 : Blo 782338 4466447 := bstep (se 1 (by rfl) ⟨3349835, by rfl⟩ : syracuseStep 4466447 = 6699671) B6699671
theorem B2238475 : Blo 782338 2238475 := bstep (se 1 (by rfl) ⟨1678856, by rfl⟩ : syracuseStep 2238475 = 3357713) B3357713
theorem B993323 : Blo 782338 993323 := bstep (se 1 (by rfl) ⟨744992, by rfl⟩ : syracuseStep 993323 = 1489985) B1489985
theorem B1321231 : Blo 782338 1321231 := bstep (se 1 (by rfl) ⟨990923, by rfl⟩ : syracuseStep 1321231 = 1981847) B1981847
theorem B2238749 : Blo 782338 2238749 := bstep (se 3 (by rfl) ⟨419765, by rfl⟩ : syracuseStep 2238749 = 839531) B839531
theorem B993799 : Blo 782338 993799 := bstep (se 1 (by rfl) ⟨745349, by rfl⟩ : syracuseStep 993799 = 1490699) B1490699
theorem B8956493 : Blo 782338 8956493 := bstep (se 3 (by rfl) ⟨1679342, by rfl⟩ : syracuseStep 8956493 = 3358685) B3358685
theorem B1190647 : Blo 782338 1190647 := bstep (se 1 (by rfl) ⟨892985, by rfl⟩ : syracuseStep 1190647 = 1785971) B1785971
theorem B1485611 : Blo 782338 1485611 := bstep (se 1 (by rfl) ⟨1114208, by rfl⟩ : syracuseStep 1485611 = 2228417) B2228417
theorem B1321771 : Blo 782338 1321771 := bstep (se 1 (by rfl) ⟨991328, by rfl⟩ : syracuseStep 1321771 = 1982657) B1982657
theorem B3353491 : Blo 782338 3353491 := bstep (se 1 (by rfl) ⟨2515118, by rfl⟩ : syracuseStep 3353491 = 5030237) B5030237
theorem B11447203 : Blo 782338 11447203 := bstep (se 1 (by rfl) ⟨8585402, by rfl⟩ : syracuseStep 11447203 = 17170805) B17170805
theorem B1321913 : Blo 782338 1321913 := bstep (se 2 (by rfl) ⟨495717, by rfl⟩ : syracuseStep 1321913 = 991435) B991435
theorem B994295 : Blo 782338 994295 := bstep (se 1 (by rfl) ⟨745721, by rfl⟩ : syracuseStep 994295 = 1491443) B1491443
theorem B1485839 : Blo 782338 1485839 := bstep (se 1 (by rfl) ⟨1114379, by rfl⟩ : syracuseStep 1485839 = 2228759) B2228759
theorem B994447 : Blo 782338 994447 := bstep (se 1 (by rfl) ⟨745835, by rfl⟩ : syracuseStep 994447 = 1491671) B1491671
theorem B4467905 : Blo 782338 4467905 := bstep (se 2 (by rfl) ⟨1675464, by rfl⟩ : syracuseStep 4467905 = 3350929) B3350929
theorem B994619 : Blo 782338 994619 := bstep (se 1 (by rfl) ⟨745964, by rfl⟩ : syracuseStep 994619 = 1491929) B1491929
theorem B1322615 : Blo 782338 1322615 := bstep (se 1 (by rfl) ⟨991961, by rfl⟩ : syracuseStep 1322615 = 1983923) B1983923
theorem B15249221 : Blo 782338 15249221 := bstep (se 4 (by rfl) ⟨1429614, by rfl⟩ : syracuseStep 15249221 = 2859229) B2859229
theorem B1191851 : Blo 782338 1191851 := bstep (se 1 (by rfl) ⟨893888, by rfl⟩ : syracuseStep 1191851 = 1787777) B1787777
theorem B6041623 : Blo 782338 6041623 := bstep (se 1 (by rfl) ⟨4531217, by rfl⟩ : syracuseStep 6041623 = 9062435) B9062435
theorem B1323067 : Blo 782338 1323067 := bstep (se 1 (by rfl) ⟨992300, by rfl⟩ : syracuseStep 1323067 = 1984601) B1984601
theorem B1323209 : Blo 782338 1323209 := bstep (se 2 (by rfl) ⟨496203, by rfl⟩ : syracuseStep 1323209 = 992407) B992407
theorem B4305241 : Blo 782338 4305241 := bstep (se 2 (by rfl) ⟨1614465, by rfl⟩ : syracuseStep 4305241 = 3228931) B3228931
theorem B3354995 : Blo 782338 3354995 := bstep (se 1 (by rfl) ⟨2516246, by rfl⟩ : syracuseStep 3354995 = 5032493) B5032493
theorem B1487251 : Blo 782338 1487251 := bstep (se 1 (by rfl) ⟨1115438, by rfl⟩ : syracuseStep 1487251 = 2230877) B2230877
theorem B6369835 : Blo 782338 6369835 := bstep (se 1 (by rfl) ⟨4777376, by rfl⟩ : syracuseStep 6369835 = 9554753) B9554753
theorem B1487479 : Blo 782338 1487479 := bstep (se 1 (by rfl) ⟨1115609, by rfl⟩ : syracuseStep 1487479 = 2231219) B2231219
theorem B8925875 : Blo 782338 8925875 := bstep (se 1 (by rfl) ⟨6694406, by rfl⟩ : syracuseStep 8925875 = 13388813) B13388813
theorem B3355337 : Blo 782338 3355337 := bstep (se 2 (by rfl) ⟨1258251, by rfl⟩ : syracuseStep 3355337 = 2516503) B2516503
theorem B1323911 : Blo 782338 1323911 := bstep (se 1 (by rfl) ⟨992933, by rfl⟩ : syracuseStep 1323911 = 1985867) B1985867
theorem B3355577 : Blo 782338 3355577 := bstep (se 2 (by rfl) ⟨1258341, by rfl⟩ : syracuseStep 3355577 = 2516683) B2516683
theorem B3814411 : Blo 782338 3814411 := bstep (se 1 (by rfl) ⟨2860808, by rfl⟩ : syracuseStep 3814411 = 5721617) B5721617
theorem B10040381 : Blo 782338 10040381 := bstep (se 3 (by rfl) ⟨1882571, by rfl⟩ : syracuseStep 10040381 = 3765143) B3765143
theorem B3355937 : Blo 782338 3355937 := bstep (se 2 (by rfl) ⟨1258476, by rfl⟩ : syracuseStep 3355937 = 2516953) B2516953
theorem B1324559 : Blo 782338 1324559 := bstep (se 1 (by rfl) ⟨993419, by rfl⟩ : syracuseStep 1324559 = 1986839) B1986839
theorem B9647923 : Blo 782338 9647923 := bstep (se 1 (by rfl) ⟨7235942, by rfl⟩ : syracuseStep 9647923 = 14471885) B14471885
theorem B28686149 : Blo 782338 28686149 := bstep (se 4 (by rfl) ⟨2689326, by rfl⟩ : syracuseStep 28686149 = 5378653) B5378653
theorem B29407093 : Blo 782338 29407093 := bstep (se 5 (by rfl) ⟨1378457, by rfl⟩ : syracuseStep 29407093 = 2756915) B2756915
theorem B1325099 : Blo 782338 1325099 := bstep (se 1 (by rfl) ⟨993824, by rfl⟩ : syracuseStep 1325099 = 1987649) B1987649
theorem B1554491 : Blo 782338 1554491 := bstep (se 1 (by rfl) ⟨1165868, by rfl⟩ : syracuseStep 1554491 = 2331737) B2331737
theorem B1980551 : Blo 782338 1980551 := bstep (se 1 (by rfl) ⟨1485413, by rfl⟩ : syracuseStep 1980551 = 2970827) B2970827
theorem B1489043 : Blo 782338 1489043 := bstep (se 1 (by rfl) ⟨1116782, by rfl⟩ : syracuseStep 1489043 = 2233565) B2233565
theorem B1489097 : Blo 782338 1489097 := bstep (se 2 (by rfl) ⟨558411, by rfl⟩ : syracuseStep 1489097 = 1116823) B1116823
theorem B3356909 : Blo 782338 3356909 := bstep (se 3 (by rfl) ⟨629420, by rfl⟩ : syracuseStep 3356909 = 1258841) B1258841
theorem B1980683 : Blo 782338 1980683 := bstep (se 1 (by rfl) ⟨1485512, by rfl⟩ : syracuseStep 1980683 = 2971025) B2971025
theorem B1489195 : Blo 782338 1489195 := bstep (se 1 (by rfl) ⟨1116896, by rfl⟩ : syracuseStep 1489195 = 2233793) B2233793
theorem B1325497 : Blo 782338 1325497 := bstep (se 2 (by rfl) ⟨497061, by rfl⟩ : syracuseStep 1325497 = 994123) B994123
theorem B1489423 : Blo 782338 1489423 := bstep (se 1 (by rfl) ⟨1117067, by rfl⟩ : syracuseStep 1489423 = 2234135) B2234135
theorem B3357251 : Blo 782338 3357251 := bstep (se 1 (by rfl) ⟨2517938, by rfl⟩ : syracuseStep 3357251 = 5035877) B5035877
theorem B1981199 : Blo 782338 1981199 := bstep (se 1 (by rfl) ⟨1485899, by rfl⟩ : syracuseStep 1981199 = 2971799) B2971799
theorem B3980177 : Blo 782338 3980177 := bstep (se 2 (by rfl) ⟨1492566, by rfl⟩ : syracuseStep 3980177 = 2985133) B2985133
theorem B1981331 : Blo 782338 1981331 := bstep (se 1 (by rfl) ⟨1485998, by rfl⟩ : syracuseStep 1981331 = 2971997) B2971997
theorem B1326199 : Blo 782338 1326199 := bstep (se 1 (by rfl) ⟨994649, by rfl⟩ : syracuseStep 1326199 = 1989299) B1989299
theorem B4242689 : Blo 782338 4242689 := bstep (se 2 (by rfl) ⟨1591008, by rfl⟩ : syracuseStep 4242689 = 3182017) B3182017
theorem B1326395 : Blo 782338 1326395 := bstep (se 1 (by rfl) ⟨994796, by rfl⟩ : syracuseStep 1326395 = 1989593) B1989593
theorem B1326793 : Blo 782338 1326793 := bstep (se 2 (by rfl) ⟨497547, by rfl⟩ : syracuseStep 1326793 = 995095) B995095
theorem B4472779 : Blo 782338 4472779 := bstep (se 1 (by rfl) ⟨3354584, by rfl⟩ : syracuseStep 4472779 = 6709169) B6709169
theorem B4538333 : Blo 782338 4538333 := bstep (se 3 (by rfl) ⟨850937, by rfl⟩ : syracuseStep 4538333 = 1701875) B1701875
theorem B1982465 : Blo 782338 1982465 := bstep (se 2 (by rfl) ⟨743424, by rfl⟩ : syracuseStep 1982465 = 1486849) B1486849
theorem B1490987 : Blo 782338 1490987 := bstep (se 1 (by rfl) ⟨1118240, by rfl⟩ : syracuseStep 1490987 = 2236481) B2236481
theorem B9519191 : Blo 782338 9519191 := bstep (se 1 (by rfl) ⟨7139393, by rfl⟩ : syracuseStep 9519191 = 14278787) B14278787
theorem B1982839 : Blo 782338 1982839 := bstep (se 1 (by rfl) ⟨1487129, by rfl⟩ : syracuseStep 1982839 = 2974259) B2974259
theorem B1983275 : Blo 782338 1983275 := bstep (se 1 (by rfl) ⟨1487456, by rfl⟩ : syracuseStep 1983275 = 2974913) B2974913
theorem B4768571 : Blo 782338 4768571 := bstep (se 1 (by rfl) ⟨3576428, by rfl⟩ : syracuseStep 4768571 = 7152857) B7152857
theorem B2507635 : Blo 782338 2507635 := bstep (se 1 (by rfl) ⟨1880726, by rfl⟩ : syracuseStep 2507635 = 3761453) B3761453
theorem B3818387 : Blo 782338 3818387 := bstep (se 1 (by rfl) ⟨2863790, by rfl⟩ : syracuseStep 3818387 = 5727581) B5727581
theorem B1885331 : Blo 782338 1885331 := bstep (se 1 (by rfl) ⟨1413998, by rfl⟩ : syracuseStep 1885331 = 2827997) B2827997
theorem B4244957 : Blo 782338 4244957 := bstep (se 3 (by rfl) ⟨795929, by rfl⟩ : syracuseStep 4244957 = 1591859) B1591859
theorem B5031467 : Blo 782338 5031467 := bstep (se 1 (by rfl) ⟨3773600, by rfl⟩ : syracuseStep 5031467 = 7547201) B7547201
theorem B3393085 : Blo 782338 3393085 := bstep (se 3 (by rfl) ⟨636203, by rfl⟩ : syracuseStep 3393085 = 1272407) B1272407
theorem B1984115 : Blo 782338 1984115 := bstep (se 1 (by rfl) ⟨1488086, by rfl⟩ : syracuseStep 1984115 = 2976173) B2976173
theorem B1984135 : Blo 782338 1984135 := bstep (se 1 (by rfl) ⟨1488101, by rfl⟩ : syracuseStep 1984135 = 2976203) B2976203
theorem B1492681 : Blo 782338 1492681 := bstep (se 2 (by rfl) ⟨559755, by rfl⟩ : syracuseStep 1492681 = 1119511) B1119511
theorem B1984409 : Blo 782338 1984409 := bstep (se 2 (by rfl) ⟨744153, by rfl⟩ : syracuseStep 1984409 = 1488307) B1488307
theorem B1984571 : Blo 782338 1984571 := bstep (se 1 (by rfl) ⟨1488428, by rfl⟩ : syracuseStep 1984571 = 2976857) B2976857
theorem B7260293 : Blo 782338 7260293 := bstep (se 4 (by rfl) ⟨680652, by rfl⟩ : syracuseStep 7260293 = 1361305) B1361305
theorem B1984783 : Blo 782338 1984783 := bstep (se 1 (by rfl) ⟨1488587, by rfl⟩ : syracuseStep 1984783 = 2977175) B2977175
theorem B4475195 : Blo 782338 4475195 := bstep (se 1 (by rfl) ⟨3356396, by rfl⟩ : syracuseStep 4475195 = 6712793) B6712793
theorem B838031 : Blo 782338 838031 := bstep (se 1 (by rfl) ⟨628523, by rfl⟩ : syracuseStep 838031 = 1257047) B1257047
theorem B1985057 : Blo 782338 1985057 := bstep (se 2 (by rfl) ⟨744396, by rfl⟩ : syracuseStep 1985057 = 1488793) B1488793
theorem B838279 : Blo 782338 838279 := bstep (se 1 (by rfl) ⟨628709, by rfl⟩ : syracuseStep 838279 = 1257419) B1257419
theorem B1788617 : Blo 782338 1788617 := bstep (se 2 (by rfl) ⟨670731, by rfl⟩ : syracuseStep 1788617 = 1341463) B1341463
theorem B2116381 : Blo 782338 2116381 := bstep (se 3 (by rfl) ⟨396821, by rfl⟩ : syracuseStep 2116381 = 793643) B793643
theorem B7654193 : Blo 782338 7654193 := bstep (se 2 (by rfl) ⟨2870322, by rfl⟩ : syracuseStep 7654193 = 5740645) B5740645
theorem B5360701 : Blo 782338 5360701 := bstep (se 3 (by rfl) ⟨1005131, by rfl⟩ : syracuseStep 5360701 = 2010263) B2010263
theorem B1986059 : Blo 782338 1986059 := bstep (se 1 (by rfl) ⟨1489544, by rfl⟩ : syracuseStep 1986059 = 2979089) B2979089
theorem B8474341 : Blo 782338 8474341 := bstep (se 4 (by rfl) ⟨794469, by rfl⟩ : syracuseStep 8474341 = 1588939) B1588939
theorem B4476653 : Blo 782338 4476653 := bstep (se 3 (by rfl) ⟨839372, by rfl⟩ : syracuseStep 4476653 = 1678745) B1678745
theorem B2641679 : Blo 782338 2641679 := bstep (se 1 (by rfl) ⟨1981259, by rfl⟩ : syracuseStep 2641679 = 3962519) B3962519
theorem B13553477 : Blo 782338 13553477 := bstep (se 4 (by rfl) ⟨1270638, by rfl⟩ : syracuseStep 13553477 = 2541277) B2541277
theorem B2641949 : Blo 782338 2641949 := bstep (se 3 (by rfl) ⟨495365, by rfl⟩ : syracuseStep 2641949 = 990731) B990731
theorem B4476971 : Blo 782338 4476971 := bstep (se 1 (by rfl) ⟨3357728, by rfl⟩ : syracuseStep 4476971 = 6715457) B6715457
theorem B1986707 : Blo 782338 1986707 := bstep (se 1 (by rfl) ⟨1490030, by rfl⟩ : syracuseStep 1986707 = 2980061) B2980061
theorem B1003691 : Blo 782338 1003691 := bstep (se 1 (by rfl) ⟨752768, by rfl⟩ : syracuseStep 1003691 = 1505537) B1505537
theorem B1987001 : Blo 782338 1987001 := bstep (se 2 (by rfl) ⟨745125, by rfl⟩ : syracuseStep 1987001 = 1490251) B1490251
theorem B2118089 : Blo 782338 2118089 := bstep (se 2 (by rfl) ⟨794283, by rfl⟩ : syracuseStep 2118089 = 1588567) B1588567
theorem B5722667 : Blo 782338 5722667 := bstep (se 1 (by rfl) ⟨4292000, by rfl⟩ : syracuseStep 5722667 = 8584001) B8584001
theorem B13587011 : Blo 782338 13587011 := bstep (se 1 (by rfl) ⟨10190258, by rfl⟩ : syracuseStep 13587011 = 20380517) B20380517
theorem B1888915 : Blo 782338 1888915 := bstep (se 1 (by rfl) ⟨1416686, by rfl⟩ : syracuseStep 1888915 = 2833373) B2833373
theorem B7525057 : Blo 782338 7525057 := bstep (se 2 (by rfl) ⟨2821896, by rfl⟩ : syracuseStep 7525057 = 5643793) B5643793
theorem B2970553 : Blo 782338 2970553 := bstep (se 2 (by rfl) ⟨1113957, by rfl⟩ : syracuseStep 2970553 = 2227915) B2227915
theorem B30626885 : Blo 782338 30626885 := bstep (se 4 (by rfl) ⟨2871270, by rfl⟩ : syracuseStep 30626885 = 5742541) B5742541
theorem B1987699 : Blo 782338 1987699 := bstep (se 1 (by rfl) ⟨1490774, by rfl⟩ : syracuseStep 1987699 = 2981549) B2981549
theorem B1987841 : Blo 782338 1987841 := bstep (se 2 (by rfl) ⟨745440, by rfl⟩ : syracuseStep 1987841 = 1490881) B1490881
theorem B2118923 : Blo 782338 2118923 := bstep (se 1 (by rfl) ⟨1589192, by rfl⟩ : syracuseStep 2118923 = 3178385) B3178385
theorem B5363003 : Blo 782338 5363003 := bstep (se 1 (by rfl) ⟨4022252, by rfl⟩ : syracuseStep 5363003 = 8044505) B8044505
theorem B2643353 : Blo 782338 2643353 := bstep (se 2 (by rfl) ⟨991257, by rfl⟩ : syracuseStep 2643353 = 1982515) B1982515
theorem B4478429 : Blo 782338 4478429 := bstep (se 3 (by rfl) ⟨839705, by rfl⟩ : syracuseStep 4478429 = 1679411) B1679411
theorem B4773437 : Blo 782338 4773437 := bstep (se 3 (by rfl) ⟨895019, by rfl⟩ : syracuseStep 4773437 = 1790039) B1790039
theorem B1988297 : Blo 782338 1988297 := bstep (se 2 (by rfl) ⟨745611, by rfl⟩ : syracuseStep 1988297 = 1491223) B1491223
theorem B1988651 : Blo 782338 1988651 := bstep (se 1 (by rfl) ⟨1491488, by rfl⟩ : syracuseStep 1988651 = 2982977) B2982977
theorem B2644055 : Blo 782338 2644055 := bstep (se 1 (by rfl) ⟨1983041, by rfl⟩ : syracuseStep 2644055 = 3966083) B3966083
theorem B16963829 : Blo 782338 16963829 := bstep (se 5 (by rfl) ⟨795179, by rfl⟩ : syracuseStep 16963829 = 1590359) B1590359
theorem B18143729 : Blo 782338 18143729 := bstep (se 2 (by rfl) ⟨6803898, by rfl⟩ : syracuseStep 18143729 = 13607797) B13607797
theorem B2644541 : Blo 782338 2644541 := bstep (se 3 (by rfl) ⟨495851, by rfl⟩ : syracuseStep 2644541 = 991703) B991703
theorem B1989643 : Blo 782338 1989643 := bstep (se 1 (by rfl) ⟨1492232, by rfl⟩ : syracuseStep 1989643 = 2984465) B2984465
theorem B1989785 : Blo 782338 1989785 := bstep (se 2 (by rfl) ⟨746169, by rfl⟩ : syracuseStep 1989785 = 1492339) B1492339
theorem B1989947 : Blo 782338 1989947 := bstep (se 1 (by rfl) ⟨1492460, by rfl⟩ : syracuseStep 1989947 = 2984921) B2984921
theorem B16997809 : Blo 782338 16997809 := bstep (se 2 (by rfl) ⟨6374178, by rfl⟩ : syracuseStep 16997809 = 12748357) B12748357
theorem B1760903 : Blo 782338 1760903 := bstep (se 1 (by rfl) ⟨1320677, by rfl⟩ : syracuseStep 1760903 = 2641355) B2641355
theorem B1990291 : Blo 782338 1990291 := bstep (se 1 (by rfl) ⟨1492718, by rfl⟩ : syracuseStep 1990291 = 2985437) B2985437
theorem B2973455 : Blo 782338 2973455 := bstep (se 1 (by rfl) ⟨2230091, by rfl⟩ : syracuseStep 2973455 = 4460183) B4460183
theorem B1761083 : Blo 782338 1761083 := bstep (se 1 (by rfl) ⟨1320812, by rfl⟩ : syracuseStep 1761083 = 2641625) B2641625
theorem B5955443 : Blo 782338 5955443 := bstep (se 1 (by rfl) ⟨4466582, by rfl⟩ : syracuseStep 5955443 = 8933165) B8933165
theorem B941959 : Blo 782338 941959 := bstep (se 1 (by rfl) ⟨706469, by rfl⟩ : syracuseStep 941959 = 1412939) B1412939
theorem B1761209 : Blo 782338 1761209 := bstep (se 2 (by rfl) ⟨660453, by rfl⟩ : syracuseStep 1761209 = 1320907) B1320907
theorem B2645945 : Blo 782338 2645945 := bstep (se 2 (by rfl) ⟨992229, by rfl⟩ : syracuseStep 2645945 = 1984459) B1984459
theorem B14344237 : Blo 782338 14344237 := bstep (se 3 (by rfl) ⟨2689544, by rfl⟩ : syracuseStep 14344237 = 5379089) B5379089
theorem B14311541 : Blo 782338 14311541 := bstep (se 5 (by rfl) ⟨670853, by rfl⟩ : syracuseStep 14311541 = 1341707) B1341707
theorem B1007759 : Blo 782338 1007759 := bstep (se 1 (by rfl) ⟨755819, by rfl⟩ : syracuseStep 1007759 = 1511639) B1511639
theorem B1761551 : Blo 782338 1761551 := bstep (se 1 (by rfl) ⟨1321163, by rfl⟩ : syracuseStep 1761551 = 2642327) B2642327
theorem B1761569 : Blo 782338 1761569 := bstep (se 2 (by rfl) ⟨660588, by rfl⟩ : syracuseStep 1761569 = 1321177) B1321177
theorem B2417015 : Blo 782338 2417015 := bstep (se 1 (by rfl) ⟨1812761, by rfl⟩ : syracuseStep 2417015 = 3625523) B3625523
theorem B2646539 : Blo 782338 2646539 := bstep (se 1 (by rfl) ⟨1984904, by rfl⟩ : syracuseStep 2646539 = 3969809) B3969809
theorem B16114211 : Blo 782338 16114211 := bstep (se 1 (by rfl) ⟨12085658, by rfl⟩ : syracuseStep 16114211 = 24171317) B24171317
theorem B1761911 : Blo 782338 1761911 := bstep (se 1 (by rfl) ⟨1321433, by rfl⟩ : syracuseStep 1761911 = 2642867) B2642867
theorem B2646647 : Blo 782338 2646647 := bstep (se 1 (by rfl) ⟨1984985, by rfl⟩ : syracuseStep 2646647 = 3969971) B3969971
theorem B1762091 : Blo 782338 1762091 := bstep (se 1 (by rfl) ⟨1321568, by rfl⟩ : syracuseStep 1762091 = 2643137) B2643137
theorem B1762451 : Blo 782338 1762451 := bstep (se 1 (by rfl) ⟨1321838, by rfl⟩ : syracuseStep 1762451 = 2643677) B2643677
theorem B1762505 : Blo 782338 1762505 := bstep (se 2 (by rfl) ⟨660939, by rfl⟩ : syracuseStep 1762505 = 1321879) B1321879
theorem B2647241 : Blo 782338 2647241 := bstep (se 2 (by rfl) ⟨992715, by rfl⟩ : syracuseStep 2647241 = 1985431) B1985431
theorem B2418295 : Blo 782338 2418295 := bstep (se 1 (by rfl) ⟨1813721, by rfl⟩ : syracuseStep 2418295 = 3627443) B3627443
theorem B1763207 : Blo 782338 1763207 := bstep (se 1 (by rfl) ⟨1322405, by rfl⟩ : syracuseStep 1763207 = 2644811) B2644811
theorem B2647943 : Blo 782338 2647943 := bstep (se 1 (by rfl) ⟨1985957, by rfl⟩ : syracuseStep 2647943 = 3971915) B3971915
theorem B1173563 : Blo 782338 1173563 := bstep (se 1 (by rfl) ⟨880172, by rfl⟩ : syracuseStep 1173563 = 1760345) B1760345
theorem B1763387 : Blo 782338 1763387 := bstep (se 1 (by rfl) ⟨1322540, by rfl⟩ : syracuseStep 1763387 = 2645081) B2645081
theorem B1173623 : Blo 782338 1173623 := bstep (se 1 (by rfl) ⟨880217, by rfl⟩ : syracuseStep 1173623 = 1760435) B1760435
theorem B1173647 : Blo 782338 1173647 := bstep (se 1 (by rfl) ⟨880235, by rfl⟩ : syracuseStep 1173647 = 1760471) B1760471
theorem B1173689 : Blo 782338 1173689 := bstep (se 2 (by rfl) ⟨440133, by rfl⟩ : syracuseStep 1173689 = 880267) B880267
theorem B1763513 : Blo 782338 1763513 := bstep (se 2 (by rfl) ⟨661317, by rfl⟩ : syracuseStep 1763513 = 1322635) B1322635
theorem B2648321 : Blo 782338 2648321 := bstep (se 2 (by rfl) ⟨993120, by rfl⟩ : syracuseStep 2648321 = 1986241) B1986241
theorem B1173767 : Blo 782338 1173767 := bstep (se 1 (by rfl) ⟨880325, by rfl⟩ : syracuseStep 1173767 = 1760651) B1760651
theorem B1173803 : Blo 782338 1173803 := bstep (se 1 (by rfl) ⟨880352, by rfl⟩ : syracuseStep 1173803 = 1760705) B1760705
theorem B4778299 : Blo 782338 4778299 := bstep (se 1 (by rfl) ⟨3583724, by rfl⟩ : syracuseStep 4778299 = 7167449) B7167449
theorem B1173833 : Blo 782338 1173833 := bstep (se 2 (by rfl) ⟨440187, by rfl⟩ : syracuseStep 1173833 = 880375) B880375
theorem B1173947 : Blo 782338 1173947 := bstep (se 1 (by rfl) ⟨880460, by rfl⟩ : syracuseStep 1173947 = 1760921) B1760921
theorem B1174007 : Blo 782338 1174007 := bstep (se 1 (by rfl) ⟨880505, by rfl⟩ : syracuseStep 1174007 = 1761011) B1761011
theorem B1206775 : Blo 782338 1206775 := bstep (se 1 (by rfl) ⟨905081, by rfl⟩ : syracuseStep 1206775 = 1810163) B1810163
theorem B1174031 : Blo 782338 1174031 := bstep (se 1 (by rfl) ⟨880523, by rfl⟩ : syracuseStep 1174031 = 1761047) B1761047
theorem B1763855 : Blo 782338 1763855 := bstep (se 1 (by rfl) ⟨1322891, by rfl⟩ : syracuseStep 1763855 = 2645783) B2645783
theorem B1763873 : Blo 782338 1763873 := bstep (se 2 (by rfl) ⟨661452, by rfl⟩ : syracuseStep 1763873 = 1322905) B1322905
theorem B1174073 : Blo 782338 1174073 := bstep (se 2 (by rfl) ⟨440277, by rfl⟩ : syracuseStep 1174073 = 880555) B880555
theorem B1174151 : Blo 782338 1174151 := bstep (se 1 (by rfl) ⟨880613, by rfl⟩ : syracuseStep 1174151 = 1761227) B1761227
theorem B1174187 : Blo 782338 1174187 := bstep (se 1 (by rfl) ⟨880640, by rfl⟩ : syracuseStep 1174187 = 1761281) B1761281
theorem B1174217 : Blo 782338 1174217 := bstep (se 2 (by rfl) ⟨440331, by rfl⟩ : syracuseStep 1174217 = 880663) B880663
theorem B1174331 : Blo 782338 1174331 := bstep (se 1 (by rfl) ⟨880748, by rfl⟩ : syracuseStep 1174331 = 1761497) B1761497
theorem B1698619 : Blo 782338 1698619 := bstep (se 1 (by rfl) ⟨1273964, by rfl⟩ : syracuseStep 1698619 = 2547929) B2547929
theorem B2517875 : Blo 782338 2517875 := bstep (se 1 (by rfl) ⟨1888406, by rfl⟩ : syracuseStep 2517875 = 3776813) B3776813
theorem B1174391 : Blo 782338 1174391 := bstep (se 1 (by rfl) ⟨880793, by rfl⟩ : syracuseStep 1174391 = 1761587) B1761587
theorem B1764215 : Blo 782338 1764215 := bstep (se 1 (by rfl) ⟨1323161, by rfl⟩ : syracuseStep 1764215 = 2646323) B2646323
theorem B1174415 : Blo 782338 1174415 := bstep (se 1 (by rfl) ⟨880811, by rfl⟩ : syracuseStep 1174415 = 1761623) B1761623
theorem B2976659 : Blo 782338 2976659 := bstep (se 1 (by rfl) ⟨2232494, by rfl⟩ : syracuseStep 2976659 = 4464989) B4464989
theorem B1174457 : Blo 782338 1174457 := bstep (se 2 (by rfl) ⟨440421, by rfl⟩ : syracuseStep 1174457 = 880843) B880843
theorem B9956357 : Blo 782338 9956357 := bstep (se 4 (by rfl) ⟨933408, by rfl⟩ : syracuseStep 9956357 = 1866817) B1866817
theorem B1174535 : Blo 782338 1174535 := bstep (se 1 (by rfl) ⟨880901, by rfl⟩ : syracuseStep 1174535 = 1761803) B1761803
theorem B1174571 : Blo 782338 1174571 := bstep (se 1 (by rfl) ⟨880928, by rfl⟩ : syracuseStep 1174571 = 1761857) B1761857
theorem B1764395 : Blo 782338 1764395 := bstep (se 1 (by rfl) ⟨1323296, by rfl⟩ : syracuseStep 1764395 = 2646593) B2646593
theorem B2649131 : Blo 782338 2649131 := bstep (se 1 (by rfl) ⟨1986848, by rfl⟩ : syracuseStep 2649131 = 3973697) B3973697
theorem B1174601 : Blo 782338 1174601 := bstep (se 2 (by rfl) ⟨440475, by rfl⟩ : syracuseStep 1174601 = 880951) B880951
theorem B1174715 : Blo 782338 1174715 := bstep (se 1 (by rfl) ⟨881036, by rfl⟩ : syracuseStep 1174715 = 1762073) B1762073
theorem B1174775 : Blo 782338 1174775 := bstep (se 1 (by rfl) ⟨881081, by rfl⟩ : syracuseStep 1174775 = 1762163) B1762163
theorem B1174799 : Blo 782338 1174799 := bstep (se 1 (by rfl) ⟨881099, by rfl⟩ : syracuseStep 1174799 = 1762199) B1762199
theorem B1174841 : Blo 782338 1174841 := bstep (se 2 (by rfl) ⟨440565, by rfl⟩ : syracuseStep 1174841 = 881131) B881131
theorem B1174919 : Blo 782338 1174919 := bstep (se 1 (by rfl) ⟨881189, by rfl⟩ : syracuseStep 1174919 = 1762379) B1762379
theorem B1764755 : Blo 782338 1764755 := bstep (se 1 (by rfl) ⟨1323566, by rfl⟩ : syracuseStep 1764755 = 2647133) B2647133
theorem B1174955 : Blo 782338 1174955 := bstep (se 1 (by rfl) ⟨881216, by rfl⟩ : syracuseStep 1174955 = 1762433) B1762433
theorem B1174985 : Blo 782338 1174985 := bstep (se 2 (by rfl) ⟨440619, by rfl⟩ : syracuseStep 1174985 = 881239) B881239
theorem B1764809 : Blo 782338 1764809 := bstep (se 2 (by rfl) ⟨661803, by rfl⟩ : syracuseStep 1764809 = 1323607) B1323607
theorem B4779467 : Blo 782338 4779467 := bstep (se 1 (by rfl) ⟨3584600, by rfl⟩ : syracuseStep 4779467 = 7169201) B7169201
theorem B1175099 : Blo 782338 1175099 := bstep (se 1 (by rfl) ⟨881324, by rfl⟩ : syracuseStep 1175099 = 1762649) B1762649
theorem B5664323 : Blo 782338 5664323 := bstep (se 1 (by rfl) ⟨4248242, by rfl⟩ : syracuseStep 5664323 = 8496485) B8496485
theorem B1175159 : Blo 782338 1175159 := bstep (se 1 (by rfl) ⟨881369, by rfl⟩ : syracuseStep 1175159 = 1762739) B1762739
theorem B1175183 : Blo 782338 1175183 := bstep (se 1 (by rfl) ⟨881387, by rfl⟩ : syracuseStep 1175183 = 1762775) B1762775
theorem B1175225 : Blo 782338 1175225 := bstep (se 2 (by rfl) ⟨440709, by rfl⟩ : syracuseStep 1175225 = 881419) B881419
theorem B6352613 : Blo 782338 6352613 := bstep (se 4 (by rfl) ⟨595557, by rfl⟩ : syracuseStep 6352613 = 1191115) B1191115
theorem B1175303 : Blo 782338 1175303 := bstep (se 1 (by rfl) ⟨881477, by rfl⟩ : syracuseStep 1175303 = 1762955) B1762955
theorem B1175339 : Blo 782338 1175339 := bstep (se 1 (by rfl) ⟨881504, by rfl⟩ : syracuseStep 1175339 = 1763009) B1763009
theorem B1175369 : Blo 782338 1175369 := bstep (se 2 (by rfl) ⟨440763, by rfl⟩ : syracuseStep 1175369 = 881527) B881527
theorem B880519 : Blo 782338 880519 := bstep (se 1 (by rfl) ⟨660389, by rfl⟩ : syracuseStep 880519 = 1320779) B1320779
theorem B1175483 : Blo 782338 1175483 := bstep (se 1 (by rfl) ⟨881612, by rfl⟩ : syracuseStep 1175483 = 1763225) B1763225
theorem B1175543 : Blo 782338 1175543 := bstep (se 1 (by rfl) ⟨881657, by rfl⟩ : syracuseStep 1175543 = 1763315) B1763315
theorem B782343 : Blo 782338 782343 := bstep (se 1 (by rfl) ⟨586757, by rfl⟩ : syracuseStep 782343 = 1173515) B1173515
theorem B782351 : Blo 782338 782351 := bstep (se 1 (by rfl) ⟨586763, by rfl⟩ : syracuseStep 782351 = 1173527) B1173527
theorem B1175567 : Blo 782338 1175567 := bstep (se 1 (by rfl) ⟨881675, by rfl⟩ : syracuseStep 1175567 = 1763351) B1763351
theorem B1175609 : Blo 782338 1175609 := bstep (se 2 (by rfl) ⟨440853, by rfl⟩ : syracuseStep 1175609 = 881707) B881707
theorem B782395 : Blo 782338 782395 := bstep (se 1 (by rfl) ⟨586796, by rfl⟩ : syracuseStep 782395 = 1173593) B1173593
theorem B880699 : Blo 782338 880699 := bstep (se 1 (by rfl) ⟨660524, by rfl⟩ : syracuseStep 880699 = 1321049) B1321049
theorem B3960899 : Blo 782338 3960899 := bstep (se 1 (by rfl) ⟨2970674, by rfl⟩ : syracuseStep 3960899 = 5941349) B5941349
theorem B1765511 : Blo 782338 1765511 := bstep (se 1 (by rfl) ⟨1324133, by rfl⟩ : syracuseStep 1765511 = 2648267) B2648267
theorem B782471 : Blo 782338 782471 := bstep (se 1 (by rfl) ⟨586853, by rfl⟩ : syracuseStep 782471 = 1173707) B1173707
theorem B1175687 : Blo 782338 1175687 := bstep (se 1 (by rfl) ⟨881765, by rfl⟩ : syracuseStep 1175687 = 1763531) B1763531
theorem B782479 : Blo 782338 782479 := bstep (se 1 (by rfl) ⟨586859, by rfl⟩ : syracuseStep 782479 = 1173719) B1173719
theorem B1175723 : Blo 782338 1175723 := bstep (se 1 (by rfl) ⟨881792, by rfl⟩ : syracuseStep 1175723 = 1763585) B1763585
theorem B782523 : Blo 782338 782523 := bstep (se 1 (by rfl) ⟨586892, by rfl⟩ : syracuseStep 782523 = 1173785) B1173785
theorem B1175753 : Blo 782338 1175753 := bstep (se 2 (by rfl) ⟨440907, by rfl⟩ : syracuseStep 1175753 = 881815) B881815
theorem B782599 : Blo 782338 782599 := bstep (se 1 (by rfl) ⟨586949, by rfl⟩ : syracuseStep 782599 = 1173899) B1173899
theorem B782607 : Blo 782338 782607 := bstep (se 1 (by rfl) ⟨586955, by rfl⟩ : syracuseStep 782607 = 1173911) B1173911
theorem B782651 : Blo 782338 782651 := bstep (se 1 (by rfl) ⟨586988, by rfl⟩ : syracuseStep 782651 = 1173977) B1173977
theorem B1175867 : Blo 782338 1175867 := bstep (se 1 (by rfl) ⟨881900, by rfl⟩ : syracuseStep 1175867 = 1763801) B1763801
theorem B1765691 : Blo 782338 1765691 := bstep (se 1 (by rfl) ⟨1324268, by rfl⟩ : syracuseStep 1765691 = 2648537) B2648537
theorem B2650427 : Blo 782338 2650427 := bstep (se 1 (by rfl) ⟨1987820, by rfl⟩ : syracuseStep 2650427 = 3975641) B3975641
theorem B1175927 : Blo 782338 1175927 := bstep (se 1 (by rfl) ⟨881945, by rfl⟩ : syracuseStep 1175927 = 1763891) B1763891
theorem B3961223 : Blo 782338 3961223 := bstep (se 1 (by rfl) ⟨2970917, by rfl⟩ : syracuseStep 3961223 = 5941835) B5941835
theorem B782727 : Blo 782338 782727 := bstep (se 1 (by rfl) ⟨587045, by rfl⟩ : syracuseStep 782727 = 1174091) B1174091
theorem B782735 : Blo 782338 782735 := bstep (se 1 (by rfl) ⟨587051, by rfl⟩ : syracuseStep 782735 = 1174103) B1174103
theorem B1175951 : Blo 782338 1175951 := bstep (se 1 (by rfl) ⟨881963, by rfl⟩ : syracuseStep 1175951 = 1763927) B1763927
theorem B1175993 : Blo 782338 1175993 := bstep (se 2 (by rfl) ⟨440997, by rfl⟩ : syracuseStep 1175993 = 881995) B881995
theorem B4026809 : Blo 782338 4026809 := bstep (se 2 (by rfl) ⟨1510053, by rfl⟩ : syracuseStep 4026809 = 3020107) B3020107
theorem B782779 : Blo 782338 782779 := bstep (se 1 (by rfl) ⟨587084, by rfl⟩ : syracuseStep 782779 = 1174169) B1174169
theorem B1765817 : Blo 782338 1765817 := bstep (se 2 (by rfl) ⟨662181, by rfl⟩ : syracuseStep 1765817 = 1324363) B1324363
theorem B6025681 : Blo 782338 6025681 := bstep (se 2 (by rfl) ⟨2259630, by rfl⟩ : syracuseStep 6025681 = 4519261) B4519261
theorem B14283229 : Blo 782338 14283229 := bstep (se 3 (by rfl) ⟨2678105, by rfl⟩ : syracuseStep 14283229 = 5356211) B5356211
theorem B782855 : Blo 782338 782855 := bstep (se 1 (by rfl) ⟨587141, by rfl⟩ : syracuseStep 782855 = 1174283) B1174283
theorem B1176071 : Blo 782338 1176071 := bstep (se 1 (by rfl) ⟨882053, by rfl⟩ : syracuseStep 1176071 = 1764107) B1764107
theorem B2978315 : Blo 782338 2978315 := bstep (se 1 (by rfl) ⟨2233736, by rfl⟩ : syracuseStep 2978315 = 4467473) B4467473
theorem B782863 : Blo 782338 782863 := bstep (se 1 (by rfl) ⟨587147, by rfl⟩ : syracuseStep 782863 = 1174295) B1174295
theorem B881167 : Blo 782338 881167 := bstep (se 1 (by rfl) ⟨660875, by rfl⟩ : syracuseStep 881167 = 1321751) B1321751
theorem B1176107 : Blo 782338 1176107 := bstep (se 1 (by rfl) ⟨882080, by rfl⟩ : syracuseStep 1176107 = 1764161) B1764161
theorem B782907 : Blo 782338 782907 := bstep (se 1 (by rfl) ⟨587180, by rfl⟩ : syracuseStep 782907 = 1174361) B1174361
theorem B1176137 : Blo 782338 1176137 := bstep (se 2 (by rfl) ⟨441051, by rfl⟩ : syracuseStep 1176137 = 882103) B882103
theorem B782983 : Blo 782338 782983 := bstep (se 1 (by rfl) ⟨587237, by rfl⟩ : syracuseStep 782983 = 1174475) B1174475
theorem B782991 : Blo 782338 782991 := bstep (se 1 (by rfl) ⟨587243, by rfl⟩ : syracuseStep 782991 = 1174487) B1174487
theorem B783035 : Blo 782338 783035 := bstep (se 1 (by rfl) ⟨587276, by rfl⟩ : syracuseStep 783035 = 1174553) B1174553
theorem B1176251 : Blo 782338 1176251 := bstep (se 1 (by rfl) ⟨882188, by rfl⟩ : syracuseStep 1176251 = 1764377) B1764377
theorem B1176311 : Blo 782338 1176311 := bstep (se 1 (by rfl) ⟨882233, by rfl⟩ : syracuseStep 1176311 = 1764467) B1764467
theorem B783111 : Blo 782338 783111 := bstep (se 1 (by rfl) ⟨587333, by rfl⟩ : syracuseStep 783111 = 1174667) B1174667
theorem B783119 : Blo 782338 783119 := bstep (se 1 (by rfl) ⟨587339, by rfl⟩ : syracuseStep 783119 = 1174679) B1174679
theorem B1176335 : Blo 782338 1176335 := bstep (se 1 (by rfl) ⟨882251, by rfl⟩ : syracuseStep 1176335 = 1764503) B1764503
theorem B1766159 : Blo 782338 1766159 := bstep (se 1 (by rfl) ⟨1324619, by rfl⟩ : syracuseStep 1766159 = 2649239) B2649239
theorem B1766177 : Blo 782338 1766177 := bstep (se 2 (by rfl) ⟨662316, by rfl⟩ : syracuseStep 1766177 = 1324633) B1324633
theorem B2650913 : Blo 782338 2650913 := bstep (se 2 (by rfl) ⟨994092, by rfl⟩ : syracuseStep 2650913 = 1988185) B1988185
theorem B1176377 : Blo 782338 1176377 := bstep (se 2 (by rfl) ⟨441141, by rfl⟩ : syracuseStep 1176377 = 882283) B882283
theorem B783163 : Blo 782338 783163 := bstep (se 1 (by rfl) ⟨587372, by rfl⟩ : syracuseStep 783163 = 1174745) B1174745
theorem B783239 : Blo 782338 783239 := bstep (se 1 (by rfl) ⟨587429, by rfl⟩ : syracuseStep 783239 = 1174859) B1174859
theorem B1176455 : Blo 782338 1176455 := bstep (se 1 (by rfl) ⟨882341, by rfl⟩ : syracuseStep 1176455 = 1764683) B1764683
theorem B783247 : Blo 782338 783247 := bstep (se 1 (by rfl) ⟨587435, by rfl⟩ : syracuseStep 783247 = 1174871) B1174871
theorem B1176491 : Blo 782338 1176491 := bstep (se 1 (by rfl) ⟨882368, by rfl⟩ : syracuseStep 1176491 = 1764737) B1764737
theorem B783291 : Blo 782338 783291 := bstep (se 1 (by rfl) ⟨587468, by rfl⟩ : syracuseStep 783291 = 1174937) B1174937
theorem B1176521 : Blo 782338 1176521 := bstep (se 2 (by rfl) ⟨441195, by rfl⟩ : syracuseStep 1176521 = 882391) B882391
theorem B783367 : Blo 782338 783367 := bstep (se 1 (by rfl) ⟨587525, by rfl⟩ : syracuseStep 783367 = 1175051) B1175051
theorem B881671 : Blo 782338 881671 := bstep (se 1 (by rfl) ⟨661253, by rfl⟩ : syracuseStep 881671 = 1322507) B1322507
theorem B783375 : Blo 782338 783375 := bstep (se 1 (by rfl) ⟨587531, by rfl⟩ : syracuseStep 783375 = 1175063) B1175063
theorem B783419 : Blo 782338 783419 := bstep (se 1 (by rfl) ⟨587564, by rfl⟩ : syracuseStep 783419 = 1175129) B1175129
theorem B1176635 : Blo 782338 1176635 := bstep (se 1 (by rfl) ⟨882476, by rfl⟩ : syracuseStep 1176635 = 1764953) B1764953
theorem B1176695 : Blo 782338 1176695 := bstep (se 1 (by rfl) ⟨882521, by rfl⟩ : syracuseStep 1176695 = 1765043) B1765043
theorem B1766519 : Blo 782338 1766519 := bstep (se 1 (by rfl) ⟨1324889, by rfl⟩ : syracuseStep 1766519 = 2649779) B2649779
theorem B783495 : Blo 782338 783495 := bstep (se 1 (by rfl) ⟨587621, by rfl⟩ : syracuseStep 783495 = 1175243) B1175243
theorem B783503 : Blo 782338 783503 := bstep (se 1 (by rfl) ⟨587627, by rfl⟩ : syracuseStep 783503 = 1175255) B1175255
theorem B1176719 : Blo 782338 1176719 := bstep (se 1 (by rfl) ⟨882539, by rfl⟩ : syracuseStep 1176719 = 1765079) B1765079
theorem B1176761 : Blo 782338 1176761 := bstep (se 2 (by rfl) ⟨441285, by rfl⟩ : syracuseStep 1176761 = 882571) B882571
theorem B783547 : Blo 782338 783547 := bstep (se 1 (by rfl) ⟨587660, by rfl⟩ : syracuseStep 783547 = 1175321) B1175321
theorem B881851 : Blo 782338 881851 := bstep (se 1 (by rfl) ⟨661388, by rfl⟩ : syracuseStep 881851 = 1322777) B1322777
theorem B3568877 : Blo 782338 3568877 := bstep (se 3 (by rfl) ⟨669164, by rfl⟩ : syracuseStep 3568877 = 1338329) B1338329
theorem B783623 : Blo 782338 783623 := bstep (se 1 (by rfl) ⟨587717, by rfl⟩ : syracuseStep 783623 = 1175435) B1175435
theorem B1176839 : Blo 782338 1176839 := bstep (se 1 (by rfl) ⟨882629, by rfl⟩ : syracuseStep 1176839 = 1765259) B1765259
theorem B783631 : Blo 782338 783631 := bstep (se 1 (by rfl) ⟨587723, by rfl⟩ : syracuseStep 783631 = 1175447) B1175447
theorem B1176875 : Blo 782338 1176875 := bstep (se 1 (by rfl) ⟨882656, by rfl⟩ : syracuseStep 1176875 = 1765313) B1765313
theorem B1766699 : Blo 782338 1766699 := bstep (se 1 (by rfl) ⟨1325024, by rfl⟩ : syracuseStep 1766699 = 2650049) B2650049
theorem B783675 : Blo 782338 783675 := bstep (se 1 (by rfl) ⟨587756, by rfl⟩ : syracuseStep 783675 = 1175513) B1175513
theorem B1176905 : Blo 782338 1176905 := bstep (se 2 (by rfl) ⟨441339, by rfl⟩ : syracuseStep 1176905 = 882679) B882679
theorem B2651507 : Blo 782338 2651507 := bstep (se 1 (by rfl) ⟨1988630, by rfl⟩ : syracuseStep 2651507 = 3977261) B3977261
theorem B783751 : Blo 782338 783751 := bstep (se 1 (by rfl) ⟨587813, by rfl⟩ : syracuseStep 783751 = 1175627) B1175627
theorem B783759 : Blo 782338 783759 := bstep (se 1 (by rfl) ⟨587819, by rfl⟩ : syracuseStep 783759 = 1175639) B1175639
theorem B783803 : Blo 782338 783803 := bstep (se 1 (by rfl) ⟨587852, by rfl⟩ : syracuseStep 783803 = 1175705) B1175705
theorem B1177019 : Blo 782338 1177019 := bstep (se 1 (by rfl) ⟨882764, by rfl⟩ : syracuseStep 1177019 = 1765529) B1765529
theorem B1177079 : Blo 782338 1177079 := bstep (se 1 (by rfl) ⟨882809, by rfl⟩ : syracuseStep 1177079 = 1765619) B1765619
theorem B783879 : Blo 782338 783879 := bstep (se 1 (by rfl) ⟨587909, by rfl⟩ : syracuseStep 783879 = 1175819) B1175819
theorem B783887 : Blo 782338 783887 := bstep (se 1 (by rfl) ⟨587915, by rfl⟩ : syracuseStep 783887 = 1175831) B1175831
theorem B1177103 : Blo 782338 1177103 := bstep (se 1 (by rfl) ⟨882827, by rfl⟩ : syracuseStep 1177103 = 1765655) B1765655
theorem B1177145 : Blo 782338 1177145 := bstep (se 2 (by rfl) ⟨441429, by rfl⟩ : syracuseStep 1177145 = 882859) B882859
theorem B783931 : Blo 782338 783931 := bstep (se 1 (by rfl) ⟨587948, by rfl⟩ : syracuseStep 783931 = 1175897) B1175897
theorem B784007 : Blo 782338 784007 := bstep (se 1 (by rfl) ⟨588005, by rfl⟩ : syracuseStep 784007 = 1176011) B1176011
theorem B1177223 : Blo 782338 1177223 := bstep (se 1 (by rfl) ⟨882917, by rfl⟩ : syracuseStep 1177223 = 1765835) B1765835
theorem B784015 : Blo 782338 784015 := bstep (se 1 (by rfl) ⟨588011, by rfl⟩ : syracuseStep 784015 = 1176023) B1176023
theorem B882319 : Blo 782338 882319 := bstep (se 1 (by rfl) ⟨661739, by rfl⟩ : syracuseStep 882319 = 1323479) B1323479
theorem B1767059 : Blo 782338 1767059 := bstep (se 1 (by rfl) ⟨1325294, by rfl⟩ : syracuseStep 1767059 = 2650589) B2650589
theorem B1177259 : Blo 782338 1177259 := bstep (se 1 (by rfl) ⟨882944, by rfl⟩ : syracuseStep 1177259 = 1765889) B1765889
theorem B784059 : Blo 782338 784059 := bstep (se 1 (by rfl) ⟨588044, by rfl⟩ : syracuseStep 784059 = 1176089) B1176089
theorem B3765953 : Blo 782338 3765953 := bstep (se 2 (by rfl) ⟨1412232, by rfl⟩ : syracuseStep 3765953 = 2824465) B2824465
theorem B1177289 : Blo 782338 1177289 := bstep (se 2 (by rfl) ⟨441483, by rfl⟩ : syracuseStep 1177289 = 882967) B882967
theorem B1767113 : Blo 782338 1767113 := bstep (se 2 (by rfl) ⟨662667, by rfl⟩ : syracuseStep 1767113 = 1325335) B1325335
theorem B784135 : Blo 782338 784135 := bstep (se 1 (by rfl) ⟨588101, by rfl⟩ : syracuseStep 784135 = 1176203) B1176203
theorem B784143 : Blo 782338 784143 := bstep (se 1 (by rfl) ⟨588107, by rfl⟩ : syracuseStep 784143 = 1176215) B1176215
theorem B784187 : Blo 782338 784187 := bstep (se 1 (by rfl) ⟨588140, by rfl⟩ : syracuseStep 784187 = 1176281) B1176281
theorem B1177403 : Blo 782338 1177403 := bstep (se 1 (by rfl) ⟨883052, by rfl⟩ : syracuseStep 1177403 = 1766105) B1766105
theorem B3766105 : Blo 782338 3766105 := bstep (se 2 (by rfl) ⟨1412289, by rfl⟩ : syracuseStep 3766105 = 2824579) B2824579
theorem B1177463 : Blo 782338 1177463 := bstep (se 1 (by rfl) ⟨883097, by rfl⟩ : syracuseStep 1177463 = 1766195) B1766195
theorem B1341319 : Blo 782338 1341319 := bstep (se 1 (by rfl) ⟨1005989, by rfl⟩ : syracuseStep 1341319 = 2011979) B2011979
theorem B784263 : Blo 782338 784263 := bstep (se 1 (by rfl) ⟨588197, by rfl⟩ : syracuseStep 784263 = 1176395) B1176395
theorem B784271 : Blo 782338 784271 := bstep (se 1 (by rfl) ⟨588203, by rfl⟩ : syracuseStep 784271 = 1176407) B1176407
theorem B1177487 : Blo 782338 1177487 := bstep (se 1 (by rfl) ⟨883115, by rfl⟩ : syracuseStep 1177487 = 1766231) B1766231
theorem B1177529 : Blo 782338 1177529 := bstep (se 2 (by rfl) ⟨441573, by rfl⟩ : syracuseStep 1177529 = 883147) B883147
theorem B784315 : Blo 782338 784315 := bstep (se 1 (by rfl) ⟨588236, by rfl⟩ : syracuseStep 784315 = 1176473) B1176473
theorem B784391 : Blo 782338 784391 := bstep (se 1 (by rfl) ⟨588293, by rfl⟩ : syracuseStep 784391 = 1176587) B1176587
theorem B1177607 : Blo 782338 1177607 := bstep (se 1 (by rfl) ⟨883205, by rfl⟩ : syracuseStep 1177607 = 1766411) B1766411
theorem B784399 : Blo 782338 784399 := bstep (se 1 (by rfl) ⟨588299, by rfl⟩ : syracuseStep 784399 = 1176599) B1176599
theorem B1177643 : Blo 782338 1177643 := bstep (se 1 (by rfl) ⟨883232, by rfl⟩ : syracuseStep 1177643 = 1766465) B1766465
theorem B784443 : Blo 782338 784443 := bstep (se 1 (by rfl) ⟨588332, by rfl⟩ : syracuseStep 784443 = 1176665) B1176665
theorem B1177673 : Blo 782338 1177673 := bstep (se 2 (by rfl) ⟨441627, by rfl⟩ : syracuseStep 1177673 = 883255) B883255
theorem B3176567 : Blo 782338 3176567 := bstep (se 1 (by rfl) ⟨2382425, by rfl⟩ : syracuseStep 3176567 = 4764851) B4764851
theorem B784519 : Blo 782338 784519 := bstep (se 1 (by rfl) ⟨588389, by rfl⟩ : syracuseStep 784519 = 1176779) B1176779
theorem B882823 : Blo 782338 882823 := bstep (se 1 (by rfl) ⟨662117, by rfl⟩ : syracuseStep 882823 = 1324235) B1324235
theorem B784527 : Blo 782338 784527 := bstep (se 1 (by rfl) ⟨588395, by rfl⟩ : syracuseStep 784527 = 1176791) B1176791
theorem B784571 : Blo 782338 784571 := bstep (se 1 (by rfl) ⟨588428, by rfl⟩ : syracuseStep 784571 = 1176857) B1176857
theorem B1177787 : Blo 782338 1177787 := bstep (se 1 (by rfl) ⟨883340, by rfl⟩ : syracuseStep 1177787 = 1766681) B1766681
theorem B1177847 : Blo 782338 1177847 := bstep (se 1 (by rfl) ⟨883385, by rfl⟩ : syracuseStep 1177847 = 1766771) B1766771
theorem B784647 : Blo 782338 784647 := bstep (se 1 (by rfl) ⟨588485, by rfl⟩ : syracuseStep 784647 = 1176971) B1176971
theorem B784655 : Blo 782338 784655 := bstep (se 1 (by rfl) ⟨588491, by rfl⟩ : syracuseStep 784655 = 1176983) B1176983
theorem B1177871 : Blo 782338 1177871 := bstep (se 1 (by rfl) ⟨883403, by rfl⟩ : syracuseStep 1177871 = 1766807) B1766807
theorem B1177913 : Blo 782338 1177913 := bstep (se 2 (by rfl) ⟨441717, by rfl⟩ : syracuseStep 1177913 = 883435) B883435
theorem B784699 : Blo 782338 784699 := bstep (se 1 (by rfl) ⟨588524, by rfl⟩ : syracuseStep 784699 = 1177049) B1177049
theorem B883003 : Blo 782338 883003 := bstep (se 1 (by rfl) ⟨662252, by rfl⟩ : syracuseStep 883003 = 1324505) B1324505
theorem B784775 : Blo 782338 784775 := bstep (se 1 (by rfl) ⟨588581, by rfl⟩ : syracuseStep 784775 = 1177163) B1177163
theorem B1177991 : Blo 782338 1177991 := bstep (se 1 (by rfl) ⟨883493, by rfl⟩ : syracuseStep 1177991 = 1766987) B1766987
theorem B1767815 : Blo 782338 1767815 := bstep (se 1 (by rfl) ⟨1325861, by rfl⟩ : syracuseStep 1767815 = 2651723) B2651723
theorem B784783 : Blo 782338 784783 := bstep (se 1 (by rfl) ⟨588587, by rfl⟩ : syracuseStep 784783 = 1177175) B1177175
theorem B1178027 : Blo 782338 1178027 := bstep (se 1 (by rfl) ⟨883520, by rfl⟩ : syracuseStep 1178027 = 1767041) B1767041
theorem B784827 : Blo 782338 784827 := bstep (se 1 (by rfl) ⟨588620, by rfl⟩ : syracuseStep 784827 = 1177241) B1177241
theorem B1178057 : Blo 782338 1178057 := bstep (se 2 (by rfl) ⟨441771, by rfl⟩ : syracuseStep 1178057 = 883543) B883543
theorem B784903 : Blo 782338 784903 := bstep (se 1 (by rfl) ⟨588677, by rfl⟩ : syracuseStep 784903 = 1177355) B1177355
theorem B784911 : Blo 782338 784911 := bstep (se 1 (by rfl) ⟨588683, by rfl⟩ : syracuseStep 784911 = 1177367) B1177367
theorem B784955 : Blo 782338 784955 := bstep (se 1 (by rfl) ⟨588716, by rfl⟩ : syracuseStep 784955 = 1177433) B1177433
theorem B1178171 : Blo 782338 1178171 := bstep (se 1 (by rfl) ⟨883628, by rfl⟩ : syracuseStep 1178171 = 1767257) B1767257
theorem B1767995 : Blo 782338 1767995 := bstep (se 1 (by rfl) ⟨1325996, by rfl⟩ : syracuseStep 1767995 = 2651993) B2651993
theorem B1178231 : Blo 782338 1178231 := bstep (se 1 (by rfl) ⟨883673, by rfl⟩ : syracuseStep 1178231 = 1767347) B1767347
theorem B785031 : Blo 782338 785031 := bstep (se 1 (by rfl) ⟨588773, by rfl⟩ : syracuseStep 785031 = 1177547) B1177547
theorem B785039 : Blo 782338 785039 := bstep (se 1 (by rfl) ⟨588779, by rfl⟩ : syracuseStep 785039 = 1177559) B1177559
theorem B1178255 : Blo 782338 1178255 := bstep (se 1 (by rfl) ⟨883691, by rfl⟩ : syracuseStep 1178255 = 1767383) B1767383
theorem B1178297 : Blo 782338 1178297 := bstep (se 2 (by rfl) ⟨441861, by rfl⟩ : syracuseStep 1178297 = 883723) B883723
theorem B1768121 : Blo 782338 1768121 := bstep (se 2 (by rfl) ⟨663045, by rfl⟩ : syracuseStep 1768121 = 1326091) B1326091
theorem B785083 : Blo 782338 785083 := bstep (se 1 (by rfl) ⟨588812, by rfl⟩ : syracuseStep 785083 = 1177625) B1177625
theorem B785159 : Blo 782338 785159 := bstep (se 1 (by rfl) ⟨588869, by rfl⟩ : syracuseStep 785159 = 1177739) B1177739
theorem B1178375 : Blo 782338 1178375 := bstep (se 1 (by rfl) ⟨883781, by rfl⟩ : syracuseStep 1178375 = 1767563) B1767563
theorem B785167 : Blo 782338 785167 := bstep (se 1 (by rfl) ⟨588875, by rfl⟩ : syracuseStep 785167 = 1177751) B1177751
theorem B883471 : Blo 782338 883471 := bstep (se 1 (by rfl) ⟨662603, by rfl⟩ : syracuseStep 883471 = 1325207) B1325207
theorem B1178411 : Blo 782338 1178411 := bstep (se 1 (by rfl) ⟨883808, by rfl⟩ : syracuseStep 1178411 = 1767617) B1767617
theorem B785211 : Blo 782338 785211 := bstep (se 1 (by rfl) ⟨588908, by rfl⟩ : syracuseStep 785211 = 1177817) B1177817
theorem B1178441 : Blo 782338 1178441 := bstep (se 2 (by rfl) ⟨441915, by rfl⟩ : syracuseStep 1178441 = 883831) B883831
theorem B785287 : Blo 782338 785287 := bstep (se 1 (by rfl) ⟨588965, by rfl⟩ : syracuseStep 785287 = 1177931) B1177931
theorem B785295 : Blo 782338 785295 := bstep (se 1 (by rfl) ⟨588971, by rfl⟩ : syracuseStep 785295 = 1177943) B1177943
theorem B785339 : Blo 782338 785339 := bstep (se 1 (by rfl) ⟨589004, by rfl⟩ : syracuseStep 785339 = 1178009) B1178009
theorem B1178555 : Blo 782338 1178555 := bstep (se 1 (by rfl) ⟨883916, by rfl⟩ : syracuseStep 1178555 = 1767833) B1767833
theorem B1178615 : Blo 782338 1178615 := bstep (se 1 (by rfl) ⟨883961, by rfl⟩ : syracuseStep 1178615 = 1767923) B1767923
theorem B3931139 : Blo 782338 3931139 := bstep (se 1 (by rfl) ⟨2948354, by rfl⟩ : syracuseStep 3931139 = 5896709) B5896709
theorem B9042949 : Blo 782338 9042949 := bstep (se 4 (by rfl) ⟨847776, by rfl⟩ : syracuseStep 9042949 = 1695553) B1695553
theorem B97876997 : Blo 782338 97876997 := bstep (se 4 (by rfl) ⟨9175968, by rfl⟩ : syracuseStep 97876997 = 18351937) B18351937
theorem B785415 : Blo 782338 785415 := bstep (se 1 (by rfl) ⟨589061, by rfl⟩ : syracuseStep 785415 = 1178123) B1178123
theorem B785423 : Blo 782338 785423 := bstep (se 1 (by rfl) ⟨589067, by rfl⟩ : syracuseStep 785423 = 1178135) B1178135
theorem B1178639 : Blo 782338 1178639 := bstep (se 1 (by rfl) ⟨883979, by rfl⟩ : syracuseStep 1178639 = 1767959) B1767959
theorem B1768463 : Blo 782338 1768463 := bstep (se 1 (by rfl) ⟨1326347, by rfl⟩ : syracuseStep 1768463 = 2652695) B2652695
theorem B1768481 : Blo 782338 1768481 := bstep (se 2 (by rfl) ⟨663180, by rfl⟩ : syracuseStep 1768481 = 1326361) B1326361
theorem B1178681 : Blo 782338 1178681 := bstep (se 2 (by rfl) ⟨442005, by rfl⟩ : syracuseStep 1178681 = 884011) B884011
theorem B785467 : Blo 782338 785467 := bstep (se 1 (by rfl) ⟨589100, by rfl⟩ : syracuseStep 785467 = 1178201) B1178201
theorem B785543 : Blo 782338 785543 := bstep (se 1 (by rfl) ⟨589157, by rfl⟩ : syracuseStep 785543 = 1178315) B1178315
theorem B1178759 : Blo 782338 1178759 := bstep (se 1 (by rfl) ⟨884069, by rfl⟩ : syracuseStep 1178759 = 1768139) B1768139
theorem B785551 : Blo 782338 785551 := bstep (se 1 (by rfl) ⟨589163, by rfl⟩ : syracuseStep 785551 = 1178327) B1178327
theorem B1178795 : Blo 782338 1178795 := bstep (se 1 (by rfl) ⟨884096, by rfl⟩ : syracuseStep 1178795 = 1768193) B1768193
theorem B785595 : Blo 782338 785595 := bstep (se 1 (by rfl) ⟨589196, by rfl⟩ : syracuseStep 785595 = 1178393) B1178393
theorem B1178825 : Blo 782338 1178825 := bstep (se 2 (by rfl) ⟨442059, by rfl⟩ : syracuseStep 1178825 = 884119) B884119
theorem B785671 : Blo 782338 785671 := bstep (se 1 (by rfl) ⟨589253, by rfl⟩ : syracuseStep 785671 = 1178507) B1178507
theorem B883975 : Blo 782338 883975 := bstep (se 1 (by rfl) ⟨662981, by rfl⟩ : syracuseStep 883975 = 1325963) B1325963
theorem B785679 : Blo 782338 785679 := bstep (se 1 (by rfl) ⟨589259, by rfl⟩ : syracuseStep 785679 = 1178519) B1178519
theorem B785723 : Blo 782338 785723 := bstep (se 1 (by rfl) ⟨589292, by rfl⟩ : syracuseStep 785723 = 1178585) B1178585
theorem B1178939 : Blo 782338 1178939 := bstep (se 1 (by rfl) ⟨884204, by rfl⟩ : syracuseStep 1178939 = 1768409) B1768409
theorem B1178999 : Blo 782338 1178999 := bstep (se 1 (by rfl) ⟨884249, by rfl⟩ : syracuseStep 1178999 = 1768499) B1768499
theorem B1768823 : Blo 782338 1768823 := bstep (se 1 (by rfl) ⟨1326617, by rfl⟩ : syracuseStep 1768823 = 2653235) B2653235
theorem B8486279 : Blo 782338 8486279 := bstep (se 1 (by rfl) ⟨6364709, by rfl⟩ : syracuseStep 8486279 = 12729419) B12729419
theorem B785799 : Blo 782338 785799 := bstep (se 1 (by rfl) ⟨589349, by rfl⟩ : syracuseStep 785799 = 1178699) B1178699
theorem B785807 : Blo 782338 785807 := bstep (se 1 (by rfl) ⟨589355, by rfl⟩ : syracuseStep 785807 = 1178711) B1178711
theorem B1179023 : Blo 782338 1179023 := bstep (se 1 (by rfl) ⟨884267, by rfl⟩ : syracuseStep 1179023 = 1768535) B1768535
theorem B1179065 : Blo 782338 1179065 := bstep (se 2 (by rfl) ⟨442149, by rfl⟩ : syracuseStep 1179065 = 884299) B884299
theorem B785851 : Blo 782338 785851 := bstep (se 1 (by rfl) ⟨589388, by rfl⟩ : syracuseStep 785851 = 1178777) B1178777
theorem B884155 : Blo 782338 884155 := bstep (se 1 (by rfl) ⟨663116, by rfl⟩ : syracuseStep 884155 = 1326233) B1326233
theorem B785927 : Blo 782338 785927 := bstep (se 1 (by rfl) ⟨589445, by rfl⟩ : syracuseStep 785927 = 1178891) B1178891
theorem B1179143 : Blo 782338 1179143 := bstep (se 1 (by rfl) ⟨884357, by rfl⟩ : syracuseStep 1179143 = 1768715) B1768715
theorem B785935 : Blo 782338 785935 := bstep (se 1 (by rfl) ⟨589451, by rfl⟩ : syracuseStep 785935 = 1178903) B1178903
theorem B1179179 : Blo 782338 1179179 := bstep (se 1 (by rfl) ⟨884384, by rfl⟩ : syracuseStep 1179179 = 1768769) B1768769
theorem B1769003 : Blo 782338 1769003 := bstep (se 1 (by rfl) ⟨1326752, by rfl⟩ : syracuseStep 1769003 = 2653505) B2653505
theorem B785979 : Blo 782338 785979 := bstep (se 1 (by rfl) ⟨589484, by rfl⟩ : syracuseStep 785979 = 1178969) B1178969
theorem B1179209 : Blo 782338 1179209 := bstep (se 2 (by rfl) ⟨442203, by rfl⟩ : syracuseStep 1179209 = 884407) B884407
theorem B786055 : Blo 782338 786055 := bstep (se 1 (by rfl) ⟨589541, by rfl⟩ : syracuseStep 786055 = 1179083) B1179083
theorem B786063 : Blo 782338 786063 := bstep (se 1 (by rfl) ⟨589547, by rfl⟩ : syracuseStep 786063 = 1179095) B1179095
theorem B786107 : Blo 782338 786107 := bstep (se 1 (by rfl) ⟨589580, by rfl⟩ : syracuseStep 786107 = 1179161) B1179161
theorem B1179323 : Blo 782338 1179323 := bstep (se 1 (by rfl) ⟨884492, by rfl⟩ : syracuseStep 1179323 = 1768985) B1768985
theorem B1179383 : Blo 782338 1179383 := bstep (se 1 (by rfl) ⟨884537, by rfl⟩ : syracuseStep 1179383 = 1769075) B1769075
theorem B786183 : Blo 782338 786183 := bstep (se 1 (by rfl) ⟨589637, by rfl⟩ : syracuseStep 786183 = 1179275) B1179275
theorem B786191 : Blo 782338 786191 := bstep (se 1 (by rfl) ⟨589643, by rfl⟩ : syracuseStep 786191 = 1179287) B1179287
theorem B1179407 : Blo 782338 1179407 := bstep (se 1 (by rfl) ⟨884555, by rfl⟩ : syracuseStep 1179407 = 1769111) B1769111
theorem B1179449 : Blo 782338 1179449 := bstep (se 2 (by rfl) ⟨442293, by rfl⟩ : syracuseStep 1179449 = 884587) B884587
theorem B1670971 : Blo 782338 1670971 := bstep (se 1 (by rfl) ⟨1253228, by rfl⟩ : syracuseStep 1670971 = 2506457) B2506457
theorem B786235 : Blo 782338 786235 := bstep (se 1 (by rfl) ⟨589676, by rfl⟩ : syracuseStep 786235 = 1179353) B1179353
theorem B3964787 : Blo 782338 3964787 := bstep (se 1 (by rfl) ⟨2973590, by rfl⟩ : syracuseStep 3964787 = 5947181) B5947181
theorem B2228087 : Blo 782338 2228087 := bstep (se 1 (by rfl) ⟨1671065, by rfl⟩ : syracuseStep 2228087 = 3342131) B3342131
theorem B3342215 : Blo 782338 3342215 := bstep (se 1 (by rfl) ⟨2506661, by rfl⟩ : syracuseStep 3342215 = 5013323) B5013323
theorem B786311 : Blo 782338 786311 := bstep (se 1 (by rfl) ⟨589733, by rfl⟩ : syracuseStep 786311 = 1179467) B1179467
theorem B786319 : Blo 782338 786319 := bstep (se 1 (by rfl) ⟨589739, by rfl⟩ : syracuseStep 786319 = 1179479) B1179479
theorem B884623 : Blo 782338 884623 := bstep (se 1 (by rfl) ⟨663467, by rfl⟩ : syracuseStep 884623 = 1326935) B1326935
theorem B2228303 : Blo 782338 2228303 := bstep (se 1 (by rfl) ⟨1671227, by rfl⟩ : syracuseStep 2228303 = 3342455) B3342455
theorem B26083685 : Blo 782338 26083685 := bstep (se 4 (by rfl) ⟨2445345, by rfl⟩ : syracuseStep 26083685 = 4890691) B4890691
theorem B2687357 : Blo 782338 2687357 := bstep (se 3 (by rfl) ⟨503879, by rfl⟩ : syracuseStep 2687357 = 1007759) B1007759
theorem B3179047 : Blo 782338 3179047 := bstep (se 1 (by rfl) ⟨2384285, by rfl⟩ : syracuseStep 3179047 = 4768571) B4768571
theorem B3343513 : Blo 782338 3343513 := bstep (se 2 (by rfl) ⟨1253817, by rfl⟩ : syracuseStep 3343513 = 2507635) B2507635
theorem B2229419 : Blo 782338 2229419 := bstep (se 1 (by rfl) ⟨1672064, by rfl⟩ : syracuseStep 2229419 = 3344129) B3344129
theorem B2983463 : Blo 782338 2983463 := bstep (se 1 (by rfl) ⟨2237597, by rfl⟩ : syracuseStep 2983463 = 4475195) B4475195
theorem B4458199 : Blo 782338 4458199 := bstep (se 1 (by rfl) ⟨3343649, by rfl⟩ : syracuseStep 4458199 = 6687299) B6687299
theorem B10061657 : Blo 782338 10061657 := bstep (se 2 (by rfl) ⟨3773121, by rfl⟩ : syracuseStep 10061657 = 7546243) B7546243
theorem B13371317 : Blo 782338 13371317 := bstep (se 5 (by rfl) ⟨626780, by rfl⟩ : syracuseStep 13371317 = 1253561) B1253561
theorem B4524113 : Blo 782338 4524113 := bstep (se 2 (by rfl) ⟨1696542, by rfl⟩ : syracuseStep 4524113 = 3393085) B3393085
theorem B3770525 : Blo 782338 3770525 := bstep (se 3 (by rfl) ⟨706973, by rfl⟩ : syracuseStep 3770525 = 1413947) B1413947
theorem B2984435 : Blo 782338 2984435 := bstep (se 1 (by rfl) ⟨2238326, by rfl⟩ : syracuseStep 2984435 = 4476653) B4476653
theorem B2984633 : Blo 782338 2984633 := bstep (se 2 (by rfl) ⟨1119237, by rfl⟩ : syracuseStep 2984633 = 2238475) B2238475
theorem B2984647 : Blo 782338 2984647 := bstep (se 1 (by rfl) ⟨2238485, by rfl⟩ : syracuseStep 2984647 = 4476971) B4476971
theorem B5966621 : Blo 782338 5966621 := bstep (se 3 (by rfl) ⟨1118741, by rfl⟩ : syracuseStep 5966621 = 2237483) B2237483
theorem B72354707 : Blo 782338 72354707 := bstep (se 1 (by rfl) ⟨54266030, by rfl⟩ : syracuseStep 72354707 = 108532061) B108532061
theorem B1117147 : Blo 782338 1117147 := bstep (se 1 (by rfl) ⟨837860, by rfl⟩ : syracuseStep 1117147 = 1675721) B1675721
theorem B1609033 : Blo 782338 1609033 := bstep (se 2 (by rfl) ⟨603387, by rfl⟩ : syracuseStep 1609033 = 1206775) B1206775
theorem B20417923 : Blo 782338 20417923 := bstep (se 1 (by rfl) ⟨15313442, by rfl⟩ : syracuseStep 20417923 = 30626885) B30626885
theorem B1412615 : Blo 782338 1412615 := bstep (se 1 (by rfl) ⟨1059461, by rfl⟩ : syracuseStep 1412615 = 2118923) B2118923
theorem B3575335 : Blo 782338 3575335 := bstep (se 1 (by rfl) ⟨2681501, by rfl⟩ : syracuseStep 3575335 = 5363003) B5363003
theorem B2985619 : Blo 782338 2985619 := bstep (se 1 (by rfl) ⟨2239214, by rfl⟩ : syracuseStep 2985619 = 4478429) B4478429
theorem B2821841 : Blo 782338 2821841 := bstep (se 2 (by rfl) ⟨1058190, by rfl⟩ : syracuseStep 2821841 = 2116381) B2116381
theorem B3182291 : Blo 782338 3182291 := bstep (se 1 (by rfl) ⟨2386718, by rfl⟩ : syracuseStep 3182291 = 4773437) B4773437
theorem B2264825 : Blo 782338 2264825 := bstep (se 2 (by rfl) ⟨849309, by rfl⟩ : syracuseStep 2264825 = 1698619) B1698619
theorem B7147601 : Blo 782338 7147601 := bstep (se 2 (by rfl) ⟨2680350, by rfl⟩ : syracuseStep 7147601 = 5360701) B5360701
theorem B3346589 : Blo 782338 3346589 := bstep (se 3 (by rfl) ⟨627485, by rfl⟩ : syracuseStep 3346589 = 1254971) B1254971
theorem B11309219 : Blo 782338 11309219 := bstep (se 1 (by rfl) ⟨8481914, by rfl⟩ : syracuseStep 11309219 = 16963829) B16963829
theorem B12095819 : Blo 782338 12095819 := bstep (se 1 (by rfl) ⟨9071864, by rfl⟩ : syracuseStep 12095819 = 18143729) B18143729
theorem B3772909 : Blo 782338 3772909 := bstep (se 3 (by rfl) ⟨707420, by rfl⟩ : syracuseStep 3772909 = 1414841) B1414841
theorem B4461115 : Blo 782338 4461115 := bstep (se 1 (by rfl) ⟨3345836, by rfl⟩ : syracuseStep 4461115 = 6691673) B6691673
theorem B3970295 : Blo 782338 3970295 := bstep (se 1 (by rfl) ⟨2977721, by rfl⟩ : syracuseStep 3970295 = 5955443) B5955443
theorem B9541027 : Blo 782338 9541027 := bstep (se 1 (by rfl) ⟨7155770, by rfl⟩ : syracuseStep 9541027 = 14311541) B14311541
theorem B1611343 : Blo 782338 1611343 := bstep (se 1 (by rfl) ⟨1208507, by rfl⟩ : syracuseStep 1611343 = 2417015) B2417015
theorem B3970781 : Blo 782338 3970781 := bstep (se 3 (by rfl) ⟨744521, by rfl⟩ : syracuseStep 3970781 = 1489043) B1489043
theorem B5740321 : Blo 782338 5740321 := bstep (se 2 (by rfl) ⟨2152620, by rfl⟩ : syracuseStep 5740321 = 4305241) B4305241
theorem B8034241 : Blo 782338 8034241 := bstep (se 2 (by rfl) ⟨3012840, by rfl⟩ : syracuseStep 8034241 = 6025681) B6025681
theorem B19044305 : Blo 782338 19044305 := bstep (se 2 (by rfl) ⟨7141614, by rfl⟩ : syracuseStep 19044305 = 14283229) B14283229
theorem B2234375 : Blo 782338 2234375 := bstep (se 1 (by rfl) ⟨1675781, by rfl⟩ : syracuseStep 2234375 = 3351563) B3351563
theorem B8493113 : Blo 782338 8493113 := bstep (se 2 (by rfl) ⟨3184917, by rfl⟩ : syracuseStep 8493113 = 6369835) B6369835
theorem B10033409 : Blo 782338 10033409 := bstep (se 2 (by rfl) ⟨3762528, by rfl⟩ : syracuseStep 10033409 = 7525057) B7525057
theorem B5085881 : Blo 782338 5085881 := bstep (se 2 (by rfl) ⟨1907205, by rfl⟩ : syracuseStep 5085881 = 3814411) B3814411
theorem B15047653 : Blo 782338 15047653 := bstep (se 4 (by rfl) ⟨1410717, by rfl⟩ : syracuseStep 15047653 = 2821435) B2821435
theorem B5970995 : Blo 782338 5970995 := bstep (se 1 (by rfl) ⟨4478246, by rfl⟩ : syracuseStep 5970995 = 8956493) B8956493
theorem B990407 : Blo 782338 990407 := bstep (se 1 (by rfl) ⟨742805, by rfl⟩ : syracuseStep 990407 = 1485611) B1485611
theorem B1678583 : Blo 782338 1678583 := bstep (se 1 (by rfl) ⟨1258937, by rfl⟩ : syracuseStep 1678583 = 2517875) B2517875
theorem B990559 : Blo 782338 990559 := bstep (se 1 (by rfl) ⟨742919, by rfl⟩ : syracuseStep 990559 = 1485839) B1485839
theorem B3186311 : Blo 782338 3186311 := bstep (se 1 (by rfl) ⟨2389733, by rfl⟩ : syracuseStep 3186311 = 4779467) B4779467
theorem B3776215 : Blo 782338 3776215 := bstep (se 1 (by rfl) ⟨2832161, by rfl⟩ : syracuseStep 3776215 = 5664323) B5664323
theorem B5644025 : Blo 782338 5644025 := bstep (se 2 (by rfl) ⟨2116509, by rfl⟩ : syracuseStep 5644025 = 4233019) B4233019
theorem B627351317 : Blo 782338 627351317 := bstep (se 6 (by rfl) ⟨14703546, by rfl⟩ : syracuseStep 627351317 = 29407093) B29407093
theorem B5021473 : Blo 782338 5021473 := bstep (se 2 (by rfl) ⟨1883052, by rfl⟩ : syracuseStep 5021473 = 3766105) B3766105
theorem B4235075 : Blo 782338 4235075 := bstep (se 1 (by rfl) ⟨3176306, by rfl⟩ : syracuseStep 4235075 = 6352613) B6352613
theorem B10166147 : Blo 782338 10166147 := bstep (se 1 (by rfl) ⟨7624610, by rfl⟩ : syracuseStep 10166147 = 15249221) B15249221
theorem B794567 : Blo 782338 794567 := bstep (se 1 (by rfl) ⟨595925, by rfl⟩ : syracuseStep 794567 = 1191851) B1191851
theorem B2236663 : Blo 782338 2236663 := bstep (se 1 (by rfl) ⟨1677497, by rfl⟩ : syracuseStep 2236663 = 3354995) B3354995
theorem B2236891 : Blo 782338 2236891 := bstep (se 1 (by rfl) ⟨1677668, by rfl⟩ : syracuseStep 2236891 = 3355337) B3355337
theorem B2237051 : Blo 782338 2237051 := bstep (se 1 (by rfl) ⟨1677788, by rfl⟩ : syracuseStep 2237051 = 3355577) B3355577
theorem B6693587 : Blo 782338 6693587 := bstep (se 1 (by rfl) ⟨5020190, by rfl⟩ : syracuseStep 6693587 = 10040381) B10040381
theorem B2237291 : Blo 782338 2237291 := bstep (se 1 (by rfl) ⟨1677968, by rfl⟩ : syracuseStep 2237291 = 3355937) B3355937
theorem B1320367 : Blo 782338 1320367 := bstep (se 1 (by rfl) ⟨990275, by rfl⟩ : syracuseStep 1320367 = 1980551) B1980551
theorem B992731 : Blo 782338 992731 := bstep (se 1 (by rfl) ⟨744548, by rfl⟩ : syracuseStep 992731 = 1489097) B1489097
theorem B2237939 : Blo 782338 2237939 := bstep (se 1 (by rfl) ⟨1678454, by rfl⟩ : syracuseStep 2237939 = 3356909) B3356909
theorem B1320455 : Blo 782338 1320455 := bstep (se 1 (by rfl) ⟨990341, by rfl⟩ : syracuseStep 1320455 = 1980683) B1980683
theorem B2238167 : Blo 782338 2238167 := bstep (se 1 (by rfl) ⟨1678625, by rfl⟩ : syracuseStep 2238167 = 3357251) B3357251
theorem B6694649 : Blo 782338 6694649 := bstep (se 2 (by rfl) ⟨2510493, by rfl⟩ : syracuseStep 6694649 = 5020987) B5020987
theorem B1320799 : Blo 782338 1320799 := bstep (se 1 (by rfl) ⟨990599, by rfl⟩ : syracuseStep 1320799 = 1981199) B1981199
theorem B1320887 : Blo 782338 1320887 := bstep (se 1 (by rfl) ⟨990665, by rfl⟩ : syracuseStep 1320887 = 1981331) B1981331
theorem B65251331 : Blo 782338 65251331 := bstep (se 1 (by rfl) ⟨48938498, by rfl⟩ : syracuseStep 65251331 = 97876997) B97876997
theorem B5023781 : Blo 782338 5023781 := bstep (se 4 (by rfl) ⟨470979, by rfl⟩ : syracuseStep 5023781 = 941959) B941959
theorem B2828459 : Blo 782338 2828459 := bstep (se 1 (by rfl) ⟨2121344, by rfl⟩ : syracuseStep 2828459 = 4242689) B4242689
theorem B1321481 : Blo 782338 1321481 := bstep (se 2 (by rfl) ⟨495555, by rfl⟩ : syracuseStep 1321481 = 991111) B991111
theorem B1485391 : Blo 782338 1485391 := bstep (se 1 (by rfl) ⟨1114043, by rfl⟩ : syracuseStep 1485391 = 2228087) B2228087
theorem B3025555 : Blo 782338 3025555 := bstep (se 1 (by rfl) ⟨2269166, by rfl⟩ : syracuseStep 3025555 = 4538333) B4538333
theorem B1321643 : Blo 782338 1321643 := bstep (se 1 (by rfl) ⟨991232, by rfl⟩ : syracuseStep 1321643 = 1982465) B1982465
theorem B3975965 : Blo 782338 3975965 := bstep (se 3 (by rfl) ⟨745493, by rfl⟩ : syracuseStep 3975965 = 1490987) B1490987
theorem B1485641 : Blo 782338 1485641 := bstep (se 2 (by rfl) ⟨557115, by rfl⟩ : syracuseStep 1485641 = 1114231) B1114231
theorem B19049363 : Blo 782338 19049363 := bstep (se 1 (by rfl) ⟨14287022, by rfl⟩ : syracuseStep 19049363 = 28574045) B28574045
theorem B2010017 : Blo 782338 2010017 := bstep (se 2 (by rfl) ⟨753756, by rfl⟩ : syracuseStep 2010017 = 1507513) B1507513
theorem B5942321 : Blo 782338 5942321 := bstep (se 2 (by rfl) ⟨2228370, by rfl⟩ : syracuseStep 5942321 = 4456741) B4456741
theorem B1322041 : Blo 782338 1322041 := bstep (se 2 (by rfl) ⟨495765, by rfl⟩ : syracuseStep 1322041 = 991531) B991531
theorem B50834627 : Blo 782338 50834627 := bstep (se 1 (by rfl) ⟨38125970, by rfl⟩ : syracuseStep 50834627 = 76251941) B76251941
theorem B1322183 : Blo 782338 1322183 := bstep (se 1 (by rfl) ⟨991637, by rfl⟩ : syracuseStep 1322183 = 1983275) B1983275
theorem B1322345 : Blo 782338 1322345 := bstep (se 2 (by rfl) ⟨495879, by rfl⟩ : syracuseStep 1322345 = 991759) B991759
theorem B2010511 : Blo 782338 2010511 := bstep (se 1 (by rfl) ⟨1507883, by rfl⟩ : syracuseStep 2010511 = 3015767) B3015767
theorem B1256887 : Blo 782338 1256887 := bstep (se 1 (by rfl) ⟨942665, by rfl⟩ : syracuseStep 1256887 = 1885331) B1885331
theorem B2829971 : Blo 782338 2829971 := bstep (se 1 (by rfl) ⟨2122478, by rfl⟩ : syracuseStep 2829971 = 4244957) B4244957
theorem B1486507 : Blo 782338 1486507 := bstep (se 1 (by rfl) ⟨1114880, by rfl⟩ : syracuseStep 1486507 = 2229761) B2229761
theorem B3354311 : Blo 782338 3354311 := bstep (se 1 (by rfl) ⟨2515733, by rfl⟩ : syracuseStep 3354311 = 5031467) B5031467
theorem B1486583 : Blo 782338 1486583 := bstep (se 1 (by rfl) ⟨1114937, by rfl⟩ : syracuseStep 1486583 = 2229875) B2229875
theorem B1322743 : Blo 782338 1322743 := bstep (se 1 (by rfl) ⟨992057, by rfl⟩ : syracuseStep 1322743 = 1984115) B1984115
theorem B5648237 : Blo 782338 5648237 := bstep (se 3 (by rfl) ⟨1059044, by rfl⟩ : syracuseStep 5648237 = 2118089) B2118089
theorem B1322939 : Blo 782338 1322939 := bstep (se 1 (by rfl) ⟨992204, by rfl⟩ : syracuseStep 1322939 = 1984409) B1984409
theorem B1486811 : Blo 782338 1486811 := bstep (se 1 (by rfl) ⟨1115108, by rfl⟩ : syracuseStep 1486811 = 2230217) B2230217
theorem B1323047 : Blo 782338 1323047 := bstep (se 1 (by rfl) ⟨992285, by rfl⟩ : syracuseStep 1323047 = 1984571) B1984571
theorem B1323337 : Blo 782338 1323337 := bstep (se 2 (by rfl) ⟨496251, by rfl⟩ : syracuseStep 1323337 = 992503) B992503
theorem B1323371 : Blo 782338 1323371 := bstep (se 1 (by rfl) ⟨992528, by rfl⟩ : syracuseStep 1323371 = 1985057) B1985057
theorem B1192411 : Blo 782338 1192411 := bstep (se 1 (by rfl) ⟨894308, by rfl⟩ : syracuseStep 1192411 = 1788617) B1788617
theorem B1323769 : Blo 782338 1323769 := bstep (se 2 (by rfl) ⟨496413, by rfl⟩ : syracuseStep 1323769 = 992827) B992827
theorem B3224393 : Blo 782338 3224393 := bstep (se 2 (by rfl) ⟨1209147, by rfl⟩ : syracuseStep 3224393 = 2418295) B2418295
theorem B1324039 : Blo 782338 1324039 := bstep (se 1 (by rfl) ⟨993029, by rfl⟩ : syracuseStep 1324039 = 1986059) B1986059
theorem B1488071 : Blo 782338 1488071 := bstep (se 1 (by rfl) ⟨1116053, by rfl⟩ : syracuseStep 1488071 = 2232107) B2232107
theorem B1488223 : Blo 782338 1488223 := bstep (se 1 (by rfl) ⟨1116167, by rfl⟩ : syracuseStep 1488223 = 2232335) B2232335
theorem B1324471 : Blo 782338 1324471 := bstep (se 1 (by rfl) ⟨993353, by rfl⟩ : syracuseStep 1324471 = 1986707) B1986707
theorem B1324667 : Blo 782338 1324667 := bstep (se 1 (by rfl) ⟨993500, by rfl⟩ : syracuseStep 1324667 = 1987001) B1987001
theorem B1357511 : Blo 782338 1357511 := bstep (se 1 (by rfl) ⟨1018133, by rfl⟩ : syracuseStep 1357511 = 2036267) B2036267
theorem B3815111 : Blo 782338 3815111 := bstep (se 1 (by rfl) ⟨2861333, by rfl⟩ : syracuseStep 3815111 = 5722667) B5722667
theorem B9058007 : Blo 782338 9058007 := bstep (se 1 (by rfl) ⟨6793505, by rfl⟩ : syracuseStep 9058007 = 13587011) B13587011
theorem B6371065 : Blo 782338 6371065 := bstep (se 2 (by rfl) ⟨2389149, by rfl⟩ : syracuseStep 6371065 = 4778299) B4778299
theorem B5027777 : Blo 782338 5027777 := bstep (se 2 (by rfl) ⟨1885416, by rfl⟩ : syracuseStep 5027777 = 3770833) B3770833
theorem B1325065 : Blo 782338 1325065 := bstep (se 2 (by rfl) ⟨496899, by rfl⟩ : syracuseStep 1325065 = 993799) B993799
theorem B4470821 : Blo 782338 4470821 := bstep (se 4 (by rfl) ⟨419139, by rfl⟩ : syracuseStep 4470821 = 838279) B838279
theorem B8927333 : Blo 782338 8927333 := bstep (se 4 (by rfl) ⟨836937, by rfl⟩ : syracuseStep 8927333 = 1673875) B1673875
theorem B1325227 : Blo 782338 1325227 := bstep (se 1 (by rfl) ⟨993920, by rfl⟩ : syracuseStep 1325227 = 1987841) B1987841
theorem B1587529 : Blo 782338 1587529 := bstep (se 2 (by rfl) ⟨595323, by rfl⟩ : syracuseStep 1587529 = 1190647) B1190647
theorem B1325531 : Blo 782338 1325531 := bstep (se 1 (by rfl) ⟨994148, by rfl⟩ : syracuseStep 1325531 = 1988297) B1988297
theorem B1882649 : Blo 782338 1882649 := bstep (se 2 (by rfl) ⟨705993, by rfl⟩ : syracuseStep 1882649 = 1411987) B1411987
theorem B4471321 : Blo 782338 4471321 := bstep (se 2 (by rfl) ⟨1676745, by rfl⟩ : syracuseStep 4471321 = 3353491) B3353491
theorem B1325767 : Blo 782338 1325767 := bstep (se 1 (by rfl) ⟨994325, by rfl⟩ : syracuseStep 1325767 = 1988651) B1988651
theorem B1325929 : Blo 782338 1325929 := bstep (se 2 (by rfl) ⟨497223, by rfl⟩ : syracuseStep 1325929 = 994447) B994447
theorem B25475953 : Blo 782338 25475953 := bstep (se 2 (by rfl) ⟨9553482, by rfl⟩ : syracuseStep 25475953 = 19106965) B19106965
theorem B3980339 : Blo 782338 3980339 := bstep (se 1 (by rfl) ⟨2985254, by rfl⟩ : syracuseStep 3980339 = 5970509) B5970509
theorem B1490167 : Blo 782338 1490167 := bstep (se 1 (by rfl) ⟨1117625, by rfl⟩ : syracuseStep 1490167 = 2235251) B2235251
theorem B1326523 : Blo 782338 1326523 := bstep (se 1 (by rfl) ⟨994892, by rfl⟩ : syracuseStep 1326523 = 1989785) B1989785
theorem B1490395 : Blo 782338 1490395 := bstep (se 1 (by rfl) ⟨1117796, by rfl⟩ : syracuseStep 1490395 = 2235593) B2235593
theorem B1490471 : Blo 782338 1490471 := bstep (se 1 (by rfl) ⟨1117853, by rfl⟩ : syracuseStep 1490471 = 2235707) B2235707
theorem B1326631 : Blo 782338 1326631 := bstep (se 1 (by rfl) ⟨994973, by rfl⟩ : syracuseStep 1326631 = 1989947) B1989947
theorem B1490555 : Blo 782338 1490555 := bstep (se 1 (by rfl) ⟨1117916, by rfl⟩ : syracuseStep 1490555 = 2235833) B2235833
theorem B10862351 : Blo 782338 10862351 := bstep (se 1 (by rfl) ⟨8146763, by rfl⟩ : syracuseStep 10862351 = 16293527) B16293527
theorem B5881643 : Blo 782338 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B1982303 : Blo 782338 1982303 := bstep (se 1 (by rfl) ⟨1486727, by rfl⟩ : syracuseStep 1982303 = 2973455) B2973455
theorem B1491041 : Blo 782338 1491041 := bstep (se 2 (by rfl) ⟨559140, by rfl⟩ : syracuseStep 1491041 = 1118281) B1118281
theorem B836015 : Blo 782338 836015 := bstep (se 1 (by rfl) ⟨627011, by rfl⟩ : syracuseStep 836015 = 1254023) B1254023
theorem B1983001 : Blo 782338 1983001 := bstep (se 2 (by rfl) ⟨743625, by rfl⟩ : syracuseStep 1983001 = 1487251) B1487251
theorem B1983305 : Blo 782338 1983305 := bstep (se 2 (by rfl) ⟨743739, by rfl⟩ : syracuseStep 1983305 = 1487479) B1487479
theorem B2016175 : Blo 782338 2016175 := bstep (se 1 (by rfl) ⟨1512131, by rfl⟩ : syracuseStep 2016175 = 3024263) B3024263
theorem B4474237 : Blo 782338 4474237 := bstep (se 3 (by rfl) ⟨838919, by rfl⟩ : syracuseStep 4474237 = 1677839) B1677839
theorem B1492499 : Blo 782338 1492499 := bstep (se 1 (by rfl) ⟨1119374, by rfl⟩ : syracuseStep 1492499 = 2238749) B2238749
theorem B1984439 : Blo 782338 1984439 := bstep (se 1 (by rfl) ⟨1488329, by rfl⟩ : syracuseStep 1984439 = 2976659) B2976659
theorem B6637571 : Blo 782338 6637571 := bstep (se 1 (by rfl) ⟨4978178, by rfl⟩ : syracuseStep 6637571 = 9956357) B9956357
theorem B12863897 : Blo 782338 12863897 := bstep (se 2 (by rfl) ⟨4823961, by rfl⟩ : syracuseStep 12863897 = 9647923) B9647923
theorem B1788425 : Blo 782338 1788425 := bstep (se 2 (by rfl) ⟨670659, by rfl⟩ : syracuseStep 1788425 = 1341319) B1341319
theorem B2640599 : Blo 782338 2640599 := bstep (se 1 (by rfl) ⟨1980449, by rfl⟩ : syracuseStep 2640599 = 3960899) B3960899
theorem B2640815 : Blo 782338 2640815 := bstep (se 1 (by rfl) ⟨1980611, by rfl⟩ : syracuseStep 2640815 = 3961223) B3961223
theorem B1985543 : Blo 782338 1985543 := bstep (se 1 (by rfl) ⟨1489157, by rfl⟩ : syracuseStep 1985543 = 2978315) B2978315
theorem B1985593 : Blo 782338 1985593 := bstep (se 2 (by rfl) ⟨744597, by rfl⟩ : syracuseStep 1985593 = 1489195) B1489195
theorem B5950583 : Blo 782338 5950583 := bstep (se 1 (by rfl) ⟨4462937, by rfl⟩ : syracuseStep 5950583 = 8925875) B8925875
theorem B1985897 : Blo 782338 1985897 := bstep (se 2 (by rfl) ⟨744711, by rfl⟩ : syracuseStep 1985897 = 1489423) B1489423
theorem B2379251 : Blo 782338 2379251 := bstep (se 1 (by rfl) ⟨1784438, by rfl⟩ : syracuseStep 2379251 = 3568877) B3568877
theorem B2510635 : Blo 782338 2510635 := bstep (se 1 (by rfl) ⟨1882976, by rfl⟩ : syracuseStep 2510635 = 3765953) B3765953
theorem B19124099 : Blo 782338 19124099 := bstep (se 1 (by rfl) ⟨14343074, by rfl⟩ : syracuseStep 19124099 = 28686149) B28686149
theorem B1036327 : Blo 782338 1036327 := bstep (se 1 (by rfl) ⟨777245, by rfl⟩ : syracuseStep 1036327 = 1554491) B1554491
theorem B2117711 : Blo 782338 2117711 := bstep (se 1 (by rfl) ⟨1588283, by rfl⟩ : syracuseStep 2117711 = 3176567) B3176567
theorem B22663745 : Blo 782338 22663745 := bstep (se 2 (by rfl) ⟨8498904, by rfl⟩ : syracuseStep 22663745 = 16997809) B16997809
theorem B5657519 : Blo 782338 5657519 := bstep (se 1 (by rfl) ⟨4243139, by rfl⟩ : syracuseStep 5657519 = 8486279) B8486279
theorem B2643191 : Blo 782338 2643191 := bstep (se 1 (by rfl) ⟨1982393, by rfl⟩ : syracuseStep 2643191 = 3964787) B3964787
theorem B6346127 : Blo 782338 6346127 := bstep (se 1 (by rfl) ⟨4759595, by rfl⟩ : syracuseStep 6346127 = 9519191) B9519191
theorem B19125649 : Blo 782338 19125649 := bstep (se 2 (by rfl) ⟨7172118, by rfl⟩ : syracuseStep 19125649 = 14344237) B14344237
theorem B19092955 : Blo 782338 19092955 := bstep (se 1 (by rfl) ⟨14319716, by rfl⟩ : syracuseStep 19092955 = 28639433) B28639433
theorem B1988135 : Blo 782338 1988135 := bstep (se 1 (by rfl) ⟨1491101, by rfl⟩ : syracuseStep 1988135 = 2982203) B2982203
theorem B2643515 : Blo 782338 2643515 := bstep (se 1 (by rfl) ⟨1982636, by rfl⟩ : syracuseStep 2643515 = 3965273) B3965273
theorem B2512583 : Blo 782338 2512583 := bstep (se 1 (by rfl) ⟨1884437, by rfl⟩ : syracuseStep 2512583 = 3768875) B3768875
theorem B2676509 : Blo 782338 2676509 := bstep (se 3 (by rfl) ⟨501845, by rfl⟩ : syracuseStep 2676509 = 1003691) B1003691
theorem B2643785 : Blo 782338 2643785 := bstep (se 2 (by rfl) ⟨991419, by rfl⟩ : syracuseStep 2643785 = 1982839) B1982839
theorem B1988459 : Blo 782338 1988459 := bstep (se 1 (by rfl) ⟨1491344, by rfl⟩ : syracuseStep 1988459 = 2982689) B2982689
theorem B2971511 : Blo 782338 2971511 := bstep (se 1 (by rfl) ⟨2228633, by rfl⟩ : syracuseStep 2971511 = 4457267) B4457267
theorem B1989107 : Blo 782338 1989107 := bstep (se 1 (by rfl) ⟨1491830, by rfl⟩ : syracuseStep 1989107 = 2983661) B2983661
theorem B4774409 : Blo 782338 4774409 := bstep (se 2 (by rfl) ⟨1790403, by rfl⟩ : syracuseStep 4774409 = 3580807) B3580807
theorem B2513531 : Blo 782338 2513531 := bstep (se 1 (by rfl) ⟨1885148, by rfl⟩ : syracuseStep 2513531 = 3770297) B3770297
theorem B1989319 : Blo 782338 1989319 := bstep (se 1 (by rfl) ⟨1491989, by rfl⟩ : syracuseStep 1989319 = 2983979) B2983979
theorem B4840195 : Blo 782338 4840195 := bstep (se 1 (by rfl) ⟨3630146, by rfl⟩ : syracuseStep 4840195 = 7260293) B7260293
theorem B2972483 : Blo 782338 2972483 := bstep (se 1 (by rfl) ⟨2229362, by rfl⟩ : syracuseStep 2972483 = 4458725) B4458725
theorem B2644919 : Blo 782338 2644919 := bstep (se 1 (by rfl) ⟨1983689, by rfl⟩ : syracuseStep 2644919 = 3967379) B3967379
theorem B8477891 : Blo 782338 8477891 := bstep (se 1 (by rfl) ⟨6358418, by rfl⟩ : syracuseStep 8477891 = 12716837) B12716837
theorem B6708419 : Blo 782338 6708419 := bstep (se 1 (by rfl) ⟨5031314, by rfl⟩ : syracuseStep 6708419 = 10062629) B10062629
theorem B5102795 : Blo 782338 5102795 := bstep (se 1 (by rfl) ⟨3827096, by rfl⟩ : syracuseStep 5102795 = 7654193) B7654193
theorem B2121203 : Blo 782338 2121203 := bstep (se 1 (by rfl) ⟨1590902, by rfl⟩ : syracuseStep 2121203 = 3181805) B3181805
theorem B1760777 : Blo 782338 1760777 := bstep (se 2 (by rfl) ⟨660291, by rfl⟩ : syracuseStep 1760777 = 1320583) B1320583
theorem B2645513 : Blo 782338 2645513 := bstep (se 2 (by rfl) ⟨992067, by rfl⟩ : syracuseStep 2645513 = 1984135) B1984135
theorem B2580007 : Blo 782338 2580007 := bstep (se 1 (by rfl) ⟨1935005, by rfl⟩ : syracuseStep 2580007 = 3870011) B3870011
theorem B1990241 : Blo 782338 1990241 := bstep (se 2 (by rfl) ⟨746340, by rfl⟩ : syracuseStep 1990241 = 1492681) B1492681
theorem B10182365 : Blo 782338 10182365 := bstep (se 3 (by rfl) ⟨1909193, by rfl⟩ : syracuseStep 10182365 = 3818387) B3818387
theorem B2973469 : Blo 782338 2973469 := bstep (se 3 (by rfl) ⟨557525, by rfl⟩ : syracuseStep 2973469 = 1115051) B1115051
theorem B1761119 : Blo 782338 1761119 := bstep (se 1 (by rfl) ⟨1320839, by rfl⟩ : syracuseStep 1761119 = 2641679) B2641679
theorem B9035651 : Blo 782338 9035651 := bstep (se 1 (by rfl) ⟨6776738, by rfl⟩ : syracuseStep 9035651 = 13553477) B13553477
theorem B2514863 : Blo 782338 2514863 := bstep (se 1 (by rfl) ⟨1886147, by rfl⟩ : syracuseStep 2514863 = 3772295) B3772295
theorem B1761299 : Blo 782338 1761299 := bstep (se 1 (by rfl) ⟨1320974, by rfl⟩ : syracuseStep 1761299 = 2641949) B2641949
theorem B1761641 : Blo 782338 1761641 := bstep (se 2 (by rfl) ⟨660615, by rfl⟩ : syracuseStep 1761641 = 1321231) B1321231
theorem B2646377 : Blo 782338 2646377 := bstep (se 2 (by rfl) ⟨992391, by rfl⟩ : syracuseStep 2646377 = 1984783) B1984783
theorem B1762235 : Blo 782338 1762235 := bstep (se 1 (by rfl) ⟨1321676, by rfl⟩ : syracuseStep 1762235 = 2643353) B2643353
theorem B2646971 : Blo 782338 2646971 := bstep (se 1 (by rfl) ⟨1985228, by rfl⟩ : syracuseStep 2646971 = 3970457) B3970457
theorem B1762361 : Blo 782338 1762361 := bstep (se 2 (by rfl) ⟨660885, by rfl⟩ : syracuseStep 1762361 = 1321771) B1321771
theorem B15262937 : Blo 782338 15262937 := bstep (se 2 (by rfl) ⟨5723601, by rfl⟩ : syracuseStep 15262937 = 11447203) B11447203
theorem B5956901 : Blo 782338 5956901 := bstep (se 4 (by rfl) ⟨558459, by rfl⟩ : syracuseStep 5956901 = 1116919) B1116919
theorem B1762703 : Blo 782338 1762703 := bstep (se 1 (by rfl) ⟨1322027, by rfl⟩ : syracuseStep 1762703 = 2644055) B2644055
theorem B943535 : Blo 782338 943535 := bstep (se 1 (by rfl) ⟨707651, by rfl⟩ : syracuseStep 943535 = 1415303) B1415303
theorem B8938997 : Blo 782338 8938997 := bstep (se 5 (by rfl) ⟨419015, by rfl⟩ : syracuseStep 8938997 = 838031) B838031
theorem B3761761 : Blo 782338 3761761 := bstep (se 2 (by rfl) ⟨1410660, by rfl⟩ : syracuseStep 3761761 = 2821321) B2821321
theorem B1763027 : Blo 782338 1763027 := bstep (se 1 (by rfl) ⟨1322270, by rfl⟩ : syracuseStep 1763027 = 2644541) B2644541
theorem B24209111 : Blo 782338 24209111 := bstep (se 1 (by rfl) ⟨18156833, by rfl⟩ : syracuseStep 24209111 = 36313667) B36313667
theorem B6711083 : Blo 782338 6711083 := bstep (se 1 (by rfl) ⟨5033312, by rfl⟩ : syracuseStep 6711083 = 10066625) B10066625
theorem B11299121 : Blo 782338 11299121 := bstep (se 2 (by rfl) ⟨4237170, by rfl⟩ : syracuseStep 11299121 = 8474341) B8474341
theorem B1173935 : Blo 782338 1173935 := bstep (se 1 (by rfl) ⟨880451, by rfl⟩ : syracuseStep 1173935 = 1760903) B1760903
theorem B1075631 : Blo 782338 1075631 := bstep (se 1 (by rfl) ⟨806723, by rfl⟩ : syracuseStep 1075631 = 1613447) B1613447
theorem B1174025 : Blo 782338 1174025 := bstep (se 2 (by rfl) ⟨440259, by rfl⟩ : syracuseStep 1174025 = 880519) B880519
theorem B1174055 : Blo 782338 1174055 := bstep (se 1 (by rfl) ⟨880541, by rfl⟩ : syracuseStep 1174055 = 1761083) B1761083
theorem B1174139 : Blo 782338 1174139 := bstep (se 1 (by rfl) ⟨880604, by rfl⟩ : syracuseStep 1174139 = 1761209) B1761209
theorem B1763963 : Blo 782338 1763963 := bstep (se 1 (by rfl) ⟨1322972, by rfl⟩ : syracuseStep 1763963 = 2645945) B2645945
theorem B2648699 : Blo 782338 2648699 := bstep (se 1 (by rfl) ⟨1986524, by rfl⟩ : syracuseStep 2648699 = 3973049) B3973049
theorem B8055497 : Blo 782338 8055497 := bstep (se 2 (by rfl) ⟨3020811, by rfl⟩ : syracuseStep 8055497 = 6041623) B6041623
theorem B1174265 : Blo 782338 1174265 := bstep (se 2 (by rfl) ⟨440349, by rfl⟩ : syracuseStep 1174265 = 880699) B880699
theorem B1764089 : Blo 782338 1764089 := bstep (se 2 (by rfl) ⟨661533, by rfl⟩ : syracuseStep 1764089 = 1323067) B1323067
theorem B2648861 : Blo 782338 2648861 := bstep (se 3 (by rfl) ⟨496661, by rfl⟩ : syracuseStep 2648861 = 993323) B993323
theorem B1174367 : Blo 782338 1174367 := bstep (se 1 (by rfl) ⟨880775, by rfl⟩ : syracuseStep 1174367 = 1761551) B1761551
theorem B1174379 : Blo 782338 1174379 := bstep (se 1 (by rfl) ⟨880784, by rfl⟩ : syracuseStep 1174379 = 1761569) B1761569
theorem B1764359 : Blo 782338 1764359 := bstep (se 1 (by rfl) ⟨1323269, by rfl⟩ : syracuseStep 1764359 = 2646539) B2646539
theorem B10742807 : Blo 782338 10742807 := bstep (se 1 (by rfl) ⟨8057105, by rfl⟩ : syracuseStep 10742807 = 16114211) B16114211
theorem B1174607 : Blo 782338 1174607 := bstep (se 1 (by rfl) ⟨880955, by rfl⟩ : syracuseStep 1174607 = 1761911) B1761911
theorem B1764431 : Blo 782338 1764431 := bstep (se 1 (by rfl) ⟨1323323, by rfl⟩ : syracuseStep 1764431 = 2646647) B2646647
theorem B1174727 : Blo 782338 1174727 := bstep (se 1 (by rfl) ⟨881045, by rfl⟩ : syracuseStep 1174727 = 1762091) B1762091
theorem B1174889 : Blo 782338 1174889 := bstep (se 2 (by rfl) ⟨440583, by rfl⟩ : syracuseStep 1174889 = 881167) B881167
theorem B1174967 : Blo 782338 1174967 := bstep (se 1 (by rfl) ⟨881225, by rfl⟩ : syracuseStep 1174967 = 1762451) B1762451
theorem B1175003 : Blo 782338 1175003 := bstep (se 1 (by rfl) ⟨881252, by rfl⟩ : syracuseStep 1175003 = 1762505) B1762505
theorem B1764827 : Blo 782338 1764827 := bstep (se 1 (by rfl) ⟨1323620, by rfl⟩ : syracuseStep 1764827 = 2647241) B2647241
theorem B2649563 : Blo 782338 2649563 := bstep (se 1 (by rfl) ⟨1987172, by rfl⟩ : syracuseStep 2649563 = 3974345) B3974345
theorem B2518553 : Blo 782338 2518553 := bstep (se 2 (by rfl) ⟨944457, by rfl⟩ : syracuseStep 2518553 = 1888915) B1888915
theorem B2977631 : Blo 782338 2977631 := bstep (se 1 (by rfl) ⟨2233223, by rfl⟩ : syracuseStep 2977631 = 4466447) B4466447
theorem B3960737 : Blo 782338 3960737 := bstep (se 2 (by rfl) ⟨1485276, by rfl⟩ : syracuseStep 3960737 = 2970553) B2970553
theorem B1175471 : Blo 782338 1175471 := bstep (se 1 (by rfl) ⟨881603, by rfl⟩ : syracuseStep 1175471 = 1763207) B1763207
theorem B1765295 : Blo 782338 1765295 := bstep (se 1 (by rfl) ⟨1323971, by rfl⟩ : syracuseStep 1765295 = 2647943) B2647943
theorem B1175561 : Blo 782338 1175561 := bstep (se 2 (by rfl) ⟨440835, by rfl⟩ : syracuseStep 1175561 = 881671) B881671
theorem B782375 : Blo 782338 782375 := bstep (se 1 (by rfl) ⟨586781, by rfl⟩ : syracuseStep 782375 = 1173563) B1173563
theorem B1175591 : Blo 782338 1175591 := bstep (se 1 (by rfl) ⟨881693, by rfl⟩ : syracuseStep 1175591 = 1763387) B1763387
theorem B782415 : Blo 782338 782415 := bstep (se 1 (by rfl) ⟨586811, by rfl⟩ : syracuseStep 782415 = 1173623) B1173623
theorem B782431 : Blo 782338 782431 := bstep (se 1 (by rfl) ⟨586823, by rfl⟩ : syracuseStep 782431 = 1173647) B1173647
theorem B782459 : Blo 782338 782459 := bstep (se 1 (by rfl) ⟨586844, by rfl⟩ : syracuseStep 782459 = 1173689) B1173689
theorem B1175675 : Blo 782338 1175675 := bstep (se 1 (by rfl) ⟨881756, by rfl⟩ : syracuseStep 1175675 = 1763513) B1763513
theorem B2650265 : Blo 782338 2650265 := bstep (se 2 (by rfl) ⟨993849, by rfl⟩ : syracuseStep 2650265 = 1987699) B1987699
theorem B1765547 : Blo 782338 1765547 := bstep (se 1 (by rfl) ⟨1324160, by rfl⟩ : syracuseStep 1765547 = 2648321) B2648321
theorem B782511 : Blo 782338 782511 := bstep (se 1 (by rfl) ⟨586883, by rfl⟩ : syracuseStep 782511 = 1173767) B1173767
theorem B782535 : Blo 782338 782535 := bstep (se 1 (by rfl) ⟨586901, by rfl⟩ : syracuseStep 782535 = 1173803) B1173803
theorem B782555 : Blo 782338 782555 := bstep (se 1 (by rfl) ⟨586916, by rfl⟩ : syracuseStep 782555 = 1173833) B1173833
theorem B1175801 : Blo 782338 1175801 := bstep (se 2 (by rfl) ⟨440925, by rfl⟩ : syracuseStep 1175801 = 881851) B881851
theorem B782631 : Blo 782338 782631 := bstep (se 1 (by rfl) ⟨586973, by rfl⟩ : syracuseStep 782631 = 1173947) B1173947
theorem B782671 : Blo 782338 782671 := bstep (se 1 (by rfl) ⟨587003, by rfl⟩ : syracuseStep 782671 = 1174007) B1174007
theorem B782687 : Blo 782338 782687 := bstep (se 1 (by rfl) ⟨587015, by rfl⟩ : syracuseStep 782687 = 1174031) B1174031
theorem B1175903 : Blo 782338 1175903 := bstep (se 1 (by rfl) ⟨881927, by rfl⟩ : syracuseStep 1175903 = 1763855) B1763855
theorem B1175915 : Blo 782338 1175915 := bstep (se 1 (by rfl) ⟨881936, by rfl⟩ : syracuseStep 1175915 = 1763873) B1763873
theorem B782715 : Blo 782338 782715 := bstep (se 1 (by rfl) ⟨587036, by rfl⟩ : syracuseStep 782715 = 1174073) B1174073
theorem B782767 : Blo 782338 782767 := bstep (se 1 (by rfl) ⟨587075, by rfl⟩ : syracuseStep 782767 = 1174151) B1174151
theorem B782791 : Blo 782338 782791 := bstep (se 1 (by rfl) ⟨587093, by rfl⟩ : syracuseStep 782791 = 1174187) B1174187
theorem B782811 : Blo 782338 782811 := bstep (se 1 (by rfl) ⟨587108, by rfl⟩ : syracuseStep 782811 = 1174217) B1174217
theorem B2978329 : Blo 782338 2978329 := bstep (se 2 (by rfl) ⟨1116873, by rfl⟩ : syracuseStep 2978329 = 2233747) B2233747
theorem B782887 : Blo 782338 782887 := bstep (se 1 (by rfl) ⟨587165, by rfl⟩ : syracuseStep 782887 = 1174331) B1174331
theorem B782927 : Blo 782338 782927 := bstep (se 1 (by rfl) ⟨587195, by rfl⟩ : syracuseStep 782927 = 1174391) B1174391
theorem B1176143 : Blo 782338 1176143 := bstep (se 1 (by rfl) ⟨882107, by rfl⟩ : syracuseStep 1176143 = 1764215) B1764215
theorem B782943 : Blo 782338 782943 := bstep (se 1 (by rfl) ⟨587207, by rfl⟩ : syracuseStep 782943 = 1174415) B1174415
theorem B15069797 : Blo 782338 15069797 := bstep (se 4 (by rfl) ⟨1412793, by rfl⟩ : syracuseStep 15069797 = 2825587) B2825587
theorem B782971 : Blo 782338 782971 := bstep (se 1 (by rfl) ⟨587228, by rfl⟩ : syracuseStep 782971 = 1174457) B1174457
theorem B881275 : Blo 782338 881275 := bstep (se 1 (by rfl) ⟨660956, by rfl⟩ : syracuseStep 881275 = 1321913) B1321913
theorem B783023 : Blo 782338 783023 := bstep (se 1 (by rfl) ⟨587267, by rfl⟩ : syracuseStep 783023 = 1174535) B1174535
theorem B783047 : Blo 782338 783047 := bstep (se 1 (by rfl) ⟨587285, by rfl⟩ : syracuseStep 783047 = 1174571) B1174571
theorem B1176263 : Blo 782338 1176263 := bstep (se 1 (by rfl) ⟨882197, by rfl⟩ : syracuseStep 1176263 = 1764395) B1764395
theorem B1766087 : Blo 782338 1766087 := bstep (se 1 (by rfl) ⟨1324565, by rfl⟩ : syracuseStep 1766087 = 2649131) B2649131
theorem B783067 : Blo 782338 783067 := bstep (se 1 (by rfl) ⟨587300, by rfl⟩ : syracuseStep 783067 = 1174601) B1174601
theorem B783143 : Blo 782338 783143 := bstep (se 1 (by rfl) ⟨587357, by rfl⟩ : syracuseStep 783143 = 1174715) B1174715
theorem B2978603 : Blo 782338 2978603 := bstep (se 1 (by rfl) ⟨2233952, by rfl⟩ : syracuseStep 2978603 = 4467905) B4467905
theorem B2978633 : Blo 782338 2978633 := bstep (se 2 (by rfl) ⟨1116987, by rfl⟩ : syracuseStep 2978633 = 2233975) B2233975
theorem B783183 : Blo 782338 783183 := bstep (se 1 (by rfl) ⟨587387, by rfl⟩ : syracuseStep 783183 = 1174775) B1174775
theorem B783199 : Blo 782338 783199 := bstep (se 1 (by rfl) ⟨587399, by rfl⟩ : syracuseStep 783199 = 1174799) B1174799
theorem B1176425 : Blo 782338 1176425 := bstep (se 2 (by rfl) ⟨441159, by rfl⟩ : syracuseStep 1176425 = 882319) B882319
theorem B783227 : Blo 782338 783227 := bstep (se 1 (by rfl) ⟨587420, by rfl⟩ : syracuseStep 783227 = 1174841) B1174841
theorem B783279 : Blo 782338 783279 := bstep (se 1 (by rfl) ⟨587459, by rfl⟩ : syracuseStep 783279 = 1174919) B1174919
theorem B1176503 : Blo 782338 1176503 := bstep (se 1 (by rfl) ⟨882377, by rfl⟩ : syracuseStep 1176503 = 1764755) B1764755
theorem B783303 : Blo 782338 783303 := bstep (se 1 (by rfl) ⟨587477, by rfl⟩ : syracuseStep 783303 = 1174955) B1174955
theorem B783323 : Blo 782338 783323 := bstep (se 1 (by rfl) ⟨587492, by rfl⟩ : syracuseStep 783323 = 1174985) B1174985
theorem B1176539 : Blo 782338 1176539 := bstep (se 1 (by rfl) ⟨882404, by rfl⟩ : syracuseStep 1176539 = 1764809) B1764809
theorem B783399 : Blo 782338 783399 := bstep (se 1 (by rfl) ⟨587549, by rfl⟩ : syracuseStep 783399 = 1175099) B1175099
theorem B783439 : Blo 782338 783439 := bstep (se 1 (by rfl) ⟨587579, by rfl⟩ : syracuseStep 783439 = 1175159) B1175159
theorem B881743 : Blo 782338 881743 := bstep (se 1 (by rfl) ⟨661307, by rfl⟩ : syracuseStep 881743 = 1322615) B1322615
theorem B783455 : Blo 782338 783455 := bstep (se 1 (by rfl) ⟨587591, by rfl⟩ : syracuseStep 783455 = 1175183) B1175183
theorem B783483 : Blo 782338 783483 := bstep (se 1 (by rfl) ⟨587612, by rfl⟩ : syracuseStep 783483 = 1175225) B1175225
theorem B783535 : Blo 782338 783535 := bstep (se 1 (by rfl) ⟨587651, by rfl⟩ : syracuseStep 783535 = 1175303) B1175303
theorem B783559 : Blo 782338 783559 := bstep (se 1 (by rfl) ⟨587669, by rfl⟩ : syracuseStep 783559 = 1175339) B1175339
theorem B783579 : Blo 782338 783579 := bstep (se 1 (by rfl) ⟨587684, by rfl⟩ : syracuseStep 783579 = 1175369) B1175369
theorem B783655 : Blo 782338 783655 := bstep (se 1 (by rfl) ⟨587741, by rfl⟩ : syracuseStep 783655 = 1175483) B1175483
theorem B2651453 : Blo 782338 2651453 := bstep (se 3 (by rfl) ⟨497147, by rfl⟩ : syracuseStep 2651453 = 994295) B994295
theorem B783695 : Blo 782338 783695 := bstep (se 1 (by rfl) ⟨587771, by rfl⟩ : syracuseStep 783695 = 1175543) B1175543
theorem B783711 : Blo 782338 783711 := bstep (se 1 (by rfl) ⟨587783, by rfl⟩ : syracuseStep 783711 = 1175567) B1175567
theorem B783739 : Blo 782338 783739 := bstep (se 1 (by rfl) ⟨587804, by rfl⟩ : syracuseStep 783739 = 1175609) B1175609
theorem B783791 : Blo 782338 783791 := bstep (se 1 (by rfl) ⟨587843, by rfl⟩ : syracuseStep 783791 = 1175687) B1175687
theorem B1177007 : Blo 782338 1177007 := bstep (se 1 (by rfl) ⟨882755, by rfl⟩ : syracuseStep 1177007 = 1765511) B1765511
theorem B783815 : Blo 782338 783815 := bstep (se 1 (by rfl) ⟨587861, by rfl⟩ : syracuseStep 783815 = 1175723) B1175723
theorem B783835 : Blo 782338 783835 := bstep (se 1 (by rfl) ⟨587876, by rfl⟩ : syracuseStep 783835 = 1175753) B1175753
theorem B882139 : Blo 782338 882139 := bstep (se 1 (by rfl) ⟨661604, by rfl⟩ : syracuseStep 882139 = 1323209) B1323209
theorem B1177097 : Blo 782338 1177097 := bstep (se 2 (by rfl) ⟨441411, by rfl⟩ : syracuseStep 1177097 = 882823) B882823
theorem B783911 : Blo 782338 783911 := bstep (se 1 (by rfl) ⟨587933, by rfl⟩ : syracuseStep 783911 = 1175867) B1175867
theorem B1177127 : Blo 782338 1177127 := bstep (se 1 (by rfl) ⟨882845, by rfl⟩ : syracuseStep 1177127 = 1765691) B1765691
theorem B1766951 : Blo 782338 1766951 := bstep (se 1 (by rfl) ⟨1325213, by rfl⟩ : syracuseStep 1766951 = 2650427) B2650427
theorem B783951 : Blo 782338 783951 := bstep (se 1 (by rfl) ⟨587963, by rfl⟩ : syracuseStep 783951 = 1175927) B1175927
theorem B783967 : Blo 782338 783967 := bstep (se 1 (by rfl) ⟨587975, by rfl⟩ : syracuseStep 783967 = 1175951) B1175951
theorem B783995 : Blo 782338 783995 := bstep (se 1 (by rfl) ⟨587996, by rfl⟩ : syracuseStep 783995 = 1175993) B1175993
theorem B2684539 : Blo 782338 2684539 := bstep (se 1 (by rfl) ⟨2013404, by rfl⟩ : syracuseStep 2684539 = 4026809) B4026809
theorem B1177211 : Blo 782338 1177211 := bstep (se 1 (by rfl) ⟨882908, by rfl⟩ : syracuseStep 1177211 = 1765817) B1765817
theorem B784047 : Blo 782338 784047 := bstep (se 1 (by rfl) ⟨588035, by rfl⟩ : syracuseStep 784047 = 1176071) B1176071
theorem B784071 : Blo 782338 784071 := bstep (se 1 (by rfl) ⟨588053, by rfl⟩ : syracuseStep 784071 = 1176107) B1176107
theorem B784091 : Blo 782338 784091 := bstep (se 1 (by rfl) ⟨588068, by rfl⟩ : syracuseStep 784091 = 1176137) B1176137
theorem B1177337 : Blo 782338 1177337 := bstep (se 2 (by rfl) ⟨441501, by rfl⟩ : syracuseStep 1177337 = 883003) B883003
theorem B784167 : Blo 782338 784167 := bstep (se 1 (by rfl) ⟨588125, by rfl⟩ : syracuseStep 784167 = 1176251) B1176251
theorem B784207 : Blo 782338 784207 := bstep (se 1 (by rfl) ⟨588155, by rfl⟩ : syracuseStep 784207 = 1176311) B1176311
theorem B784223 : Blo 782338 784223 := bstep (se 1 (by rfl) ⟨588167, by rfl⟩ : syracuseStep 784223 = 1176335) B1176335
theorem B1177439 : Blo 782338 1177439 := bstep (se 1 (by rfl) ⟨883079, by rfl⟩ : syracuseStep 1177439 = 1766159) B1766159
theorem B1177451 : Blo 782338 1177451 := bstep (se 1 (by rfl) ⟨883088, by rfl⟩ : syracuseStep 1177451 = 1766177) B1766177
theorem B1767275 : Blo 782338 1767275 := bstep (se 1 (by rfl) ⟨1325456, by rfl⟩ : syracuseStep 1767275 = 2650913) B2650913
theorem B784251 : Blo 782338 784251 := bstep (se 1 (by rfl) ⟨588188, by rfl⟩ : syracuseStep 784251 = 1176377) B1176377
theorem B1767329 : Blo 782338 1767329 := bstep (se 2 (by rfl) ⟨662748, by rfl⟩ : syracuseStep 1767329 = 1325497) B1325497
theorem B784303 : Blo 782338 784303 := bstep (se 1 (by rfl) ⟨588227, by rfl⟩ : syracuseStep 784303 = 1176455) B1176455
theorem B882607 : Blo 782338 882607 := bstep (se 1 (by rfl) ⟨661955, by rfl⟩ : syracuseStep 882607 = 1323911) B1323911
theorem B784327 : Blo 782338 784327 := bstep (se 1 (by rfl) ⟨588245, by rfl⟩ : syracuseStep 784327 = 1176491) B1176491
theorem B784347 : Blo 782338 784347 := bstep (se 1 (by rfl) ⟨588260, by rfl⟩ : syracuseStep 784347 = 1176521) B1176521
theorem B784423 : Blo 782338 784423 := bstep (se 1 (by rfl) ⟨588317, by rfl⟩ : syracuseStep 784423 = 1176635) B1176635
theorem B784463 : Blo 782338 784463 := bstep (se 1 (by rfl) ⟨588347, by rfl⟩ : syracuseStep 784463 = 1176695) B1176695
theorem B1177679 : Blo 782338 1177679 := bstep (se 1 (by rfl) ⟨883259, by rfl⟩ : syracuseStep 1177679 = 1766519) B1766519
theorem B784479 : Blo 782338 784479 := bstep (se 1 (by rfl) ⟨588359, by rfl⟩ : syracuseStep 784479 = 1176719) B1176719
theorem B784507 : Blo 782338 784507 := bstep (se 1 (by rfl) ⟨588380, by rfl⟩ : syracuseStep 784507 = 1176761) B1176761
theorem B2652317 : Blo 782338 2652317 := bstep (se 3 (by rfl) ⟨497309, by rfl⟩ : syracuseStep 2652317 = 994619) B994619
theorem B784559 : Blo 782338 784559 := bstep (se 1 (by rfl) ⟨588419, by rfl⟩ : syracuseStep 784559 = 1176839) B1176839
theorem B784583 : Blo 782338 784583 := bstep (se 1 (by rfl) ⟨588437, by rfl⟩ : syracuseStep 784583 = 1176875) B1176875
theorem B1177799 : Blo 782338 1177799 := bstep (se 1 (by rfl) ⟨883349, by rfl⟩ : syracuseStep 1177799 = 1766699) B1766699
theorem B784603 : Blo 782338 784603 := bstep (se 1 (by rfl) ⟨588452, by rfl⟩ : syracuseStep 784603 = 1176905) B1176905
theorem B1767671 : Blo 782338 1767671 := bstep (se 1 (by rfl) ⟨1325753, by rfl⟩ : syracuseStep 1767671 = 2651507) B2651507
theorem B784679 : Blo 782338 784679 := bstep (se 1 (by rfl) ⟨588509, by rfl⟩ : syracuseStep 784679 = 1177019) B1177019
theorem B784719 : Blo 782338 784719 := bstep (se 1 (by rfl) ⟨588539, by rfl⟩ : syracuseStep 784719 = 1177079) B1177079
theorem B784735 : Blo 782338 784735 := bstep (se 1 (by rfl) ⟨588551, by rfl⟩ : syracuseStep 784735 = 1177103) B1177103
theorem B883039 : Blo 782338 883039 := bstep (se 1 (by rfl) ⟨662279, by rfl⟩ : syracuseStep 883039 = 1324559) B1324559
theorem B1177961 : Blo 782338 1177961 := bstep (se 2 (by rfl) ⟨441735, by rfl⟩ : syracuseStep 1177961 = 883471) B883471
theorem B784763 : Blo 782338 784763 := bstep (se 1 (by rfl) ⟨588572, by rfl⟩ : syracuseStep 784763 = 1177145) B1177145
theorem B784815 : Blo 782338 784815 := bstep (se 1 (by rfl) ⟨588611, by rfl⟩ : syracuseStep 784815 = 1177223) B1177223
theorem B1178039 : Blo 782338 1178039 := bstep (se 1 (by rfl) ⟨883529, by rfl⟩ : syracuseStep 1178039 = 1767059) B1767059
theorem B784839 : Blo 782338 784839 := bstep (se 1 (by rfl) ⟨588629, by rfl⟩ : syracuseStep 784839 = 1177259) B1177259
theorem B784859 : Blo 782338 784859 := bstep (se 1 (by rfl) ⟨588644, by rfl⟩ : syracuseStep 784859 = 1177289) B1177289
theorem B1178075 : Blo 782338 1178075 := bstep (se 1 (by rfl) ⟨883556, by rfl⟩ : syracuseStep 1178075 = 1767113) B1767113
theorem B784935 : Blo 782338 784935 := bstep (se 1 (by rfl) ⟨588701, by rfl⟩ : syracuseStep 784935 = 1177403) B1177403
theorem B784975 : Blo 782338 784975 := bstep (se 1 (by rfl) ⟨588731, by rfl⟩ : syracuseStep 784975 = 1177463) B1177463
theorem B784991 : Blo 782338 784991 := bstep (se 1 (by rfl) ⟨588743, by rfl⟩ : syracuseStep 784991 = 1177487) B1177487
theorem B785019 : Blo 782338 785019 := bstep (se 1 (by rfl) ⟨588764, by rfl⟩ : syracuseStep 785019 = 1177529) B1177529
theorem B785071 : Blo 782338 785071 := bstep (se 1 (by rfl) ⟨588803, by rfl⟩ : syracuseStep 785071 = 1177607) B1177607
theorem B12057265 : Blo 782338 12057265 := bstep (se 2 (by rfl) ⟨4521474, by rfl⟩ : syracuseStep 12057265 = 9042949) B9042949
theorem B2652857 : Blo 782338 2652857 := bstep (se 2 (by rfl) ⟨994821, by rfl⟩ : syracuseStep 2652857 = 1989643) B1989643
theorem B785095 : Blo 782338 785095 := bstep (se 1 (by rfl) ⟨588821, by rfl⟩ : syracuseStep 785095 = 1177643) B1177643
theorem B883399 : Blo 782338 883399 := bstep (se 1 (by rfl) ⟨662549, by rfl⟩ : syracuseStep 883399 = 1325099) B1325099
theorem B785115 : Blo 782338 785115 := bstep (se 1 (by rfl) ⟨588836, by rfl⟩ : syracuseStep 785115 = 1177673) B1177673
theorem B785191 : Blo 782338 785191 := bstep (se 1 (by rfl) ⟨588893, by rfl⟩ : syracuseStep 785191 = 1177787) B1177787
theorem B1768265 : Blo 782338 1768265 := bstep (se 2 (by rfl) ⟨663099, by rfl⟩ : syracuseStep 1768265 = 1326199) B1326199
theorem B785231 : Blo 782338 785231 := bstep (se 1 (by rfl) ⟨588923, by rfl⟩ : syracuseStep 785231 = 1177847) B1177847
theorem B785247 : Blo 782338 785247 := bstep (se 1 (by rfl) ⟨588935, by rfl⟩ : syracuseStep 785247 = 1177871) B1177871
theorem B785275 : Blo 782338 785275 := bstep (se 1 (by rfl) ⟨588956, by rfl⟩ : syracuseStep 785275 = 1177913) B1177913
theorem B785327 : Blo 782338 785327 := bstep (se 1 (by rfl) ⟨588995, by rfl⟩ : syracuseStep 785327 = 1177991) B1177991
theorem B1178543 : Blo 782338 1178543 := bstep (se 1 (by rfl) ⟨883907, by rfl⟩ : syracuseStep 1178543 = 1767815) B1767815
theorem B785351 : Blo 782338 785351 := bstep (se 1 (by rfl) ⟨589013, by rfl⟩ : syracuseStep 785351 = 1178027) B1178027
theorem B785371 : Blo 782338 785371 := bstep (se 1 (by rfl) ⟨589028, by rfl⟩ : syracuseStep 785371 = 1178057) B1178057
theorem B1178633 : Blo 782338 1178633 := bstep (se 2 (by rfl) ⟨441987, by rfl⟩ : syracuseStep 1178633 = 883975) B883975
theorem B785447 : Blo 782338 785447 := bstep (se 1 (by rfl) ⟨589085, by rfl⟩ : syracuseStep 785447 = 1178171) B1178171
theorem B1178663 : Blo 782338 1178663 := bstep (se 1 (by rfl) ⟨883997, by rfl⟩ : syracuseStep 1178663 = 1767995) B1767995
theorem B785487 : Blo 782338 785487 := bstep (se 1 (by rfl) ⟨589115, by rfl⟩ : syracuseStep 785487 = 1178231) B1178231
theorem B785503 : Blo 782338 785503 := bstep (se 1 (by rfl) ⟨589127, by rfl⟩ : syracuseStep 785503 = 1178255) B1178255
theorem B785531 : Blo 782338 785531 := bstep (se 1 (by rfl) ⟨589148, by rfl⟩ : syracuseStep 785531 = 1178297) B1178297
theorem B1178747 : Blo 782338 1178747 := bstep (se 1 (by rfl) ⟨884060, by rfl⟩ : syracuseStep 1178747 = 1768121) B1768121
theorem B785583 : Blo 782338 785583 := bstep (se 1 (by rfl) ⟨589187, by rfl⟩ : syracuseStep 785583 = 1178375) B1178375
theorem B785607 : Blo 782338 785607 := bstep (se 1 (by rfl) ⟨589205, by rfl⟩ : syracuseStep 785607 = 1178411) B1178411
theorem B785627 : Blo 782338 785627 := bstep (se 1 (by rfl) ⟨589220, by rfl⟩ : syracuseStep 785627 = 1178441) B1178441
theorem B1178873 : Blo 782338 1178873 := bstep (se 2 (by rfl) ⟨442077, by rfl⟩ : syracuseStep 1178873 = 884155) B884155
theorem B2653451 : Blo 782338 2653451 := bstep (se 1 (by rfl) ⟨1990088, by rfl⟩ : syracuseStep 2653451 = 3980177) B3980177
theorem B785703 : Blo 782338 785703 := bstep (se 1 (by rfl) ⟨589277, by rfl⟩ : syracuseStep 785703 = 1178555) B1178555
theorem B785743 : Blo 782338 785743 := bstep (se 1 (by rfl) ⟨589307, by rfl⟩ : syracuseStep 785743 = 1178615) B1178615
theorem B2620759 : Blo 782338 2620759 := bstep (se 1 (by rfl) ⟨1965569, by rfl⟩ : syracuseStep 2620759 = 3931139) B3931139
theorem B785759 : Blo 782338 785759 := bstep (se 1 (by rfl) ⟨589319, by rfl⟩ : syracuseStep 785759 = 1178639) B1178639
theorem B1178975 : Blo 782338 1178975 := bstep (se 1 (by rfl) ⟨884231, by rfl⟩ : syracuseStep 1178975 = 1768463) B1768463
theorem B1178987 : Blo 782338 1178987 := bstep (se 1 (by rfl) ⟨884240, by rfl⟩ : syracuseStep 1178987 = 1768481) B1768481
theorem B785787 : Blo 782338 785787 := bstep (se 1 (by rfl) ⟨589340, by rfl⟩ : syracuseStep 785787 = 1178681) B1178681
theorem B2981245 : Blo 782338 2981245 := bstep (se 3 (by rfl) ⟨558983, by rfl⟩ : syracuseStep 2981245 = 1117967) B1117967
theorem B785839 : Blo 782338 785839 := bstep (se 1 (by rfl) ⟨589379, by rfl⟩ : syracuseStep 785839 = 1178759) B1178759
theorem B785863 : Blo 782338 785863 := bstep (se 1 (by rfl) ⟨589397, by rfl⟩ : syracuseStep 785863 = 1178795) B1178795
theorem B785883 : Blo 782338 785883 := bstep (se 1 (by rfl) ⟨589412, by rfl⟩ : syracuseStep 785883 = 1178825) B1178825
theorem B2653721 : Blo 782338 2653721 := bstep (se 2 (by rfl) ⟨995145, by rfl⟩ : syracuseStep 2653721 = 1990291) B1990291
theorem B785959 : Blo 782338 785959 := bstep (se 1 (by rfl) ⟨589469, by rfl⟩ : syracuseStep 785959 = 1178939) B1178939
theorem B884263 : Blo 782338 884263 := bstep (se 1 (by rfl) ⟨663197, by rfl⟩ : syracuseStep 884263 = 1326395) B1326395
theorem B785999 : Blo 782338 785999 := bstep (se 1 (by rfl) ⟨589499, by rfl⟩ : syracuseStep 785999 = 1178999) B1178999
theorem B1179215 : Blo 782338 1179215 := bstep (se 1 (by rfl) ⟨884411, by rfl⟩ : syracuseStep 1179215 = 1768823) B1768823
theorem B786015 : Blo 782338 786015 := bstep (se 1 (by rfl) ⟨589511, by rfl⟩ : syracuseStep 786015 = 1179023) B1179023
theorem B1769057 : Blo 782338 1769057 := bstep (se 2 (by rfl) ⟨663396, by rfl⟩ : syracuseStep 1769057 = 1326793) B1326793
theorem B786043 : Blo 782338 786043 := bstep (se 1 (by rfl) ⟨589532, by rfl⟩ : syracuseStep 786043 = 1179065) B1179065
theorem B786095 : Blo 782338 786095 := bstep (se 1 (by rfl) ⟨589571, by rfl⟩ : syracuseStep 786095 = 1179143) B1179143
theorem B786119 : Blo 782338 786119 := bstep (se 1 (by rfl) ⟨589589, by rfl⟩ : syracuseStep 786119 = 1179179) B1179179
theorem B1179335 : Blo 782338 1179335 := bstep (se 1 (by rfl) ⟨884501, by rfl⟩ : syracuseStep 1179335 = 1769003) B1769003
theorem B786139 : Blo 782338 786139 := bstep (se 1 (by rfl) ⟨589604, by rfl⟩ : syracuseStep 786139 = 1179209) B1179209
theorem B2227961 : Blo 782338 2227961 := bstep (se 2 (by rfl) ⟨835485, by rfl⟩ : syracuseStep 2227961 = 1670971) B1670971
theorem B786215 : Blo 782338 786215 := bstep (se 1 (by rfl) ⟨589661, by rfl⟩ : syracuseStep 786215 = 1179323) B1179323
theorem B786255 : Blo 782338 786255 := bstep (se 1 (by rfl) ⟨589691, by rfl⟩ : syracuseStep 786255 = 1179383) B1179383
theorem B786271 : Blo 782338 786271 := bstep (se 1 (by rfl) ⟨589703, by rfl⟩ : syracuseStep 786271 = 1179407) B1179407
theorem B1179497 : Blo 782338 1179497 := bstep (se 2 (by rfl) ⟨442311, by rfl⟩ : syracuseStep 1179497 = 884623) B884623
theorem B786299 : Blo 782338 786299 := bstep (se 1 (by rfl) ⟨589724, by rfl⟩ : syracuseStep 786299 = 1179449) B1179449
theorem B2228143 : Blo 782338 2228143 := bstep (se 1 (by rfl) ⟨1671107, by rfl⟩ : syracuseStep 2228143 = 3342215) B3342215
theorem B5963705 : Blo 782338 5963705 := bstep (se 2 (by rfl) ⟨2236389, by rfl⟩ : syracuseStep 5963705 = 4472779) B4472779
theorem B2982217 : Blo 782338 2982217 := bstep (se 2 (by rfl) ⟨1118331, by rfl⟩ : syracuseStep 2982217 = 2236663) B2236663
theorem B2982521 : Blo 782338 2982521 := bstep (se 2 (by rfl) ⟨1118445, by rfl⟩ : syracuseStep 2982521 = 2236891) B2236891
theorem B2229373 : Blo 782338 2229373 := bstep (se 3 (by rfl) ⟨418007, by rfl⟩ : syracuseStep 2229373 = 836015) B836015
theorem B2688233 : Blo 782338 2688233 := bstep (se 2 (by rfl) ⟨1008087, by rfl⟩ : syracuseStep 2688233 = 2016175) B2016175
theorem B8914211 : Blo 782338 8914211 := bstep (se 1 (by rfl) ⟨6685658, by rfl⟩ : syracuseStep 8914211 = 13371317) B13371317
theorem B4425047 : Blo 782338 4425047 := bstep (se 1 (by rfl) ⟨3318785, by rfl⟩ : syracuseStep 4425047 = 6637571) B6637571
theorem B3016075 : Blo 782338 3016075 := bstep (se 1 (by rfl) ⟨2262056, by rfl⟩ : syracuseStep 3016075 = 4524113) B4524113
theorem B4458017 : Blo 782338 4458017 := bstep (se 2 (by rfl) ⟨1671756, by rfl⟩ : syracuseStep 4458017 = 3343513) B3343513
theorem B5965649 : Blo 782338 5965649 := bstep (se 2 (by rfl) ⟨2237118, by rfl⟩ : syracuseStep 5965649 = 4474237) B4474237
theorem B48236471 : Blo 782338 48236471 := bstep (se 1 (by rfl) ⟨36177353, by rfl⟩ : syracuseStep 48236471 = 72354707) B72354707
theorem B3967055 : Blo 782338 3967055 := bstep (se 1 (by rfl) ⟨2975291, by rfl⟩ : syracuseStep 3967055 = 5950583) B5950583
theorem B5015681 : Blo 782338 5015681 := bstep (se 2 (by rfl) ⟨1880880, by rfl⟩ : syracuseStep 5015681 = 3761761) B3761761
theorem B1509883 : Blo 782338 1509883 := bstep (se 1 (by rfl) ⟨1132412, by rfl⟩ : syracuseStep 1509883 = 2264825) B2264825
theorem B12749399 : Blo 782338 12749399 := bstep (se 1 (by rfl) ⟨9562049, by rfl⟩ : syracuseStep 12749399 = 19124099) B19124099
theorem B2231059 : Blo 782338 2231059 := bstep (se 1 (by rfl) ⟨1673294, by rfl⟩ : syracuseStep 2231059 = 3346589) B3346589
theorem B7539479 : Blo 782338 7539479 := bstep (se 1 (by rfl) ⟨5654609, by rfl⟩ : syracuseStep 7539479 = 11309219) B11309219
theorem B8063879 : Blo 782338 8063879 := bstep (se 1 (by rfl) ⟨6047909, by rfl⟩ : syracuseStep 8063879 = 12095819) B12095819
theorem B15109163 : Blo 782338 15109163 := bstep (se 1 (by rfl) ⟨11331872, by rfl⟩ : syracuseStep 15109163 = 22663745) B22663745
theorem B3968189 : Blo 782338 3968189 := bstep (se 3 (by rfl) ⟨744035, by rfl⟩ : syracuseStep 3968189 = 1488071) B1488071
theorem B3771679 : Blo 782338 3771679 := bstep (se 1 (by rfl) ⟨2828759, by rfl⟩ : syracuseStep 3771679 = 5657519) B5657519
theorem B1675055 : Blo 782338 1675055 := bstep (se 1 (by rfl) ⟨1256291, by rfl⟩ : syracuseStep 1675055 = 2512583) B2512583
theorem B6688939 : Blo 782338 6688939 := bstep (se 1 (by rfl) ⟨5016704, by rfl⟩ : syracuseStep 6688939 = 10033409) B10033409
theorem B3182939 : Blo 782338 3182939 := bstep (se 1 (by rfl) ⟨2387204, by rfl⟩ : syracuseStep 3182939 = 4774409) B4774409
theorem B1675687 : Blo 782338 1675687 := bstep (se 1 (by rfl) ⟨1256765, by rfl⟩ : syracuseStep 1675687 = 2513531) B2513531
theorem B11473397 : Blo 782338 11473397 := bstep (se 5 (by rfl) ⟨537815, by rfl⟩ : syracuseStep 11473397 = 1075631) B1075631
theorem B24154685 : Blo 782338 24154685 := bstep (se 3 (by rfl) ⟨4529003, by rfl⟩ : syracuseStep 24154685 = 9058007) B9058007
theorem B1414135 : Blo 782338 1414135 := bstep (se 1 (by rfl) ⟨1060601, by rfl⟩ : syracuseStep 1414135 = 2121203) B2121203
theorem B3347513 : Blo 782338 3347513 := bstep (se 2 (by rfl) ⟨1255317, by rfl⟩ : syracuseStep 3347513 = 2510635) B2510635
theorem B6788243 : Blo 782338 6788243 := bstep (se 1 (by rfl) ⟨5091182, by rfl⟩ : syracuseStep 6788243 = 10182365) B10182365
theorem B2823383 : Blo 782338 2823383 := bstep (se 1 (by rfl) ⟨2117537, by rfl⟩ : syracuseStep 2823383 = 4235075) B4235075
theorem B1676575 : Blo 782338 1676575 := bstep (se 1 (by rfl) ⟨1257431, by rfl⟩ : syracuseStep 1676575 = 2514863) B2514863
theorem B1381769 : Blo 782338 1381769 := bstep (se 2 (by rfl) ⟨518163, by rfl⟩ : syracuseStep 1381769 = 1036327) B1036327
theorem B4462391 : Blo 782338 4462391 := bstep (se 1 (by rfl) ⟨3346793, by rfl⟩ : syracuseStep 4462391 = 6693587) B6693587
theorem B3971105 : Blo 782338 3971105 := bstep (se 2 (by rfl) ⟨1489164, by rfl⟩ : syracuseStep 3971105 = 2978329) B2978329
theorem B3971267 : Blo 782338 3971267 := bstep (se 1 (by rfl) ⟨2978450, by rfl⟩ : syracuseStep 3971267 = 5956901) B5956901
theorem B4463099 : Blo 782338 4463099 := bstep (se 1 (by rfl) ⟨3347324, by rfl⟩ : syracuseStep 4463099 = 6694649) B6694649
theorem B3349187 : Blo 782338 3349187 := bstep (se 1 (by rfl) ⟨2511890, by rfl⟩ : syracuseStep 3349187 = 5023781) B5023781
theorem B25500865 : Blo 782338 25500865 := bstep (se 2 (by rfl) ⟨9562824, by rfl⟩ : syracuseStep 25500865 = 19125649) B19125649
theorem B12721369 : Blo 782338 12721369 := bstep (se 2 (by rfl) ⟨4770513, by rfl⟩ : syracuseStep 12721369 = 9541027) B9541027
theorem B10722725 : Blo 782338 10722725 := bstep (se 4 (by rfl) ⟨1005255, by rfl⟩ : syracuseStep 10722725 = 2010511) B2010511
theorem B33889751 : Blo 782338 33889751 := bstep (se 1 (by rfl) ⟨25417313, by rfl⟩ : syracuseStep 33889751 = 50834627) B50834627
theorem B3579385 : Blo 782338 3579385 := bstep (se 2 (by rfl) ⟨1342269, by rfl⟩ : syracuseStep 3579385 = 2684539) B2684539
theorem B8494753 : Blo 782338 8494753 := bstep (se 2 (by rfl) ⟨3185532, by rfl⟩ : syracuseStep 8494753 = 6371065) B6371065
theorem B991055 : Blo 782338 991055 := bstep (se 1 (by rfl) ⟨743291, by rfl⟩ : syracuseStep 991055 = 1486583) B1486583
theorem B991207 : Blo 782338 991207 := bstep (se 1 (by rfl) ⟨743405, by rfl⟩ : syracuseStep 991207 = 1486811) B1486811
theorem B13607453 : Blo 782338 13607453 := bstep (se 3 (by rfl) ⟨2551397, by rfl⟩ : syracuseStep 13607453 = 5102795) B5102795
theorem B3351851 : Blo 782338 3351851 := bstep (se 1 (by rfl) ⟨2513888, by rfl⟩ : syracuseStep 3351851 = 5027777) B5027777
theorem B20063537 : Blo 782338 20063537 := bstep (se 2 (by rfl) ⟨7523826, by rfl⟩ : syracuseStep 20063537 = 15047653) B15047653
theorem B1255099 : Blo 782338 1255099 := bstep (se 1 (by rfl) ⟨941324, by rfl⟩ : syracuseStep 1255099 = 1882649) B1882649
theorem B8496829 : Blo 782338 8496829 := bstep (se 3 (by rfl) ⟨1593155, by rfl⟩ : syracuseStep 8496829 = 3186311) B3186311
theorem B1320745 : Blo 782338 1320745 := bstep (se 2 (by rfl) ⟨495279, by rfl⟩ : syracuseStep 1320745 = 990559) B990559
theorem B3974993 : Blo 782338 3974993 := bstep (se 2 (by rfl) ⟨1490622, by rfl⟩ : syracuseStep 3974993 = 2981245) B2981245
theorem B24095069 : Blo 782338 24095069 := bstep (se 3 (by rfl) ⟨4517825, by rfl⟩ : syracuseStep 24095069 = 9035651) B9035651
theorem B993647 : Blo 782338 993647 := bstep (se 1 (by rfl) ⟨745235, by rfl⟩ : syracuseStep 993647 = 1490471) B1490471
theorem B6695297 : Blo 782338 6695297 := bstep (se 2 (by rfl) ⟨2510736, by rfl⟩ : syracuseStep 6695297 = 5021473) B5021473
theorem B993703 : Blo 782338 993703 := bstep (se 1 (by rfl) ⟨745277, by rfl⟩ : syracuseStep 993703 = 1490555) B1490555
theorem B1485307 : Blo 782338 1485307 := bstep (se 1 (by rfl) ⟨1113980, by rfl⟩ : syracuseStep 1485307 = 2227961) B2227961
theorem B1321535 : Blo 782338 1321535 := bstep (se 1 (by rfl) ⟨991151, by rfl⟩ : syracuseStep 1321535 = 1982303) B1982303
theorem B3975803 : Blo 782338 3975803 := bstep (se 1 (by rfl) ⟨2981852, by rfl⟩ : syracuseStep 3975803 = 5963705) B5963705
theorem B1485535 : Blo 782338 1485535 := bstep (se 1 (by rfl) ⟨1114151, by rfl⟩ : syracuseStep 1485535 = 2228303) B2228303
theorem B994027 : Blo 782338 994027 := bstep (se 1 (by rfl) ⟨745520, by rfl⟩ : syracuseStep 994027 = 1491041) B1491041
theorem B5647229 : Blo 782338 5647229 := bstep (se 3 (by rfl) ⟨1058855, by rfl⟩ : syracuseStep 5647229 = 2117711) B2117711
theorem B1322203 : Blo 782338 1322203 := bstep (se 1 (by rfl) ⟨991652, by rfl⟩ : syracuseStep 1322203 = 1983305) B1983305
theorem B4238729 : Blo 782338 4238729 := bstep (se 2 (by rfl) ⟨1589523, by rfl⟩ : syracuseStep 4238729 = 3179047) B3179047
theorem B1486279 : Blo 782338 1486279 := bstep (se 1 (by rfl) ⟨1114709, by rfl⟩ : syracuseStep 1486279 = 2229419) B2229419
theorem B994999 : Blo 782338 994999 := bstep (se 1 (by rfl) ⟨746249, by rfl⟩ : syracuseStep 994999 = 1492499) B1492499
theorem B1322959 : Blo 782338 1322959 := bstep (se 1 (by rfl) ⟨992219, by rfl⟩ : syracuseStep 1322959 = 1984439) B1984439
theorem B1192283 : Blo 782338 1192283 := bstep (se 1 (by rfl) ⟨894212, by rfl⟩ : syracuseStep 1192283 = 1788425) B1788425
theorem B3977747 : Blo 782338 3977747 := bstep (se 1 (by rfl) ⟨2983310, by rfl⟩ : syracuseStep 3977747 = 5966621) B5966621
theorem B1323641 : Blo 782338 1323641 := bstep (se 2 (by rfl) ⟨496365, by rfl⟩ : syracuseStep 1323641 = 992731) B992731
theorem B1323695 : Blo 782338 1323695 := bstep (se 1 (by rfl) ⟨992771, by rfl⟩ : syracuseStep 1323695 = 1985543) B1985543
theorem B1323931 : Blo 782338 1323931 := bstep (se 1 (by rfl) ⟨992948, by rfl⟩ : syracuseStep 1323931 = 1985897) B1985897
theorem B5944265 : Blo 782338 5944265 := bstep (se 2 (by rfl) ⟨2229099, by rfl⟩ : syracuseStep 5944265 = 4458199) B4458199
theorem B1881227 : Blo 782338 1881227 := bstep (se 1 (by rfl) ⟨1410920, by rfl⟩ : syracuseStep 1881227 = 2821841) B2821841
theorem B4765067 : Blo 782338 4765067 := bstep (se 1 (by rfl) ⟨3573800, by rfl⟩ : syracuseStep 4765067 = 7147601) B7147601
theorem B1980521 : Blo 782338 1980521 := bstep (se 2 (by rfl) ⟨742695, by rfl⟩ : syracuseStep 1980521 = 1485391) B1485391
theorem B3979529 : Blo 782338 3979529 := bstep (se 2 (by rfl) ⟨1492323, by rfl⟩ : syracuseStep 3979529 = 2984647) B2984647
theorem B1325423 : Blo 782338 1325423 := bstep (se 1 (by rfl) ⟨994067, by rfl⟩ : syracuseStep 1325423 = 1988135) B1988135
theorem B16923005 : Blo 782338 16923005 := bstep (se 3 (by rfl) ⟨3173063, by rfl⟩ : syracuseStep 16923005 = 6346127) B6346127
theorem B1784339 : Blo 782338 1784339 := bstep (se 1 (by rfl) ⟨1338254, by rfl⟩ : syracuseStep 1784339 = 2676509) B2676509
theorem B1325639 : Blo 782338 1325639 := bstep (se 1 (by rfl) ⟨994229, by rfl⟩ : syracuseStep 1325639 = 1988459) B1988459
theorem B1981007 : Blo 782338 1981007 := bstep (se 1 (by rfl) ⟨1485755, by rfl⟩ : syracuseStep 1981007 = 2971511) B2971511
theorem B1489529 : Blo 782338 1489529 := bstep (se 2 (by rfl) ⟨558573, by rfl⟩ : syracuseStep 1489529 = 1117147) B1117147
theorem B12696203 : Blo 782338 12696203 := bstep (se 1 (by rfl) ⟨9522152, by rfl⟩ : syracuseStep 12696203 = 19044305) B19044305
theorem B1489583 : Blo 782338 1489583 := bstep (se 1 (by rfl) ⟨1117187, by rfl⟩ : syracuseStep 1489583 = 2234375) B2234375
theorem B1326071 : Blo 782338 1326071 := bstep (se 1 (by rfl) ⟨994553, by rfl⟩ : syracuseStep 1326071 = 1989107) B1989107
theorem B2145377 : Blo 782338 2145377 := bstep (se 2 (by rfl) ⟨804516, by rfl⟩ : syracuseStep 2145377 = 1609033) B1609033
theorem B3390587 : Blo 782338 3390587 := bstep (se 1 (by rfl) ⟨2542940, by rfl⟩ : syracuseStep 3390587 = 5085881) B5085881
theorem B1981655 : Blo 782338 1981655 := bstep (se 1 (by rfl) ⟨1486241, by rfl⟩ : syracuseStep 1981655 = 2972483) B2972483
theorem B3980663 : Blo 782338 3980663 := bstep (se 1 (by rfl) ⟨2985497, by rfl⟩ : syracuseStep 3980663 = 5970995) B5970995
theorem B4767113 : Blo 782338 4767113 := bstep (se 2 (by rfl) ⟨1787667, by rfl⟩ : syracuseStep 4767113 = 3575335) B3575335
theorem B5651927 : Blo 782338 5651927 := bstep (se 1 (by rfl) ⟨4238945, by rfl⟩ : syracuseStep 5651927 = 8477891) B8477891
theorem B4472279 : Blo 782338 4472279 := bstep (se 1 (by rfl) ⟨3354209, by rfl⟩ : syracuseStep 4472279 = 6708419) B6708419
theorem B3980825 : Blo 782338 3980825 := bstep (se 2 (by rfl) ⟨1492809, by rfl⟩ : syracuseStep 3980825 = 2985619) B2985619
theorem B1982009 : Blo 782338 1982009 := bstep (se 2 (by rfl) ⟨743253, by rfl⟩ : syracuseStep 1982009 = 1486507) B1486507
theorem B1326827 : Blo 782338 1326827 := bstep (se 1 (by rfl) ⟨995120, by rfl⟩ : syracuseStep 1326827 = 1990241) B1990241
theorem B418234211 : Blo 782338 418234211 := bstep (se 1 (by rfl) ⟨313675658, by rfl⟩ : syracuseStep 418234211 = 627351317) B627351317
theorem B1491367 : Blo 782338 1491367 := bstep (se 1 (by rfl) ⟨1118525, by rfl⟩ : syracuseStep 1491367 = 2237051) B2237051
theorem B1491527 : Blo 782338 1491527 := bstep (se 1 (by rfl) ⟨1118645, by rfl⟩ : syracuseStep 1491527 = 2237291) B2237291
theorem B1589881 : Blo 782338 1589881 := bstep (se 2 (by rfl) ⟨596205, by rfl⟩ : syracuseStep 1589881 = 1192411) B1192411
theorem B5030545 : Blo 782338 5030545 := bstep (se 2 (by rfl) ⟨1886454, by rfl⟩ : syracuseStep 5030545 = 3772909) B3772909
theorem B5948153 : Blo 782338 5948153 := bstep (se 2 (by rfl) ⟨2230557, by rfl⟩ : syracuseStep 5948153 = 4461115) B4461115
theorem B10175291 : Blo 782338 10175291 := bstep (se 1 (by rfl) ⟨7631468, by rfl⟩ : syracuseStep 10175291 = 15262937) B15262937
theorem B1491959 : Blo 782338 1491959 := bstep (se 1 (by rfl) ⟨1118969, by rfl⟩ : syracuseStep 1491959 = 2237939) B2237939
theorem B1492111 : Blo 782338 1492111 := bstep (se 1 (by rfl) ⟨1119083, by rfl⟩ : syracuseStep 1492111 = 2238167) B2238167
theorem B16139407 : Blo 782338 16139407 := bstep (se 1 (by rfl) ⟨12104555, by rfl⟩ : syracuseStep 16139407 = 24209111) B24209111
theorem B4474055 : Blo 782338 4474055 := bstep (se 1 (by rfl) ⟨3355541, by rfl⟩ : syracuseStep 4474055 = 6711083) B6711083
theorem B43500887 : Blo 782338 43500887 := bstep (se 1 (by rfl) ⟨32625665, by rfl⟩ : syracuseStep 43500887 = 65251331) B65251331
theorem B1885639 : Blo 782338 1885639 := bstep (se 1 (by rfl) ⟨1414229, by rfl⟩ : syracuseStep 1885639 = 2828459) B2828459
theorem B1984297 : Blo 782338 1984297 := bstep (se 2 (by rfl) ⟨744111, by rfl⟩ : syracuseStep 1984297 = 1488223) B1488223
theorem B21481325 : Blo 782338 21481325 := bstep (se 3 (by rfl) ⟨4027748, by rfl⟩ : syracuseStep 21481325 = 8055497) B8055497
theorem B12699575 : Blo 782338 12699575 := bstep (se 1 (by rfl) ⟨9524681, by rfl⟩ : syracuseStep 12699575 = 19049363) B19049363
theorem B7161871 : Blo 782338 7161871 := bstep (se 1 (by rfl) ⟨5371403, by rfl⟩ : syracuseStep 7161871 = 10742807) B10742807
theorem B2148457 : Blo 782338 2148457 := bstep (se 2 (by rfl) ⟨805671, by rfl⟩ : syracuseStep 2148457 = 1611343) B1611343
theorem B6703397 : Blo 782338 6703397 := bstep (se 4 (by rfl) ⟨628443, by rfl⟩ : syracuseStep 6703397 = 1256887) B1256887
theorem B7653761 : Blo 782338 7653761 := bstep (se 2 (by rfl) ⟨2870160, by rfl⟩ : syracuseStep 7653761 = 5740321) B5740321
theorem B1886647 : Blo 782338 1886647 := bstep (se 1 (by rfl) ⟨1414985, by rfl⟩ : syracuseStep 1886647 = 2829971) B2829971
theorem B1985087 : Blo 782338 1985087 := bstep (se 1 (by rfl) ⟨1488815, by rfl⟩ : syracuseStep 1985087 = 2977631) B2977631
theorem B2640491 : Blo 782338 2640491 := bstep (se 1 (by rfl) ⟨1980368, by rfl⟩ : syracuseStep 2640491 = 3960737) B3960737
theorem B10046531 : Blo 782338 10046531 := bstep (se 1 (by rfl) ⟨7534898, by rfl⟩ : syracuseStep 10046531 = 15069797) B15069797
theorem B2116705 : Blo 782338 2116705 := bstep (se 2 (by rfl) ⟨793764, by rfl⟩ : syracuseStep 2116705 = 1587529) B1587529
theorem B2641085 : Blo 782338 2641085 := bstep (se 3 (by rfl) ⟨495203, by rfl⟩ : syracuseStep 2641085 = 990407) B990407
theorem B1985735 : Blo 782338 1985735 := bstep (se 1 (by rfl) ⟨1489301, by rfl⟩ : syracuseStep 1985735 = 2978603) B2978603
theorem B1985755 : Blo 782338 1985755 := bstep (se 1 (by rfl) ⟨1489316, by rfl⟩ : syracuseStep 1985755 = 2978633) B2978633
theorem B2149595 : Blo 782338 2149595 := bstep (se 1 (by rfl) ⟨1612196, by rfl⟩ : syracuseStep 2149595 = 3224393) B3224393
theorem B4476221 : Blo 782338 4476221 := bstep (se 3 (by rfl) ⟨839291, by rfl⟩ : syracuseStep 4476221 = 1678583) B1678583
theorem B16076353 : Blo 782338 16076353 := bstep (se 2 (by rfl) ⟨6028632, by rfl⟩ : syracuseStep 16076353 = 12057265) B12057265
theorem B2543407 : Blo 782338 2543407 := bstep (se 1 (by rfl) ⟨1907555, by rfl⟩ : syracuseStep 2543407 = 3815111) B3815111
theorem B33967937 : Blo 782338 33967937 := bstep (se 2 (by rfl) ⟨12737976, by rfl⟩ : syracuseStep 33967937 = 25475953) B25475953
theorem B6344669 : Blo 782338 6344669 := bstep (se 3 (by rfl) ⟨1189625, by rfl⟩ : syracuseStep 6344669 = 2379251) B2379251
theorem B5951555 : Blo 782338 5951555 := bstep (se 1 (by rfl) ⟨4463666, by rfl⟩ : syracuseStep 5951555 = 8927333) B8927333
theorem B1986889 : Blo 782338 1986889 := bstep (se 2 (by rfl) ⟨745083, by rfl⟩ : syracuseStep 1986889 = 1490167) B1490167
theorem B3494345 : Blo 782338 3494345 := bstep (se 2 (by rfl) ⟨1310379, by rfl⟩ : syracuseStep 3494345 = 2620759) B2620759
theorem B1987193 : Blo 782338 1987193 := bstep (se 2 (by rfl) ⟨745197, by rfl⟩ : syracuseStep 1987193 = 1490395) B1490395
theorem B5034953 : Blo 782338 5034953 := bstep (se 2 (by rfl) ⟨1888107, by rfl⟩ : syracuseStep 5034953 = 3776215) B3776215
theorem B2118845 : Blo 782338 2118845 := bstep (se 3 (by rfl) ⟨397283, by rfl⟩ : syracuseStep 2118845 = 794567) B794567
theorem B3921095 : Blo 782338 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B2970857 : Blo 782338 2970857 := bstep (se 2 (by rfl) ⟨1114071, by rfl⟩ : syracuseStep 2970857 = 2228143) B2228143
theorem B1791571 : Blo 782338 1791571 := bstep (se 1 (by rfl) ⟨1343678, by rfl⟩ : syracuseStep 1791571 = 2687357) B2687357
theorem B2644001 : Blo 782338 2644001 := bstep (se 2 (by rfl) ⟨991500, by rfl⟩ : syracuseStep 2644001 = 1983001) B1983001
theorem B69556493 : Blo 782338 69556493 := bstep (se 3 (by rfl) ⟨13041842, by rfl⟩ : syracuseStep 69556493 = 26083685) B26083685
theorem B1988975 : Blo 782338 1988975 := bstep (se 1 (by rfl) ⟨1491731, by rfl⟩ : syracuseStep 1988975 = 2983463) B2983463
theorem B6707771 : Blo 782338 6707771 := bstep (se 1 (by rfl) ⟨5030828, by rfl⟩ : syracuseStep 6707771 = 10061657) B10061657
theorem B2513683 : Blo 782338 2513683 := bstep (se 1 (by rfl) ⟨1885262, by rfl⟩ : syracuseStep 2513683 = 3770525) B3770525
theorem B8575931 : Blo 782338 8575931 := bstep (se 1 (by rfl) ⟨6431948, by rfl⟩ : syracuseStep 8575931 = 12863897) B12863897
theorem B1989623 : Blo 782338 1989623 := bstep (se 1 (by rfl) ⟨1492217, by rfl⟩ : syracuseStep 1989623 = 2984435) B2984435
theorem B1989755 : Blo 782338 1989755 := bstep (se 1 (by rfl) ⟨1492316, by rfl⟩ : syracuseStep 1989755 = 2984633) B2984633
theorem B1760399 : Blo 782338 1760399 := bstep (se 1 (by rfl) ⟨1320299, by rfl⟩ : syracuseStep 1760399 = 2640599) B2640599
theorem B1760489 : Blo 782338 1760489 := bstep (se 2 (by rfl) ⟨660183, by rfl⟩ : syracuseStep 1760489 = 1320367) B1320367
theorem B1760543 : Blo 782338 1760543 := bstep (se 1 (by rfl) ⟨1320407, by rfl⟩ : syracuseStep 1760543 = 2640815) B2640815
theorem B941743 : Blo 782338 941743 := bstep (se 1 (by rfl) ⟨706307, by rfl⟩ : syracuseStep 941743 = 1412615) B1412615
theorem B1761065 : Blo 782338 1761065 := bstep (se 2 (by rfl) ⟨660399, by rfl⟩ : syracuseStep 1761065 = 1320799) B1320799
theorem B2121527 : Blo 782338 2121527 := bstep (se 1 (by rfl) ⟨1591145, by rfl⟩ : syracuseStep 2121527 = 3182291) B3182291
theorem B64545173 : Blo 782338 64545173 := bstep (se 6 (by rfl) ⟨1512777, by rfl⟩ : syracuseStep 64545173 = 3025555) B3025555
theorem B1762127 : Blo 782338 1762127 := bstep (se 1 (by rfl) ⟨1321595, by rfl⟩ : syracuseStep 1762127 = 2643191) B2643191
theorem B2646863 : Blo 782338 2646863 := bstep (se 1 (by rfl) ⟨1985147, by rfl⟩ : syracuseStep 2646863 = 3970295) B3970295
theorem B1762343 : Blo 782338 1762343 := bstep (se 1 (by rfl) ⟨1321757, by rfl⟩ : syracuseStep 1762343 = 2643515) B2643515
theorem B2516093 : Blo 782338 2516093 := bstep (se 3 (by rfl) ⟨471767, by rfl⟩ : syracuseStep 2516093 = 943535) B943535
theorem B2647187 : Blo 782338 2647187 := bstep (se 1 (by rfl) ⟨1985390, by rfl⟩ : syracuseStep 2647187 = 3970781) B3970781
theorem B1762523 : Blo 782338 1762523 := bstep (se 1 (by rfl) ⟨1321892, by rfl⟩ : syracuseStep 1762523 = 2643785) B2643785
theorem B5662075 : Blo 782338 5662075 := bstep (se 1 (by rfl) ⟨4246556, by rfl⟩ : syracuseStep 5662075 = 8493113) B8493113
theorem B1762721 : Blo 782338 1762721 := bstep (se 2 (by rfl) ⟨661020, by rfl⟩ : syracuseStep 1762721 = 1322041) B1322041
theorem B2647457 : Blo 782338 2647457 := bstep (se 2 (by rfl) ⟨992796, by rfl⟩ : syracuseStep 2647457 = 1985593) B1985593
theorem B27223897 : Blo 782338 27223897 := bstep (se 2 (by rfl) ⟨10208961, by rfl⟩ : syracuseStep 27223897 = 20417923) B20417923
theorem B1763279 : Blo 782338 1763279 := bstep (se 1 (by rfl) ⟨1322459, by rfl⟩ : syracuseStep 1763279 = 2644919) B2644919
theorem B1763657 : Blo 782338 1763657 := bstep (se 2 (by rfl) ⟨661371, by rfl⟩ : syracuseStep 1763657 = 1322743) B1322743
theorem B1173851 : Blo 782338 1173851 := bstep (se 1 (by rfl) ⟨880388, by rfl⟩ : syracuseStep 1173851 = 1760777) B1760777
theorem B1763675 : Blo 782338 1763675 := bstep (se 1 (by rfl) ⟨1322756, by rfl⟩ : syracuseStep 1763675 = 2645513) B2645513
theorem B3762683 : Blo 782338 3762683 := bstep (se 1 (by rfl) ⟨2822012, by rfl⟩ : syracuseStep 3762683 = 5644025) B5644025
theorem B1174079 : Blo 782338 1174079 := bstep (se 1 (by rfl) ⟨880559, by rfl⟩ : syracuseStep 1174079 = 1761119) B1761119
theorem B6777431 : Blo 782338 6777431 := bstep (se 1 (by rfl) ⟨5083073, by rfl⟩ : syracuseStep 6777431 = 10166147) B10166147
theorem B1174199 : Blo 782338 1174199 := bstep (se 1 (by rfl) ⟨880649, by rfl⟩ : syracuseStep 1174199 = 1761299) B1761299
theorem B1174427 : Blo 782338 1174427 := bstep (se 1 (by rfl) ⟨880820, by rfl⟩ : syracuseStep 1174427 = 1761641) B1761641
theorem B1764251 : Blo 782338 1764251 := bstep (se 1 (by rfl) ⟨1323188, by rfl⟩ : syracuseStep 1764251 = 2646377) B2646377
theorem B1764449 : Blo 782338 1764449 := bstep (se 2 (by rfl) ⟨661668, by rfl⟩ : syracuseStep 1764449 = 1323337) B1323337
theorem B1174823 : Blo 782338 1174823 := bstep (se 1 (by rfl) ⟨881117, by rfl⟩ : syracuseStep 1174823 = 1762235) B1762235
theorem B1764647 : Blo 782338 1764647 := bstep (se 1 (by rfl) ⟨1323485, by rfl⟩ : syracuseStep 1764647 = 2646971) B2646971
theorem B1174907 : Blo 782338 1174907 := bstep (se 1 (by rfl) ⟨881180, by rfl⟩ : syracuseStep 1174907 = 1762361) B1762361
theorem B1175033 : Blo 782338 1175033 := bstep (se 2 (by rfl) ⟨440637, by rfl⟩ : syracuseStep 1175033 = 881275) B881275
theorem B1175135 : Blo 782338 1175135 := bstep (se 1 (by rfl) ⟨881351, by rfl⟩ : syracuseStep 1175135 = 1762703) B1762703
theorem B1765025 : Blo 782338 1765025 := bstep (se 2 (by rfl) ⟨661884, by rfl⟩ : syracuseStep 1765025 = 1323769) B1323769
theorem B5959331 : Blo 782338 5959331 := bstep (se 1 (by rfl) ⟨4469498, by rfl⟩ : syracuseStep 5959331 = 8938997) B8938997
theorem B880303 : Blo 782338 880303 := bstep (se 1 (by rfl) ⟨660227, by rfl⟩ : syracuseStep 880303 = 1320455) B1320455
theorem B1175351 : Blo 782338 1175351 := bstep (se 1 (by rfl) ⟨881513, by rfl⟩ : syracuseStep 1175351 = 1763027) B1763027
theorem B880591 : Blo 782338 880591 := bstep (se 1 (by rfl) ⟨660443, by rfl⟩ : syracuseStep 880591 = 1320887) B1320887
theorem B1765385 : Blo 782338 1765385 := bstep (se 2 (by rfl) ⟨662019, by rfl⟩ : syracuseStep 1765385 = 1324039) B1324039
theorem B1175657 : Blo 782338 1175657 := bstep (se 2 (by rfl) ⟨440871, by rfl⟩ : syracuseStep 1175657 = 881743) B881743
theorem B7532747 : Blo 782338 7532747 := bstep (se 1 (by rfl) ⟨5649560, by rfl⟩ : syracuseStep 7532747 = 11299121) B11299121
theorem B782623 : Blo 782338 782623 := bstep (se 1 (by rfl) ⟨586967, by rfl⟩ : syracuseStep 782623 = 1173935) B1173935
theorem B782683 : Blo 782338 782683 := bstep (se 1 (by rfl) ⟨587012, by rfl⟩ : syracuseStep 782683 = 1174025) B1174025
theorem B880987 : Blo 782338 880987 := bstep (se 1 (by rfl) ⟨660740, by rfl⟩ : syracuseStep 880987 = 1321481) B1321481
theorem B782703 : Blo 782338 782703 := bstep (se 1 (by rfl) ⟨587027, by rfl⟩ : syracuseStep 782703 = 1174055) B1174055
theorem B782759 : Blo 782338 782759 := bstep (se 1 (by rfl) ⟨587069, by rfl⟩ : syracuseStep 782759 = 1174139) B1174139
theorem B1175975 : Blo 782338 1175975 := bstep (se 1 (by rfl) ⟨881981, by rfl⟩ : syracuseStep 1175975 = 1763963) B1763963
theorem B1765799 : Blo 782338 1765799 := bstep (se 1 (by rfl) ⟨1324349, by rfl⟩ : syracuseStep 1765799 = 2648699) B2648699
theorem B881095 : Blo 782338 881095 := bstep (se 1 (by rfl) ⟨660821, by rfl⟩ : syracuseStep 881095 = 1321643) B1321643
theorem B782843 : Blo 782338 782843 := bstep (se 1 (by rfl) ⟨587132, by rfl⟩ : syracuseStep 782843 = 1174265) B1174265
theorem B1176059 : Blo 782338 1176059 := bstep (se 1 (by rfl) ⟨882044, by rfl⟩ : syracuseStep 1176059 = 1764089) B1764089
theorem B1765907 : Blo 782338 1765907 := bstep (se 1 (by rfl) ⟨1324430, by rfl⟩ : syracuseStep 1765907 = 2648861) B2648861
theorem B2650643 : Blo 782338 2650643 := bstep (se 1 (by rfl) ⟨1987982, by rfl⟩ : syracuseStep 2650643 = 3975965) B3975965
theorem B782911 : Blo 782338 782911 := bstep (se 1 (by rfl) ⟨587183, by rfl⟩ : syracuseStep 782911 = 1174367) B1174367
theorem B782919 : Blo 782338 782919 := bstep (se 1 (by rfl) ⟨587189, by rfl⟩ : syracuseStep 782919 = 1174379) B1174379
theorem B1765961 : Blo 782338 1765961 := bstep (se 2 (by rfl) ⟨662235, by rfl⟩ : syracuseStep 1765961 = 1324471) B1324471
theorem B1340011 : Blo 782338 1340011 := bstep (se 1 (by rfl) ⟨1005008, by rfl⟩ : syracuseStep 1340011 = 2010017) B2010017
theorem B1176185 : Blo 782338 1176185 := bstep (se 2 (by rfl) ⟨441069, by rfl⟩ : syracuseStep 1176185 = 882139) B882139
theorem B25457273 : Blo 782338 25457273 := bstep (se 2 (by rfl) ⟨9546477, by rfl⟩ : syracuseStep 25457273 = 19092955) B19092955
theorem B1176239 : Blo 782338 1176239 := bstep (se 1 (by rfl) ⟨882179, by rfl⟩ : syracuseStep 1176239 = 1764359) B1764359
theorem B3961547 : Blo 782338 3961547 := bstep (se 1 (by rfl) ⟨2971160, by rfl⟩ : syracuseStep 3961547 = 5942321) B5942321
theorem B783071 : Blo 782338 783071 := bstep (se 1 (by rfl) ⟨587303, by rfl⟩ : syracuseStep 783071 = 1174607) B1174607
theorem B1176287 : Blo 782338 1176287 := bstep (se 1 (by rfl) ⟨882215, by rfl⟩ : syracuseStep 1176287 = 1764431) B1764431
theorem B14480117 : Blo 782338 14480117 := bstep (se 5 (by rfl) ⟨678755, by rfl⟩ : syracuseStep 14480117 = 1357511) B1357511
theorem B783151 : Blo 782338 783151 := bstep (se 1 (by rfl) ⟨587363, by rfl⟩ : syracuseStep 783151 = 1174727) B1174727
theorem B881455 : Blo 782338 881455 := bstep (se 1 (by rfl) ⟨661091, by rfl⟩ : syracuseStep 881455 = 1322183) B1322183
theorem B3961709 : Blo 782338 3961709 := bstep (se 3 (by rfl) ⟨742820, by rfl⟩ : syracuseStep 3961709 = 1485641) B1485641
theorem B783259 : Blo 782338 783259 := bstep (se 1 (by rfl) ⟨587444, by rfl⟩ : syracuseStep 783259 = 1174889) B1174889
theorem B881563 : Blo 782338 881563 := bstep (se 1 (by rfl) ⟨661172, by rfl⟩ : syracuseStep 881563 = 1322345) B1322345
theorem B783311 : Blo 782338 783311 := bstep (se 1 (by rfl) ⟨587483, by rfl⟩ : syracuseStep 783311 = 1174967) B1174967
theorem B783335 : Blo 782338 783335 := bstep (se 1 (by rfl) ⟨587501, by rfl⟩ : syracuseStep 783335 = 1175003) B1175003
theorem B1176551 : Blo 782338 1176551 := bstep (se 1 (by rfl) ⟨882413, by rfl⟩ : syracuseStep 1176551 = 1764827) B1764827
theorem B1766375 : Blo 782338 1766375 := bstep (se 1 (by rfl) ⟨1324781, by rfl⟩ : syracuseStep 1766375 = 2649563) B2649563
theorem B1176809 : Blo 782338 1176809 := bstep (se 2 (by rfl) ⟨441303, by rfl⟩ : syracuseStep 1176809 = 882607) B882607
theorem B3765491 : Blo 782338 3765491 := bstep (se 1 (by rfl) ⟨2824118, by rfl⟩ : syracuseStep 3765491 = 5648237) B5648237
theorem B10712321 : Blo 782338 10712321 := bstep (se 2 (by rfl) ⟨4017120, by rfl⟩ : syracuseStep 10712321 = 8034241) B8034241
theorem B783647 : Blo 782338 783647 := bstep (se 1 (by rfl) ⟨587735, by rfl⟩ : syracuseStep 783647 = 1175471) B1175471
theorem B1176863 : Blo 782338 1176863 := bstep (se 1 (by rfl) ⟨882647, by rfl⟩ : syracuseStep 1176863 = 1765295) B1765295
theorem B881959 : Blo 782338 881959 := bstep (se 1 (by rfl) ⟨661469, by rfl⟩ : syracuseStep 881959 = 1322939) B1322939
theorem B783707 : Blo 782338 783707 := bstep (se 1 (by rfl) ⟨587780, by rfl⟩ : syracuseStep 783707 = 1175561) B1175561
theorem B1766753 : Blo 782338 1766753 := bstep (se 2 (by rfl) ⟨662532, by rfl⟩ : syracuseStep 1766753 = 1325065) B1325065
theorem B783727 : Blo 782338 783727 := bstep (se 1 (by rfl) ⟨587795, by rfl⟩ : syracuseStep 783727 = 1175591) B1175591
theorem B882031 : Blo 782338 882031 := bstep (se 1 (by rfl) ⟨661523, by rfl⟩ : syracuseStep 882031 = 1323047) B1323047
theorem B783783 : Blo 782338 783783 := bstep (se 1 (by rfl) ⟨587837, by rfl⟩ : syracuseStep 783783 = 1175675) B1175675
theorem B1766843 : Blo 782338 1766843 := bstep (se 1 (by rfl) ⟨1325132, by rfl⟩ : syracuseStep 1766843 = 2650265) B2650265
theorem B1177031 : Blo 782338 1177031 := bstep (se 1 (by rfl) ⟨882773, by rfl⟩ : syracuseStep 1177031 = 1765547) B1765547
theorem B783867 : Blo 782338 783867 := bstep (se 1 (by rfl) ⟨587900, by rfl⟩ : syracuseStep 783867 = 1175801) B1175801
theorem B1766969 : Blo 782338 1766969 := bstep (se 2 (by rfl) ⟨662613, by rfl⟩ : syracuseStep 1766969 = 1325227) B1325227
theorem B783935 : Blo 782338 783935 := bstep (se 1 (by rfl) ⟨587951, by rfl⟩ : syracuseStep 783935 = 1175903) B1175903
theorem B783943 : Blo 782338 783943 := bstep (se 1 (by rfl) ⟨587957, by rfl⟩ : syracuseStep 783943 = 1175915) B1175915
theorem B882247 : Blo 782338 882247 := bstep (se 1 (by rfl) ⟨661685, by rfl⟩ : syracuseStep 882247 = 1323371) B1323371
theorem B784095 : Blo 782338 784095 := bstep (se 1 (by rfl) ⟨588071, by rfl⟩ : syracuseStep 784095 = 1176143) B1176143
theorem B1177385 : Blo 782338 1177385 := bstep (se 2 (by rfl) ⟨441519, by rfl⟩ : syracuseStep 1177385 = 883039) B883039
theorem B784175 : Blo 782338 784175 := bstep (se 1 (by rfl) ⟨588131, by rfl⟩ : syracuseStep 784175 = 1176263) B1176263
theorem B1177391 : Blo 782338 1177391 := bstep (se 1 (by rfl) ⟨883043, by rfl⟩ : syracuseStep 1177391 = 1766087) B1766087
theorem B784283 : Blo 782338 784283 := bstep (se 1 (by rfl) ⟨588212, by rfl⟩ : syracuseStep 784283 = 1176425) B1176425
theorem B784335 : Blo 782338 784335 := bstep (se 1 (by rfl) ⟨588251, by rfl⟩ : syracuseStep 784335 = 1176503) B1176503
theorem B784359 : Blo 782338 784359 := bstep (se 1 (by rfl) ⟨588269, by rfl⟩ : syracuseStep 784359 = 1176539) B1176539
theorem B5961761 : Blo 782338 5961761 := bstep (se 2 (by rfl) ⟨2235660, by rfl⟩ : syracuseStep 5961761 = 4471321) B4471321
theorem B1767635 : Blo 782338 1767635 := bstep (se 1 (by rfl) ⟨1325726, by rfl⟩ : syracuseStep 1767635 = 2651453) B2651453
theorem B1177865 : Blo 782338 1177865 := bstep (se 2 (by rfl) ⟨441699, by rfl⟩ : syracuseStep 1177865 = 883399) B883399
theorem B1767689 : Blo 782338 1767689 := bstep (se 2 (by rfl) ⟨662883, by rfl⟩ : syracuseStep 1767689 = 1325767) B1325767
theorem B2652425 : Blo 782338 2652425 := bstep (se 2 (by rfl) ⟨994659, by rfl⟩ : syracuseStep 2652425 = 1989319) B1989319
theorem B784671 : Blo 782338 784671 := bstep (se 1 (by rfl) ⟨588503, by rfl⟩ : syracuseStep 784671 = 1177007) B1177007
theorem B6453593 : Blo 782338 6453593 := bstep (se 2 (by rfl) ⟨2420097, by rfl⟩ : syracuseStep 6453593 = 4840195) B4840195
theorem B784731 : Blo 782338 784731 := bstep (se 1 (by rfl) ⟨588548, by rfl⟩ : syracuseStep 784731 = 1177097) B1177097
theorem B784751 : Blo 782338 784751 := bstep (se 1 (by rfl) ⟨588563, by rfl⟩ : syracuseStep 784751 = 1177127) B1177127
theorem B1177967 : Blo 782338 1177967 := bstep (se 1 (by rfl) ⟨883475, by rfl⟩ : syracuseStep 1177967 = 1766951) B1766951
theorem B784807 : Blo 782338 784807 := bstep (se 1 (by rfl) ⟨588605, by rfl⟩ : syracuseStep 784807 = 1177211) B1177211
theorem B883111 : Blo 782338 883111 := bstep (se 1 (by rfl) ⟨662333, by rfl⟩ : syracuseStep 883111 = 1324667) B1324667
theorem B1767905 : Blo 782338 1767905 := bstep (se 2 (by rfl) ⟨662964, by rfl⟩ : syracuseStep 1767905 = 1325929) B1325929
theorem B784891 : Blo 782338 784891 := bstep (se 1 (by rfl) ⟨588668, by rfl⟩ : syracuseStep 784891 = 1177337) B1177337
theorem B784959 : Blo 782338 784959 := bstep (se 1 (by rfl) ⟨588719, by rfl⟩ : syracuseStep 784959 = 1177439) B1177439
theorem B784967 : Blo 782338 784967 := bstep (se 1 (by rfl) ⟨588725, by rfl⟩ : syracuseStep 784967 = 1177451) B1177451
theorem B1178183 : Blo 782338 1178183 := bstep (se 1 (by rfl) ⟨883637, by rfl⟩ : syracuseStep 1178183 = 1767275) B1767275
theorem B1178219 : Blo 782338 1178219 := bstep (se 1 (by rfl) ⟨883664, by rfl⟩ : syracuseStep 1178219 = 1767329) B1767329
theorem B2980547 : Blo 782338 2980547 := bstep (se 1 (by rfl) ⟨2235410, by rfl⟩ : syracuseStep 2980547 = 4470821) B4470821
theorem B785119 : Blo 782338 785119 := bstep (se 1 (by rfl) ⟨588839, by rfl⟩ : syracuseStep 785119 = 1177679) B1177679
theorem B6716141 : Blo 782338 6716141 := bstep (se 3 (by rfl) ⟨1259276, by rfl⟩ : syracuseStep 6716141 = 2518553) B2518553
theorem B1768211 : Blo 782338 1768211 := bstep (se 1 (by rfl) ⟨1326158, by rfl⟩ : syracuseStep 1768211 = 2652317) B2652317
theorem B785199 : Blo 782338 785199 := bstep (se 1 (by rfl) ⟨588899, by rfl⟩ : syracuseStep 785199 = 1177799) B1177799
theorem B1178447 : Blo 782338 1178447 := bstep (se 1 (by rfl) ⟨883835, by rfl⟩ : syracuseStep 1178447 = 1767671) B1767671
theorem B785307 : Blo 782338 785307 := bstep (se 1 (by rfl) ⟨588980, by rfl⟩ : syracuseStep 785307 = 1177961) B1177961
theorem B785359 : Blo 782338 785359 := bstep (se 1 (by rfl) ⟨589019, by rfl⟩ : syracuseStep 785359 = 1178039) B1178039
theorem B785383 : Blo 782338 785383 := bstep (se 1 (by rfl) ⟨589037, by rfl⟩ : syracuseStep 785383 = 1178075) B1178075
theorem B883687 : Blo 782338 883687 := bstep (se 1 (by rfl) ⟨662765, by rfl⟩ : syracuseStep 883687 = 1325531) B1325531
theorem B1768571 : Blo 782338 1768571 := bstep (se 1 (by rfl) ⟨1326428, by rfl⟩ : syracuseStep 1768571 = 2652857) B2652857
theorem B8944829 : Blo 782338 8944829 := bstep (se 3 (by rfl) ⟨1677155, by rfl⟩ : syracuseStep 8944829 = 3354311) B3354311
theorem B1178843 : Blo 782338 1178843 := bstep (se 1 (by rfl) ⟨884132, by rfl⟩ : syracuseStep 1178843 = 1768265) B1768265
theorem B1768697 : Blo 782338 1768697 := bstep (se 2 (by rfl) ⟨663261, by rfl⟩ : syracuseStep 1768697 = 1326523) B1326523
theorem B785695 : Blo 782338 785695 := bstep (se 1 (by rfl) ⟨589271, by rfl⟩ : syracuseStep 785695 = 1178543) B1178543
theorem B785755 : Blo 782338 785755 := bstep (se 1 (by rfl) ⟨589316, by rfl⟩ : syracuseStep 785755 = 1178633) B1178633
theorem B785775 : Blo 782338 785775 := bstep (se 1 (by rfl) ⟨589331, by rfl⟩ : syracuseStep 785775 = 1178663) B1178663
theorem B2653559 : Blo 782338 2653559 := bstep (se 1 (by rfl) ⟨1990169, by rfl⟩ : syracuseStep 2653559 = 3980339) B3980339
theorem B3440009 : Blo 782338 3440009 := bstep (se 2 (by rfl) ⟨1290003, by rfl⟩ : syracuseStep 3440009 = 2580007) B2580007
theorem B1179017 : Blo 782338 1179017 := bstep (se 2 (by rfl) ⟨442131, by rfl⟩ : syracuseStep 1179017 = 884263) B884263
theorem B1768841 : Blo 782338 1768841 := bstep (se 2 (by rfl) ⟨663315, by rfl⟩ : syracuseStep 1768841 = 1326631) B1326631
theorem B785831 : Blo 782338 785831 := bstep (se 1 (by rfl) ⟨589373, by rfl⟩ : syracuseStep 785831 = 1178747) B1178747
theorem B785915 : Blo 782338 785915 := bstep (se 1 (by rfl) ⟨589436, by rfl⟩ : syracuseStep 785915 = 1178873) B1178873
theorem B1768967 : Blo 782338 1768967 := bstep (se 1 (by rfl) ⟨1326725, by rfl⟩ : syracuseStep 1768967 = 2653451) B2653451
theorem B785983 : Blo 782338 785983 := bstep (se 1 (by rfl) ⟨589487, by rfl⟩ : syracuseStep 785983 = 1178975) B1178975
theorem B785991 : Blo 782338 785991 := bstep (se 1 (by rfl) ⟨589493, by rfl⟩ : syracuseStep 785991 = 1178987) B1178987
theorem B1769147 : Blo 782338 1769147 := bstep (se 1 (by rfl) ⟨1326860, by rfl⟩ : syracuseStep 1769147 = 2653721) B2653721
theorem B3964625 : Blo 782338 3964625 := bstep (se 2 (by rfl) ⟨1486734, by rfl⟩ : syracuseStep 3964625 = 2973469) B2973469
theorem B786143 : Blo 782338 786143 := bstep (se 1 (by rfl) ⟨589607, by rfl⟩ : syracuseStep 786143 = 1179215) B1179215
theorem B1179371 : Blo 782338 1179371 := bstep (se 1 (by rfl) ⟨884528, by rfl⟩ : syracuseStep 1179371 = 1769057) B1769057
theorem B786223 : Blo 782338 786223 := bstep (se 1 (by rfl) ⟨589667, by rfl⟩ : syracuseStep 786223 = 1179335) B1179335
theorem B7241567 : Blo 782338 7241567 := bstep (se 1 (by rfl) ⟨5431175, by rfl⟩ : syracuseStep 7241567 = 10862351) B10862351
theorem B786331 : Blo 782338 786331 := bstep (se 1 (by rfl) ⟨589748, by rfl⟩ : syracuseStep 786331 = 1179497) B1179497
theorem B3965435 : Blo 782338 3965435 := bstep (se 1 (by rfl) ⟨2974076, by rfl⟩ : syracuseStep 3965435 = 5948153) B5948153
theorem B6783527 : Blo 782338 6783527 := bstep (se 1 (by rfl) ⟨5087645, by rfl⟩ : syracuseStep 6783527 = 10175291) B10175291
theorem B2982703 : Blo 782338 2982703 := bstep (se 1 (by rfl) ⟨2237027, by rfl⟩ : syracuseStep 2982703 = 4474055) B4474055
theorem B29000591 : Blo 782338 29000591 := bstep (se 1 (by rfl) ⟨21750443, by rfl⟩ : syracuseStep 29000591 = 43500887) B43500887
theorem B2950031 : Blo 782338 2950031 := bstep (se 1 (by rfl) ⟨2212523, by rfl⟩ : syracuseStep 2950031 = 4425047) B4425047
theorem B14320883 : Blo 782338 14320883 := bstep (se 1 (by rfl) ⟨10740662, by rfl⟩ : syracuseStep 14320883 = 21481325) B21481325
theorem B3343787 : Blo 782338 3343787 := bstep (se 1 (by rfl) ⟨2507840, by rfl⟩ : syracuseStep 3343787 = 5015681) B5015681
theorem B2984147 : Blo 782338 2984147 := bstep (se 1 (by rfl) ⟨2238110, by rfl⟩ : syracuseStep 2984147 = 4476221) B4476221
theorem B1673465 : Blo 782338 1673465 := bstep (se 2 (by rfl) ⟨627549, by rfl⟩ : syracuseStep 1673465 = 1255099) B1255099
theorem B1116703 : Blo 782338 1116703 := bstep (se 1 (by rfl) ⟨837527, by rfl⟩ : syracuseStep 1116703 = 1675055) B1675055
theorem B22645291 : Blo 782338 22645291 := bstep (se 1 (by rfl) ⟨16983968, by rfl⟩ : syracuseStep 22645291 = 33967937) B33967937
theorem B4229779 : Blo 782338 4229779 := bstep (se 1 (by rfl) ⟨3172334, by rfl⟩ : syracuseStep 4229779 = 6344669) B6344669
theorem B3967703 : Blo 782338 3967703 := bstep (se 1 (by rfl) ⟨2975777, by rfl⟩ : syracuseStep 3967703 = 5951555) B5951555
theorem B10456253 : Blo 782338 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B2231675 : Blo 782338 2231675 := bstep (se 1 (by rfl) ⟨1673756, by rfl⟩ : syracuseStep 2231675 = 3347513) B3347513
theorem B1412563 : Blo 782338 1412563 := bstep (se 1 (by rfl) ⟨1059422, by rfl⟩ : syracuseStep 1412563 = 2118845) B2118845
theorem B921179 : Blo 782338 921179 := bstep (se 1 (by rfl) ⟨690884, by rfl⟩ : syracuseStep 921179 = 1381769) B1381769
theorem B13406309 : Blo 782338 13406309 := bstep (se 4 (by rfl) ⟨1256841, by rfl⟩ : syracuseStep 13406309 = 2513683) B2513683
theorem B2822273 : Blo 782338 2822273 := bstep (se 2 (by rfl) ⟨1058352, by rfl⟩ : syracuseStep 2822273 = 2116705) B2116705
theorem B2232791 : Blo 782338 2232791 := bstep (se 1 (by rfl) ⟨1674593, by rfl⟩ : syracuseStep 2232791 = 3349187) B3349187
theorem B21435137 : Blo 782338 21435137 := bstep (se 2 (by rfl) ⟨8038176, by rfl⟩ : syracuseStep 21435137 = 16076353) B16076353
theorem B7148483 : Blo 782338 7148483 := bstep (se 1 (by rfl) ⟨5361362, by rfl⟩ : syracuseStep 7148483 = 10722725) B10722725
theorem B1414351 : Blo 782338 1414351 := bstep (se 1 (by rfl) ⟨1060763, by rfl⟩ : syracuseStep 1414351 = 2121527) B2121527
theorem B8918585 : Blo 782338 8918585 := bstep (se 2 (by rfl) ⟨3344469, by rfl⟩ : syracuseStep 8918585 = 6688939) B6688939
theorem B43030115 : Blo 782338 43030115 := bstep (se 1 (by rfl) ⟨32272586, by rfl⟩ : syracuseStep 43030115 = 64545173) B64545173
theorem B2234249 : Blo 782338 2234249 := bstep (se 2 (by rfl) ⟨837843, by rfl⟩ : syracuseStep 2234249 = 1675687) B1675687
theorem B1677395 : Blo 782338 1677395 := bstep (se 1 (by rfl) ⟨1258046, by rfl⟩ : syracuseStep 1677395 = 2516093) B2516093
theorem B2234567 : Blo 782338 2234567 := bstep (se 1 (by rfl) ⟨1675925, by rfl⟩ : syracuseStep 2234567 = 3351851) B3351851
theorem B13375691 : Blo 782338 13375691 := bstep (se 1 (by rfl) ⟨10031768, by rfl⟩ : syracuseStep 13375691 = 20063537) B20063537
theorem B16063379 : Blo 782338 16063379 := bstep (se 1 (by rfl) ⟨12047534, by rfl⟩ : syracuseStep 16063379 = 24095069) B24095069
theorem B4463531 : Blo 782338 4463531 := bstep (se 1 (by rfl) ⟨3347648, by rfl⟩ : syracuseStep 4463531 = 6695297) B6695297
theorem B3972077 : Blo 782338 3972077 := bstep (se 3 (by rfl) ⟨744764, by rfl⟩ : syracuseStep 3972077 = 1489529) B1489529
theorem B2235433 : Blo 782338 2235433 := bstep (se 2 (by rfl) ⟨838287, by rfl⟩ : syracuseStep 2235433 = 1676575) B1676575
theorem B2825819 : Blo 782338 2825819 := bstep (se 1 (by rfl) ⟨2119364, by rfl⟩ : syracuseStep 2825819 = 4238729) B4238729
theorem B21503677 : Blo 782338 21503677 := bstep (se 3 (by rfl) ⟨4031939, by rfl⟩ : syracuseStep 21503677 = 8063879) B8063879
theorem B3972887 : Blo 782338 3972887 := bstep (se 1 (by rfl) ⟨2979665, by rfl⟩ : syracuseStep 3972887 = 5959331) B5959331
theorem B5021831 : Blo 782338 5021831 := bstep (se 1 (by rfl) ⟨3766373, by rfl⟩ : syracuseStep 5021831 = 7532747) B7532747
theorem B794855 : Blo 782338 794855 := bstep (se 1 (by rfl) ⟨596141, by rfl⟩ : syracuseStep 794855 = 1192283) B1192283
theorem B1254151 : Blo 782338 1254151 := bstep (se 1 (by rfl) ⟨940613, by rfl⟩ : syracuseStep 1254151 = 1881227) B1881227
theorem B3974507 : Blo 782338 3974507 := bstep (se 1 (by rfl) ⟨2980880, by rfl⟩ : syracuseStep 3974507 = 5961761) B5961761
theorem B1320347 : Blo 782338 1320347 := bstep (se 1 (by rfl) ⟨990260, by rfl⟩ : syracuseStep 1320347 = 1980521) B1980521
theorem B4302395 : Blo 782338 4302395 := bstep (se 1 (by rfl) ⟨3226796, by rfl⟩ : syracuseStep 4302395 = 6453593) B6453593
theorem B11282003 : Blo 782338 11282003 := bstep (se 1 (by rfl) ⟨8461502, by rfl⟩ : syracuseStep 11282003 = 16923005) B16923005
theorem B1189559 : Blo 782338 1189559 := bstep (se 1 (by rfl) ⟨892169, by rfl⟩ : syracuseStep 1189559 = 1784339) B1784339
theorem B1320671 : Blo 782338 1320671 := bstep (se 1 (by rfl) ⟨990503, by rfl⟩ : syracuseStep 1320671 = 1981007) B1981007
theorem B8464135 : Blo 782338 8464135 := bstep (se 1 (by rfl) ⟨6348101, by rfl⟩ : syracuseStep 8464135 = 12696203) B12696203
theorem B993055 : Blo 782338 993055 := bstep (se 1 (by rfl) ⟨744791, by rfl⟩ : syracuseStep 993055 = 1489583) B1489583
theorem B1321103 : Blo 782338 1321103 := bstep (se 1 (by rfl) ⟨990827, by rfl⟩ : syracuseStep 1321103 = 1981655) B1981655
theorem B1255657 : Blo 782338 1255657 := bstep (se 2 (by rfl) ⟨470871, by rfl⟩ : syracuseStep 1255657 = 941743) B941743
theorem B19310845 : Blo 782338 19310845 := bstep (se 3 (by rfl) ⟨3620783, by rfl⟩ : syracuseStep 19310845 = 7241567) B7241567
theorem B1321339 : Blo 782338 1321339 := bstep (se 1 (by rfl) ⟨991004, by rfl⟩ : syracuseStep 1321339 = 1982009) B1982009
theorem B1321609 : Blo 782338 1321609 := bstep (se 2 (by rfl) ⟨495603, by rfl⟩ : syracuseStep 1321609 = 991207) B991207
theorem B994351 : Blo 782338 994351 := bstep (se 1 (by rfl) ⟨745763, by rfl⟩ : syracuseStep 994351 = 1491527) B1491527
theorem B3976289 : Blo 782338 3976289 := bstep (se 2 (by rfl) ⟨1491108, by rfl⟩ : syracuseStep 3976289 = 2982217) B2982217
theorem B5942807 : Blo 782338 5942807 := bstep (se 1 (by rfl) ⟨4457105, by rfl⟩ : syracuseStep 5942807 = 8914211) B8914211
theorem B9318253 : Blo 782338 9318253 := bstep (se 3 (by rfl) ⟨1747172, by rfl⟩ : syracuseStep 9318253 = 3494345) B3494345
theorem B3977099 : Blo 782338 3977099 := bstep (se 1 (by rfl) ⟨2982824, by rfl⟩ : syracuseStep 3977099 = 5965649) B5965649
theorem B8466383 : Blo 782338 8466383 := bstep (se 1 (by rfl) ⟨6349787, by rfl⟩ : syracuseStep 8466383 = 12699575) B12699575
theorem B32157647 : Blo 782338 32157647 := bstep (se 1 (by rfl) ⟨24118235, by rfl⟩ : syracuseStep 32157647 = 48236471) B48236471
theorem B4468931 : Blo 782338 4468931 := bstep (se 1 (by rfl) ⟨3351698, by rfl⟩ : syracuseStep 4468931 = 6703397) B6703397
theorem B1323391 : Blo 782338 1323391 := bstep (se 1 (by rfl) ⟨992543, by rfl⟩ : syracuseStep 1323391 = 1985087) B1985087
theorem B8499599 : Blo 782338 8499599 := bstep (se 1 (by rfl) ⟨6374699, by rfl⟩ : syracuseStep 8499599 = 12749399) B12749399
theorem B7549433 : Blo 782338 7549433 := bstep (se 2 (by rfl) ⟨2831037, by rfl⟩ : syracuseStep 7549433 = 5662075) B5662075
theorem B5026319 : Blo 782338 5026319 := bstep (se 1 (by rfl) ⟨3769739, by rfl⟩ : syracuseStep 5026319 = 7539479) B7539479
theorem B10072775 : Blo 782338 10072775 := bstep (se 1 (by rfl) ⟨7554581, by rfl⟩ : syracuseStep 10072775 = 15109163) B15109163
theorem B6697687 : Blo 782338 6697687 := bstep (se 1 (by rfl) ⟨5023265, by rfl⟩ : syracuseStep 6697687 = 10046531) B10046531
theorem B1323823 : Blo 782338 1323823 := bstep (se 1 (by rfl) ⟨992867, by rfl⟩ : syracuseStep 1323823 = 1985735) B1985735
theorem B3978557 : Blo 782338 3978557 := bstep (se 3 (by rfl) ⟨745979, by rfl⟩ : syracuseStep 3978557 = 1491959) B1491959
theorem B9549161 : Blo 782338 9549161 := bstep (se 2 (by rfl) ⟨3580935, by rfl⟩ : syracuseStep 9549161 = 7161871) B7161871
theorem B2864609 : Blo 782338 2864609 := bstep (se 2 (by rfl) ⟨1074228, by rfl⟩ : syracuseStep 2864609 = 2148457) B2148457
theorem B7648931 : Blo 782338 7648931 := bstep (se 1 (by rfl) ⟨5736698, by rfl⟩ : syracuseStep 7648931 = 11473397) B11473397
theorem B16103123 : Blo 782338 16103123 := bstep (se 1 (by rfl) ⟨12077342, by rfl⟩ : syracuseStep 16103123 = 24154685) B24154685
theorem B18101981 : Blo 782338 18101981 := bstep (se 3 (by rfl) ⟨3394121, by rfl⟩ : syracuseStep 18101981 = 6788243) B6788243
theorem B1324795 : Blo 782338 1324795 := bstep (se 1 (by rfl) ⟨993596, by rfl⟩ : syracuseStep 1324795 = 1987193) B1987193
theorem B1324937 : Blo 782338 1324937 := bstep (se 2 (by rfl) ⟨496851, by rfl⟩ : syracuseStep 1324937 = 993703) B993703
theorem B3356635 : Blo 782338 3356635 := bstep (se 1 (by rfl) ⟨2517476, by rfl⟩ : syracuseStep 3356635 = 5034953) B5034953
theorem B1980409 : Blo 782338 1980409 := bstep (se 2 (by rfl) ⟨742653, by rfl⟩ : syracuseStep 1980409 = 1485307) B1485307
theorem B1980571 : Blo 782338 1980571 := bstep (se 1 (by rfl) ⟨1485428, by rfl⟩ : syracuseStep 1980571 = 2970857) B2970857
theorem B1980713 : Blo 782338 1980713 := bstep (se 2 (by rfl) ⟨742767, by rfl⟩ : syracuseStep 1980713 = 1485535) B1485535
theorem B1325369 : Blo 782338 1325369 := bstep (se 2 (by rfl) ⟨497013, by rfl⟩ : syracuseStep 1325369 = 994027) B994027
theorem B1325983 : Blo 782338 1325983 := bstep (se 1 (by rfl) ⟨994487, by rfl⟩ : syracuseStep 1325983 = 1988975) B1988975
theorem B4471847 : Blo 782338 4471847 := bstep (se 1 (by rfl) ⟨3353885, by rfl⟩ : syracuseStep 4471847 = 6707771) B6707771
theorem B5028905 : Blo 782338 5028905 := bstep (se 2 (by rfl) ⟨1885839, by rfl⟩ : syracuseStep 5028905 = 3771679) B3771679
theorem B1981705 : Blo 782338 1981705 := bstep (se 2 (by rfl) ⟨743139, by rfl⟩ : syracuseStep 1981705 = 1486279) B1486279
theorem B5717287 : Blo 782338 5717287 := bstep (se 1 (by rfl) ⟨4287965, by rfl⟩ : syracuseStep 5717287 = 8575931) B8575931
theorem B1326415 : Blo 782338 1326415 := bstep (se 1 (by rfl) ⟨994811, by rfl⟩ : syracuseStep 1326415 = 1989623) B1989623
theorem B1326503 : Blo 782338 1326503 := bstep (se 1 (by rfl) ⟨994877, by rfl⟩ : syracuseStep 1326503 = 1989755) B1989755
theorem B1326665 : Blo 782338 1326665 := bstep (se 2 (by rfl) ⟨497499, by rfl⟩ : syracuseStep 1326665 = 994999) B994999
theorem B22593167 : Blo 782338 22593167 := bstep (se 1 (by rfl) ⟨16944875, by rfl⟩ : syracuseStep 22593167 = 33889751) B33889751
theorem B185483981 : Blo 782338 185483981 := bstep (se 3 (by rfl) ⟨34778246, by rfl⟩ : syracuseStep 185483981 = 69556493) B69556493
theorem B1786681 : Blo 782338 1786681 := bstep (se 2 (by rfl) ⟨670005, by rfl⟩ : syracuseStep 1786681 = 1340011) B1340011
theorem B1885513 : Blo 782338 1885513 := bstep (se 2 (by rfl) ⟨707067, by rfl⟩ : syracuseStep 1885513 = 1414135) B1414135
theorem B2508455 : Blo 782338 2508455 := bstep (se 1 (by rfl) ⟨1881341, by rfl⟩ : syracuseStep 2508455 = 3762683) B3762683
theorem B5721005 : Blo 782338 5721005 := bstep (se 3 (by rfl) ⟨1072688, by rfl⟩ : syracuseStep 5721005 = 2145377) B2145377
theorem B2641031 : Blo 782338 2641031 := bstep (se 1 (by rfl) ⟨1980773, by rfl⟩ : syracuseStep 2641031 = 3961547) B3961547
theorem B9653411 : Blo 782338 9653411 := bstep (se 1 (by rfl) ⟨7240058, by rfl⟩ : syracuseStep 9653411 = 14480117) B14480117
theorem B2641139 : Blo 782338 2641139 := bstep (se 1 (by rfl) ⟨1980854, by rfl⟩ : syracuseStep 2641139 = 3961709) B3961709
theorem B2510327 : Blo 782338 2510327 := bstep (se 1 (by rfl) ⟨1882745, by rfl⟩ : syracuseStep 2510327 = 3765491) B3765491
theorem B34001153 : Blo 782338 34001153 := bstep (se 2 (by rfl) ⟨12750432, by rfl⟩ : syracuseStep 34001153 = 25500865) B25500865
theorem B16961825 : Blo 782338 16961825 := bstep (se 2 (by rfl) ⟨6360684, by rfl⟩ : syracuseStep 16961825 = 12721369) B12721369
theorem B1987031 : Blo 782338 1987031 := bstep (se 1 (by rfl) ⟨1490273, by rfl⟩ : syracuseStep 1987031 = 2980547) B2980547
theorem B4477427 : Blo 782338 4477427 := bstep (se 1 (by rfl) ⟨3358070, by rfl⟩ : syracuseStep 4477427 = 6716141) B6716141
theorem B4772513 : Blo 782338 4772513 := bstep (se 2 (by rfl) ⟨1789692, by rfl⟩ : syracuseStep 4772513 = 3579385) B3579385
theorem B2642813 : Blo 782338 2642813 := bstep (se 3 (by rfl) ⟨495527, by rfl⟩ : syracuseStep 2642813 = 991055) B991055
theorem B11326337 : Blo 782338 11326337 := bstep (se 2 (by rfl) ⟨4247376, by rfl⟩ : syracuseStep 11326337 = 8494753) B8494753
theorem B2643083 : Blo 782338 2643083 := bstep (se 1 (by rfl) ⟨1982312, by rfl⟩ : syracuseStep 2643083 = 3964625) B3964625
theorem B1988347 : Blo 782338 1988347 := bstep (se 1 (by rfl) ⟨1491260, by rfl⟩ : syracuseStep 1988347 = 2982521) B2982521
theorem B1988489 : Blo 782338 1988489 := bstep (se 2 (by rfl) ⟨745683, by rfl⟩ : syracuseStep 1988489 = 1491367) B1491367
theorem B2119841 : Blo 782338 2119841 := bstep (se 2 (by rfl) ⟨794940, by rfl⟩ : syracuseStep 2119841 = 1589881) B1589881
theorem B6707393 : Blo 782338 6707393 := bstep (se 2 (by rfl) ⟨2515272, by rfl⟩ : syracuseStep 6707393 = 5030545) B5030545
theorem B2972011 : Blo 782338 2972011 := bstep (se 1 (by rfl) ⟨2229008, by rfl⟩ : syracuseStep 2972011 = 4458017) B4458017
theorem B2644703 : Blo 782338 2644703 := bstep (se 1 (by rfl) ⟨1983527, by rfl⟩ : syracuseStep 2644703 = 3967055) B3967055
theorem B2972497 : Blo 782338 2972497 := bstep (se 2 (by rfl) ⟨1114686, by rfl⟩ : syracuseStep 2972497 = 2229373) B2229373
theorem B1989481 : Blo 782338 1989481 := bstep (se 2 (by rfl) ⟨746055, by rfl⟩ : syracuseStep 1989481 = 1492111) B1492111
theorem B21519209 : Blo 782338 21519209 := bstep (se 2 (by rfl) ⟨8069703, by rfl⟩ : syracuseStep 21519209 = 16139407) B16139407
theorem B5102507 : Blo 782338 5102507 := bstep (se 1 (by rfl) ⟨3826880, by rfl⟩ : syracuseStep 5102507 = 7653761) B7653761
theorem B1760327 : Blo 782338 1760327 := bstep (se 1 (by rfl) ⟨1320245, by rfl⟩ : syracuseStep 1760327 = 2640491) B2640491
theorem B4021433 : Blo 782338 4021433 := bstep (se 2 (by rfl) ⟨1508037, by rfl⟩ : syracuseStep 4021433 = 3016075) B3016075
theorem B2514185 : Blo 782338 2514185 := bstep (se 2 (by rfl) ⟨942819, by rfl⟩ : syracuseStep 2514185 = 1885639) B1885639
theorem B1760723 : Blo 782338 1760723 := bstep (se 1 (by rfl) ⟨1320542, by rfl⟩ : syracuseStep 1760723 = 2641085) B2641085
theorem B2645459 : Blo 782338 2645459 := bstep (se 1 (by rfl) ⟨1984094, by rfl⟩ : syracuseStep 2645459 = 3968189) B3968189
theorem B1433063 : Blo 782338 1433063 := bstep (se 1 (by rfl) ⟨1074797, by rfl⟩ : syracuseStep 1433063 = 2149595) B2149595
theorem B11329105 : Blo 782338 11329105 := bstep (se 2 (by rfl) ⟨4248414, by rfl⟩ : syracuseStep 11329105 = 8496829) B8496829
theorem B1760993 : Blo 782338 1760993 := bstep (se 2 (by rfl) ⟨660372, by rfl⟩ : syracuseStep 1760993 = 1320745) B1320745
theorem B2645729 : Blo 782338 2645729 := bstep (se 2 (by rfl) ⟨992148, by rfl⟩ : syracuseStep 2645729 = 1984297) B1984297
theorem B36298529 : Blo 782338 36298529 := bstep (se 2 (by rfl) ⟨13611948, by rfl⟩ : syracuseStep 36298529 = 27223897) B27223897
theorem B8052709 : Blo 782338 8052709 := bstep (se 4 (by rfl) ⟨754941, by rfl⟩ : syracuseStep 8052709 = 1509883) B1509883
theorem B2121959 : Blo 782338 2121959 := bstep (se 1 (by rfl) ⟨1591469, by rfl⟩ : syracuseStep 2121959 = 3182939) B3182939
theorem B7529021 : Blo 782338 7529021 := bstep (se 3 (by rfl) ⟨1411691, by rfl⟩ : syracuseStep 7529021 = 2823383) B2823383
theorem B2515529 : Blo 782338 2515529 := bstep (se 2 (by rfl) ⟨943323, by rfl⟩ : syracuseStep 2515529 = 1886647) B1886647
theorem B7168621 : Blo 782338 7168621 := bstep (se 3 (by rfl) ⟨1344116, by rfl⟩ : syracuseStep 7168621 = 2688233) B2688233
theorem B2974745 : Blo 782338 2974745 := bstep (se 2 (by rfl) ⟨1115529, by rfl⟩ : syracuseStep 2974745 = 2231059) B2231059
theorem B2974927 : Blo 782338 2974927 := bstep (se 1 (by rfl) ⟨2231195, by rfl⟩ : syracuseStep 2974927 = 4462391) B4462391
theorem B1762667 : Blo 782338 1762667 := bstep (se 1 (by rfl) ⟨1322000, by rfl⟩ : syracuseStep 1762667 = 2644001) B2644001
theorem B2647403 : Blo 782338 2647403 := bstep (se 1 (by rfl) ⟨1985552, by rfl⟩ : syracuseStep 2647403 = 3971105) B3971105
theorem B2647511 : Blo 782338 2647511 := bstep (se 1 (by rfl) ⟨1985633, by rfl⟩ : syracuseStep 2647511 = 3971267) B3971267
theorem B1762937 : Blo 782338 1762937 := bstep (se 2 (by rfl) ⟨661101, by rfl⟩ : syracuseStep 1762937 = 1322203) B1322203
theorem B2647673 : Blo 782338 2647673 := bstep (se 2 (by rfl) ⟨992877, by rfl⟩ : syracuseStep 2647673 = 1985755) B1985755
theorem B2975399 : Blo 782338 2975399 := bstep (se 1 (by rfl) ⟨2231549, by rfl⟩ : syracuseStep 2975399 = 4463099) B4463099
theorem B1173599 : Blo 782338 1173599 := bstep (se 1 (by rfl) ⟨880199, by rfl⟩ : syracuseStep 1173599 = 1760399) B1760399
theorem B1173659 : Blo 782338 1173659 := bstep (se 1 (by rfl) ⟨880244, by rfl⟩ : syracuseStep 1173659 = 1760489) B1760489
theorem B1173695 : Blo 782338 1173695 := bstep (se 1 (by rfl) ⟨880271, by rfl⟩ : syracuseStep 1173695 = 1760543) B1760543
theorem B1173737 : Blo 782338 1173737 := bstep (se 2 (by rfl) ⟨440151, by rfl⟩ : syracuseStep 1173737 = 880303) B880303
theorem B1174043 : Blo 782338 1174043 := bstep (se 1 (by rfl) ⟨880532, by rfl⟩ : syracuseStep 1174043 = 1761065) B1761065
theorem B1174121 : Blo 782338 1174121 := bstep (se 2 (by rfl) ⟨440295, by rfl⟩ : syracuseStep 1174121 = 880591) B880591
theorem B1763945 : Blo 782338 1763945 := bstep (se 2 (by rfl) ⟨661479, by rfl⟩ : syracuseStep 1763945 = 1322959) B1322959
theorem B9071635 : Blo 782338 9071635 := bstep (se 1 (by rfl) ⟨6803726, by rfl⟩ : syracuseStep 9071635 = 13607453) B13607453
theorem B2649185 : Blo 782338 2649185 := bstep (se 2 (by rfl) ⟨993444, by rfl⟩ : syracuseStep 2649185 = 1986889) B1986889
theorem B1174649 : Blo 782338 1174649 := bstep (se 2 (by rfl) ⟨440493, by rfl⟩ : syracuseStep 1174649 = 880987) B880987
theorem B1174751 : Blo 782338 1174751 := bstep (se 1 (by rfl) ⟨881063, by rfl⟩ : syracuseStep 1174751 = 1762127) B1762127
theorem B1764575 : Blo 782338 1764575 := bstep (se 1 (by rfl) ⟨1323431, by rfl⟩ : syracuseStep 1764575 = 2646863) B2646863
theorem B1174793 : Blo 782338 1174793 := bstep (se 2 (by rfl) ⟨440547, by rfl⟩ : syracuseStep 1174793 = 881095) B881095
theorem B1174895 : Blo 782338 1174895 := bstep (se 1 (by rfl) ⟨881171, by rfl⟩ : syracuseStep 1174895 = 1762343) B1762343
theorem B1764791 : Blo 782338 1764791 := bstep (se 1 (by rfl) ⟨1323593, by rfl⟩ : syracuseStep 1764791 = 2647187) B2647187
theorem B1175015 : Blo 782338 1175015 := bstep (se 1 (by rfl) ⟨881261, by rfl⟩ : syracuseStep 1175015 = 1762523) B1762523
theorem B1175147 : Blo 782338 1175147 := bstep (se 1 (by rfl) ⟨881360, by rfl⟩ : syracuseStep 1175147 = 1762721) B1762721
theorem B1764971 : Blo 782338 1764971 := bstep (se 1 (by rfl) ⟨1323728, by rfl⟩ : syracuseStep 1764971 = 2647457) B2647457
theorem B2649725 : Blo 782338 2649725 := bstep (se 3 (by rfl) ⟨496823, by rfl⟩ : syracuseStep 2649725 = 993647) B993647
theorem B1175273 : Blo 782338 1175273 := bstep (se 2 (by rfl) ⟨440727, by rfl⟩ : syracuseStep 1175273 = 881455) B881455
theorem B1175417 : Blo 782338 1175417 := bstep (se 2 (by rfl) ⟨440781, by rfl⟩ : syracuseStep 1175417 = 881563) B881563
theorem B1765241 : Blo 782338 1765241 := bstep (se 2 (by rfl) ⟨661965, by rfl⟩ : syracuseStep 1765241 = 1323931) B1323931
theorem B2649995 : Blo 782338 2649995 := bstep (se 1 (by rfl) ⟨1987496, by rfl⟩ : syracuseStep 2649995 = 3974993) B3974993
theorem B1175519 : Blo 782338 1175519 := bstep (se 1 (by rfl) ⟨881639, by rfl⟩ : syracuseStep 1175519 = 1763279) B1763279
theorem B1175771 : Blo 782338 1175771 := bstep (se 1 (by rfl) ⟨881828, by rfl⟩ : syracuseStep 1175771 = 1763657) B1763657
theorem B782567 : Blo 782338 782567 := bstep (se 1 (by rfl) ⟨586925, by rfl⟩ : syracuseStep 782567 = 1173851) B1173851
theorem B1175783 : Blo 782338 1175783 := bstep (se 1 (by rfl) ⟨881837, by rfl⟩ : syracuseStep 1175783 = 1763675) B1763675
theorem B782719 : Blo 782338 782719 := bstep (se 1 (by rfl) ⟨587039, by rfl⟩ : syracuseStep 782719 = 1174079) B1174079
theorem B881023 : Blo 782338 881023 := bstep (se 1 (by rfl) ⟨660767, by rfl⟩ : syracuseStep 881023 = 1321535) B1321535
theorem B1175945 : Blo 782338 1175945 := bstep (se 2 (by rfl) ⟨440979, by rfl⟩ : syracuseStep 1175945 = 881959) B881959
theorem B4518287 : Blo 782338 4518287 := bstep (se 1 (by rfl) ⟨3388715, by rfl⟩ : syracuseStep 4518287 = 6777431) B6777431
theorem B2650535 : Blo 782338 2650535 := bstep (se 1 (by rfl) ⟨1987901, by rfl⟩ : syracuseStep 2650535 = 3975803) B3975803
theorem B782799 : Blo 782338 782799 := bstep (se 1 (by rfl) ⟨587099, by rfl⟩ : syracuseStep 782799 = 1174199) B1174199
theorem B1176041 : Blo 782338 1176041 := bstep (se 2 (by rfl) ⟨441015, by rfl⟩ : syracuseStep 1176041 = 882031) B882031
theorem B3764819 : Blo 782338 3764819 := bstep (se 1 (by rfl) ⟨2823614, by rfl⟩ : syracuseStep 3764819 = 5647229) B5647229
theorem B782951 : Blo 782338 782951 := bstep (se 1 (by rfl) ⟨587213, by rfl⟩ : syracuseStep 782951 = 1174427) B1174427
theorem B1176167 : Blo 782338 1176167 := bstep (se 1 (by rfl) ⟨882125, by rfl⟩ : syracuseStep 1176167 = 1764251) B1764251
theorem B1176299 : Blo 782338 1176299 := bstep (se 1 (by rfl) ⟨882224, by rfl⟩ : syracuseStep 1176299 = 1764449) B1764449
theorem B1176329 : Blo 782338 1176329 := bstep (se 2 (by rfl) ⟨441123, by rfl⟩ : syracuseStep 1176329 = 882247) B882247
theorem B2388761 : Blo 782338 2388761 := bstep (se 2 (by rfl) ⟨895785, by rfl⟩ : syracuseStep 2388761 = 1791571) B1791571
theorem B783215 : Blo 782338 783215 := bstep (se 1 (by rfl) ⟨587411, by rfl⟩ : syracuseStep 783215 = 1174823) B1174823
theorem B1176431 : Blo 782338 1176431 := bstep (se 1 (by rfl) ⟨882323, by rfl⟩ : syracuseStep 1176431 = 1764647) B1764647
theorem B783271 : Blo 782338 783271 := bstep (se 1 (by rfl) ⟨587453, by rfl⟩ : syracuseStep 783271 = 1174907) B1174907
theorem B783355 : Blo 782338 783355 := bstep (se 1 (by rfl) ⟨587516, by rfl⟩ : syracuseStep 783355 = 1175033) B1175033
theorem B783423 : Blo 782338 783423 := bstep (se 1 (by rfl) ⟨587567, by rfl⟩ : syracuseStep 783423 = 1175135) B1175135
theorem B1176683 : Blo 782338 1176683 := bstep (se 1 (by rfl) ⟨882512, by rfl⟩ : syracuseStep 1176683 = 1765025) B1765025
theorem B783567 : Blo 782338 783567 := bstep (se 1 (by rfl) ⟨587675, by rfl⟩ : syracuseStep 783567 = 1175351) B1175351
theorem B1176923 : Blo 782338 1176923 := bstep (se 1 (by rfl) ⟨882692, by rfl⟩ : syracuseStep 1176923 = 1765385) B1765385
theorem B783771 : Blo 782338 783771 := bstep (se 1 (by rfl) ⟨587828, by rfl⟩ : syracuseStep 783771 = 1175657) B1175657
theorem B783983 : Blo 782338 783983 := bstep (se 1 (by rfl) ⟨587987, by rfl⟩ : syracuseStep 783983 = 1175975) B1175975
theorem B1177199 : Blo 782338 1177199 := bstep (se 1 (by rfl) ⟨882899, by rfl⟩ : syracuseStep 1177199 = 1765799) B1765799
theorem B784039 : Blo 782338 784039 := bstep (se 1 (by rfl) ⟨588029, by rfl⟩ : syracuseStep 784039 = 1176059) B1176059
theorem B1177271 : Blo 782338 1177271 := bstep (se 1 (by rfl) ⟨882953, by rfl⟩ : syracuseStep 1177271 = 1765907) B1765907
theorem B1767095 : Blo 782338 1767095 := bstep (se 1 (by rfl) ⟨1325321, by rfl⟩ : syracuseStep 1767095 = 2650643) B2650643
theorem B2651831 : Blo 782338 2651831 := bstep (se 1 (by rfl) ⟨1988873, by rfl⟩ : syracuseStep 2651831 = 3977747) B3977747
theorem B1177307 : Blo 782338 1177307 := bstep (se 1 (by rfl) ⟨882980, by rfl⟩ : syracuseStep 1177307 = 1765961) B1765961
theorem B784123 : Blo 782338 784123 := bstep (se 1 (by rfl) ⟨588092, by rfl⟩ : syracuseStep 784123 = 1176185) B1176185
theorem B882427 : Blo 782338 882427 := bstep (se 1 (by rfl) ⟨661820, by rfl⟩ : syracuseStep 882427 = 1323641) B1323641
theorem B16971515 : Blo 782338 16971515 := bstep (se 1 (by rfl) ⟨12728636, by rfl⟩ : syracuseStep 16971515 = 25457273) B25457273
theorem B784159 : Blo 782338 784159 := bstep (se 1 (by rfl) ⟨588119, by rfl⟩ : syracuseStep 784159 = 1176239) B1176239
theorem B882463 : Blo 782338 882463 := bstep (se 1 (by rfl) ⟨661847, by rfl⟩ : syracuseStep 882463 = 1323695) B1323695
theorem B784191 : Blo 782338 784191 := bstep (se 1 (by rfl) ⟨588143, by rfl⟩ : syracuseStep 784191 = 1176287) B1176287
theorem B1177481 : Blo 782338 1177481 := bstep (se 2 (by rfl) ⟨441555, by rfl⟩ : syracuseStep 1177481 = 883111) B883111
theorem B3962843 : Blo 782338 3962843 := bstep (se 1 (by rfl) ⟨2972132, by rfl⟩ : syracuseStep 3962843 = 5944265) B5944265
theorem B784367 : Blo 782338 784367 := bstep (se 1 (by rfl) ⟨588275, by rfl⟩ : syracuseStep 784367 = 1176551) B1176551
theorem B1177583 : Blo 782338 1177583 := bstep (se 1 (by rfl) ⟨883187, by rfl⟩ : syracuseStep 1177583 = 1766375) B1766375
theorem B784539 : Blo 782338 784539 := bstep (se 1 (by rfl) ⟨588404, by rfl⟩ : syracuseStep 784539 = 1176809) B1176809
theorem B7141547 : Blo 782338 7141547 := bstep (se 1 (by rfl) ⟨5356160, by rfl⟩ : syracuseStep 7141547 = 10712321) B10712321
theorem B784575 : Blo 782338 784575 := bstep (se 1 (by rfl) ⟨588431, by rfl⟩ : syracuseStep 784575 = 1176863) B1176863
theorem B1177835 : Blo 782338 1177835 := bstep (se 1 (by rfl) ⟨883376, by rfl⟩ : syracuseStep 1177835 = 1766753) B1766753
theorem B3176711 : Blo 782338 3176711 := bstep (se 1 (by rfl) ⟨2382533, by rfl⟩ : syracuseStep 3176711 = 4765067) B4765067
theorem B1177895 : Blo 782338 1177895 := bstep (se 1 (by rfl) ⟨883421, by rfl⟩ : syracuseStep 1177895 = 1766843) B1766843
theorem B784687 : Blo 782338 784687 := bstep (se 1 (by rfl) ⟨588515, by rfl⟩ : syracuseStep 784687 = 1177031) B1177031
theorem B9173357 : Blo 782338 9173357 := bstep (se 3 (by rfl) ⟨1720004, by rfl⟩ : syracuseStep 9173357 = 3440009) B3440009
theorem B12712301 : Blo 782338 12712301 := bstep (se 3 (by rfl) ⟨2383556, by rfl⟩ : syracuseStep 12712301 = 4767113) B4767113
theorem B1177979 : Blo 782338 1177979 := bstep (se 1 (by rfl) ⟨883484, by rfl⟩ : syracuseStep 1177979 = 1766969) B1766969
theorem B784923 : Blo 782338 784923 := bstep (se 1 (by rfl) ⟨588692, by rfl⟩ : syracuseStep 784923 = 1177385) B1177385
theorem B784927 : Blo 782338 784927 := bstep (se 1 (by rfl) ⟨588695, by rfl⟩ : syracuseStep 784927 = 1177391) B1177391
theorem B1178249 : Blo 782338 1178249 := bstep (se 2 (by rfl) ⟨441843, by rfl⟩ : syracuseStep 1178249 = 883687) B883687
theorem B1178423 : Blo 782338 1178423 := bstep (se 1 (by rfl) ⟨883817, by rfl⟩ : syracuseStep 1178423 = 1767635) B1767635
theorem B785243 : Blo 782338 785243 := bstep (se 1 (by rfl) ⟨588932, by rfl⟩ : syracuseStep 785243 = 1177865) B1177865
theorem B1178459 : Blo 782338 1178459 := bstep (se 1 (by rfl) ⟨883844, by rfl⟩ : syracuseStep 1178459 = 1767689) B1767689
theorem B1768283 : Blo 782338 1768283 := bstep (se 1 (by rfl) ⟨1326212, by rfl⟩ : syracuseStep 1768283 = 2652425) B2652425
theorem B2653019 : Blo 782338 2653019 := bstep (se 1 (by rfl) ⟨1989764, by rfl⟩ : syracuseStep 2653019 = 3979529) B3979529
theorem B785311 : Blo 782338 785311 := bstep (se 1 (by rfl) ⟨588983, by rfl⟩ : syracuseStep 785311 = 1177967) B1177967
theorem B883615 : Blo 782338 883615 := bstep (se 1 (by rfl) ⟨662711, by rfl⟩ : syracuseStep 883615 = 1325423) B1325423
theorem B13564837 : Blo 782338 13564837 := bstep (se 4 (by rfl) ⟨1271703, by rfl⟩ : syracuseStep 13564837 = 2543407) B2543407
theorem B1178603 : Blo 782338 1178603 := bstep (se 1 (by rfl) ⟨883952, by rfl⟩ : syracuseStep 1178603 = 1767905) B1767905
theorem B785455 : Blo 782338 785455 := bstep (se 1 (by rfl) ⟨589091, by rfl⟩ : syracuseStep 785455 = 1178183) B1178183
theorem B883759 : Blo 782338 883759 := bstep (se 1 (by rfl) ⟨662819, by rfl⟩ : syracuseStep 883759 = 1325639) B1325639
theorem B785479 : Blo 782338 785479 := bstep (se 1 (by rfl) ⟨589109, by rfl⟩ : syracuseStep 785479 = 1178219) B1178219
theorem B1178807 : Blo 782338 1178807 := bstep (se 1 (by rfl) ⟨884105, by rfl⟩ : syracuseStep 1178807 = 1768211) B1768211
theorem B785631 : Blo 782338 785631 := bstep (se 1 (by rfl) ⟨589223, by rfl⟩ : syracuseStep 785631 = 1178447) B1178447
theorem B884047 : Blo 782338 884047 := bstep (se 1 (by rfl) ⟨663035, by rfl⟩ : syracuseStep 884047 = 1326071) B1326071
theorem B2260391 : Blo 782338 2260391 := bstep (se 1 (by rfl) ⟨1695293, by rfl⟩ : syracuseStep 2260391 = 3390587) B3390587
theorem B1179047 : Blo 782338 1179047 := bstep (se 1 (by rfl) ⟨884285, by rfl⟩ : syracuseStep 1179047 = 1768571) B1768571
theorem B5963219 : Blo 782338 5963219 := bstep (se 1 (by rfl) ⟨4472414, by rfl⟩ : syracuseStep 5963219 = 8944829) B8944829
theorem B785895 : Blo 782338 785895 := bstep (se 1 (by rfl) ⟨589421, by rfl⟩ : syracuseStep 785895 = 1178843) B1178843
theorem B1179131 : Blo 782338 1179131 := bstep (se 1 (by rfl) ⟨884348, by rfl⟩ : syracuseStep 1179131 = 1768697) B1768697
theorem B1769039 : Blo 782338 1769039 := bstep (se 1 (by rfl) ⟨1326779, by rfl⟩ : syracuseStep 1769039 = 2653559) B2653559
theorem B2653775 : Blo 782338 2653775 := bstep (se 1 (by rfl) ⟨1990331, by rfl⟩ : syracuseStep 2653775 = 3980663) B3980663
theorem B786011 : Blo 782338 786011 := bstep (se 1 (by rfl) ⟨589508, by rfl⟩ : syracuseStep 786011 = 1179017) B1179017
theorem B1179227 : Blo 782338 1179227 := bstep (se 1 (by rfl) ⟨884420, by rfl⟩ : syracuseStep 1179227 = 1768841) B1768841
theorem B3767951 : Blo 782338 3767951 := bstep (se 1 (by rfl) ⟨2825963, by rfl⟩ : syracuseStep 3767951 = 5651927) B5651927
theorem B2981519 : Blo 782338 2981519 := bstep (se 1 (by rfl) ⟨2236139, by rfl⟩ : syracuseStep 2981519 = 4472279) B4472279
theorem B1179311 : Blo 782338 1179311 := bstep (se 1 (by rfl) ⟨884483, by rfl⟩ : syracuseStep 1179311 = 1768967) B1768967
theorem B2653883 : Blo 782338 2653883 := bstep (se 1 (by rfl) ⟨1990412, by rfl⟩ : syracuseStep 2653883 = 3980825) B3980825
theorem B1179431 : Blo 782338 1179431 := bstep (se 1 (by rfl) ⟨884573, by rfl⟩ : syracuseStep 1179431 = 1769147) B1769147
theorem B786247 : Blo 782338 786247 := bstep (se 1 (by rfl) ⟨589685, by rfl⟩ : syracuseStep 786247 = 1179371) B1179371
theorem B884551 : Blo 782338 884551 := bstep (se 1 (by rfl) ⟨663413, by rfl⟩ : syracuseStep 884551 = 1326827) B1326827
theorem B278822807 : Blo 782338 278822807 := bstep (se 1 (by rfl) ⟨209117105, by rfl⟩ : syracuseStep 278822807 = 418234211) B418234211
theorem B19333727 : Blo 782338 19333727 := bstep (se 1 (by rfl) ⟨14500295, by rfl⟩ : syracuseStep 19333727 = 29000591) B29000591
theorem B1966687 : Blo 782338 1966687 := bstep (se 1 (by rfl) ⟨1475015, by rfl⟩ : syracuseStep 1966687 = 2950031) B2950031
theorem B2229191 : Blo 782338 2229191 := bstep (se 1 (by rfl) ⟨1671893, by rfl⟩ : syracuseStep 2229191 = 3343787) B3343787
theorem B1672201 : Blo 782338 1672201 := bstep (se 2 (by rfl) ⟨627075, by rfl⟩ : syracuseStep 1672201 = 1254151) B1254151
theorem B18089405 : Blo 782338 18089405 := bstep (se 3 (by rfl) ⟨3391763, by rfl⟩ : syracuseStep 18089405 = 6783527) B6783527
theorem B3966569 : Blo 782338 3966569 := bstep (se 2 (by rfl) ⟨1487463, by rfl⟩ : syracuseStep 3966569 = 2974927) B2974927
theorem B1673551 : Blo 782338 1673551 := bstep (se 1 (by rfl) ⟨1255163, by rfl⟩ : syracuseStep 1673551 = 2510327) B2510327
theorem B1674209 : Blo 782338 1674209 := bstep (se 2 (by rfl) ⟨627828, by rfl⟩ : syracuseStep 1674209 = 1255657) B1255657
theorem B2984951 : Blo 782338 2984951 := bstep (se 1 (by rfl) ⟨2238713, by rfl⟩ : syracuseStep 2984951 = 4477427) B4477427
theorem B3181675 : Blo 782338 3181675 := bstep (se 1 (by rfl) ⟨2386256, by rfl⟩ : syracuseStep 3181675 = 4772513) B4772513
theorem B14290091 : Blo 782338 14290091 := bstep (se 1 (by rfl) ⟨10717568, by rfl⟩ : syracuseStep 14290091 = 21435137) B21435137
theorem B5639705 : Blo 782338 5639705 := bstep (se 2 (by rfl) ⟨2114889, by rfl⟩ : syracuseStep 5639705 = 4229779) B4229779
theorem B12095513 : Blo 782338 12095513 := bstep (se 2 (by rfl) ⟨4535817, by rfl⟩ : syracuseStep 12095513 = 9071635) B9071635
theorem B1413227 : Blo 782338 1413227 := bstep (se 1 (by rfl) ⟨1059920, by rfl⟩ : syracuseStep 1413227 = 2119841) B2119841
theorem B8917127 : Blo 782338 8917127 := bstep (se 1 (by rfl) ⟨6687845, by rfl⟩ : syracuseStep 8917127 = 13375691) B13375691
theorem B6689213 : Blo 782338 6689213 := bstep (se 3 (by rfl) ⟨1254227, by rfl⟩ : syracuseStep 6689213 = 2508455) B2508455
theorem B1676123 : Blo 782338 1676123 := bstep (se 1 (by rfl) ⟨1257092, by rfl⟩ : syracuseStep 1676123 = 2514185) B2514185
theorem B12424337 : Blo 782338 12424337 := bstep (se 2 (by rfl) ⟨4659126, by rfl⟩ : syracuseStep 12424337 = 9318253) B9318253
theorem B3347887 : Blo 782338 3347887 := bstep (se 1 (by rfl) ⟨2510915, by rfl⟩ : syracuseStep 3347887 = 5021831) B5021831
theorem B1414639 : Blo 782338 1414639 := bstep (se 1 (by rfl) ⟨1060979, by rfl⟩ : syracuseStep 1414639 = 2121959) B2121959
theorem B5019347 : Blo 782338 5019347 := bstep (se 1 (by rfl) ⟨3764510, by rfl⟩ : syracuseStep 5019347 = 7529021) B7529021
theorem B1677019 : Blo 782338 1677019 := bstep (se 1 (by rfl) ⟨1257764, by rfl⟩ : syracuseStep 1677019 = 2515529) B2515529
theorem B4462573 : Blo 782338 4462573 := bstep (se 3 (by rfl) ⟨836732, by rfl⟩ : syracuseStep 4462573 = 1673465) B1673465
theorem B7543205 : Blo 782338 7543205 := bstep (se 4 (by rfl) ⟨707175, by rfl⟩ : syracuseStep 7543205 = 1414351) B1414351
theorem B793039 : Blo 782338 793039 := bstep (se 1 (by rfl) ⟨594779, by rfl⟩ : syracuseStep 793039 = 1189559) B1189559
theorem B57384557 : Blo 782338 57384557 := bstep (se 3 (by rfl) ⟨10759604, by rfl⟩ : syracuseStep 57384557 = 21519209) B21519209
theorem B5644255 : Blo 782338 5644255 := bstep (se 1 (by rfl) ⟨4233191, by rfl⟩ : syracuseStep 5644255 = 8466383) B8466383
theorem B21438431 : Blo 782338 21438431 := bstep (se 1 (by rfl) ⟨16078823, by rfl⟩ : syracuseStep 21438431 = 32157647) B32157647
theorem B3350879 : Blo 782338 3350879 := bstep (se 1 (by rfl) ⟨2513159, by rfl⟩ : syracuseStep 3350879 = 5026319) B5026319
theorem B6366107 : Blo 782338 6366107 := bstep (se 1 (by rfl) ⟨4774580, by rfl⟩ : syracuseStep 6366107 = 9549161) B9549161
theorem B1909739 : Blo 782338 1909739 := bstep (se 1 (by rfl) ⟨1432304, by rfl⟩ : syracuseStep 1909739 = 2864609) B2864609
theorem B12067987 : Blo 782338 12067987 := bstep (se 1 (by rfl) ⟨9050990, by rfl⟩ : syracuseStep 12067987 = 18101981) B18101981
theorem B11314343 : Blo 782338 11314343 := bstep (se 1 (by rfl) ⟨8485757, by rfl⟩ : syracuseStep 11314343 = 16971515) B16971515
theorem B4761031 : Blo 782338 4761031 := bstep (se 1 (by rfl) ⟨3570773, by rfl⟩ : syracuseStep 4761031 = 7141547) B7141547
theorem B1320475 : Blo 782338 1320475 := bstep (se 1 (by rfl) ⟨990356, by rfl⟩ : syracuseStep 1320475 = 1980713) B1980713
theorem B3352603 : Blo 782338 3352603 := bstep (se 1 (by rfl) ⟨2514452, by rfl⟩ : syracuseStep 3352603 = 5028905) B5028905
theorem B3975479 : Blo 782338 3975479 := bstep (se 1 (by rfl) ⟨2981609, by rfl⟩ : syracuseStep 3975479 = 5963219) B5963219
theorem B45231533 : Blo 782338 45231533 := bstep (se 3 (by rfl) ⟨8480912, by rfl⟩ : syracuseStep 45231533 = 16961825) B16961825
theorem B9547255 : Blo 782338 9547255 := bstep (se 1 (by rfl) ⟨7160441, by rfl⟩ : syracuseStep 9547255 = 14320883) B14320883
theorem B3976937 : Blo 782338 3976937 := bstep (se 2 (by rfl) ⟨1491351, by rfl⟩ : syracuseStep 3976937 = 2982703) B2982703
theorem B3814003 : Blo 782338 3814003 := bstep (se 1 (by rfl) ⟨2860502, by rfl⟩ : syracuseStep 3814003 = 5721005) B5721005
theorem B6435607 : Blo 782338 6435607 := bstep (se 1 (by rfl) ⟨4826705, by rfl⟩ : syracuseStep 6435607 = 9653411) B9653411
theorem B1487783 : Blo 782338 1487783 := bstep (se 1 (by rfl) ⟨1115837, by rfl⟩ : syracuseStep 1487783 = 2231675) B2231675
theorem B11285513 : Blo 782338 11285513 := bstep (se 2 (by rfl) ⟨4232067, by rfl⟩ : syracuseStep 11285513 = 8464135) B8464135
theorem B1324073 : Blo 782338 1324073 := bstep (se 2 (by rfl) ⟨496527, by rfl⟩ : syracuseStep 1324073 = 993055) B993055
theorem B1881515 : Blo 782338 1881515 := bstep (se 1 (by rfl) ⟨1411136, by rfl⟩ : syracuseStep 1881515 = 2822273) B2822273
theorem B1488527 : Blo 782338 1488527 := bstep (se 1 (by rfl) ⟨1116395, by rfl⟩ : syracuseStep 1488527 = 2232791) B2232791
theorem B1324687 : Blo 782338 1324687 := bstep (se 1 (by rfl) ⟨993515, by rfl⟩ : syracuseStep 1324687 = 1987031) B1987031
theorem B7550891 : Blo 782338 7550891 := bstep (se 1 (by rfl) ⟨5663168, by rfl⟩ : syracuseStep 7550891 = 11326337) B11326337
theorem B4765655 : Blo 782338 4765655 := bstep (se 1 (by rfl) ⟨3574241, by rfl⟩ : syracuseStep 4765655 = 7148483) B7148483
theorem B1488937 : Blo 782338 1488937 := bstep (se 2 (by rfl) ⟨558351, by rfl⟩ : syracuseStep 1488937 = 1116703) B1116703
theorem B30193721 : Blo 782338 30193721 := bstep (se 2 (by rfl) ⟨11322645, by rfl⟩ : syracuseStep 30193721 = 22645291) B22645291
theorem B5945723 : Blo 782338 5945723 := bstep (se 1 (by rfl) ⟨4459292, by rfl⟩ : syracuseStep 5945723 = 8918585) B8918585
theorem B28686743 : Blo 782338 28686743 := bstep (se 1 (by rfl) ⟨21515057, by rfl⟩ : syracuseStep 28686743 = 43030115) B43030115
theorem B1489499 : Blo 782338 1489499 := bstep (se 1 (by rfl) ⟨1117124, by rfl⟩ : syracuseStep 1489499 = 2234249) B2234249
theorem B1325659 : Blo 782338 1325659 := bstep (se 1 (by rfl) ⟨994244, by rfl⟩ : syracuseStep 1325659 = 1988489) B1988489
theorem B1325801 : Blo 782338 1325801 := bstep (se 2 (by rfl) ⟨497175, by rfl⟩ : syracuseStep 1325801 = 994351) B994351
theorem B4471595 : Blo 782338 4471595 := bstep (se 1 (by rfl) ⟨3353696, by rfl⟩ : syracuseStep 4471595 = 6707393) B6707393
theorem B1883417 : Blo 782338 1883417 := bstep (se 2 (by rfl) ⟨706281, by rfl⟩ : syracuseStep 1883417 = 1412563) B1412563
theorem B1883879 : Blo 782338 1883879 := bstep (se 1 (by rfl) ⟨1412909, by rfl⟩ : syracuseStep 1883879 = 2825819) B2825819
theorem B24199019 : Blo 782338 24199019 := bstep (se 1 (by rfl) ⟨18149264, by rfl⟩ : syracuseStep 24199019 = 36298529) B36298529
theorem B4473053 : Blo 782338 4473053 := bstep (se 3 (by rfl) ⟨838697, by rfl⟩ : syracuseStep 4473053 = 1677395) B1677395
theorem B1983163 : Blo 782338 1983163 := bstep (se 1 (by rfl) ⟨1487372, by rfl⟩ : syracuseStep 1983163 = 2974745) B2974745
theorem B8930249 : Blo 782338 8930249 := bstep (se 2 (by rfl) ⟨3348843, by rfl⟩ : syracuseStep 8930249 = 6697687) B6697687
theorem B2868263 : Blo 782338 2868263 := bstep (se 1 (by rfl) ⟨2151197, by rfl⟩ : syracuseStep 2868263 = 4302395) B4302395
theorem B7521335 : Blo 782338 7521335 := bstep (se 1 (by rfl) ⟨5641001, by rfl⟩ : syracuseStep 7521335 = 11282003) B11282003
theorem B1983599 : Blo 782338 1983599 := bstep (se 1 (by rfl) ⟨1487699, by rfl⟩ : syracuseStep 1983599 = 2975399) B2975399
theorem B30492197 : Blo 782338 30492197 := bstep (se 4 (by rfl) ⟨2858643, by rfl⟩ : syracuseStep 30492197 = 5717287) B5717287
theorem B4475513 : Blo 782338 4475513 := bstep (se 2 (by rfl) ⟨1678317, by rfl⟩ : syracuseStep 4475513 = 3356635) B3356635
theorem B2640545 : Blo 782338 2640545 := bstep (se 2 (by rfl) ⟨990204, by rfl⟩ : syracuseStep 2640545 = 1980409) B1980409
theorem B2640761 : Blo 782338 2640761 := bstep (se 2 (by rfl) ⟨990285, by rfl⟩ : syracuseStep 2640761 = 1980571) B1980571
theorem B5032955 : Blo 782338 5032955 := bstep (se 1 (by rfl) ⟨3774716, by rfl⟩ : syracuseStep 5032955 = 7549433) B7549433
theorem B2509879 : Blo 782338 2509879 := bstep (se 1 (by rfl) ⟨1882409, by rfl⟩ : syracuseStep 2509879 = 3764819) B3764819
theorem B1592507 : Blo 782338 1592507 := bstep (se 1 (by rfl) ⟨1194380, by rfl⟩ : syracuseStep 1592507 = 2388761) B2388761
theorem B5099287 : Blo 782338 5099287 := bstep (se 1 (by rfl) ⟨3824465, by rfl⟩ : syracuseStep 5099287 = 7648931) B7648931
theorem B10735415 : Blo 782338 10735415 := bstep (se 1 (by rfl) ⟨8051561, by rfl⟩ : syracuseStep 10735415 = 16103123) B16103123
theorem B3821501 : Blo 782338 3821501 := bstep (se 3 (by rfl) ⟨716531, by rfl⟩ : syracuseStep 3821501 = 1433063) B1433063
theorem B2641895 : Blo 782338 2641895 := bstep (se 1 (by rfl) ⟨1981421, by rfl⟩ : syracuseStep 2641895 = 3962843) B3962843
theorem B2117807 : Blo 782338 2117807 := bstep (se 1 (by rfl) ⟨1588355, by rfl⟩ : syracuseStep 2117807 = 3176711) B3176711
theorem B6115571 : Blo 782338 6115571 := bstep (se 1 (by rfl) ⟨4586678, by rfl⟩ : syracuseStep 6115571 = 9173357) B9173357
theorem B8474867 : Blo 782338 8474867 := bstep (se 1 (by rfl) ⟨6356150, by rfl⟩ : syracuseStep 8474867 = 12712301) B12712301
theorem B2642273 : Blo 782338 2642273 := bstep (se 2 (by rfl) ⟨990852, by rfl⟩ : syracuseStep 2642273 = 1981705) B1981705
theorem B15062111 : Blo 782338 15062111 := bstep (se 1 (by rfl) ⟨11296583, by rfl⟩ : syracuseStep 15062111 = 22593167) B22593167
theorem B2511967 : Blo 782338 2511967 := bstep (se 1 (by rfl) ⟨1883975, by rfl⟩ : syracuseStep 2511967 = 3767951) B3767951
theorem B1987679 : Blo 782338 1987679 := bstep (se 1 (by rfl) ⟨1490759, by rfl⟩ : syracuseStep 1987679 = 2981519) B2981519
theorem B185881871 : Blo 782338 185881871 := bstep (se 1 (by rfl) ⟨139411403, by rfl⟩ : syracuseStep 185881871 = 278822807) B278822807
theorem B10736945 : Blo 782338 10736945 := bstep (se 2 (by rfl) ⟨4026354, by rfl⟩ : syracuseStep 10736945 = 8052709) B8052709
theorem B2643623 : Blo 782338 2643623 := bstep (se 1 (by rfl) ⟨1982717, by rfl⟩ : syracuseStep 2643623 = 3965435) B3965435
theorem B123655987 : Blo 782338 123655987 := bstep (se 1 (by rfl) ⟨92741990, by rfl⟩ : syracuseStep 123655987 = 185483981) B185483981
theorem B2119613 : Blo 782338 2119613 := bstep (se 3 (by rfl) ⟨397427, by rfl⟩ : syracuseStep 2119613 = 794855) B794855
theorem B9558161 : Blo 782338 9558161 := bstep (se 2 (by rfl) ⟨3584310, by rfl⟩ : syracuseStep 9558161 = 7168621) B7168621
theorem B1989431 : Blo 782338 1989431 := bstep (se 1 (by rfl) ⟨1492073, by rfl⟩ : syracuseStep 1989431 = 2984147) B2984147
theorem B2514017 : Blo 782338 2514017 := bstep (se 2 (by rfl) ⟨942756, by rfl⟩ : syracuseStep 2514017 = 1885513) B1885513
theorem B2645135 : Blo 782338 2645135 := bstep (se 1 (by rfl) ⟨1983851, by rfl⟩ : syracuseStep 2645135 = 3967703) B3967703
theorem B1760687 : Blo 782338 1760687 := bstep (se 1 (by rfl) ⟨1320515, by rfl⟩ : syracuseStep 1760687 = 2641031) B2641031
theorem B6970835 : Blo 782338 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B1760759 : Blo 782338 1760759 := bstep (se 1 (by rfl) ⟨1320569, by rfl⟩ : syracuseStep 1760759 = 2641139) B2641139
theorem B8937539 : Blo 782338 8937539 := bstep (se 1 (by rfl) ⟨6703154, by rfl⟩ : syracuseStep 8937539 = 13406309) B13406309
theorem B22667435 : Blo 782338 22667435 := bstep (se 1 (by rfl) ⟨17000576, by rfl⟩ : syracuseStep 22667435 = 34001153) B34001153
theorem B25747793 : Blo 782338 25747793 := bstep (se 2 (by rfl) ⟨9655422, by rfl⟩ : syracuseStep 25747793 = 19310845) B19310845
theorem B1761785 : Blo 782338 1761785 := bstep (se 2 (by rfl) ⟨660669, by rfl⟩ : syracuseStep 1761785 = 1321339) B1321339
theorem B1761875 : Blo 782338 1761875 := bstep (se 1 (by rfl) ⟨1321406, by rfl⟩ : syracuseStep 1761875 = 2642813) B2642813
theorem B1762055 : Blo 782338 1762055 := bstep (se 1 (by rfl) ⟨1321541, by rfl⟩ : syracuseStep 1762055 = 2643083) B2643083
theorem B1762145 : Blo 782338 1762145 := bstep (se 2 (by rfl) ⟨660804, by rfl⟩ : syracuseStep 1762145 = 1321609) B1321609
theorem B9528965 : Blo 782338 9528965 := bstep (se 4 (by rfl) ⟨893340, by rfl⟩ : syracuseStep 9528965 = 1786681) B1786681
theorem B1763135 : Blo 782338 1763135 := bstep (se 1 (by rfl) ⟨1322351, by rfl⟩ : syracuseStep 1763135 = 2644703) B2644703
theorem B10708919 : Blo 782338 10708919 := bstep (se 1 (by rfl) ⟨8031689, by rfl⟩ : syracuseStep 10708919 = 16063379) B16063379
theorem B2975687 : Blo 782338 2975687 := bstep (se 1 (by rfl) ⟨2231765, by rfl⟩ : syracuseStep 2975687 = 4463531) B4463531
theorem B3401671 : Blo 782338 3401671 := bstep (se 1 (by rfl) ⟨2551253, by rfl⟩ : syracuseStep 3401671 = 5102507) B5102507
theorem B2648051 : Blo 782338 2648051 := bstep (se 1 (by rfl) ⟨1986038, by rfl⟩ : syracuseStep 2648051 = 3972077) B3972077
theorem B1173551 : Blo 782338 1173551 := bstep (se 1 (by rfl) ⟨880163, by rfl⟩ : syracuseStep 1173551 = 1760327) B1760327
theorem B2680955 : Blo 782338 2680955 := bstep (se 1 (by rfl) ⟨2010716, by rfl⟩ : syracuseStep 2680955 = 4021433) B4021433
theorem B1173815 : Blo 782338 1173815 := bstep (se 1 (by rfl) ⟨880361, by rfl⟩ : syracuseStep 1173815 = 1760723) B1760723
theorem B1763639 : Blo 782338 1763639 := bstep (se 1 (by rfl) ⟨1322729, by rfl⟩ : syracuseStep 1763639 = 2645459) B2645459
theorem B1173995 : Blo 782338 1173995 := bstep (se 1 (by rfl) ⟨880496, by rfl⟩ : syracuseStep 1173995 = 1760993) B1760993
theorem B1763819 : Blo 782338 1763819 := bstep (se 1 (by rfl) ⟨1322864, by rfl⟩ : syracuseStep 1763819 = 2645729) B2645729
theorem B2648591 : Blo 782338 2648591 := bstep (se 1 (by rfl) ⟨1986443, by rfl⟩ : syracuseStep 2648591 = 3972887) B3972887
theorem B1174697 : Blo 782338 1174697 := bstep (se 2 (by rfl) ⟨440511, by rfl⟩ : syracuseStep 1174697 = 881023) B881023
theorem B1764521 : Blo 782338 1764521 := bstep (se 2 (by rfl) ⟨661695, by rfl⟩ : syracuseStep 1764521 = 1323391) B1323391
theorem B5958845 : Blo 782338 5958845 := bstep (se 3 (by rfl) ⟨1117283, by rfl⟩ : syracuseStep 5958845 = 2234567) B2234567
theorem B1175111 : Blo 782338 1175111 := bstep (se 1 (by rfl) ⟨881333, by rfl⟩ : syracuseStep 1175111 = 1762667) B1762667
theorem B1764935 : Blo 782338 1764935 := bstep (se 1 (by rfl) ⟨1323701, by rfl⟩ : syracuseStep 1764935 = 2647403) B2647403
theorem B2649671 : Blo 782338 2649671 := bstep (se 1 (by rfl) ⟨1987253, by rfl⟩ : syracuseStep 2649671 = 3974507) B3974507
theorem B880231 : Blo 782338 880231 := bstep (se 1 (by rfl) ⟨660173, by rfl⟩ : syracuseStep 880231 = 1320347) B1320347
theorem B1765007 : Blo 782338 1765007 := bstep (se 1 (by rfl) ⟨1323755, by rfl⟩ : syracuseStep 1765007 = 2647511) B2647511
theorem B1765097 : Blo 782338 1765097 := bstep (se 2 (by rfl) ⟨661911, by rfl⟩ : syracuseStep 1765097 = 1323823) B1323823
theorem B1175291 : Blo 782338 1175291 := bstep (se 1 (by rfl) ⟨881468, by rfl⟩ : syracuseStep 1175291 = 1762937) B1762937
theorem B1765115 : Blo 782338 1765115 := bstep (se 1 (by rfl) ⟨1323836, by rfl⟩ : syracuseStep 1765115 = 2647673) B2647673
theorem B880447 : Blo 782338 880447 := bstep (se 1 (by rfl) ⟨660335, by rfl⟩ : syracuseStep 880447 = 1320671) B1320671
theorem B782399 : Blo 782338 782399 := bstep (se 1 (by rfl) ⟨586799, by rfl⟩ : syracuseStep 782399 = 1173599) B1173599
theorem B880735 : Blo 782338 880735 := bstep (se 1 (by rfl) ⟨660551, by rfl⟩ : syracuseStep 880735 = 1321103) B1321103
theorem B782439 : Blo 782338 782439 := bstep (se 1 (by rfl) ⟨586829, by rfl⟩ : syracuseStep 782439 = 1173659) B1173659
theorem B782463 : Blo 782338 782463 := bstep (se 1 (by rfl) ⟨586847, by rfl⟩ : syracuseStep 782463 = 1173695) B1173695
theorem B782491 : Blo 782338 782491 := bstep (se 1 (by rfl) ⟨586868, by rfl⟩ : syracuseStep 782491 = 1173737) B1173737
theorem B782695 : Blo 782338 782695 := bstep (se 1 (by rfl) ⟨587021, by rfl⟩ : syracuseStep 782695 = 1174043) B1174043
theorem B782747 : Blo 782338 782747 := bstep (se 1 (by rfl) ⟨587060, by rfl⟩ : syracuseStep 782747 = 1174121) B1174121
theorem B1175963 : Blo 782338 1175963 := bstep (se 1 (by rfl) ⟨881972, by rfl⟩ : syracuseStep 1175963 = 1763945) B1763945
theorem B1766123 : Blo 782338 1766123 := bstep (se 1 (by rfl) ⟨1324592, by rfl⟩ : syracuseStep 1766123 = 2649185) B2649185
theorem B2650859 : Blo 782338 2650859 := bstep (se 1 (by rfl) ⟨1988144, by rfl⟩ : syracuseStep 2650859 = 3976289) B3976289
theorem B783099 : Blo 782338 783099 := bstep (se 1 (by rfl) ⟨587324, by rfl⟩ : syracuseStep 783099 = 1174649) B1174649
theorem B783167 : Blo 782338 783167 := bstep (se 1 (by rfl) ⟨587375, by rfl⟩ : syracuseStep 783167 = 1174751) B1174751
theorem B1176383 : Blo 782338 1176383 := bstep (se 1 (by rfl) ⟨882287, by rfl⟩ : syracuseStep 1176383 = 1764575) B1764575
theorem B783195 : Blo 782338 783195 := bstep (se 1 (by rfl) ⟨587396, by rfl⟩ : syracuseStep 783195 = 1174793) B1174793
theorem B783263 : Blo 782338 783263 := bstep (se 1 (by rfl) ⟨587447, by rfl⟩ : syracuseStep 783263 = 1174895) B1174895
theorem B1176527 : Blo 782338 1176527 := bstep (se 1 (by rfl) ⟨882395, by rfl⟩ : syracuseStep 1176527 = 1764791) B1764791
theorem B783343 : Blo 782338 783343 := bstep (se 1 (by rfl) ⟨587507, by rfl⟩ : syracuseStep 783343 = 1175015) B1175015
theorem B2651129 : Blo 782338 2651129 := bstep (se 2 (by rfl) ⟨994173, by rfl⟩ : syracuseStep 2651129 = 1988347) B1988347
theorem B1176569 : Blo 782338 1176569 := bstep (se 2 (by rfl) ⟨441213, by rfl⟩ : syracuseStep 1176569 = 882427) B882427
theorem B1766393 : Blo 782338 1766393 := bstep (se 2 (by rfl) ⟨662397, by rfl⟩ : syracuseStep 1766393 = 1324795) B1324795
theorem B3961871 : Blo 782338 3961871 := bstep (se 1 (by rfl) ⟨2971403, by rfl⟩ : syracuseStep 3961871 = 5942807) B5942807
theorem B1176617 : Blo 782338 1176617 := bstep (se 2 (by rfl) ⟨441231, by rfl⟩ : syracuseStep 1176617 = 882463) B882463
theorem B783431 : Blo 782338 783431 := bstep (se 1 (by rfl) ⟨587573, by rfl⟩ : syracuseStep 783431 = 1175147) B1175147
theorem B1176647 : Blo 782338 1176647 := bstep (se 1 (by rfl) ⟨882485, by rfl⟩ : syracuseStep 1176647 = 1764971) B1764971
theorem B1766483 : Blo 782338 1766483 := bstep (se 1 (by rfl) ⟨1324862, by rfl⟩ : syracuseStep 1766483 = 2649725) B2649725
theorem B783515 : Blo 782338 783515 := bstep (se 1 (by rfl) ⟨587636, by rfl⟩ : syracuseStep 783515 = 1175273) B1175273
theorem B783611 : Blo 782338 783611 := bstep (se 1 (by rfl) ⟨587708, by rfl⟩ : syracuseStep 783611 = 1175417) B1175417
theorem B1176827 : Blo 782338 1176827 := bstep (se 1 (by rfl) ⟨882620, by rfl⟩ : syracuseStep 1176827 = 1765241) B1765241
theorem B1766663 : Blo 782338 1766663 := bstep (se 1 (by rfl) ⟨1324997, by rfl⟩ : syracuseStep 1766663 = 2649995) B2649995
theorem B2651399 : Blo 782338 2651399 := bstep (se 1 (by rfl) ⟨1988549, by rfl⟩ : syracuseStep 2651399 = 3977099) B3977099
theorem B783679 : Blo 782338 783679 := bstep (se 1 (by rfl) ⟨587759, by rfl⟩ : syracuseStep 783679 = 1175519) B1175519
theorem B2979287 : Blo 782338 2979287 := bstep (se 1 (by rfl) ⟨2234465, by rfl⟩ : syracuseStep 2979287 = 4468931) B4468931
theorem B783847 : Blo 782338 783847 := bstep (se 1 (by rfl) ⟨587885, by rfl⟩ : syracuseStep 783847 = 1175771) B1175771
theorem B783855 : Blo 782338 783855 := bstep (se 1 (by rfl) ⟨587891, by rfl⟩ : syracuseStep 783855 = 1175783) B1175783
theorem B783963 : Blo 782338 783963 := bstep (se 1 (by rfl) ⟨587972, by rfl⟩ : syracuseStep 783963 = 1175945) B1175945
theorem B3012191 : Blo 782338 3012191 := bstep (se 1 (by rfl) ⟨2259143, by rfl⟩ : syracuseStep 3012191 = 4518287) B4518287
theorem B5666399 : Blo 782338 5666399 := bstep (se 1 (by rfl) ⟨4249799, by rfl⟩ : syracuseStep 5666399 = 8499599) B8499599
theorem B1767023 : Blo 782338 1767023 := bstep (se 1 (by rfl) ⟨1325267, by rfl⟩ : syracuseStep 1767023 = 2650535) B2650535
theorem B784027 : Blo 782338 784027 := bstep (se 1 (by rfl) ⟨588020, by rfl⟩ : syracuseStep 784027 = 1176041) B1176041
theorem B784111 : Blo 782338 784111 := bstep (se 1 (by rfl) ⟨588083, by rfl⟩ : syracuseStep 784111 = 1176167) B1176167
theorem B6715183 : Blo 782338 6715183 := bstep (se 1 (by rfl) ⟨5036387, by rfl⟩ : syracuseStep 6715183 = 10072775) B10072775
theorem B3962681 : Blo 782338 3962681 := bstep (se 2 (by rfl) ⟨1486005, by rfl⟩ : syracuseStep 3962681 = 2972011) B2972011
theorem B784199 : Blo 782338 784199 := bstep (se 1 (by rfl) ⟨588149, by rfl⟩ : syracuseStep 784199 = 1176299) B1176299
theorem B784219 : Blo 782338 784219 := bstep (se 1 (by rfl) ⟨588164, by rfl⟩ : syracuseStep 784219 = 1176329) B1176329
theorem B784287 : Blo 782338 784287 := bstep (se 1 (by rfl) ⟨588215, by rfl⟩ : syracuseStep 784287 = 1176431) B1176431
theorem B784455 : Blo 782338 784455 := bstep (se 1 (by rfl) ⟨588341, by rfl⟩ : syracuseStep 784455 = 1176683) B1176683
theorem B2652371 : Blo 782338 2652371 := bstep (se 1 (by rfl) ⟨1989278, by rfl⟩ : syracuseStep 2652371 = 3978557) B3978557
theorem B784615 : Blo 782338 784615 := bstep (se 1 (by rfl) ⟨588461, by rfl⟩ : syracuseStep 784615 = 1176923) B1176923
theorem B784799 : Blo 782338 784799 := bstep (se 1 (by rfl) ⟨588599, by rfl⟩ : syracuseStep 784799 = 1177199) B1177199
theorem B6027709 : Blo 782338 6027709 := bstep (se 3 (by rfl) ⟨1130195, by rfl⟩ : syracuseStep 6027709 = 2260391) B2260391
theorem B3963329 : Blo 782338 3963329 := bstep (se 2 (by rfl) ⟨1486248, by rfl⟩ : syracuseStep 3963329 = 2972497) B2972497
theorem B784847 : Blo 782338 784847 := bstep (se 1 (by rfl) ⟨588635, by rfl⟩ : syracuseStep 784847 = 1177271) B1177271
theorem B1178063 : Blo 782338 1178063 := bstep (se 1 (by rfl) ⟨883547, by rfl⟩ : syracuseStep 1178063 = 1767095) B1767095
theorem B1767887 : Blo 782338 1767887 := bstep (se 1 (by rfl) ⟨1325915, by rfl⟩ : syracuseStep 1767887 = 2651831) B2651831
theorem B2652641 : Blo 782338 2652641 := bstep (se 2 (by rfl) ⟨994740, by rfl⟩ : syracuseStep 2652641 = 1989481) B1989481
theorem B784871 : Blo 782338 784871 := bstep (se 1 (by rfl) ⟨588653, by rfl⟩ : syracuseStep 784871 = 1177307) B1177307
theorem B1178153 : Blo 782338 1178153 := bstep (se 2 (by rfl) ⟨441807, by rfl⟩ : syracuseStep 1178153 = 883615) B883615
theorem B1767977 : Blo 782338 1767977 := bstep (se 2 (by rfl) ⟨662991, by rfl⟩ : syracuseStep 1767977 = 1325983) B1325983
theorem B18086449 : Blo 782338 18086449 := bstep (se 2 (by rfl) ⟨6782418, by rfl⟩ : syracuseStep 18086449 = 13564837) B13564837
theorem B784987 : Blo 782338 784987 := bstep (se 1 (by rfl) ⟨588740, by rfl⟩ : syracuseStep 784987 = 1177481) B1177481
theorem B883291 : Blo 782338 883291 := bstep (se 1 (by rfl) ⟨662468, by rfl⟩ : syracuseStep 883291 = 1324937) B1324937
theorem B785055 : Blo 782338 785055 := bstep (se 1 (by rfl) ⟨588791, by rfl⟩ : syracuseStep 785055 = 1177583) B1177583
theorem B2980577 : Blo 782338 2980577 := bstep (se 2 (by rfl) ⟨1117716, by rfl⟩ : syracuseStep 2980577 = 2235433) B2235433
theorem B1178345 : Blo 782338 1178345 := bstep (se 2 (by rfl) ⟨441879, by rfl⟩ : syracuseStep 1178345 = 883759) B883759
theorem B785223 : Blo 782338 785223 := bstep (se 1 (by rfl) ⟨588917, by rfl⟩ : syracuseStep 785223 = 1177835) B1177835
theorem B785263 : Blo 782338 785263 := bstep (se 1 (by rfl) ⟨588947, by rfl⟩ : syracuseStep 785263 = 1177895) B1177895
theorem B883579 : Blo 782338 883579 := bstep (se 1 (by rfl) ⟨662684, by rfl⟩ : syracuseStep 883579 = 1325369) B1325369
theorem B2456477 : Blo 782338 2456477 := bstep (se 3 (by rfl) ⟨460589, by rfl⟩ : syracuseStep 2456477 = 921179) B921179
theorem B785319 : Blo 782338 785319 := bstep (se 1 (by rfl) ⟨588989, by rfl⟩ : syracuseStep 785319 = 1177979) B1177979
theorem B785499 : Blo 782338 785499 := bstep (se 1 (by rfl) ⟨589124, by rfl⟩ : syracuseStep 785499 = 1178249) B1178249
theorem B1178729 : Blo 782338 1178729 := bstep (se 2 (by rfl) ⟨442023, by rfl⟩ : syracuseStep 1178729 = 884047) B884047
theorem B1768553 : Blo 782338 1768553 := bstep (se 2 (by rfl) ⟨663207, by rfl⟩ : syracuseStep 1768553 = 1326415) B1326415
theorem B785615 : Blo 782338 785615 := bstep (se 1 (by rfl) ⟨589211, by rfl⟩ : syracuseStep 785615 = 1178423) B1178423
theorem B785639 : Blo 782338 785639 := bstep (se 1 (by rfl) ⟨589229, by rfl⟩ : syracuseStep 785639 = 1178459) B1178459
theorem B1178855 : Blo 782338 1178855 := bstep (se 1 (by rfl) ⟨884141, by rfl⟩ : syracuseStep 1178855 = 1768283) B1768283
theorem B1768679 : Blo 782338 1768679 := bstep (se 1 (by rfl) ⟨1326509, by rfl⟩ : syracuseStep 1768679 = 2653019) B2653019
theorem B785735 : Blo 782338 785735 := bstep (se 1 (by rfl) ⟨589301, by rfl⟩ : syracuseStep 785735 = 1178603) B1178603
theorem B2981231 : Blo 782338 2981231 := bstep (se 1 (by rfl) ⟨2235923, by rfl⟩ : syracuseStep 2981231 = 4471847) B4471847
theorem B15105473 : Blo 782338 15105473 := bstep (se 2 (by rfl) ⟨5664552, by rfl⟩ : syracuseStep 15105473 = 11329105) B11329105
theorem B785871 : Blo 782338 785871 := bstep (se 1 (by rfl) ⟨589403, by rfl⟩ : syracuseStep 785871 = 1178807) B1178807
theorem B28671569 : Blo 782338 28671569 := bstep (se 2 (by rfl) ⟨10751838, by rfl⟩ : syracuseStep 28671569 = 21503677) B21503677
theorem B786031 : Blo 782338 786031 := bstep (se 1 (by rfl) ⟨589523, by rfl⟩ : syracuseStep 786031 = 1179047) B1179047
theorem B884335 : Blo 782338 884335 := bstep (se 1 (by rfl) ⟨663251, by rfl⟩ : syracuseStep 884335 = 1326503) B1326503
theorem B786087 : Blo 782338 786087 := bstep (se 1 (by rfl) ⟨589565, by rfl⟩ : syracuseStep 786087 = 1179131) B1179131
theorem B884443 : Blo 782338 884443 := bstep (se 1 (by rfl) ⟨663332, by rfl⟩ : syracuseStep 884443 = 1326665) B1326665
theorem B1179359 : Blo 782338 1179359 := bstep (se 1 (by rfl) ⟨884519, by rfl⟩ : syracuseStep 1179359 = 1769039) B1769039
theorem B1769183 : Blo 782338 1769183 := bstep (se 1 (by rfl) ⟨1326887, by rfl⟩ : syracuseStep 1769183 = 2653775) B2653775
theorem B786151 : Blo 782338 786151 := bstep (se 1 (by rfl) ⟨589613, by rfl⟩ : syracuseStep 786151 = 1179227) B1179227
theorem B1179401 : Blo 782338 1179401 := bstep (se 2 (by rfl) ⟨442275, by rfl⟩ : syracuseStep 1179401 = 884551) B884551
theorem B786207 : Blo 782338 786207 := bstep (se 1 (by rfl) ⟨589655, by rfl⟩ : syracuseStep 786207 = 1179311) B1179311
theorem B1769255 : Blo 782338 1769255 := bstep (se 1 (by rfl) ⟨1326941, by rfl⟩ : syracuseStep 1769255 = 2653883) B2653883
theorem B786287 : Blo 782338 786287 := bstep (se 1 (by rfl) ⟨589715, by rfl⟩ : syracuseStep 786287 = 1179431) B1179431
theorem B2982035 : Blo 782338 2982035 := bstep (se 1 (by rfl) ⟨2236526, by rfl⟩ : syracuseStep 2982035 = 4473053) B4473053
theorem B3768605 : Blo 782338 3768605 := bstep (se 3 (by rfl) ⟨706613, by rfl⟩ : syracuseStep 3768605 = 1413227) B1413227
theorem B5014223 : Blo 782338 5014223 := bstep (se 1 (by rfl) ⟨3760667, by rfl⟩ : syracuseStep 5014223 = 7521335) B7521335
theorem B12059603 : Blo 782338 12059603 := bstep (se 1 (by rfl) ⟨9044702, by rfl⟩ : syracuseStep 12059603 = 18089405) B18089405
theorem B2229601 : Blo 782338 2229601 := bstep (se 2 (by rfl) ⟨836100, by rfl⟩ : syracuseStep 2229601 = 1672201) B1672201
theorem B16090649 : Blo 782338 16090649 := bstep (se 2 (by rfl) ⟨6033993, by rfl⟩ : syracuseStep 16090649 = 12067987) B12067987
theorem B2983675 : Blo 782338 2983675 := bstep (se 1 (by rfl) ⟨2237756, by rfl⟩ : syracuseStep 2983675 = 4475513) B4475513
theorem B8063675 : Blo 782338 8063675 := bstep (se 1 (by rfl) ⟨6047756, by rfl⟩ : syracuseStep 8063675 = 12095513) B12095513
theorem B1411871 : Blo 782338 1411871 := bstep (se 1 (by rfl) ⟨1058903, by rfl⟩ : syracuseStep 1411871 = 2117807) B2117807
theorem B20089781 : Blo 782338 20089781 := bstep (se 5 (by rfl) ⟨941708, by rfl⟩ : syracuseStep 20089781 = 1883417) B1883417
theorem B4459475 : Blo 782338 4459475 := bstep (se 1 (by rfl) ⟨3344606, by rfl⟩ : syracuseStep 4459475 = 6689213) B6689213
theorem B2231401 : Blo 782338 2231401 := bstep (se 2 (by rfl) ⟨836775, by rfl⟩ : syracuseStep 2231401 = 1673551) B1673551
theorem B10488997 : Blo 782338 10488997 := bstep (se 4 (by rfl) ⟨983343, by rfl⟩ : syracuseStep 10488997 = 1966687) B1966687
theorem B1117415 : Blo 782338 1117415 := bstep (se 1 (by rfl) ⟨838061, by rfl⟩ : syracuseStep 1117415 = 1676123) B1676123
theorem B5017373 : Blo 782338 5017373 := bstep (se 3 (by rfl) ⟨940757, by rfl⟩ : syracuseStep 5017373 = 1881515) B1881515
theorem B3346231 : Blo 782338 3346231 := bstep (se 1 (by rfl) ⟨2509673, by rfl⟩ : syracuseStep 3346231 = 5019347) B5019347
theorem B3346505 : Blo 782338 3346505 := bstep (se 2 (by rfl) ⟨1254939, by rfl⟩ : syracuseStep 3346505 = 2509879) B2509879
theorem B14292287 : Blo 782338 14292287 := bstep (se 1 (by rfl) ⟨10719215, by rfl⟩ : syracuseStep 14292287 = 21438431) B21438431
theorem B15111623 : Blo 782338 15111623 := bstep (se 1 (by rfl) ⟨11333717, by rfl⟩ : syracuseStep 15111623 = 22667435) B22667435
theorem B2233919 : Blo 782338 2233919 := bstep (se 1 (by rfl) ⟨1675439, by rfl⟩ : syracuseStep 2233919 = 3350879) B3350879
theorem B7542895 : Blo 782338 7542895 := bstep (se 1 (by rfl) ⟨5657171, by rfl⟩ : syracuseStep 7542895 = 11314343) B11314343
theorem B5085337 : Blo 782338 5085337 := bstep (se 2 (by rfl) ⟨1907001, by rfl⟩ : syracuseStep 5085337 = 3814003) B3814003
theorem B3349289 : Blo 782338 3349289 := bstep (se 2 (by rfl) ⟨1255983, by rfl⟩ : syracuseStep 3349289 = 2511967) B2511967
theorem B4463849 : Blo 782338 4463849 := bstep (se 2 (by rfl) ⟨1673943, by rfl⟩ : syracuseStep 4463849 = 3347887) B3347887
theorem B3972563 : Blo 782338 3972563 := bstep (se 1 (by rfl) ⟨2979422, by rfl⟩ : syracuseStep 3972563 = 5958845) B5958845
theorem B30154355 : Blo 782338 30154355 := bstep (se 1 (by rfl) ⟨22615766, by rfl⟩ : syracuseStep 30154355 = 45231533) B45231533
theorem B2236025 : Blo 782338 2236025 := bstep (se 2 (by rfl) ⟨838509, by rfl⟩ : syracuseStep 2236025 = 1677019) B1677019
theorem B8953577 : Blo 782338 8953577 := bstep (se 2 (by rfl) ⟨3357591, by rfl⟩ : syracuseStep 8953577 = 6715183) B6715183
theorem B4464557 : Blo 782338 4464557 := bstep (se 3 (by rfl) ⟨837104, by rfl⟩ : syracuseStep 4464557 = 1674209) B1674209
theorem B8036945 : Blo 782338 8036945 := bstep (se 2 (by rfl) ⟨3013854, by rfl⟩ : syracuseStep 8036945 = 6027709) B6027709
theorem B1057385 : Blo 782338 1057385 := bstep (se 2 (by rfl) ⟨396519, by rfl⟩ : syracuseStep 1057385 = 793039) B793039
theorem B991855 : Blo 782338 991855 := bstep (se 1 (by rfl) ⟨743891, by rfl⟩ : syracuseStep 991855 = 1487783) B1487783
theorem B3777599 : Blo 782338 3777599 := bstep (se 1 (by rfl) ⟨2833199, by rfl⟩ : syracuseStep 3777599 = 5666399) B5666399
theorem B992351 : Blo 782338 992351 := bstep (se 1 (by rfl) ⟨744263, by rfl⟩ : syracuseStep 992351 = 1488527) B1488527
theorem B20129147 : Blo 782338 20129147 := bstep (se 1 (by rfl) ⟨15096860, by rfl⟩ : syracuseStep 20129147 = 30193721) B30193721
theorem B992999 : Blo 782338 992999 := bstep (se 1 (by rfl) ⟨744749, by rfl⟩ : syracuseStep 992999 = 1489499) B1489499
theorem B10070315 : Blo 782338 10070315 := bstep (se 1 (by rfl) ⟨7552736, by rfl⟩ : syracuseStep 10070315 = 15105473) B15105473
theorem B19114379 : Blo 782338 19114379 := bstep (se 1 (by rfl) ⟨14335784, by rfl⟩ : syracuseStep 19114379 = 28671569) B28671569
theorem B1255919 : Blo 782338 1255919 := bstep (se 1 (by rfl) ⟨941939, by rfl⟩ : syracuseStep 1255919 = 1883879) B1883879
theorem B16132679 : Blo 782338 16132679 := bstep (se 1 (by rfl) ⟨12099509, by rfl⟩ : syracuseStep 16132679 = 24199019) B24199019
theorem B12889151 : Blo 782338 12889151 := bstep (se 1 (by rfl) ⟨9666863, by rfl⟩ : syracuseStep 12889151 = 19333727) B19333727
theorem B1486127 : Blo 782338 1486127 := bstep (se 1 (by rfl) ⟨1114595, by rfl⟩ : syracuseStep 1486127 = 2229191) B2229191
theorem B1912175 : Blo 782338 1912175 := bstep (se 1 (by rfl) ⟨1434131, by rfl⟩ : syracuseStep 1912175 = 2868263) B2868263
theorem B1322399 : Blo 782338 1322399 := bstep (se 1 (by rfl) ⟨991799, by rfl⟩ : syracuseStep 1322399 = 1983599) B1983599
theorem B20328131 : Blo 782338 20328131 := bstep (se 1 (by rfl) ⟨15246098, by rfl⟩ : syracuseStep 20328131 = 30492197) B30492197
theorem B3355303 : Blo 782338 3355303 := bstep (se 1 (by rfl) ⟨2516477, by rfl⟩ : syracuseStep 3355303 = 5032955) B5032955
theorem B7156943 : Blo 782338 7156943 := bstep (se 1 (by rfl) ⟨5367707, by rfl⟩ : syracuseStep 7156943 = 10735415) B10735415
theorem B4535561 : Blo 782338 4535561 := bstep (se 2 (by rfl) ⟨1700835, by rfl⟩ : syracuseStep 4535561 = 3401671) B3401671
theorem B4470137 : Blo 782338 4470137 := bstep (se 2 (by rfl) ⟨1676301, by rfl⟩ : syracuseStep 4470137 = 3352603) B3352603
theorem B5944751 : Blo 782338 5944751 := bstep (se 1 (by rfl) ⟨4458563, by rfl⟩ : syracuseStep 5944751 = 8917127) B8917127
theorem B4077047 : Blo 782338 4077047 := bstep (se 1 (by rfl) ⟨3057785, by rfl⟩ : syracuseStep 4077047 = 6115571) B6115571
theorem B5649911 : Blo 782338 5649911 := bstep (se 1 (by rfl) ⟨4237433, by rfl⟩ : syracuseStep 5649911 = 8474867) B8474867
theorem B10041407 : Blo 782338 10041407 := bstep (se 1 (by rfl) ⟨7531055, by rfl⟩ : syracuseStep 10041407 = 15062111) B15062111
theorem B1325119 : Blo 782338 1325119 := bstep (se 1 (by rfl) ⟨993839, by rfl⟩ : syracuseStep 1325119 = 1987679) B1987679
theorem B7157963 : Blo 782338 7157963 := bstep (se 1 (by rfl) ⟨5368472, by rfl⟩ : syracuseStep 7157963 = 10736945) B10736945
theorem B6372107 : Blo 782338 6372107 := bstep (se 1 (by rfl) ⟨4779080, by rfl⟩ : syracuseStep 6372107 = 9558161) B9558161
theorem B4242233 : Blo 782338 4242233 := bstep (se 2 (by rfl) ⟨1590837, by rfl⟩ : syracuseStep 4242233 = 3181675) B3181675
theorem B5028803 : Blo 782338 5028803 := bstep (se 1 (by rfl) ⟨3771602, by rfl⟩ : syracuseStep 5028803 = 7543205) B7543205
theorem B1326287 : Blo 782338 1326287 := bstep (se 1 (by rfl) ⟨994715, by rfl⟩ : syracuseStep 1326287 = 1989431) B1989431
theorem B12729673 : Blo 782338 12729673 := bstep (se 2 (by rfl) ⟨4773627, by rfl⟩ : syracuseStep 12729673 = 9547255) B9547255
theorem B6799049 : Blo 782338 6799049 := bstep (se 2 (by rfl) ⟨2549643, by rfl⟩ : syracuseStep 6799049 = 5099287) B5099287
theorem B38256371 : Blo 782338 38256371 := bstep (se 1 (by rfl) ⟨28692278, by rfl⟩ : syracuseStep 38256371 = 57384557) B57384557
theorem B4244071 : Blo 782338 4244071 := bstep (se 1 (by rfl) ⟨3183053, by rfl⟩ : syracuseStep 4244071 = 6366107) B6366107
theorem B32130037 : Blo 782338 32130037 := bstep (se 5 (by rfl) ⟨1506095, by rfl⟩ : syracuseStep 32130037 = 3012191) B3012191
theorem B1983791 : Blo 782338 1983791 := bstep (se 1 (by rfl) ⟨1487843, by rfl⟩ : syracuseStep 1983791 = 2975687) B2975687
theorem B1787303 : Blo 782338 1787303 := bstep (se 1 (by rfl) ⟨1340477, by rfl⟩ : syracuseStep 1787303 = 2680955) B2680955
theorem B1886185 : Blo 782338 1886185 := bstep (se 2 (by rfl) ⟨707319, by rfl⟩ : syracuseStep 1886185 = 1414639) B1414639
theorem B164874649 : Blo 782338 164874649 := bstep (se 2 (by rfl) ⟨61827993, by rfl⟩ : syracuseStep 164874649 = 123655987) B123655987
theorem B5950097 : Blo 782338 5950097 := bstep (se 2 (by rfl) ⟨2231286, by rfl⟩ : syracuseStep 5950097 = 4462573) B4462573
theorem B1985249 : Blo 782338 1985249 := bstep (se 2 (by rfl) ⟨744468, by rfl⟩ : syracuseStep 1985249 = 1488937) B1488937
theorem B6704045 : Blo 782338 6704045 := bstep (se 3 (by rfl) ⟨1257008, by rfl⟩ : syracuseStep 6704045 = 2514017) B2514017
theorem B4246685 : Blo 782338 4246685 := bstep (se 3 (by rfl) ⟨796253, by rfl⟩ : syracuseStep 4246685 = 1592507) B1592507
theorem B7523675 : Blo 782338 7523675 := bstep (se 1 (by rfl) ⟨5642756, by rfl⟩ : syracuseStep 7523675 = 11285513) B11285513
theorem B2641247 : Blo 782338 2641247 := bstep (se 1 (by rfl) ⟨1980935, by rfl⟩ : syracuseStep 2641247 = 3961871) B3961871
theorem B1986191 : Blo 782338 1986191 := bstep (se 1 (by rfl) ⟨1489643, by rfl⟩ : syracuseStep 1986191 = 2979287) B2979287
theorem B2641787 : Blo 782338 2641787 := bstep (se 1 (by rfl) ⟨1981340, by rfl⟩ : syracuseStep 2641787 = 3962681) B3962681
theorem B5033927 : Blo 782338 5033927 := bstep (se 1 (by rfl) ⟨3775445, by rfl⟩ : syracuseStep 5033927 = 7550891) B7550891
theorem B19124495 : Blo 782338 19124495 := bstep (se 1 (by rfl) ⟨14343371, by rfl⟩ : syracuseStep 19124495 = 28686743) B28686743
theorem B2642219 : Blo 782338 2642219 := bstep (se 1 (by rfl) ⟨1981664, by rfl⟩ : syracuseStep 2642219 = 3963329) B3963329
theorem B1987051 : Blo 782338 1987051 := bstep (se 1 (by rfl) ⟨1490288, by rfl⟩ : syracuseStep 1987051 = 2980577) B2980577
theorem B1987487 : Blo 782338 1987487 := bstep (se 1 (by rfl) ⟨1490615, by rfl⟩ : syracuseStep 1987487 = 2981231) B2981231
theorem B7525673 : Blo 782338 7525673 := bstep (se 2 (by rfl) ⟨2822127, by rfl⟩ : syracuseStep 7525673 = 5644255) B5644255
theorem B5953499 : Blo 782338 5953499 := bstep (se 1 (by rfl) ⟨4465124, by rfl⟩ : syracuseStep 5953499 = 8930249) B8930249
theorem B2644217 : Blo 782338 2644217 := bstep (se 2 (by rfl) ⟨991581, by rfl⟩ : syracuseStep 2644217 = 1983163) B1983163
theorem B2644379 : Blo 782338 2644379 := bstep (se 1 (by rfl) ⟨1983284, by rfl⟩ : syracuseStep 2644379 = 3966569) B3966569
theorem B1760363 : Blo 782338 1760363 := bstep (se 1 (by rfl) ⟨1320272, by rfl⟩ : syracuseStep 1760363 = 2640545) B2640545
theorem B1760507 : Blo 782338 1760507 := bstep (se 1 (by rfl) ⟨1320380, by rfl⟩ : syracuseStep 1760507 = 2640761) B2640761
theorem B6348041 : Blo 782338 6348041 := bstep (se 2 (by rfl) ⟨2380515, by rfl⟩ : syracuseStep 6348041 = 4761031) B4761031
theorem B1989967 : Blo 782338 1989967 := bstep (se 1 (by rfl) ⟨1492475, by rfl⟩ : syracuseStep 1989967 = 2984951) B2984951
theorem B1760633 : Blo 782338 1760633 := bstep (se 2 (by rfl) ⟨660237, by rfl⟩ : syracuseStep 1760633 = 1320475) B1320475
theorem B9526727 : Blo 782338 9526727 := bstep (se 1 (by rfl) ⟨7145045, by rfl⟩ : syracuseStep 9526727 = 14290091) B14290091
theorem B3759803 : Blo 782338 3759803 := bstep (se 1 (by rfl) ⟨2819852, by rfl⟩ : syracuseStep 3759803 = 5639705) B5639705
theorem B2547667 : Blo 782338 2547667 := bstep (se 1 (by rfl) ⟨1910750, by rfl⟩ : syracuseStep 2547667 = 3821501) B3821501
theorem B1761263 : Blo 782338 1761263 := bstep (se 1 (by rfl) ⟨1320947, by rfl⟩ : syracuseStep 1761263 = 2641895) B2641895
theorem B1761515 : Blo 782338 1761515 := bstep (se 1 (by rfl) ⟨1321136, by rfl⟩ : syracuseStep 1761515 = 2642273) B2642273
theorem B8282891 : Blo 782338 8282891 := bstep (se 1 (by rfl) ⟨6212168, by rfl⟩ : syracuseStep 8282891 = 12424337) B12424337
theorem B123921247 : Blo 782338 123921247 := bstep (se 1 (by rfl) ⟨92940935, by rfl⟩ : syracuseStep 123921247 = 185881871) B185881871
theorem B1762415 : Blo 782338 1762415 := bstep (se 1 (by rfl) ⟨1321811, by rfl⟩ : syracuseStep 1762415 = 2643623) B2643623
theorem B1763423 : Blo 782338 1763423 := bstep (se 1 (by rfl) ⟨1322567, by rfl⟩ : syracuseStep 1763423 = 2645135) B2645135
theorem B1173641 : Blo 782338 1173641 := bstep (se 2 (by rfl) ⟨440115, by rfl⟩ : syracuseStep 1173641 = 880231) B880231
theorem B1173791 : Blo 782338 1173791 := bstep (se 1 (by rfl) ⟨880343, by rfl⟩ : syracuseStep 1173791 = 1760687) B1760687
theorem B4647223 : Blo 782338 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B1173839 : Blo 782338 1173839 := bstep (se 1 (by rfl) ⟨880379, by rfl⟩ : syracuseStep 1173839 = 1760759) B1760759
theorem B1173929 : Blo 782338 1173929 := bstep (se 2 (by rfl) ⟨440223, by rfl⟩ : syracuseStep 1173929 = 880447) B880447
theorem B5958359 : Blo 782338 5958359 := bstep (se 1 (by rfl) ⟨4468769, by rfl⟩ : syracuseStep 5958359 = 8937539) B8937539
theorem B1174313 : Blo 782338 1174313 := bstep (se 2 (by rfl) ⟨440367, by rfl⟩ : syracuseStep 1174313 = 880735) B880735
theorem B17165195 : Blo 782338 17165195 := bstep (se 1 (by rfl) ⟨12873896, by rfl⟩ : syracuseStep 17165195 = 25747793) B25747793
theorem B1174523 : Blo 782338 1174523 := bstep (se 1 (by rfl) ⟨880892, by rfl⟩ : syracuseStep 1174523 = 1761785) B1761785
theorem B1174583 : Blo 782338 1174583 := bstep (se 1 (by rfl) ⟨880937, by rfl⟩ : syracuseStep 1174583 = 1761875) B1761875
theorem B1174703 : Blo 782338 1174703 := bstep (se 1 (by rfl) ⟨881027, by rfl⟩ : syracuseStep 1174703 = 1762055) B1762055
theorem B1174763 : Blo 782338 1174763 := bstep (se 1 (by rfl) ⟨881072, by rfl⟩ : syracuseStep 1174763 = 1762145) B1762145
theorem B1273159 : Blo 782338 1273159 := bstep (se 1 (by rfl) ⟨954869, by rfl⟩ : syracuseStep 1273159 = 1909739) B1909739
theorem B8580809 : Blo 782338 8580809 := bstep (se 2 (by rfl) ⟨3217803, by rfl⟩ : syracuseStep 8580809 = 6435607) B6435607
theorem B6352643 : Blo 782338 6352643 := bstep (se 1 (by rfl) ⟨4764482, by rfl⟩ : syracuseStep 6352643 = 9528965) B9528965
theorem B1175423 : Blo 782338 1175423 := bstep (se 1 (by rfl) ⟨881567, by rfl⟩ : syracuseStep 1175423 = 1763135) B1763135
theorem B7139279 : Blo 782338 7139279 := bstep (se 1 (by rfl) ⟨5354459, by rfl⟩ : syracuseStep 7139279 = 10708919) B10708919
theorem B1765367 : Blo 782338 1765367 := bstep (se 1 (by rfl) ⟨1324025, by rfl⟩ : syracuseStep 1765367 = 2648051) B2648051
theorem B782367 : Blo 782338 782367 := bstep (se 1 (by rfl) ⟨586775, by rfl⟩ : syracuseStep 782367 = 1173551) B1173551
theorem B782543 : Blo 782338 782543 := bstep (se 1 (by rfl) ⟨586907, by rfl⟩ : syracuseStep 782543 = 1173815) B1173815
theorem B1175759 : Blo 782338 1175759 := bstep (se 1 (by rfl) ⟨881819, by rfl⟩ : syracuseStep 1175759 = 1763639) B1763639
theorem B2650319 : Blo 782338 2650319 := bstep (se 1 (by rfl) ⟨1987739, by rfl⟩ : syracuseStep 2650319 = 3975479) B3975479
theorem B782663 : Blo 782338 782663 := bstep (se 1 (by rfl) ⟨586997, by rfl⟩ : syracuseStep 782663 = 1173995) B1173995
theorem B1175879 : Blo 782338 1175879 := bstep (se 1 (by rfl) ⟨881909, by rfl⟩ : syracuseStep 1175879 = 1763819) B1763819
theorem B1765727 : Blo 782338 1765727 := bstep (se 1 (by rfl) ⟨1324295, by rfl⟩ : syracuseStep 1765727 = 2648591) B2648591
theorem B783131 : Blo 782338 783131 := bstep (se 1 (by rfl) ⟨587348, by rfl⟩ : syracuseStep 783131 = 1174697) B1174697
theorem B1176347 : Blo 782338 1176347 := bstep (se 1 (by rfl) ⟨882260, by rfl⟩ : syracuseStep 1176347 = 1764521) B1764521
theorem B1766249 : Blo 782338 1766249 := bstep (se 2 (by rfl) ⟨662343, by rfl⟩ : syracuseStep 1766249 = 1324687) B1324687
theorem B783407 : Blo 782338 783407 := bstep (se 1 (by rfl) ⟨587555, by rfl⟩ : syracuseStep 783407 = 1175111) B1175111
theorem B1176623 : Blo 782338 1176623 := bstep (se 1 (by rfl) ⟨882467, by rfl⟩ : syracuseStep 1176623 = 1764935) B1764935
theorem B1766447 : Blo 782338 1766447 := bstep (se 1 (by rfl) ⟨1324835, by rfl⟩ : syracuseStep 1766447 = 2649671) B2649671
theorem B1176671 : Blo 782338 1176671 := bstep (se 1 (by rfl) ⟨882503, by rfl⟩ : syracuseStep 1176671 = 1765007) B1765007
theorem B1176731 : Blo 782338 1176731 := bstep (se 1 (by rfl) ⟨882548, by rfl⟩ : syracuseStep 1176731 = 1765097) B1765097
theorem B2651291 : Blo 782338 2651291 := bstep (se 1 (by rfl) ⟨1988468, by rfl⟩ : syracuseStep 2651291 = 3976937) B3976937
theorem B783527 : Blo 782338 783527 := bstep (se 1 (by rfl) ⟨587645, by rfl⟩ : syracuseStep 783527 = 1175291) B1175291
theorem B1176743 : Blo 782338 1176743 := bstep (se 1 (by rfl) ⟨882557, by rfl⟩ : syracuseStep 1176743 = 1765115) B1765115
theorem B783975 : Blo 782338 783975 := bstep (se 1 (by rfl) ⟨587981, by rfl⟩ : syracuseStep 783975 = 1175963) B1175963
theorem B1177415 : Blo 782338 1177415 := bstep (se 1 (by rfl) ⟨883061, by rfl⟩ : syracuseStep 1177415 = 1766123) B1766123
theorem B1767239 : Blo 782338 1767239 := bstep (se 1 (by rfl) ⟨1325429, by rfl⟩ : syracuseStep 1767239 = 2650859) B2650859
theorem B784255 : Blo 782338 784255 := bstep (se 1 (by rfl) ⟨588191, by rfl⟩ : syracuseStep 784255 = 1176383) B1176383
theorem B784351 : Blo 782338 784351 := bstep (se 1 (by rfl) ⟨588263, by rfl⟩ : syracuseStep 784351 = 1176527) B1176527
theorem B784379 : Blo 782338 784379 := bstep (se 1 (by rfl) ⟨588284, by rfl⟩ : syracuseStep 784379 = 1176569) B1176569
theorem B1177595 : Blo 782338 1177595 := bstep (se 1 (by rfl) ⟨883196, by rfl⟩ : syracuseStep 1177595 = 1766393) B1766393
theorem B1767419 : Blo 782338 1767419 := bstep (se 1 (by rfl) ⟨1325564, by rfl⟩ : syracuseStep 1767419 = 2651129) B2651129
theorem B784411 : Blo 782338 784411 := bstep (se 1 (by rfl) ⟨588308, by rfl⟩ : syracuseStep 784411 = 1176617) B1176617
theorem B882715 : Blo 782338 882715 := bstep (se 1 (by rfl) ⟨662036, by rfl⟩ : syracuseStep 882715 = 1324073) B1324073
theorem B784431 : Blo 782338 784431 := bstep (se 1 (by rfl) ⟨588323, by rfl⟩ : syracuseStep 784431 = 1176647) B1176647
theorem B1177655 : Blo 782338 1177655 := bstep (se 1 (by rfl) ⟨883241, by rfl⟩ : syracuseStep 1177655 = 1766483) B1766483
theorem B24115265 : Blo 782338 24115265 := bstep (se 2 (by rfl) ⟨9043224, by rfl⟩ : syracuseStep 24115265 = 18086449) B18086449
theorem B1177721 : Blo 782338 1177721 := bstep (se 2 (by rfl) ⟨441645, by rfl⟩ : syracuseStep 1177721 = 883291) B883291
theorem B1767545 : Blo 782338 1767545 := bstep (se 2 (by rfl) ⟨662829, by rfl⟩ : syracuseStep 1767545 = 1325659) B1325659
theorem B784551 : Blo 782338 784551 := bstep (se 1 (by rfl) ⟨588413, by rfl⟩ : syracuseStep 784551 = 1176827) B1176827
theorem B1767599 : Blo 782338 1767599 := bstep (se 1 (by rfl) ⟨1325699, by rfl⟩ : syracuseStep 1767599 = 2651399) B2651399
theorem B1177775 : Blo 782338 1177775 := bstep (se 1 (by rfl) ⟨883331, by rfl⟩ : syracuseStep 1177775 = 1766663) B1766663
theorem B1178015 : Blo 782338 1178015 := bstep (se 1 (by rfl) ⟨883511, by rfl⟩ : syracuseStep 1178015 = 1767023) B1767023
theorem B1178105 : Blo 782338 1178105 := bstep (se 2 (by rfl) ⟨441789, by rfl⟩ : syracuseStep 1178105 = 883579) B883579
theorem B3177103 : Blo 782338 3177103 := bstep (se 1 (by rfl) ⟨2382827, by rfl⟩ : syracuseStep 3177103 = 4765655) B4765655
theorem B1768247 : Blo 782338 1768247 := bstep (se 1 (by rfl) ⟨1326185, by rfl⟩ : syracuseStep 1768247 = 2652371) B2652371
theorem B3963815 : Blo 782338 3963815 := bstep (se 1 (by rfl) ⟨2972861, by rfl⟩ : syracuseStep 3963815 = 5945723) B5945723
theorem B785375 : Blo 782338 785375 := bstep (se 1 (by rfl) ⟨589031, by rfl⟩ : syracuseStep 785375 = 1178063) B1178063
theorem B1178591 : Blo 782338 1178591 := bstep (se 1 (by rfl) ⟨883943, by rfl⟩ : syracuseStep 1178591 = 1767887) B1767887
theorem B1768427 : Blo 782338 1768427 := bstep (se 1 (by rfl) ⟨1326320, by rfl⟩ : syracuseStep 1768427 = 2652641) B2652641
theorem B785435 : Blo 782338 785435 := bstep (se 1 (by rfl) ⟨589076, by rfl⟩ : syracuseStep 785435 = 1178153) B1178153
theorem B1178651 : Blo 782338 1178651 := bstep (se 1 (by rfl) ⟨883988, by rfl⟩ : syracuseStep 1178651 = 1767977) B1767977
theorem B785563 : Blo 782338 785563 := bstep (se 1 (by rfl) ⟨589172, by rfl⟩ : syracuseStep 785563 = 1178345) B1178345
theorem B883867 : Blo 782338 883867 := bstep (se 1 (by rfl) ⟨662900, by rfl⟩ : syracuseStep 883867 = 1325801) B1325801
theorem B2981063 : Blo 782338 2981063 := bstep (se 1 (by rfl) ⟨2235797, by rfl⟩ : syracuseStep 2981063 = 4471595) B4471595
theorem B1637651 : Blo 782338 1637651 := bstep (se 1 (by rfl) ⟨1228238, by rfl⟩ : syracuseStep 1637651 = 2456477) B2456477
theorem B22609205 : Blo 782338 22609205 := bstep (se 5 (by rfl) ⟨1059806, by rfl⟩ : syracuseStep 22609205 = 2119613) B2119613
theorem B785819 : Blo 782338 785819 := bstep (se 1 (by rfl) ⟨589364, by rfl⟩ : syracuseStep 785819 = 1178729) B1178729
theorem B1179035 : Blo 782338 1179035 := bstep (se 1 (by rfl) ⟨884276, by rfl⟩ : syracuseStep 1179035 = 1768553) B1768553
theorem B1179113 : Blo 782338 1179113 := bstep (se 2 (by rfl) ⟨442167, by rfl⟩ : syracuseStep 1179113 = 884335) B884335
theorem B785903 : Blo 782338 785903 := bstep (se 1 (by rfl) ⟨589427, by rfl⟩ : syracuseStep 785903 = 1178855) B1178855
theorem B1179119 : Blo 782338 1179119 := bstep (se 1 (by rfl) ⟨884339, by rfl⟩ : syracuseStep 1179119 = 1768679) B1768679
theorem B1179257 : Blo 782338 1179257 := bstep (se 2 (by rfl) ⟨442221, by rfl⟩ : syracuseStep 1179257 = 884443) B884443
theorem B786239 : Blo 782338 786239 := bstep (se 1 (by rfl) ⟨589679, by rfl⟩ : syracuseStep 786239 = 1179359) B1179359
theorem B1179455 : Blo 782338 1179455 := bstep (se 1 (by rfl) ⟨884591, by rfl⟩ : syracuseStep 1179455 = 1769183) B1769183
theorem B786267 : Blo 782338 786267 := bstep (se 1 (by rfl) ⟨589700, by rfl⟩ : syracuseStep 786267 = 1179401) B1179401
theorem B1179503 : Blo 782338 1179503 := bstep (se 1 (by rfl) ⟨884627, by rfl⟩ : syracuseStep 1179503 = 1769255) B1769255
theorem B3342815 : Blo 782338 3342815 := bstep (se 1 (by rfl) ⟨2507111, by rfl⟩ : syracuseStep 3342815 = 5014223) B5014223
theorem B2819693 : Blo 782338 2819693 := bstep (se 3 (by rfl) ⟨528692, by rfl⟩ : syracuseStep 2819693 = 1057385) B1057385
theorem B3966731 : Blo 782338 3966731 := bstep (se 1 (by rfl) ⟨2975048, by rfl⟩ : syracuseStep 3966731 = 5950097) B5950097
theorem B5375783 : Blo 782338 5375783 := bstep (se 1 (by rfl) ⟨4031837, by rfl⟩ : syracuseStep 5375783 = 8063675) B8063675
theorem B22087709 : Blo 782338 22087709 := bstep (se 3 (by rfl) ⟨4141445, by rfl⟩ : syracuseStep 22087709 = 8282891) B8282891
theorem B5015783 : Blo 782338 5015783 := bstep (se 1 (by rfl) ⟨3761837, by rfl⟩ : syracuseStep 5015783 = 7523675) B7523675
theorem B3344915 : Blo 782338 3344915 := bstep (se 1 (by rfl) ⟨2508686, by rfl⟩ : syracuseStep 3344915 = 5017373) B5017373
theorem B2231003 : Blo 782338 2231003 := bstep (se 1 (by rfl) ⟨1673252, by rfl⟩ : syracuseStep 2231003 = 3346505) B3346505
theorem B12749663 : Blo 782338 12749663 := bstep (se 1 (by rfl) ⟨9562247, by rfl⟩ : syracuseStep 12749663 = 19124495) B19124495
theorem B12094829 : Blo 782338 12094829 := bstep (se 3 (by rfl) ⟨2267780, by rfl⟩ : syracuseStep 12094829 = 4535561) B4535561
theorem B5017115 : Blo 782338 5017115 := bstep (se 1 (by rfl) ⟨3762836, by rfl⟩ : syracuseStep 5017115 = 7525673) B7525673
theorem B3968999 : Blo 782338 3968999 := bstep (se 1 (by rfl) ⟨2976749, by rfl⟩ : syracuseStep 3968999 = 5953499) B5953499
theorem B2232859 : Blo 782338 2232859 := bstep (se 1 (by rfl) ⟨1674644, by rfl⟩ : syracuseStep 2232859 = 3349289) B3349289
theorem B4232027 : Blo 782338 4232027 := bstep (se 1 (by rfl) ⟨3174020, by rfl⟩ : syracuseStep 4232027 = 6348041) B6348041
theorem B4461641 : Blo 782338 4461641 := bstep (se 2 (by rfl) ⟨1673115, by rfl⟩ : syracuseStep 4461641 = 3346231) B3346231
theorem B5969051 : Blo 782338 5969051 := bstep (se 1 (by rfl) ⟨4476788, by rfl⟩ : syracuseStep 5969051 = 8953577) B8953577
theorem B3349117 : Blo 782338 3349117 := bstep (se 3 (by rfl) ⟨627959, by rfl⟩ : syracuseStep 3349117 = 1255919) B1255919
theorem B10755119 : Blo 782338 10755119 := bstep (se 1 (by rfl) ⟨8066339, by rfl⟩ : syracuseStep 10755119 = 16132679) B16132679
theorem B3972239 : Blo 782338 3972239 := bstep (se 1 (by rfl) ⟨2979179, by rfl⟩ : syracuseStep 3972239 = 5958359) B5958359
theorem B11443463 : Blo 782338 11443463 := bstep (se 1 (by rfl) ⟨8582597, by rfl⟩ : syracuseStep 11443463 = 17165195) B17165195
theorem B8592767 : Blo 782338 8592767 := bstep (se 1 (by rfl) ⟨6444575, by rfl⟩ : syracuseStep 8592767 = 12889151) B12889151
theorem B11312621 : Blo 782338 11312621 := bstep (se 3 (by rfl) ⟨2121116, by rfl⟩ : syracuseStep 11312621 = 4242233) B4242233
theorem B4235095 : Blo 782338 4235095 := bstep (se 1 (by rfl) ⟨3176321, by rfl⟩ : syracuseStep 4235095 = 6352643) B6352643
theorem B4236137 : Blo 782338 4236137 := bstep (se 2 (by rfl) ⟨1588551, by rfl⟩ : syracuseStep 4236137 = 3177103) B3177103
theorem B6694271 : Blo 782338 6694271 := bstep (se 1 (by rfl) ⟨5020703, by rfl⟩ : syracuseStep 6694271 = 10041407) B10041407
theorem B54208349 : Blo 782338 54208349 := bstep (se 3 (by rfl) ⟨10164065, by rfl⟩ : syracuseStep 54208349 = 20328131) B20328131
theorem B3352535 : Blo 782338 3352535 := bstep (se 1 (by rfl) ⟨2514401, by rfl⟩ : syracuseStep 3352535 = 5028803) B5028803
theorem B1091767 : Blo 782338 1091767 := bstep (se 1 (by rfl) ⟨818825, by rfl⟩ : syracuseStep 1091767 = 1637651) B1637651
theorem B4532699 : Blo 782338 4532699 := bstep (se 1 (by rfl) ⟨3399524, by rfl⟩ : syracuseStep 4532699 = 6799049) B6799049
theorem B25504247 : Blo 782338 25504247 := bstep (se 1 (by rfl) ⟨19128185, by rfl⟩ : syracuseStep 25504247 = 38256371) B38256371
theorem B8039735 : Blo 782338 8039735 := bstep (se 1 (by rfl) ⟨6029801, by rfl⟩ : syracuseStep 8039735 = 12059603) B12059603
theorem B1322473 : Blo 782338 1322473 := bstep (se 2 (by rfl) ⟨495927, by rfl⟩ : syracuseStep 1322473 = 991855) B991855
theorem B1322527 : Blo 782338 1322527 := bstep (se 1 (by rfl) ⟨991895, by rfl⟩ : syracuseStep 1322527 = 1983791) B1983791
theorem B10727099 : Blo 782338 10727099 := bstep (se 1 (by rfl) ⟨8045324, by rfl⟩ : syracuseStep 10727099 = 16090649) B16090649
theorem B165228329 : Blo 782338 165228329 := bstep (se 2 (by rfl) ⟨61960623, by rfl⟩ : syracuseStep 165228329 = 123921247) B123921247
theorem B42840049 : Blo 782338 42840049 := bstep (se 2 (by rfl) ⟨16065018, by rfl⟩ : syracuseStep 42840049 = 32130037) B32130037
theorem B24785189 : Blo 782338 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B1323499 : Blo 782338 1323499 := bstep (se 1 (by rfl) ⟨992624, by rfl⟩ : syracuseStep 1323499 = 1985249) B1985249
theorem B4469363 : Blo 782338 4469363 := bstep (se 1 (by rfl) ⟨3352022, by rfl⟩ : syracuseStep 4469363 = 6704045) B6704045
theorem B2831123 : Blo 782338 2831123 := bstep (se 1 (by rfl) ⟨2123342, by rfl⟩ : syracuseStep 2831123 = 4246685) B4246685
theorem B3978233 : Blo 782338 3978233 := bstep (se 2 (by rfl) ⟨1491837, by rfl⟩ : syracuseStep 3978233 = 2983675) B2983675
theorem B1324127 : Blo 782338 1324127 := bstep (se 1 (by rfl) ⟨993095, by rfl⟩ : syracuseStep 1324127 = 1986191) B1986191
theorem B1324991 : Blo 782338 1324991 := bstep (se 1 (by rfl) ⟨993743, by rfl⟩ : syracuseStep 1324991 = 1987487) B1987487
theorem B10074415 : Blo 782338 10074415 := bstep (se 1 (by rfl) ⟨7555811, by rfl⟩ : syracuseStep 10074415 = 15111623) B15111623
theorem B1489279 : Blo 782338 1489279 := bstep (se 1 (by rfl) ⟨1116959, by rfl⟩ : syracuseStep 1489279 = 2233919) B2233919
theorem B4766141 : Blo 782338 4766141 := bstep (se 3 (by rfl) ⟨893651, by rfl⟩ : syracuseStep 4766141 = 1787303) B1787303
theorem B20102903 : Blo 782338 20102903 := bstep (se 1 (by rfl) ⟨15077177, by rfl⟩ : syracuseStep 20102903 = 30154355) B30154355
theorem B2506535 : Blo 782338 2506535 := bstep (se 1 (by rfl) ⟨1879901, by rfl⟩ : syracuseStep 2506535 = 3759803) B3759803
theorem B5357963 : Blo 782338 5357963 := bstep (se 1 (by rfl) ⟨4018472, by rfl⟩ : syracuseStep 5357963 = 8036945) B8036945
theorem B4473737 : Blo 782338 4473737 := bstep (se 2 (by rfl) ⟨1677651, by rfl⟩ : syracuseStep 4473737 = 3355303) B3355303
theorem B13419431 : Blo 782338 13419431 := bstep (se 1 (by rfl) ⟨10064573, by rfl⟩ : syracuseStep 13419431 = 20129147) B20129147
theorem B5720539 : Blo 782338 5720539 := bstep (se 1 (by rfl) ⟨4290404, by rfl⟩ : syracuseStep 5720539 = 8580809) B8580809
theorem B4771295 : Blo 782338 4771295 := bstep (se 1 (by rfl) ⟨3578471, by rfl⟩ : syracuseStep 4771295 = 7156943) B7156943
theorem B16076843 : Blo 782338 16076843 := bstep (se 1 (by rfl) ⟨12057632, by rfl⟩ : syracuseStep 16076843 = 24115265) B24115265
theorem B4771975 : Blo 782338 4771975 := bstep (se 1 (by rfl) ⟨3578981, by rfl⟩ : syracuseStep 4771975 = 7157963) B7157963
theorem B4248071 : Blo 782338 4248071 := bstep (se 1 (by rfl) ⟨3186053, by rfl⟩ : syracuseStep 4248071 = 6372107) B6372107
theorem B2642543 : Blo 782338 2642543 := bstep (se 1 (by rfl) ⟨1981907, by rfl⟩ : syracuseStep 2642543 = 3963815) B3963815
theorem B1987375 : Blo 782338 1987375 := bstep (se 1 (by rfl) ⟨1490531, by rfl⟩ : syracuseStep 1987375 = 2981063) B2981063
theorem B13423805 : Blo 782338 13423805 := bstep (se 3 (by rfl) ⟨2516963, by rfl⟩ : syracuseStep 13423805 = 5033927) B5033927
theorem B3396889 : Blo 782338 3396889 := bstep (se 2 (by rfl) ⟨1273833, by rfl⟩ : syracuseStep 3396889 = 2547667) B2547667
theorem B1988023 : Blo 782338 1988023 := bstep (se 1 (by rfl) ⟨1491017, by rfl⟩ : syracuseStep 1988023 = 2982035) B2982035
theorem B2512403 : Blo 782338 2512403 := bstep (se 1 (by rfl) ⟨1884302, by rfl⟩ : syracuseStep 2512403 = 3768605) B3768605
theorem B5658761 : Blo 782338 5658761 := bstep (se 2 (by rfl) ⟨2122035, by rfl⟩ : syracuseStep 5658761 = 4244071) B4244071
theorem B2972801 : Blo 782338 2972801 := bstep (se 2 (by rfl) ⟨1114800, by rfl⟩ : syracuseStep 2972801 = 2229601) B2229601
theorem B13393187 : Blo 782338 13393187 := bstep (se 1 (by rfl) ⟨10044890, by rfl⟩ : syracuseStep 13393187 = 20089781) B20089781
theorem B2972983 : Blo 782338 2972983 := bstep (se 1 (by rfl) ⟨2229737, by rfl⟩ : syracuseStep 2972983 = 4459475) B4459475
theorem B1760831 : Blo 782338 1760831 := bstep (se 1 (by rfl) ⟨1320623, by rfl⟩ : syracuseStep 1760831 = 2641247) B2641247
theorem B1761191 : Blo 782338 1761191 := bstep (se 1 (by rfl) ⟨1320893, by rfl⟩ : syracuseStep 1761191 = 2641787) B2641787
theorem B1761479 : Blo 782338 1761479 := bstep (se 1 (by rfl) ⟨1321109, by rfl⟩ : syracuseStep 1761479 = 2642219) B2642219
theorem B2646269 : Blo 782338 2646269 := bstep (se 3 (by rfl) ⟨496175, by rfl⟩ : syracuseStep 2646269 = 992351) B992351
theorem B219832865 : Blo 782338 219832865 := bstep (se 2 (by rfl) ⟨82437324, by rfl⟩ : syracuseStep 219832865 = 164874649) B164874649
theorem B9528191 : Blo 782338 9528191 := bstep (se 1 (by rfl) ⟨7146143, by rfl⟩ : syracuseStep 9528191 = 14292287) B14292287
theorem B2975201 : Blo 782338 2975201 := bstep (se 2 (by rfl) ⟨1115700, by rfl⟩ : syracuseStep 2975201 = 2231401) B2231401
theorem B1762811 : Blo 782338 1762811 := bstep (se 1 (by rfl) ⟨1322108, by rfl⟩ : syracuseStep 1762811 = 2644217) B2644217
theorem B13985329 : Blo 782338 13985329 := bstep (se 2 (by rfl) ⟨5244498, by rfl⟩ : syracuseStep 13985329 = 10488997) B10488997
theorem B1762919 : Blo 782338 1762919 := bstep (se 1 (by rfl) ⟨1322189, by rfl⟩ : syracuseStep 1762919 = 2644379) B2644379
theorem B1697545 : Blo 782338 1697545 := bstep (se 2 (by rfl) ⟨636579, by rfl⟩ : syracuseStep 1697545 = 1273159) B1273159
theorem B2647997 : Blo 782338 2647997 := bstep (se 3 (by rfl) ⟨496499, by rfl⟩ : syracuseStep 2647997 = 992999) B992999
theorem B1173575 : Blo 782338 1173575 := bstep (se 1 (by rfl) ⟨880181, by rfl⟩ : syracuseStep 1173575 = 1760363) B1760363
theorem B2975899 : Blo 782338 2975899 := bstep (se 1 (by rfl) ⟨2231924, by rfl⟩ : syracuseStep 2975899 = 4463849) B4463849
theorem B1173671 : Blo 782338 1173671 := bstep (se 1 (by rfl) ⟨880253, by rfl⟩ : syracuseStep 1173671 = 1760507) B1760507
theorem B1173755 : Blo 782338 1173755 := bstep (se 1 (by rfl) ⟨880316, by rfl⟩ : syracuseStep 1173755 = 1760633) B1760633
theorem B6351151 : Blo 782338 6351151 := bstep (se 1 (by rfl) ⟨4763363, by rfl⟩ : syracuseStep 6351151 = 9526727) B9526727
theorem B2648375 : Blo 782338 2648375 := bstep (se 1 (by rfl) ⟨1986281, by rfl⟩ : syracuseStep 2648375 = 3972563) B3972563
theorem B2976371 : Blo 782338 2976371 := bstep (se 1 (by rfl) ⟨2232278, by rfl⟩ : syracuseStep 2976371 = 4464557) B4464557
theorem B1174175 : Blo 782338 1174175 := bstep (se 1 (by rfl) ⟨880631, by rfl⟩ : syracuseStep 1174175 = 1761263) B1761263
theorem B1174343 : Blo 782338 1174343 := bstep (se 1 (by rfl) ⟨880757, by rfl⟩ : syracuseStep 1174343 = 1761515) B1761515
theorem B2649401 : Blo 782338 2649401 := bstep (se 2 (by rfl) ⟨993525, by rfl⟩ : syracuseStep 2649401 = 1987051) B1987051
theorem B2518399 : Blo 782338 2518399 := bstep (se 1 (by rfl) ⟨1888799, by rfl⟩ : syracuseStep 2518399 = 3777599) B3777599
theorem B1174943 : Blo 782338 1174943 := bstep (se 1 (by rfl) ⟨881207, by rfl⟩ : syracuseStep 1174943 = 1762415) B1762415
theorem B1175615 : Blo 782338 1175615 := bstep (se 1 (by rfl) ⟨881711, by rfl⟩ : syracuseStep 1175615 = 1763423) B1763423
theorem B782427 : Blo 782338 782427 := bstep (se 1 (by rfl) ⟨586820, by rfl⟩ : syracuseStep 782427 = 1173641) B1173641
theorem B782527 : Blo 782338 782527 := bstep (se 1 (by rfl) ⟨586895, by rfl⟩ : syracuseStep 782527 = 1173791) B1173791
theorem B6713543 : Blo 782338 6713543 := bstep (se 1 (by rfl) ⟨5035157, by rfl⟩ : syracuseStep 6713543 = 10070315) B10070315
theorem B782559 : Blo 782338 782559 := bstep (se 1 (by rfl) ⟨586919, by rfl⟩ : syracuseStep 782559 = 1173839) B1173839
theorem B12742919 : Blo 782338 12742919 := bstep (se 1 (by rfl) ⟨9557189, by rfl⟩ : syracuseStep 12742919 = 19114379) B19114379
theorem B782619 : Blo 782338 782619 := bstep (se 1 (by rfl) ⟨586964, by rfl⟩ : syracuseStep 782619 = 1173929) B1173929
theorem B782875 : Blo 782338 782875 := bstep (se 1 (by rfl) ⟨587156, by rfl⟩ : syracuseStep 782875 = 1174313) B1174313
theorem B783015 : Blo 782338 783015 := bstep (se 1 (by rfl) ⟨587261, by rfl⟩ : syracuseStep 783015 = 1174523) B1174523
theorem B783055 : Blo 782338 783055 := bstep (se 1 (by rfl) ⟨587291, by rfl⟩ : syracuseStep 783055 = 1174583) B1174583
theorem B3764989 : Blo 782338 3764989 := bstep (se 3 (by rfl) ⟨705935, by rfl⟩ : syracuseStep 3764989 = 1411871) B1411871
theorem B783135 : Blo 782338 783135 := bstep (se 1 (by rfl) ⟨587351, by rfl⟩ : syracuseStep 783135 = 1174703) B1174703
theorem B783175 : Blo 782338 783175 := bstep (se 1 (by rfl) ⟨587381, by rfl⟩ : syracuseStep 783175 = 1174763) B1174763
theorem B1274783 : Blo 782338 1274783 := bstep (se 1 (by rfl) ⟨956087, by rfl⟩ : syracuseStep 1274783 = 1912175) B1912175
theorem B881599 : Blo 782338 881599 := bstep (se 1 (by rfl) ⟨661199, by rfl⟩ : syracuseStep 881599 = 1322399) B1322399
theorem B783615 : Blo 782338 783615 := bstep (se 1 (by rfl) ⟨587711, by rfl⟩ : syracuseStep 783615 = 1175423) B1175423
theorem B1176911 : Blo 782338 1176911 := bstep (se 1 (by rfl) ⟨882683, by rfl⟩ : syracuseStep 1176911 = 1765367) B1765367
theorem B1176953 : Blo 782338 1176953 := bstep (se 2 (by rfl) ⟨441357, by rfl⟩ : syracuseStep 1176953 = 882715) B882715
theorem B1766825 : Blo 782338 1766825 := bstep (se 2 (by rfl) ⟨662559, by rfl⟩ : syracuseStep 1766825 = 1325119) B1325119
theorem B783839 : Blo 782338 783839 := bstep (se 1 (by rfl) ⟨587879, by rfl⟩ : syracuseStep 783839 = 1175759) B1175759
theorem B1766879 : Blo 782338 1766879 := bstep (se 1 (by rfl) ⟨1325159, by rfl⟩ : syracuseStep 1766879 = 2650319) B2650319
theorem B10057193 : Blo 782338 10057193 := bstep (se 2 (by rfl) ⟨3771447, by rfl⟩ : syracuseStep 10057193 = 7542895) B7542895
theorem B6780449 : Blo 782338 6780449 := bstep (se 2 (by rfl) ⟨2542668, by rfl⟩ : syracuseStep 6780449 = 5085337) B5085337
theorem B783919 : Blo 782338 783919 := bstep (se 1 (by rfl) ⟨587939, by rfl⟩ : syracuseStep 783919 = 1175879) B1175879
theorem B1177151 : Blo 782338 1177151 := bstep (se 1 (by rfl) ⟨882863, by rfl⟩ : syracuseStep 1177151 = 1765727) B1765727
theorem B784231 : Blo 782338 784231 := bstep (se 1 (by rfl) ⟨588173, by rfl⟩ : syracuseStep 784231 = 1176347) B1176347
theorem B1177499 : Blo 782338 1177499 := bstep (se 1 (by rfl) ⟨883124, by rfl⟩ : syracuseStep 1177499 = 1766249) B1766249
theorem B2979773 : Blo 782338 2979773 := bstep (se 3 (by rfl) ⟨558707, by rfl⟩ : syracuseStep 2979773 = 1117415) B1117415
theorem B784415 : Blo 782338 784415 := bstep (se 1 (by rfl) ⟨588311, by rfl⟩ : syracuseStep 784415 = 1176623) B1176623
theorem B1177631 : Blo 782338 1177631 := bstep (se 1 (by rfl) ⟨883223, by rfl⟩ : syracuseStep 1177631 = 1766447) B1766447
theorem B784447 : Blo 782338 784447 := bstep (se 1 (by rfl) ⟨588335, by rfl⟩ : syracuseStep 784447 = 1176671) B1176671
theorem B784487 : Blo 782338 784487 := bstep (se 1 (by rfl) ⟨588365, by rfl⟩ : syracuseStep 784487 = 1176731) B1176731
theorem B1767527 : Blo 782338 1767527 := bstep (se 1 (by rfl) ⟨1325645, by rfl⟩ : syracuseStep 1767527 = 2651291) B2651291
theorem B784495 : Blo 782338 784495 := bstep (se 1 (by rfl) ⟨588371, by rfl⟩ : syracuseStep 784495 = 1176743) B1176743
theorem B3963005 : Blo 782338 3963005 := bstep (se 3 (by rfl) ⟨743063, by rfl⟩ : syracuseStep 3963005 = 1486127) B1486127
theorem B2980091 : Blo 782338 2980091 := bstep (se 1 (by rfl) ⟨2235068, by rfl⟩ : syracuseStep 2980091 = 4470137) B4470137
theorem B3963167 : Blo 782338 3963167 := bstep (se 1 (by rfl) ⟨2972375, by rfl⟩ : syracuseStep 3963167 = 5944751) B5944751
theorem B2718031 : Blo 782338 2718031 := bstep (se 1 (by rfl) ⟨2038523, by rfl⟩ : syracuseStep 2718031 = 4077047) B4077047
theorem B3766607 : Blo 782338 3766607 := bstep (se 1 (by rfl) ⟨2824955, by rfl⟩ : syracuseStep 3766607 = 5649911) B5649911
theorem B784943 : Blo 782338 784943 := bstep (se 1 (by rfl) ⟨588707, by rfl⟩ : syracuseStep 784943 = 1177415) B1177415
theorem B1178159 : Blo 782338 1178159 := bstep (se 1 (by rfl) ⟨883619, by rfl⟩ : syracuseStep 1178159 = 1767239) B1767239
theorem B785063 : Blo 782338 785063 := bstep (se 1 (by rfl) ⟨588797, by rfl⟩ : syracuseStep 785063 = 1177595) B1177595
theorem B1178279 : Blo 782338 1178279 := bstep (se 1 (by rfl) ⟨883709, by rfl⟩ : syracuseStep 1178279 = 1767419) B1767419
theorem B785103 : Blo 782338 785103 := bstep (se 1 (by rfl) ⟨588827, by rfl⟩ : syracuseStep 785103 = 1177655) B1177655
theorem B785147 : Blo 782338 785147 := bstep (se 1 (by rfl) ⟨588860, by rfl⟩ : syracuseStep 785147 = 1177721) B1177721
theorem B1178363 : Blo 782338 1178363 := bstep (se 1 (by rfl) ⟨883772, by rfl⟩ : syracuseStep 1178363 = 1767545) B1767545
theorem B785183 : Blo 782338 785183 := bstep (se 1 (by rfl) ⟨588887, by rfl⟩ : syracuseStep 785183 = 1177775) B1177775
theorem B1178399 : Blo 782338 1178399 := bstep (se 1 (by rfl) ⟨883799, by rfl⟩ : syracuseStep 1178399 = 1767599) B1767599
theorem B1178489 : Blo 782338 1178489 := bstep (se 2 (by rfl) ⟨441933, by rfl⟩ : syracuseStep 1178489 = 883867) B883867
theorem B785343 : Blo 782338 785343 := bstep (se 1 (by rfl) ⟨589007, by rfl⟩ : syracuseStep 785343 = 1178015) B1178015
theorem B5962733 : Blo 782338 5962733 := bstep (se 3 (by rfl) ⟨1118012, by rfl⟩ : syracuseStep 5962733 = 2236025) B2236025
theorem B785403 : Blo 782338 785403 := bstep (se 1 (by rfl) ⟨589052, by rfl⟩ : syracuseStep 785403 = 1178105) B1178105
theorem B16972897 : Blo 782338 16972897 := bstep (se 2 (by rfl) ⟨6364836, by rfl⟩ : syracuseStep 16972897 = 12729673) B12729673
theorem B2653289 : Blo 782338 2653289 := bstep (se 2 (by rfl) ⟨994983, by rfl⟩ : syracuseStep 2653289 = 1989967) B1989967
theorem B1178831 : Blo 782338 1178831 := bstep (se 1 (by rfl) ⟨884123, by rfl⟩ : syracuseStep 1178831 = 1768247) B1768247
theorem B785727 : Blo 782338 785727 := bstep (se 1 (by rfl) ⟨589295, by rfl⟩ : syracuseStep 785727 = 1178591) B1178591
theorem B1178951 : Blo 782338 1178951 := bstep (se 1 (by rfl) ⟨884213, by rfl⟩ : syracuseStep 1178951 = 1768427) B1768427
theorem B785767 : Blo 782338 785767 := bstep (se 1 (by rfl) ⟨589325, by rfl⟩ : syracuseStep 785767 = 1178651) B1178651
theorem B884191 : Blo 782338 884191 := bstep (se 1 (by rfl) ⟨663143, by rfl⟩ : syracuseStep 884191 = 1326287) B1326287
theorem B15072803 : Blo 782338 15072803 := bstep (se 1 (by rfl) ⟨11304602, by rfl⟩ : syracuseStep 15072803 = 22609205) B22609205
theorem B786023 : Blo 782338 786023 := bstep (se 1 (by rfl) ⟨589517, by rfl⟩ : syracuseStep 786023 = 1179035) B1179035
theorem B786075 : Blo 782338 786075 := bstep (se 1 (by rfl) ⟨589556, by rfl⟩ : syracuseStep 786075 = 1179113) B1179113
theorem B786079 : Blo 782338 786079 := bstep (se 1 (by rfl) ⟨589559, by rfl⟩ : syracuseStep 786079 = 1179119) B1179119
theorem B786171 : Blo 782338 786171 := bstep (se 1 (by rfl) ⟨589628, by rfl⟩ : syracuseStep 786171 = 1179257) B1179257
theorem B19038077 : Blo 782338 19038077 := bstep (se 3 (by rfl) ⟨3569639, by rfl⟩ : syracuseStep 19038077 = 7139279) B7139279
theorem B786303 : Blo 782338 786303 := bstep (se 1 (by rfl) ⟨589727, by rfl⟩ : syracuseStep 786303 = 1179455) B1179455
theorem B10059653 : Blo 782338 10059653 := bstep (se 4 (by rfl) ⟨943092, by rfl⟩ : syracuseStep 10059653 = 1886185) B1886185
theorem B786335 : Blo 782338 786335 := bstep (se 1 (by rfl) ⟨589751, by rfl⟩ : syracuseStep 786335 = 1179503) B1179503
theorem B3571975 : Blo 782338 3571975 := bstep (se 1 (by rfl) ⟨2678981, by rfl⟩ : syracuseStep 3571975 = 5357963) B5357963
theorem B235602229 : Blo 782338 235602229 := bstep (se 5 (by rfl) ⟨11043854, by rfl⟩ : syracuseStep 235602229 = 22087709) B22087709
theorem B2228543 : Blo 782338 2228543 := bstep (se 1 (by rfl) ⟨1671407, by rfl⟩ : syracuseStep 2228543 = 3342815) B3342815
theorem B2982491 : Blo 782338 2982491 := bstep (se 1 (by rfl) ⟨2236868, by rfl⟩ : syracuseStep 2982491 = 4473737) B4473737
theorem B8946287 : Blo 782338 8946287 := bstep (se 1 (by rfl) ⟨6709715, by rfl⟩ : syracuseStep 8946287 = 13419431) B13419431
theorem B3343855 : Blo 782338 3343855 := bstep (se 1 (by rfl) ⟨2507891, by rfl⟩ : syracuseStep 3343855 = 5015783) B5015783
theorem B2229943 : Blo 782338 2229943 := bstep (se 1 (by rfl) ⟨1672457, by rfl⟩ : syracuseStep 2229943 = 3344915) B3344915
theorem B18647105 : Blo 782338 18647105 := bstep (se 2 (by rfl) ⟨6992664, by rfl⟩ : syracuseStep 18647105 = 13985329) B13985329
theorem B8063219 : Blo 782338 8063219 := bstep (se 1 (by rfl) ⟨6047414, by rfl⟩ : syracuseStep 8063219 = 12094829) B12094829
theorem B3180863 : Blo 782338 3180863 := bstep (se 1 (by rfl) ⟨2385647, by rfl⟩ : syracuseStep 3180863 = 4771295) B4771295
theorem B2263393 : Blo 782338 2263393 := bstep (se 2 (by rfl) ⟨848772, by rfl⟩ : syracuseStep 2263393 = 1697545) B1697545
theorem B3344743 : Blo 782338 3344743 := bstep (se 1 (by rfl) ⟨2508557, by rfl⟩ : syracuseStep 3344743 = 5017115) B5017115
theorem B10717895 : Blo 782338 10717895 := bstep (se 1 (by rfl) ⟨8038421, by rfl⟩ : syracuseStep 10717895 = 16076843) B16076843
theorem B3967865 : Blo 782338 3967865 := bstep (se 2 (by rfl) ⟨1487949, by rfl⟩ : syracuseStep 3967865 = 2975899) B2975899
theorem B2821351 : Blo 782338 2821351 := bstep (se 1 (by rfl) ⟨2116013, by rfl⟩ : syracuseStep 2821351 = 4232027) B4232027
theorem B8949203 : Blo 782338 8949203 := bstep (se 1 (by rfl) ⟨6711902, by rfl⟩ : syracuseStep 8949203 = 13423805) B13423805
theorem B1674935 : Blo 782338 1674935 := bstep (se 1 (by rfl) ⟨1256201, by rfl⟩ : syracuseStep 1674935 = 2512403) B2512403
theorem B3772507 : Blo 782338 3772507 := bstep (se 1 (by rfl) ⟨2829380, by rfl⟩ : syracuseStep 3772507 = 5658761) B5658761
theorem B7541747 : Blo 782338 7541747 := bstep (se 1 (by rfl) ⟨5656310, by rfl⟩ : syracuseStep 7541747 = 11312621) B11312621
theorem B57120065 : Blo 782338 57120065 := bstep (se 2 (by rfl) ⟨21420024, by rfl⟩ : syracuseStep 57120065 = 42840049) B42840049
theorem B6362633 : Blo 782338 6362633 := bstep (se 2 (by rfl) ⟨2385987, by rfl⟩ : syracuseStep 6362633 = 4771975) B4771975
theorem B2824091 : Blo 782338 2824091 := bstep (se 1 (by rfl) ⟨2118068, by rfl⟩ : syracuseStep 2824091 = 4236137) B4236137
theorem B4462847 : Blo 782338 4462847 := bstep (se 1 (by rfl) ⟨3347135, by rfl⟩ : syracuseStep 4462847 = 6694271) B6694271
theorem B5019985 : Blo 782338 5019985 := bstep (se 2 (by rfl) ⟨1882494, by rfl⟩ : syracuseStep 5019985 = 3764989) B3764989
theorem B2235023 : Blo 782338 2235023 := bstep (se 1 (by rfl) ⟨1676267, by rfl⟩ : syracuseStep 2235023 = 3352535) B3352535
theorem B3021799 : Blo 782338 3021799 := bstep (se 1 (by rfl) ⟨2266349, by rfl⟩ : syracuseStep 3021799 = 4532699) B4532699
theorem B7151399 : Blo 782338 7151399 := bstep (se 1 (by rfl) ⟨5363549, by rfl⟩ : syracuseStep 7151399 = 10727099) B10727099
theorem B28680317 : Blo 782338 28680317 := bstep (se 3 (by rfl) ⟨5377559, by rfl⟩ : syracuseStep 28680317 = 10755119) B10755119
theorem B8495279 : Blo 782338 8495279 := bstep (se 1 (by rfl) ⟨6371459, by rfl⟩ : syracuseStep 8495279 = 12742919) B12742919
theorem B16523459 : Blo 782338 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B4465489 : Blo 782338 4465489 := bstep (se 2 (by rfl) ⟨1674558, by rfl⟩ : syracuseStep 4465489 = 3349117) B3349117
theorem B3975155 : Blo 782338 3975155 := bstep (se 1 (by rfl) ⟨2981366, by rfl⟩ : syracuseStep 3975155 = 5962733) B5962733
theorem B5646793 : Blo 782338 5646793 := bstep (se 2 (by rfl) ⟨2117547, by rfl⟩ : syracuseStep 5646793 = 4235095) B4235095
theorem B12692051 : Blo 782338 12692051 := bstep (se 1 (by rfl) ⟨9519038, by rfl⟩ : syracuseStep 12692051 = 19038077) B19038077
theorem B1879795 : Blo 782338 1879795 := bstep (se 1 (by rfl) ⟨1409846, by rfl⟩ : syracuseStep 1879795 = 2819693) B2819693
theorem B3583855 : Blo 782338 3583855 := bstep (se 1 (by rfl) ⟨2687891, by rfl⟩ : syracuseStep 3583855 = 5375783) B5375783
theorem B1487335 : Blo 782338 1487335 := bstep (se 1 (by rfl) ⟨1115501, by rfl⟩ : syracuseStep 1487335 = 2231003) B2231003
theorem B8499775 : Blo 782338 8499775 := bstep (se 1 (by rfl) ⟨6374831, by rfl⟩ : syracuseStep 8499775 = 12749663) B12749663
theorem B7549661 : Blo 782338 7549661 := bstep (se 3 (by rfl) ⟨1415561, by rfl⟩ : syracuseStep 7549661 = 2831123) B2831123
theorem B1455689 : Blo 782338 1455689 := bstep (se 2 (by rfl) ⟨545883, by rfl⟩ : syracuseStep 1455689 = 1091767) B1091767
theorem B2832047 : Blo 782338 2832047 := bstep (se 1 (by rfl) ⟨2124035, by rfl⟩ : syracuseStep 2832047 = 4248071) B4248071
theorem B8468201 : Blo 782338 8468201 := bstep (se 2 (by rfl) ⟨3175575, by rfl⟩ : syracuseStep 8468201 = 6351151) B6351151
theorem B3979367 : Blo 782338 3979367 := bstep (se 1 (by rfl) ⟨2984525, by rfl⟩ : syracuseStep 3979367 = 5969051) B5969051
theorem B3357865 : Blo 782338 3357865 := bstep (se 2 (by rfl) ⟨1259199, by rfl⟩ : syracuseStep 3357865 = 2518399) B2518399
theorem B1981867 : Blo 782338 1981867 := bstep (se 1 (by rfl) ⟨1486400, by rfl⟩ : syracuseStep 1981867 = 2972801) B2972801
theorem B8928791 : Blo 782338 8928791 := bstep (se 1 (by rfl) ⟨6696593, by rfl⟩ : syracuseStep 8928791 = 13393187) B13393187
theorem B146555243 : Blo 782338 146555243 := bstep (se 1 (by rfl) ⟨109916432, by rfl⟩ : syracuseStep 146555243 = 219832865) B219832865
theorem B1983467 : Blo 782338 1983467 := bstep (se 1 (by rfl) ⟨1487600, by rfl⟩ : syracuseStep 1983467 = 2975201) B2975201
theorem B1984247 : Blo 782338 1984247 := bstep (se 1 (by rfl) ⟨1488185, by rfl⟩ : syracuseStep 1984247 = 2976371) B2976371
theorem B5359823 : Blo 782338 5359823 := bstep (se 1 (by rfl) ⟨4019867, by rfl⟩ : syracuseStep 5359823 = 8039735) B8039735
theorem B110152219 : Blo 782338 110152219 := bstep (se 1 (by rfl) ⟨82614164, by rfl⟩ : syracuseStep 110152219 = 165228329) B165228329
theorem B4475695 : Blo 782338 4475695 := bstep (se 1 (by rfl) ⟨3356771, by rfl⟩ : syracuseStep 4475695 = 6713543) B6713543
theorem B3624041 : Blo 782338 3624041 := bstep (se 2 (by rfl) ⟨1359015, by rfl⟩ : syracuseStep 3624041 = 2718031) B2718031
theorem B1985705 : Blo 782338 1985705 := bstep (se 2 (by rfl) ⟨744639, by rfl⟩ : syracuseStep 1985705 = 1489279) B1489279
theorem B6704795 : Blo 782338 6704795 := bstep (se 1 (by rfl) ⟨5028596, by rfl⟩ : syracuseStep 6704795 = 10057193) B10057193
theorem B1986515 : Blo 782338 1986515 := bstep (se 1 (by rfl) ⟨1489886, by rfl⟩ : syracuseStep 1986515 = 2979773) B2979773
theorem B2642003 : Blo 782338 2642003 := bstep (se 1 (by rfl) ⟨1981502, by rfl⟩ : syracuseStep 2642003 = 3963005) B3963005
theorem B22630529 : Blo 782338 22630529 := bstep (se 2 (by rfl) ⟨8486448, by rfl⟩ : syracuseStep 22630529 = 16972897) B16972897
theorem B1986727 : Blo 782338 1986727 := bstep (se 1 (by rfl) ⟨1490045, by rfl⟩ : syracuseStep 1986727 = 2980091) B2980091
theorem B2642111 : Blo 782338 2642111 := bstep (se 1 (by rfl) ⟨1981583, by rfl⟩ : syracuseStep 2642111 = 3963167) B3963167
theorem B2511071 : Blo 782338 2511071 := bstep (se 1 (by rfl) ⟨1883303, by rfl⟩ : syracuseStep 2511071 = 3766607) B3766607
theorem B10048535 : Blo 782338 10048535 := bstep (se 1 (by rfl) ⟨7536401, by rfl⟩ : syracuseStep 10048535 = 15072803) B15072803
theorem B6706435 : Blo 782338 6706435 := bstep (se 1 (by rfl) ⟨5029826, by rfl⟩ : syracuseStep 6706435 = 10059653) B10059653
theorem B2644487 : Blo 782338 2644487 := bstep (se 1 (by rfl) ⟨1983365, by rfl⟩ : syracuseStep 2644487 = 3966731) B3966731
theorem B3399421 : Blo 782338 3399421 := bstep (se 3 (by rfl) ⟨637391, by rfl⟩ : syracuseStep 3399421 = 1274783) B1274783
theorem B2645999 : Blo 782338 2645999 := bstep (se 1 (by rfl) ⟨1984499, by rfl⟩ : syracuseStep 2645999 = 3968999) B3968999
theorem B1761695 : Blo 782338 1761695 := bstep (se 1 (by rfl) ⟨1321271, by rfl⟩ : syracuseStep 1761695 = 2642543) B2642543
theorem B7627385 : Blo 782338 7627385 := bstep (se 2 (by rfl) ⟨2860269, by rfl⟩ : syracuseStep 7627385 = 5720539) B5720539
theorem B2974427 : Blo 782338 2974427 := bstep (se 1 (by rfl) ⟨2230820, by rfl⟩ : syracuseStep 2974427 = 4461641) B4461641
theorem B1763297 : Blo 782338 1763297 := bstep (se 2 (by rfl) ⟨661236, by rfl⟩ : syracuseStep 1763297 = 1322473) B1322473
theorem B1763369 : Blo 782338 1763369 := bstep (se 2 (by rfl) ⟨661263, by rfl⟩ : syracuseStep 1763369 = 1322527) B1322527
theorem B2648159 : Blo 782338 2648159 := bstep (se 1 (by rfl) ⟨1986119, by rfl⟩ : syracuseStep 2648159 = 3972239) B3972239
theorem B7628975 : Blo 782338 7628975 := bstep (se 1 (by rfl) ⟨5721731, by rfl⟩ : syracuseStep 7628975 = 11443463) B11443463
theorem B5728511 : Blo 782338 5728511 := bstep (se 1 (by rfl) ⟨4296383, by rfl⟩ : syracuseStep 5728511 = 8592767) B8592767
theorem B1173887 : Blo 782338 1173887 := bstep (se 1 (by rfl) ⟨880415, by rfl⟩ : syracuseStep 1173887 = 1760831) B1760831
theorem B1174127 : Blo 782338 1174127 := bstep (se 1 (by rfl) ⟨880595, by rfl⟩ : syracuseStep 1174127 = 1761191) B1761191
theorem B1174319 : Blo 782338 1174319 := bstep (se 1 (by rfl) ⟨880739, by rfl⟩ : syracuseStep 1174319 = 1761479) B1761479
theorem B1764179 : Blo 782338 1764179 := bstep (se 1 (by rfl) ⟨1323134, by rfl⟩ : syracuseStep 1764179 = 2646269) B2646269
theorem B6352127 : Blo 782338 6352127 := bstep (se 1 (by rfl) ⟨4764095, by rfl⟩ : syracuseStep 6352127 = 9528191) B9528191
theorem B1764665 : Blo 782338 1764665 := bstep (se 2 (by rfl) ⟨661749, by rfl⟩ : syracuseStep 1764665 = 1323499) B1323499
theorem B2977145 : Blo 782338 2977145 := bstep (se 2 (by rfl) ⟨1116429, by rfl⟩ : syracuseStep 2977145 = 2232859) B2232859
theorem B1175207 : Blo 782338 1175207 := bstep (se 1 (by rfl) ⟨881405, by rfl⟩ : syracuseStep 1175207 = 1762811) B1762811
theorem B2649833 : Blo 782338 2649833 := bstep (se 2 (by rfl) ⟨993687, by rfl⟩ : syracuseStep 2649833 = 1987375) B1987375
theorem B1175279 : Blo 782338 1175279 := bstep (se 1 (by rfl) ⟨881459, by rfl⟩ : syracuseStep 1175279 = 1762919) B1762919
theorem B36138899 : Blo 782338 36138899 := bstep (se 1 (by rfl) ⟨27104174, by rfl⟩ : syracuseStep 36138899 = 54208349) B54208349
theorem B1175465 : Blo 782338 1175465 := bstep (se 2 (by rfl) ⟨440799, by rfl⟩ : syracuseStep 1175465 = 881599) B881599
theorem B1765331 : Blo 782338 1765331 := bstep (se 1 (by rfl) ⟨1323998, by rfl⟩ : syracuseStep 1765331 = 2647997) B2647997
theorem B782383 : Blo 782338 782383 := bstep (se 1 (by rfl) ⟨586787, by rfl⟩ : syracuseStep 782383 = 1173575) B1173575
theorem B782447 : Blo 782338 782447 := bstep (se 1 (by rfl) ⟨586835, by rfl⟩ : syracuseStep 782447 = 1173671) B1173671
theorem B18116741 : Blo 782338 18116741 := bstep (se 4 (by rfl) ⟨1698444, by rfl⟩ : syracuseStep 18116741 = 3396889) B3396889
theorem B782503 : Blo 782338 782503 := bstep (se 1 (by rfl) ⟨586877, by rfl⟩ : syracuseStep 782503 = 1173755) B1173755
theorem B1765583 : Blo 782338 1765583 := bstep (se 1 (by rfl) ⟨1324187, by rfl⟩ : syracuseStep 1765583 = 2648375) B2648375
theorem B17002831 : Blo 782338 17002831 := bstep (se 1 (by rfl) ⟨12752123, by rfl⟩ : syracuseStep 17002831 = 25504247) B25504247
theorem B782783 : Blo 782338 782783 := bstep (se 1 (by rfl) ⟨587087, by rfl⟩ : syracuseStep 782783 = 1174175) B1174175
theorem B782895 : Blo 782338 782895 := bstep (se 1 (by rfl) ⟨587171, by rfl⟩ : syracuseStep 782895 = 1174343) B1174343
theorem B2650697 : Blo 782338 2650697 := bstep (se 2 (by rfl) ⟨994011, by rfl⟩ : syracuseStep 2650697 = 1988023) B1988023
theorem B1766267 : Blo 782338 1766267 := bstep (se 1 (by rfl) ⟨1324700, by rfl⟩ : syracuseStep 1766267 = 2649401) B2649401
theorem B783295 : Blo 782338 783295 := bstep (se 1 (by rfl) ⟨587471, by rfl⟩ : syracuseStep 783295 = 1174943) B1174943
theorem B783743 : Blo 782338 783743 := bstep (se 1 (by rfl) ⟨587807, by rfl⟩ : syracuseStep 783743 = 1175615) B1175615
theorem B13432553 : Blo 782338 13432553 := bstep (se 2 (by rfl) ⟨5037207, by rfl⟩ : syracuseStep 13432553 = 10074415) B10074415
theorem B2979575 : Blo 782338 2979575 := bstep (se 1 (by rfl) ⟨2234681, by rfl⟩ : syracuseStep 2979575 = 4469363) B4469363
theorem B2652155 : Blo 782338 2652155 := bstep (se 1 (by rfl) ⟨1989116, by rfl⟩ : syracuseStep 2652155 = 3978233) B3978233
theorem B882751 : Blo 782338 882751 := bstep (se 1 (by rfl) ⟨662063, by rfl⟩ : syracuseStep 882751 = 1324127) B1324127
theorem B784607 : Blo 782338 784607 := bstep (se 1 (by rfl) ⟨588455, by rfl⟩ : syracuseStep 784607 = 1176911) B1176911
theorem B784635 : Blo 782338 784635 := bstep (se 1 (by rfl) ⟨588476, by rfl⟩ : syracuseStep 784635 = 1176953) B1176953
theorem B1177883 : Blo 782338 1177883 := bstep (se 1 (by rfl) ⟨883412, by rfl⟩ : syracuseStep 1177883 = 1766825) B1766825
theorem B1177919 : Blo 782338 1177919 := bstep (se 1 (by rfl) ⟨883439, by rfl⟩ : syracuseStep 1177919 = 1766879) B1766879
theorem B4520299 : Blo 782338 4520299 := bstep (se 1 (by rfl) ⟨3390224, by rfl⟩ : syracuseStep 4520299 = 6780449) B6780449
theorem B784767 : Blo 782338 784767 := bstep (se 1 (by rfl) ⟨588575, by rfl⟩ : syracuseStep 784767 = 1177151) B1177151
theorem B784999 : Blo 782338 784999 := bstep (se 1 (by rfl) ⟨588749, by rfl⟩ : syracuseStep 784999 = 1177499) B1177499
theorem B883327 : Blo 782338 883327 := bstep (se 1 (by rfl) ⟨662495, by rfl⟩ : syracuseStep 883327 = 1324991) B1324991
theorem B785087 : Blo 782338 785087 := bstep (se 1 (by rfl) ⟨588815, by rfl⟩ : syracuseStep 785087 = 1177631) B1177631
theorem B1178351 : Blo 782338 1178351 := bstep (se 1 (by rfl) ⟨883763, by rfl⟩ : syracuseStep 1178351 = 1767527) B1767527
theorem B3177427 : Blo 782338 3177427 := bstep (se 1 (by rfl) ⟨2383070, by rfl⟩ : syracuseStep 3177427 = 4766141) B4766141
theorem B785439 : Blo 782338 785439 := bstep (se 1 (by rfl) ⟨589079, by rfl⟩ : syracuseStep 785439 = 1178159) B1178159
theorem B3963977 : Blo 782338 3963977 := bstep (se 2 (by rfl) ⟨1486491, by rfl⟩ : syracuseStep 3963977 = 2972983) B2972983
theorem B785519 : Blo 782338 785519 := bstep (se 1 (by rfl) ⟨589139, by rfl⟩ : syracuseStep 785519 = 1178279) B1178279
theorem B785575 : Blo 782338 785575 := bstep (se 1 (by rfl) ⟨589181, by rfl⟩ : syracuseStep 785575 = 1178363) B1178363
theorem B785599 : Blo 782338 785599 := bstep (se 1 (by rfl) ⟨589199, by rfl⟩ : syracuseStep 785599 = 1178399) B1178399
theorem B785659 : Blo 782338 785659 := bstep (se 1 (by rfl) ⟨589244, by rfl⟩ : syracuseStep 785659 = 1178489) B1178489
theorem B1178921 : Blo 782338 1178921 := bstep (se 2 (by rfl) ⟨442095, by rfl⟩ : syracuseStep 1178921 = 884191) B884191
theorem B1768859 : Blo 782338 1768859 := bstep (se 1 (by rfl) ⟨1326644, by rfl⟩ : syracuseStep 1768859 = 2653289) B2653289
theorem B785887 : Blo 782338 785887 := bstep (se 1 (by rfl) ⟨589415, by rfl⟩ : syracuseStep 785887 = 1178831) B1178831
theorem B785967 : Blo 782338 785967 := bstep (se 1 (by rfl) ⟨589475, by rfl⟩ : syracuseStep 785967 = 1178951) B1178951
theorem B13401935 : Blo 782338 13401935 := bstep (se 1 (by rfl) ⟨10051451, by rfl⟩ : syracuseStep 13401935 = 20102903) B20102903
theorem B1671023 : Blo 782338 1671023 := bstep (se 1 (by rfl) ⟨1253267, by rfl⟩ : syracuseStep 1671023 = 2506535) B2506535
theorem B5964191 : Blo 782338 5964191 := bstep (se 1 (by rfl) ⟨4473143, by rfl⟩ : syracuseStep 5964191 = 8946287) B8946287
theorem B3573215 : Blo 782338 3573215 := bstep (se 1 (by rfl) ⟨2679911, by rfl⟩ : syracuseStep 3573215 = 5359823) B5359823
theorem B5375479 : Blo 782338 5375479 := bstep (se 1 (by rfl) ⟨4031609, by rfl⟩ : syracuseStep 5375479 = 8063219) B8063219
theorem B7145263 : Blo 782338 7145263 := bstep (se 1 (by rfl) ⟨5358947, by rfl⟩ : syracuseStep 7145263 = 10717895) B10717895
theorem B4458473 : Blo 782338 4458473 := bstep (se 2 (by rfl) ⟨1671927, by rfl⟩ : syracuseStep 4458473 = 3343855) B3343855
theorem B5966135 : Blo 782338 5966135 := bstep (se 1 (by rfl) ⟨4474601, by rfl⟩ : syracuseStep 5966135 = 8949203) B8949203
theorem B1116623 : Blo 782338 1116623 := bstep (se 1 (by rfl) ⟨837467, by rfl⟩ : syracuseStep 1116623 = 1674935) B1674935
theorem B1674047 : Blo 782338 1674047 := bstep (se 1 (by rfl) ⟨1255535, by rfl⟩ : syracuseStep 1674047 = 2511071) B2511071
theorem B3017857 : Blo 782338 3017857 := bstep (se 2 (by rfl) ⟨1131696, by rfl⟩ : syracuseStep 3017857 = 2263393) B2263393
theorem B4459657 : Blo 782338 4459657 := bstep (se 2 (by rfl) ⟨1672371, by rfl⟩ : syracuseStep 4459657 = 3344743) B3344743
theorem B146869625 : Blo 782338 146869625 := bstep (se 2 (by rfl) ⟨55076109, by rfl⟩ : syracuseStep 146869625 = 110152219) B110152219
theorem B38080043 : Blo 782338 38080043 := bstep (se 1 (by rfl) ⟨28560032, by rfl⟩ : syracuseStep 38080043 = 57120065) B57120065
theorem B5967593 : Blo 782338 5967593 := bstep (se 2 (by rfl) ⟨2237847, by rfl⟩ : syracuseStep 5967593 = 4475695) B4475695
theorem B11015639 : Blo 782338 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B5085983 : Blo 782338 5085983 := bstep (se 1 (by rfl) ⟨3814487, by rfl⟩ : syracuseStep 5085983 = 7628975) B7628975
theorem B8461367 : Blo 782338 8461367 := bstep (se 1 (by rfl) ⟨6346025, by rfl⟩ : syracuseStep 8461367 = 12692051) B12692051
theorem B4234751 : Blo 782338 4234751 := bstep (se 1 (by rfl) ⟨3176063, by rfl⟩ : syracuseStep 4234751 = 6352127) B6352127
theorem B6693313 : Blo 782338 6693313 := bstep (se 2 (by rfl) ⟨2509992, by rfl⟩ : syracuseStep 6693313 = 5019985) B5019985
theorem B5645467 : Blo 782338 5645467 := bstep (se 1 (by rfl) ⟨4234100, by rfl⟩ : syracuseStep 5645467 = 8468201) B8468201
theorem B8955035 : Blo 782338 8955035 := bstep (se 1 (by rfl) ⟨6716276, by rfl⟩ : syracuseStep 8955035 = 13432553) B13432553
theorem B4236569 : Blo 782338 4236569 := bstep (se 2 (by rfl) ⟨1588713, by rfl⟩ : syracuseStep 4236569 = 3177427) B3177427
theorem B4532561 : Blo 782338 4532561 := bstep (se 2 (by rfl) ⟨1699710, by rfl⟩ : syracuseStep 4532561 = 3399421) B3399421
theorem B1485695 : Blo 782338 1485695 := bstep (se 1 (by rfl) ⟨1114271, by rfl⟩ : syracuseStep 1485695 = 2228543) B2228543
theorem B4762633 : Blo 782338 4762633 := bstep (se 2 (by rfl) ⟨1785987, by rfl⟩ : syracuseStep 4762633 = 3571975) B3571975
theorem B48311309 : Blo 782338 48311309 := bstep (se 3 (by rfl) ⟨9058370, by rfl⟩ : syracuseStep 48311309 = 18116741) B18116741
theorem B1322311 : Blo 782338 1322311 := bstep (se 1 (by rfl) ⟨991733, by rfl⟩ : syracuseStep 1322311 = 1983467) B1983467
theorem B1322831 : Blo 782338 1322831 := bstep (se 1 (by rfl) ⟨992123, by rfl⟩ : syracuseStep 1322831 = 1984247) B1984247
theorem B1323803 : Blo 782338 1323803 := bstep (se 1 (by rfl) ⟨992852, by rfl⟩ : syracuseStep 1323803 = 1985705) B1985705
theorem B4469863 : Blo 782338 4469863 := bstep (se 1 (by rfl) ⟨3352397, by rfl⟩ : syracuseStep 4469863 = 6704795) B6704795
theorem B1324343 : Blo 782338 1324343 := bstep (se 1 (by rfl) ⟨993257, by rfl⟩ : syracuseStep 1324343 = 1986515) B1986515
theorem B15087019 : Blo 782338 15087019 := bstep (se 1 (by rfl) ⟨11315264, by rfl⟩ : syracuseStep 15087019 = 22630529) B22630529
theorem B5027831 : Blo 782338 5027831 := bstep (se 1 (by rfl) ⟨3770873, by rfl⟩ : syracuseStep 5027831 = 7541747) B7541747
theorem B6699023 : Blo 782338 6699023 := bstep (se 1 (by rfl) ⟨5024267, by rfl⟩ : syracuseStep 6699023 = 10048535) B10048535
theorem B4241755 : Blo 782338 4241755 := bstep (se 1 (by rfl) ⟨3181316, by rfl⟩ : syracuseStep 4241755 = 6362633) B6362633
theorem B1882727 : Blo 782338 1882727 := bstep (se 1 (by rfl) ⟨1412045, by rfl⟩ : syracuseStep 1882727 = 2824091) B2824091
theorem B1490015 : Blo 782338 1490015 := bstep (se 1 (by rfl) ⟨1117511, by rfl⟩ : syracuseStep 1490015 = 2235023) B2235023
theorem B2506393 : Blo 782338 2506393 := bstep (se 2 (by rfl) ⟨939897, by rfl⟩ : syracuseStep 2506393 = 1879795) B1879795
theorem B4767599 : Blo 782338 4767599 := bstep (se 1 (by rfl) ⟨3575699, by rfl⟩ : syracuseStep 4767599 = 7151399) B7151399
theorem B19120211 : Blo 782338 19120211 := bstep (se 1 (by rfl) ⟨14340158, by rfl⟩ : syracuseStep 19120211 = 28680317) B28680317
theorem B5030009 : Blo 782338 5030009 := bstep (se 2 (by rfl) ⟨1886253, by rfl⟩ : syracuseStep 5030009 = 3772507) B3772507
theorem B49725613 : Blo 782338 49725613 := bstep (se 3 (by rfl) ⟨9323552, by rfl⟩ : syracuseStep 49725613 = 18647105) B18647105
theorem B1982951 : Blo 782338 1982951 := bstep (se 1 (by rfl) ⟨1487213, by rfl⟩ : syracuseStep 1982951 = 2974427) B2974427
theorem B1983113 : Blo 782338 1983113 := bstep (se 2 (by rfl) ⟨743667, by rfl⟩ : syracuseStep 1983113 = 1487335) B1487335
theorem B3819007 : Blo 782338 3819007 := bstep (se 1 (by rfl) ⟨2864255, by rfl⟩ : syracuseStep 3819007 = 5728511) B5728511
theorem B1984763 : Blo 782338 1984763 := bstep (se 1 (by rfl) ⟨1488572, by rfl⟩ : syracuseStep 1984763 = 2977145) B2977145
theorem B5033107 : Blo 782338 5033107 := bstep (se 1 (by rfl) ⟨3774830, by rfl⟩ : syracuseStep 5033107 = 7549661) B7549661
theorem B970459 : Blo 782338 970459 := bstep (se 1 (by rfl) ⟨727844, by rfl⟩ : syracuseStep 970459 = 1455689) B1455689
theorem B1888031 : Blo 782338 1888031 := bstep (se 1 (by rfl) ⟨1416023, by rfl⟩ : syracuseStep 1888031 = 2832047) B2832047
theorem B1986383 : Blo 782338 1986383 := bstep (se 1 (by rfl) ⟨1489787, by rfl⟩ : syracuseStep 1986383 = 2979575) B2979575
theorem B4477153 : Blo 782338 4477153 := bstep (se 2 (by rfl) ⟨1678932, by rfl⟩ : syracuseStep 4477153 = 3357865) B3357865
theorem B2642489 : Blo 782338 2642489 := bstep (se 2 (by rfl) ⟨990933, by rfl⟩ : syracuseStep 2642489 = 1981867) B1981867
theorem B2642651 : Blo 782338 2642651 := bstep (se 1 (by rfl) ⟨1981988, by rfl⟩ : syracuseStep 2642651 = 3963977) B3963977
theorem B5952527 : Blo 782338 5952527 := bstep (se 1 (by rfl) ⟨4464395, by rfl⟩ : syracuseStep 5952527 = 8928791) B8928791
theorem B8934623 : Blo 782338 8934623 := bstep (se 1 (by rfl) ⟨6700967, by rfl⟩ : syracuseStep 8934623 = 13401935) B13401935
theorem B97703495 : Blo 782338 97703495 := bstep (se 1 (by rfl) ⟨73277621, by rfl⟩ : syracuseStep 97703495 = 146555243) B146555243
theorem B1988327 : Blo 782338 1988327 := bstep (se 1 (by rfl) ⟨1491245, by rfl⟩ : syracuseStep 1988327 = 2982491) B2982491
theorem B314136305 : Blo 782338 314136305 := bstep (se 2 (by rfl) ⟨117801114, by rfl⟩ : syracuseStep 314136305 = 235602229) B235602229
theorem B5953985 : Blo 782338 5953985 := bstep (se 2 (by rfl) ⟨2232744, by rfl⟩ : syracuseStep 5953985 = 4465489) B4465489
theorem B2120575 : Blo 782338 2120575 := bstep (se 1 (by rfl) ⟨1590431, by rfl⟩ : syracuseStep 2120575 = 3180863) B3180863
theorem B20339693 : Blo 782338 20339693 := bstep (se 3 (by rfl) ⟨3813692, by rfl⟩ : syracuseStep 20339693 = 7627385) B7627385
theorem B2645243 : Blo 782338 2645243 := bstep (se 1 (by rfl) ⟨1983932, by rfl⟩ : syracuseStep 2645243 = 3967865) B3967865
theorem B2416027 : Blo 782338 2416027 := bstep (se 1 (by rfl) ⟨1812020, by rfl⟩ : syracuseStep 2416027 = 3624041) B3624041
theorem B2973257 : Blo 782338 2973257 := bstep (se 2 (by rfl) ⟨1114971, by rfl⟩ : syracuseStep 2973257 = 2229943) B2229943
theorem B1761335 : Blo 782338 1761335 := bstep (se 1 (by rfl) ⟨1321001, by rfl⟩ : syracuseStep 1761335 = 2642003) B2642003
theorem B1761407 : Blo 782338 1761407 := bstep (se 1 (by rfl) ⟨1321055, by rfl⟩ : syracuseStep 1761407 = 2642111) B2642111
theorem B7529057 : Blo 782338 7529057 := bstep (se 2 (by rfl) ⟨2823396, by rfl⟩ : syracuseStep 7529057 = 5646793) B5646793
theorem B2975231 : Blo 782338 2975231 := bstep (se 1 (by rfl) ⟨2231423, by rfl⟩ : syracuseStep 2975231 = 4462847) B4462847
theorem B3761801 : Blo 782338 3761801 := bstep (se 2 (by rfl) ⟨1410675, by rfl⟩ : syracuseStep 3761801 = 2821351) B2821351
theorem B1762991 : Blo 782338 1762991 := bstep (se 1 (by rfl) ⟨1322243, by rfl⟩ : syracuseStep 1762991 = 2644487) B2644487
theorem B4778473 : Blo 782338 4778473 := bstep (se 2 (by rfl) ⟨1791927, by rfl⟩ : syracuseStep 4778473 = 3583855) B3583855
theorem B1763999 : Blo 782338 1763999 := bstep (se 1 (by rfl) ⟨1322999, by rfl⟩ : syracuseStep 1763999 = 2645999) B2645999
theorem B5663519 : Blo 782338 5663519 := bstep (se 1 (by rfl) ⟨4247639, by rfl⟩ : syracuseStep 5663519 = 8495279) B8495279
theorem B2648969 : Blo 782338 2648969 := bstep (se 2 (by rfl) ⟨993363, by rfl⟩ : syracuseStep 2648969 = 1986727) B1986727
theorem B1174463 : Blo 782338 1174463 := bstep (se 1 (by rfl) ⟨880847, by rfl⟩ : syracuseStep 1174463 = 1761695) B1761695
theorem B22670441 : Blo 782338 22670441 := bstep (se 2 (by rfl) ⟨8501415, by rfl⟩ : syracuseStep 22670441 = 17002831) B17002831
theorem B11333033 : Blo 782338 11333033 := bstep (se 2 (by rfl) ⟨4249887, by rfl⟩ : syracuseStep 11333033 = 8499775) B8499775
theorem B1175531 : Blo 782338 1175531 := bstep (se 1 (by rfl) ⟨881648, by rfl⟩ : syracuseStep 1175531 = 1763297) B1763297
theorem B2650103 : Blo 782338 2650103 := bstep (se 1 (by rfl) ⟨1987577, by rfl⟩ : syracuseStep 2650103 = 3975155) B3975155
theorem B1175579 : Blo 782338 1175579 := bstep (se 1 (by rfl) ⟨881684, by rfl⟩ : syracuseStep 1175579 = 1763369) B1763369
theorem B1765439 : Blo 782338 1765439 := bstep (se 1 (by rfl) ⟨1324079, by rfl⟩ : syracuseStep 1765439 = 2648159) B2648159
theorem B782591 : Blo 782338 782591 := bstep (se 1 (by rfl) ⟨586943, by rfl⟩ : syracuseStep 782591 = 1173887) B1173887
theorem B8941913 : Blo 782338 8941913 := bstep (se 2 (by rfl) ⟨3353217, by rfl⟩ : syracuseStep 8941913 = 6706435) B6706435
theorem B782751 : Blo 782338 782751 := bstep (se 1 (by rfl) ⟨587063, by rfl⟩ : syracuseStep 782751 = 1174127) B1174127
theorem B782879 : Blo 782338 782879 := bstep (se 1 (by rfl) ⟨587159, by rfl⟩ : syracuseStep 782879 = 1174319) B1174319
theorem B1176119 : Blo 782338 1176119 := bstep (se 1 (by rfl) ⟨882089, by rfl⟩ : syracuseStep 1176119 = 1764179) B1764179
theorem B1176443 : Blo 782338 1176443 := bstep (se 1 (by rfl) ⟨882332, by rfl⟩ : syracuseStep 1176443 = 1764665) B1764665
theorem B783471 : Blo 782338 783471 := bstep (se 1 (by rfl) ⟨587603, by rfl⟩ : syracuseStep 783471 = 1175207) B1175207
theorem B1766555 : Blo 782338 1766555 := bstep (se 1 (by rfl) ⟨1324916, by rfl⟩ : syracuseStep 1766555 = 2649833) B2649833
theorem B783519 : Blo 782338 783519 := bstep (se 1 (by rfl) ⟨587639, by rfl⟩ : syracuseStep 783519 = 1175279) B1175279
theorem B783643 : Blo 782338 783643 := bstep (se 1 (by rfl) ⟨587732, by rfl⟩ : syracuseStep 783643 = 1175465) B1175465
theorem B1176887 : Blo 782338 1176887 := bstep (se 1 (by rfl) ⟨882665, by rfl⟩ : syracuseStep 1176887 = 1765331) B1765331
theorem B1177001 : Blo 782338 1177001 := bstep (se 2 (by rfl) ⟨441375, by rfl⟩ : syracuseStep 1177001 = 882751) B882751
theorem B1177055 : Blo 782338 1177055 := bstep (se 1 (by rfl) ⟨882791, by rfl⟩ : syracuseStep 1177055 = 1765583) B1765583
theorem B1767131 : Blo 782338 1767131 := bstep (se 1 (by rfl) ⟨1325348, by rfl⟩ : syracuseStep 1767131 = 2650697) B2650697
theorem B6027065 : Blo 782338 6027065 := bstep (se 2 (by rfl) ⟨2260149, by rfl⟩ : syracuseStep 6027065 = 4520299) B4520299
theorem B1177511 : Blo 782338 1177511 := bstep (se 1 (by rfl) ⟨883133, by rfl⟩ : syracuseStep 1177511 = 1766267) B1766267
theorem B1177769 : Blo 782338 1177769 := bstep (se 2 (by rfl) ⟨441663, by rfl⟩ : syracuseStep 1177769 = 883327) B883327
theorem B4029065 : Blo 782338 4029065 := bstep (se 2 (by rfl) ⟨1510899, by rfl⟩ : syracuseStep 4029065 = 3021799) B3021799
theorem B1768103 : Blo 782338 1768103 := bstep (se 1 (by rfl) ⟨1326077, by rfl⟩ : syracuseStep 1768103 = 2652155) B2652155
theorem B2652911 : Blo 782338 2652911 := bstep (se 1 (by rfl) ⟨1989683, by rfl⟩ : syracuseStep 2652911 = 3979367) B3979367
theorem B785255 : Blo 782338 785255 := bstep (se 1 (by rfl) ⟨588941, by rfl⟩ : syracuseStep 785255 = 1177883) B1177883
theorem B785279 : Blo 782338 785279 := bstep (se 1 (by rfl) ⟨588959, by rfl⟩ : syracuseStep 785279 = 1177919) B1177919
theorem B785567 : Blo 782338 785567 := bstep (se 1 (by rfl) ⟨589175, by rfl⟩ : syracuseStep 785567 = 1178351) B1178351
theorem B785947 : Blo 782338 785947 := bstep (se 1 (by rfl) ⟨589460, by rfl⟩ : syracuseStep 785947 = 1178921) B1178921
theorem B1179239 : Blo 782338 1179239 := bstep (se 1 (by rfl) ⟨884429, by rfl⟩ : syracuseStep 1179239 = 1768859) B1768859
theorem B96370397 : Blo 782338 96370397 := bstep (se 3 (by rfl) ⟨18069449, by rfl⟩ : syracuseStep 96370397 = 36138899) B36138899
theorem B1114015 : Blo 782338 1114015 := bstep (se 1 (by rfl) ⟨835511, by rfl⟩ : syracuseStep 1114015 = 1671023) B1671023
theorem B12746807 : Blo 782338 12746807 := bstep (se 1 (by rfl) ⟨9560105, by rfl⟩ : syracuseStep 12746807 = 19120211) B19120211
theorem B1116031 : Blo 782338 1116031 := bstep (se 1 (by rfl) ⟨837023, by rfl⟩ : syracuseStep 1116031 = 1674047) B1674047
theorem B97913083 : Blo 782338 97913083 := bstep (se 1 (by rfl) ⟨73434812, by rfl⟩ : syracuseStep 97913083 = 146869625) B146869625
theorem B3968351 : Blo 782338 3968351 := bstep (se 1 (by rfl) ⟨2976263, by rfl⟩ : syracuseStep 3968351 = 5952527) B5952527
theorem B7343759 : Blo 782338 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B209424203 : Blo 782338 209424203 := bstep (se 1 (by rfl) ⟨157068152, by rfl⟩ : syracuseStep 209424203 = 314136305) B314136305
theorem B3969323 : Blo 782338 3969323 := bstep (se 1 (by rfl) ⟨2976992, by rfl⟩ : syracuseStep 3969323 = 5953985) B5953985
theorem B5640911 : Blo 782338 5640911 := bstep (se 1 (by rfl) ⟨4230683, by rfl⟩ : syracuseStep 5640911 = 8461367) B8461367
theorem B2823167 : Blo 782338 2823167 := bstep (se 1 (by rfl) ⟨2117375, by rfl⟩ : syracuseStep 2823167 = 4234751) B4234751
theorem B5969537 : Blo 782338 5969537 := bstep (se 2 (by rfl) ⟨2238576, by rfl⟩ : syracuseStep 5969537 = 4477153) B4477153
theorem B5019371 : Blo 782338 5019371 := bstep (se 1 (by rfl) ⟨3764528, by rfl⟩ : syracuseStep 5019371 = 7529057) B7529057
theorem B5970023 : Blo 782338 5970023 := bstep (se 1 (by rfl) ⟨4477517, by rfl⟩ : syracuseStep 5970023 = 8955035) B8955035
theorem B2824379 : Blo 782338 2824379 := bstep (se 1 (by rfl) ⟨2118284, by rfl⟩ : syracuseStep 2824379 = 4236569) B4236569
theorem B3021707 : Blo 782338 3021707 := bstep (se 1 (by rfl) ⟨2266280, by rfl⟩ : syracuseStep 3021707 = 4532561) B4532561
theorem B3775679 : Blo 782338 3775679 := bstep (se 1 (by rfl) ⟨2831759, by rfl⟩ : syracuseStep 3775679 = 5663519) B5663519
theorem B990463 : Blo 782338 990463 := bstep (se 1 (by rfl) ⟨742847, by rfl⟩ : syracuseStep 990463 = 1485695) B1485695
theorem B15113627 : Blo 782338 15113627 := bstep (se 1 (by rfl) ⟨11335220, by rfl⟩ : syracuseStep 15113627 = 22670441) B22670441
theorem B3973373 : Blo 782338 3973373 := bstep (se 3 (by rfl) ⟨745007, by rfl⟩ : syracuseStep 3973373 = 1490015) B1490015
theorem B2827433 : Blo 782338 2827433 := bstep (se 2 (by rfl) ⟨1060287, by rfl⟩ : syracuseStep 2827433 = 2120575) B2120575
theorem B3351887 : Blo 782338 3351887 := bstep (se 1 (by rfl) ⟨2513915, by rfl⟩ : syracuseStep 3351887 = 5027831) B5027831
theorem B4466015 : Blo 782338 4466015 := bstep (se 1 (by rfl) ⟨3349511, by rfl⟩ : syracuseStep 4466015 = 6699023) B6699023
theorem B1255151 : Blo 782338 1255151 := bstep (se 1 (by rfl) ⟨941363, by rfl⟩ : syracuseStep 1255151 = 1882727) B1882727
theorem B3221369 : Blo 782338 3221369 := bstep (se 2 (by rfl) ⟨1208013, by rfl⟩ : syracuseStep 3221369 = 2416027) B2416027
theorem B1485353 : Blo 782338 1485353 := bstep (se 2 (by rfl) ⟨557007, by rfl⟩ : syracuseStep 1485353 = 1114015) B1114015
theorem B3353339 : Blo 782338 3353339 := bstep (se 1 (by rfl) ⟨2515004, by rfl⟩ : syracuseStep 3353339 = 5030009) B5030009
theorem B66300817 : Blo 782338 66300817 := bstep (se 2 (by rfl) ⟨24862806, by rfl⟩ : syracuseStep 66300817 = 49725613) B49725613
theorem B3976127 : Blo 782338 3976127 := bstep (se 1 (by rfl) ⟨2982095, by rfl⟩ : syracuseStep 3976127 = 5964191) B5964191
theorem B1321967 : Blo 782338 1321967 := bstep (se 1 (by rfl) ⟨991475, by rfl⟩ : syracuseStep 1321967 = 1982951) B1982951
theorem B1322075 : Blo 782338 1322075 := bstep (se 1 (by rfl) ⟨991556, by rfl⟩ : syracuseStep 1322075 = 1983113) B1983113
theorem B8924417 : Blo 782338 8924417 := bstep (se 2 (by rfl) ⟨3346656, by rfl⟩ : syracuseStep 8924417 = 6693313) B6693313
theorem B1323175 : Blo 782338 1323175 := bstep (se 1 (by rfl) ⟨992381, by rfl⟩ : syracuseStep 1323175 = 1984763) B1984763
theorem B3977423 : Blo 782338 3977423 := bstep (se 1 (by rfl) ⟨2983067, by rfl⟩ : syracuseStep 3977423 = 5966135) B5966135
theorem B3978395 : Blo 782338 3978395 := bstep (se 1 (by rfl) ⟨2983796, by rfl⟩ : syracuseStep 3978395 = 5967593) B5967593
theorem B1258687 : Blo 782338 1258687 := bstep (se 1 (by rfl) ⟨944015, by rfl⟩ : syracuseStep 1258687 = 1888031) B1888031
theorem B1324255 : Blo 782338 1324255 := bstep (se 1 (by rfl) ⟨993191, by rfl⟩ : syracuseStep 1324255 = 1986383) B1986383
theorem B6371297 : Blo 782338 6371297 := bstep (se 2 (by rfl) ⟨2389236, by rfl⟩ : syracuseStep 6371297 = 4778473) B4778473
theorem B1325551 : Blo 782338 1325551 := bstep (se 1 (by rfl) ⟨994163, by rfl⟩ : syracuseStep 1325551 = 1988327) B1988327
theorem B5946209 : Blo 782338 5946209 := bstep (se 2 (by rfl) ⟨2229828, by rfl⟩ : syracuseStep 5946209 = 4459657) B4459657
theorem B3390655 : Blo 782338 3390655 := bstep (se 1 (by rfl) ⟨2542991, by rfl⟩ : syracuseStep 3390655 = 5085983) B5085983
theorem B1982171 : Blo 782338 1982171 := bstep (se 1 (by rfl) ⟨1486628, by rfl⟩ : syracuseStep 1982171 = 2973257) B2973257
theorem B1983487 : Blo 782338 1983487 := bstep (se 1 (by rfl) ⟨1487615, by rfl⟩ : syracuseStep 1983487 = 2975231) B2975231
theorem B2507867 : Blo 782338 2507867 := bstep (se 1 (by rfl) ⟨1880900, by rfl⟩ : syracuseStep 2507867 = 3761801) B3761801
theorem B7555355 : Blo 782338 7555355 := bstep (se 1 (by rfl) ⟨5666516, by rfl⟩ : syracuseStep 7555355 = 11333033) B11333033
theorem B20368037 : Blo 782338 20368037 := bstep (se 4 (by rfl) ⟨1909503, by rfl⟩ : syracuseStep 20368037 = 3819007) B3819007
theorem B5655673 : Blo 782338 5655673 := bstep (se 2 (by rfl) ⟨2120877, by rfl⟩ : syracuseStep 5655673 = 4241755) B4241755
theorem B4018043 : Blo 782338 4018043 := bstep (se 1 (by rfl) ⟨3013532, by rfl⟩ : syracuseStep 4018043 = 6027065) B6027065
theorem B64246931 : Blo 782338 64246931 := bstep (se 1 (by rfl) ⟨48185198, by rfl⟩ : syracuseStep 64246931 = 96370397) B96370397
theorem B2382143 : Blo 782338 2382143 := bstep (se 1 (by rfl) ⟨1786607, by rfl⟩ : syracuseStep 2382143 = 3573215) B3573215
theorem B2972315 : Blo 782338 2972315 := bstep (se 1 (by rfl) ⟨2229236, by rfl⟩ : syracuseStep 2972315 = 4458473) B4458473
theorem B7527289 : Blo 782338 7527289 := bstep (se 2 (by rfl) ⟨2822733, by rfl⟩ : syracuseStep 7527289 = 5645467) B5645467
theorem B7167305 : Blo 782338 7167305 := bstep (se 2 (by rfl) ⟨2687739, by rfl⟩ : syracuseStep 7167305 = 5375479) B5375479
theorem B25386695 : Blo 782338 25386695 := bstep (se 1 (by rfl) ⟨19040021, by rfl⟩ : syracuseStep 25386695 = 38080043) B38080043
theorem B9527017 : Blo 782338 9527017 := bstep (se 2 (by rfl) ⟨3572631, by rfl⟩ : syracuseStep 9527017 = 7145263) B7145263
theorem B1761659 : Blo 782338 1761659 := bstep (se 1 (by rfl) ⟨1321244, by rfl⟩ : syracuseStep 1761659 = 2642489) B2642489
theorem B1761767 : Blo 782338 1761767 := bstep (se 1 (by rfl) ⟨1321325, by rfl⟩ : syracuseStep 1761767 = 2642651) B2642651
theorem B5956415 : Blo 782338 5956415 := bstep (se 1 (by rfl) ⟨4467311, by rfl⟩ : syracuseStep 5956415 = 8934623) B8934623
theorem B65135663 : Blo 782338 65135663 := bstep (se 1 (by rfl) ⟨48851747, by rfl⟩ : syracuseStep 65135663 = 97703495) B97703495
theorem B6350177 : Blo 782338 6350177 := bstep (se 2 (by rfl) ⟨2381316, by rfl⟩ : syracuseStep 6350177 = 4762633) B4762633
theorem B4023809 : Blo 782338 4023809 := bstep (se 2 (by rfl) ⟨1508928, by rfl⟩ : syracuseStep 4023809 = 3017857) B3017857
theorem B6710809 : Blo 782338 6710809 := bstep (se 2 (by rfl) ⟨2516553, by rfl⟩ : syracuseStep 6710809 = 5033107) B5033107
theorem B1763081 : Blo 782338 1763081 := bstep (se 2 (by rfl) ⟨661155, by rfl⟩ : syracuseStep 1763081 = 1322311) B1322311
theorem B20703125 : Blo 782338 20703125 := bstep (se 6 (by rfl) ⟨485229, by rfl⟩ : syracuseStep 20703125 = 970459) B970459
theorem B13559795 : Blo 782338 13559795 := bstep (se 1 (by rfl) ⟨10169846, by rfl⟩ : syracuseStep 13559795 = 20339693) B20339693
theorem B1763495 : Blo 782338 1763495 := bstep (se 1 (by rfl) ⟨1322621, by rfl⟩ : syracuseStep 1763495 = 2645243) B2645243
theorem B1174223 : Blo 782338 1174223 := bstep (se 1 (by rfl) ⟨880667, by rfl⟩ : syracuseStep 1174223 = 1761335) B1761335
theorem B1174271 : Blo 782338 1174271 := bstep (se 1 (by rfl) ⟨880703, by rfl⟩ : syracuseStep 1174271 = 1761407) B1761407
theorem B1175327 : Blo 782338 1175327 := bstep (se 1 (by rfl) ⟨881495, by rfl⟩ : syracuseStep 1175327 = 1762991) B1762991
theorem B2977661 : Blo 782338 2977661 := bstep (se 3 (by rfl) ⟨558311, by rfl⟩ : syracuseStep 2977661 = 1116623) B1116623
theorem B5959817 : Blo 782338 5959817 := bstep (se 2 (by rfl) ⟨2234931, by rfl⟩ : syracuseStep 5959817 = 4469863) B4469863
theorem B1175999 : Blo 782338 1175999 := bstep (se 1 (by rfl) ⟨881999, by rfl⟩ : syracuseStep 1175999 = 1763999) B1763999
theorem B20116025 : Blo 782338 20116025 := bstep (se 2 (by rfl) ⟨7543509, by rfl⟩ : syracuseStep 20116025 = 15087019) B15087019
theorem B1765979 : Blo 782338 1765979 := bstep (se 1 (by rfl) ⟨1324484, by rfl⟩ : syracuseStep 1765979 = 2648969) B2648969
theorem B782975 : Blo 782338 782975 := bstep (se 1 (by rfl) ⟨587231, by rfl⟩ : syracuseStep 782975 = 1174463) B1174463
theorem B32207539 : Blo 782338 32207539 := bstep (se 1 (by rfl) ⟨24155654, by rfl⟩ : syracuseStep 32207539 = 48311309) B48311309
theorem B881887 : Blo 782338 881887 := bstep (se 1 (by rfl) ⟨661415, by rfl⟩ : syracuseStep 881887 = 1322831) B1322831
theorem B783687 : Blo 782338 783687 := bstep (se 1 (by rfl) ⟨587765, by rfl⟩ : syracuseStep 783687 = 1175531) B1175531
theorem B1766735 : Blo 782338 1766735 := bstep (se 1 (by rfl) ⟨1325051, by rfl⟩ : syracuseStep 1766735 = 2650103) B2650103
theorem B783719 : Blo 782338 783719 := bstep (se 1 (by rfl) ⟨587789, by rfl⟩ : syracuseStep 783719 = 1175579) B1175579
theorem B1176959 : Blo 782338 1176959 := bstep (se 1 (by rfl) ⟨882719, by rfl⟩ : syracuseStep 1176959 = 1765439) B1765439
theorem B5961275 : Blo 782338 5961275 := bstep (se 1 (by rfl) ⟨4470956, by rfl⟩ : syracuseStep 5961275 = 8941913) B8941913
theorem B784079 : Blo 782338 784079 := bstep (se 1 (by rfl) ⟨588059, by rfl⟩ : syracuseStep 784079 = 1176119) B1176119
theorem B882535 : Blo 782338 882535 := bstep (se 1 (by rfl) ⟨661901, by rfl⟩ : syracuseStep 882535 = 1323803) B1323803
theorem B784295 : Blo 782338 784295 := bstep (se 1 (by rfl) ⟨588221, by rfl⟩ : syracuseStep 784295 = 1176443) B1176443
theorem B1177703 : Blo 782338 1177703 := bstep (se 1 (by rfl) ⟨883277, by rfl⟩ : syracuseStep 1177703 = 1766555) B1766555
theorem B784591 : Blo 782338 784591 := bstep (se 1 (by rfl) ⟨588443, by rfl⟩ : syracuseStep 784591 = 1176887) B1176887
theorem B882895 : Blo 782338 882895 := bstep (se 1 (by rfl) ⟨662171, by rfl⟩ : syracuseStep 882895 = 1324343) B1324343
theorem B784667 : Blo 782338 784667 := bstep (se 1 (by rfl) ⟨588500, by rfl⟩ : syracuseStep 784667 = 1177001) B1177001
theorem B784703 : Blo 782338 784703 := bstep (se 1 (by rfl) ⟨588527, by rfl⟩ : syracuseStep 784703 = 1177055) B1177055
theorem B1178087 : Blo 782338 1178087 := bstep (se 1 (by rfl) ⟨883565, by rfl⟩ : syracuseStep 1178087 = 1767131) B1767131
theorem B785007 : Blo 782338 785007 := bstep (se 1 (by rfl) ⟨588755, by rfl⟩ : syracuseStep 785007 = 1177511) B1177511
theorem B785179 : Blo 782338 785179 := bstep (se 1 (by rfl) ⟨588884, by rfl⟩ : syracuseStep 785179 = 1177769) B1177769
theorem B2686043 : Blo 782338 2686043 := bstep (se 1 (by rfl) ⟨2014532, by rfl⟩ : syracuseStep 2686043 = 4029065) B4029065
theorem B1178735 : Blo 782338 1178735 := bstep (se 1 (by rfl) ⟨884051, by rfl⟩ : syracuseStep 1178735 = 1768103) B1768103
theorem B1768607 : Blo 782338 1768607 := bstep (se 1 (by rfl) ⟨1326455, by rfl⟩ : syracuseStep 1768607 = 2652911) B2652911
theorem B3341857 : Blo 782338 3341857 := bstep (se 2 (by rfl) ⟨1253196, by rfl⟩ : syracuseStep 3341857 = 2506393) B2506393
theorem B786159 : Blo 782338 786159 := bstep (se 1 (by rfl) ⟨589619, by rfl⟩ : syracuseStep 786159 = 1179239) B1179239
theorem B3178399 : Blo 782338 3178399 := bstep (se 1 (by rfl) ⟨2383799, by rfl⟩ : syracuseStep 3178399 = 4767599) B4767599
theorem B1671911 : Blo 782338 1671911 := bstep (se 1 (by rfl) ⟨1253933, by rfl⟩ : syracuseStep 1671911 = 2507867) B2507867
theorem B8947745 : Blo 782338 8947745 := bstep (se 2 (by rfl) ⟨3355404, by rfl⟩ : syracuseStep 8947745 = 6710809) B6710809
theorem B130550777 : Blo 782338 130550777 := bstep (se 2 (by rfl) ⟨48956541, by rfl⟩ : syracuseStep 130550777 = 97913083) B97913083
theorem B42831287 : Blo 782338 42831287 := bstep (se 1 (by rfl) ⟨32123465, by rfl⟩ : syracuseStep 42831287 = 64246931) B64246931
theorem B3346247 : Blo 782338 3346247 := bstep (se 1 (by rfl) ⟨2509685, by rfl⟩ : syracuseStep 3346247 = 5019371) B5019371
theorem B7540897 : Blo 782338 7540897 := bstep (se 2 (by rfl) ⟨2827836, by rfl⟩ : syracuseStep 7540897 = 5655673) B5655673
theorem B3970943 : Blo 782338 3970943 := bstep (se 1 (by rfl) ⟨2978207, by rfl⟩ : syracuseStep 3970943 = 5956415) B5956415
theorem B43423775 : Blo 782338 43423775 := bstep (se 1 (by rfl) ⟨32567831, by rfl⟩ : syracuseStep 43423775 = 65135663) B65135663
theorem B2234591 : Blo 782338 2234591 := bstep (se 1 (by rfl) ⟨1675943, by rfl⟩ : syracuseStep 2234591 = 3351887) B3351887
theorem B13802083 : Blo 782338 13802083 := bstep (se 1 (by rfl) ⟨10351562, by rfl⟩ : syracuseStep 13802083 = 20703125) B20703125
theorem B1678249 : Blo 782338 1678249 := bstep (se 2 (by rfl) ⟨629343, by rfl⟩ : syracuseStep 1678249 = 1258687) B1258687
theorem B990235 : Blo 782338 990235 := bstep (se 1 (by rfl) ⟨742676, by rfl⟩ : syracuseStep 990235 = 1485353) B1485353
theorem B2235559 : Blo 782338 2235559 := bstep (se 1 (by rfl) ⟨1676669, by rfl⟩ : syracuseStep 2235559 = 3353339) B3353339
theorem B3973211 : Blo 782338 3973211 := bstep (se 1 (by rfl) ⟨2979908, by rfl⟩ : syracuseStep 3973211 = 5959817) B5959817
theorem B13410683 : Blo 782338 13410683 := bstep (se 1 (by rfl) ⟨10058012, by rfl⟩ : syracuseStep 13410683 = 20116025) B20116025
theorem B3974183 : Blo 782338 3974183 := bstep (se 1 (by rfl) ⟨2980637, by rfl⟩ : syracuseStep 3974183 = 5961275) B5961275
theorem B10036385 : Blo 782338 10036385 := bstep (se 2 (by rfl) ⟨3763644, by rfl⟩ : syracuseStep 10036385 = 7527289) B7527289
theorem B1320617 : Blo 782338 1320617 := bstep (se 2 (by rfl) ⟨495231, by rfl⟩ : syracuseStep 1320617 = 990463) B990463
theorem B1321447 : Blo 782338 1321447 := bstep (se 1 (by rfl) ⟨991085, by rfl⟩ : syracuseStep 1321447 = 1982171) B1982171
theorem B4237865 : Blo 782338 4237865 := bstep (se 2 (by rfl) ⟨1589199, by rfl⟩ : syracuseStep 4237865 = 3178399) B3178399
theorem B8497871 : Blo 782338 8497871 := bstep (se 1 (by rfl) ⟨6373403, by rfl⟩ : syracuseStep 8497871 = 12746807) B12746807
theorem B13578691 : Blo 782338 13578691 := bstep (se 1 (by rfl) ⟨10184018, by rfl⟩ : syracuseStep 13578691 = 20368037) B20368037
theorem B4895839 : Blo 782338 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B1488041 : Blo 782338 1488041 := bstep (se 2 (by rfl) ⟨558015, by rfl⟩ : syracuseStep 1488041 = 1116031) B1116031
theorem B1882111 : Blo 782338 1882111 := bstep (se 1 (by rfl) ⟨1411583, by rfl⟩ : syracuseStep 1882111 = 2823167) B2823167
theorem B3979691 : Blo 782338 3979691 := bstep (se 1 (by rfl) ⟨2984768, by rfl⟩ : syracuseStep 3979691 = 5969537) B5969537
theorem B3980015 : Blo 782338 3980015 := bstep (se 1 (by rfl) ⟨2985011, by rfl⟩ : syracuseStep 3980015 = 5970023) B5970023
theorem B1882919 : Blo 782338 1882919 := bstep (se 1 (by rfl) ⟨1412189, by rfl⟩ : syracuseStep 1882919 = 2824379) B2824379
theorem B1981543 : Blo 782338 1981543 := bstep (se 1 (by rfl) ⟨1486157, by rfl⟩ : syracuseStep 1981543 = 2972315) B2972315
theorem B2014471 : Blo 782338 2014471 := bstep (se 1 (by rfl) ⟨1510853, by rfl⟩ : syracuseStep 2014471 = 3021707) B3021707
theorem B10075751 : Blo 782338 10075751 := bstep (se 1 (by rfl) ⟨7556813, by rfl⟩ : syracuseStep 10075751 = 15113627) B15113627
theorem B16924463 : Blo 782338 16924463 := bstep (se 1 (by rfl) ⟨12693347, by rfl⟩ : syracuseStep 16924463 = 25386695) B25386695
theorem B1884955 : Blo 782338 1884955 := bstep (se 1 (by rfl) ⟨1413716, by rfl⟩ : syracuseStep 1884955 = 2827433) B2827433
theorem B42943385 : Blo 782338 42943385 := bstep (se 2 (by rfl) ⟨16103769, by rfl⟩ : syracuseStep 42943385 = 32207539) B32207539
theorem B836767 : Blo 782338 836767 := bstep (se 1 (by rfl) ⟨627575, by rfl⟩ : syracuseStep 836767 = 1255151) B1255151
theorem B2147579 : Blo 782338 2147579 := bstep (se 1 (by rfl) ⟨1610684, by rfl⟩ : syracuseStep 2147579 = 3221369) B3221369
theorem B5949611 : Blo 782338 5949611 := bstep (se 1 (by rfl) ⟨4462208, by rfl⟩ : syracuseStep 5949611 = 8924417) B8924417
theorem B1985107 : Blo 782338 1985107 := bstep (se 1 (by rfl) ⟨1488830, by rfl⟩ : syracuseStep 1985107 = 2977661) B2977661
theorem B4247531 : Blo 782338 4247531 := bstep (se 1 (by rfl) ⟨3185648, by rfl⟩ : syracuseStep 4247531 = 6371297) B6371297
theorem B1790695 : Blo 782338 1790695 := bstep (se 1 (by rfl) ⟨1343021, by rfl⟩ : syracuseStep 1790695 = 2686043) B2686043
theorem B12702689 : Blo 782338 12702689 := bstep (se 2 (by rfl) ⟨4763508, by rfl⟩ : syracuseStep 12702689 = 9527017) B9527017
theorem B2644649 : Blo 782338 2644649 := bstep (se 2 (by rfl) ⟨991743, by rfl⟩ : syracuseStep 2644649 = 1983487) B1983487
theorem B5036903 : Blo 782338 5036903 := bstep (se 1 (by rfl) ⟨3777677, by rfl⟩ : syracuseStep 5036903 = 7555355) B7555355
theorem B2645567 : Blo 782338 2645567 := bstep (se 1 (by rfl) ⟨1984175, by rfl⟩ : syracuseStep 2645567 = 3968351) B3968351
theorem B139616135 : Blo 782338 139616135 := bstep (se 1 (by rfl) ⟨104712101, by rfl⟩ : syracuseStep 139616135 = 209424203) B209424203
theorem B2646215 : Blo 782338 2646215 := bstep (se 1 (by rfl) ⟨1984661, by rfl⟩ : syracuseStep 2646215 = 3969323) B3969323
theorem B3760607 : Blo 782338 3760607 := bstep (se 1 (by rfl) ⟨2820455, by rfl⟩ : syracuseStep 3760607 = 5640911) B5640911
theorem B16933805 : Blo 782338 16933805 := bstep (se 3 (by rfl) ⟨3175088, by rfl⟩ : syracuseStep 16933805 = 6350177) B6350177
theorem B88401089 : Blo 782338 88401089 := bstep (se 2 (by rfl) ⟨33150408, by rfl⟩ : syracuseStep 88401089 = 66300817) B66300817
theorem B2517119 : Blo 782338 2517119 := bstep (se 1 (by rfl) ⟨1887839, by rfl⟩ : syracuseStep 2517119 = 3775679) B3775679
theorem B4778203 : Blo 782338 4778203 := bstep (se 1 (by rfl) ⟨3583652, by rfl⟩ : syracuseStep 4778203 = 7167305) B7167305
theorem B2648915 : Blo 782338 2648915 := bstep (se 1 (by rfl) ⟨1986686, by rfl⟩ : syracuseStep 2648915 = 3973373) B3973373
theorem B1764233 : Blo 782338 1764233 := bstep (se 2 (by rfl) ⟨661587, by rfl⟩ : syracuseStep 1764233 = 1323175) B1323175
theorem B1174439 : Blo 782338 1174439 := bstep (se 1 (by rfl) ⟨880829, by rfl⟩ : syracuseStep 1174439 = 1761659) B1761659
theorem B1174511 : Blo 782338 1174511 := bstep (se 1 (by rfl) ⟨880883, by rfl⟩ : syracuseStep 1174511 = 1761767) B1761767
theorem B6352381 : Blo 782338 6352381 := bstep (se 3 (by rfl) ⟨1191071, by rfl⟩ : syracuseStep 6352381 = 2382143) B2382143
theorem B2977343 : Blo 782338 2977343 := bstep (se 1 (by rfl) ⟨2233007, by rfl⟩ : syracuseStep 2977343 = 4466015) B4466015
theorem B2682539 : Blo 782338 2682539 := bstep (se 1 (by rfl) ⟨2011904, by rfl⟩ : syracuseStep 2682539 = 4023809) B4023809
theorem B1175387 : Blo 782338 1175387 := bstep (se 1 (by rfl) ⟨881540, by rfl⟩ : syracuseStep 1175387 = 1763081) B1763081
theorem B9039863 : Blo 782338 9039863 := bstep (se 1 (by rfl) ⟨6779897, by rfl⟩ : syracuseStep 9039863 = 13559795) B13559795
theorem B1175663 : Blo 782338 1175663 := bstep (se 1 (by rfl) ⟨881747, by rfl⟩ : syracuseStep 1175663 = 1763495) B1763495
theorem B1175849 : Blo 782338 1175849 := bstep (se 2 (by rfl) ⟨440943, by rfl⟩ : syracuseStep 1175849 = 881887) B881887
theorem B1765673 : Blo 782338 1765673 := bstep (se 2 (by rfl) ⟨662127, by rfl⟩ : syracuseStep 1765673 = 1324255) B1324255
theorem B782815 : Blo 782338 782815 := bstep (se 1 (by rfl) ⟨587111, by rfl⟩ : syracuseStep 782815 = 1174223) B1174223
theorem B782847 : Blo 782338 782847 := bstep (se 1 (by rfl) ⟨587135, by rfl⟩ : syracuseStep 782847 = 1174271) B1174271
theorem B2650751 : Blo 782338 2650751 := bstep (se 1 (by rfl) ⟨1988063, by rfl⟩ : syracuseStep 2650751 = 3976127) B3976127
theorem B881311 : Blo 782338 881311 := bstep (se 1 (by rfl) ⟨660983, by rfl⟩ : syracuseStep 881311 = 1321967) B1321967
theorem B881383 : Blo 782338 881383 := bstep (se 1 (by rfl) ⟨661037, by rfl⟩ : syracuseStep 881383 = 1322075) B1322075
theorem B1176713 : Blo 782338 1176713 := bstep (se 2 (by rfl) ⟨441267, by rfl⟩ : syracuseStep 1176713 = 882535) B882535
theorem B783551 : Blo 782338 783551 := bstep (se 1 (by rfl) ⟨587663, by rfl⟩ : syracuseStep 783551 = 1175327) B1175327
theorem B2651615 : Blo 782338 2651615 := bstep (se 1 (by rfl) ⟨1988711, by rfl⟩ : syracuseStep 2651615 = 3977423) B3977423
theorem B1177193 : Blo 782338 1177193 := bstep (se 2 (by rfl) ⟨441447, by rfl⟩ : syracuseStep 1177193 = 882895) B882895
theorem B783999 : Blo 782338 783999 := bstep (se 1 (by rfl) ⟨587999, by rfl⟩ : syracuseStep 783999 = 1175999) B1175999
theorem B1177319 : Blo 782338 1177319 := bstep (se 1 (by rfl) ⟨882989, by rfl⟩ : syracuseStep 1177319 = 1765979) B1765979
theorem B1767401 : Blo 782338 1767401 := bstep (se 2 (by rfl) ⟨662775, by rfl⟩ : syracuseStep 1767401 = 1325551) B1325551
theorem B2652263 : Blo 782338 2652263 := bstep (se 1 (by rfl) ⟨1989197, by rfl⟩ : syracuseStep 2652263 = 3978395) B3978395
theorem B1177823 : Blo 782338 1177823 := bstep (se 1 (by rfl) ⟨883367, by rfl⟩ : syracuseStep 1177823 = 1766735) B1766735
theorem B784639 : Blo 782338 784639 := bstep (se 1 (by rfl) ⟨588479, by rfl⟩ : syracuseStep 784639 = 1176959) B1176959
theorem B785135 : Blo 782338 785135 := bstep (se 1 (by rfl) ⟨588851, by rfl⟩ : syracuseStep 785135 = 1177703) B1177703
theorem B4520873 : Blo 782338 4520873 := bstep (se 2 (by rfl) ⟨1695327, by rfl⟩ : syracuseStep 4520873 = 3390655) B3390655
theorem B785391 : Blo 782338 785391 := bstep (se 1 (by rfl) ⟨589043, by rfl⟩ : syracuseStep 785391 = 1178087) B1178087
theorem B3964139 : Blo 782338 3964139 := bstep (se 1 (by rfl) ⟨2973104, by rfl⟩ : syracuseStep 3964139 = 5946209) B5946209
theorem B4455809 : Blo 782338 4455809 := bstep (se 2 (by rfl) ⟨1670928, by rfl⟩ : syracuseStep 4455809 = 3341857) B3341857
theorem B785823 : Blo 782338 785823 := bstep (se 1 (by rfl) ⟨589367, by rfl⟩ : syracuseStep 785823 = 1178735) B1178735
theorem B1179071 : Blo 782338 1179071 := bstep (se 1 (by rfl) ⟨884303, by rfl⟩ : syracuseStep 1179071 = 1768607) B1768607
theorem B10714781 : Blo 782338 10714781 := bstep (se 3 (by rfl) ⟨2009021, by rfl⟩ : syracuseStep 10714781 = 4018043) B4018043
theorem B1114607 : Blo 782338 1114607 := bstep (se 1 (by rfl) ⟨835955, by rfl⟩ : syracuseStep 1114607 = 1671911) B1671911
theorem B10028285 : Blo 782338 10028285 := bstep (se 3 (by rfl) ⟨1880303, by rfl⟩ : syracuseStep 10028285 = 3760607) B3760607
theorem B5965163 : Blo 782338 5965163 := bstep (se 1 (by rfl) ⟨4473872, by rfl⟩ : syracuseStep 5965163 = 8947745) B8947745
theorem B3966407 : Blo 782338 3966407 := bstep (se 1 (by rfl) ⟨2974805, by rfl⟩ : syracuseStep 3966407 = 5949611) B5949611
theorem B1115689 : Blo 782338 1115689 := bstep (se 2 (by rfl) ⟨418383, by rfl⟩ : syracuseStep 1115689 = 836767) B836767
theorem B87033851 : Blo 782338 87033851 := bstep (se 1 (by rfl) ⟨65275388, by rfl⟩ : syracuseStep 87033851 = 130550777) B130550777
theorem B2230831 : Blo 782338 2230831 := bstep (se 1 (by rfl) ⟨1673123, by rfl⟩ : syracuseStep 2230831 = 3346247) B3346247
theorem B235736237 : Blo 782338 235736237 := bstep (se 3 (by rfl) ⟨44200544, by rfl⟩ : syracuseStep 235736237 = 88401089) B88401089
theorem B8950661 : Blo 782338 8950661 := bstep (se 4 (by rfl) ⟨839124, by rfl⟩ : syracuseStep 8950661 = 1678249) B1678249
theorem B6690923 : Blo 782338 6690923 := bstep (se 1 (by rfl) ⟨5018192, by rfl⟩ : syracuseStep 6690923 = 10036385) B10036385
theorem B1678079 : Blo 782338 1678079 := bstep (se 1 (by rfl) ⟨1258559, by rfl⟩ : syracuseStep 1678079 = 2517119) B2517119
theorem B6527785 : Blo 782338 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B2825243 : Blo 782338 2825243 := bstep (se 1 (by rfl) ⟨2118932, by rfl⟩ : syracuseStep 2825243 = 4237865) B4237865
theorem B992027 : Blo 782338 992027 := bstep (se 1 (by rfl) ⟨744020, by rfl⟩ : syracuseStep 992027 = 1488041) B1488041
theorem B1320313 : Blo 782338 1320313 := bstep (se 2 (by rfl) ⟨495117, by rfl⟩ : syracuseStep 1320313 = 990235) B990235
theorem B1255279 : Blo 782338 1255279 := bstep (se 1 (by rfl) ⟨941459, by rfl⟩ : syracuseStep 1255279 = 1882919) B1882919
theorem B11282975 : Blo 782338 11282975 := bstep (se 1 (by rfl) ⟨8462231, by rfl⟩ : syracuseStep 11282975 = 16924463) B16924463
theorem B28554191 : Blo 782338 28554191 := bstep (se 1 (by rfl) ⟨21415643, by rfl⟩ : syracuseStep 28554191 = 42831287) B42831287
theorem B2831687 : Blo 782338 2831687 := bstep (se 1 (by rfl) ⟨2123765, by rfl⟩ : syracuseStep 2831687 = 4247531) B4247531
theorem B6370937 : Blo 782338 6370937 := bstep (se 2 (by rfl) ⟨2389101, by rfl⟩ : syracuseStep 6370937 = 4778203) B4778203
theorem B73611109 : Blo 782338 73611109 := bstep (se 4 (by rfl) ⟨6901041, by rfl⟩ : syracuseStep 73611109 = 13802083) B13802083
theorem B8468459 : Blo 782338 8468459 := bstep (se 1 (by rfl) ⟨6351344, by rfl⟩ : syracuseStep 8468459 = 12702689) B12702689
theorem B28949183 : Blo 782338 28949183 := bstep (se 1 (by rfl) ⟨21711887, by rfl⟩ : syracuseStep 28949183 = 43423775) B43423775
theorem B1489727 : Blo 782338 1489727 := bstep (se 1 (by rfl) ⟨1117295, by rfl⟩ : syracuseStep 1489727 = 2234591) B2234591
theorem B3357935 : Blo 782338 3357935 := bstep (se 1 (by rfl) ⟨2518451, by rfl⟩ : syracuseStep 3357935 = 5036903) B5036903
theorem B8469841 : Blo 782338 8469841 := bstep (se 2 (by rfl) ⟨3176190, by rfl⟩ : syracuseStep 8469841 = 6352381) B6352381
theorem B93077423 : Blo 782338 93077423 := bstep (se 1 (by rfl) ⟨69808067, by rfl⟩ : syracuseStep 93077423 = 139616135) B139616135
theorem B18104921 : Blo 782338 18104921 := bstep (se 2 (by rfl) ⟨6789345, by rfl⟩ : syracuseStep 18104921 = 13578691) B13578691
theorem B11289203 : Blo 782338 11289203 := bstep (se 1 (by rfl) ⟨8466902, by rfl⟩ : syracuseStep 11289203 = 16933805) B16933805
theorem B1984895 : Blo 782338 1984895 := bstep (se 1 (by rfl) ⟨1488671, by rfl⟩ : syracuseStep 1984895 = 2977343) B2977343
theorem B1788359 : Blo 782338 1788359 := bstep (se 1 (by rfl) ⟨1341269, by rfl⟩ : syracuseStep 1788359 = 2682539) B2682539
theorem B2509481 : Blo 782338 2509481 := bstep (se 2 (by rfl) ⟨941055, by rfl⟩ : syracuseStep 2509481 = 1882111) B1882111
theorem B2642057 : Blo 782338 2642057 := bstep (se 2 (by rfl) ⟨990771, by rfl⟩ : syracuseStep 2642057 = 1981543) B1981543
theorem B2642759 : Blo 782338 2642759 := bstep (se 1 (by rfl) ⟨1982069, by rfl⟩ : syracuseStep 2642759 = 3964139) B3964139
theorem B2970539 : Blo 782338 2970539 := bstep (se 1 (by rfl) ⟨2227904, by rfl⟩ : syracuseStep 2970539 = 4455809) B4455809
theorem B1431719 : Blo 782338 1431719 := bstep (se 1 (by rfl) ⟨1073789, by rfl⟩ : syracuseStep 1431719 = 2147579) B2147579
theorem B2513273 : Blo 782338 2513273 := bstep (se 2 (by rfl) ⟨942477, by rfl⟩ : syracuseStep 2513273 = 1884955) B1884955
theorem B114515693 : Blo 782338 114515693 := bstep (se 3 (by rfl) ⟨21471692, by rfl⟩ : syracuseStep 114515693 = 42943385) B42943385
theorem B1761929 : Blo 782338 1761929 := bstep (se 2 (by rfl) ⟨660723, by rfl⟩ : syracuseStep 1761929 = 1321447) B1321447
theorem B2646809 : Blo 782338 2646809 := bstep (se 2 (by rfl) ⟨992553, by rfl⟩ : syracuseStep 2646809 = 1985107) B1985107
theorem B2647295 : Blo 782338 2647295 := bstep (se 1 (by rfl) ⟨1985471, by rfl⟩ : syracuseStep 2647295 = 3970943) B3970943
theorem B1763099 : Blo 782338 1763099 := bstep (se 1 (by rfl) ⟨1322324, by rfl⟩ : syracuseStep 1763099 = 2644649) B2644649
theorem B1763711 : Blo 782338 1763711 := bstep (se 1 (by rfl) ⟨1322783, by rfl⟩ : syracuseStep 1763711 = 2645567) B2645567
theorem B2648807 : Blo 782338 2648807 := bstep (se 1 (by rfl) ⟨1986605, by rfl⟩ : syracuseStep 2648807 = 3973211) B3973211
theorem B1764143 : Blo 782338 1764143 := bstep (se 1 (by rfl) ⟨1323107, by rfl⟩ : syracuseStep 1764143 = 2646215) B2646215
theorem B10054529 : Blo 782338 10054529 := bstep (se 2 (by rfl) ⟨3770448, by rfl⟩ : syracuseStep 10054529 = 7540897) B7540897
theorem B8940455 : Blo 782338 8940455 := bstep (se 1 (by rfl) ⟨6705341, by rfl⟩ : syracuseStep 8940455 = 13410683) B13410683
theorem B2649455 : Blo 782338 2649455 := bstep (se 1 (by rfl) ⟨1987091, by rfl⟩ : syracuseStep 2649455 = 3974183) B3974183
theorem B1175081 : Blo 782338 1175081 := bstep (se 2 (by rfl) ⟨440655, by rfl⟩ : syracuseStep 1175081 = 881311) B881311
theorem B1175177 : Blo 782338 1175177 := bstep (se 2 (by rfl) ⟨440691, by rfl⟩ : syracuseStep 1175177 = 881383) B881383
theorem B2387593 : Blo 782338 2387593 := bstep (se 2 (by rfl) ⟨895347, by rfl⟩ : syracuseStep 2387593 = 1790695) B1790695
theorem B880411 : Blo 782338 880411 := bstep (se 1 (by rfl) ⟨660308, by rfl⟩ : syracuseStep 880411 = 1320617) B1320617
theorem B5665247 : Blo 782338 5665247 := bstep (se 1 (by rfl) ⟨4248935, by rfl⟩ : syracuseStep 5665247 = 8497871) B8497871
theorem B1765943 : Blo 782338 1765943 := bstep (se 1 (by rfl) ⟨1324457, by rfl⟩ : syracuseStep 1765943 = 2648915) B2648915
theorem B1176155 : Blo 782338 1176155 := bstep (se 1 (by rfl) ⟨882116, by rfl⟩ : syracuseStep 1176155 = 1764233) B1764233
theorem B782959 : Blo 782338 782959 := bstep (se 1 (by rfl) ⟨587219, by rfl⟩ : syracuseStep 782959 = 1174439) B1174439
theorem B783007 : Blo 782338 783007 := bstep (se 1 (by rfl) ⟨587255, by rfl⟩ : syracuseStep 783007 = 1174511) B1174511
theorem B12055661 : Blo 782338 12055661 := bstep (se 3 (by rfl) ⟨2260436, by rfl⟩ : syracuseStep 12055661 = 4520873) B4520873
theorem B783591 : Blo 782338 783591 := bstep (se 1 (by rfl) ⟨587693, by rfl⟩ : syracuseStep 783591 = 1175387) B1175387
theorem B6026575 : Blo 782338 6026575 := bstep (se 1 (by rfl) ⟨4519931, by rfl⟩ : syracuseStep 6026575 = 9039863) B9039863
theorem B783775 : Blo 782338 783775 := bstep (se 1 (by rfl) ⟨587831, by rfl⟩ : syracuseStep 783775 = 1175663) B1175663
theorem B783899 : Blo 782338 783899 := bstep (se 1 (by rfl) ⟨587924, by rfl⟩ : syracuseStep 783899 = 1175849) B1175849
theorem B1177115 : Blo 782338 1177115 := bstep (se 1 (by rfl) ⟨882836, by rfl⟩ : syracuseStep 1177115 = 1765673) B1765673
theorem B1767167 : Blo 782338 1767167 := bstep (se 1 (by rfl) ⟨1325375, by rfl⟩ : syracuseStep 1767167 = 2650751) B2650751
theorem B784475 : Blo 782338 784475 := bstep (se 1 (by rfl) ⟨588356, by rfl⟩ : syracuseStep 784475 = 1176713) B1176713
theorem B1767743 : Blo 782338 1767743 := bstep (se 1 (by rfl) ⟨1325807, by rfl⟩ : syracuseStep 1767743 = 2651615) B2651615
theorem B784795 : Blo 782338 784795 := bstep (se 1 (by rfl) ⟨588596, by rfl⟩ : syracuseStep 784795 = 1177193) B1177193
theorem B784879 : Blo 782338 784879 := bstep (se 1 (by rfl) ⟨588659, by rfl⟩ : syracuseStep 784879 = 1177319) B1177319
theorem B1178267 : Blo 782338 1178267 := bstep (se 1 (by rfl) ⟨883700, by rfl⟩ : syracuseStep 1178267 = 1767401) B1767401
theorem B1768175 : Blo 782338 1768175 := bstep (se 1 (by rfl) ⟨1326131, by rfl⟩ : syracuseStep 1768175 = 2652263) B2652263
theorem B785215 : Blo 782338 785215 := bstep (se 1 (by rfl) ⟨588911, by rfl⟩ : syracuseStep 785215 = 1177823) B1177823
theorem B2980745 : Blo 782338 2980745 := bstep (se 2 (by rfl) ⟨1117779, by rfl⟩ : syracuseStep 2980745 = 2235559) B2235559
theorem B2653127 : Blo 782338 2653127 := bstep (se 1 (by rfl) ⟨1989845, by rfl⟩ : syracuseStep 2653127 = 3979691) B3979691
theorem B2685961 : Blo 782338 2685961 := bstep (se 2 (by rfl) ⟨1007235, by rfl⟩ : syracuseStep 2685961 = 2014471) B2014471
theorem B2653343 : Blo 782338 2653343 := bstep (se 1 (by rfl) ⟨1990007, by rfl⟩ : syracuseStep 2653343 = 3980015) B3980015
theorem B786047 : Blo 782338 786047 := bstep (se 1 (by rfl) ⟨589535, by rfl⟩ : syracuseStep 786047 = 1179071) B1179071
theorem B6717167 : Blo 782338 6717167 := bstep (se 1 (by rfl) ⟨5037875, by rfl⟩ : syracuseStep 6717167 = 10075751) B10075751
theorem B7143187 : Blo 782338 7143187 := bstep (se 1 (by rfl) ⟨5357390, by rfl⟩ : syracuseStep 7143187 = 10714781) B10714781
theorem B6685523 : Blo 782338 6685523 := bstep (se 1 (by rfl) ⟨5014142, by rfl⟩ : syracuseStep 6685523 = 10028285) B10028285
theorem B1672987 : Blo 782338 1672987 := bstep (se 1 (by rfl) ⟨1254740, by rfl⟩ : syracuseStep 1672987 = 2509481) B2509481
theorem B157157491 : Blo 782338 157157491 := bstep (se 1 (by rfl) ⟨117868118, by rfl⟩ : syracuseStep 157157491 = 235736237) B235736237
theorem B1673705 : Blo 782338 1673705 := bstep (se 2 (by rfl) ⟨627639, by rfl⟩ : syracuseStep 1673705 = 1255279) B1255279
theorem B5967107 : Blo 782338 5967107 := bstep (se 1 (by rfl) ⟨4475330, by rfl⟩ : syracuseStep 5967107 = 8950661) B8950661
theorem B4460615 : Blo 782338 4460615 := bstep (se 1 (by rfl) ⟨3345461, by rfl⟩ : syracuseStep 4460615 = 6690923) B6690923
theorem B954479 : Blo 782338 954479 := bstep (se 1 (by rfl) ⟨715859, by rfl⟩ : syracuseStep 954479 = 1431719) B1431719
theorem B1118719 : Blo 782338 1118719 := bstep (se 1 (by rfl) ⟨839039, by rfl⟩ : syracuseStep 1118719 = 1678079) B1678079
theorem B3183457 : Blo 782338 3183457 := bstep (se 2 (by rfl) ⟨1193796, by rfl⟩ : syracuseStep 3183457 = 2387593) B2387593
theorem B8035433 : Blo 782338 8035433 := bstep (se 2 (by rfl) ⟨3013287, by rfl⟩ : syracuseStep 8035433 = 6026575) B6026575
theorem B98148145 : Blo 782338 98148145 := bstep (se 2 (by rfl) ⟨36805554, by rfl⟩ : syracuseStep 98148145 = 73611109) B73611109
theorem B3776831 : Blo 782338 3776831 := bstep (se 1 (by rfl) ⟨2832623, by rfl⟩ : syracuseStep 3776831 = 5665247) B5665247
theorem B8037107 : Blo 782338 8037107 := bstep (se 1 (by rfl) ⟨6027830, by rfl⟩ : syracuseStep 8037107 = 12055661) B12055661
theorem B5645639 : Blo 782338 5645639 := bstep (se 1 (by rfl) ⟨4234229, by rfl⟩ : syracuseStep 5645639 = 8468459) B8468459
theorem B3581281 : Blo 782338 3581281 := bstep (se 2 (by rfl) ⟨1342980, by rfl⟩ : syracuseStep 3581281 = 2685961) B2685961
theorem B993151 : Blo 782338 993151 := bstep (se 1 (by rfl) ⟨744863, by rfl⟩ : syracuseStep 993151 = 1489727) B1489727
theorem B2238623 : Blo 782338 2238623 := bstep (se 1 (by rfl) ⟨1678967, by rfl⟩ : syracuseStep 2238623 = 3357935) B3357935
theorem B12069947 : Blo 782338 12069947 := bstep (se 1 (by rfl) ⟨9052460, by rfl⟩ : syracuseStep 12069947 = 18104921) B18104921
theorem B3976775 : Blo 782338 3976775 := bstep (se 1 (by rfl) ⟨2982581, by rfl⟩ : syracuseStep 3976775 = 5965163) B5965163
theorem B1323263 : Blo 782338 1323263 := bstep (se 1 (by rfl) ⟨992447, by rfl⟩ : syracuseStep 1323263 = 1984895) B1984895
theorem B1487585 : Blo 782338 1487585 := bstep (se 2 (by rfl) ⟨557844, by rfl⟩ : syracuseStep 1487585 = 1115689) B1115689
theorem B1980359 : Blo 782338 1980359 := bstep (se 1 (by rfl) ⟨1485269, by rfl⟩ : syracuseStep 1980359 = 2970539) B2970539
theorem B1883495 : Blo 782338 1883495 := bstep (se 1 (by rfl) ⟨1412621, by rfl⟩ : syracuseStep 1883495 = 2825243) B2825243
theorem B6702061 : Blo 782338 6702061 := bstep (se 3 (by rfl) ⟨1256636, by rfl⟩ : syracuseStep 6702061 = 2513273) B2513273
theorem B4768957 : Blo 782338 4768957 := bstep (se 3 (by rfl) ⟨894179, by rfl⟩ : syracuseStep 4768957 = 1788359) B1788359
theorem B7521983 : Blo 782338 7521983 := bstep (se 1 (by rfl) ⟨5641487, by rfl⟩ : syracuseStep 7521983 = 11282975) B11282975
theorem B6703019 : Blo 782338 6703019 := bstep (se 1 (by rfl) ⟨5027264, by rfl⟩ : syracuseStep 6703019 = 10054529) B10054529
theorem B1887791 : Blo 782338 1887791 := bstep (se 1 (by rfl) ⟨1415843, by rfl⟩ : syracuseStep 1887791 = 2831687) B2831687
theorem B8703713 : Blo 782338 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B4247291 : Blo 782338 4247291 := bstep (se 1 (by rfl) ⟨3185468, by rfl⟩ : syracuseStep 4247291 = 6370937) B6370937
theorem B11293121 : Blo 782338 11293121 := bstep (se 2 (by rfl) ⟨4234920, by rfl⟩ : syracuseStep 11293121 = 8469841) B8469841
theorem B1987163 : Blo 782338 1987163 := bstep (se 1 (by rfl) ⟨1490372, by rfl⟩ : syracuseStep 1987163 = 2980745) B2980745
theorem B9524249 : Blo 782338 9524249 := bstep (se 2 (by rfl) ⟨3571593, by rfl⟩ : syracuseStep 9524249 = 7143187) B7143187
theorem B4478111 : Blo 782338 4478111 := bstep (se 1 (by rfl) ⟨3358583, by rfl⟩ : syracuseStep 4478111 = 6717167) B6717167
theorem B62051615 : Blo 782338 62051615 := bstep (se 1 (by rfl) ⟨46538711, by rfl⟩ : syracuseStep 62051615 = 93077423) B93077423
theorem B7526135 : Blo 782338 7526135 := bstep (se 1 (by rfl) ⟨5644601, by rfl⟩ : syracuseStep 7526135 = 11289203) B11289203
theorem B2644271 : Blo 782338 2644271 := bstep (se 1 (by rfl) ⟨1983203, by rfl⟩ : syracuseStep 2644271 = 3966407) B3966407
theorem B2972285 : Blo 782338 2972285 := bstep (se 3 (by rfl) ⟨557303, by rfl⟩ : syracuseStep 2972285 = 1114607) B1114607
theorem B58022567 : Blo 782338 58022567 := bstep (se 1 (by rfl) ⟨43516925, by rfl⟩ : syracuseStep 58022567 = 87033851) B87033851
theorem B1760417 : Blo 782338 1760417 := bstep (se 2 (by rfl) ⟨660156, by rfl⟩ : syracuseStep 1760417 = 1320313) B1320313
theorem B2645405 : Blo 782338 2645405 := bstep (se 3 (by rfl) ⟨496013, by rfl⟩ : syracuseStep 2645405 = 992027) B992027
theorem B1761371 : Blo 782338 1761371 := bstep (se 1 (by rfl) ⟨1321028, by rfl⟩ : syracuseStep 1761371 = 2642057) B2642057
theorem B1761839 : Blo 782338 1761839 := bstep (se 1 (by rfl) ⟨1321379, by rfl⟩ : syracuseStep 1761839 = 2642759) B2642759
theorem B2974441 : Blo 782338 2974441 := bstep (se 2 (by rfl) ⟨1115415, by rfl⟩ : syracuseStep 2974441 = 2230831) B2230831
theorem B1173881 : Blo 782338 1173881 := bstep (se 2 (by rfl) ⟨440205, by rfl⟩ : syracuseStep 1173881 = 880411) B880411
theorem B76343795 : Blo 782338 76343795 := bstep (se 1 (by rfl) ⟨57257846, by rfl⟩ : syracuseStep 76343795 = 114515693) B114515693
theorem B1174619 : Blo 782338 1174619 := bstep (se 1 (by rfl) ⟨880964, by rfl⟩ : syracuseStep 1174619 = 1761929) B1761929
theorem B1764539 : Blo 782338 1764539 := bstep (se 1 (by rfl) ⟨1323404, by rfl⟩ : syracuseStep 1764539 = 2646809) B2646809
theorem B1764863 : Blo 782338 1764863 := bstep (se 1 (by rfl) ⟨1323647, by rfl⟩ : syracuseStep 1764863 = 2647295) B2647295
theorem B1175399 : Blo 782338 1175399 := bstep (se 1 (by rfl) ⟨881549, by rfl⟩ : syracuseStep 1175399 = 1763099) B1763099
theorem B1175807 : Blo 782338 1175807 := bstep (se 1 (by rfl) ⟨881855, by rfl⟩ : syracuseStep 1175807 = 1763711) B1763711
theorem B1765871 : Blo 782338 1765871 := bstep (se 1 (by rfl) ⟨1324403, by rfl⟩ : syracuseStep 1765871 = 2648807) B2648807
theorem B1176095 : Blo 782338 1176095 := bstep (se 1 (by rfl) ⟨882071, by rfl⟩ : syracuseStep 1176095 = 1764143) B1764143
theorem B5960303 : Blo 782338 5960303 := bstep (se 1 (by rfl) ⟨4470227, by rfl⟩ : syracuseStep 5960303 = 8940455) B8940455
theorem B1766303 : Blo 782338 1766303 := bstep (se 1 (by rfl) ⟨1324727, by rfl⟩ : syracuseStep 1766303 = 2649455) B2649455
theorem B783387 : Blo 782338 783387 := bstep (se 1 (by rfl) ⟨587540, by rfl⟩ : syracuseStep 783387 = 1175081) B1175081
theorem B783451 : Blo 782338 783451 := bstep (se 1 (by rfl) ⟨587588, by rfl⟩ : syracuseStep 783451 = 1175177) B1175177
theorem B1177295 : Blo 782338 1177295 := bstep (se 1 (by rfl) ⟨882971, by rfl⟩ : syracuseStep 1177295 = 1765943) B1765943
theorem B784103 : Blo 782338 784103 := bstep (se 1 (by rfl) ⟨588077, by rfl⟩ : syracuseStep 784103 = 1176155) B1176155
theorem B19036127 : Blo 782338 19036127 := bstep (se 1 (by rfl) ⟨14277095, by rfl⟩ : syracuseStep 19036127 = 28554191) B28554191
theorem B784743 : Blo 782338 784743 := bstep (se 1 (by rfl) ⟨588557, by rfl⟩ : syracuseStep 784743 = 1177115) B1177115
theorem B1178111 : Blo 782338 1178111 := bstep (se 1 (by rfl) ⟨883583, by rfl⟩ : syracuseStep 1178111 = 1767167) B1767167
theorem B1178495 : Blo 782338 1178495 := bstep (se 1 (by rfl) ⟨883871, by rfl⟩ : syracuseStep 1178495 = 1767743) B1767743
theorem B785511 : Blo 782338 785511 := bstep (se 1 (by rfl) ⟨589133, by rfl⟩ : syracuseStep 785511 = 1178267) B1178267
theorem B19299455 : Blo 782338 19299455 := bstep (se 1 (by rfl) ⟨14474591, by rfl⟩ : syracuseStep 19299455 = 28949183) B28949183
theorem B1178783 : Blo 782338 1178783 := bstep (se 1 (by rfl) ⟨884087, by rfl⟩ : syracuseStep 1178783 = 1768175) B1768175
theorem B1768751 : Blo 782338 1768751 := bstep (se 1 (by rfl) ⟨1326563, by rfl⟩ : syracuseStep 1768751 = 2653127) B2653127
theorem B1768895 : Blo 782338 1768895 := bstep (se 1 (by rfl) ⟨1326671, by rfl⟩ : syracuseStep 1768895 = 2653343) B2653343
theorem B4457015 : Blo 782338 4457015 := bstep (se 1 (by rfl) ⟨3342761, by rfl⟩ : syracuseStep 4457015 = 6685523) B6685523
theorem B3965921 : Blo 782338 3965921 := bstep (se 2 (by rfl) ⟨1487220, by rfl⟩ : syracuseStep 3965921 = 2974441) B2974441
theorem B5014655 : Blo 782338 5014655 := bstep (se 1 (by rfl) ⟨3760991, by rfl⟩ : syracuseStep 5014655 = 7521983) B7521983
theorem B30114989 : Blo 782338 30114989 := bstep (se 3 (by rfl) ⟨5646560, by rfl⟩ : syracuseStep 30114989 = 11293121) B11293121
theorem B6358609 : Blo 782338 6358609 := bstep (se 2 (by rfl) ⟨2384478, by rfl⟩ : syracuseStep 6358609 = 4768957) B4768957
theorem B1115803 : Blo 782338 1115803 := bstep (se 1 (by rfl) ⟨836852, by rfl⟩ : syracuseStep 1115803 = 1673705) B1673705
theorem B3966893 : Blo 782338 3966893 := bstep (se 3 (by rfl) ⟨743792, by rfl⟩ : syracuseStep 3966893 = 1487585) B1487585
theorem B2230649 : Blo 782338 2230649 := bstep (se 2 (by rfl) ⟨836493, by rfl⟩ : syracuseStep 2230649 = 1672987) B1672987
theorem B2985407 : Blo 782338 2985407 := bstep (se 1 (by rfl) ⟨2239055, by rfl⟩ : syracuseStep 2985407 = 4478111) B4478111
theorem B5017423 : Blo 782338 5017423 := bstep (se 1 (by rfl) ⟨3763067, by rfl⟩ : syracuseStep 5017423 = 7526135) B7526135
theorem B50895863 : Blo 782338 50895863 := bstep (se 1 (by rfl) ⟨38171897, by rfl⟩ : syracuseStep 50895863 = 76343795) B76343795
theorem B3973535 : Blo 782338 3973535 := bstep (se 1 (by rfl) ⟨2980151, by rfl⟩ : syracuseStep 3973535 = 5960303) B5960303
theorem B1320239 : Blo 782338 1320239 := bstep (se 1 (by rfl) ⟨990179, by rfl⟩ : syracuseStep 1320239 = 1980359) B1980359
theorem B12690751 : Blo 782338 12690751 := bstep (se 1 (by rfl) ⟨9518063, by rfl⟩ : syracuseStep 12690751 = 19036127) B19036127
theorem B23209901 : Blo 782338 23209901 := bstep (se 3 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 23209901 = 8703713) B8703713
theorem B1255663 : Blo 782338 1255663 := bstep (se 1 (by rfl) ⟨941747, by rfl⟩ : syracuseStep 1255663 = 1883495) B1883495
theorem B4468679 : Blo 782338 4468679 := bstep (se 1 (by rfl) ⟨3351509, by rfl⟩ : syracuseStep 4468679 = 6703019) B6703019
theorem B3978071 : Blo 782338 3978071 := bstep (se 1 (by rfl) ⟨2983553, by rfl⟩ : syracuseStep 3978071 = 5967107) B5967107
theorem B2831527 : Blo 782338 2831527 := bstep (se 1 (by rfl) ⟨2123645, by rfl⟩ : syracuseStep 2831527 = 4247291) B4247291
theorem B1324201 : Blo 782338 1324201 := bstep (se 2 (by rfl) ⟨496575, by rfl⟩ : syracuseStep 1324201 = 993151) B993151
theorem B1324775 : Blo 782338 1324775 := bstep (se 1 (by rfl) ⟨993581, by rfl⟩ : syracuseStep 1324775 = 1987163) B1987163
theorem B41367743 : Blo 782338 41367743 := bstep (se 1 (by rfl) ⟨31025807, by rfl⟩ : syracuseStep 41367743 = 62051615) B62051615
theorem B1981523 : Blo 782338 1981523 := bstep (se 1 (by rfl) ⟨1486142, by rfl⟩ : syracuseStep 1981523 = 2972285) B2972285
theorem B38681711 : Blo 782338 38681711 := bstep (se 1 (by rfl) ⟨29011283, by rfl⟩ : syracuseStep 38681711 = 58022567) B58022567
theorem B5356955 : Blo 782338 5356955 := bstep (se 1 (by rfl) ⟨4017716, by rfl⟩ : syracuseStep 5356955 = 8035433) B8035433
theorem B5358071 : Blo 782338 5358071 := bstep (se 1 (by rfl) ⟨4018553, by rfl⟩ : syracuseStep 5358071 = 8037107) B8037107
theorem B1491625 : Blo 782338 1491625 := bstep (se 2 (by rfl) ⟨559359, by rfl⟩ : syracuseStep 1491625 = 1118719) B1118719
theorem B4244609 : Blo 782338 4244609 := bstep (se 2 (by rfl) ⟨1591728, by rfl⟩ : syracuseStep 4244609 = 3183457) B3183457
theorem B1492415 : Blo 782338 1492415 := bstep (se 1 (by rfl) ⟨1119311, by rfl⟩ : syracuseStep 1492415 = 2238623) B2238623
theorem B8046631 : Blo 782338 8046631 := bstep (se 1 (by rfl) ⟨6034973, by rfl⟩ : syracuseStep 8046631 = 12069947) B12069947
theorem B5034109 : Blo 782338 5034109 := bstep (se 3 (by rfl) ⟨943895, by rfl⟩ : syracuseStep 5034109 = 1887791) B1887791
theorem B12866303 : Blo 782338 12866303 := bstep (se 1 (by rfl) ⟨9649727, by rfl⟩ : syracuseStep 12866303 = 19299455) B19299455
theorem B130864193 : Blo 782338 130864193 := bstep (se 2 (by rfl) ⟨49074072, by rfl⟩ : syracuseStep 130864193 = 98148145) B98148145
theorem B2545277 : Blo 782338 2545277 := bstep (se 3 (by rfl) ⟨477239, by rfl⟩ : syracuseStep 2545277 = 954479) B954479
theorem B8936081 : Blo 782338 8936081 := bstep (se 2 (by rfl) ⟨3351030, by rfl⟩ : syracuseStep 8936081 = 6702061) B6702061
theorem B4775041 : Blo 782338 4775041 := bstep (se 2 (by rfl) ⟨1790640, by rfl⟩ : syracuseStep 4775041 = 3581281) B3581281
theorem B2973743 : Blo 782338 2973743 := bstep (se 1 (by rfl) ⟨2230307, by rfl⟩ : syracuseStep 2973743 = 4460615) B4460615
theorem B209543321 : Blo 782338 209543321 := bstep (se 2 (by rfl) ⟨78578745, by rfl⟩ : syracuseStep 209543321 = 157157491) B157157491
theorem B6349499 : Blo 782338 6349499 := bstep (se 1 (by rfl) ⟨4762124, by rfl⟩ : syracuseStep 6349499 = 9524249) B9524249
theorem B1762847 : Blo 782338 1762847 := bstep (se 1 (by rfl) ⟨1322135, by rfl⟩ : syracuseStep 1762847 = 2644271) B2644271
theorem B1173611 : Blo 782338 1173611 := bstep (se 1 (by rfl) ⟨880208, by rfl⟩ : syracuseStep 1173611 = 1760417) B1760417
theorem B1763603 : Blo 782338 1763603 := bstep (se 1 (by rfl) ⟨1322702, by rfl⟩ : syracuseStep 1763603 = 2645405) B2645405
theorem B1174247 : Blo 782338 1174247 := bstep (se 1 (by rfl) ⟨880685, by rfl⟩ : syracuseStep 1174247 = 1761371) B1761371
theorem B2517887 : Blo 782338 2517887 := bstep (se 1 (by rfl) ⟨1888415, by rfl⟩ : syracuseStep 2517887 = 3776831) B3776831
theorem B1174559 : Blo 782338 1174559 := bstep (se 1 (by rfl) ⟨880919, by rfl⟩ : syracuseStep 1174559 = 1761839) B1761839
theorem B3763759 : Blo 782338 3763759 := bstep (se 1 (by rfl) ⟨2822819, by rfl⟩ : syracuseStep 3763759 = 5645639) B5645639
theorem B782587 : Blo 782338 782587 := bstep (se 1 (by rfl) ⟨586940, by rfl⟩ : syracuseStep 782587 = 1173881) B1173881
theorem B783079 : Blo 782338 783079 := bstep (se 1 (by rfl) ⟨587309, by rfl⟩ : syracuseStep 783079 = 1174619) B1174619
theorem B1176359 : Blo 782338 1176359 := bstep (se 1 (by rfl) ⟨882269, by rfl⟩ : syracuseStep 1176359 = 1764539) B1764539
theorem B1176575 : Blo 782338 1176575 := bstep (se 1 (by rfl) ⟨882431, by rfl⟩ : syracuseStep 1176575 = 1764863) B1764863
theorem B2651183 : Blo 782338 2651183 := bstep (se 1 (by rfl) ⟨1988387, by rfl⟩ : syracuseStep 2651183 = 3976775) B3976775
theorem B783599 : Blo 782338 783599 := bstep (se 1 (by rfl) ⟨587699, by rfl⟩ : syracuseStep 783599 = 1175399) B1175399
theorem B783871 : Blo 782338 783871 := bstep (se 1 (by rfl) ⟨587903, by rfl⟩ : syracuseStep 783871 = 1175807) B1175807
theorem B882175 : Blo 782338 882175 := bstep (se 1 (by rfl) ⟨661631, by rfl⟩ : syracuseStep 882175 = 1323263) B1323263
theorem B1177247 : Blo 782338 1177247 := bstep (se 1 (by rfl) ⟨882935, by rfl⟩ : syracuseStep 1177247 = 1765871) B1765871
theorem B784063 : Blo 782338 784063 := bstep (se 1 (by rfl) ⟨588047, by rfl⟩ : syracuseStep 784063 = 1176095) B1176095
theorem B1177535 : Blo 782338 1177535 := bstep (se 1 (by rfl) ⟨883151, by rfl⟩ : syracuseStep 1177535 = 1766303) B1766303
theorem B784863 : Blo 782338 784863 := bstep (se 1 (by rfl) ⟨588647, by rfl⟩ : syracuseStep 784863 = 1177295) B1177295
theorem B785407 : Blo 782338 785407 := bstep (se 1 (by rfl) ⟨589055, by rfl⟩ : syracuseStep 785407 = 1178111) B1178111
theorem B785663 : Blo 782338 785663 := bstep (se 1 (by rfl) ⟨589247, by rfl⟩ : syracuseStep 785663 = 1178495) B1178495
theorem B785855 : Blo 782338 785855 := bstep (se 1 (by rfl) ⟨589391, by rfl⟩ : syracuseStep 785855 = 1178783) B1178783
theorem B1179167 : Blo 782338 1179167 := bstep (se 1 (by rfl) ⟨884375, by rfl⟩ : syracuseStep 1179167 = 1768751) B1768751
theorem B1179263 : Blo 782338 1179263 := bstep (se 1 (by rfl) ⟨884447, by rfl⟩ : syracuseStep 1179263 = 1768895) B1768895
theorem B3572047 : Blo 782338 3572047 := bstep (se 1 (by rfl) ⟨2679035, by rfl⟩ : syracuseStep 3572047 = 5358071) B5358071
theorem B3343103 : Blo 782338 3343103 := bstep (se 1 (by rfl) ⟨2507327, by rfl⟩ : syracuseStep 3343103 = 5014655) B5014655
theorem B1674217 : Blo 782338 1674217 := bstep (se 2 (by rfl) ⟨627831, by rfl⟩ : syracuseStep 1674217 = 1255663) B1255663
theorem B6787405 : Blo 782338 6787405 := bstep (se 3 (by rfl) ⟨1272638, by rfl⟩ : syracuseStep 6787405 = 2545277) B2545277
theorem B5018345 : Blo 782338 5018345 := bstep (se 2 (by rfl) ⟨1881879, by rfl⟩ : syracuseStep 5018345 = 3763759) B3763759
theorem B6689897 : Blo 782338 6689897 := bstep (se 2 (by rfl) ⟨2508711, by rfl⟩ : syracuseStep 6689897 = 5017423) B5017423
theorem B139695547 : Blo 782338 139695547 := bstep (se 1 (by rfl) ⟨104771660, by rfl⟩ : syracuseStep 139695547 = 209543321) B209543321
theorem B4232999 : Blo 782338 4232999 := bstep (se 1 (by rfl) ⟨3174749, by rfl⟩ : syracuseStep 4232999 = 6349499) B6349499
theorem B25466885 : Blo 782338 25466885 := bstep (se 4 (by rfl) ⟨2387520, by rfl⟩ : syracuseStep 25466885 = 4775041) B4775041
theorem B15473267 : Blo 782338 15473267 := bstep (se 1 (by rfl) ⟨11604950, by rfl⟩ : syracuseStep 15473267 = 23209901) B23209901
theorem B1678591 : Blo 782338 1678591 := bstep (se 1 (by rfl) ⟨1258943, by rfl⟩ : syracuseStep 1678591 = 2517887) B2517887
theorem B1321015 : Blo 782338 1321015 := bstep (se 1 (by rfl) ⟨990761, by rfl⟩ : syracuseStep 1321015 = 1981523) B1981523
theorem B2829739 : Blo 782338 2829739 := bstep (se 1 (by rfl) ⟨2122304, by rfl⟩ : syracuseStep 2829739 = 4244609) B4244609
theorem B994943 : Blo 782338 994943 := bstep (se 1 (by rfl) ⟨746207, by rfl⟩ : syracuseStep 994943 = 1492415) B1492415
theorem B1487099 : Blo 782338 1487099 := bstep (se 1 (by rfl) ⟨1115324, by rfl⟩ : syracuseStep 1487099 = 2230649) B2230649
theorem B16921001 : Blo 782338 16921001 := bstep (se 2 (by rfl) ⟨6345375, by rfl⟩ : syracuseStep 16921001 = 12690751) B12690751
theorem B1487737 : Blo 782338 1487737 := bstep (se 2 (by rfl) ⟨557901, by rfl⟩ : syracuseStep 1487737 = 1115803) B1115803
theorem B87242795 : Blo 782338 87242795 := bstep (se 1 (by rfl) ⟨65432096, by rfl⟩ : syracuseStep 87242795 = 130864193) B130864193
theorem B33930575 : Blo 782338 33930575 := bstep (se 1 (by rfl) ⟨25447931, by rfl⟩ : syracuseStep 33930575 = 50895863) B50895863
theorem B1982495 : Blo 782338 1982495 := bstep (se 1 (by rfl) ⟨1486871, by rfl⟩ : syracuseStep 1982495 = 2973743) B2973743
theorem B27578495 : Blo 782338 27578495 := bstep (se 1 (by rfl) ⟨20683871, by rfl⟩ : syracuseStep 27578495 = 41367743) B41367743
theorem B42915365 : Blo 782338 42915365 := bstep (se 4 (by rfl) ⟨4023315, by rfl⟩ : syracuseStep 42915365 = 8046631) B8046631
theorem B2971343 : Blo 782338 2971343 := bstep (se 1 (by rfl) ⟨2228507, by rfl⟩ : syracuseStep 2971343 = 4457015) B4457015
theorem B2643947 : Blo 782338 2643947 := bstep (se 1 (by rfl) ⟨1982960, by rfl⟩ : syracuseStep 2643947 = 3965921) B3965921
theorem B20076659 : Blo 782338 20076659 := bstep (se 1 (by rfl) ⟨15057494, by rfl⟩ : syracuseStep 20076659 = 30114989) B30114989
theorem B1988833 : Blo 782338 1988833 := bstep (se 2 (by rfl) ⟨745812, by rfl⟩ : syracuseStep 1988833 = 1491625) B1491625
theorem B2644595 : Blo 782338 2644595 := bstep (se 1 (by rfl) ⟨1983446, by rfl⟩ : syracuseStep 2644595 = 3966893) B3966893
theorem B8478145 : Blo 782338 8478145 := bstep (se 2 (by rfl) ⟨3179304, by rfl⟩ : syracuseStep 8478145 = 6358609) B6358609
theorem B1990271 : Blo 782338 1990271 := bstep (se 1 (by rfl) ⟨1492703, by rfl⟩ : syracuseStep 1990271 = 2985407) B2985407
theorem B8577535 : Blo 782338 8577535 := bstep (se 1 (by rfl) ⟨6433151, by rfl⟩ : syracuseStep 8577535 = 12866303) B12866303
theorem B5957387 : Blo 782338 5957387 := bstep (se 1 (by rfl) ⟨4468040, by rfl⟩ : syracuseStep 5957387 = 8936081) B8936081
theorem B6712145 : Blo 782338 6712145 := bstep (se 2 (by rfl) ⟨2517054, by rfl⟩ : syracuseStep 6712145 = 5034109) B5034109
theorem B2649023 : Blo 782338 2649023 := bstep (se 1 (by rfl) ⟨1986767, by rfl⟩ : syracuseStep 2649023 = 3973535) B3973535
theorem B880159 : Blo 782338 880159 := bstep (se 1 (by rfl) ⟨660119, by rfl⟩ : syracuseStep 880159 = 1320239) B1320239
theorem B15101477 : Blo 782338 15101477 := bstep (se 4 (by rfl) ⟨1415763, by rfl⟩ : syracuseStep 15101477 = 2831527) B2831527
theorem B1175231 : Blo 782338 1175231 := bstep (se 1 (by rfl) ⟨881423, by rfl⟩ : syracuseStep 1175231 = 1762847) B1762847
theorem B782407 : Blo 782338 782407 := bstep (se 1 (by rfl) ⟨586805, by rfl⟩ : syracuseStep 782407 = 1173611) B1173611
theorem B1175735 : Blo 782338 1175735 := bstep (se 1 (by rfl) ⟨881801, by rfl⟩ : syracuseStep 1175735 = 1763603) B1763603
theorem B1765601 : Blo 782338 1765601 := bstep (se 2 (by rfl) ⟨662100, by rfl⟩ : syracuseStep 1765601 = 1324201) B1324201
theorem B782831 : Blo 782338 782831 := bstep (se 1 (by rfl) ⟨587123, by rfl⟩ : syracuseStep 782831 = 1174247) B1174247
theorem B1176233 : Blo 782338 1176233 := bstep (se 2 (by rfl) ⟨441087, by rfl⟩ : syracuseStep 1176233 = 882175) B882175
theorem B783039 : Blo 782338 783039 := bstep (se 1 (by rfl) ⟨587279, by rfl⟩ : syracuseStep 783039 = 1174559) B1174559
theorem B2979119 : Blo 782338 2979119 := bstep (se 1 (by rfl) ⟨2234339, by rfl⟩ : syracuseStep 2979119 = 4468679) B4468679
theorem B784239 : Blo 782338 784239 := bstep (se 1 (by rfl) ⟨588179, by rfl⟩ : syracuseStep 784239 = 1176359) B1176359
theorem B2652047 : Blo 782338 2652047 := bstep (se 1 (by rfl) ⟨1989035, by rfl⟩ : syracuseStep 2652047 = 3978071) B3978071
theorem B784383 : Blo 782338 784383 := bstep (se 1 (by rfl) ⟨588287, by rfl⟩ : syracuseStep 784383 = 1176575) B1176575
theorem B1767455 : Blo 782338 1767455 := bstep (se 1 (by rfl) ⟨1325591, by rfl⟩ : syracuseStep 1767455 = 2651183) B2651183
theorem B784831 : Blo 782338 784831 := bstep (se 1 (by rfl) ⟨588623, by rfl⟩ : syracuseStep 784831 = 1177247) B1177247
theorem B883183 : Blo 782338 883183 := bstep (se 1 (by rfl) ⟨662387, by rfl⟩ : syracuseStep 883183 = 1324775) B1324775
theorem B785023 : Blo 782338 785023 := bstep (se 1 (by rfl) ⟨588767, by rfl⟩ : syracuseStep 785023 = 1177535) B1177535
theorem B25787807 : Blo 782338 25787807 := bstep (se 1 (by rfl) ⟨19340855, by rfl⟩ : syracuseStep 25787807 = 38681711) B38681711
theorem B3571303 : Blo 782338 3571303 := bstep (se 1 (by rfl) ⟨2678477, by rfl⟩ : syracuseStep 3571303 = 5356955) B5356955
theorem B786111 : Blo 782338 786111 := bstep (se 1 (by rfl) ⟨589583, by rfl⟩ : syracuseStep 786111 = 1179167) B1179167
theorem B786175 : Blo 782338 786175 := bstep (se 1 (by rfl) ⟨589631, by rfl⟩ : syracuseStep 786175 = 1179263) B1179263
theorem B2228735 : Blo 782338 2228735 := bstep (se 1 (by rfl) ⟨1671551, by rfl⟩ : syracuseStep 2228735 = 3343103) B3343103
theorem B3965597 : Blo 782338 3965597 := bstep (se 3 (by rfl) ⟨743549, by rfl⟩ : syracuseStep 3965597 = 1487099) B1487099
theorem B11436713 : Blo 782338 11436713 := bstep (se 2 (by rfl) ⟨4288767, by rfl⟩ : syracuseStep 11436713 = 8577535) B8577535
theorem B18385663 : Blo 782338 18385663 := bstep (se 1 (by rfl) ⟨13789247, by rfl⟩ : syracuseStep 18385663 = 27578495) B27578495
theorem B3345563 : Blo 782338 3345563 := bstep (se 1 (by rfl) ⟨2509172, by rfl⟩ : syracuseStep 3345563 = 5018345) B5018345
theorem B4459931 : Blo 782338 4459931 := bstep (se 1 (by rfl) ⟨3344948, by rfl⟩ : syracuseStep 4459931 = 6689897) B6689897
theorem B28610243 : Blo 782338 28610243 := bstep (se 1 (by rfl) ⟨21457682, by rfl⟩ : syracuseStep 28610243 = 42915365) B42915365
theorem B2232289 : Blo 782338 2232289 := bstep (se 2 (by rfl) ⟨837108, by rfl⟩ : syracuseStep 2232289 = 1674217) B1674217
theorem B16977923 : Blo 782338 16977923 := bstep (se 1 (by rfl) ⟨12733442, by rfl⟩ : syracuseStep 16977923 = 25466885) B25466885
theorem B3772985 : Blo 782338 3772985 := bstep (se 2 (by rfl) ⟨1414869, by rfl⟩ : syracuseStep 3772985 = 2829739) B2829739
theorem B9049873 : Blo 782338 9049873 := bstep (se 2 (by rfl) ⟨3393702, by rfl⟩ : syracuseStep 9049873 = 6787405) B6787405
theorem B3971591 : Blo 782338 3971591 := bstep (se 1 (by rfl) ⟨2978693, by rfl⟩ : syracuseStep 3971591 = 5957387) B5957387
theorem B186260729 : Blo 782338 186260729 := bstep (se 2 (by rfl) ⟨69847773, by rfl⟩ : syracuseStep 186260729 = 139695547) B139695547
theorem B10067651 : Blo 782338 10067651 := bstep (se 1 (by rfl) ⟨7550738, by rfl⟩ : syracuseStep 10067651 = 15101477) B15101477
theorem B11280667 : Blo 782338 11280667 := bstep (se 1 (by rfl) ⟨8460500, by rfl⟩ : syracuseStep 11280667 = 16921001) B16921001
theorem B2238121 : Blo 782338 2238121 := bstep (se 2 (by rfl) ⟨839295, by rfl⟩ : syracuseStep 2238121 = 1678591) B1678591
theorem B4761737 : Blo 782338 4761737 := bstep (se 2 (by rfl) ⟨1785651, by rfl⟩ : syracuseStep 4761737 = 3571303) B3571303
theorem B22620383 : Blo 782338 22620383 := bstep (se 1 (by rfl) ⟨16965287, by rfl⟩ : syracuseStep 22620383 = 33930575) B33930575
theorem B1321663 : Blo 782338 1321663 := bstep (se 1 (by rfl) ⟨991247, by rfl⟩ : syracuseStep 1321663 = 1982495) B1982495
theorem B4762729 : Blo 782338 4762729 := bstep (se 2 (by rfl) ⟨1786023, by rfl⟩ : syracuseStep 4762729 = 3572047) B3572047
theorem B1980895 : Blo 782338 1980895 := bstep (se 1 (by rfl) ⟨1485671, by rfl⟩ : syracuseStep 1980895 = 2971343) B2971343
theorem B13384439 : Blo 782338 13384439 := bstep (se 1 (by rfl) ⟨10038329, by rfl⟩ : syracuseStep 13384439 = 20076659) B20076659
theorem B11287997 : Blo 782338 11287997 := bstep (se 3 (by rfl) ⟨2116499, by rfl⟩ : syracuseStep 11287997 = 4232999) B4232999
theorem B1326847 : Blo 782338 1326847 := bstep (se 1 (by rfl) ⟨995135, by rfl⟩ : syracuseStep 1326847 = 1990271) B1990271
theorem B1983649 : Blo 782338 1983649 := bstep (se 2 (by rfl) ⟨743868, by rfl⟩ : syracuseStep 1983649 = 1487737) B1487737
theorem B4474763 : Blo 782338 4474763 := bstep (se 1 (by rfl) ⟨3356072, by rfl⟩ : syracuseStep 4474763 = 6712145) B6712145
theorem B1986079 : Blo 782338 1986079 := bstep (se 1 (by rfl) ⟨1489559, by rfl⟩ : syracuseStep 1986079 = 2979119) B2979119
theorem B17191871 : Blo 782338 17191871 := bstep (se 1 (by rfl) ⟨12893903, by rfl⟩ : syracuseStep 17191871 = 25787807) B25787807
theorem B1761353 : Blo 782338 1761353 := bstep (se 2 (by rfl) ⟨660507, by rfl⟩ : syracuseStep 1761353 = 1321015) B1321015
theorem B1762631 : Blo 782338 1762631 := bstep (se 1 (by rfl) ⟨1321973, by rfl⟩ : syracuseStep 1762631 = 2643947) B2643947
theorem B10315511 : Blo 782338 10315511 := bstep (se 1 (by rfl) ⟨7736633, by rfl⟩ : syracuseStep 10315511 = 15473267) B15473267
theorem B1763063 : Blo 782338 1763063 := bstep (se 1 (by rfl) ⟨1322297, by rfl⟩ : syracuseStep 1763063 = 2644595) B2644595
theorem B1173545 : Blo 782338 1173545 := bstep (se 2 (by rfl) ⟨440079, by rfl⟩ : syracuseStep 1173545 = 880159) B880159
theorem B1766015 : Blo 782338 1766015 := bstep (se 1 (by rfl) ⟨1324511, by rfl⟩ : syracuseStep 1766015 = 2649023) B2649023
theorem B783487 : Blo 782338 783487 := bstep (se 1 (by rfl) ⟨587615, by rfl⟩ : syracuseStep 783487 = 1175231) B1175231
theorem B783823 : Blo 782338 783823 := bstep (se 1 (by rfl) ⟨587867, by rfl⟩ : syracuseStep 783823 = 1175735) B1175735
theorem B1177067 : Blo 782338 1177067 := bstep (se 1 (by rfl) ⟨882800, by rfl⟩ : syracuseStep 1177067 = 1765601) B1765601
theorem B2651777 : Blo 782338 2651777 := bstep (se 2 (by rfl) ⟨994416, by rfl⟩ : syracuseStep 2651777 = 1988833) B1988833
theorem B784155 : Blo 782338 784155 := bstep (se 1 (by rfl) ⟨588116, by rfl⟩ : syracuseStep 784155 = 1176233) B1176233
theorem B1177577 : Blo 782338 1177577 := bstep (se 2 (by rfl) ⟨441591, by rfl⟩ : syracuseStep 1177577 = 883183) B883183
theorem B1768031 : Blo 782338 1768031 := bstep (se 1 (by rfl) ⟨1326023, by rfl⟩ : syracuseStep 1768031 = 2652047) B2652047
theorem B1178303 : Blo 782338 1178303 := bstep (se 1 (by rfl) ⟨883727, by rfl⟩ : syracuseStep 1178303 = 1767455) B1767455
theorem B58161863 : Blo 782338 58161863 := bstep (se 1 (by rfl) ⟨43621397, by rfl⟩ : syracuseStep 58161863 = 87242795) B87242795
theorem B2653181 : Blo 782338 2653181 := bstep (se 3 (by rfl) ⟨497471, by rfl⟩ : syracuseStep 2653181 = 994943) B994943
theorem B11304193 : Blo 782338 11304193 := bstep (se 2 (by rfl) ⟨4239072, by rfl⟩ : syracuseStep 11304193 = 8478145) B8478145
theorem B15040889 : Blo 782338 15040889 := bstep (se 2 (by rfl) ⟨5640333, by rfl⟩ : syracuseStep 15040889 = 11280667) B11280667
theorem B2983175 : Blo 782338 2983175 := bstep (se 1 (by rfl) ⟨2237381, by rfl⟩ : syracuseStep 2983175 = 4474763) B4474763
theorem B10061293 : Blo 782338 10061293 := bstep (se 3 (by rfl) ⟨1886492, by rfl⟩ : syracuseStep 10061293 = 3772985) B3772985
theorem B2984161 : Blo 782338 2984161 := bstep (se 2 (by rfl) ⟨1119060, by rfl⟩ : syracuseStep 2984161 = 2238121) B2238121
theorem B19073495 : Blo 782338 19073495 := bstep (se 1 (by rfl) ⟨14305121, by rfl⟩ : syracuseStep 19073495 = 28610243) B28610243
theorem B24514217 : Blo 782338 24514217 := bstep (se 2 (by rfl) ⟨9192831, by rfl⟩ : syracuseStep 24514217 = 18385663) B18385663
theorem B25401221 : Blo 782338 25401221 := bstep (se 4 (by rfl) ⟨2381364, by rfl⟩ : syracuseStep 25401221 = 4762729) B4762729
theorem B15080255 : Blo 782338 15080255 := bstep (se 1 (by rfl) ⟨11310191, by rfl⟩ : syracuseStep 15080255 = 22620383) B22620383
theorem B12066497 : Blo 782338 12066497 := bstep (se 2 (by rfl) ⟨4524936, by rfl⟩ : syracuseStep 12066497 = 9049873) B9049873
theorem B8921501 : Blo 782338 8921501 := bstep (se 3 (by rfl) ⟨1672781, by rfl⟩ : syracuseStep 8921501 = 3345563) B3345563
theorem B38774575 : Blo 782338 38774575 := bstep (se 1 (by rfl) ⟨29080931, by rfl⟩ : syracuseStep 38774575 = 58161863) B58161863
theorem B8922959 : Blo 782338 8922959 := bstep (se 1 (by rfl) ⟨6692219, by rfl⟩ : syracuseStep 8922959 = 13384439) B13384439
theorem B5943293 : Blo 782338 5943293 := bstep (se 3 (by rfl) ⟨1114367, by rfl⟩ : syracuseStep 5943293 = 2228735) B2228735
theorem B11318615 : Blo 782338 11318615 := bstep (se 1 (by rfl) ⟨8488961, by rfl⟩ : syracuseStep 11318615 = 16977923) B16977923
theorem B2641193 : Blo 782338 2641193 := bstep (se 2 (by rfl) ⟨990447, by rfl⟩ : syracuseStep 2641193 = 1980895) B1980895
theorem B7525331 : Blo 782338 7525331 := bstep (se 1 (by rfl) ⟨5643998, by rfl⟩ : syracuseStep 7525331 = 11287997) B11287997
theorem B2643731 : Blo 782338 2643731 := bstep (se 1 (by rfl) ⟨1982798, by rfl⟩ : syracuseStep 2643731 = 3965597) B3965597
theorem B7624475 : Blo 782338 7624475 := bstep (se 1 (by rfl) ⟨5718356, by rfl⟩ : syracuseStep 7624475 = 11436713) B11436713
theorem B2644865 : Blo 782338 2644865 := bstep (se 2 (by rfl) ⟨991824, by rfl⟩ : syracuseStep 2644865 = 1983649) B1983649
theorem B2973287 : Blo 782338 2973287 := bstep (se 1 (by rfl) ⟨2229965, by rfl⟩ : syracuseStep 2973287 = 4459931) B4459931
theorem B11461247 : Blo 782338 11461247 := bstep (se 1 (by rfl) ⟨8595935, by rfl⟩ : syracuseStep 11461247 = 17191871) B17191871
theorem B1762217 : Blo 782338 1762217 := bstep (se 2 (by rfl) ⟨660831, by rfl⟩ : syracuseStep 1762217 = 1321663) B1321663
theorem B2647727 : Blo 782338 2647727 := bstep (se 1 (by rfl) ⟨1985795, by rfl⟩ : syracuseStep 2647727 = 3971591) B3971591
theorem B2648105 : Blo 782338 2648105 := bstep (se 2 (by rfl) ⟨993039, by rfl⟩ : syracuseStep 2648105 = 1986079) B1986079
theorem B6711767 : Blo 782338 6711767 := bstep (se 1 (by rfl) ⟨5033825, by rfl⟩ : syracuseStep 6711767 = 10067651) B10067651
theorem B2976385 : Blo 782338 2976385 := bstep (se 2 (by rfl) ⟨1116144, by rfl⟩ : syracuseStep 2976385 = 2232289) B2232289
theorem B1174235 : Blo 782338 1174235 := bstep (se 1 (by rfl) ⟨880676, by rfl⟩ : syracuseStep 1174235 = 1761353) B1761353
theorem B1175087 : Blo 782338 1175087 := bstep (se 1 (by rfl) ⟨881315, by rfl⟩ : syracuseStep 1175087 = 1762631) B1762631
theorem B6877007 : Blo 782338 6877007 := bstep (se 1 (by rfl) ⟨5157755, by rfl⟩ : syracuseStep 6877007 = 10315511) B10315511
theorem B1175375 : Blo 782338 1175375 := bstep (se 1 (by rfl) ⟨881531, by rfl⟩ : syracuseStep 1175375 = 1763063) B1763063
theorem B782363 : Blo 782338 782363 := bstep (se 1 (by rfl) ⟨586772, by rfl⟩ : syracuseStep 782363 = 1173545) B1173545
theorem B3174491 : Blo 782338 3174491 := bstep (se 1 (by rfl) ⟨2380868, by rfl⟩ : syracuseStep 3174491 = 4761737) B4761737
theorem B1177343 : Blo 782338 1177343 := bstep (se 1 (by rfl) ⟨883007, by rfl⟩ : syracuseStep 1177343 = 1766015) B1766015
theorem B496695277 : Blo 782338 496695277 := bstep (se 3 (by rfl) ⟨93130364, by rfl⟩ : syracuseStep 496695277 = 186260729) B186260729
theorem B784711 : Blo 782338 784711 := bstep (se 1 (by rfl) ⟨588533, by rfl⟩ : syracuseStep 784711 = 1177067) B1177067
theorem B1767851 : Blo 782338 1767851 := bstep (se 1 (by rfl) ⟨1325888, by rfl⟩ : syracuseStep 1767851 = 2651777) B2651777
theorem B785051 : Blo 782338 785051 := bstep (se 1 (by rfl) ⟨588788, by rfl⟩ : syracuseStep 785051 = 1177577) B1177577
theorem B15072257 : Blo 782338 15072257 := bstep (se 2 (by rfl) ⟨5652096, by rfl⟩ : syracuseStep 15072257 = 11304193) B11304193
theorem B1178687 : Blo 782338 1178687 := bstep (se 1 (by rfl) ⟨884015, by rfl⟩ : syracuseStep 1178687 = 1768031) B1768031
theorem B785535 : Blo 782338 785535 := bstep (se 1 (by rfl) ⟨589151, by rfl⟩ : syracuseStep 785535 = 1178303) B1178303
theorem B1768787 : Blo 782338 1768787 := bstep (se 1 (by rfl) ⟨1326590, by rfl⟩ : syracuseStep 1768787 = 2653181) B2653181
theorem B1769129 : Blo 782338 1769129 := bstep (se 2 (by rfl) ⟨663423, by rfl⟩ : syracuseStep 1769129 = 1326847) B1326847
theorem B10027259 : Blo 782338 10027259 := bstep (se 1 (by rfl) ⟨7520444, by rfl⟩ : syracuseStep 10027259 = 15040889) B15040889
theorem B12715663 : Blo 782338 12715663 := bstep (se 1 (by rfl) ⟨9536747, by rfl⟩ : syracuseStep 12715663 = 19073495) B19073495
theorem B5016887 : Blo 782338 5016887 := bstep (se 1 (by rfl) ⟨3762665, by rfl⟩ : syracuseStep 5016887 = 7525331) B7525331
theorem B3968513 : Blo 782338 3968513 := bstep (se 2 (by rfl) ⟨1488192, by rfl⟩ : syracuseStep 3968513 = 2976385) B2976385
theorem B5082983 : Blo 782338 5082983 := bstep (se 1 (by rfl) ⟨3812237, by rfl⟩ : syracuseStep 5082983 = 7624475) B7624475
theorem B7640831 : Blo 782338 7640831 := bstep (se 1 (by rfl) ⟨5730623, by rfl⟩ : syracuseStep 7640831 = 11461247) B11461247
theorem B7545743 : Blo 782338 7545743 := bstep (se 1 (by rfl) ⟨5659307, by rfl⟩ : syracuseStep 7545743 = 11318615) B11318615
theorem B8465309 : Blo 782338 8465309 := bstep (se 3 (by rfl) ⟨1587245, by rfl⟩ : syracuseStep 8465309 = 3174491) B3174491
theorem B13415057 : Blo 782338 13415057 := bstep (se 2 (by rfl) ⟨5030646, by rfl⟩ : syracuseStep 13415057 = 10061293) B10061293
theorem B3978881 : Blo 782338 3978881 := bstep (se 2 (by rfl) ⟨1492080, by rfl⟩ : syracuseStep 3978881 = 2984161) B2984161
theorem B1982191 : Blo 782338 1982191 := bstep (se 1 (by rfl) ⟨1486643, by rfl⟩ : syracuseStep 1982191 = 2973287) B2973287
theorem B8044331 : Blo 782338 8044331 := bstep (se 1 (by rfl) ⟨6033248, by rfl⟩ : syracuseStep 8044331 = 12066497) B12066497
theorem B5947667 : Blo 782338 5947667 := bstep (se 1 (by rfl) ⟨4460750, by rfl⟩ : syracuseStep 5947667 = 8921501) B8921501
theorem B5948639 : Blo 782338 5948639 := bstep (se 1 (by rfl) ⟨4461479, by rfl⟩ : syracuseStep 5948639 = 8922959) B8922959
theorem B4474511 : Blo 782338 4474511 := bstep (se 1 (by rfl) ⟨3355883, by rfl⟩ : syracuseStep 4474511 = 6711767) B6711767
theorem B662260369 : Blo 782338 662260369 := bstep (se 2 (by rfl) ⟨248347638, by rfl⟩ : syracuseStep 662260369 = 496695277) B496695277
theorem B10048171 : Blo 782338 10048171 := bstep (se 1 (by rfl) ⟨7536128, by rfl⟩ : syracuseStep 10048171 = 15072257) B15072257
theorem B1988783 : Blo 782338 1988783 := bstep (se 1 (by rfl) ⟨1491587, by rfl⟩ : syracuseStep 1988783 = 2983175) B2983175
theorem B1760795 : Blo 782338 1760795 := bstep (se 1 (by rfl) ⟨1320596, by rfl⟩ : syracuseStep 1760795 = 2641193) B2641193
theorem B51699433 : Blo 782338 51699433 := bstep (se 2 (by rfl) ⟨19387287, by rfl⟩ : syracuseStep 51699433 = 38774575) B38774575
theorem B16342811 : Blo 782338 16342811 := bstep (se 1 (by rfl) ⟨12257108, by rfl⟩ : syracuseStep 16342811 = 24514217) B24514217
theorem B1762487 : Blo 782338 1762487 := bstep (se 1 (by rfl) ⟨1321865, by rfl⟩ : syracuseStep 1762487 = 2643731) B2643731
theorem B16934147 : Blo 782338 16934147 := bstep (se 1 (by rfl) ⟨12700610, by rfl⟩ : syracuseStep 16934147 = 25401221) B25401221
theorem B10053503 : Blo 782338 10053503 := bstep (se 1 (by rfl) ⟨7540127, by rfl⟩ : syracuseStep 10053503 = 15080255) B15080255
theorem B1763243 : Blo 782338 1763243 := bstep (se 1 (by rfl) ⟨1322432, by rfl⟩ : syracuseStep 1763243 = 2644865) B2644865
theorem B1174811 : Blo 782338 1174811 := bstep (se 1 (by rfl) ⟨881108, by rfl⟩ : syracuseStep 1174811 = 1762217) B1762217
theorem B1765151 : Blo 782338 1765151 := bstep (se 1 (by rfl) ⟨1323863, by rfl⟩ : syracuseStep 1765151 = 2647727) B2647727
theorem B1765403 : Blo 782338 1765403 := bstep (se 1 (by rfl) ⟨1324052, by rfl⟩ : syracuseStep 1765403 = 2648105) B2648105
theorem B782823 : Blo 782338 782823 := bstep (se 1 (by rfl) ⟨587117, by rfl⟩ : syracuseStep 782823 = 1174235) B1174235
theorem B783391 : Blo 782338 783391 := bstep (se 1 (by rfl) ⟨587543, by rfl⟩ : syracuseStep 783391 = 1175087) B1175087
theorem B4584671 : Blo 782338 4584671 := bstep (se 1 (by rfl) ⟨3438503, by rfl⟩ : syracuseStep 4584671 = 6877007) B6877007
theorem B783583 : Blo 782338 783583 := bstep (se 1 (by rfl) ⟨587687, by rfl⟩ : syracuseStep 783583 = 1175375) B1175375
theorem B3962195 : Blo 782338 3962195 := bstep (se 1 (by rfl) ⟨2971646, by rfl⟩ : syracuseStep 3962195 = 5943293) B5943293
theorem B784895 : Blo 782338 784895 := bstep (se 1 (by rfl) ⟨588671, by rfl⟩ : syracuseStep 784895 = 1177343) B1177343
theorem B1178567 : Blo 782338 1178567 := bstep (se 1 (by rfl) ⟨883925, by rfl⟩ : syracuseStep 1178567 = 1767851) B1767851
theorem B785791 : Blo 782338 785791 := bstep (se 1 (by rfl) ⟨589343, by rfl⟩ : syracuseStep 785791 = 1178687) B1178687
theorem B1179191 : Blo 782338 1179191 := bstep (se 1 (by rfl) ⟨884393, by rfl⟩ : syracuseStep 1179191 = 1768787) B1768787
theorem B1179419 : Blo 782338 1179419 := bstep (se 1 (by rfl) ⟨884564, by rfl⟩ : syracuseStep 1179419 = 1769129) B1769129
theorem B6684839 : Blo 782338 6684839 := bstep (se 1 (by rfl) ⟨5013629, by rfl⟩ : syracuseStep 6684839 = 10027259) B10027259
theorem B3965111 : Blo 782338 3965111 := bstep (se 1 (by rfl) ⟨2973833, by rfl⟩ : syracuseStep 3965111 = 5947667) B5947667
theorem B3965759 : Blo 782338 3965759 := bstep (se 1 (by rfl) ⟨2974319, by rfl⟩ : syracuseStep 3965759 = 5948639) B5948639
theorem B2983007 : Blo 782338 2983007 := bstep (se 1 (by rfl) ⟨2237255, by rfl⟩ : syracuseStep 2983007 = 4474511) B4474511
theorem B3344591 : Blo 782338 3344591 := bstep (se 1 (by rfl) ⟨2508443, by rfl⟩ : syracuseStep 3344591 = 5016887) B5016887
theorem B5643539 : Blo 782338 5643539 := bstep (se 1 (by rfl) ⟨4232654, by rfl⟩ : syracuseStep 5643539 = 8465309) B8465309
theorem B3056447 : Blo 782338 3056447 := bstep (se 1 (by rfl) ⟨2292335, by rfl⟩ : syracuseStep 3056447 = 4584671) B4584671
theorem B16954217 : Blo 782338 16954217 := bstep (se 2 (by rfl) ⟨6357831, by rfl⟩ : syracuseStep 16954217 = 12715663) B12715663
theorem B3388655 : Blo 782338 3388655 := bstep (se 1 (by rfl) ⟨2541491, by rfl⟩ : syracuseStep 3388655 = 5082983) B5082983
theorem B883013825 : Blo 782338 883013825 := bstep (se 2 (by rfl) ⟨331130184, by rfl⟩ : syracuseStep 883013825 = 662260369) B662260369
theorem B1325855 : Blo 782338 1325855 := bstep (se 1 (by rfl) ⟨994391, by rfl⟩ : syracuseStep 1325855 = 1988783) B1988783
theorem B10895207 : Blo 782338 10895207 := bstep (se 1 (by rfl) ⟨8171405, by rfl⟩ : syracuseStep 10895207 = 16342811) B16342811
theorem B5030495 : Blo 782338 5030495 := bstep (se 1 (by rfl) ⟨3772871, by rfl⟩ : syracuseStep 5030495 = 7545743) B7545743
theorem B11289431 : Blo 782338 11289431 := bstep (se 1 (by rfl) ⟨8467073, by rfl⟩ : syracuseStep 11289431 = 16934147) B16934147
theorem B6702335 : Blo 782338 6702335 := bstep (se 1 (by rfl) ⟨5026751, by rfl⟩ : syracuseStep 6702335 = 10053503) B10053503
theorem B2641463 : Blo 782338 2641463 := bstep (se 1 (by rfl) ⟨1981097, by rfl⟩ : syracuseStep 2641463 = 3962195) B3962195
theorem B21451549 : Blo 782338 21451549 := bstep (se 3 (by rfl) ⟨4022165, by rfl⟩ : syracuseStep 21451549 = 8044331) B8044331
theorem B68932577 : Blo 782338 68932577 := bstep (se 2 (by rfl) ⟨25849716, by rfl⟩ : syracuseStep 68932577 = 51699433) B51699433
theorem B2642921 : Blo 782338 2642921 := bstep (se 2 (by rfl) ⟨991095, by rfl⟩ : syracuseStep 2642921 = 1982191) B1982191
theorem B2645675 : Blo 782338 2645675 := bstep (se 1 (by rfl) ⟨1984256, by rfl⟩ : syracuseStep 2645675 = 3968513) B3968513
theorem B20375549 : Blo 782338 20375549 := bstep (se 3 (by rfl) ⟨3820415, by rfl⟩ : syracuseStep 20375549 = 7640831) B7640831
theorem B1173863 : Blo 782338 1173863 := bstep (se 1 (by rfl) ⟨880397, by rfl⟩ : syracuseStep 1173863 = 1760795) B1760795
theorem B1174991 : Blo 782338 1174991 := bstep (se 1 (by rfl) ⟨881243, by rfl⟩ : syracuseStep 1174991 = 1762487) B1762487
theorem B13397561 : Blo 782338 13397561 := bstep (se 2 (by rfl) ⟨5024085, by rfl⟩ : syracuseStep 13397561 = 10048171) B10048171
theorem B1175495 : Blo 782338 1175495 := bstep (se 1 (by rfl) ⟨881621, by rfl⟩ : syracuseStep 1175495 = 1763243) B1763243
theorem B783207 : Blo 782338 783207 := bstep (se 1 (by rfl) ⟨587405, by rfl⟩ : syracuseStep 783207 = 1174811) B1174811
theorem B1176767 : Blo 782338 1176767 := bstep (se 1 (by rfl) ⟨882575, by rfl⟩ : syracuseStep 1176767 = 1765151) B1765151
theorem B1176935 : Blo 782338 1176935 := bstep (se 1 (by rfl) ⟨882701, by rfl⟩ : syracuseStep 1176935 = 1765403) B1765403
theorem B8943371 : Blo 782338 8943371 := bstep (se 1 (by rfl) ⟨6707528, by rfl⟩ : syracuseStep 8943371 = 13415057) B13415057
theorem B2652587 : Blo 782338 2652587 := bstep (se 1 (by rfl) ⟨1989440, by rfl⟩ : syracuseStep 2652587 = 3978881) B3978881
theorem B785711 : Blo 782338 785711 := bstep (se 1 (by rfl) ⟨589283, by rfl⟩ : syracuseStep 785711 = 1178567) B1178567
theorem B786127 : Blo 782338 786127 := bstep (se 1 (by rfl) ⟨589595, by rfl⟩ : syracuseStep 786127 = 1179191) B1179191
theorem B786279 : Blo 782338 786279 := bstep (se 1 (by rfl) ⟨589709, by rfl⟩ : syracuseStep 786279 = 1179419) B1179419
theorem B4456559 : Blo 782338 4456559 := bstep (se 1 (by rfl) ⟨3342419, by rfl⟩ : syracuseStep 4456559 = 6684839) B6684839
theorem B2229727 : Blo 782338 2229727 := bstep (se 1 (by rfl) ⟨1672295, by rfl⟩ : syracuseStep 2229727 = 3344591) B3344591
theorem B2037631 : Blo 782338 2037631 := bstep (se 1 (by rfl) ⟨1528223, by rfl⟩ : syracuseStep 2037631 = 3056447) B3056447
theorem B3353663 : Blo 782338 3353663 := bstep (se 1 (by rfl) ⟨2515247, by rfl⟩ : syracuseStep 3353663 = 5030495) B5030495
theorem B4468223 : Blo 782338 4468223 := bstep (se 1 (by rfl) ⟨3351167, by rfl⟩ : syracuseStep 4468223 = 6702335) B6702335
theorem B13583699 : Blo 782338 13583699 := bstep (se 1 (by rfl) ⟨10187774, by rfl⟩ : syracuseStep 13583699 = 20375549) B20375549
theorem B8931707 : Blo 782338 8931707 := bstep (se 1 (by rfl) ⟨6698780, by rfl⟩ : syracuseStep 8931707 = 13397561) B13397561
theorem B29053885 : Blo 782338 29053885 := bstep (se 3 (by rfl) ⟨5447603, by rfl⟩ : syracuseStep 29053885 = 10895207) B10895207
theorem B2643407 : Blo 782338 2643407 := bstep (se 1 (by rfl) ⟨1982555, by rfl⟩ : syracuseStep 2643407 = 3965111) B3965111
theorem B2643839 : Blo 782338 2643839 := bstep (se 1 (by rfl) ⟨1982879, by rfl⟩ : syracuseStep 2643839 = 3965759) B3965759
theorem B7526287 : Blo 782338 7526287 := bstep (se 1 (by rfl) ⟨5644715, by rfl⟩ : syracuseStep 7526287 = 11289431) B11289431
theorem B1988671 : Blo 782338 1988671 := bstep (se 1 (by rfl) ⟨1491503, by rfl⟩ : syracuseStep 1988671 = 2983007) B2983007
theorem B1760975 : Blo 782338 1760975 := bstep (se 1 (by rfl) ⟨1320731, by rfl⟩ : syracuseStep 1760975 = 2641463) B2641463
theorem B183820205 : Blo 782338 183820205 := bstep (se 3 (by rfl) ⟨34466288, by rfl⟩ : syracuseStep 183820205 = 68932577) B68932577
theorem B1761947 : Blo 782338 1761947 := bstep (se 1 (by rfl) ⟨1321460, by rfl⟩ : syracuseStep 1761947 = 2642921) B2642921
theorem B3762359 : Blo 782338 3762359 := bstep (se 1 (by rfl) ⟨2821769, by rfl⟩ : syracuseStep 3762359 = 5643539) B5643539
theorem B1763783 : Blo 782338 1763783 := bstep (se 1 (by rfl) ⟨1322837, by rfl⟩ : syracuseStep 1763783 = 2645675) B2645675
theorem B28602065 : Blo 782338 28602065 := bstep (se 2 (by rfl) ⟨10725774, by rfl⟩ : syracuseStep 28602065 = 21451549) B21451549
theorem B782575 : Blo 782338 782575 := bstep (se 1 (by rfl) ⟨586931, by rfl⟩ : syracuseStep 782575 = 1173863) B1173863
theorem B783327 : Blo 782338 783327 := bstep (se 1 (by rfl) ⟨587495, by rfl⟩ : syracuseStep 783327 = 1174991) B1174991
theorem B783663 : Blo 782338 783663 := bstep (se 1 (by rfl) ⟨587747, by rfl⟩ : syracuseStep 783663 = 1175495) B1175495
theorem B11302811 : Blo 782338 11302811 := bstep (se 1 (by rfl) ⟨8477108, by rfl⟩ : syracuseStep 11302811 = 16954217) B16954217
theorem B784511 : Blo 782338 784511 := bstep (se 1 (by rfl) ⟨588383, by rfl⟩ : syracuseStep 784511 = 1176767) B1176767
theorem B2259103 : Blo 782338 2259103 := bstep (se 1 (by rfl) ⟨1694327, by rfl⟩ : syracuseStep 2259103 = 3388655) B3388655
theorem B784623 : Blo 782338 784623 := bstep (se 1 (by rfl) ⟨588467, by rfl⟩ : syracuseStep 784623 = 1176935) B1176935
theorem B5962247 : Blo 782338 5962247 := bstep (se 1 (by rfl) ⟨4471685, by rfl⟩ : syracuseStep 5962247 = 8943371) B8943371
theorem B588675883 : Blo 782338 588675883 := bstep (se 1 (by rfl) ⟨441506912, by rfl⟩ : syracuseStep 588675883 = 883013825) B883013825
theorem B1768391 : Blo 782338 1768391 := bstep (se 1 (by rfl) ⟨1326293, by rfl⟩ : syracuseStep 1768391 = 2652587) B2652587
theorem B883903 : Blo 782338 883903 := bstep (se 1 (by rfl) ⟨662927, by rfl⟩ : syracuseStep 883903 = 1325855) B1325855
theorem B38738513 : Blo 782338 38738513 := bstep (se 2 (by rfl) ⟨14526942, by rfl⟩ : syracuseStep 38738513 = 29053885) B29053885
theorem B2235775 : Blo 782338 2235775 := bstep (se 1 (by rfl) ⟨1676831, by rfl⟩ : syracuseStep 2235775 = 3353663) B3353663
theorem B10035049 : Blo 782338 10035049 := bstep (se 2 (by rfl) ⟨3763143, by rfl⟩ : syracuseStep 10035049 = 7526287) B7526287
theorem B784901177 : Blo 782338 784901177 := bstep (se 2 (by rfl) ⟨294337941, by rfl⟩ : syracuseStep 784901177 = 588675883) B588675883
theorem B3974831 : Blo 782338 3974831 := bstep (se 1 (by rfl) ⟨2981123, by rfl⟩ : syracuseStep 3974831 = 5962247) B5962247
theorem B9055799 : Blo 782338 9055799 := bstep (se 1 (by rfl) ⟨6791849, by rfl⟩ : syracuseStep 9055799 = 13583699) B13583699
theorem B2508239 : Blo 782338 2508239 := bstep (se 1 (by rfl) ⟨1881179, by rfl⟩ : syracuseStep 2508239 = 3762359) B3762359
theorem B2971039 : Blo 782338 2971039 := bstep (se 1 (by rfl) ⟨2228279, by rfl⟩ : syracuseStep 2971039 = 4456559) B4456559
theorem B5954471 : Blo 782338 5954471 := bstep (se 1 (by rfl) ⟨4465853, by rfl⟩ : syracuseStep 5954471 = 8931707) B8931707
theorem B2972969 : Blo 782338 2972969 := bstep (se 2 (by rfl) ⟨1114863, by rfl⟩ : syracuseStep 2972969 = 2229727) B2229727
theorem B1762271 : Blo 782338 1762271 := bstep (se 1 (by rfl) ⟨1321703, by rfl⟩ : syracuseStep 1762271 = 2643407) B2643407
theorem B1762559 : Blo 782338 1762559 := bstep (se 1 (by rfl) ⟨1321919, by rfl⟩ : syracuseStep 1762559 = 2643839) B2643839
theorem B1173983 : Blo 782338 1173983 := bstep (se 1 (by rfl) ⟨880487, by rfl⟩ : syracuseStep 1173983 = 1760975) B1760975
theorem B122546803 : Blo 782338 122546803 := bstep (se 1 (by rfl) ⟨91910102, by rfl⟩ : syracuseStep 122546803 = 183820205) B183820205
theorem B1174631 : Blo 782338 1174631 := bstep (se 1 (by rfl) ⟨880973, by rfl⟩ : syracuseStep 1174631 = 1761947) B1761947
theorem B1175855 : Blo 782338 1175855 := bstep (se 1 (by rfl) ⟨881891, by rfl⟩ : syracuseStep 1175855 = 1763783) B1763783
theorem B2978815 : Blo 782338 2978815 := bstep (se 1 (by rfl) ⟨2234111, by rfl⟩ : syracuseStep 2978815 = 4468223) B4468223
theorem B19068043 : Blo 782338 19068043 := bstep (se 1 (by rfl) ⟨14301032, by rfl⟩ : syracuseStep 19068043 = 28602065) B28602065
theorem B2716841 : Blo 782338 2716841 := bstep (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) B2037631
theorem B2651561 : Blo 782338 2651561 := bstep (se 2 (by rfl) ⟨994335, by rfl⟩ : syracuseStep 2651561 = 1988671) B1988671
theorem B3012137 : Blo 782338 3012137 := bstep (se 2 (by rfl) ⟨1129551, by rfl⟩ : syracuseStep 3012137 = 2259103) B2259103
theorem B7535207 : Blo 782338 7535207 := bstep (se 1 (by rfl) ⟨5651405, by rfl⟩ : syracuseStep 7535207 = 11302811) B11302811
theorem B1178537 : Blo 782338 1178537 := bstep (se 2 (by rfl) ⟨441951, by rfl⟩ : syracuseStep 1178537 = 883903) B883903
theorem B1178927 : Blo 782338 1178927 := bstep (se 1 (by rfl) ⟨884195, by rfl⟩ : syracuseStep 1178927 = 1768391) B1768391
theorem B1672159 : Blo 782338 1672159 := bstep (se 1 (by rfl) ⟨1254119, by rfl⟩ : syracuseStep 1672159 = 2508239) B2508239
theorem B7244909 : Blo 782338 7244909 := bstep (se 3 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 7244909 = 2716841) B2716841
theorem B25825675 : Blo 782338 25825675 := bstep (se 1 (by rfl) ⟨19369256, by rfl⟩ : syracuseStep 25825675 = 38738513) B38738513
theorem B3969647 : Blo 782338 3969647 := bstep (se 1 (by rfl) ⟨2977235, by rfl⟩ : syracuseStep 3969647 = 5954471) B5954471
theorem B3971753 : Blo 782338 3971753 := bstep (se 2 (by rfl) ⟨1489407, by rfl⟩ : syracuseStep 3971753 = 2978815) B2978815
theorem B6037199 : Blo 782338 6037199 := bstep (se 1 (by rfl) ⟨4527899, by rfl⟩ : syracuseStep 6037199 = 9055799) B9055799
theorem B2008091 : Blo 782338 2008091 := bstep (se 1 (by rfl) ⟨1506068, by rfl⟩ : syracuseStep 2008091 = 3012137) B3012137
theorem B5023471 : Blo 782338 5023471 := bstep (se 1 (by rfl) ⟨3767603, by rfl⟩ : syracuseStep 5023471 = 7535207) B7535207
theorem B13380065 : Blo 782338 13380065 := bstep (se 2 (by rfl) ⟨5017524, by rfl⟩ : syracuseStep 13380065 = 10035049) B10035049
theorem B163395737 : Blo 782338 163395737 := bstep (se 2 (by rfl) ⟨61273401, by rfl⟩ : syracuseStep 163395737 = 122546803) B122546803
theorem B1981979 : Blo 782338 1981979 := bstep (se 1 (by rfl) ⟨1486484, by rfl⟩ : syracuseStep 1981979 = 2972969) B2972969
theorem B1174847 : Blo 782338 1174847 := bstep (se 1 (by rfl) ⟨881135, by rfl⟩ : syracuseStep 1174847 = 1762271) B1762271
theorem B523267451 : Blo 782338 523267451 := bstep (se 1 (by rfl) ⟨392450588, by rfl⟩ : syracuseStep 523267451 = 784901177) B784901177
theorem B1175039 : Blo 782338 1175039 := bstep (se 1 (by rfl) ⟨881279, by rfl⟩ : syracuseStep 1175039 = 1762559) B1762559
theorem B2649887 : Blo 782338 2649887 := bstep (se 1 (by rfl) ⟨1987415, by rfl⟩ : syracuseStep 2649887 = 3974831) B3974831
theorem B25424057 : Blo 782338 25424057 := bstep (se 2 (by rfl) ⟨9534021, by rfl⟩ : syracuseStep 25424057 = 19068043) B19068043
theorem B782655 : Blo 782338 782655 := bstep (se 1 (by rfl) ⟨586991, by rfl⟩ : syracuseStep 782655 = 1173983) B1173983
theorem B3961385 : Blo 782338 3961385 := bstep (se 2 (by rfl) ⟨1485519, by rfl⟩ : syracuseStep 3961385 = 2971039) B2971039
theorem B783087 : Blo 782338 783087 := bstep (se 1 (by rfl) ⟨587315, by rfl⟩ : syracuseStep 783087 = 1174631) B1174631
theorem B783903 : Blo 782338 783903 := bstep (se 1 (by rfl) ⟨587927, by rfl⟩ : syracuseStep 783903 = 1175855) B1175855
theorem B1767707 : Blo 782338 1767707 := bstep (se 1 (by rfl) ⟨1325780, by rfl⟩ : syracuseStep 1767707 = 2651561) B2651561
theorem B2981033 : Blo 782338 2981033 := bstep (se 2 (by rfl) ⟨1117887, by rfl⟩ : syracuseStep 2981033 = 2235775) B2235775
theorem B785691 : Blo 782338 785691 := bstep (se 1 (by rfl) ⟨589268, by rfl⟩ : syracuseStep 785691 = 1178537) B1178537
theorem B785951 : Blo 782338 785951 := bstep (se 1 (by rfl) ⟨589463, by rfl⟩ : syracuseStep 785951 = 1178927) B1178927
theorem B2229545 : Blo 782338 2229545 := bstep (se 2 (by rfl) ⟨836079, by rfl⟩ : syracuseStep 2229545 = 1672159) B1672159
theorem B8920043 : Blo 782338 8920043 := bstep (se 1 (by rfl) ⟨6690032, by rfl⟩ : syracuseStep 8920043 = 13380065) B13380065
theorem B16949371 : Blo 782338 16949371 := bstep (se 1 (by rfl) ⟨12712028, by rfl⟩ : syracuseStep 16949371 = 25424057) B25424057
theorem B108930491 : Blo 782338 108930491 := bstep (se 1 (by rfl) ⟨81697868, by rfl⟩ : syracuseStep 108930491 = 163395737) B163395737
theorem B1321319 : Blo 782338 1321319 := bstep (se 1 (by rfl) ⟨990989, by rfl⟩ : syracuseStep 1321319 = 1981979) B1981979
theorem B4829939 : Blo 782338 4829939 := bstep (se 1 (by rfl) ⟨3622454, by rfl⟩ : syracuseStep 4829939 = 7244909) B7244909
theorem B6697961 : Blo 782338 6697961 := bstep (se 2 (by rfl) ⟨2511735, by rfl⟩ : syracuseStep 6697961 = 5023471) B5023471
theorem B2640923 : Blo 782338 2640923 := bstep (se 1 (by rfl) ⟨1980692, by rfl⟩ : syracuseStep 2640923 = 3961385) B3961385
theorem B1987355 : Blo 782338 1987355 := bstep (se 1 (by rfl) ⟨1490516, by rfl⟩ : syracuseStep 1987355 = 2981033) B2981033
theorem B2646431 : Blo 782338 2646431 := bstep (se 1 (by rfl) ⟨1984823, by rfl⟩ : syracuseStep 2646431 = 3969647) B3969647
theorem B2647835 : Blo 782338 2647835 := bstep (se 1 (by rfl) ⟨1985876, by rfl⟩ : syracuseStep 2647835 = 3971753) B3971753
theorem B4024799 : Blo 782338 4024799 := bstep (se 1 (by rfl) ⟨3018599, by rfl⟩ : syracuseStep 4024799 = 6037199) B6037199
theorem B34434233 : Blo 782338 34434233 := bstep (se 2 (by rfl) ⟨12912837, by rfl⟩ : syracuseStep 34434233 = 25825675) B25825675
theorem B1338727 : Blo 782338 1338727 := bstep (se 1 (by rfl) ⟨1004045, by rfl⟩ : syracuseStep 1338727 = 2008091) B2008091
theorem B783231 : Blo 782338 783231 := bstep (se 1 (by rfl) ⟨587423, by rfl⟩ : syracuseStep 783231 = 1174847) B1174847
theorem B348844967 : Blo 782338 348844967 := bstep (se 1 (by rfl) ⟨261633725, by rfl⟩ : syracuseStep 348844967 = 523267451) B523267451
theorem B783359 : Blo 782338 783359 := bstep (se 1 (by rfl) ⟨587519, by rfl⟩ : syracuseStep 783359 = 1175039) B1175039
theorem B1766591 : Blo 782338 1766591 := bstep (se 1 (by rfl) ⟨1324943, by rfl⟩ : syracuseStep 1766591 = 2649887) B2649887
theorem B1178471 : Blo 782338 1178471 := bstep (se 1 (by rfl) ⟨883853, by rfl⟩ : syracuseStep 1178471 = 1767707) B1767707
theorem B72620327 : Blo 782338 72620327 := bstep (se 1 (by rfl) ⟨54465245, by rfl⟩ : syracuseStep 72620327 = 108930491) B108930491
theorem B3219959 : Blo 782338 3219959 := bstep (se 1 (by rfl) ⟨2414969, by rfl⟩ : syracuseStep 3219959 = 4829939) B4829939
theorem B232563311 : Blo 782338 232563311 := bstep (se 1 (by rfl) ⟨174422483, by rfl⟩ : syracuseStep 232563311 = 348844967) B348844967
theorem B4465307 : Blo 782338 4465307 := bstep (se 1 (by rfl) ⟨3348980, by rfl⟩ : syracuseStep 4465307 = 6697961) B6697961
theorem B1486363 : Blo 782338 1486363 := bstep (se 1 (by rfl) ⟨1114772, by rfl⟩ : syracuseStep 1486363 = 2229545) B2229545
theorem B1324903 : Blo 782338 1324903 := bstep (se 1 (by rfl) ⟨993677, by rfl⟩ : syracuseStep 1324903 = 1987355) B1987355
theorem B1784969 : Blo 782338 1784969 := bstep (se 2 (by rfl) ⟨669363, by rfl⟩ : syracuseStep 1784969 = 1338727) B1338727
theorem B5946695 : Blo 782338 5946695 := bstep (se 1 (by rfl) ⟨4460021, by rfl⟩ : syracuseStep 5946695 = 8920043) B8920043
theorem B22956155 : Blo 782338 22956155 := bstep (se 1 (by rfl) ⟨17217116, by rfl⟩ : syracuseStep 22956155 = 34434233) B34434233
theorem B22599161 : Blo 782338 22599161 := bstep (se 2 (by rfl) ⟨8474685, by rfl⟩ : syracuseStep 22599161 = 16949371) B16949371
theorem B1760615 : Blo 782338 1760615 := bstep (se 1 (by rfl) ⟨1320461, by rfl⟩ : syracuseStep 1760615 = 2640923) B2640923
theorem B1764287 : Blo 782338 1764287 := bstep (se 1 (by rfl) ⟨1323215, by rfl⟩ : syracuseStep 1764287 = 2646431) B2646431
theorem B1765223 : Blo 782338 1765223 := bstep (se 1 (by rfl) ⟨1323917, by rfl⟩ : syracuseStep 1765223 = 2647835) B2647835
theorem B880879 : Blo 782338 880879 := bstep (se 1 (by rfl) ⟨660659, by rfl⟩ : syracuseStep 880879 = 1321319) B1321319
theorem B2683199 : Blo 782338 2683199 := bstep (se 1 (by rfl) ⟨2012399, by rfl⟩ : syracuseStep 2683199 = 4024799) B4024799
theorem B1177727 : Blo 782338 1177727 := bstep (se 1 (by rfl) ⟨883295, by rfl⟩ : syracuseStep 1177727 = 1766591) B1766591
theorem B785647 : Blo 782338 785647 := bstep (se 1 (by rfl) ⟨589235, by rfl⟩ : syracuseStep 785647 = 1178471) B1178471
theorem B8586557 : Blo 782338 8586557 := bstep (se 3 (by rfl) ⟨1609979, by rfl⟩ : syracuseStep 8586557 = 3219959) B3219959
theorem B15304103 : Blo 782338 15304103 := bstep (se 1 (by rfl) ⟨11478077, by rfl⟩ : syracuseStep 15304103 = 22956155) B22956155
theorem B1189979 : Blo 782338 1189979 := bstep (se 1 (by rfl) ⟨892484, by rfl⟩ : syracuseStep 1189979 = 1784969) B1784969
theorem B48413551 : Blo 782338 48413551 := bstep (se 1 (by rfl) ⟨36310163, by rfl⟩ : syracuseStep 48413551 = 72620327) B72620327
theorem B1981817 : Blo 782338 1981817 := bstep (se 2 (by rfl) ⟨743181, by rfl⟩ : syracuseStep 1981817 = 1486363) B1486363
theorem B155042207 : Blo 782338 155042207 := bstep (se 1 (by rfl) ⟨116281655, by rfl⟩ : syracuseStep 155042207 = 232563311) B232563311
theorem B1788799 : Blo 782338 1788799 := bstep (se 1 (by rfl) ⟨1341599, by rfl⟩ : syracuseStep 1788799 = 2683199) B2683199
theorem B15066107 : Blo 782338 15066107 := bstep (se 1 (by rfl) ⟨11299580, by rfl⟩ : syracuseStep 15066107 = 22599161) B22599161
theorem B1173743 : Blo 782338 1173743 := bstep (se 1 (by rfl) ⟨880307, by rfl⟩ : syracuseStep 1173743 = 1760615) B1760615
theorem B1174505 : Blo 782338 1174505 := bstep (se 2 (by rfl) ⟨440439, by rfl⟩ : syracuseStep 1174505 = 880879) B880879
theorem B2976871 : Blo 782338 2976871 := bstep (se 1 (by rfl) ⟨2232653, by rfl⟩ : syracuseStep 2976871 = 4465307) B4465307
theorem B1176191 : Blo 782338 1176191 := bstep (se 1 (by rfl) ⟨882143, by rfl⟩ : syracuseStep 1176191 = 1764287) B1764287
theorem B1766537 : Blo 782338 1766537 := bstep (se 2 (by rfl) ⟨662451, by rfl⟩ : syracuseStep 1766537 = 1324903) B1324903
theorem B1176815 : Blo 782338 1176815 := bstep (se 1 (by rfl) ⟨882611, by rfl⟩ : syracuseStep 1176815 = 1765223) B1765223
theorem B785151 : Blo 782338 785151 := bstep (se 1 (by rfl) ⟨588863, by rfl⟩ : syracuseStep 785151 = 1177727) B1177727
theorem B3964463 : Blo 782338 3964463 := bstep (se 1 (by rfl) ⟨2973347, by rfl⟩ : syracuseStep 3964463 = 5946695) B5946695
theorem B3969161 : Blo 782338 3969161 := bstep (se 2 (by rfl) ⟨1488435, by rfl⟩ : syracuseStep 3969161 = 2976871) B2976871
theorem B793319 : Blo 782338 793319 := bstep (se 1 (by rfl) ⟨594989, by rfl⟩ : syracuseStep 793319 = 1189979) B1189979
theorem B1321211 : Blo 782338 1321211 := bstep (se 1 (by rfl) ⟨990908, by rfl⟩ : syracuseStep 1321211 = 1981817) B1981817
theorem B103361471 : Blo 782338 103361471 := bstep (se 1 (by rfl) ⟨77521103, by rfl⟩ : syracuseStep 103361471 = 155042207) B155042207
theorem B10202735 : Blo 782338 10202735 := bstep (se 1 (by rfl) ⟨7652051, by rfl⟩ : syracuseStep 10202735 = 15304103) B15304103
theorem B10044071 : Blo 782338 10044071 := bstep (se 1 (by rfl) ⟨7533053, by rfl⟩ : syracuseStep 10044071 = 15066107) B15066107
theorem B2642975 : Blo 782338 2642975 := bstep (se 1 (by rfl) ⟨1982231, by rfl⟩ : syracuseStep 2642975 = 3964463) B3964463
theorem B5724371 : Blo 782338 5724371 := bstep (se 1 (by rfl) ⟨4293278, by rfl⟩ : syracuseStep 5724371 = 8586557) B8586557
theorem B2385065 : Blo 782338 2385065 := bstep (se 2 (by rfl) ⟨894399, by rfl⟩ : syracuseStep 2385065 = 1788799) B1788799
theorem B782495 : Blo 782338 782495 := bstep (se 1 (by rfl) ⟨586871, by rfl⟩ : syracuseStep 782495 = 1173743) B1173743
theorem B783003 : Blo 782338 783003 := bstep (se 1 (by rfl) ⟨587252, by rfl⟩ : syracuseStep 783003 = 1174505) B1174505
theorem B784127 : Blo 782338 784127 := bstep (se 1 (by rfl) ⟨588095, by rfl⟩ : syracuseStep 784127 = 1176191) B1176191
theorem B1177691 : Blo 782338 1177691 := bstep (se 1 (by rfl) ⟨883268, by rfl⟩ : syracuseStep 1177691 = 1766537) B1766537
theorem B784543 : Blo 782338 784543 := bstep (se 1 (by rfl) ⟨588407, by rfl⟩ : syracuseStep 784543 = 1176815) B1176815
theorem B64551401 : Blo 782338 64551401 := bstep (se 2 (by rfl) ⟨24206775, by rfl⟩ : syracuseStep 64551401 = 48413551) B48413551
theorem B43034267 : Blo 782338 43034267 := bstep (se 1 (by rfl) ⟨32275700, by rfl⟩ : syracuseStep 43034267 = 64551401) B64551401
theorem B6696047 : Blo 782338 6696047 := bstep (se 1 (by rfl) ⟨5022035, by rfl⟩ : syracuseStep 6696047 = 10044071) B10044071
theorem B3816247 : Blo 782338 3816247 := bstep (se 1 (by rfl) ⟨2862185, by rfl⟩ : syracuseStep 3816247 = 5724371) B5724371
theorem B1590043 : Blo 782338 1590043 := bstep (se 1 (by rfl) ⟨1192532, by rfl⟩ : syracuseStep 1590043 = 2385065) B2385065
theorem B2115517 : Blo 782338 2115517 := bstep (se 3 (by rfl) ⟨396659, by rfl⟩ : syracuseStep 2115517 = 793319) B793319
theorem B6801823 : Blo 782338 6801823 := bstep (se 1 (by rfl) ⟨5101367, by rfl⟩ : syracuseStep 6801823 = 10202735) B10202735
theorem B2646107 : Blo 782338 2646107 := bstep (se 1 (by rfl) ⟨1984580, by rfl⟩ : syracuseStep 2646107 = 3969161) B3969161
theorem B1761983 : Blo 782338 1761983 := bstep (se 1 (by rfl) ⟨1321487, by rfl⟩ : syracuseStep 1761983 = 2642975) B2642975
theorem B880807 : Blo 782338 880807 := bstep (se 1 (by rfl) ⟨660605, by rfl⟩ : syracuseStep 880807 = 1321211) B1321211
theorem B68907647 : Blo 782338 68907647 := bstep (se 1 (by rfl) ⟨51680735, by rfl⟩ : syracuseStep 68907647 = 103361471) B103361471
theorem B785127 : Blo 782338 785127 := bstep (se 1 (by rfl) ⟨588845, by rfl⟩ : syracuseStep 785127 = 1177691) B1177691
theorem B2820689 : Blo 782338 2820689 := bstep (se 2 (by rfl) ⟨1057758, by rfl⟩ : syracuseStep 2820689 = 2115517) B2115517
theorem B4464031 : Blo 782338 4464031 := bstep (se 1 (by rfl) ⟨3348023, by rfl⟩ : syracuseStep 4464031 = 6696047) B6696047
theorem B5088329 : Blo 782338 5088329 := bstep (se 2 (by rfl) ⟨1908123, by rfl⟩ : syracuseStep 5088329 = 3816247) B3816247
theorem B28689511 : Blo 782338 28689511 := bstep (se 1 (by rfl) ⟨21517133, by rfl⟩ : syracuseStep 28689511 = 43034267) B43034267
theorem B2120057 : Blo 782338 2120057 := bstep (se 2 (by rfl) ⟨795021, by rfl⟩ : syracuseStep 2120057 = 1590043) B1590043
theorem B9069097 : Blo 782338 9069097 := bstep (se 2 (by rfl) ⟨3400911, by rfl⟩ : syracuseStep 9069097 = 6801823) B6801823
theorem B1764071 : Blo 782338 1764071 := bstep (se 1 (by rfl) ⟨1323053, by rfl⟩ : syracuseStep 1764071 = 2646107) B2646107
theorem B1174409 : Blo 782338 1174409 := bstep (se 2 (by rfl) ⟨440403, by rfl⟩ : syracuseStep 1174409 = 880807) B880807
theorem B1174655 : Blo 782338 1174655 := bstep (se 1 (by rfl) ⟨880991, by rfl⟩ : syracuseStep 1174655 = 1761983) B1761983
theorem B45938431 : Blo 782338 45938431 := bstep (se 1 (by rfl) ⟨34453823, by rfl⟩ : syracuseStep 45938431 = 68907647) B68907647
theorem B12092129 : Blo 782338 12092129 := bstep (se 2 (by rfl) ⟨4534548, by rfl⟩ : syracuseStep 12092129 = 9069097) B9069097
theorem B1413371 : Blo 782338 1413371 := bstep (se 1 (by rfl) ⟨1060028, by rfl⟩ : syracuseStep 1413371 = 2120057) B2120057
theorem B61251241 : Blo 782338 61251241 := bstep (se 2 (by rfl) ⟨22969215, by rfl⟩ : syracuseStep 61251241 = 45938431) B45938431
theorem B38252681 : Blo 782338 38252681 := bstep (se 2 (by rfl) ⟨14344755, by rfl⟩ : syracuseStep 38252681 = 28689511) B28689511
theorem B1880459 : Blo 782338 1880459 := bstep (se 1 (by rfl) ⟨1410344, by rfl⟩ : syracuseStep 1880459 = 2820689) B2820689
theorem B3392219 : Blo 782338 3392219 := bstep (se 1 (by rfl) ⟨2544164, by rfl⟩ : syracuseStep 3392219 = 5088329) B5088329
theorem B5952041 : Blo 782338 5952041 := bstep (se 2 (by rfl) ⟨2232015, by rfl⟩ : syracuseStep 5952041 = 4464031) B4464031
theorem B1176047 : Blo 782338 1176047 := bstep (se 1 (by rfl) ⟨882035, by rfl⟩ : syracuseStep 1176047 = 1764071) B1764071
theorem B782939 : Blo 782338 782939 := bstep (se 1 (by rfl) ⟨587204, by rfl⟩ : syracuseStep 782939 = 1174409) B1174409
theorem B783103 : Blo 782338 783103 := bstep (se 1 (by rfl) ⟨587327, by rfl⟩ : syracuseStep 783103 = 1174655) B1174655
theorem B2261479 : Blo 782338 2261479 := bstep (se 1 (by rfl) ⟨1696109, by rfl⟩ : syracuseStep 2261479 = 3392219) B3392219
theorem B8061419 : Blo 782338 8061419 := bstep (se 1 (by rfl) ⟨6046064, by rfl⟩ : syracuseStep 8061419 = 12092129) B12092129
theorem B3968027 : Blo 782338 3968027 := bstep (se 1 (by rfl) ⟨2976020, by rfl⟩ : syracuseStep 3968027 = 5952041) B5952041
theorem B25501787 : Blo 782338 25501787 := bstep (se 1 (by rfl) ⟨19126340, by rfl⟩ : syracuseStep 25501787 = 38252681) B38252681
theorem B1253639 : Blo 782338 1253639 := bstep (se 1 (by rfl) ⟨940229, by rfl⟩ : syracuseStep 1253639 = 1880459) B1880459
theorem B81668321 : Blo 782338 81668321 := bstep (se 2 (by rfl) ⟨30625620, by rfl⟩ : syracuseStep 81668321 = 61251241) B61251241
theorem B942247 : Blo 782338 942247 := bstep (se 1 (by rfl) ⟨706685, by rfl⟩ : syracuseStep 942247 = 1413371) B1413371
theorem B784031 : Blo 782338 784031 := bstep (se 1 (by rfl) ⟨588023, by rfl⟩ : syracuseStep 784031 = 1176047) B1176047
theorem B5374279 : Blo 782338 5374279 := bstep (se 1 (by rfl) ⟨4030709, by rfl⟩ : syracuseStep 5374279 = 8061419) B8061419
theorem B3015305 : Blo 782338 3015305 := bstep (se 2 (by rfl) ⟨1130739, by rfl⟩ : syracuseStep 3015305 = 2261479) B2261479
theorem B1256329 : Blo 782338 1256329 := bstep (se 2 (by rfl) ⟨471123, by rfl⟩ : syracuseStep 1256329 = 942247) B942247
theorem B835759 : Blo 782338 835759 := bstep (se 1 (by rfl) ⟨626819, by rfl⟩ : syracuseStep 835759 = 1253639) B1253639
theorem B54445547 : Blo 782338 54445547 := bstep (se 1 (by rfl) ⟨40834160, by rfl⟩ : syracuseStep 54445547 = 81668321) B81668321
theorem B2645351 : Blo 782338 2645351 := bstep (se 1 (by rfl) ⟨1984013, by rfl⟩ : syracuseStep 2645351 = 3968027) B3968027
theorem B17001191 : Blo 782338 17001191 := bstep (se 1 (by rfl) ⟨12750893, by rfl⟩ : syracuseStep 17001191 = 25501787) B25501787
theorem B1114345 : Blo 782338 1114345 := bstep (se 2 (by rfl) ⟨417879, by rfl⟩ : syracuseStep 1114345 = 835759) B835759
theorem B2010203 : Blo 782338 2010203 := bstep (se 1 (by rfl) ⟨1507652, by rfl⟩ : syracuseStep 2010203 = 3015305) B3015305
theorem B6700421 : Blo 782338 6700421 := bstep (se 4 (by rfl) ⟨628164, by rfl⟩ : syracuseStep 6700421 = 1256329) B1256329
theorem B7165705 : Blo 782338 7165705 := bstep (se 2 (by rfl) ⟨2687139, by rfl⟩ : syracuseStep 7165705 = 5374279) B5374279
theorem B36297031 : Blo 782338 36297031 := bstep (se 1 (by rfl) ⟨27222773, by rfl⟩ : syracuseStep 36297031 = 54445547) B54445547
theorem B1763567 : Blo 782338 1763567 := bstep (se 1 (by rfl) ⟨1322675, by rfl⟩ : syracuseStep 1763567 = 2645351) B2645351
theorem B11334127 : Blo 782338 11334127 := bstep (se 1 (by rfl) ⟨8500595, by rfl⟩ : syracuseStep 11334127 = 17001191) B17001191
theorem B15112169 : Blo 782338 15112169 := bstep (se 2 (by rfl) ⟨5667063, by rfl⟩ : syracuseStep 15112169 = 11334127) B11334127
theorem B4466947 : Blo 782338 4466947 := bstep (se 1 (by rfl) ⟨3350210, by rfl⟩ : syracuseStep 4466947 = 6700421) B6700421
theorem B1485793 : Blo 782338 1485793 := bstep (se 2 (by rfl) ⟨557172, by rfl⟩ : syracuseStep 1485793 = 1114345) B1114345
theorem B9554273 : Blo 782338 9554273 := bstep (se 2 (by rfl) ⟨3582852, by rfl⟩ : syracuseStep 9554273 = 7165705) B7165705
theorem B1175711 : Blo 782338 1175711 := bstep (se 1 (by rfl) ⟨881783, by rfl⟩ : syracuseStep 1175711 = 1763567) B1763567
theorem B1340135 : Blo 782338 1340135 := bstep (se 1 (by rfl) ⟨1005101, by rfl⟩ : syracuseStep 1340135 = 2010203) B2010203
theorem B48396041 : Blo 782338 48396041 := bstep (se 2 (by rfl) ⟨18148515, by rfl⟩ : syracuseStep 48396041 = 36297031) B36297031
theorem B893423 : Blo 782338 893423 := bstep (se 1 (by rfl) ⟨670067, by rfl⟩ : syracuseStep 893423 = 1340135) B1340135
theorem B6369515 : Blo 782338 6369515 := bstep (se 1 (by rfl) ⟨4777136, by rfl⟩ : syracuseStep 6369515 = 9554273) B9554273
theorem B1981057 : Blo 782338 1981057 := bstep (se 2 (by rfl) ⟨742896, by rfl⟩ : syracuseStep 1981057 = 1485793) B1485793
theorem B10074779 : Blo 782338 10074779 := bstep (se 1 (by rfl) ⟨7556084, by rfl⟩ : syracuseStep 10074779 = 15112169) B15112169
theorem B32264027 : Blo 782338 32264027 := bstep (se 1 (by rfl) ⟨24198020, by rfl⟩ : syracuseStep 32264027 = 48396041) B48396041
theorem B5955929 : Blo 782338 5955929 := bstep (se 2 (by rfl) ⟨2233473, by rfl⟩ : syracuseStep 5955929 = 4466947) B4466947
theorem B783807 : Blo 782338 783807 := bstep (se 1 (by rfl) ⟨587855, by rfl⟩ : syracuseStep 783807 = 1175711) B1175711
theorem B3970619 : Blo 782338 3970619 := bstep (se 1 (by rfl) ⟨2977964, by rfl⟩ : syracuseStep 3970619 = 5955929) B5955929
theorem B21509351 : Blo 782338 21509351 := bstep (se 1 (by rfl) ⟨16132013, by rfl⟩ : syracuseStep 21509351 = 32264027) B32264027
theorem B4246343 : Blo 782338 4246343 := bstep (se 1 (by rfl) ⟨3184757, by rfl⟩ : syracuseStep 4246343 = 6369515) B6369515
theorem B2641409 : Blo 782338 2641409 := bstep (se 2 (by rfl) ⟨990528, by rfl⟩ : syracuseStep 2641409 = 1981057) B1981057
theorem B2382461 : Blo 782338 2382461 := bstep (se 3 (by rfl) ⟨446711, by rfl⟩ : syracuseStep 2382461 = 893423) B893423
theorem B6716519 : Blo 782338 6716519 := bstep (se 1 (by rfl) ⟨5037389, by rfl⟩ : syracuseStep 6716519 = 10074779) B10074779
theorem B2830895 : Blo 782338 2830895 := bstep (se 1 (by rfl) ⟨2123171, by rfl⟩ : syracuseStep 2830895 = 4246343) B4246343
theorem B1588307 : Blo 782338 1588307 := bstep (se 1 (by rfl) ⟨1191230, by rfl⟩ : syracuseStep 1588307 = 2382461) B2382461
theorem B14339567 : Blo 782338 14339567 := bstep (se 1 (by rfl) ⟨10754675, by rfl⟩ : syracuseStep 14339567 = 21509351) B21509351
theorem B4477679 : Blo 782338 4477679 := bstep (se 1 (by rfl) ⟨3358259, by rfl⟩ : syracuseStep 4477679 = 6716519) B6716519
theorem B1760939 : Blo 782338 1760939 := bstep (se 1 (by rfl) ⟨1320704, by rfl⟩ : syracuseStep 1760939 = 2641409) B2641409
theorem B2647079 : Blo 782338 2647079 := bstep (se 1 (by rfl) ⟨1985309, by rfl⟩ : syracuseStep 2647079 = 3970619) B3970619
theorem B2985119 : Blo 782338 2985119 := bstep (se 1 (by rfl) ⟨2238839, by rfl⟩ : syracuseStep 2985119 = 4477679) B4477679
theorem B4235485 : Blo 782338 4235485 := bstep (se 3 (by rfl) ⟨794153, by rfl⟩ : syracuseStep 4235485 = 1588307) B1588307
theorem B1887263 : Blo 782338 1887263 := bstep (se 1 (by rfl) ⟨1415447, by rfl⟩ : syracuseStep 1887263 = 2830895) B2830895
theorem B9559711 : Blo 782338 9559711 := bstep (se 1 (by rfl) ⟨7169783, by rfl⟩ : syracuseStep 9559711 = 14339567) B14339567
theorem B1173959 : Blo 782338 1173959 := bstep (se 1 (by rfl) ⟨880469, by rfl⟩ : syracuseStep 1173959 = 1760939) B1760939
theorem B1764719 : Blo 782338 1764719 := bstep (se 1 (by rfl) ⟨1323539, by rfl⟩ : syracuseStep 1764719 = 2647079) B2647079
theorem B5647313 : Blo 782338 5647313 := bstep (se 2 (by rfl) ⟨2117742, by rfl⟩ : syracuseStep 5647313 = 4235485) B4235485
theorem B1258175 : Blo 782338 1258175 := bstep (se 1 (by rfl) ⟨943631, by rfl⟩ : syracuseStep 1258175 = 1887263) B1887263
theorem B1990079 : Blo 782338 1990079 := bstep (se 1 (by rfl) ⟨1492559, by rfl⟩ : syracuseStep 1990079 = 2985119) B2985119
theorem B782639 : Blo 782338 782639 := bstep (se 1 (by rfl) ⟨586979, by rfl⟩ : syracuseStep 782639 = 1173959) B1173959
theorem B1176479 : Blo 782338 1176479 := bstep (se 1 (by rfl) ⟨882359, by rfl⟩ : syracuseStep 1176479 = 1764719) B1764719
theorem B12746281 : Blo 782338 12746281 := bstep (se 2 (by rfl) ⟨4779855, by rfl⟩ : syracuseStep 12746281 = 9559711) B9559711
theorem B1326719 : Blo 782338 1326719 := bstep (se 1 (by rfl) ⟨995039, by rfl⟩ : syracuseStep 1326719 = 1990079) B1990079
theorem B838783 : Blo 782338 838783 := bstep (se 1 (by rfl) ⟨629087, by rfl⟩ : syracuseStep 838783 = 1258175) B1258175
theorem B16995041 : Blo 782338 16995041 := bstep (se 2 (by rfl) ⟨6373140, by rfl⟩ : syracuseStep 16995041 = 12746281) B12746281
theorem B3764875 : Blo 782338 3764875 := bstep (se 1 (by rfl) ⟨2823656, by rfl⟩ : syracuseStep 3764875 = 5647313) B5647313
theorem B784319 : Blo 782338 784319 := bstep (se 1 (by rfl) ⟨588239, by rfl⟩ : syracuseStep 784319 = 1176479) B1176479
theorem B1118377 : Blo 782338 1118377 := bstep (se 2 (by rfl) ⟨419391, by rfl⟩ : syracuseStep 1118377 = 838783) B838783
theorem B5019833 : Blo 782338 5019833 := bstep (se 2 (by rfl) ⟨1882437, by rfl⟩ : syracuseStep 5019833 = 3764875) B3764875
theorem B11330027 : Blo 782338 11330027 := bstep (se 1 (by rfl) ⟨8497520, by rfl⟩ : syracuseStep 11330027 = 16995041) B16995041
theorem B884479 : Blo 782338 884479 := bstep (se 1 (by rfl) ⟨663359, by rfl⟩ : syracuseStep 884479 = 1326719) B1326719
theorem B5964677 : Blo 782338 5964677 := bstep (se 4 (by rfl) ⟨559188, by rfl⟩ : syracuseStep 5964677 = 1118377) B1118377
theorem B3346555 : Blo 782338 3346555 := bstep (se 1 (by rfl) ⟨2509916, by rfl⟩ : syracuseStep 3346555 = 5019833) B5019833
theorem B7553351 : Blo 782338 7553351 := bstep (se 1 (by rfl) ⟨5665013, by rfl⟩ : syracuseStep 7553351 = 11330027) B11330027
theorem B1179305 : Blo 782338 1179305 := bstep (se 2 (by rfl) ⟨442239, by rfl⟩ : syracuseStep 1179305 = 884479) B884479
theorem B4462073 : Blo 782338 4462073 := bstep (se 2 (by rfl) ⟨1673277, by rfl⟩ : syracuseStep 4462073 = 3346555) B3346555
theorem B3976451 : Blo 782338 3976451 := bstep (se 1 (by rfl) ⟨2982338, by rfl⟩ : syracuseStep 3976451 = 5964677) B5964677
theorem B20142269 : Blo 782338 20142269 := bstep (se 3 (by rfl) ⟨3776675, by rfl⟩ : syracuseStep 20142269 = 7553351) B7553351
theorem B786203 : Blo 782338 786203 := bstep (se 1 (by rfl) ⟨589652, by rfl⟩ : syracuseStep 786203 = 1179305) B1179305
theorem B2974715 : Blo 782338 2974715 := bstep (se 1 (by rfl) ⟨2231036, by rfl⟩ : syracuseStep 2974715 = 4462073) B4462073
theorem B13428179 : Blo 782338 13428179 := bstep (se 1 (by rfl) ⟨10071134, by rfl⟩ : syracuseStep 13428179 = 20142269) B20142269
theorem B2650967 : Blo 782338 2650967 := bstep (se 1 (by rfl) ⟨1988225, by rfl⟩ : syracuseStep 2650967 = 3976451) B3976451
theorem B8952119 : Blo 782338 8952119 := bstep (se 1 (by rfl) ⟨6714089, by rfl⟩ : syracuseStep 8952119 = 13428179) B13428179
theorem B1983143 : Blo 782338 1983143 := bstep (se 1 (by rfl) ⟨1487357, by rfl⟩ : syracuseStep 1983143 = 2974715) B2974715
theorem B1767311 : Blo 782338 1767311 := bstep (se 1 (by rfl) ⟨1325483, by rfl⟩ : syracuseStep 1767311 = 2650967) B2650967
theorem B5968079 : Blo 782338 5968079 := bstep (se 1 (by rfl) ⟨4476059, by rfl⟩ : syracuseStep 5968079 = 8952119) B8952119
theorem B1322095 : Blo 782338 1322095 := bstep (se 1 (by rfl) ⟨991571, by rfl⟩ : syracuseStep 1322095 = 1983143) B1983143
theorem B1178207 : Blo 782338 1178207 := bstep (se 1 (by rfl) ⟨883655, by rfl⟩ : syracuseStep 1178207 = 1767311) B1767311
theorem B3978719 : Blo 782338 3978719 := bstep (se 1 (by rfl) ⟨2984039, by rfl⟩ : syracuseStep 3978719 = 5968079) B5968079
theorem B1762793 : Blo 782338 1762793 := bstep (se 2 (by rfl) ⟨661047, by rfl⟩ : syracuseStep 1762793 = 1322095) B1322095
theorem B785471 : Blo 782338 785471 := bstep (se 1 (by rfl) ⟨589103, by rfl⟩ : syracuseStep 785471 = 1178207) B1178207
theorem B1175195 : Blo 782338 1175195 := bstep (se 1 (by rfl) ⟨881396, by rfl⟩ : syracuseStep 1175195 = 1762793) B1762793
theorem B2652479 : Blo 782338 2652479 := bstep (se 1 (by rfl) ⟨1989359, by rfl⟩ : syracuseStep 2652479 = 3978719) B3978719
theorem B783463 : Blo 782338 783463 := bstep (se 1 (by rfl) ⟨587597, by rfl⟩ : syracuseStep 783463 = 1175195) B1175195
theorem B1768319 : Blo 782338 1768319 := bstep (se 1 (by rfl) ⟨1326239, by rfl⟩ : syracuseStep 1768319 = 2652479) B2652479
theorem B1178879 : Blo 782338 1178879 := bstep (se 1 (by rfl) ⟨884159, by rfl⟩ : syracuseStep 1178879 = 1768319) B1768319
theorem B785919 : Blo 782338 785919 := bstep (se 1 (by rfl) ⟨589439, by rfl⟩ : syracuseStep 785919 = 1178879) B1178879

theorem C0 (j : ℕ) (h1 : 195584 ≤ j) (h2 : j ≤ 196283) : Blo 782338 (4 * j + 3) := by
  interval_cases j
  · exact B782339
  · exact B782343
  · exact B782347
  · exact B782351
  · exact B782355
  · exact B782359
  · exact B782363
  · exact B782367
  · exact B782371
  · exact B782375
  · exact B782379
  · exact B782383
  · exact B782387
  · exact B782391
  · exact B782395
  · exact B782399
  · exact B782403
  · exact B782407
  · exact B782411
  · exact B782415
  · exact B782419
  · exact B782423
  · exact B782427
  · exact B782431
  · exact B782435
  · exact B782439
  · exact B782443
  · exact B782447
  · exact B782451
  · exact B782455
  · exact B782459
  · exact B782463
  · exact B782467
  · exact B782471
  · exact B782475
  · exact B782479
  · exact B782483
  · exact B782487
  · exact B782491
  · exact B782495
  · exact B782499
  · exact B782503
  · exact B782507
  · exact B782511
  · exact B782515
  · exact B782519
  · exact B782523
  · exact B782527
  · exact B782531
  · exact B782535
  · exact B782539
  · exact B782543
  · exact B782547
  · exact B782551
  · exact B782555
  · exact B782559
  · exact B782563
  · exact B782567
  · exact B782571
  · exact B782575
  · exact B782579
  · exact B782583
  · exact B782587
  · exact B782591
  · exact B782595
  · exact B782599
  · exact B782603
  · exact B782607
  · exact B782611
  · exact B782615
  · exact B782619
  · exact B782623
  · exact B782627
  · exact B782631
  · exact B782635
  · exact B782639
  · exact B782643
  · exact B782647
  · exact B782651
  · exact B782655
  · exact B782659
  · exact B782663
  · exact B782667
  · exact B782671
  · exact B782675
  · exact B782679
  · exact B782683
  · exact B782687
  · exact B782691
  · exact B782695
  · exact B782699
  · exact B782703
  · exact B782707
  · exact B782711
  · exact B782715
  · exact B782719
  · exact B782723
  · exact B782727
  · exact B782731
  · exact B782735
  · exact B782739
  · exact B782743
  · exact B782747
  · exact B782751
  · exact B782755
  · exact B782759
  · exact B782763
  · exact B782767
  · exact B782771
  · exact B782775
  · exact B782779
  · exact B782783
  · exact B782787
  · exact B782791
  · exact B782795
  · exact B782799
  · exact B782803
  · exact B782807
  · exact B782811
  · exact B782815
  · exact B782819
  · exact B782823
  · exact B782827
  · exact B782831
  · exact B782835
  · exact B782839
  · exact B782843
  · exact B782847
  · exact B782851
  · exact B782855
  · exact B782859
  · exact B782863
  · exact B782867
  · exact B782871
  · exact B782875
  · exact B782879
  · exact B782883
  · exact B782887
  · exact B782891
  · exact B782895
  · exact B782899
  · exact B782903
  · exact B782907
  · exact B782911
  · exact B782915
  · exact B782919
  · exact B782923
  · exact B782927
  · exact B782931
  · exact B782935
  · exact B782939
  · exact B782943
  · exact B782947
  · exact B782951
  · exact B782955
  · exact B782959
  · exact B782963
  · exact B782967
  · exact B782971
  · exact B782975
  · exact B782979
  · exact B782983
  · exact B782987
  · exact B782991
  · exact B782995
  · exact B782999
  · exact B783003
  · exact B783007
  · exact B783011
  · exact B783015
  · exact B783019
  · exact B783023
  · exact B783027
  · exact B783031
  · exact B783035
  · exact B783039
  · exact B783043
  · exact B783047
  · exact B783051
  · exact B783055
  · exact B783059
  · exact B783063
  · exact B783067
  · exact B783071
  · exact B783075
  · exact B783079
  · exact B783083
  · exact B783087
  · exact B783091
  · exact B783095
  · exact B783099
  · exact B783103
  · exact B783107
  · exact B783111
  · exact B783115
  · exact B783119
  · exact B783123
  · exact B783127
  · exact B783131
  · exact B783135
  · exact B783139
  · exact B783143
  · exact B783147
  · exact B783151
  · exact B783155
  · exact B783159
  · exact B783163
  · exact B783167
  · exact B783171
  · exact B783175
  · exact B783179
  · exact B783183
  · exact B783187
  · exact B783191
  · exact B783195
  · exact B783199
  · exact B783203
  · exact B783207
  · exact B783211
  · exact B783215
  · exact B783219
  · exact B783223
  · exact B783227
  · exact B783231
  · exact B783235
  · exact B783239
  · exact B783243
  · exact B783247
  · exact B783251
  · exact B783255
  · exact B783259
  · exact B783263
  · exact B783267
  · exact B783271
  · exact B783275
  · exact B783279
  · exact B783283
  · exact B783287
  · exact B783291
  · exact B783295
  · exact B783299
  · exact B783303
  · exact B783307
  · exact B783311
  · exact B783315
  · exact B783319
  · exact B783323
  · exact B783327
  · exact B783331
  · exact B783335
  · exact B783339
  · exact B783343
  · exact B783347
  · exact B783351
  · exact B783355
  · exact B783359
  · exact B783363
  · exact B783367
  · exact B783371
  · exact B783375
  · exact B783379
  · exact B783383
  · exact B783387
  · exact B783391
  · exact B783395
  · exact B783399
  · exact B783403
  · exact B783407
  · exact B783411
  · exact B783415
  · exact B783419
  · exact B783423
  · exact B783427
  · exact B783431
  · exact B783435
  · exact B783439
  · exact B783443
  · exact B783447
  · exact B783451
  · exact B783455
  · exact B783459
  · exact B783463
  · exact B783467
  · exact B783471
  · exact B783475
  · exact B783479
  · exact B783483
  · exact B783487
  · exact B783491
  · exact B783495
  · exact B783499
  · exact B783503
  · exact B783507
  · exact B783511
  · exact B783515
  · exact B783519
  · exact B783523
  · exact B783527
  · exact B783531
  · exact B783535
  · exact B783539
  · exact B783543
  · exact B783547
  · exact B783551
  · exact B783555
  · exact B783559
  · exact B783563
  · exact B783567
  · exact B783571
  · exact B783575
  · exact B783579
  · exact B783583
  · exact B783587
  · exact B783591
  · exact B783595
  · exact B783599
  · exact B783603
  · exact B783607
  · exact B783611
  · exact B783615
  · exact B783619
  · exact B783623
  · exact B783627
  · exact B783631
  · exact B783635
  · exact B783639
  · exact B783643
  · exact B783647
  · exact B783651
  · exact B783655
  · exact B783659
  · exact B783663
  · exact B783667
  · exact B783671
  · exact B783675
  · exact B783679
  · exact B783683
  · exact B783687
  · exact B783691
  · exact B783695
  · exact B783699
  · exact B783703
  · exact B783707
  · exact B783711
  · exact B783715
  · exact B783719
  · exact B783723
  · exact B783727
  · exact B783731
  · exact B783735
  · exact B783739
  · exact B783743
  · exact B783747
  · exact B783751
  · exact B783755
  · exact B783759
  · exact B783763
  · exact B783767
  · exact B783771
  · exact B783775
  · exact B783779
  · exact B783783
  · exact B783787
  · exact B783791
  · exact B783795
  · exact B783799
  · exact B783803
  · exact B783807
  · exact B783811
  · exact B783815
  · exact B783819
  · exact B783823
  · exact B783827
  · exact B783831
  · exact B783835
  · exact B783839
  · exact B783843
  · exact B783847
  · exact B783851
  · exact B783855
  · exact B783859
  · exact B783863
  · exact B783867
  · exact B783871
  · exact B783875
  · exact B783879
  · exact B783883
  · exact B783887
  · exact B783891
  · exact B783895
  · exact B783899
  · exact B783903
  · exact B783907
  · exact B783911
  · exact B783915
  · exact B783919
  · exact B783923
  · exact B783927
  · exact B783931
  · exact B783935
  · exact B783939
  · exact B783943
  · exact B783947
  · exact B783951
  · exact B783955
  · exact B783959
  · exact B783963
  · exact B783967
  · exact B783971
  · exact B783975
  · exact B783979
  · exact B783983
  · exact B783987
  · exact B783991
  · exact B783995
  · exact B783999
  · exact B784003
  · exact B784007
  · exact B784011
  · exact B784015
  · exact B784019
  · exact B784023
  · exact B784027
  · exact B784031
  · exact B784035
  · exact B784039
  · exact B784043
  · exact B784047
  · exact B784051
  · exact B784055
  · exact B784059
  · exact B784063
  · exact B784067
  · exact B784071
  · exact B784075
  · exact B784079
  · exact B784083
  · exact B784087
  · exact B784091
  · exact B784095
  · exact B784099
  · exact B784103
  · exact B784107
  · exact B784111
  · exact B784115
  · exact B784119
  · exact B784123
  · exact B784127
  · exact B784131
  · exact B784135
  · exact B784139
  · exact B784143
  · exact B784147
  · exact B784151
  · exact B784155
  · exact B784159
  · exact B784163
  · exact B784167
  · exact B784171
  · exact B784175
  · exact B784179
  · exact B784183
  · exact B784187
  · exact B784191
  · exact B784195
  · exact B784199
  · exact B784203
  · exact B784207
  · exact B784211
  · exact B784215
  · exact B784219
  · exact B784223
  · exact B784227
  · exact B784231
  · exact B784235
  · exact B784239
  · exact B784243
  · exact B784247
  · exact B784251
  · exact B784255
  · exact B784259
  · exact B784263
  · exact B784267
  · exact B784271
  · exact B784275
  · exact B784279
  · exact B784283
  · exact B784287
  · exact B784291
  · exact B784295
  · exact B784299
  · exact B784303
  · exact B784307
  · exact B784311
  · exact B784315
  · exact B784319
  · exact B784323
  · exact B784327
  · exact B784331
  · exact B784335
  · exact B784339
  · exact B784343
  · exact B784347
  · exact B784351
  · exact B784355
  · exact B784359
  · exact B784363
  · exact B784367
  · exact B784371
  · exact B784375
  · exact B784379
  · exact B784383
  · exact B784387
  · exact B784391
  · exact B784395
  · exact B784399
  · exact B784403
  · exact B784407
  · exact B784411
  · exact B784415
  · exact B784419
  · exact B784423
  · exact B784427
  · exact B784431
  · exact B784435
  · exact B784439
  · exact B784443
  · exact B784447
  · exact B784451
  · exact B784455
  · exact B784459
  · exact B784463
  · exact B784467
  · exact B784471
  · exact B784475
  · exact B784479
  · exact B784483
  · exact B784487
  · exact B784491
  · exact B784495
  · exact B784499
  · exact B784503
  · exact B784507
  · exact B784511
  · exact B784515
  · exact B784519
  · exact B784523
  · exact B784527
  · exact B784531
  · exact B784535
  · exact B784539
  · exact B784543
  · exact B784547
  · exact B784551
  · exact B784555
  · exact B784559
  · exact B784563
  · exact B784567
  · exact B784571
  · exact B784575
  · exact B784579
  · exact B784583
  · exact B784587
  · exact B784591
  · exact B784595
  · exact B784599
  · exact B784603
  · exact B784607
  · exact B784611
  · exact B784615
  · exact B784619
  · exact B784623
  · exact B784627
  · exact B784631
  · exact B784635
  · exact B784639
  · exact B784643
  · exact B784647
  · exact B784651
  · exact B784655
  · exact B784659
  · exact B784663
  · exact B784667
  · exact B784671
  · exact B784675
  · exact B784679
  · exact B784683
  · exact B784687
  · exact B784691
  · exact B784695
  · exact B784699
  · exact B784703
  · exact B784707
  · exact B784711
  · exact B784715
  · exact B784719
  · exact B784723
  · exact B784727
  · exact B784731
  · exact B784735
  · exact B784739
  · exact B784743
  · exact B784747
  · exact B784751
  · exact B784755
  · exact B784759
  · exact B784763
  · exact B784767
  · exact B784771
  · exact B784775
  · exact B784779
  · exact B784783
  · exact B784787
  · exact B784791
  · exact B784795
  · exact B784799
  · exact B784803
  · exact B784807
  · exact B784811
  · exact B784815
  · exact B784819
  · exact B784823
  · exact B784827
  · exact B784831
  · exact B784835
  · exact B784839
  · exact B784843
  · exact B784847
  · exact B784851
  · exact B784855
  · exact B784859
  · exact B784863
  · exact B784867
  · exact B784871
  · exact B784875
  · exact B784879
  · exact B784883
  · exact B784887
  · exact B784891
  · exact B784895
  · exact B784899
  · exact B784903
  · exact B784907
  · exact B784911
  · exact B784915
  · exact B784919
  · exact B784923
  · exact B784927
  · exact B784931
  · exact B784935
  · exact B784939
  · exact B784943
  · exact B784947
  · exact B784951
  · exact B784955
  · exact B784959
  · exact B784963
  · exact B784967
  · exact B784971
  · exact B784975
  · exact B784979
  · exact B784983
  · exact B784987
  · exact B784991
  · exact B784995
  · exact B784999
  · exact B785003
  · exact B785007
  · exact B785011
  · exact B785015
  · exact B785019
  · exact B785023
  · exact B785027
  · exact B785031
  · exact B785035
  · exact B785039
  · exact B785043
  · exact B785047
  · exact B785051
  · exact B785055
  · exact B785059
  · exact B785063
  · exact B785067
  · exact B785071
  · exact B785075
  · exact B785079
  · exact B785083
  · exact B785087
  · exact B785091
  · exact B785095
  · exact B785099
  · exact B785103
  · exact B785107
  · exact B785111
  · exact B785115
  · exact B785119
  · exact B785123
  · exact B785127
  · exact B785131
  · exact B785135

theorem C1 (j : ℕ) (h1 : 196284 ≤ j) (h2 : j ≤ 196583) : Blo 782338 (4 * j + 3) := by
  interval_cases j
  · exact B785139
  · exact B785143
  · exact B785147
  · exact B785151
  · exact B785155
  · exact B785159
  · exact B785163
  · exact B785167
  · exact B785171
  · exact B785175
  · exact B785179
  · exact B785183
  · exact B785187
  · exact B785191
  · exact B785195
  · exact B785199
  · exact B785203
  · exact B785207
  · exact B785211
  · exact B785215
  · exact B785219
  · exact B785223
  · exact B785227
  · exact B785231
  · exact B785235
  · exact B785239
  · exact B785243
  · exact B785247
  · exact B785251
  · exact B785255
  · exact B785259
  · exact B785263
  · exact B785267
  · exact B785271
  · exact B785275
  · exact B785279
  · exact B785283
  · exact B785287
  · exact B785291
  · exact B785295
  · exact B785299
  · exact B785303
  · exact B785307
  · exact B785311
  · exact B785315
  · exact B785319
  · exact B785323
  · exact B785327
  · exact B785331
  · exact B785335
  · exact B785339
  · exact B785343
  · exact B785347
  · exact B785351
  · exact B785355
  · exact B785359
  · exact B785363
  · exact B785367
  · exact B785371
  · exact B785375
  · exact B785379
  · exact B785383
  · exact B785387
  · exact B785391
  · exact B785395
  · exact B785399
  · exact B785403
  · exact B785407
  · exact B785411
  · exact B785415
  · exact B785419
  · exact B785423
  · exact B785427
  · exact B785431
  · exact B785435
  · exact B785439
  · exact B785443
  · exact B785447
  · exact B785451
  · exact B785455
  · exact B785459
  · exact B785463
  · exact B785467
  · exact B785471
  · exact B785475
  · exact B785479
  · exact B785483
  · exact B785487
  · exact B785491
  · exact B785495
  · exact B785499
  · exact B785503
  · exact B785507
  · exact B785511
  · exact B785515
  · exact B785519
  · exact B785523
  · exact B785527
  · exact B785531
  · exact B785535
  · exact B785539
  · exact B785543
  · exact B785547
  · exact B785551
  · exact B785555
  · exact B785559
  · exact B785563
  · exact B785567
  · exact B785571
  · exact B785575
  · exact B785579
  · exact B785583
  · exact B785587
  · exact B785591
  · exact B785595
  · exact B785599
  · exact B785603
  · exact B785607
  · exact B785611
  · exact B785615
  · exact B785619
  · exact B785623
  · exact B785627
  · exact B785631
  · exact B785635
  · exact B785639
  · exact B785643
  · exact B785647
  · exact B785651
  · exact B785655
  · exact B785659
  · exact B785663
  · exact B785667
  · exact B785671
  · exact B785675
  · exact B785679
  · exact B785683
  · exact B785687
  · exact B785691
  · exact B785695
  · exact B785699
  · exact B785703
  · exact B785707
  · exact B785711
  · exact B785715
  · exact B785719
  · exact B785723
  · exact B785727
  · exact B785731
  · exact B785735
  · exact B785739
  · exact B785743
  · exact B785747
  · exact B785751
  · exact B785755
  · exact B785759
  · exact B785763
  · exact B785767
  · exact B785771
  · exact B785775
  · exact B785779
  · exact B785783
  · exact B785787
  · exact B785791
  · exact B785795
  · exact B785799
  · exact B785803
  · exact B785807
  · exact B785811
  · exact B785815
  · exact B785819
  · exact B785823
  · exact B785827
  · exact B785831
  · exact B785835
  · exact B785839
  · exact B785843
  · exact B785847
  · exact B785851
  · exact B785855
  · exact B785859
  · exact B785863
  · exact B785867
  · exact B785871
  · exact B785875
  · exact B785879
  · exact B785883
  · exact B785887
  · exact B785891
  · exact B785895
  · exact B785899
  · exact B785903
  · exact B785907
  · exact B785911
  · exact B785915
  · exact B785919
  · exact B785923
  · exact B785927
  · exact B785931
  · exact B785935
  · exact B785939
  · exact B785943
  · exact B785947
  · exact B785951
  · exact B785955
  · exact B785959
  · exact B785963
  · exact B785967
  · exact B785971
  · exact B785975
  · exact B785979
  · exact B785983
  · exact B785987
  · exact B785991
  · exact B785995
  · exact B785999
  · exact B786003
  · exact B786007
  · exact B786011
  · exact B786015
  · exact B786019
  · exact B786023
  · exact B786027
  · exact B786031
  · exact B786035
  · exact B786039
  · exact B786043
  · exact B786047
  · exact B786051
  · exact B786055
  · exact B786059
  · exact B786063
  · exact B786067
  · exact B786071
  · exact B786075
  · exact B786079
  · exact B786083
  · exact B786087
  · exact B786091
  · exact B786095
  · exact B786099
  · exact B786103
  · exact B786107
  · exact B786111
  · exact B786115
  · exact B786119
  · exact B786123
  · exact B786127
  · exact B786131
  · exact B786135
  · exact B786139
  · exact B786143
  · exact B786147
  · exact B786151
  · exact B786155
  · exact B786159
  · exact B786163
  · exact B786167
  · exact B786171
  · exact B786175
  · exact B786179
  · exact B786183
  · exact B786187
  · exact B786191
  · exact B786195
  · exact B786199
  · exact B786203
  · exact B786207
  · exact B786211
  · exact B786215
  · exact B786219
  · exact B786223
  · exact B786227
  · exact B786231
  · exact B786235
  · exact B786239
  · exact B786243
  · exact B786247
  · exact B786251
  · exact B786255
  · exact B786259
  · exact B786263
  · exact B786267
  · exact B786271
  · exact B786275
  · exact B786279
  · exact B786283
  · exact B786287
  · exact B786291
  · exact B786295
  · exact B786299
  · exact B786303
  · exact B786307
  · exact B786311
  · exact B786315
  · exact B786319
  · exact B786323
  · exact B786327
  · exact B786331
  · exact B786335

theorem solution (m : ℕ) (hlo : 782338 ≤ m) (hhi : m ≤ 786338) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 195584 ≤ j := by omega
    have hj2 : j ≤ 196583 := by omega
    have hb : Blo 782338 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 196284 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
