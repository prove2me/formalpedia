-- Prove2me | solution 1 for syracuse_descends_range_1688044_1690044
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:23:37.425143+00:00
-- url     : https://prove2.me/submissions/fe1ea704-930f-4859-bea4-0e9025c09949

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


theorem B1900561 : Blo 1688044 1900561 := bbase (se 2 (by rfl) ⟨712710, by rfl⟩ : syracuseStep 1900561 = 1425421) (by norm_num)
theorem B4276253 : Blo 1688044 4276253 := bbase (se 3 (by rfl) ⟨801797, by rfl⟩ : syracuseStep 4276253 = 1603595) (by norm_num)
theorem B1925165 : Blo 1688044 1925165 := bbase (se 3 (by rfl) ⟨360968, by rfl⟩ : syracuseStep 1925165 = 721937) (by norm_num)
theorem B2850869 : Blo 1688044 2850869 := bbase (se 5 (by rfl) ⟨133634, by rfl⟩ : syracuseStep 2850869 = 267269) (by norm_num)
theorem B1900597 : Blo 1688044 1900597 := bbase (se 5 (by rfl) ⟨89090, by rfl⟩ : syracuseStep 1900597 = 178181) (by norm_num)
theorem B3801149 : Blo 1688044 3801149 := bbase (se 3 (by rfl) ⟨712715, by rfl⟩ : syracuseStep 3801149 = 1425431) (by norm_num)
theorem B2138177 : Blo 1688044 2138177 := bbase (se 2 (by rfl) ⟨801816, by rfl⟩ : syracuseStep 2138177 = 1603633) (by norm_num)
theorem B7217221 : Blo 1688044 7217221 := bbase (se 4 (by rfl) ⟨676614, by rfl⟩ : syracuseStep 7217221 = 1353229) (by norm_num)
theorem B1925201 : Blo 1688044 1925201 := bbase (se 2 (by rfl) ⟨721950, by rfl⟩ : syracuseStep 1925201 = 1443901) (by norm_num)
theorem B7217237 : Blo 1688044 7217237 := bbase (se 8 (by rfl) ⟨42288, by rfl⟩ : syracuseStep 7217237 = 84577) (by norm_num)
theorem B1900633 : Blo 1688044 1900633 := bbase (se 2 (by rfl) ⟨712737, by rfl⟩ : syracuseStep 1900633 = 1425475) (by norm_num)
theorem B2138233 : Blo 1688044 2138233 := bbase (se 2 (by rfl) ⟨801837, by rfl⟩ : syracuseStep 2138233 = 1603675) (by norm_num)
theorem B1900669 : Blo 1688044 1900669 := bbase (se 3 (by rfl) ⟨356375, by rfl⟩ : syracuseStep 1900669 = 712751) (by norm_num)
theorem B3801221 : Blo 1688044 3801221 := bbase (se 4 (by rfl) ⟨356364, by rfl⟩ : syracuseStep 3801221 = 712729) (by norm_num)
theorem B1900705 : Blo 1688044 1900705 := bbase (se 2 (by rfl) ⟨712764, by rfl⟩ : syracuseStep 1900705 = 1425529) (by norm_num)
theorem B2850997 : Blo 1688044 2850997 := bbase (se 5 (by rfl) ⟨133640, by rfl⟩ : syracuseStep 2850997 = 267281) (by norm_num)
theorem B1900741 : Blo 1688044 1900741 := bbase (se 4 (by rfl) ⟨178194, by rfl⟩ : syracuseStep 1900741 = 356389) (by norm_num)
theorem B3801293 : Blo 1688044 3801293 := bbase (se 3 (by rfl) ⟨712742, by rfl⟩ : syracuseStep 3801293 = 1425485) (by norm_num)
theorem B9126101 : Blo 1688044 9126101 := bbase (se 7 (by rfl) ⟨106946, by rfl⟩ : syracuseStep 9126101 = 213893) (by norm_num)
theorem B2138329 : Blo 1688044 2138329 := bbase (se 2 (by rfl) ⟨801873, by rfl⟩ : syracuseStep 2138329 = 1603747) (by norm_num)
theorem B1900777 : Blo 1688044 1900777 := bbase (se 2 (by rfl) ⟨712791, by rfl⟩ : syracuseStep 1900777 = 1425583) (by norm_num)
theorem B1712377 : Blo 1688044 1712377 := bbase (se 2 (by rfl) ⟨642141, by rfl⟩ : syracuseStep 1712377 = 1284283) (by norm_num)
theorem B3424525 : Blo 1688044 3424525 := bbase (se 3 (by rfl) ⟨642098, by rfl⟩ : syracuseStep 3424525 = 1284197) (by norm_num)
theorem B2851085 : Blo 1688044 2851085 := bbase (se 3 (by rfl) ⟨534578, by rfl⟩ : syracuseStep 2851085 = 1069157) (by norm_num)
theorem B1900813 : Blo 1688044 1900813 := bbase (se 3 (by rfl) ⟨356402, by rfl⟩ : syracuseStep 1900813 = 712805) (by norm_num)
theorem B3801365 : Blo 1688044 3801365 := bbase (se 6 (by rfl) ⟨89094, by rfl⟩ : syracuseStep 3801365 = 178189) (by norm_num)
theorem B1900849 : Blo 1688044 1900849 := bbase (se 2 (by rfl) ⟨712818, by rfl⟩ : syracuseStep 1900849 = 1425637) (by norm_num)
theorem B33497429 : Blo 1688044 33497429 := bbase (se 10 (by rfl) ⟨49068, by rfl⟩ : syracuseStep 33497429 = 98137) (by norm_num)
theorem B8552789 : Blo 1688044 8552789 := bbase (se 10 (by rfl) ⟨12528, by rfl⟩ : syracuseStep 8552789 = 25057) (by norm_num)
theorem B1900885 : Blo 1688044 1900885 := bbase (se 10 (by rfl) ⟨2784, by rfl⟩ : syracuseStep 1900885 = 5569) (by norm_num)
theorem B3801437 : Blo 1688044 3801437 := bbase (se 3 (by rfl) ⟨712769, by rfl⟩ : syracuseStep 3801437 = 1425539) (by norm_num)
theorem B2056549 : Blo 1688044 2056549 := bbase (se 4 (by rfl) ⟨192801, by rfl⟩ : syracuseStep 2056549 = 385603) (by norm_num)
theorem B4809077 : Blo 1688044 4809077 := bbase (se 5 (by rfl) ⟨225425, by rfl⟩ : syracuseStep 4809077 = 450851) (by norm_num)
theorem B4276597 : Blo 1688044 4276597 := bbase (se 5 (by rfl) ⟨200465, by rfl⟩ : syracuseStep 4276597 = 400931) (by norm_num)
theorem B1900921 : Blo 1688044 1900921 := bbase (se 2 (by rfl) ⟨712845, by rfl⟩ : syracuseStep 1900921 = 1425691) (by norm_num)
theorem B5702021 : Blo 1688044 5702021 := bbase (se 4 (by rfl) ⟨534564, by rfl⟩ : syracuseStep 5702021 = 1069129) (by norm_num)
theorem B2138501 : Blo 1688044 2138501 := bbase (se 4 (by rfl) ⟨200484, by rfl⟩ : syracuseStep 2138501 = 400969) (by norm_num)
theorem B2851213 : Blo 1688044 2851213 := bbase (se 3 (by rfl) ⟨534602, by rfl⟩ : syracuseStep 2851213 = 1069205) (by norm_num)
theorem B1900957 : Blo 1688044 1900957 := bbase (se 3 (by rfl) ⟨356429, by rfl⟩ : syracuseStep 1900957 = 712859) (by norm_num)
theorem B3801509 : Blo 1688044 3801509 := bbase (se 4 (by rfl) ⟨356391, by rfl⟩ : syracuseStep 3801509 = 712783) (by norm_num)
theorem B1802665 : Blo 1688044 1802665 := bbase (se 2 (by rfl) ⟨675999, by rfl⟩ : syracuseStep 1802665 = 1351999) (by norm_num)
theorem B1802669 : Blo 1688044 1802669 := bbase (se 3 (by rfl) ⟨338000, by rfl⟩ : syracuseStep 1802669 = 676001) (by norm_num)
theorem B2138557 : Blo 1688044 2138557 := bbase (se 3 (by rfl) ⟨400979, by rfl⟩ : syracuseStep 2138557 = 801959) (by norm_num)
theorem B1900993 : Blo 1688044 1900993 := bbase (se 2 (by rfl) ⟨712872, by rfl⟩ : syracuseStep 1900993 = 1425745) (by norm_num)
theorem B6414821 : Blo 1688044 6414821 := bbase (se 4 (by rfl) ⟨601389, by rfl⟩ : syracuseStep 6414821 = 1202779) (by norm_num)
theorem B4276709 : Blo 1688044 4276709 := bbase (se 4 (by rfl) ⟨400941, by rfl⟩ : syracuseStep 4276709 = 801883) (by norm_num)
theorem B2851301 : Blo 1688044 2851301 := bbase (se 4 (by rfl) ⟨267309, by rfl⟩ : syracuseStep 2851301 = 534619) (by norm_num)
theorem B1901029 : Blo 1688044 1901029 := bbase (se 4 (by rfl) ⟨178221, by rfl⟩ : syracuseStep 1901029 = 356443) (by norm_num)
theorem B3801581 : Blo 1688044 3801581 := bbase (se 3 (by rfl) ⟨712796, by rfl⟩ : syracuseStep 3801581 = 1425593) (by norm_num)
theorem B1901065 : Blo 1688044 1901065 := bbase (se 2 (by rfl) ⟨712899, by rfl⟩ : syracuseStep 1901065 = 1425799) (by norm_num)
theorem B2138653 : Blo 1688044 2138653 := bbase (se 3 (by rfl) ⟨400997, by rfl⟩ : syracuseStep 2138653 = 801995) (by norm_num)
theorem B1901101 : Blo 1688044 1901101 := bbase (se 3 (by rfl) ⟨356456, by rfl⟩ : syracuseStep 1901101 = 712913) (by norm_num)
theorem B3801653 : Blo 1688044 3801653 := bbase (se 5 (by rfl) ⟨178202, by rfl⟩ : syracuseStep 3801653 = 356405) (by norm_num)
theorem B7316021 : Blo 1688044 7316021 := bbase (se 5 (by rfl) ⟨342938, by rfl⟩ : syracuseStep 7316021 = 685877) (by norm_num)
theorem B1901137 : Blo 1688044 1901137 := bbase (se 2 (by rfl) ⟨712926, by rfl⟩ : syracuseStep 1901137 = 1425853) (by norm_num)
theorem B3293789 : Blo 1688044 3293789 := bbase (se 3 (by rfl) ⟨617585, by rfl⟩ : syracuseStep 3293789 = 1235171) (by norm_num)
theorem B2851429 : Blo 1688044 2851429 := bbase (se 4 (by rfl) ⟨267321, by rfl⟩ : syracuseStep 2851429 = 534643) (by norm_num)
theorem B1901173 : Blo 1688044 1901173 := bbase (se 5 (by rfl) ⟨89117, by rfl⟩ : syracuseStep 1901173 = 178235) (by norm_num)
theorem B3801725 : Blo 1688044 3801725 := bbase (se 3 (by rfl) ⟨712823, by rfl⟩ : syracuseStep 3801725 = 1425647) (by norm_num)
theorem B1901209 : Blo 1688044 1901209 := bbase (se 2 (by rfl) ⟨712953, by rfl⟩ : syracuseStep 1901209 = 1425907) (by norm_num)
theorem B3424933 : Blo 1688044 3424933 := bbase (se 4 (by rfl) ⟨321087, by rfl⟩ : syracuseStep 3424933 = 642175) (by norm_num)
theorem B4276901 : Blo 1688044 4276901 := bbase (se 4 (by rfl) ⟨400959, by rfl⟩ : syracuseStep 4276901 = 801919) (by norm_num)
theorem B2851517 : Blo 1688044 2851517 := bbase (se 3 (by rfl) ⟨534659, by rfl⟩ : syracuseStep 2851517 = 1069319) (by norm_num)
theorem B1901245 : Blo 1688044 1901245 := bbase (se 3 (by rfl) ⟨356483, by rfl⟩ : syracuseStep 1901245 = 712967) (by norm_num)
theorem B3801797 : Blo 1688044 3801797 := bbase (se 4 (by rfl) ⟨356418, by rfl⟩ : syracuseStep 3801797 = 712837) (by norm_num)
theorem B2138825 : Blo 1688044 2138825 := bbase (se 2 (by rfl) ⟨802059, by rfl⟩ : syracuseStep 2138825 = 1604119) (by norm_num)
theorem B1901281 : Blo 1688044 1901281 := bbase (se 2 (by rfl) ⟨712980, by rfl⟩ : syracuseStep 1901281 = 1425961) (by norm_num)
theorem B2532077 : Blo 1688044 2532077 := bbase (se 3 (by rfl) ⟨474764, by rfl⟩ : syracuseStep 2532077 = 949529) (by norm_num)
theorem B6087413 : Blo 1688044 6087413 := bbase (se 5 (by rfl) ⟨285347, by rfl⟩ : syracuseStep 6087413 = 570695) (by norm_num)
theorem B2138881 : Blo 1688044 2138881 := bbase (se 2 (by rfl) ⟨802080, by rfl⟩ : syracuseStep 2138881 = 1604161) (by norm_num)
theorem B2532101 : Blo 1688044 2532101 := bbase (se 4 (by rfl) ⟨237384, by rfl⟩ : syracuseStep 2532101 = 474769) (by norm_num)
theorem B6415109 : Blo 1688044 6415109 := bbase (se 4 (by rfl) ⟨601416, by rfl⟩ : syracuseStep 6415109 = 1202833) (by norm_num)
theorem B3801869 : Blo 1688044 3801869 := bbase (se 3 (by rfl) ⟨712850, by rfl⟩ : syracuseStep 3801869 = 1425701) (by norm_num)
theorem B2532125 : Blo 1688044 2532125 := bbase (se 3 (by rfl) ⟨474773, by rfl⟩ : syracuseStep 2532125 = 949547) (by norm_num)
theorem B2532149 : Blo 1688044 2532149 := bbase (se 5 (by rfl) ⟨118694, by rfl⟩ : syracuseStep 2532149 = 237389) (by norm_num)
theorem B5702453 : Blo 1688044 5702453 := bbase (se 5 (by rfl) ⟨267302, by rfl⟩ : syracuseStep 5702453 = 534605) (by norm_num)
theorem B2851645 : Blo 1688044 2851645 := bbase (se 3 (by rfl) ⟨534683, by rfl⟩ : syracuseStep 2851645 = 1069367) (by norm_num)
theorem B2532173 : Blo 1688044 2532173 := bbase (se 3 (by rfl) ⟨474782, by rfl⟩ : syracuseStep 2532173 = 949565) (by norm_num)
theorem B3801941 : Blo 1688044 3801941 := bbase (se 9 (by rfl) ⟨11138, by rfl⟩ : syracuseStep 3801941 = 22277) (by norm_num)
theorem B2532197 : Blo 1688044 2532197 := bbase (se 4 (by rfl) ⟨237393, by rfl⟩ : syracuseStep 2532197 = 474787) (by norm_num)
theorem B2532221 : Blo 1688044 2532221 := bbase (se 3 (by rfl) ⟨474791, by rfl⟩ : syracuseStep 2532221 = 949583) (by norm_num)
theorem B2532245 : Blo 1688044 2532245 := bbase (se 6 (by rfl) ⟨59349, by rfl⟩ : syracuseStep 2532245 = 118699) (by norm_num)
theorem B2851733 : Blo 1688044 2851733 := bbase (se 6 (by rfl) ⟨66837, by rfl⟩ : syracuseStep 2851733 = 133675) (by norm_num)
theorem B3802013 : Blo 1688044 3802013 := bbase (se 3 (by rfl) ⟨712877, by rfl⟩ : syracuseStep 3802013 = 1425755) (by norm_num)
theorem B2532269 : Blo 1688044 2532269 := bbase (se 3 (by rfl) ⟨474800, by rfl⟩ : syracuseStep 2532269 = 949601) (by norm_num)
theorem B2532293 : Blo 1688044 2532293 := bbase (se 4 (by rfl) ⟨237402, by rfl⟩ : syracuseStep 2532293 = 474805) (by norm_num)
theorem B2532317 : Blo 1688044 2532317 := bbase (se 3 (by rfl) ⟨474809, by rfl⟩ : syracuseStep 2532317 = 949619) (by norm_num)
theorem B1803233 : Blo 1688044 1803233 := bbase (se 2 (by rfl) ⟨676212, by rfl⟩ : syracuseStep 1803233 = 1352425) (by norm_num)
theorem B2704357 : Blo 1688044 2704357 := bbase (se 4 (by rfl) ⟨253533, by rfl⟩ : syracuseStep 2704357 = 507067) (by norm_num)
theorem B3802085 : Blo 1688044 3802085 := bbase (se 4 (by rfl) ⟨356445, by rfl⟩ : syracuseStep 3802085 = 712891) (by norm_num)
theorem B2532341 : Blo 1688044 2532341 := bbase (se 5 (by rfl) ⟨118703, by rfl⟩ : syracuseStep 2532341 = 237407) (by norm_num)
theorem B5776373 : Blo 1688044 5776373 := bbase (se 5 (by rfl) ⟨270767, by rfl⟩ : syracuseStep 5776373 = 541535) (by norm_num)
theorem B4277245 : Blo 1688044 4277245 := bbase (se 3 (by rfl) ⟨801983, by rfl⟩ : syracuseStep 4277245 = 1603967) (by norm_num)
theorem B3605509 : Blo 1688044 3605509 := bbase (se 4 (by rfl) ⟨338016, by rfl⟩ : syracuseStep 3605509 = 676033) (by norm_num)
theorem B2532365 : Blo 1688044 2532365 := bbase (se 3 (by rfl) ⟨474818, by rfl⟩ : syracuseStep 2532365 = 949637) (by norm_num)
theorem B2851861 : Blo 1688044 2851861 := bbase (se 6 (by rfl) ⟨66840, by rfl⟩ : syracuseStep 2851861 = 133681) (by norm_num)
theorem B2532389 : Blo 1688044 2532389 := bbase (se 4 (by rfl) ⟨237411, by rfl⟩ : syracuseStep 2532389 = 474823) (by norm_num)
theorem B3802157 : Blo 1688044 3802157 := bbase (se 3 (by rfl) ⟨712904, by rfl⟩ : syracuseStep 3802157 = 1425809) (by norm_num)
theorem B2532413 : Blo 1688044 2532413 := bbase (se 3 (by rfl) ⟨474827, by rfl⟩ : syracuseStep 2532413 = 949655) (by norm_num)
theorem B2532437 : Blo 1688044 2532437 := bbase (se 8 (by rfl) ⟨14838, by rfl⟩ : syracuseStep 2532437 = 29677) (by norm_num)
theorem B17572949 : Blo 1688044 17572949 := bbase (se 8 (by rfl) ⟨102966, by rfl⟩ : syracuseStep 17572949 = 205933) (by norm_num)
theorem B2532461 : Blo 1688044 2532461 := bbase (se 3 (by rfl) ⟨474836, by rfl⟩ : syracuseStep 2532461 = 949673) (by norm_num)
theorem B4277357 : Blo 1688044 4277357 := bbase (se 3 (by rfl) ⟨802004, by rfl⟩ : syracuseStep 4277357 = 1604009) (by norm_num)
theorem B2851949 : Blo 1688044 2851949 := bbase (se 3 (by rfl) ⟨534740, by rfl⟩ : syracuseStep 2851949 = 1069481) (by norm_num)
theorem B3802229 : Blo 1688044 3802229 := bbase (se 5 (by rfl) ⟨178229, by rfl⟩ : syracuseStep 3802229 = 356459) (by norm_num)
theorem B3605629 : Blo 1688044 3605629 := bbase (se 3 (by rfl) ⟨676055, by rfl⟩ : syracuseStep 3605629 = 1352111) (by norm_num)
theorem B2532485 : Blo 1688044 2532485 := bbase (se 4 (by rfl) ⟨237420, by rfl⟩ : syracuseStep 2532485 = 474841) (by norm_num)
theorem B27780245 : Blo 1688044 27780245 := bbase (se 6 (by rfl) ⟨651099, by rfl⟩ : syracuseStep 27780245 = 1302199) (by norm_num)
theorem B2532509 : Blo 1688044 2532509 := bbase (se 3 (by rfl) ⟨474845, by rfl⟩ : syracuseStep 2532509 = 949691) (by norm_num)
theorem B1803421 : Blo 1688044 1803421 := bbase (se 3 (by rfl) ⟨338141, by rfl⟩ : syracuseStep 1803421 = 676283) (by norm_num)
theorem B2532533 : Blo 1688044 2532533 := bbase (se 5 (by rfl) ⟨118712, by rfl⟩ : syracuseStep 2532533 = 237425) (by norm_num)
theorem B3802301 : Blo 1688044 3802301 := bbase (se 3 (by rfl) ⟨712931, by rfl⟩ : syracuseStep 3802301 = 1425863) (by norm_num)
theorem B2532557 : Blo 1688044 2532557 := bbase (se 3 (by rfl) ⟨474854, by rfl⟩ : syracuseStep 2532557 = 949709) (by norm_num)
theorem B2532581 : Blo 1688044 2532581 := bbase (se 4 (by rfl) ⟨237429, by rfl⟩ : syracuseStep 2532581 = 474859) (by norm_num)
theorem B5702885 : Blo 1688044 5702885 := bbase (se 4 (by rfl) ⟨534645, by rfl⟩ : syracuseStep 5702885 = 1069291) (by norm_num)
theorem B2532605 : Blo 1688044 2532605 := bbase (se 3 (by rfl) ⟨474863, by rfl⟩ : syracuseStep 2532605 = 949727) (by norm_num)
theorem B3802373 : Blo 1688044 3802373 := bbase (se 4 (by rfl) ⟨356472, by rfl⟩ : syracuseStep 3802373 = 712945) (by norm_num)
theorem B2532629 : Blo 1688044 2532629 := bbase (se 6 (by rfl) ⟨59358, by rfl⟩ : syracuseStep 2532629 = 118717) (by norm_num)
theorem B2532653 : Blo 1688044 2532653 := bbase (se 3 (by rfl) ⟨474872, by rfl⟩ : syracuseStep 2532653 = 949745) (by norm_num)
theorem B4277549 : Blo 1688044 4277549 := bbase (se 3 (by rfl) ⟨802040, by rfl⟩ : syracuseStep 4277549 = 1604081) (by norm_num)
theorem B2532677 : Blo 1688044 2532677 := bbase (se 4 (by rfl) ⟨237438, by rfl⟩ : syracuseStep 2532677 = 474877) (by norm_num)
theorem B3802445 : Blo 1688044 3802445 := bbase (se 3 (by rfl) ⟨712958, by rfl⟩ : syracuseStep 3802445 = 1425917) (by norm_num)
theorem B2532701 : Blo 1688044 2532701 := bbase (se 3 (by rfl) ⟨474881, by rfl⟩ : syracuseStep 2532701 = 949763) (by norm_num)
theorem B2532725 : Blo 1688044 2532725 := bbase (se 5 (by rfl) ⟨118721, by rfl⟩ : syracuseStep 2532725 = 237443) (by norm_num)
theorem B3605885 : Blo 1688044 3605885 := bbase (se 3 (by rfl) ⟨676103, by rfl⟩ : syracuseStep 3605885 = 1352207) (by norm_num)
theorem B2532749 : Blo 1688044 2532749 := bbase (se 3 (by rfl) ⟨474890, by rfl⟩ : syracuseStep 2532749 = 949781) (by norm_num)
theorem B3802517 : Blo 1688044 3802517 := bbase (se 6 (by rfl) ⟨89121, by rfl⟩ : syracuseStep 3802517 = 178243) (by norm_num)
theorem B2532773 : Blo 1688044 2532773 := bbase (se 4 (by rfl) ⟨237447, by rfl⟩ : syracuseStep 2532773 = 474895) (by norm_num)
theorem B2532797 : Blo 1688044 2532797 := bbase (se 3 (by rfl) ⟨474899, by rfl⟩ : syracuseStep 2532797 = 949799) (by norm_num)
theorem B2532821 : Blo 1688044 2532821 := bbase (se 7 (by rfl) ⟨29681, by rfl⟩ : syracuseStep 2532821 = 59363) (by norm_num)
theorem B3802589 : Blo 1688044 3802589 := bbase (se 3 (by rfl) ⟨712985, by rfl⟩ : syracuseStep 3802589 = 1425971) (by norm_num)
theorem B2532845 : Blo 1688044 2532845 := bbase (se 3 (by rfl) ⟨474908, by rfl⟩ : syracuseStep 2532845 = 949817) (by norm_num)
theorem B2532869 : Blo 1688044 2532869 := bbase (se 4 (by rfl) ⟨237456, by rfl⟩ : syracuseStep 2532869 = 474913) (by norm_num)
theorem B4810261 : Blo 1688044 4810261 := bbase (se 6 (by rfl) ⟨112740, by rfl⟩ : syracuseStep 4810261 = 225481) (by norm_num)
theorem B2532893 : Blo 1688044 2532893 := bbase (se 3 (by rfl) ⟨474917, by rfl⟩ : syracuseStep 2532893 = 949835) (by norm_num)
theorem B2532917 : Blo 1688044 2532917 := bbase (se 5 (by rfl) ⟨118730, by rfl⟩ : syracuseStep 2532917 = 237461) (by norm_num)
theorem B3204677 : Blo 1688044 3204677 := bbase (se 4 (by rfl) ⟨300438, by rfl⟩ : syracuseStep 3204677 = 600877) (by norm_num)
theorem B2532941 : Blo 1688044 2532941 := bbase (se 3 (by rfl) ⟨474926, by rfl⟩ : syracuseStep 2532941 = 949853) (by norm_num)
theorem B2532965 : Blo 1688044 2532965 := bbase (se 4 (by rfl) ⟨237465, by rfl⟩ : syracuseStep 2532965 = 474931) (by norm_num)
theorem B8554085 : Blo 1688044 8554085 := bbase (se 4 (by rfl) ⟨801945, by rfl⟩ : syracuseStep 8554085 = 1603891) (by norm_num)
theorem B7308917 : Blo 1688044 7308917 := bbase (se 5 (by rfl) ⟨342605, by rfl⟩ : syracuseStep 7308917 = 685211) (by norm_num)
theorem B6497909 : Blo 1688044 6497909 := bbase (se 5 (by rfl) ⟨304589, by rfl⟩ : syracuseStep 6497909 = 609179) (by norm_num)
theorem B2532989 : Blo 1688044 2532989 := bbase (se 3 (by rfl) ⟨474935, by rfl⟩ : syracuseStep 2532989 = 949871) (by norm_num)
theorem B4277893 : Blo 1688044 4277893 := bbase (se 4 (by rfl) ⟨401052, by rfl⟩ : syracuseStep 4277893 = 802105) (by norm_num)
theorem B2533013 : Blo 1688044 2533013 := bbase (se 6 (by rfl) ⟨59367, by rfl⟩ : syracuseStep 2533013 = 118735) (by norm_num)
theorem B5703317 : Blo 1688044 5703317 := bbase (se 6 (by rfl) ⟨133671, by rfl⟩ : syracuseStep 5703317 = 267343) (by norm_num)
theorem B2533037 : Blo 1688044 2533037 := bbase (se 3 (by rfl) ⟨474944, by rfl⟩ : syracuseStep 2533037 = 949889) (by norm_num)
theorem B4810421 : Blo 1688044 4810421 := bbase (se 5 (by rfl) ⟨225488, by rfl⟩ : syracuseStep 4810421 = 450977) (by norm_num)
theorem B2533061 : Blo 1688044 2533061 := bbase (se 4 (by rfl) ⟨237474, by rfl⟩ : syracuseStep 2533061 = 474949) (by norm_num)
theorem B3204821 : Blo 1688044 3204821 := bbase (se 7 (by rfl) ⟨37556, by rfl⟩ : syracuseStep 3204821 = 75113) (by norm_num)
theorem B2533085 : Blo 1688044 2533085 := bbase (se 3 (by rfl) ⟨474953, by rfl⟩ : syracuseStep 2533085 = 949907) (by norm_num)
theorem B6088421 : Blo 1688044 6088421 := bbase (se 4 (by rfl) ⟨570789, by rfl⟩ : syracuseStep 6088421 = 1141579) (by norm_num)
theorem B2533109 : Blo 1688044 2533109 := bbase (se 5 (by rfl) ⟨118739, by rfl⟩ : syracuseStep 2533109 = 237479) (by norm_num)
theorem B2533133 : Blo 1688044 2533133 := bbase (se 3 (by rfl) ⟨474962, by rfl⟩ : syracuseStep 2533133 = 949925) (by norm_num)
theorem B2533157 : Blo 1688044 2533157 := bbase (se 4 (by rfl) ⟨237483, by rfl⟩ : syracuseStep 2533157 = 474967) (by norm_num)
theorem B4171565 : Blo 1688044 4171565 := bbase (se 3 (by rfl) ⟨782168, by rfl⟩ : syracuseStep 4171565 = 1564337) (by norm_num)
theorem B2533181 : Blo 1688044 2533181 := bbase (se 3 (by rfl) ⟨474971, by rfl⟩ : syracuseStep 2533181 = 949943) (by norm_num)
theorem B2533205 : Blo 1688044 2533205 := bbase (se 9 (by rfl) ⟨7421, by rfl⟩ : syracuseStep 2533205 = 14843) (by norm_num)
theorem B2533229 : Blo 1688044 2533229 := bbase (se 3 (by rfl) ⟨474980, by rfl⟩ : syracuseStep 2533229 = 949961) (by norm_num)
theorem B2533253 : Blo 1688044 2533253 := bbase (se 4 (by rfl) ⟨237492, by rfl⟩ : syracuseStep 2533253 = 474985) (by norm_num)
theorem B2705285 : Blo 1688044 2705285 := bbase (se 4 (by rfl) ⟨253620, by rfl⟩ : syracuseStep 2705285 = 507241) (by norm_num)
theorem B2533277 : Blo 1688044 2533277 := bbase (se 3 (by rfl) ⟨474989, by rfl⟩ : syracuseStep 2533277 = 949979) (by norm_num)
theorem B4810661 : Blo 1688044 4810661 := bbase (se 4 (by rfl) ⟨450999, by rfl⟩ : syracuseStep 4810661 = 901999) (by norm_num)
theorem B6416293 : Blo 1688044 6416293 := bbase (se 4 (by rfl) ⟨601527, by rfl⟩ : syracuseStep 6416293 = 1203055) (by norm_num)
theorem B2533301 : Blo 1688044 2533301 := bbase (se 5 (by rfl) ⟨118748, by rfl⟩ : syracuseStep 2533301 = 237497) (by norm_num)
theorem B2533325 : Blo 1688044 2533325 := bbase (se 3 (by rfl) ⟨474998, by rfl⟩ : syracuseStep 2533325 = 949997) (by norm_num)
theorem B1804241 : Blo 1688044 1804241 := bbase (se 2 (by rfl) ⟨676590, by rfl⟩ : syracuseStep 1804241 = 1353181) (by norm_num)
theorem B2533349 : Blo 1688044 2533349 := bbase (se 4 (by rfl) ⟨237501, by rfl⟩ : syracuseStep 2533349 = 475003) (by norm_num)
theorem B3205109 : Blo 1688044 3205109 := bbase (se 5 (by rfl) ⟨150239, by rfl⟩ : syracuseStep 3205109 = 300479) (by norm_num)
theorem B2533373 : Blo 1688044 2533373 := bbase (se 3 (by rfl) ⟨475007, by rfl⟩ : syracuseStep 2533373 = 950015) (by norm_num)
theorem B8546309 : Blo 1688044 8546309 := bbase (se 4 (by rfl) ⟨801216, by rfl⟩ : syracuseStep 8546309 = 1602433) (by norm_num)
theorem B2533397 : Blo 1688044 2533397 := bbase (se 6 (by rfl) ⟨59376, by rfl⟩ : syracuseStep 2533397 = 118753) (by norm_num)
theorem B2533421 : Blo 1688044 2533421 := bbase (se 3 (by rfl) ⟨475016, by rfl⟩ : syracuseStep 2533421 = 950033) (by norm_num)
theorem B12994613 : Blo 1688044 12994613 := bbase (se 5 (by rfl) ⟨609122, by rfl⟩ : syracuseStep 12994613 = 1218245) (by norm_num)
theorem B9750581 : Blo 1688044 9750581 := bbase (se 5 (by rfl) ⟨457058, by rfl⟩ : syracuseStep 9750581 = 914117) (by norm_num)
theorem B2533445 : Blo 1688044 2533445 := bbase (se 4 (by rfl) ⟨237510, by rfl⟩ : syracuseStep 2533445 = 475021) (by norm_num)
theorem B5703749 : Blo 1688044 5703749 := bbase (se 4 (by rfl) ⟨534726, by rfl⟩ : syracuseStep 5703749 = 1069453) (by norm_num)
theorem B2533469 : Blo 1688044 2533469 := bbase (se 3 (by rfl) ⟨475025, by rfl⟩ : syracuseStep 2533469 = 950051) (by norm_num)
theorem B4810853 : Blo 1688044 4810853 := bbase (se 4 (by rfl) ⟨451017, by rfl⟩ : syracuseStep 4810853 = 902035) (by norm_num)
theorem B2533493 : Blo 1688044 2533493 := bbase (se 5 (by rfl) ⟨118757, by rfl⟩ : syracuseStep 2533493 = 237515) (by norm_num)
theorem B3205261 : Blo 1688044 3205261 := bbase (se 3 (by rfl) ⟨600986, by rfl⟩ : syracuseStep 3205261 = 1201973) (by norm_num)
theorem B2533517 : Blo 1688044 2533517 := bbase (se 3 (by rfl) ⟨475034, by rfl⟩ : syracuseStep 2533517 = 950069) (by norm_num)
theorem B5777573 : Blo 1688044 5777573 := bbase (se 4 (by rfl) ⟨541647, by rfl⟩ : syracuseStep 5777573 = 1083295) (by norm_num)
theorem B2533541 : Blo 1688044 2533541 := bbase (se 4 (by rfl) ⟨237519, by rfl⟩ : syracuseStep 2533541 = 475039) (by norm_num)
theorem B2533565 : Blo 1688044 2533565 := bbase (se 3 (by rfl) ⟨475043, by rfl⟩ : syracuseStep 2533565 = 950087) (by norm_num)
theorem B8784085 : Blo 1688044 8784085 := bbase (se 7 (by rfl) ⟨102938, by rfl⟩ : syracuseStep 8784085 = 205877) (by norm_num)
theorem B2533589 : Blo 1688044 2533589 := bbase (se 7 (by rfl) ⟨29690, by rfl⟩ : syracuseStep 2533589 = 59381) (by norm_num)
theorem B6416597 : Blo 1688044 6416597 := bbase (se 7 (by rfl) ⟨75194, by rfl⟩ : syracuseStep 6416597 = 150389) (by norm_num)
theorem B2533613 : Blo 1688044 2533613 := bbase (se 3 (by rfl) ⟨475052, by rfl⟩ : syracuseStep 2533613 = 950105) (by norm_num)
theorem B3606773 : Blo 1688044 3606773 := bbase (se 5 (by rfl) ⟨169067, by rfl⟩ : syracuseStep 3606773 = 338135) (by norm_num)
theorem B2533637 : Blo 1688044 2533637 := bbase (se 4 (by rfl) ⟨237528, by rfl⟩ : syracuseStep 2533637 = 475057) (by norm_num)
theorem B14436629 : Blo 1688044 14436629 := bbase (se 6 (by rfl) ⟨338358, by rfl⟩ : syracuseStep 14436629 = 676717) (by norm_num)
theorem B2533661 : Blo 1688044 2533661 := bbase (se 3 (by rfl) ⟨475061, by rfl⟩ : syracuseStep 2533661 = 950123) (by norm_num)
theorem B4057381 : Blo 1688044 4057381 := bbase (se 4 (by rfl) ⟨380379, by rfl⟩ : syracuseStep 4057381 = 760759) (by norm_num)
theorem B2533685 : Blo 1688044 2533685 := bbase (se 5 (by rfl) ⟨118766, by rfl⟩ : syracuseStep 2533685 = 237533) (by norm_num)
theorem B2533709 : Blo 1688044 2533709 := bbase (se 3 (by rfl) ⟨475070, by rfl⟩ : syracuseStep 2533709 = 950141) (by norm_num)
theorem B2705741 : Blo 1688044 2705741 := bbase (se 3 (by rfl) ⟨507326, by rfl⟩ : syracuseStep 2705741 = 1014653) (by norm_num)
theorem B2533733 : Blo 1688044 2533733 := bbase (se 4 (by rfl) ⟨237537, by rfl⟩ : syracuseStep 2533733 = 475075) (by norm_num)
theorem B2533757 : Blo 1688044 2533757 := bbase (se 3 (by rfl) ⟨475079, by rfl⟩ : syracuseStep 2533757 = 950159) (by norm_num)
theorem B1804685 : Blo 1688044 1804685 := bbase (se 3 (by rfl) ⟨338378, by rfl⟩ : syracuseStep 1804685 = 676757) (by norm_num)
theorem B2533781 : Blo 1688044 2533781 := bbase (se 6 (by rfl) ⟨59385, by rfl⟩ : syracuseStep 2533781 = 118771) (by norm_num)
theorem B7211429 : Blo 1688044 7211429 := bbase (se 4 (by rfl) ⟨676071, by rfl⟩ : syracuseStep 7211429 = 1352143) (by norm_num)
theorem B2533805 : Blo 1688044 2533805 := bbase (se 3 (by rfl) ⟨475088, by rfl⟩ : syracuseStep 2533805 = 950177) (by norm_num)
theorem B3205565 : Blo 1688044 3205565 := bbase (se 3 (by rfl) ⟨601043, by rfl⟩ : syracuseStep 3205565 = 1202087) (by norm_num)
theorem B2533829 : Blo 1688044 2533829 := bbase (se 4 (by rfl) ⟨237546, by rfl⟩ : syracuseStep 2533829 = 475093) (by norm_num)
theorem B2533853 : Blo 1688044 2533853 := bbase (se 3 (by rfl) ⟨475097, by rfl⟩ : syracuseStep 2533853 = 950195) (by norm_num)
theorem B3607013 : Blo 1688044 3607013 := bbase (se 4 (by rfl) ⟨338157, by rfl⟩ : syracuseStep 3607013 = 676315) (by norm_num)
theorem B2533877 : Blo 1688044 2533877 := bbase (se 5 (by rfl) ⟨118775, by rfl⟩ : syracuseStep 2533877 = 237551) (by norm_num)
theorem B2533901 : Blo 1688044 2533901 := bbase (se 3 (by rfl) ⟨475106, by rfl⟩ : syracuseStep 2533901 = 950213) (by norm_num)
theorem B2533925 : Blo 1688044 2533925 := bbase (se 4 (by rfl) ⟨237555, by rfl⟩ : syracuseStep 2533925 = 475111) (by norm_num)
theorem B2533949 : Blo 1688044 2533949 := bbase (se 3 (by rfl) ⟨475115, by rfl⟩ : syracuseStep 2533949 = 950231) (by norm_num)
theorem B2533973 : Blo 1688044 2533973 := bbase (se 8 (by rfl) ⟨14847, by rfl⟩ : syracuseStep 2533973 = 29695) (by norm_num)
theorem B2533997 : Blo 1688044 2533997 := bbase (se 3 (by rfl) ⟨475124, by rfl⟩ : syracuseStep 2533997 = 950249) (by norm_num)
theorem B4057717 : Blo 1688044 4057717 := bbase (se 5 (by rfl) ⟨190205, by rfl⟩ : syracuseStep 4057717 = 380411) (by norm_num)
theorem B2534021 : Blo 1688044 2534021 := bbase (se 4 (by rfl) ⟨237564, by rfl⟩ : syracuseStep 2534021 = 475129) (by norm_num)
theorem B2534045 : Blo 1688044 2534045 := bbase (se 3 (by rfl) ⟨475133, by rfl⟩ : syracuseStep 2534045 = 950267) (by norm_num)
theorem B2534069 : Blo 1688044 2534069 := bbase (se 5 (by rfl) ⟨118784, by rfl⟩ : syracuseStep 2534069 = 237569) (by norm_num)
theorem B2534093 : Blo 1688044 2534093 := bbase (se 3 (by rfl) ⟨475142, by rfl⟩ : syracuseStep 2534093 = 950285) (by norm_num)
theorem B2534117 : Blo 1688044 2534117 := bbase (se 4 (by rfl) ⟨237573, by rfl⟩ : syracuseStep 2534117 = 475147) (by norm_num)
theorem B2534141 : Blo 1688044 2534141 := bbase (se 3 (by rfl) ⟨475151, by rfl⟩ : syracuseStep 2534141 = 950303) (by norm_num)
theorem B1854205 : Blo 1688044 1854205 := bbase (se 3 (by rfl) ⟨347663, by rfl⟩ : syracuseStep 1854205 = 695327) (by norm_num)
theorem B2534165 : Blo 1688044 2534165 := bbase (se 6 (by rfl) ⟨59394, by rfl⟩ : syracuseStep 2534165 = 118789) (by norm_num)
theorem B2534189 : Blo 1688044 2534189 := bbase (se 3 (by rfl) ⟨475160, by rfl⟩ : syracuseStep 2534189 = 950321) (by norm_num)
theorem B2534213 : Blo 1688044 2534213 := bbase (se 4 (by rfl) ⟨237582, by rfl⟩ : syracuseStep 2534213 = 475165) (by norm_num)
theorem B2534237 : Blo 1688044 2534237 := bbase (se 3 (by rfl) ⟨475169, by rfl⟩ : syracuseStep 2534237 = 950339) (by norm_num)
theorem B2534261 : Blo 1688044 2534261 := bbase (se 5 (by rfl) ⟨118793, by rfl⟩ : syracuseStep 2534261 = 237587) (by norm_num)
theorem B8555381 : Blo 1688044 8555381 := bbase (se 5 (by rfl) ⟨401033, by rfl⟩ : syracuseStep 8555381 = 802067) (by norm_num)
theorem B8121221 : Blo 1688044 8121221 := bbase (se 4 (by rfl) ⟨761364, by rfl⟩ : syracuseStep 8121221 = 1522729) (by norm_num)
theorem B2534285 : Blo 1688044 2534285 := bbase (se 3 (by rfl) ⟨475178, by rfl⟩ : syracuseStep 2534285 = 950357) (by norm_num)
theorem B2534309 : Blo 1688044 2534309 := bbase (se 4 (by rfl) ⟨237591, by rfl⟩ : syracuseStep 2534309 = 475183) (by norm_num)
theorem B2534333 : Blo 1688044 2534333 := bbase (se 3 (by rfl) ⟨475187, by rfl⟩ : syracuseStep 2534333 = 950375) (by norm_num)
theorem B2534357 : Blo 1688044 2534357 := bbase (se 7 (by rfl) ⟨29699, by rfl⟩ : syracuseStep 2534357 = 59399) (by norm_num)
theorem B3607517 : Blo 1688044 3607517 := bbase (se 3 (by rfl) ⟨676409, by rfl⟩ : syracuseStep 3607517 = 1352819) (by norm_num)
theorem B3607525 : Blo 1688044 3607525 := bbase (se 4 (by rfl) ⟨338205, by rfl⟩ : syracuseStep 3607525 = 676411) (by norm_num)
theorem B2534381 : Blo 1688044 2534381 := bbase (se 3 (by rfl) ⟨475196, by rfl⟩ : syracuseStep 2534381 = 950393) (by norm_num)
theorem B2534405 : Blo 1688044 2534405 := bbase (se 4 (by rfl) ⟨237600, by rfl⟩ : syracuseStep 2534405 = 475201) (by norm_num)
theorem B2534429 : Blo 1688044 2534429 := bbase (se 3 (by rfl) ⟨475205, by rfl⟩ : syracuseStep 2534429 = 950411) (by norm_num)
theorem B10275893 : Blo 1688044 10275893 := bbase (se 5 (by rfl) ⟨481682, by rfl⟩ : syracuseStep 10275893 = 963365) (by norm_num)
theorem B2534453 : Blo 1688044 2534453 := bbase (se 5 (by rfl) ⟨118802, by rfl⟩ : syracuseStep 2534453 = 237605) (by norm_num)
theorem B3042365 : Blo 1688044 3042365 := bbase (se 3 (by rfl) ⟨570443, by rfl⟩ : syracuseStep 3042365 = 1140887) (by norm_num)
theorem B4811845 : Blo 1688044 4811845 := bbase (se 4 (by rfl) ⟨451110, by rfl⟩ : syracuseStep 4811845 = 902221) (by norm_num)
theorem B2534477 : Blo 1688044 2534477 := bbase (se 3 (by rfl) ⟨475214, by rfl⟩ : syracuseStep 2534477 = 950429) (by norm_num)
theorem B2534501 : Blo 1688044 2534501 := bbase (se 4 (by rfl) ⟨237609, by rfl⟩ : syracuseStep 2534501 = 475219) (by norm_num)
theorem B2534525 : Blo 1688044 2534525 := bbase (se 3 (by rfl) ⟨475223, by rfl⟩ : syracuseStep 2534525 = 950447) (by norm_num)
theorem B2534549 : Blo 1688044 2534549 := bbase (se 6 (by rfl) ⟨59403, by rfl⟩ : syracuseStep 2534549 = 118807) (by norm_num)
theorem B3206317 : Blo 1688044 3206317 := bbase (se 3 (by rfl) ⟨601184, by rfl⟩ : syracuseStep 3206317 = 1202369) (by norm_num)
theorem B2534573 : Blo 1688044 2534573 := bbase (se 3 (by rfl) ⟨475232, by rfl⟩ : syracuseStep 2534573 = 950465) (by norm_num)
theorem B2534597 : Blo 1688044 2534597 := bbase (se 4 (by rfl) ⟨237618, by rfl⟩ : syracuseStep 2534597 = 475237) (by norm_num)
theorem B3706069 : Blo 1688044 3706069 := bbase (se 7 (by rfl) ⟨43430, by rfl⟩ : syracuseStep 3706069 = 86861) (by norm_num)
theorem B4058333 : Blo 1688044 4058333 := bbase (se 3 (by rfl) ⟨760937, by rfl⟩ : syracuseStep 4058333 = 1521875) (by norm_num)
theorem B2534621 : Blo 1688044 2534621 := bbase (se 3 (by rfl) ⟨475241, by rfl⟩ : syracuseStep 2534621 = 950483) (by norm_num)
theorem B2534645 : Blo 1688044 2534645 := bbase (se 5 (by rfl) ⟨118811, by rfl⟩ : syracuseStep 2534645 = 237623) (by norm_num)
theorem B2534669 : Blo 1688044 2534669 := bbase (se 3 (by rfl) ⟨475250, by rfl⟩ : syracuseStep 2534669 = 950501) (by norm_num)
theorem B8547605 : Blo 1688044 8547605 := bbase (se 6 (by rfl) ⟨200334, by rfl⟩ : syracuseStep 8547605 = 400669) (by norm_num)
theorem B2534693 : Blo 1688044 2534693 := bbase (se 4 (by rfl) ⟨237627, by rfl⟩ : syracuseStep 2534693 = 475255) (by norm_num)
theorem B3206461 : Blo 1688044 3206461 := bbase (se 3 (by rfl) ⟨601211, by rfl⟩ : syracuseStep 3206461 = 1202423) (by norm_num)
theorem B2534717 : Blo 1688044 2534717 := bbase (se 3 (by rfl) ⟨475259, by rfl⟩ : syracuseStep 2534717 = 950519) (by norm_num)
theorem B2534741 : Blo 1688044 2534741 := bbase (se 11 (by rfl) ⟨1856, by rfl⟩ : syracuseStep 2534741 = 3713) (by norm_num)
theorem B2567533 : Blo 1688044 2567533 := bbase (se 3 (by rfl) ⟨481412, by rfl⟩ : syracuseStep 2567533 = 962825) (by norm_num)
theorem B2534765 : Blo 1688044 2534765 := bbase (se 3 (by rfl) ⟨475268, by rfl⟩ : syracuseStep 2534765 = 950537) (by norm_num)
theorem B2534789 : Blo 1688044 2534789 := bbase (se 4 (by rfl) ⟨237636, by rfl⟩ : syracuseStep 2534789 = 475273) (by norm_num)
theorem B2534813 : Blo 1688044 2534813 := bbase (se 3 (by rfl) ⟨475277, by rfl⟩ : syracuseStep 2534813 = 950555) (by norm_num)
theorem B2534837 : Blo 1688044 2534837 := bbase (se 5 (by rfl) ⟨118820, by rfl⟩ : syracuseStep 2534837 = 237641) (by norm_num)
theorem B2534861 : Blo 1688044 2534861 := bbase (se 3 (by rfl) ⟨475286, by rfl⟩ : syracuseStep 2534861 = 950573) (by norm_num)
theorem B3206621 : Blo 1688044 3206621 := bbase (se 3 (by rfl) ⟨601241, by rfl⟩ : syracuseStep 3206621 = 1202483) (by norm_num)
theorem B2534885 : Blo 1688044 2534885 := bbase (se 4 (by rfl) ⟨237645, by rfl⟩ : syracuseStep 2534885 = 475291) (by norm_num)
theorem B2534909 : Blo 1688044 2534909 := bbase (se 3 (by rfl) ⟨475295, by rfl⟩ : syracuseStep 2534909 = 950591) (by norm_num)
theorem B2534933 : Blo 1688044 2534933 := bbase (se 6 (by rfl) ⟨59412, by rfl⟩ : syracuseStep 2534933 = 118825) (by norm_num)
theorem B2534957 : Blo 1688044 2534957 := bbase (se 3 (by rfl) ⟨475304, by rfl⟩ : syracuseStep 2534957 = 950609) (by norm_num)
theorem B2534981 : Blo 1688044 2534981 := bbase (se 4 (by rfl) ⟨237654, by rfl⟩ : syracuseStep 2534981 = 475309) (by norm_num)
theorem B2535005 : Blo 1688044 2535005 := bbase (se 3 (by rfl) ⟨475313, by rfl⟩ : syracuseStep 2535005 = 950627) (by norm_num)
theorem B3206765 : Blo 1688044 3206765 := bbase (se 3 (by rfl) ⟨601268, by rfl⟩ : syracuseStep 3206765 = 1202537) (by norm_num)
theorem B2535029 : Blo 1688044 2535029 := bbase (se 5 (by rfl) ⟨118829, by rfl⟩ : syracuseStep 2535029 = 237659) (by norm_num)
theorem B4566661 : Blo 1688044 4566661 := bbase (se 4 (by rfl) ⟨428124, by rfl⟩ : syracuseStep 4566661 = 856249) (by norm_num)
theorem B3083917 : Blo 1688044 3083917 := bbase (se 3 (by rfl) ⟨578234, by rfl⟩ : syracuseStep 3083917 = 1156469) (by norm_num)
theorem B4058765 : Blo 1688044 4058765 := bbase (se 3 (by rfl) ⟨761018, by rfl⟩ : syracuseStep 4058765 = 1522037) (by norm_num)
theorem B2535053 : Blo 1688044 2535053 := bbase (se 3 (by rfl) ⟨475322, by rfl⟩ : syracuseStep 2535053 = 950645) (by norm_num)
theorem B2404037 : Blo 1688044 2404037 := bbase (se 4 (by rfl) ⟨225378, by rfl⟩ : syracuseStep 2404037 = 450757) (by norm_num)
theorem B7720645 : Blo 1688044 7720645 := bbase (se 4 (by rfl) ⟨723810, by rfl⟩ : syracuseStep 7720645 = 1447621) (by norm_num)
theorem B5697269 : Blo 1688044 5697269 := bbase (se 5 (by rfl) ⟨267059, by rfl⟩ : syracuseStep 5697269 = 534119) (by norm_num)
theorem B4878085 : Blo 1688044 4878085 := bbase (se 4 (by rfl) ⟨457320, by rfl⟩ : syracuseStep 4878085 = 914641) (by norm_num)
theorem B2404117 : Blo 1688044 2404117 := bbase (se 6 (by rfl) ⟨56346, by rfl⟩ : syracuseStep 2404117 = 112693) (by norm_num)
theorem B5410597 : Blo 1688044 5410597 := bbase (se 4 (by rfl) ⟨507243, by rfl⟩ : syracuseStep 5410597 = 1014487) (by norm_num)
theorem B2404237 : Blo 1688044 2404237 := bbase (se 3 (by rfl) ⟨450794, by rfl⟩ : syracuseStep 2404237 = 901589) (by norm_num)
theorem B3207053 : Blo 1688044 3207053 := bbase (se 3 (by rfl) ⟨601322, by rfl⟩ : syracuseStep 3207053 = 1202645) (by norm_num)
theorem B2404333 : Blo 1688044 2404333 := bbase (se 3 (by rfl) ⟨450812, by rfl⟩ : syracuseStep 2404333 = 901625) (by norm_num)
theorem B8114165 : Blo 1688044 8114165 := bbase (se 5 (by rfl) ⟨380351, by rfl⟩ : syracuseStep 8114165 = 760703) (by norm_num)
theorem B3043325 : Blo 1688044 3043325 := bbase (se 3 (by rfl) ⟨570623, by rfl⟩ : syracuseStep 3043325 = 1141247) (by norm_num)
theorem B3207205 : Blo 1688044 3207205 := bbase (se 4 (by rfl) ⟨300675, by rfl⟩ : syracuseStep 3207205 = 601351) (by norm_num)
theorem B2887741 : Blo 1688044 2887741 := bbase (se 3 (by rfl) ⟨541451, by rfl⟩ : syracuseStep 2887741 = 1082903) (by norm_num)
theorem B3608653 : Blo 1688044 3608653 := bbase (se 3 (by rfl) ⟨676622, by rfl⟩ : syracuseStep 3608653 = 1353245) (by norm_num)
theorem B7213205 : Blo 1688044 7213205 := bbase (se 6 (by rfl) ⟨169059, by rfl⟩ : syracuseStep 7213205 = 338119) (by norm_num)
theorem B5697701 : Blo 1688044 5697701 := bbase (se 4 (by rfl) ⟨534159, by rfl⟩ : syracuseStep 5697701 = 1068319) (by norm_num)
theorem B3903677 : Blo 1688044 3903677 := bbase (se 3 (by rfl) ⟨731939, by rfl⟩ : syracuseStep 3903677 = 1463879) (by norm_num)
theorem B13693141 : Blo 1688044 13693141 := bbase (se 7 (by rfl) ⟨160466, by rfl⟩ : syracuseStep 13693141 = 320933) (by norm_num)
theorem B4059389 : Blo 1688044 4059389 := bbase (se 3 (by rfl) ⟨761135, by rfl⟩ : syracuseStep 4059389 = 1522271) (by norm_num)
theorem B3207509 : Blo 1688044 3207509 := bbase (se 10 (by rfl) ⟨4698, by rfl⟩ : syracuseStep 3207509 = 9397) (by norm_num)
theorem B8229221 : Blo 1688044 8229221 := bbase (se 4 (by rfl) ⟨771489, by rfl⟩ : syracuseStep 8229221 = 1542979) (by norm_num)
theorem B7213445 : Blo 1688044 7213445 := bbase (se 4 (by rfl) ⟨676260, by rfl⟩ : syracuseStep 7213445 = 1352521) (by norm_num)
theorem B11121077 : Blo 1688044 11121077 := bbase (se 5 (by rfl) ⟨521300, by rfl⟩ : syracuseStep 11121077 = 1042601) (by norm_num)
theorem B3609029 : Blo 1688044 3609029 := bbase (se 4 (by rfl) ⟨338346, by rfl⟩ : syracuseStep 3609029 = 676693) (by norm_num)
theorem B7311829 : Blo 1688044 7311829 := bbase (se 7 (by rfl) ⟨85685, by rfl⟩ : syracuseStep 7311829 = 171371) (by norm_num)
theorem B5485013 : Blo 1688044 5485013 := bbase (se 7 (by rfl) ⟨64277, by rfl⟩ : syracuseStep 5485013 = 128555) (by norm_num)
theorem B2404829 : Blo 1688044 2404829 := bbase (se 3 (by rfl) ⟨450905, by rfl⟩ : syracuseStep 2404829 = 901811) (by norm_num)
theorem B8548901 : Blo 1688044 8548901 := bbase (se 4 (by rfl) ⟨801459, by rfl⟩ : syracuseStep 8548901 = 1602919) (by norm_num)
theorem B5698133 : Blo 1688044 5698133 := bbase (se 8 (by rfl) ⟨33387, by rfl⟩ : syracuseStep 5698133 = 66775) (by norm_num)
theorem B6410933 : Blo 1688044 6410933 := bbase (se 5 (by rfl) ⟨300512, by rfl⟩ : syracuseStep 6410933 = 601025) (by norm_num)
theorem B2282293 : Blo 1688044 2282293 := bbase (se 5 (by rfl) ⟨106982, by rfl⟩ : syracuseStep 2282293 = 213965) (by norm_num)
theorem B2028349 : Blo 1688044 2028349 := bbase (se 3 (by rfl) ⟨380315, by rfl⟩ : syracuseStep 2028349 = 760631) (by norm_num)
theorem B4273013 : Blo 1688044 4273013 := bbase (se 5 (by rfl) ⟨200297, by rfl⟩ : syracuseStep 4273013 = 400595) (by norm_num)
theorem B6411221 : Blo 1688044 6411221 := bbase (se 7 (by rfl) ⟨75131, by rfl⟩ : syracuseStep 6411221 = 150263) (by norm_num)
theorem B5698565 : Blo 1688044 5698565 := bbase (se 4 (by rfl) ⟨534240, by rfl⟩ : syracuseStep 5698565 = 1068481) (by norm_num)
theorem B2405381 : Blo 1688044 2405381 := bbase (se 4 (by rfl) ⟨225504, by rfl⟩ : syracuseStep 2405381 = 451009) (by norm_num)
theorem B3208261 : Blo 1688044 3208261 := bbase (se 4 (by rfl) ⟨300774, by rfl⟩ : syracuseStep 3208261 = 601549) (by norm_num)
theorem B3798125 : Blo 1688044 3798125 := bbase (se 3 (by rfl) ⟨712148, by rfl⟩ : syracuseStep 3798125 = 1424297) (by norm_num)
theorem B4568197 : Blo 1688044 4568197 := bbase (se 4 (by rfl) ⟨428268, by rfl⟩ : syracuseStep 4568197 = 856537) (by norm_num)
theorem B3798197 : Blo 1688044 3798197 := bbase (se 5 (by rfl) ⟨178040, by rfl⟩ : syracuseStep 3798197 = 356081) (by norm_num)
theorem B9622709 : Blo 1688044 9622709 := bbase (se 5 (by rfl) ⟨451064, by rfl⟩ : syracuseStep 9622709 = 902129) (by norm_num)
theorem B2028733 : Blo 1688044 2028733 := bbase (se 3 (by rfl) ⟨380387, by rfl⟩ : syracuseStep 2028733 = 760775) (by norm_num)
theorem B4273357 : Blo 1688044 4273357 := bbase (se 3 (by rfl) ⟨801254, by rfl⟩ : syracuseStep 4273357 = 1602509) (by norm_num)
theorem B3044557 : Blo 1688044 3044557 := bbase (se 3 (by rfl) ⟨570854, by rfl⟩ : syracuseStep 3044557 = 1141709) (by norm_num)
theorem B3208405 : Blo 1688044 3208405 := bbase (se 7 (by rfl) ⟨37598, by rfl⟩ : syracuseStep 3208405 = 75197) (by norm_num)
theorem B3798269 : Blo 1688044 3798269 := bbase (se 3 (by rfl) ⟨712175, by rfl⟩ : syracuseStep 3798269 = 1424351) (by norm_num)
theorem B9614645 : Blo 1688044 9614645 := bbase (se 5 (by rfl) ⟨450686, by rfl⟩ : syracuseStep 9614645 = 901373) (by norm_num)
theorem B4273469 : Blo 1688044 4273469 := bbase (se 3 (by rfl) ⟨801275, by rfl⟩ : syracuseStep 4273469 = 1602551) (by norm_num)
theorem B3798341 : Blo 1688044 3798341 := bbase (se 4 (by rfl) ⟨356094, by rfl⟩ : syracuseStep 3798341 = 712189) (by norm_num)
theorem B3798413 : Blo 1688044 3798413 := bbase (se 3 (by rfl) ⟨712202, by rfl⟩ : syracuseStep 3798413 = 1424405) (by norm_num)
theorem B2282909 : Blo 1688044 2282909 := bbase (se 3 (by rfl) ⟨428045, by rfl⟩ : syracuseStep 2282909 = 856091) (by norm_num)
theorem B5698997 : Blo 1688044 5698997 := bbase (se 5 (by rfl) ⟨267140, by rfl⟩ : syracuseStep 5698997 = 534281) (by norm_num)
theorem B3798485 : Blo 1688044 3798485 := bbase (se 7 (by rfl) ⟨44513, by rfl⟩ : syracuseStep 3798485 = 89027) (by norm_num)
theorem B3085789 : Blo 1688044 3085789 := bbase (se 3 (by rfl) ⟨578585, by rfl⟩ : syracuseStep 3085789 = 1157171) (by norm_num)
theorem B4273661 : Blo 1688044 4273661 := bbase (se 3 (by rfl) ⟨801311, by rfl⟩ : syracuseStep 4273661 = 1602623) (by norm_num)
theorem B3798557 : Blo 1688044 3798557 := bbase (se 3 (by rfl) ⟨712229, by rfl⟩ : syracuseStep 3798557 = 1424459) (by norm_num)
theorem B3798629 : Blo 1688044 3798629 := bbase (se 4 (by rfl) ⟨356121, by rfl⟩ : syracuseStep 3798629 = 712243) (by norm_num)
theorem B3798701 : Blo 1688044 3798701 := bbase (se 3 (by rfl) ⟨712256, by rfl⟩ : syracuseStep 3798701 = 1424513) (by norm_num)
theorem B3798773 : Blo 1688044 3798773 := bbase (se 5 (by rfl) ⟨178067, by rfl⟩ : syracuseStep 3798773 = 356135) (by norm_num)
theorem B2406133 : Blo 1688044 2406133 := bbase (se 5 (by rfl) ⟨112787, by rfl⟩ : syracuseStep 2406133 = 225575) (by norm_num)
theorem B8550197 : Blo 1688044 8550197 := bbase (se 5 (by rfl) ⟨400790, by rfl⟩ : syracuseStep 8550197 = 801581) (by norm_num)
theorem B3798845 : Blo 1688044 3798845 := bbase (se 3 (by rfl) ⟨712283, by rfl⟩ : syracuseStep 3798845 = 1424567) (by norm_num)
theorem B4274005 : Blo 1688044 4274005 := bbase (se 9 (by rfl) ⟨12521, by rfl⟩ : syracuseStep 4274005 = 25043) (by norm_num)
theorem B5699429 : Blo 1688044 5699429 := bbase (se 4 (by rfl) ⟨534321, by rfl⟩ : syracuseStep 5699429 = 1068643) (by norm_num)
theorem B2848621 : Blo 1688044 2848621 := bbase (se 3 (by rfl) ⟨534116, by rfl⟩ : syracuseStep 2848621 = 1068233) (by norm_num)
theorem B3798917 : Blo 1688044 3798917 := bbase (se 4 (by rfl) ⟨356148, by rfl⟩ : syracuseStep 3798917 = 712297) (by norm_num)
theorem B10827701 : Blo 1688044 10827701 := bbase (se 5 (by rfl) ⟨507548, by rfl⟩ : syracuseStep 10827701 = 1015097) (by norm_num)
theorem B2848709 : Blo 1688044 2848709 := bbase (se 4 (by rfl) ⟨267066, by rfl⟩ : syracuseStep 2848709 = 534133) (by norm_num)
theorem B4274117 : Blo 1688044 4274117 := bbase (se 4 (by rfl) ⟨400698, by rfl⟩ : syracuseStep 4274117 = 801397) (by norm_num)
theorem B3798989 : Blo 1688044 3798989 := bbase (se 3 (by rfl) ⟨712310, by rfl⟩ : syracuseStep 3798989 = 1424621) (by norm_num)
theorem B3250133 : Blo 1688044 3250133 := bbase (se 7 (by rfl) ⟨38087, by rfl⟩ : syracuseStep 3250133 = 76175) (by norm_num)
theorem B9385973 : Blo 1688044 9385973 := bbase (se 5 (by rfl) ⟨439967, by rfl⟩ : syracuseStep 9385973 = 879935) (by norm_num)
theorem B3799061 : Blo 1688044 3799061 := bbase (se 6 (by rfl) ⟨89040, by rfl⟩ : syracuseStep 3799061 = 178081) (by norm_num)
theorem B2848837 : Blo 1688044 2848837 := bbase (se 4 (by rfl) ⟨267078, by rfl⟩ : syracuseStep 2848837 = 534157) (by norm_num)
theorem B2029637 : Blo 1688044 2029637 := bbase (se 4 (by rfl) ⟨190278, by rfl⟩ : syracuseStep 2029637 = 380557) (by norm_num)
theorem B3799133 : Blo 1688044 3799133 := bbase (se 3 (by rfl) ⟨712337, by rfl⟩ : syracuseStep 3799133 = 1424675) (by norm_num)
theorem B6412405 : Blo 1688044 6412405 := bbase (se 5 (by rfl) ⟨300581, by rfl⟩ : syracuseStep 6412405 = 601163) (by norm_num)
theorem B3086461 : Blo 1688044 3086461 := bbase (se 3 (by rfl) ⟨578711, by rfl⟩ : syracuseStep 3086461 = 1157423) (by norm_num)
theorem B4274309 : Blo 1688044 4274309 := bbase (se 4 (by rfl) ⟨400716, by rfl⟩ : syracuseStep 4274309 = 801433) (by norm_num)
theorem B2283661 : Blo 1688044 2283661 := bbase (se 3 (by rfl) ⟨428186, by rfl⟩ : syracuseStep 2283661 = 856373) (by norm_num)
theorem B2848925 : Blo 1688044 2848925 := bbase (se 3 (by rfl) ⟨534173, by rfl⟩ : syracuseStep 2848925 = 1068347) (by norm_num)
theorem B3799205 : Blo 1688044 3799205 := bbase (se 4 (by rfl) ⟨356175, by rfl⟩ : syracuseStep 3799205 = 712351) (by norm_num)
theorem B2283709 : Blo 1688044 2283709 := bbase (se 3 (by rfl) ⟨428195, by rfl⟩ : syracuseStep 2283709 = 856391) (by norm_num)
theorem B3799277 : Blo 1688044 3799277 := bbase (se 3 (by rfl) ⟨712364, by rfl⟩ : syracuseStep 3799277 = 1424729) (by norm_num)
theorem B5699861 : Blo 1688044 5699861 := bbase (se 6 (by rfl) ⟨133590, by rfl⟩ : syracuseStep 5699861 = 267181) (by norm_num)
theorem B2849053 : Blo 1688044 2849053 := bbase (se 3 (by rfl) ⟨534197, by rfl⟩ : syracuseStep 2849053 = 1068395) (by norm_num)
theorem B3799349 : Blo 1688044 3799349 := bbase (se 5 (by rfl) ⟨178094, by rfl⟩ : syracuseStep 3799349 = 356189) (by norm_num)
theorem B7706933 : Blo 1688044 7706933 := bbase (se 5 (by rfl) ⟨361262, by rfl⟩ : syracuseStep 7706933 = 722525) (by norm_num)
theorem B2029897 : Blo 1688044 2029897 := bbase (se 2 (by rfl) ⟨761211, by rfl⟩ : syracuseStep 2029897 = 1522423) (by norm_num)
theorem B9623893 : Blo 1688044 9623893 := bbase (se 10 (by rfl) ⟨14097, by rfl⟩ : syracuseStep 9623893 = 28195) (by norm_num)
theorem B4872565 : Blo 1688044 4872565 := bbase (se 5 (by rfl) ⟨228401, by rfl⟩ : syracuseStep 4872565 = 456803) (by norm_num)
theorem B2849141 : Blo 1688044 2849141 := bbase (se 5 (by rfl) ⟨133553, by rfl⟩ : syracuseStep 2849141 = 267107) (by norm_num)
theorem B12826997 : Blo 1688044 12826997 := bbase (se 5 (by rfl) ⟨601265, by rfl⟩ : syracuseStep 12826997 = 1202531) (by norm_num)
theorem B3799421 : Blo 1688044 3799421 := bbase (se 3 (by rfl) ⟨712391, by rfl⟩ : syracuseStep 3799421 = 1424783) (by norm_num)
theorem B6412709 : Blo 1688044 6412709 := bbase (se 4 (by rfl) ⟨601191, by rfl⟩ : syracuseStep 6412709 = 1202383) (by norm_num)
theorem B3799493 : Blo 1688044 3799493 := bbase (se 4 (by rfl) ⟨356202, by rfl⟩ : syracuseStep 3799493 = 712405) (by norm_num)
theorem B3422677 : Blo 1688044 3422677 := bbase (se 7 (by rfl) ⟨40109, by rfl⟩ : syracuseStep 3422677 = 80219) (by norm_num)
theorem B4274653 : Blo 1688044 4274653 := bbase (se 3 (by rfl) ⟨801497, by rfl⟩ : syracuseStep 4274653 = 1602995) (by norm_num)
theorem B2136557 : Blo 1688044 2136557 := bbase (se 3 (by rfl) ⟨400604, by rfl⟩ : syracuseStep 2136557 = 801209) (by norm_num)
theorem B2849269 : Blo 1688044 2849269 := bbase (se 5 (by rfl) ⟨133559, by rfl⟩ : syracuseStep 2849269 = 267119) (by norm_num)
theorem B2030089 : Blo 1688044 2030089 := bbase (se 2 (by rfl) ⟨761283, by rfl⟩ : syracuseStep 2030089 = 1522567) (by norm_num)
theorem B3799565 : Blo 1688044 3799565 := bbase (se 3 (by rfl) ⟨712418, by rfl⟩ : syracuseStep 3799565 = 1424837) (by norm_num)
theorem B2030113 : Blo 1688044 2030113 := bbase (se 2 (by rfl) ⟨761292, by rfl⟩ : syracuseStep 2030113 = 1522585) (by norm_num)
theorem B2136613 : Blo 1688044 2136613 := bbase (se 4 (by rfl) ⟨200307, by rfl⟩ : syracuseStep 2136613 = 400615) (by norm_num)
theorem B2030117 : Blo 1688044 2030117 := bbase (se 4 (by rfl) ⟨190323, by rfl⟩ : syracuseStep 2030117 = 380647) (by norm_num)
theorem B1899085 : Blo 1688044 1899085 := bbase (se 3 (by rfl) ⟨356078, by rfl⟩ : syracuseStep 1899085 = 712157) (by norm_num)
theorem B2849357 : Blo 1688044 2849357 := bbase (se 3 (by rfl) ⟨534254, by rfl⟩ : syracuseStep 2849357 = 1068509) (by norm_num)
theorem B4274765 : Blo 1688044 4274765 := bbase (se 3 (by rfl) ⟨801518, by rfl⟩ : syracuseStep 4274765 = 1603037) (by norm_num)
theorem B24672853 : Blo 1688044 24672853 := bbase (se 8 (by rfl) ⟨144567, by rfl⟩ : syracuseStep 24672853 = 289135) (by norm_num)
theorem B3799637 : Blo 1688044 3799637 := bbase (se 8 (by rfl) ⟨22263, by rfl⟩ : syracuseStep 3799637 = 44527) (by norm_num)
theorem B16235093 : Blo 1688044 16235093 := bbase (se 8 (by rfl) ⟨95127, by rfl⟩ : syracuseStep 16235093 = 190255) (by norm_num)
theorem B1899121 : Blo 1688044 1899121 := bbase (se 2 (by rfl) ⟨712170, by rfl⟩ : syracuseStep 1899121 = 1424341) (by norm_num)
theorem B7215733 : Blo 1688044 7215733 := bbase (se 5 (by rfl) ⟨338237, by rfl⟩ : syracuseStep 7215733 = 676475) (by norm_num)
theorem B5413493 : Blo 1688044 5413493 := bbase (se 5 (by rfl) ⟨253757, by rfl⟩ : syracuseStep 5413493 = 507515) (by norm_num)
theorem B2136709 : Blo 1688044 2136709 := bbase (se 4 (by rfl) ⟨200316, by rfl⟩ : syracuseStep 2136709 = 400633) (by norm_num)
theorem B1899157 : Blo 1688044 1899157 := bbase (se 6 (by rfl) ⟨44511, by rfl⟩ : syracuseStep 1899157 = 89023) (by norm_num)
theorem B3799709 : Blo 1688044 3799709 := bbase (se 3 (by rfl) ⟨712445, by rfl⟩ : syracuseStep 3799709 = 1424891) (by norm_num)
theorem B2603677 : Blo 1688044 2603677 := bbase (se 3 (by rfl) ⟨488189, by rfl⟩ : syracuseStep 2603677 = 976379) (by norm_num)
theorem B4332197 : Blo 1688044 4332197 := bbase (se 4 (by rfl) ⟨406143, by rfl⟩ : syracuseStep 4332197 = 812287) (by norm_num)
theorem B9747125 : Blo 1688044 9747125 := bbase (se 5 (by rfl) ⟨456896, by rfl⟩ : syracuseStep 9747125 = 913793) (by norm_num)
theorem B1899193 : Blo 1688044 1899193 := bbase (se 2 (by rfl) ⟨712197, by rfl⟩ : syracuseStep 1899193 = 1424395) (by norm_num)
theorem B5700293 : Blo 1688044 5700293 := bbase (se 4 (by rfl) ⟨534402, by rfl⟩ : syracuseStep 5700293 = 1068805) (by norm_num)
theorem B2849485 : Blo 1688044 2849485 := bbase (se 3 (by rfl) ⟨534278, by rfl⟩ : syracuseStep 2849485 = 1068557) (by norm_num)
theorem B1899229 : Blo 1688044 1899229 := bbase (se 3 (by rfl) ⟨356105, by rfl⟩ : syracuseStep 1899229 = 712211) (by norm_num)
theorem B3799781 : Blo 1688044 3799781 := bbase (se 4 (by rfl) ⟨356229, by rfl⟩ : syracuseStep 3799781 = 712459) (by norm_num)
theorem B4692725 : Blo 1688044 4692725 := bbase (se 5 (by rfl) ⟨219971, by rfl⟩ : syracuseStep 4692725 = 439943) (by norm_num)
theorem B1899265 : Blo 1688044 1899265 := bbase (se 2 (by rfl) ⟨712224, by rfl⟩ : syracuseStep 1899265 = 1424449) (by norm_num)
theorem B4274957 : Blo 1688044 4274957 := bbase (se 3 (by rfl) ⟨801554, by rfl⟩ : syracuseStep 4274957 = 1603109) (by norm_num)
theorem B12819221 : Blo 1688044 12819221 := bbase (se 6 (by rfl) ⟨300450, by rfl⟩ : syracuseStep 12819221 = 600901) (by norm_num)
theorem B1899301 : Blo 1688044 1899301 := bbase (se 4 (by rfl) ⟨178059, by rfl⟩ : syracuseStep 1899301 = 356119) (by norm_num)
theorem B2849573 : Blo 1688044 2849573 := bbase (se 4 (by rfl) ⟨267147, by rfl⟩ : syracuseStep 2849573 = 534295) (by norm_num)
theorem B3799853 : Blo 1688044 3799853 := bbase (se 3 (by rfl) ⟨712472, by rfl⟩ : syracuseStep 3799853 = 1424945) (by norm_num)
theorem B2136881 : Blo 1688044 2136881 := bbase (se 2 (by rfl) ⟨801330, by rfl⟩ : syracuseStep 2136881 = 1602661) (by norm_num)
theorem B1899337 : Blo 1688044 1899337 := bbase (se 2 (by rfl) ⟨712251, by rfl⟩ : syracuseStep 1899337 = 1424503) (by norm_num)
theorem B2136937 : Blo 1688044 2136937 := bbase (se 2 (by rfl) ⟨801351, by rfl⟩ : syracuseStep 2136937 = 1602703) (by norm_num)
theorem B1899373 : Blo 1688044 1899373 := bbase (se 3 (by rfl) ⟨356132, by rfl⟩ : syracuseStep 1899373 = 712265) (by norm_num)
theorem B3799925 : Blo 1688044 3799925 := bbase (se 5 (by rfl) ⟨178121, by rfl⟩ : syracuseStep 3799925 = 356243) (by norm_num)
theorem B1899409 : Blo 1688044 1899409 := bbase (se 2 (by rfl) ⟨712278, by rfl⟩ : syracuseStep 1899409 = 1424557) (by norm_num)
theorem B2849701 : Blo 1688044 2849701 := bbase (se 4 (by rfl) ⟨267159, by rfl⟩ : syracuseStep 2849701 = 534319) (by norm_num)
theorem B3251117 : Blo 1688044 3251117 := bbase (se 3 (by rfl) ⟨609584, by rfl⟩ : syracuseStep 3251117 = 1219169) (by norm_num)
theorem B1899445 : Blo 1688044 1899445 := bbase (se 5 (by rfl) ⟨89036, by rfl⟩ : syracuseStep 1899445 = 178073) (by norm_num)
theorem B3799997 : Blo 1688044 3799997 := bbase (se 3 (by rfl) ⟨712499, by rfl⟩ : syracuseStep 3799997 = 1424999) (by norm_num)
theorem B2137033 : Blo 1688044 2137033 := bbase (se 2 (by rfl) ⟨801387, by rfl⟩ : syracuseStep 2137033 = 1602775) (by norm_num)
theorem B1899481 : Blo 1688044 1899481 := bbase (se 2 (by rfl) ⟨712305, by rfl⟩ : syracuseStep 1899481 = 1424611) (by norm_num)
theorem B3423197 : Blo 1688044 3423197 := bbase (se 3 (by rfl) ⟨641849, by rfl⟩ : syracuseStep 3423197 = 1283699) (by norm_num)
theorem B1899517 : Blo 1688044 1899517 := bbase (se 3 (by rfl) ⟨356159, by rfl⟩ : syracuseStep 1899517 = 712319) (by norm_num)
theorem B2849789 : Blo 1688044 2849789 := bbase (se 3 (by rfl) ⟨534335, by rfl⟩ : syracuseStep 2849789 = 1068671) (by norm_num)
theorem B3800069 : Blo 1688044 3800069 := bbase (se 4 (by rfl) ⟨356256, by rfl⟩ : syracuseStep 3800069 = 712513) (by norm_num)
theorem B1899553 : Blo 1688044 1899553 := bbase (se 2 (by rfl) ⟨712332, by rfl⟩ : syracuseStep 1899553 = 1424665) (by norm_num)
theorem B1899589 : Blo 1688044 1899589 := bbase (se 4 (by rfl) ⟨178086, by rfl⟩ : syracuseStep 1899589 = 356173) (by norm_num)
theorem B8551493 : Blo 1688044 8551493 := bbase (se 4 (by rfl) ⟨801702, by rfl⟩ : syracuseStep 8551493 = 1603405) (by norm_num)
theorem B3800141 : Blo 1688044 3800141 := bbase (se 3 (by rfl) ⟨712526, by rfl⟩ : syracuseStep 3800141 = 1425053) (by norm_num)
theorem B1711189 : Blo 1688044 1711189 := bbase (se 8 (by rfl) ⟨10026, by rfl⟩ : syracuseStep 1711189 = 20053) (by norm_num)
theorem B4275301 : Blo 1688044 4275301 := bbase (se 4 (by rfl) ⟨400809, by rfl⟩ : syracuseStep 4275301 = 801619) (by norm_num)
theorem B1899625 : Blo 1688044 1899625 := bbase (se 2 (by rfl) ⟨712359, by rfl⟩ : syracuseStep 1899625 = 1424719) (by norm_num)
theorem B2137205 : Blo 1688044 2137205 := bbase (se 5 (by rfl) ⟨100181, by rfl⟩ : syracuseStep 2137205 = 200363) (by norm_num)
theorem B5700725 : Blo 1688044 5700725 := bbase (se 5 (by rfl) ⟨267221, by rfl⟩ : syracuseStep 5700725 = 534443) (by norm_num)
theorem B2849917 : Blo 1688044 2849917 := bbase (se 3 (by rfl) ⟨534359, by rfl⟩ : syracuseStep 2849917 = 1068719) (by norm_num)
theorem B1899661 : Blo 1688044 1899661 := bbase (se 3 (by rfl) ⟨356186, by rfl⟩ : syracuseStep 1899661 = 712373) (by norm_num)
theorem B3800213 : Blo 1688044 3800213 := bbase (se 6 (by rfl) ⟨89067, by rfl⟩ : syracuseStep 3800213 = 178135) (by norm_num)
theorem B2137261 : Blo 1688044 2137261 := bbase (se 3 (by rfl) ⟨400736, by rfl⟩ : syracuseStep 2137261 = 801473) (by norm_num)
theorem B1899697 : Blo 1688044 1899697 := bbase (se 2 (by rfl) ⟨712386, by rfl⟩ : syracuseStep 1899697 = 1424773) (by norm_num)
theorem B1899733 : Blo 1688044 1899733 := bbase (se 7 (by rfl) ⟨22262, by rfl⟩ : syracuseStep 1899733 = 44525) (by norm_num)
theorem B2850005 : Blo 1688044 2850005 := bbase (se 7 (by rfl) ⟨33398, by rfl⟩ : syracuseStep 2850005 = 66797) (by norm_num)
theorem B4275413 : Blo 1688044 4275413 := bbase (se 7 (by rfl) ⟨50102, by rfl⟩ : syracuseStep 4275413 = 100205) (by norm_num)
theorem B3800285 : Blo 1688044 3800285 := bbase (se 3 (by rfl) ⟨712553, by rfl⟩ : syracuseStep 3800285 = 1425107) (by norm_num)
theorem B1899769 : Blo 1688044 1899769 := bbase (se 2 (by rfl) ⟨712413, by rfl⟩ : syracuseStep 1899769 = 1424827) (by norm_num)
theorem B2137357 : Blo 1688044 2137357 := bbase (se 3 (by rfl) ⟨400754, by rfl⟩ : syracuseStep 2137357 = 801509) (by norm_num)
theorem B1899805 : Blo 1688044 1899805 := bbase (se 3 (by rfl) ⟨356213, by rfl⟩ : syracuseStep 1899805 = 712427) (by norm_num)
theorem B3800357 : Blo 1688044 3800357 := bbase (se 4 (by rfl) ⟨356283, by rfl⟩ : syracuseStep 3800357 = 712567) (by norm_num)
theorem B1899841 : Blo 1688044 1899841 := bbase (se 2 (by rfl) ⟨712440, by rfl⟩ : syracuseStep 1899841 = 1424881) (by norm_num)
theorem B2850133 : Blo 1688044 2850133 := bbase (se 11 (by rfl) ⟨2087, by rfl⟩ : syracuseStep 2850133 = 4175) (by norm_num)
theorem B1899877 : Blo 1688044 1899877 := bbase (se 4 (by rfl) ⟨178113, by rfl⟩ : syracuseStep 1899877 = 356227) (by norm_num)
theorem B3800429 : Blo 1688044 3800429 := bbase (se 3 (by rfl) ⟨712580, by rfl⟩ : syracuseStep 3800429 = 1425161) (by norm_num)
theorem B14433653 : Blo 1688044 14433653 := bbase (se 5 (by rfl) ⟨676577, by rfl⟩ : syracuseStep 14433653 = 1353155) (by norm_num)
theorem B1899913 : Blo 1688044 1899913 := bbase (se 2 (by rfl) ⟨712467, by rfl⟩ : syracuseStep 1899913 = 1424935) (by norm_num)
theorem B4275605 : Blo 1688044 4275605 := bbase (se 6 (by rfl) ⟨100209, by rfl⟩ : syracuseStep 4275605 = 200419) (by norm_num)
theorem B1899949 : Blo 1688044 1899949 := bbase (se 3 (by rfl) ⟨356240, by rfl⟩ : syracuseStep 1899949 = 712481) (by norm_num)
theorem B2850221 : Blo 1688044 2850221 := bbase (se 3 (by rfl) ⟨534416, by rfl⟩ : syracuseStep 2850221 = 1068833) (by norm_num)
theorem B3800501 : Blo 1688044 3800501 := bbase (se 5 (by rfl) ⟨178148, by rfl⟩ : syracuseStep 3800501 = 356297) (by norm_num)
theorem B2137529 : Blo 1688044 2137529 := bbase (se 2 (by rfl) ⟨801573, by rfl⟩ : syracuseStep 2137529 = 1603147) (by norm_num)
theorem B1711549 : Blo 1688044 1711549 := bbase (se 3 (by rfl) ⟨320915, by rfl⟩ : syracuseStep 1711549 = 641831) (by norm_num)
theorem B1899985 : Blo 1688044 1899985 := bbase (se 2 (by rfl) ⟨712494, by rfl⟩ : syracuseStep 1899985 = 1424989) (by norm_num)
theorem B2137585 : Blo 1688044 2137585 := bbase (se 2 (by rfl) ⟨801594, by rfl⟩ : syracuseStep 2137585 = 1603189) (by norm_num)
theorem B1900021 : Blo 1688044 1900021 := bbase (se 5 (by rfl) ⟨89063, by rfl⟩ : syracuseStep 1900021 = 178127) (by norm_num)
theorem B3800573 : Blo 1688044 3800573 := bbase (se 3 (by rfl) ⟨712607, by rfl⟩ : syracuseStep 3800573 = 1425215) (by norm_num)
theorem B1900057 : Blo 1688044 1900057 := bbase (se 2 (by rfl) ⟨712521, by rfl⟩ : syracuseStep 1900057 = 1425043) (by norm_num)
theorem B5701157 : Blo 1688044 5701157 := bbase (se 4 (by rfl) ⟨534483, by rfl⟩ : syracuseStep 5701157 = 1068967) (by norm_num)
theorem B2850349 : Blo 1688044 2850349 := bbase (se 3 (by rfl) ⟨534440, by rfl⟩ : syracuseStep 2850349 = 1068881) (by norm_num)
theorem B1900093 : Blo 1688044 1900093 := bbase (se 3 (by rfl) ⟨356267, by rfl⟩ : syracuseStep 1900093 = 712535) (by norm_num)
theorem B3800645 : Blo 1688044 3800645 := bbase (se 4 (by rfl) ⟨356310, by rfl⟩ : syracuseStep 3800645 = 712621) (by norm_num)
theorem B2137681 : Blo 1688044 2137681 := bbase (se 2 (by rfl) ⟨801630, by rfl⟩ : syracuseStep 2137681 = 1603261) (by norm_num)
theorem B1900129 : Blo 1688044 1900129 := bbase (se 2 (by rfl) ⟨712548, by rfl⟩ : syracuseStep 1900129 = 1425097) (by norm_num)
theorem B1900165 : Blo 1688044 1900165 := bbase (se 4 (by rfl) ⟨178140, by rfl⟩ : syracuseStep 1900165 = 356281) (by norm_num)
theorem B2850437 : Blo 1688044 2850437 := bbase (se 4 (by rfl) ⟨267228, by rfl⟩ : syracuseStep 2850437 = 534457) (by norm_num)
theorem B3800717 : Blo 1688044 3800717 := bbase (se 3 (by rfl) ⟨712634, by rfl⟩ : syracuseStep 3800717 = 1425269) (by norm_num)
theorem B1900201 : Blo 1688044 1900201 := bbase (se 2 (by rfl) ⟨712575, by rfl⟩ : syracuseStep 1900201 = 1425151) (by norm_num)
theorem B1900237 : Blo 1688044 1900237 := bbase (se 3 (by rfl) ⟨356294, by rfl⟩ : syracuseStep 1900237 = 712589) (by norm_num)
theorem B3800789 : Blo 1688044 3800789 := bbase (se 7 (by rfl) ⟨44540, by rfl⟩ : syracuseStep 3800789 = 89081) (by norm_num)
theorem B4275949 : Blo 1688044 4275949 := bbase (se 3 (by rfl) ⟨801740, by rfl⟩ : syracuseStep 4275949 = 1603481) (by norm_num)
theorem B1900273 : Blo 1688044 1900273 := bbase (se 2 (by rfl) ⟨712602, by rfl⟩ : syracuseStep 1900273 = 1425205) (by norm_num)
theorem B4112117 : Blo 1688044 4112117 := bbase (se 5 (by rfl) ⟨192755, by rfl⟩ : syracuseStep 4112117 = 385511) (by norm_num)
theorem B2137853 : Blo 1688044 2137853 := bbase (se 3 (by rfl) ⟨400847, by rfl⟩ : syracuseStep 2137853 = 801695) (by norm_num)
theorem B2850565 : Blo 1688044 2850565 := bbase (se 4 (by rfl) ⟨267240, by rfl⟩ : syracuseStep 2850565 = 534481) (by norm_num)
theorem B10821397 : Blo 1688044 10821397 := bbase (se 6 (by rfl) ⟨253626, by rfl⟩ : syracuseStep 10821397 = 507253) (by norm_num)
theorem B1900309 : Blo 1688044 1900309 := bbase (se 6 (by rfl) ⟨44538, by rfl⟩ : syracuseStep 1900309 = 89077) (by norm_num)
theorem B3800861 : Blo 1688044 3800861 := bbase (se 3 (by rfl) ⟨712661, by rfl⟩ : syracuseStep 3800861 = 1425323) (by norm_num)
theorem B2137909 : Blo 1688044 2137909 := bbase (se 5 (by rfl) ⟨100214, by rfl⟩ : syracuseStep 2137909 = 200429) (by norm_num)
theorem B1900345 : Blo 1688044 1900345 := bbase (se 2 (by rfl) ⟨712629, by rfl⟩ : syracuseStep 1900345 = 1425259) (by norm_num)
theorem B1900381 : Blo 1688044 1900381 := bbase (se 3 (by rfl) ⟨356321, by rfl⟩ : syracuseStep 1900381 = 712643) (by norm_num)
theorem B2850653 : Blo 1688044 2850653 := bbase (se 3 (by rfl) ⟨534497, by rfl⟩ : syracuseStep 2850653 = 1068995) (by norm_num)
theorem B4276061 : Blo 1688044 4276061 := bbase (se 3 (by rfl) ⟨801761, by rfl⟩ : syracuseStep 4276061 = 1603523) (by norm_num)
theorem B3800933 : Blo 1688044 3800933 := bbase (se 4 (by rfl) ⟨356337, by rfl⟩ : syracuseStep 3800933 = 712675) (by norm_num)
theorem B1900417 : Blo 1688044 1900417 := bbase (se 2 (by rfl) ⟨712656, by rfl⟩ : syracuseStep 1900417 = 1425313) (by norm_num)
theorem B2138005 : Blo 1688044 2138005 := bbase (se 6 (by rfl) ⟨50109, by rfl⟩ : syracuseStep 2138005 = 100219) (by norm_num)
theorem B1900453 : Blo 1688044 1900453 := bbase (se 4 (by rfl) ⟨178167, by rfl⟩ : syracuseStep 1900453 = 356335) (by norm_num)
theorem B3801005 : Blo 1688044 3801005 := bbase (se 3 (by rfl) ⟨712688, by rfl⟩ : syracuseStep 3801005 = 1425377) (by norm_num)
theorem B1900489 : Blo 1688044 1900489 := bbase (se 2 (by rfl) ⟨712683, by rfl⟩ : syracuseStep 1900489 = 1425367) (by norm_num)
theorem B5701589 : Blo 1688044 5701589 := bbase (se 7 (by rfl) ⟨66815, by rfl⟩ : syracuseStep 5701589 = 133631) (by norm_num)
theorem B2850781 : Blo 1688044 2850781 := bbase (se 3 (by rfl) ⟨534521, by rfl⟩ : syracuseStep 2850781 = 1069043) (by norm_num)
theorem B1712101 : Blo 1688044 1712101 := bbase (se 4 (by rfl) ⟨160509, by rfl⟩ : syracuseStep 1712101 = 321019) (by norm_num)
theorem B1900525 : Blo 1688044 1900525 := bbase (se 3 (by rfl) ⟨356348, by rfl⟩ : syracuseStep 1900525 = 712697) (by norm_num)
theorem B3801077 : Blo 1688044 3801077 := bbase (se 5 (by rfl) ⟨178175, by rfl⟩ : syracuseStep 3801077 = 356351) (by norm_num)
theorem B6414349 : Blo 1688044 6414349 := bstep (se 3 (by rfl) ⟨1202690, by rfl⟩ : syracuseStep 6414349 = 2405381) B2405381
theorem B2850835 : Blo 1688044 2850835 := bstep (se 1 (by rfl) ⟨2138126, by rfl⟩ : syracuseStep 2850835 = 4276253) B4276253
theorem B1900579 : Blo 1688044 1900579 := bstep (se 1 (by rfl) ⟨1425434, by rfl⟩ : syracuseStep 1900579 = 2850869) B2850869
theorem B4276273 : Blo 1688044 4276273 := bstep (se 2 (by rfl) ⟨1603602, by rfl⟩ : syracuseStep 4276273 = 3207205) B3207205
theorem B3850321 : Blo 1688044 3850321 := bstep (se 2 (by rfl) ⟨1443870, by rfl⟩ : syracuseStep 3850321 = 2887741) B2887741
theorem B4808803 : Blo 1688044 4808803 := bstep (se 1 (by rfl) ⟨3606602, by rfl⟩ : syracuseStep 4808803 = 7213205) B7213205
theorem B2850977 : Blo 1688044 2850977 := bstep (se 2 (by rfl) ⟨1069116, by rfl⟩ : syracuseStep 2850977 = 2138233) B2138233
theorem B5701805 : Blo 1688044 5701805 := bstep (se 3 (by rfl) ⟨1069088, by rfl⟩ : syracuseStep 5701805 = 2138177) B2138177
theorem B1900723 : Blo 1688044 1900723 := bstep (se 1 (by rfl) ⟨1425542, by rfl⟩ : syracuseStep 1900723 = 2851085) B2851085
theorem B5701859 : Blo 1688044 5701859 := bstep (se 1 (by rfl) ⟨4276394, by rfl⟩ : syracuseStep 5701859 = 8552789) B8552789
theorem B2138339 : Blo 1688044 2138339 := bstep (se 1 (by rfl) ⟨1603754, by rfl⟩ : syracuseStep 2138339 = 3207509) B3207509
theorem B3801329 : Blo 1688044 3801329 := bstep (se 2 (by rfl) ⟨1425498, by rfl⟩ : syracuseStep 3801329 = 2850997) B2850997
theorem B4808963 : Blo 1688044 4808963 := bstep (se 1 (by rfl) ⟨3606722, by rfl⟩ : syracuseStep 4808963 = 7213445) B7213445
theorem B3801347 : Blo 1688044 3801347 := bstep (se 1 (by rfl) ⟨2851010, by rfl⟩ : syracuseStep 3801347 = 5702021) B5702021
theorem B12828941 : Blo 1688044 12828941 := bstep (se 3 (by rfl) ⟨2405426, by rfl⟩ : syracuseStep 12828941 = 4810853) B4810853
theorem B2851105 : Blo 1688044 2851105 := bstep (se 2 (by rfl) ⟨1069164, by rfl⟩ : syracuseStep 2851105 = 2138329) B2138329
theorem B7414051 : Blo 1688044 7414051 := bstep (se 1 (by rfl) ⟨5560538, by rfl⟩ : syracuseStep 7414051 = 11121077) B11121077
theorem B4276547 : Blo 1688044 4276547 := bstep (se 1 (by rfl) ⟨3207410, by rfl⟩ : syracuseStep 4276547 = 6414821) B6414821
theorem B2851139 : Blo 1688044 2851139 := bstep (se 1 (by rfl) ⟨2138354, by rfl⟩ : syracuseStep 2851139 = 4276709) B4276709
theorem B1900867 : Blo 1688044 1900867 := bstep (se 1 (by rfl) ⟨1425650, by rfl⟩ : syracuseStep 1900867 = 2851301) B2851301
theorem B2851267 : Blo 1688044 2851267 := bstep (se 1 (by rfl) ⟨2138450, by rfl⟩ : syracuseStep 2851267 = 4276901) B4276901
theorem B9126341 : Blo 1688044 9126341 := bstep (se 4 (by rfl) ⟨855594, by rfl⟩ : syracuseStep 9126341 = 1711189) B1711189
theorem B1901011 : Blo 1688044 1901011 := bstep (se 1 (by rfl) ⟨1425758, by rfl⟩ : syracuseStep 1901011 = 2851517) B2851517
theorem B5702129 : Blo 1688044 5702129 := bstep (se 2 (by rfl) ⟨2138298, by rfl⟩ : syracuseStep 5702129 = 4276597) B4276597
theorem B1688051 : Blo 1688044 1688051 := bstep (se 1 (by rfl) ⟨1266038, by rfl⟩ : syracuseStep 1688051 = 2532077) B2532077
theorem B1688067 : Blo 1688044 1688067 := bstep (se 1 (by rfl) ⟨1266050, by rfl⟩ : syracuseStep 1688067 = 2532101) B2532101
theorem B4276739 : Blo 1688044 4276739 := bstep (se 1 (by rfl) ⟨3207554, by rfl⟩ : syracuseStep 4276739 = 6415109) B6415109
theorem B3801617 : Blo 1688044 3801617 := bstep (se 2 (by rfl) ⟨1425606, by rfl⟩ : syracuseStep 3801617 = 2851213) B2851213
theorem B1688083 : Blo 1688044 1688083 := bstep (se 1 (by rfl) ⟨1266062, by rfl⟩ : syracuseStep 1688083 = 2532125) B2532125
theorem B1688099 : Blo 1688044 1688099 := bstep (se 1 (by rfl) ⟨1266074, by rfl⟩ : syracuseStep 1688099 = 2532149) B2532149
theorem B3801635 : Blo 1688044 3801635 := bstep (se 1 (by rfl) ⟨2851226, by rfl⟩ : syracuseStep 3801635 = 5702453) B5702453
theorem B1688115 : Blo 1688044 1688115 := bstep (se 1 (by rfl) ⟨1266086, by rfl⟩ : syracuseStep 1688115 = 2532173) B2532173
theorem B1688131 : Blo 1688044 1688131 := bstep (se 1 (by rfl) ⟨1266098, by rfl⟩ : syracuseStep 1688131 = 2532197) B2532197
theorem B2851409 : Blo 1688044 2851409 := bstep (se 2 (by rfl) ⟨1069278, by rfl⟩ : syracuseStep 2851409 = 2138557) B2138557
theorem B1688147 : Blo 1688044 1688147 := bstep (se 1 (by rfl) ⟨1266110, by rfl⟩ : syracuseStep 1688147 = 2532221) B2532221
theorem B1688163 : Blo 1688044 1688163 := bstep (se 1 (by rfl) ⟨1266122, by rfl⟩ : syracuseStep 1688163 = 2532245) B2532245
theorem B1901155 : Blo 1688044 1901155 := bstep (se 1 (by rfl) ⟨1425866, by rfl⟩ : syracuseStep 1901155 = 2851733) B2851733
theorem B4563569 : Blo 1688044 4563569 := bstep (se 2 (by rfl) ⟨1711338, by rfl⟩ : syracuseStep 4563569 = 3422677) B3422677
theorem B9749105 : Blo 1688044 9749105 := bstep (se 2 (by rfl) ⟨3655914, by rfl⟩ : syracuseStep 9749105 = 7311829) B7311829
theorem B1688179 : Blo 1688044 1688179 := bstep (se 1 (by rfl) ⟨1266134, by rfl⟩ : syracuseStep 1688179 = 2532269) B2532269
theorem B1688195 : Blo 1688044 1688195 := bstep (se 1 (by rfl) ⟨1266146, by rfl⟩ : syracuseStep 1688195 = 2532293) B2532293
theorem B9618061 : Blo 1688044 9618061 := bstep (se 3 (by rfl) ⟨1803386, by rfl⟩ : syracuseStep 9618061 = 3606773) B3606773
theorem B1688211 : Blo 1688044 1688211 := bstep (se 1 (by rfl) ⟨1266158, by rfl⟩ : syracuseStep 1688211 = 2532317) B2532317
theorem B1688227 : Blo 1688044 1688227 := bstep (se 1 (by rfl) ⟨1266170, by rfl⟩ : syracuseStep 1688227 = 2532341) B2532341
theorem B3850915 : Blo 1688044 3850915 := bstep (se 1 (by rfl) ⟨2888186, by rfl⟩ : syracuseStep 3850915 = 5776373) B5776373
theorem B1688243 : Blo 1688044 1688243 := bstep (se 1 (by rfl) ⟨1266182, by rfl⟩ : syracuseStep 1688243 = 2532365) B2532365
theorem B1688259 : Blo 1688044 1688259 := bstep (se 1 (by rfl) ⟨1266194, by rfl⟩ : syracuseStep 1688259 = 2532389) B2532389
theorem B24355525 : Blo 1688044 24355525 := bstep (se 4 (by rfl) ⟨2283330, by rfl⟩ : syracuseStep 24355525 = 4566661) B4566661
theorem B2851537 : Blo 1688044 2851537 := bstep (se 2 (by rfl) ⟨1069326, by rfl⟩ : syracuseStep 2851537 = 2138653) B2138653
theorem B1688275 : Blo 1688044 1688275 := bstep (se 1 (by rfl) ⟨1266206, by rfl⟩ : syracuseStep 1688275 = 2532413) B2532413
theorem B1688291 : Blo 1688044 1688291 := bstep (se 1 (by rfl) ⟨1266218, by rfl⟩ : syracuseStep 1688291 = 2532437) B2532437
theorem B11715299 : Blo 1688044 11715299 := bstep (se 1 (by rfl) ⟨8786474, by rfl⟩ : syracuseStep 11715299 = 17572949) B17572949
theorem B2532083 : Blo 1688044 2532083 := bstep (se 1 (by rfl) ⟨1899062, by rfl⟩ : syracuseStep 2532083 = 3798125) B3798125
theorem B1688307 : Blo 1688044 1688307 := bstep (se 1 (by rfl) ⟨1266230, by rfl⟩ : syracuseStep 1688307 = 2532461) B2532461
theorem B2851571 : Blo 1688044 2851571 := bstep (se 1 (by rfl) ⟨2138678, by rfl⟩ : syracuseStep 2851571 = 4277357) B4277357
theorem B1901299 : Blo 1688044 1901299 := bstep (se 1 (by rfl) ⟨1425974, by rfl⟩ : syracuseStep 1901299 = 2851949) B2851949
theorem B1688323 : Blo 1688044 1688323 := bstep (se 1 (by rfl) ⟨1266242, by rfl⟩ : syracuseStep 1688323 = 2532485) B2532485
theorem B2532113 : Blo 1688044 2532113 := bstep (se 2 (by rfl) ⟨949542, by rfl⟩ : syracuseStep 2532113 = 1899085) B1899085
theorem B1688339 : Blo 1688044 1688339 := bstep (se 1 (by rfl) ⟨1266254, by rfl⟩ : syracuseStep 1688339 = 2532509) B2532509
theorem B2532131 : Blo 1688044 2532131 := bstep (se 1 (by rfl) ⟨1899098, by rfl⟩ : syracuseStep 2532131 = 3798197) B3798197
theorem B1688355 : Blo 1688044 1688355 := bstep (se 1 (by rfl) ⟨1266266, by rfl⟩ : syracuseStep 1688355 = 2532533) B2532533
theorem B6415139 : Blo 1688044 6415139 := bstep (se 1 (by rfl) ⟨4811354, by rfl⟩ : syracuseStep 6415139 = 9622709) B9622709
theorem B3801905 : Blo 1688044 3801905 := bstep (se 2 (by rfl) ⟨1425714, by rfl⟩ : syracuseStep 3801905 = 2851429) B2851429
theorem B1688371 : Blo 1688044 1688371 := bstep (se 1 (by rfl) ⟨1266278, by rfl⟩ : syracuseStep 1688371 = 2532557) B2532557
theorem B2532161 : Blo 1688044 2532161 := bstep (se 2 (by rfl) ⟨949560, by rfl⟩ : syracuseStep 2532161 = 1899121) B1899121
theorem B1688387 : Blo 1688044 1688387 := bstep (se 1 (by rfl) ⟨1266290, by rfl⟩ : syracuseStep 1688387 = 2532581) B2532581
theorem B3801923 : Blo 1688044 3801923 := bstep (se 1 (by rfl) ⟨2851442, by rfl⟩ : syracuseStep 3801923 = 5702885) B5702885
theorem B2532179 : Blo 1688044 2532179 := bstep (se 1 (by rfl) ⟨1899134, by rfl⟩ : syracuseStep 2532179 = 3798269) B3798269
theorem B1688403 : Blo 1688044 1688403 := bstep (se 1 (by rfl) ⟨1266302, by rfl⟩ : syracuseStep 1688403 = 2532605) B2532605
theorem B1688419 : Blo 1688044 1688419 := bstep (se 1 (by rfl) ⟨1266314, by rfl⟩ : syracuseStep 1688419 = 2532629) B2532629
theorem B2532209 : Blo 1688044 2532209 := bstep (se 2 (by rfl) ⟨949578, by rfl⟩ : syracuseStep 2532209 = 1899157) B1899157
theorem B1688435 : Blo 1688044 1688435 := bstep (se 1 (by rfl) ⟨1266326, by rfl⟩ : syracuseStep 1688435 = 2532653) B2532653
theorem B2851699 : Blo 1688044 2851699 := bstep (se 1 (by rfl) ⟨2138774, by rfl⟩ : syracuseStep 2851699 = 4277549) B4277549
theorem B2532227 : Blo 1688044 2532227 := bstep (se 1 (by rfl) ⟨1899170, by rfl⟩ : syracuseStep 2532227 = 3798341) B3798341
theorem B1688451 : Blo 1688044 1688451 := bstep (se 1 (by rfl) ⟨1266338, by rfl⟩ : syracuseStep 1688451 = 2532677) B2532677
theorem B1688467 : Blo 1688044 1688467 := bstep (se 1 (by rfl) ⟨1266350, by rfl⟩ : syracuseStep 1688467 = 2532701) B2532701
theorem B2532257 : Blo 1688044 2532257 := bstep (se 2 (by rfl) ⟨949596, by rfl⟩ : syracuseStep 2532257 = 1899193) B1899193
theorem B1688483 : Blo 1688044 1688483 := bstep (se 1 (by rfl) ⟨1266362, by rfl⟩ : syracuseStep 1688483 = 2532725) B2532725
theorem B2532275 : Blo 1688044 2532275 := bstep (se 1 (by rfl) ⟨1899206, by rfl⟩ : syracuseStep 2532275 = 3798413) B3798413
theorem B1688499 : Blo 1688044 1688499 := bstep (se 1 (by rfl) ⟨1266374, by rfl⟩ : syracuseStep 1688499 = 2532749) B2532749
theorem B1688515 : Blo 1688044 1688515 := bstep (se 1 (by rfl) ⟨1266386, by rfl⟩ : syracuseStep 1688515 = 2532773) B2532773
theorem B2532305 : Blo 1688044 2532305 := bstep (se 2 (by rfl) ⟨949614, by rfl⟩ : syracuseStep 2532305 = 1899229) B1899229
theorem B1688531 : Blo 1688044 1688531 := bstep (se 1 (by rfl) ⟨1266398, by rfl⟩ : syracuseStep 1688531 = 2532797) B2532797
theorem B2532323 : Blo 1688044 2532323 := bstep (se 1 (by rfl) ⟨1899242, by rfl⟩ : syracuseStep 2532323 = 3798485) B3798485
theorem B1688547 : Blo 1688044 1688547 := bstep (se 1 (by rfl) ⟨1266410, by rfl⟩ : syracuseStep 1688547 = 2532821) B2532821
theorem B1688563 : Blo 1688044 1688563 := bstep (se 1 (by rfl) ⟨1266422, by rfl⟩ : syracuseStep 1688563 = 2532845) B2532845
theorem B2532353 : Blo 1688044 2532353 := bstep (se 2 (by rfl) ⟨949632, by rfl⟩ : syracuseStep 2532353 = 1899265) B1899265
theorem B1688579 : Blo 1688044 1688579 := bstep (se 1 (by rfl) ⟨1266434, by rfl⟩ : syracuseStep 1688579 = 2532869) B2532869
theorem B2851841 : Blo 1688044 2851841 := bstep (se 2 (by rfl) ⟨1069440, by rfl⟩ : syracuseStep 2851841 = 2138881) B2138881
theorem B5702669 : Blo 1688044 5702669 := bstep (se 3 (by rfl) ⟨1069250, by rfl⟩ : syracuseStep 5702669 = 2138501) B2138501
theorem B2532371 : Blo 1688044 2532371 := bstep (se 1 (by rfl) ⟨1899278, by rfl⟩ : syracuseStep 2532371 = 3798557) B3798557
theorem B1688595 : Blo 1688044 1688595 := bstep (se 1 (by rfl) ⟨1266446, by rfl⟩ : syracuseStep 1688595 = 2532893) B2532893
theorem B1688611 : Blo 1688044 1688611 := bstep (se 1 (by rfl) ⟨1266458, by rfl⟩ : syracuseStep 1688611 = 2532917) B2532917
theorem B2532401 : Blo 1688044 2532401 := bstep (se 2 (by rfl) ⟨949650, by rfl⟩ : syracuseStep 2532401 = 1899301) B1899301
theorem B1688627 : Blo 1688044 1688627 := bstep (se 1 (by rfl) ⟨1266470, by rfl⟩ : syracuseStep 1688627 = 2532941) B2532941
theorem B2532419 : Blo 1688044 2532419 := bstep (se 1 (by rfl) ⟨1899314, by rfl⟩ : syracuseStep 2532419 = 3798629) B3798629
theorem B1688643 : Blo 1688044 1688643 := bstep (se 1 (by rfl) ⟨1266482, by rfl⟩ : syracuseStep 1688643 = 2532965) B2532965
theorem B5702723 : Blo 1688044 5702723 := bstep (se 1 (by rfl) ⟨4277042, by rfl⟩ : syracuseStep 5702723 = 8554085) B8554085
theorem B2704465 : Blo 1688044 2704465 := bstep (se 2 (by rfl) ⟨1014174, by rfl⟩ : syracuseStep 2704465 = 2028349) B2028349
theorem B3802193 : Blo 1688044 3802193 := bstep (se 2 (by rfl) ⟨1425822, by rfl⟩ : syracuseStep 3802193 = 2851645) B2851645
theorem B1688659 : Blo 1688044 1688659 := bstep (se 1 (by rfl) ⟨1266494, by rfl⟩ : syracuseStep 1688659 = 2532989) B2532989
theorem B2532449 : Blo 1688044 2532449 := bstep (se 2 (by rfl) ⟨949668, by rfl⟩ : syracuseStep 2532449 = 1899337) B1899337
theorem B1688675 : Blo 1688044 1688675 := bstep (se 1 (by rfl) ⟨1266506, by rfl⟩ : syracuseStep 1688675 = 2533013) B2533013
theorem B3802211 : Blo 1688044 3802211 := bstep (se 1 (by rfl) ⟨2851658, by rfl⟩ : syracuseStep 3802211 = 5703317) B5703317
theorem B2532467 : Blo 1688044 2532467 := bstep (se 1 (by rfl) ⟨1899350, by rfl⟩ : syracuseStep 2532467 = 3798701) B3798701
theorem B1688691 : Blo 1688044 1688691 := bstep (se 1 (by rfl) ⟨1266518, by rfl⟩ : syracuseStep 1688691 = 2533037) B2533037
theorem B1688707 : Blo 1688044 1688707 := bstep (se 1 (by rfl) ⟨1266530, by rfl⟩ : syracuseStep 1688707 = 2533061) B2533061
theorem B2532497 : Blo 1688044 2532497 := bstep (se 2 (by rfl) ⟨949686, by rfl⟩ : syracuseStep 2532497 = 1899373) B1899373
theorem B1688723 : Blo 1688044 1688723 := bstep (se 1 (by rfl) ⟨1266542, by rfl⟩ : syracuseStep 1688723 = 2533085) B2533085
theorem B2532515 : Blo 1688044 2532515 := bstep (se 1 (by rfl) ⟨1899386, by rfl⟩ : syracuseStep 2532515 = 3798773) B3798773
theorem B1688739 : Blo 1688044 1688739 := bstep (se 1 (by rfl) ⟨1266554, by rfl⟩ : syracuseStep 1688739 = 2533109) B2533109
theorem B1688755 : Blo 1688044 1688755 := bstep (se 1 (by rfl) ⟨1266566, by rfl⟩ : syracuseStep 1688755 = 2533133) B2533133
theorem B2532545 : Blo 1688044 2532545 := bstep (se 2 (by rfl) ⟨949704, by rfl⟩ : syracuseStep 2532545 = 1899409) B1899409
theorem B1688771 : Blo 1688044 1688771 := bstep (se 1 (by rfl) ⟨1266578, by rfl⟩ : syracuseStep 1688771 = 2533157) B2533157
theorem B2532563 : Blo 1688044 2532563 := bstep (se 1 (by rfl) ⟨1899422, by rfl⟩ : syracuseStep 2532563 = 3798845) B3798845
theorem B1688787 : Blo 1688044 1688787 := bstep (se 1 (by rfl) ⟨1266590, by rfl⟩ : syracuseStep 1688787 = 2533181) B2533181
theorem B1688803 : Blo 1688044 1688803 := bstep (se 1 (by rfl) ⟨1266602, by rfl⟩ : syracuseStep 1688803 = 2533205) B2533205
theorem B2532593 : Blo 1688044 2532593 := bstep (se 2 (by rfl) ⟨949722, by rfl⟩ : syracuseStep 2532593 = 1899445) B1899445
theorem B1688819 : Blo 1688044 1688819 := bstep (se 1 (by rfl) ⟨1266614, by rfl⟩ : syracuseStep 1688819 = 2533229) B2533229
theorem B2532611 : Blo 1688044 2532611 := bstep (se 1 (by rfl) ⟨1899458, by rfl⟩ : syracuseStep 2532611 = 3798917) B3798917
theorem B1688835 : Blo 1688044 1688835 := bstep (se 1 (by rfl) ⟨1266626, by rfl⟩ : syracuseStep 1688835 = 2533253) B2533253
theorem B1688851 : Blo 1688044 1688851 := bstep (se 1 (by rfl) ⟨1266638, by rfl⟩ : syracuseStep 1688851 = 2533277) B2533277
theorem B2532641 : Blo 1688044 2532641 := bstep (se 2 (by rfl) ⟨949740, by rfl⟩ : syracuseStep 2532641 = 1899481) B1899481
theorem B1688867 : Blo 1688044 1688867 := bstep (se 1 (by rfl) ⟨1266650, by rfl⟩ : syracuseStep 1688867 = 2533301) B2533301
theorem B7218467 : Blo 1688044 7218467 := bstep (se 1 (by rfl) ⟨5413850, by rfl⟩ : syracuseStep 7218467 = 10827701) B10827701
theorem B3605809 : Blo 1688044 3605809 := bstep (se 2 (by rfl) ⟨1352178, by rfl⟩ : syracuseStep 3605809 = 2704357) B2704357
theorem B4810033 : Blo 1688044 4810033 := bstep (se 2 (by rfl) ⟨1803762, by rfl⟩ : syracuseStep 4810033 = 3607525) B3607525
theorem B2532659 : Blo 1688044 2532659 := bstep (se 1 (by rfl) ⟨1899494, by rfl⟩ : syracuseStep 2532659 = 3798989) B3798989
theorem B1688883 : Blo 1688044 1688883 := bstep (se 1 (by rfl) ⟨1266662, by rfl⟩ : syracuseStep 1688883 = 2533325) B2533325
theorem B1688899 : Blo 1688044 1688899 := bstep (se 1 (by rfl) ⟨1266674, by rfl⟩ : syracuseStep 1688899 = 2533349) B2533349
theorem B9889093 : Blo 1688044 9889093 := bstep (se 4 (by rfl) ⟨927102, by rfl⟩ : syracuseStep 9889093 = 1854205) B1854205
theorem B2532689 : Blo 1688044 2532689 := bstep (se 2 (by rfl) ⟨949758, by rfl⟩ : syracuseStep 2532689 = 1899517) B1899517
theorem B1688915 : Blo 1688044 1688915 := bstep (se 1 (by rfl) ⟨1266686, by rfl⟩ : syracuseStep 1688915 = 2533373) B2533373
theorem B5702993 : Blo 1688044 5702993 := bstep (se 2 (by rfl) ⟨2138622, by rfl⟩ : syracuseStep 5702993 = 4277245) B4277245
theorem B2532707 : Blo 1688044 2532707 := bstep (se 1 (by rfl) ⟨1899530, by rfl⟩ : syracuseStep 2532707 = 3799061) B3799061
theorem B1688931 : Blo 1688044 1688931 := bstep (se 1 (by rfl) ⟨1266698, by rfl⟩ : syracuseStep 1688931 = 2533397) B2533397
theorem B3802481 : Blo 1688044 3802481 := bstep (se 2 (by rfl) ⟨1425930, by rfl⟩ : syracuseStep 3802481 = 2851861) B2851861
theorem B1688947 : Blo 1688044 1688947 := bstep (se 1 (by rfl) ⟨1266710, by rfl⟩ : syracuseStep 1688947 = 2533421) B2533421
theorem B2532737 : Blo 1688044 2532737 := bstep (se 2 (by rfl) ⟨949776, by rfl⟩ : syracuseStep 2532737 = 1899553) B1899553
theorem B1688963 : Blo 1688044 1688963 := bstep (se 1 (by rfl) ⟨1266722, by rfl⟩ : syracuseStep 1688963 = 2533445) B2533445
theorem B3802499 : Blo 1688044 3802499 := bstep (se 1 (by rfl) ⟨2851874, by rfl⟩ : syracuseStep 3802499 = 5703749) B5703749
theorem B2532755 : Blo 1688044 2532755 := bstep (se 1 (by rfl) ⟨1899566, by rfl⟩ : syracuseStep 2532755 = 3799133) B3799133
theorem B1688979 : Blo 1688044 1688979 := bstep (se 1 (by rfl) ⟨1266734, by rfl⟩ : syracuseStep 1688979 = 2533469) B2533469
theorem B1688995 : Blo 1688044 1688995 := bstep (se 1 (by rfl) ⟨1266746, by rfl⟩ : syracuseStep 1688995 = 2533493) B2533493
theorem B2532785 : Blo 1688044 2532785 := bstep (se 2 (by rfl) ⟨949794, by rfl⟩ : syracuseStep 2532785 = 1899589) B1899589
theorem B6415793 : Blo 1688044 6415793 := bstep (se 2 (by rfl) ⟨2405922, by rfl⟩ : syracuseStep 6415793 = 4811845) B4811845
theorem B1689011 : Blo 1688044 1689011 := bstep (se 1 (by rfl) ⟨1266758, by rfl⟩ : syracuseStep 1689011 = 2533517) B2533517
theorem B4277681 : Blo 1688044 4277681 := bstep (se 2 (by rfl) ⟨1604130, by rfl⟩ : syracuseStep 4277681 = 3208261) B3208261
theorem B2532803 : Blo 1688044 2532803 := bstep (se 1 (by rfl) ⟨1899602, by rfl⟩ : syracuseStep 2532803 = 3799205) B3799205
theorem B1689027 : Blo 1688044 1689027 := bstep (se 1 (by rfl) ⟨1266770, by rfl⟩ : syracuseStep 1689027 = 2533541) B2533541
theorem B1689043 : Blo 1688044 1689043 := bstep (se 1 (by rfl) ⟨1266782, by rfl⟩ : syracuseStep 1689043 = 2533565) B2533565
theorem B2532833 : Blo 1688044 2532833 := bstep (se 2 (by rfl) ⟨949812, by rfl⟩ : syracuseStep 2532833 = 1899625) B1899625
theorem B1689059 : Blo 1688044 1689059 := bstep (se 1 (by rfl) ⟨1266794, by rfl⟩ : syracuseStep 1689059 = 2533589) B2533589
theorem B4277731 : Blo 1688044 4277731 := bstep (se 1 (by rfl) ⟨3208298, by rfl⟩ : syracuseStep 4277731 = 6416597) B6416597
theorem B2532851 : Blo 1688044 2532851 := bstep (se 1 (by rfl) ⟨1899638, by rfl⟩ : syracuseStep 2532851 = 3799277) B3799277
theorem B1689075 : Blo 1688044 1689075 := bstep (se 1 (by rfl) ⟨1266806, by rfl⟩ : syracuseStep 1689075 = 2533613) B2533613
theorem B1689091 : Blo 1688044 1689091 := bstep (se 1 (by rfl) ⟨1266818, by rfl⟩ : syracuseStep 1689091 = 2533637) B2533637
theorem B2532881 : Blo 1688044 2532881 := bstep (se 2 (by rfl) ⟨949830, by rfl⟩ : syracuseStep 2532881 = 1899661) B1899661
theorem B1689107 : Blo 1688044 1689107 := bstep (se 1 (by rfl) ⟨1266830, by rfl⟩ : syracuseStep 1689107 = 2533661) B2533661
theorem B2532899 : Blo 1688044 2532899 := bstep (se 1 (by rfl) ⟨1899674, by rfl⟩ : syracuseStep 2532899 = 3799349) B3799349
theorem B1689123 : Blo 1688044 1689123 := bstep (se 1 (by rfl) ⟨1266842, by rfl⟩ : syracuseStep 1689123 = 2533685) B2533685
theorem B5137955 : Blo 1688044 5137955 := bstep (se 1 (by rfl) ⟨3853466, by rfl⟩ : syracuseStep 5137955 = 7706933) B7706933
theorem B1689139 : Blo 1688044 1689139 := bstep (se 1 (by rfl) ⟨1266854, by rfl⟩ : syracuseStep 1689139 = 2533709) B2533709
theorem B1803827 : Blo 1688044 1803827 := bstep (se 1 (by rfl) ⟨1352870, by rfl⟩ : syracuseStep 1803827 = 2705741) B2705741
theorem B2532929 : Blo 1688044 2532929 := bstep (se 2 (by rfl) ⟨949848, by rfl⟩ : syracuseStep 2532929 = 1899697) B1899697
theorem B1689155 : Blo 1688044 1689155 := bstep (se 1 (by rfl) ⟨1266866, by rfl⟩ : syracuseStep 1689155 = 2533733) B2533733
theorem B8783437 : Blo 1688044 8783437 := bstep (se 3 (by rfl) ⟨1646894, by rfl⟩ : syracuseStep 8783437 = 3293789) B3293789
theorem B2532947 : Blo 1688044 2532947 := bstep (se 1 (by rfl) ⟨1899710, by rfl⟩ : syracuseStep 2532947 = 3799421) B3799421
theorem B1689171 : Blo 1688044 1689171 := bstep (se 1 (by rfl) ⟨1266878, by rfl⟩ : syracuseStep 1689171 = 2533757) B2533757
theorem B1689187 : Blo 1688044 1689187 := bstep (se 1 (by rfl) ⟨1266890, by rfl⟩ : syracuseStep 1689187 = 2533781) B2533781
theorem B2532977 : Blo 1688044 2532977 := bstep (se 2 (by rfl) ⟨949866, by rfl⟩ : syracuseStep 2532977 = 1899733) B1899733
theorem B4941425 : Blo 1688044 4941425 := bstep (se 2 (by rfl) ⟨1853034, by rfl⟩ : syracuseStep 4941425 = 3706069) B3706069
theorem B1689203 : Blo 1688044 1689203 := bstep (se 1 (by rfl) ⟨1266902, by rfl⟩ : syracuseStep 1689203 = 2533805) B2533805
theorem B4277873 : Blo 1688044 4277873 := bstep (se 2 (by rfl) ⟨1604202, by rfl⟩ : syracuseStep 4277873 = 3208405) B3208405
theorem B2532995 : Blo 1688044 2532995 := bstep (se 1 (by rfl) ⟨1899746, by rfl⟩ : syracuseStep 2532995 = 3799493) B3799493
theorem B1689219 : Blo 1688044 1689219 := bstep (se 1 (by rfl) ⟨1266914, by rfl⟩ : syracuseStep 1689219 = 2533829) B2533829
theorem B1689235 : Blo 1688044 1689235 := bstep (se 1 (by rfl) ⟨1266926, by rfl⟩ : syracuseStep 1689235 = 2533853) B2533853
theorem B2533025 : Blo 1688044 2533025 := bstep (se 2 (by rfl) ⟨949884, by rfl⟩ : syracuseStep 2533025 = 1899769) B1899769
theorem B1689251 : Blo 1688044 1689251 := bstep (se 1 (by rfl) ⟨1266938, by rfl⟩ : syracuseStep 1689251 = 2533877) B2533877
theorem B2533043 : Blo 1688044 2533043 := bstep (se 1 (by rfl) ⟨1899782, by rfl⟩ : syracuseStep 2533043 = 3799565) B3799565
theorem B1689267 : Blo 1688044 1689267 := bstep (se 1 (by rfl) ⟨1266950, by rfl⟩ : syracuseStep 1689267 = 2533901) B2533901
theorem B1689283 : Blo 1688044 1689283 := bstep (se 1 (by rfl) ⟨1266962, by rfl⟩ : syracuseStep 1689283 = 2533925) B2533925
theorem B2533073 : Blo 1688044 2533073 := bstep (se 2 (by rfl) ⟨949902, by rfl⟩ : syracuseStep 2533073 = 1899805) B1899805
theorem B1689299 : Blo 1688044 1689299 := bstep (se 1 (by rfl) ⟨1266974, by rfl⟩ : syracuseStep 1689299 = 2533949) B2533949
theorem B2533091 : Blo 1688044 2533091 := bstep (se 1 (by rfl) ⟨1899818, by rfl⟩ : syracuseStep 2533091 = 3799637) B3799637
theorem B10823395 : Blo 1688044 10823395 := bstep (se 1 (by rfl) ⟨8117546, by rfl⟩ : syracuseStep 10823395 = 16235093) B16235093
theorem B1689315 : Blo 1688044 1689315 := bstep (se 1 (by rfl) ⟨1266986, by rfl⟩ : syracuseStep 1689315 = 2533973) B2533973
theorem B1689331 : Blo 1688044 1689331 := bstep (se 1 (by rfl) ⟨1266998, by rfl⟩ : syracuseStep 1689331 = 2533997) B2533997
theorem B2533121 : Blo 1688044 2533121 := bstep (se 2 (by rfl) ⟨949920, by rfl⟩ : syracuseStep 2533121 = 1899841) B1899841
theorem B1689347 : Blo 1688044 1689347 := bstep (se 1 (by rfl) ⟨1267010, by rfl⟩ : syracuseStep 1689347 = 2534021) B2534021
theorem B2533139 : Blo 1688044 2533139 := bstep (se 1 (by rfl) ⟨1899854, by rfl⟩ : syracuseStep 2533139 = 3799709) B3799709
theorem B1689363 : Blo 1688044 1689363 := bstep (se 1 (by rfl) ⟨1267022, by rfl⟩ : syracuseStep 1689363 = 2534045) B2534045
theorem B6498083 : Blo 1688044 6498083 := bstep (se 1 (by rfl) ⟨4873562, by rfl⟩ : syracuseStep 6498083 = 9747125) B9747125
theorem B1689379 : Blo 1688044 1689379 := bstep (se 1 (by rfl) ⟨1267034, by rfl⟩ : syracuseStep 1689379 = 2534069) B2534069
theorem B2533169 : Blo 1688044 2533169 := bstep (se 2 (by rfl) ⟨949938, by rfl⟩ : syracuseStep 2533169 = 1899877) B1899877
theorem B1689395 : Blo 1688044 1689395 := bstep (se 1 (by rfl) ⟨1267046, by rfl⟩ : syracuseStep 1689395 = 2534093) B2534093
theorem B2533187 : Blo 1688044 2533187 := bstep (se 1 (by rfl) ⟨1899890, by rfl⟩ : syracuseStep 2533187 = 3799781) B3799781
theorem B1689411 : Blo 1688044 1689411 := bstep (se 1 (by rfl) ⟨1267058, by rfl⟩ : syracuseStep 1689411 = 2534117) B2534117
theorem B1689427 : Blo 1688044 1689427 := bstep (se 1 (by rfl) ⟨1267070, by rfl⟩ : syracuseStep 1689427 = 2534141) B2534141
theorem B2533217 : Blo 1688044 2533217 := bstep (se 2 (by rfl) ⟨949956, by rfl⟩ : syracuseStep 2533217 = 1899913) B1899913
theorem B8546147 : Blo 1688044 8546147 := bstep (se 1 (by rfl) ⟨6409610, by rfl⟩ : syracuseStep 8546147 = 12819221) B12819221
theorem B1689443 : Blo 1688044 1689443 := bstep (se 1 (by rfl) ⟨1267082, by rfl⟩ : syracuseStep 1689443 = 2534165) B2534165
theorem B5703533 : Blo 1688044 5703533 := bstep (se 3 (by rfl) ⟨1069412, by rfl⟩ : syracuseStep 5703533 = 2138825) B2138825
theorem B2533235 : Blo 1688044 2533235 := bstep (se 1 (by rfl) ⟨1899926, by rfl⟩ : syracuseStep 2533235 = 3799853) B3799853
theorem B1689459 : Blo 1688044 1689459 := bstep (se 1 (by rfl) ⟨1267094, by rfl⟩ : syracuseStep 1689459 = 2534189) B2534189
theorem B1689475 : Blo 1688044 1689475 := bstep (se 1 (by rfl) ⟨1267106, by rfl⟩ : syracuseStep 1689475 = 2534213) B2534213
theorem B2533265 : Blo 1688044 2533265 := bstep (se 2 (by rfl) ⟨949974, by rfl⟩ : syracuseStep 2533265 = 1899949) B1899949
theorem B1689491 : Blo 1688044 1689491 := bstep (se 1 (by rfl) ⟨1267118, by rfl⟩ : syracuseStep 1689491 = 2534237) B2534237
theorem B2533283 : Blo 1688044 2533283 := bstep (se 1 (by rfl) ⟨1899962, by rfl⟩ : syracuseStep 2533283 = 3799925) B3799925
theorem B1689507 : Blo 1688044 1689507 := bstep (se 1 (by rfl) ⟨1267130, by rfl⟩ : syracuseStep 1689507 = 2534261) B2534261
theorem B5703587 : Blo 1688044 5703587 := bstep (se 1 (by rfl) ⟨4277690, by rfl⟩ : syracuseStep 5703587 = 8555381) B8555381
theorem B1689523 : Blo 1688044 1689523 := bstep (se 1 (by rfl) ⟨1267142, by rfl⟩ : syracuseStep 1689523 = 2534285) B2534285
theorem B2533313 : Blo 1688044 2533313 := bstep (se 2 (by rfl) ⟨949992, by rfl⟩ : syracuseStep 2533313 = 1899985) B1899985
theorem B1689539 : Blo 1688044 1689539 := bstep (se 1 (by rfl) ⟨1267154, by rfl⟩ : syracuseStep 1689539 = 2534309) B2534309
theorem B25987013 : Blo 1688044 25987013 := bstep (se 4 (by rfl) ⟨2436282, by rfl⟩ : syracuseStep 25987013 = 4872565) B4872565
theorem B4114385 : Blo 1688044 4114385 := bstep (se 2 (by rfl) ⟨1542894, by rfl⟩ : syracuseStep 4114385 = 3085789) B3085789
theorem B2533331 : Blo 1688044 2533331 := bstep (se 1 (by rfl) ⟨1899998, by rfl⟩ : syracuseStep 2533331 = 3799997) B3799997
theorem B1689555 : Blo 1688044 1689555 := bstep (se 1 (by rfl) ⟨1267166, by rfl⟩ : syracuseStep 1689555 = 2534333) B2534333
theorem B1689571 : Blo 1688044 1689571 := bstep (se 1 (by rfl) ⟨1267178, by rfl⟩ : syracuseStep 1689571 = 2534357) B2534357
theorem B2533361 : Blo 1688044 2533361 := bstep (se 2 (by rfl) ⟨950010, by rfl⟩ : syracuseStep 2533361 = 1900021) B1900021
theorem B1689587 : Blo 1688044 1689587 := bstep (se 1 (by rfl) ⟨1267190, by rfl⟩ : syracuseStep 1689587 = 2534381) B2534381
theorem B2533379 : Blo 1688044 2533379 := bstep (se 1 (by rfl) ⟨1900034, by rfl⟩ : syracuseStep 2533379 = 3800069) B3800069
theorem B1689603 : Blo 1688044 1689603 := bstep (se 1 (by rfl) ⟨1267202, by rfl⟩ : syracuseStep 1689603 = 2534405) B2534405
theorem B1689619 : Blo 1688044 1689619 := bstep (se 1 (by rfl) ⟨1267214, by rfl⟩ : syracuseStep 1689619 = 2534429) B2534429
theorem B2533409 : Blo 1688044 2533409 := bstep (se 2 (by rfl) ⟨950028, by rfl⟩ : syracuseStep 2533409 = 1900057) B1900057
theorem B6850595 : Blo 1688044 6850595 := bstep (se 1 (by rfl) ⟨5137946, by rfl⟩ : syracuseStep 6850595 = 10275893) B10275893
theorem B1689635 : Blo 1688044 1689635 := bstep (se 1 (by rfl) ⟨1267226, by rfl⟩ : syracuseStep 1689635 = 2534453) B2534453
theorem B2533427 : Blo 1688044 2533427 := bstep (se 1 (by rfl) ⟨1900070, by rfl⟩ : syracuseStep 2533427 = 3800141) B3800141
theorem B1689651 : Blo 1688044 1689651 := bstep (se 1 (by rfl) ⟨1267238, by rfl⟩ : syracuseStep 1689651 = 2534477) B2534477
theorem B1689667 : Blo 1688044 1689667 := bstep (se 1 (by rfl) ⟨1267250, by rfl⟩ : syracuseStep 1689667 = 2534501) B2534501
theorem B2533457 : Blo 1688044 2533457 := bstep (se 2 (by rfl) ⟨950046, by rfl⟩ : syracuseStep 2533457 = 1900093) B1900093
theorem B1689683 : Blo 1688044 1689683 := bstep (se 1 (by rfl) ⟨1267262, by rfl⟩ : syracuseStep 1689683 = 2534525) B2534525
theorem B2533475 : Blo 1688044 2533475 := bstep (se 1 (by rfl) ⟨1900106, by rfl⟩ : syracuseStep 2533475 = 3800213) B3800213
theorem B1689699 : Blo 1688044 1689699 := bstep (se 1 (by rfl) ⟨1267274, by rfl⟩ : syracuseStep 1689699 = 2534549) B2534549
theorem B1689715 : Blo 1688044 1689715 := bstep (se 1 (by rfl) ⟨1267286, by rfl⟩ : syracuseStep 1689715 = 2534573) B2534573
theorem B2533505 : Blo 1688044 2533505 := bstep (se 2 (by rfl) ⟨950064, by rfl⟩ : syracuseStep 2533505 = 1900129) B1900129
theorem B1689731 : Blo 1688044 1689731 := bstep (se 1 (by rfl) ⟨1267298, by rfl⟩ : syracuseStep 1689731 = 2534597) B2534597
theorem B2533523 : Blo 1688044 2533523 := bstep (se 1 (by rfl) ⟨1900142, by rfl⟩ : syracuseStep 2533523 = 3800285) B3800285
theorem B2705555 : Blo 1688044 2705555 := bstep (se 1 (by rfl) ⟨2029166, by rfl⟩ : syracuseStep 2705555 = 4058333) B4058333
theorem B1689747 : Blo 1688044 1689747 := bstep (se 1 (by rfl) ⟨1267310, by rfl⟩ : syracuseStep 1689747 = 2534621) B2534621
theorem B1689763 : Blo 1688044 1689763 := bstep (se 1 (by rfl) ⟨1267322, by rfl⟩ : syracuseStep 1689763 = 2534645) B2534645
theorem B2533553 : Blo 1688044 2533553 := bstep (se 2 (by rfl) ⟨950082, by rfl⟩ : syracuseStep 2533553 = 1900165) B1900165
theorem B5703857 : Blo 1688044 5703857 := bstep (se 2 (by rfl) ⟨2138946, by rfl⟩ : syracuseStep 5703857 = 4277893) B4277893
theorem B1689779 : Blo 1688044 1689779 := bstep (se 1 (by rfl) ⟨1267334, by rfl⟩ : syracuseStep 1689779 = 2534669) B2534669
theorem B2533571 : Blo 1688044 2533571 := bstep (se 1 (by rfl) ⟨1900178, by rfl⟩ : syracuseStep 2533571 = 3800357) B3800357
theorem B1689795 : Blo 1688044 1689795 := bstep (se 1 (by rfl) ⟨1267346, by rfl⟩ : syracuseStep 1689795 = 2534693) B2534693
theorem B1689811 : Blo 1688044 1689811 := bstep (se 1 (by rfl) ⟨1267358, by rfl⟩ : syracuseStep 1689811 = 2534717) B2534717
theorem B2533601 : Blo 1688044 2533601 := bstep (se 2 (by rfl) ⟨950100, by rfl⟩ : syracuseStep 2533601 = 1900201) B1900201
theorem B1689827 : Blo 1688044 1689827 := bstep (se 1 (by rfl) ⟨1267370, by rfl⟩ : syracuseStep 1689827 = 2534741) B2534741
theorem B2533619 : Blo 1688044 2533619 := bstep (se 1 (by rfl) ⟨1900214, by rfl⟩ : syracuseStep 2533619 = 3800429) B3800429
theorem B1689843 : Blo 1688044 1689843 := bstep (se 1 (by rfl) ⟨1267382, by rfl⟩ : syracuseStep 1689843 = 2534765) B2534765
theorem B1689859 : Blo 1688044 1689859 := bstep (se 1 (by rfl) ⟨1267394, by rfl⟩ : syracuseStep 1689859 = 2534789) B2534789
theorem B2533649 : Blo 1688044 2533649 := bstep (se 2 (by rfl) ⟨950118, by rfl⟩ : syracuseStep 2533649 = 1900237) B1900237
theorem B1689875 : Blo 1688044 1689875 := bstep (se 1 (by rfl) ⟨1267406, by rfl⟩ : syracuseStep 1689875 = 2534813) B2534813
theorem B2533667 : Blo 1688044 2533667 := bstep (se 1 (by rfl) ⟨1900250, by rfl⟩ : syracuseStep 2533667 = 3800501) B3800501
theorem B1689891 : Blo 1688044 1689891 := bstep (se 1 (by rfl) ⟨1267418, by rfl⟩ : syracuseStep 1689891 = 2534837) B2534837
theorem B1689907 : Blo 1688044 1689907 := bstep (se 1 (by rfl) ⟨1267430, by rfl⟩ : syracuseStep 1689907 = 2534861) B2534861
theorem B2533697 : Blo 1688044 2533697 := bstep (se 2 (by rfl) ⟨950136, by rfl⟩ : syracuseStep 2533697 = 1900273) B1900273
theorem B1689923 : Blo 1688044 1689923 := bstep (se 1 (by rfl) ⟨1267442, by rfl⟩ : syracuseStep 1689923 = 2534885) B2534885
theorem B9128261 : Blo 1688044 9128261 := bstep (se 4 (by rfl) ⟨855774, by rfl⟩ : syracuseStep 9128261 = 1711549) B1711549
theorem B2533715 : Blo 1688044 2533715 := bstep (se 1 (by rfl) ⟨1900286, by rfl⟩ : syracuseStep 2533715 = 3800573) B3800573
theorem B1689939 : Blo 1688044 1689939 := bstep (se 1 (by rfl) ⟨1267454, by rfl⟩ : syracuseStep 1689939 = 2534909) B2534909
theorem B1689955 : Blo 1688044 1689955 := bstep (se 1 (by rfl) ⟨1267466, by rfl⟩ : syracuseStep 1689955 = 2534933) B2534933
theorem B3205489 : Blo 1688044 3205489 := bstep (se 2 (by rfl) ⟨1202058, by rfl⟩ : syracuseStep 3205489 = 2404117) B2404117
theorem B14428529 : Blo 1688044 14428529 := bstep (se 2 (by rfl) ⟨5410698, by rfl⟩ : syracuseStep 14428529 = 10821397) B10821397
theorem B2533745 : Blo 1688044 2533745 := bstep (se 2 (by rfl) ⟨950154, by rfl⟩ : syracuseStep 2533745 = 1900309) B1900309
theorem B1689971 : Blo 1688044 1689971 := bstep (se 1 (by rfl) ⟨1267478, by rfl⟩ : syracuseStep 1689971 = 2534957) B2534957
theorem B2533763 : Blo 1688044 2533763 := bstep (se 1 (by rfl) ⟨1900322, by rfl⟩ : syracuseStep 2533763 = 3800645) B3800645
theorem B1689987 : Blo 1688044 1689987 := bstep (se 1 (by rfl) ⟨1267490, by rfl⟩ : syracuseStep 1689987 = 2534981) B2534981
theorem B1690003 : Blo 1688044 1690003 := bstep (se 1 (by rfl) ⟨1267502, by rfl⟩ : syracuseStep 1690003 = 2535005) B2535005
theorem B2533793 : Blo 1688044 2533793 := bstep (se 2 (by rfl) ⟨950172, by rfl⟩ : syracuseStep 2533793 = 1900345) B1900345
theorem B1690019 : Blo 1688044 1690019 := bstep (se 1 (by rfl) ⟨1267514, by rfl⟩ : syracuseStep 1690019 = 2535029) B2535029
theorem B2533811 : Blo 1688044 2533811 := bstep (se 1 (by rfl) ⟨1900358, by rfl⟩ : syracuseStep 2533811 = 3800717) B3800717
theorem B2705843 : Blo 1688044 2705843 := bstep (se 1 (by rfl) ⟨2029382, by rfl⟩ : syracuseStep 2705843 = 4058765) B4058765
theorem B1690035 : Blo 1688044 1690035 := bstep (se 1 (by rfl) ⟨1267526, by rfl⟩ : syracuseStep 1690035 = 2535053) B2535053
theorem B8669645 : Blo 1688044 8669645 := bstep (se 3 (by rfl) ⟨1625558, by rfl⟩ : syracuseStep 8669645 = 3251117) B3251117
theorem B2533841 : Blo 1688044 2533841 := bstep (se 2 (by rfl) ⟨950190, by rfl⟩ : syracuseStep 2533841 = 1900381) B1900381
theorem B2533859 : Blo 1688044 2533859 := bstep (se 1 (by rfl) ⟨1900394, by rfl⟩ : syracuseStep 2533859 = 3800789) B3800789
theorem B2533889 : Blo 1688044 2533889 := bstep (se 2 (by rfl) ⟨950208, by rfl⟩ : syracuseStep 2533889 = 1900417) B1900417
theorem B3205649 : Blo 1688044 3205649 := bstep (se 2 (by rfl) ⟨1202118, by rfl⟩ : syracuseStep 3205649 = 2404237) B2404237
theorem B2533907 : Blo 1688044 2533907 := bstep (se 1 (by rfl) ⟨1900430, by rfl⟩ : syracuseStep 2533907 = 3800861) B3800861
theorem B4811309 : Blo 1688044 4811309 := bstep (se 3 (by rfl) ⟨902120, by rfl⟩ : syracuseStep 4811309 = 1804241) B1804241
theorem B2533937 : Blo 1688044 2533937 := bstep (se 2 (by rfl) ⟨950226, by rfl⟩ : syracuseStep 2533937 = 1900453) B1900453
theorem B8555057 : Blo 1688044 8555057 := bstep (se 2 (by rfl) ⟨3208146, by rfl⟩ : syracuseStep 8555057 = 6416293) B6416293
theorem B2533955 : Blo 1688044 2533955 := bstep (se 1 (by rfl) ⟨1900466, by rfl⟩ : syracuseStep 2533955 = 3800933) B3800933
theorem B12823109 : Blo 1688044 12823109 := bstep (se 4 (by rfl) ⟨1202166, by rfl⟩ : syracuseStep 12823109 = 2404333) B2404333
theorem B9620045 : Blo 1688044 9620045 := bstep (se 3 (by rfl) ⟨1803758, by rfl⟩ : syracuseStep 9620045 = 3607517) B3607517
theorem B2533985 : Blo 1688044 2533985 := bstep (se 2 (by rfl) ⟨950244, by rfl⟩ : syracuseStep 2533985 = 1900489) B1900489
theorem B2534003 : Blo 1688044 2534003 := bstep (se 1 (by rfl) ⟨1900502, by rfl⟩ : syracuseStep 2534003 = 3801005) B3801005
theorem B8546957 : Blo 1688044 8546957 := bstep (se 3 (by rfl) ⟨1602554, by rfl⟩ : syracuseStep 8546957 = 3205109) B3205109
theorem B2534033 : Blo 1688044 2534033 := bstep (se 2 (by rfl) ⟨950262, by rfl⟩ : syracuseStep 2534033 = 1900525) B1900525
theorem B5409443 : Blo 1688044 5409443 := bstep (se 1 (by rfl) ⟨4057082, by rfl⟩ : syracuseStep 5409443 = 8114165) B8114165
theorem B2534051 : Blo 1688044 2534051 := bstep (se 1 (by rfl) ⟨1900538, by rfl⟩ : syracuseStep 2534051 = 3801077) B3801077
theorem B2534081 : Blo 1688044 2534081 := bstep (se 2 (by rfl) ⟨950280, by rfl⟩ : syracuseStep 2534081 = 1900561) B1900561
theorem B2534099 : Blo 1688044 2534099 := bstep (se 1 (by rfl) ⟨1900574, by rfl⟩ : syracuseStep 2534099 = 3801149) B3801149
theorem B4811491 : Blo 1688044 4811491 := bstep (se 1 (by rfl) ⟨3608618, by rfl⟩ : syracuseStep 4811491 = 7217237) B7217237
theorem B2534129 : Blo 1688044 2534129 := bstep (se 2 (by rfl) ⟨950298, by rfl⟩ : syracuseStep 2534129 = 1900597) B1900597
theorem B2534147 : Blo 1688044 2534147 := bstep (se 1 (by rfl) ⟨1900610, by rfl⟩ : syracuseStep 2534147 = 3801221) B3801221
theorem B4811537 : Blo 1688044 4811537 := bstep (se 2 (by rfl) ⟨1804326, by rfl⟩ : syracuseStep 4811537 = 3608653) B3608653
theorem B2534177 : Blo 1688044 2534177 := bstep (se 2 (by rfl) ⟨950316, by rfl⟩ : syracuseStep 2534177 = 1900633) B1900633
theorem B2534195 : Blo 1688044 2534195 := bstep (se 1 (by rfl) ⟨1900646, by rfl⟩ : syracuseStep 2534195 = 3801293) B3801293
theorem B8112973 : Blo 1688044 8112973 := bstep (se 3 (by rfl) ⟨1521182, by rfl⟩ : syracuseStep 8112973 = 3042365) B3042365
theorem B2534225 : Blo 1688044 2534225 := bstep (se 2 (by rfl) ⟨950334, by rfl⟩ : syracuseStep 2534225 = 1900669) B1900669
theorem B4115281 : Blo 1688044 4115281 := bstep (se 2 (by rfl) ⟨1543230, by rfl⟩ : syracuseStep 4115281 = 3086461) B3086461
theorem B2706259 : Blo 1688044 2706259 := bstep (se 1 (by rfl) ⟨2029694, by rfl⟩ : syracuseStep 2706259 = 4059389) B4059389
theorem B2534243 : Blo 1688044 2534243 := bstep (se 1 (by rfl) ⟨1900682, by rfl⟩ : syracuseStep 2534243 = 3801365) B3801365
theorem B2534273 : Blo 1688044 2534273 := bstep (se 2 (by rfl) ⟨950352, by rfl⟩ : syracuseStep 2534273 = 1900705) B1900705
theorem B2534291 : Blo 1688044 2534291 := bstep (se 1 (by rfl) ⟨1900718, by rfl⟩ : syracuseStep 2534291 = 3801437) B3801437
theorem B3206051 : Blo 1688044 3206051 := bstep (se 1 (by rfl) ⟨2404538, by rfl⟩ : syracuseStep 3206051 = 4809077) B4809077
theorem B2534321 : Blo 1688044 2534321 := bstep (se 2 (by rfl) ⟨950370, by rfl⟩ : syracuseStep 2534321 = 1900741) B1900741
theorem B2534339 : Blo 1688044 2534339 := bstep (se 1 (by rfl) ⟨1900754, by rfl⟩ : syracuseStep 2534339 = 3801509) B3801509
theorem B2534369 : Blo 1688044 2534369 := bstep (se 2 (by rfl) ⟨950388, by rfl⟩ : syracuseStep 2534369 = 1900777) B1900777
theorem B3656675 : Blo 1688044 3656675 := bstep (se 1 (by rfl) ⟨2742506, by rfl⟩ : syracuseStep 3656675 = 5485013) B5485013
theorem B2534387 : Blo 1688044 2534387 := bstep (se 1 (by rfl) ⟨1900790, by rfl⟩ : syracuseStep 2534387 = 3801581) B3801581
theorem B2534417 : Blo 1688044 2534417 := bstep (se 2 (by rfl) ⟨950406, by rfl⟩ : syracuseStep 2534417 = 1900813) B1900813
theorem B2534435 : Blo 1688044 2534435 := bstep (se 1 (by rfl) ⟨1900826, by rfl⟩ : syracuseStep 2534435 = 3801653) B3801653
theorem B4877347 : Blo 1688044 4877347 := bstep (se 1 (by rfl) ⟨3658010, by rfl⟩ : syracuseStep 4877347 = 7316021) B7316021
theorem B5409841 : Blo 1688044 5409841 := bstep (se 2 (by rfl) ⟨2028690, by rfl⟩ : syracuseStep 5409841 = 4057381) B4057381
theorem B2534465 : Blo 1688044 2534465 := bstep (se 2 (by rfl) ⟨950424, by rfl⟩ : syracuseStep 2534465 = 1900849) B1900849
theorem B2534483 : Blo 1688044 2534483 := bstep (se 1 (by rfl) ⟨1900862, by rfl⟩ : syracuseStep 2534483 = 3801725) B3801725
theorem B2706529 : Blo 1688044 2706529 := bstep (se 2 (by rfl) ⟨1014948, by rfl⟩ : syracuseStep 2706529 = 2029897) B2029897
theorem B2534513 : Blo 1688044 2534513 := bstep (se 2 (by rfl) ⟨950442, by rfl⟩ : syracuseStep 2534513 = 1900885) B1900885
theorem B12831857 : Blo 1688044 12831857 := bstep (se 2 (by rfl) ⟨4811946, by rfl⟩ : syracuseStep 12831857 = 9623893) B9623893
theorem B2534531 : Blo 1688044 2534531 := bstep (se 1 (by rfl) ⟨1900898, by rfl⟩ : syracuseStep 2534531 = 3801797) B3801797
theorem B2534561 : Blo 1688044 2534561 := bstep (se 2 (by rfl) ⟨950460, by rfl⟩ : syracuseStep 2534561 = 1900921) B1900921
theorem B4058275 : Blo 1688044 4058275 := bstep (se 1 (by rfl) ⟨3043706, by rfl⟩ : syracuseStep 4058275 = 6087413) B6087413
theorem B2534579 : Blo 1688044 2534579 := bstep (se 1 (by rfl) ⟨1900934, by rfl⟩ : syracuseStep 2534579 = 3801869) B3801869
theorem B2534609 : Blo 1688044 2534609 := bstep (se 2 (by rfl) ⟨950478, by rfl⟩ : syracuseStep 2534609 = 1900957) B1900957
theorem B2534627 : Blo 1688044 2534627 := bstep (se 1 (by rfl) ⟨1900970, by rfl⟩ : syracuseStep 2534627 = 3801941) B3801941
theorem B2534657 : Blo 1688044 2534657 := bstep (se 2 (by rfl) ⟨950496, by rfl⟩ : syracuseStep 2534657 = 1900993) B1900993
theorem B2534675 : Blo 1688044 2534675 := bstep (se 1 (by rfl) ⟨1901006, by rfl⟩ : syracuseStep 2534675 = 3802013) B3802013
theorem B2534705 : Blo 1688044 2534705 := bstep (se 2 (by rfl) ⟨950514, by rfl⟩ : syracuseStep 2534705 = 1901029) B1901029
theorem B2534723 : Blo 1688044 2534723 := bstep (se 1 (by rfl) ⟨1901042, by rfl⟩ : syracuseStep 2534723 = 3802085) B3802085
theorem B2706785 : Blo 1688044 2706785 := bstep (se 2 (by rfl) ⟨1015044, by rfl⟩ : syracuseStep 2706785 = 2030089) B2030089
theorem B2534753 : Blo 1688044 2534753 := bstep (se 2 (by rfl) ⟨950532, by rfl⟩ : syracuseStep 2534753 = 1901065) B1901065
theorem B2534771 : Blo 1688044 2534771 := bstep (se 1 (by rfl) ⟨1901078, by rfl⟩ : syracuseStep 2534771 = 3802157) B3802157
theorem B2534801 : Blo 1688044 2534801 := bstep (se 2 (by rfl) ⟨950550, by rfl⟩ : syracuseStep 2534801 = 1901101) B1901101
theorem B2534819 : Blo 1688044 2534819 := bstep (se 1 (by rfl) ⟨1901114, by rfl⟩ : syracuseStep 2534819 = 3802229) B3802229
theorem B2534849 : Blo 1688044 2534849 := bstep (se 2 (by rfl) ⟨950568, by rfl⟩ : syracuseStep 2534849 = 1901137) B1901137
theorem B2534867 : Blo 1688044 2534867 := bstep (se 1 (by rfl) ⟨1901150, by rfl⟩ : syracuseStep 2534867 = 3802301) B3802301
theorem B5410289 : Blo 1688044 5410289 := bstep (se 2 (by rfl) ⟨2028858, by rfl⟩ : syracuseStep 5410289 = 4057717) B4057717
theorem B9620977 : Blo 1688044 9620977 := bstep (se 2 (by rfl) ⟨3607866, by rfl⟩ : syracuseStep 9620977 = 7215733) B7215733
theorem B2534897 : Blo 1688044 2534897 := bstep (se 2 (by rfl) ⟨950586, by rfl⟩ : syracuseStep 2534897 = 1901173) B1901173
theorem B2534915 : Blo 1688044 2534915 := bstep (se 1 (by rfl) ⟨1901186, by rfl⟩ : syracuseStep 2534915 = 3802373) B3802373
theorem B2534945 : Blo 1688044 2534945 := bstep (se 2 (by rfl) ⟨950604, by rfl⟩ : syracuseStep 2534945 = 1901209) B1901209
theorem B6409763 : Blo 1688044 6409763 := bstep (se 1 (by rfl) ⟨4807322, by rfl⟩ : syracuseStep 6409763 = 9614645) B9614645
theorem B4566577 : Blo 1688044 4566577 := bstep (se 2 (by rfl) ⟨1712466, by rfl⟩ : syracuseStep 4566577 = 3424933) B3424933
theorem B2534963 : Blo 1688044 2534963 := bstep (se 1 (by rfl) ⟨1901222, by rfl⟩ : syracuseStep 2534963 = 3802445) B3802445
theorem B357305909 : Blo 1688044 357305909 := bstep (se 5 (by rfl) ⟨16748714, by rfl⟩ : syracuseStep 357305909 = 33497429) B33497429
theorem B2534993 : Blo 1688044 2534993 := bstep (se 2 (by rfl) ⟨950622, by rfl⟩ : syracuseStep 2534993 = 1901245) B1901245
theorem B2403923 : Blo 1688044 2403923 := bstep (se 1 (by rfl) ⟨1802942, by rfl⟩ : syracuseStep 2403923 = 3605885) B3605885
theorem B2535011 : Blo 1688044 2535011 := bstep (se 1 (by rfl) ⟨1901258, by rfl⟩ : syracuseStep 2535011 = 3802517) B3802517
theorem B2535041 : Blo 1688044 2535041 := bstep (se 2 (by rfl) ⟨950640, by rfl⟩ : syracuseStep 2535041 = 1901281) B1901281
theorem B2535059 : Blo 1688044 2535059 := bstep (se 1 (by rfl) ⟨1901294, by rfl⟩ : syracuseStep 2535059 = 3802589) B3802589
theorem B3043057 : Blo 1688044 3043057 := bstep (se 2 (by rfl) ⟨1141146, by rfl⟩ : syracuseStep 3043057 = 2282293) B2282293
theorem B3206947 : Blo 1688044 3206947 := bstep (se 1 (by rfl) ⟨2405210, by rfl⟩ : syracuseStep 3206947 = 4810421) B4810421
theorem B4058947 : Blo 1688044 4058947 := bstep (se 1 (by rfl) ⟨3044210, by rfl⟩ : syracuseStep 4058947 = 6088421) B6088421
theorem B3207107 : Blo 1688044 3207107 := bstep (se 1 (by rfl) ⟨2405330, by rfl⟩ : syracuseStep 3207107 = 4810661) B4810661
theorem B5697485 : Blo 1688044 5697485 := bstep (se 3 (by rfl) ⟨1068278, by rfl⟩ : syracuseStep 5697485 = 2136557) B2136557
theorem B2166755 : Blo 1688044 2166755 := bstep (se 1 (by rfl) ⟨1625066, by rfl⟩ : syracuseStep 2166755 = 3250133) B3250133
theorem B5697539 : Blo 1688044 5697539 := bstep (se 1 (by rfl) ⟨4273154, by rfl⟩ : syracuseStep 5697539 = 8546309) B8546309
theorem B8663075 : Blo 1688044 8663075 := bstep (se 1 (by rfl) ⟨6497306, by rfl⟩ : syracuseStep 8663075 = 12994613) B12994613
theorem B6500387 : Blo 1688044 6500387 := bstep (se 1 (by rfl) ⟨4875290, by rfl⟩ : syracuseStep 6500387 = 9750581) B9750581
theorem B18264133 : Blo 1688044 18264133 := bstep (se 4 (by rfl) ⟨1712262, by rfl⟩ : syracuseStep 18264133 = 3424525) B3424525
theorem B6090929 : Blo 1688044 6090929 := bstep (se 2 (by rfl) ⟨2284098, by rfl⟩ : syracuseStep 6090929 = 4568197) B4568197
theorem B2404561 : Blo 1688044 2404561 := bstep (se 2 (by rfl) ⟨901710, by rfl⟩ : syracuseStep 2404561 = 1803421) B1803421
theorem B5697809 : Blo 1688044 5697809 := bstep (se 2 (by rfl) ⟨2136678, by rfl⟩ : syracuseStep 5697809 = 4273357) B4273357
theorem B4059409 : Blo 1688044 4059409 := bstep (se 2 (by rfl) ⟨1522278, by rfl⟩ : syracuseStep 4059409 = 3044557) B3044557
theorem B24351029 : Blo 1688044 24351029 := bstep (se 5 (by rfl) ⟨1141454, by rfl⟩ : syracuseStep 24351029 = 2282909) B2282909
theorem B2404675 : Blo 1688044 2404675 := bstep (se 1 (by rfl) ⟨1803506, by rfl⟩ : syracuseStep 2404675 = 3607013) B3607013
theorem B3608995 : Blo 1688044 3608995 := bstep (se 1 (by rfl) ⟨2706746, by rfl⟩ : syracuseStep 3608995 = 5413493) B5413493
theorem B2888131 : Blo 1688044 2888131 := bstep (se 1 (by rfl) ⟨2166098, by rfl⟩ : syracuseStep 2888131 = 4332197) B4332197
theorem B6410765 : Blo 1688044 6410765 := bstep (se 3 (by rfl) ⟨1202018, by rfl⟩ : syracuseStep 6410765 = 2404037) B2404037
theorem B2282131 : Blo 1688044 2282131 := bstep (se 1 (by rfl) ⟨1711598, by rfl⟩ : syracuseStep 2282131 = 3423197) B3423197
theorem B5698349 : Blo 1688044 5698349 := bstep (se 3 (by rfl) ⟨1068440, by rfl⟩ : syracuseStep 5698349 = 2136881) B2136881
theorem B5698403 : Blo 1688044 5698403 := bstep (se 1 (by rfl) ⟨4273802, by rfl⟩ : syracuseStep 5698403 = 8547605) B8547605
theorem B9614213 : Blo 1688044 9614213 := bstep (se 4 (by rfl) ⟨901332, by rfl⟩ : syracuseStep 9614213 = 1802665) B1802665
theorem B9622435 : Blo 1688044 9622435 := bstep (se 1 (by rfl) ⟨7216826, by rfl⟩ : syracuseStep 9622435 = 14433653) B14433653
theorem B10294193 : Blo 1688044 10294193 := bstep (se 2 (by rfl) ⟨3860322, by rfl⟩ : syracuseStep 10294193 = 7720645) B7720645
theorem B3208177 : Blo 1688044 3208177 := bstep (se 2 (by rfl) ⟨1203066, by rfl⟩ : syracuseStep 3208177 = 2406133) B2406133
theorem B7214093 : Blo 1688044 7214093 := bstep (se 3 (by rfl) ⟨1352642, by rfl⟩ : syracuseStep 7214093 = 2705285) B2705285
theorem B7214129 : Blo 1688044 7214129 := bstep (se 2 (by rfl) ⟨2705298, by rfl⟩ : syracuseStep 7214129 = 5410597) B5410597
theorem B5698673 : Blo 1688044 5698673 := bstep (se 2 (by rfl) ⟨2137002, by rfl⟩ : syracuseStep 5698673 = 4274005) B4274005
theorem B3798161 : Blo 1688044 3798161 := bstep (se 2 (by rfl) ⟨1424310, by rfl⟩ : syracuseStep 3798161 = 2848621) B2848621
theorem B3798179 : Blo 1688044 3798179 := bstep (se 1 (by rfl) ⟨2848634, by rfl⟩ : syracuseStep 3798179 = 5697269) B5697269
theorem B2741411 : Blo 1688044 2741411 := bstep (se 1 (by rfl) ⟨2056058, by rfl⟩ : syracuseStep 2741411 = 4112117) B4112117
theorem B2282801 : Blo 1688044 2282801 := bstep (se 2 (by rfl) ⟨856050, by rfl⟩ : syracuseStep 2282801 = 1712101) B1712101
theorem B2028883 : Blo 1688044 2028883 := bstep (se 1 (by rfl) ⟨1521662, by rfl⟩ : syracuseStep 2028883 = 3043325) B3043325
theorem B3798449 : Blo 1688044 3798449 := bstep (se 2 (by rfl) ⟨1424418, by rfl⟩ : syracuseStep 3798449 = 2848837) B2848837
theorem B9622961 : Blo 1688044 9622961 := bstep (se 2 (by rfl) ⟨3608610, by rfl⟩ : syracuseStep 9622961 = 7217221) B7217221
theorem B3798467 : Blo 1688044 3798467 := bstep (se 1 (by rfl) ⟨2848850, by rfl⟩ : syracuseStep 3798467 = 5697701) B5697701
theorem B5133773 : Blo 1688044 5133773 := bstep (se 3 (by rfl) ⟨962582, by rfl⟩ : syracuseStep 5133773 = 1925165) B1925165
theorem B2602451 : Blo 1688044 2602451 := bstep (se 1 (by rfl) ⟨1951838, by rfl⟩ : syracuseStep 2602451 = 3903677) B3903677
theorem B6084067 : Blo 1688044 6084067 := bstep (se 1 (by rfl) ⟨4563050, by rfl⟩ : syracuseStep 6084067 = 9126101) B9126101
theorem B8549873 : Blo 1688044 8549873 := bstep (se 2 (by rfl) ⟨3206202, by rfl⟩ : syracuseStep 8549873 = 6412405) B6412405
theorem B10827269 : Blo 1688044 10827269 := bstep (se 4 (by rfl) ⟨1015056, by rfl⟩ : syracuseStep 10827269 = 2030113) B2030113
theorem B5412365 : Blo 1688044 5412365 := bstep (se 3 (by rfl) ⟨1014818, by rfl⟩ : syracuseStep 5412365 = 2029637) B2029637
theorem B4273681 : Blo 1688044 4273681 := bstep (se 2 (by rfl) ⟨1602630, by rfl⟩ : syracuseStep 4273681 = 3205261) B3205261
theorem B3044881 : Blo 1688044 3044881 := bstep (se 2 (by rfl) ⟨1141830, by rfl⟩ : syracuseStep 3044881 = 2283661) B2283661
theorem B5133869 : Blo 1688044 5133869 := bstep (se 3 (by rfl) ⟨962600, by rfl⟩ : syracuseStep 5133869 = 1925201) B1925201
theorem B5486147 : Blo 1688044 5486147 := bstep (se 1 (by rfl) ⟨4114610, by rfl⟩ : syracuseStep 5486147 = 8229221) B8229221
theorem B3044945 : Blo 1688044 3044945 := bstep (se 2 (by rfl) ⟨1141854, by rfl⟩ : syracuseStep 3044945 = 2283709) B2283709
theorem B18257521 : Blo 1688044 18257521 := bstep (se 2 (by rfl) ⟨6846570, by rfl⟩ : syracuseStep 18257521 = 13693141) B13693141
theorem B11712113 : Blo 1688044 11712113 := bstep (se 2 (by rfl) ⟨4392042, by rfl⟩ : syracuseStep 11712113 = 8784085) B8784085
theorem B2406019 : Blo 1688044 2406019 := bstep (se 1 (by rfl) ⟨1804514, by rfl⟩ : syracuseStep 2406019 = 3609029) B3609029
theorem B5699213 : Blo 1688044 5699213 := bstep (se 3 (by rfl) ⟨1068602, by rfl⟩ : syracuseStep 5699213 = 2137205) B2137205
theorem B2283169 : Blo 1688044 2283169 := bstep (se 2 (by rfl) ⟨856188, by rfl⟩ : syracuseStep 2283169 = 1712377) B1712377
theorem B5699267 : Blo 1688044 5699267 := bstep (se 1 (by rfl) ⟨4274450, by rfl⟩ : syracuseStep 5699267 = 8548901) B8548901
theorem B3798737 : Blo 1688044 3798737 := bstep (se 2 (by rfl) ⟨1424526, by rfl⟩ : syracuseStep 3798737 = 2849053) B2849053
theorem B3798755 : Blo 1688044 3798755 := bstep (se 1 (by rfl) ⟨2849066, by rfl⟩ : syracuseStep 3798755 = 5698133) B5698133
theorem B15406861 : Blo 1688044 15406861 := bstep (se 3 (by rfl) ⟨2888786, by rfl⟩ : syracuseStep 15406861 = 5777573) B5777573
theorem B4273955 : Blo 1688044 4273955 := bstep (se 1 (by rfl) ⟨3205466, by rfl⟩ : syracuseStep 4273955 = 6410933) B6410933
theorem B2742065 : Blo 1688044 2742065 := bstep (se 2 (by rfl) ⟨1028274, by rfl⟩ : syracuseStep 2742065 = 2056549) B2056549
theorem B2848675 : Blo 1688044 2848675 := bstep (se 1 (by rfl) ⟨2136506, by rfl⟩ : syracuseStep 2848675 = 4273013) B4273013
theorem B5699537 : Blo 1688044 5699537 := bstep (se 2 (by rfl) ⟨2137326, by rfl⟩ : syracuseStep 5699537 = 4274653) B4274653
theorem B4274147 : Blo 1688044 4274147 := bstep (se 1 (by rfl) ⟨3205610, by rfl⟩ : syracuseStep 4274147 = 6411221) B6411221
theorem B3799025 : Blo 1688044 3799025 := bstep (se 2 (by rfl) ⟨1424634, by rfl⟩ : syracuseStep 3799025 = 2849269) B2849269
theorem B3799043 : Blo 1688044 3799043 := bstep (se 1 (by rfl) ⟨2849282, by rfl⟩ : syracuseStep 3799043 = 5698565) B5698565
theorem B2848817 : Blo 1688044 2848817 := bstep (se 2 (by rfl) ⟨1068306, by rfl⟩ : syracuseStep 2848817 = 2136613) B2136613
theorem B18520163 : Blo 1688044 18520163 := bstep (se 1 (by rfl) ⟨13890122, by rfl⟩ : syracuseStep 18520163 = 27780245) B27780245
theorem B32897137 : Blo 1688044 32897137 := bstep (se 2 (by rfl) ⟨12336426, by rfl⟩ : syracuseStep 32897137 = 24672853) B24672853
theorem B2848945 : Blo 1688044 2848945 := bstep (se 2 (by rfl) ⟨1068354, by rfl⟩ : syracuseStep 2848945 = 2136709) B2136709
theorem B3471569 : Blo 1688044 3471569 := bstep (se 2 (by rfl) ⟨1301838, by rfl⟩ : syracuseStep 3471569 = 2603677) B2603677
theorem B2848979 : Blo 1688044 2848979 := bstep (se 1 (by rfl) ⟨2136734, by rfl⟩ : syracuseStep 2848979 = 4273469) B4273469
theorem B3799313 : Blo 1688044 3799313 := bstep (se 2 (by rfl) ⟨1424742, by rfl⟩ : syracuseStep 3799313 = 2849485) B2849485
theorem B3799331 : Blo 1688044 3799331 := bstep (se 1 (by rfl) ⟨2849498, by rfl⟩ : syracuseStep 3799331 = 5698997) B5698997
theorem B10819909 : Blo 1688044 10819909 := bstep (se 4 (by rfl) ⟨1014366, by rfl⟩ : syracuseStep 10819909 = 2028733) B2028733
theorem B2849107 : Blo 1688044 2849107 := bstep (se 1 (by rfl) ⟨2136830, by rfl⟩ : syracuseStep 2849107 = 4273661) B4273661
theorem B2136451 : Blo 1688044 2136451 := bstep (se 1 (by rfl) ⟨1602338, by rfl⟩ : syracuseStep 2136451 = 3204677) B3204677
theorem B4872611 : Blo 1688044 4872611 := bstep (se 1 (by rfl) ⟨3654458, by rfl⟩ : syracuseStep 4872611 = 7308917) B7308917
theorem B4331939 : Blo 1688044 4331939 := bstep (se 1 (by rfl) ⟨3248954, by rfl⟩ : syracuseStep 4331939 = 6497909) B6497909
theorem B4807117 : Blo 1688044 4807117 := bstep (se 3 (by rfl) ⟨901334, by rfl⟩ : syracuseStep 4807117 = 1802669) B1802669
theorem B2849249 : Blo 1688044 2849249 := bstep (se 2 (by rfl) ⟨1068468, by rfl⟩ : syracuseStep 2849249 = 2136937) B2136937
theorem B2136547 : Blo 1688044 2136547 := bstep (se 1 (by rfl) ⟨1602410, by rfl⟩ : syracuseStep 2136547 = 3204821) B3204821
theorem B5700077 : Blo 1688044 5700077 := bstep (se 3 (by rfl) ⟨1068764, by rfl⟩ : syracuseStep 5700077 = 2137529) B2137529
theorem B5700131 : Blo 1688044 5700131 := bstep (se 1 (by rfl) ⟨4275098, by rfl⟩ : syracuseStep 5700131 = 8550197) B8550197
theorem B3799601 : Blo 1688044 3799601 := bstep (se 2 (by rfl) ⟨1424850, by rfl⟩ : syracuseStep 3799601 = 2849701) B2849701
theorem B3799619 : Blo 1688044 3799619 := bstep (se 1 (by rfl) ⟨2849714, by rfl⟩ : syracuseStep 3799619 = 5699429) B5699429
theorem B6412877 : Blo 1688044 6412877 := bstep (se 3 (by rfl) ⟨1202414, by rfl⟩ : syracuseStep 6412877 = 2404829) B2404829
theorem B2849377 : Blo 1688044 2849377 := bstep (se 2 (by rfl) ⟨1068516, by rfl⟩ : syracuseStep 2849377 = 2137033) B2137033
theorem B1899139 : Blo 1688044 1899139 := bstep (se 1 (by rfl) ⟨1424354, by rfl⟩ : syracuseStep 1899139 = 2848709) B2848709
theorem B2849411 : Blo 1688044 2849411 := bstep (se 1 (by rfl) ⟨2137058, by rfl⟩ : syracuseStep 2849411 = 4274117) B4274117
theorem B6257315 : Blo 1688044 6257315 := bstep (se 1 (by rfl) ⟨4692986, by rfl⟩ : syracuseStep 6257315 = 9385973) B9385973
theorem B4807345 : Blo 1688044 4807345 := bstep (se 2 (by rfl) ⟨1802754, by rfl⟩ : syracuseStep 4807345 = 3605509) B3605509
theorem B2849539 : Blo 1688044 2849539 := bstep (se 1 (by rfl) ⟨2137154, by rfl⟩ : syracuseStep 2849539 = 4274309) B4274309
theorem B5413645 : Blo 1688044 5413645 := bstep (se 3 (by rfl) ⟨1015058, by rfl⟩ : syracuseStep 5413645 = 2030117) B2030117
theorem B1899283 : Blo 1688044 1899283 := bstep (se 1 (by rfl) ⟨1424462, by rfl⟩ : syracuseStep 1899283 = 2848925) B2848925
theorem B5700401 : Blo 1688044 5700401 := bstep (se 2 (by rfl) ⟨2137650, by rfl⟩ : syracuseStep 5700401 = 4275301) B4275301
theorem B19249973 : Blo 1688044 19249973 := bstep (se 5 (by rfl) ⟨902342, by rfl⟩ : syracuseStep 19249973 = 1804685) B1804685
theorem B4807505 : Blo 1688044 4807505 := bstep (se 2 (by rfl) ⟨1802814, by rfl⟩ : syracuseStep 4807505 = 3605629) B3605629
theorem B3799889 : Blo 1688044 3799889 := bstep (se 2 (by rfl) ⟨1424958, by rfl⟩ : syracuseStep 3799889 = 2849917) B2849917
theorem B3799907 : Blo 1688044 3799907 := bstep (se 1 (by rfl) ⟨2849930, by rfl⟩ : syracuseStep 3799907 = 5699861) B5699861
theorem B9624419 : Blo 1688044 9624419 := bstep (se 1 (by rfl) ⟨7218314, by rfl⟩ : syracuseStep 9624419 = 14436629) B14436629
theorem B2849681 : Blo 1688044 2849681 := bstep (se 2 (by rfl) ⟨1068630, by rfl⟩ : syracuseStep 2849681 = 2137261) B2137261
theorem B4275089 : Blo 1688044 4275089 := bstep (se 2 (by rfl) ⟨1603158, by rfl⟩ : syracuseStep 4275089 = 3206317) B3206317
theorem B1899427 : Blo 1688044 1899427 := bstep (se 1 (by rfl) ⟨1424570, by rfl⟩ : syracuseStep 1899427 = 2849141) B2849141
theorem B8551331 : Blo 1688044 8551331 := bstep (se 1 (by rfl) ⟨6413498, by rfl⟩ : syracuseStep 8551331 = 12826997) B12826997
theorem B4807619 : Blo 1688044 4807619 := bstep (se 1 (by rfl) ⟨3605714, by rfl⟩ : syracuseStep 4807619 = 7211429) B7211429
theorem B4275139 : Blo 1688044 4275139 := bstep (se 1 (by rfl) ⟨3206354, by rfl⟩ : syracuseStep 4275139 = 6412709) B6412709
theorem B2137043 : Blo 1688044 2137043 := bstep (se 1 (by rfl) ⟨1602782, by rfl⟩ : syracuseStep 2137043 = 3205565) B3205565
theorem B2849809 : Blo 1688044 2849809 := bstep (se 2 (by rfl) ⟨1068678, by rfl⟩ : syracuseStep 2849809 = 2137357) B2137357
theorem B1899571 : Blo 1688044 1899571 := bstep (se 1 (by rfl) ⟨1424678, by rfl⟩ : syracuseStep 1899571 = 2849357) B2849357
theorem B2849843 : Blo 1688044 2849843 := bstep (se 1 (by rfl) ⟨2137382, by rfl⟩ : syracuseStep 2849843 = 4274765) B4274765
theorem B4275281 : Blo 1688044 4275281 := bstep (se 2 (by rfl) ⟨1603230, by rfl⟩ : syracuseStep 4275281 = 3206461) B3206461
theorem B3800177 : Blo 1688044 3800177 := bstep (se 2 (by rfl) ⟨1425066, by rfl⟩ : syracuseStep 3800177 = 2850133) B2850133
theorem B3800195 : Blo 1688044 3800195 := bstep (se 1 (by rfl) ⟨2850146, by rfl⟩ : syracuseStep 3800195 = 5700293) B5700293
theorem B3423377 : Blo 1688044 3423377 := bstep (se 2 (by rfl) ⟨1283766, by rfl⟩ : syracuseStep 3423377 = 2567533) B2567533
theorem B3128483 : Blo 1688044 3128483 := bstep (se 1 (by rfl) ⟨2346362, by rfl⟩ : syracuseStep 3128483 = 4692725) B4692725
theorem B2849971 : Blo 1688044 2849971 := bstep (se 1 (by rfl) ⟨2137478, by rfl⟩ : syracuseStep 2849971 = 4274957) B4274957
theorem B1899715 : Blo 1688044 1899715 := bstep (se 1 (by rfl) ⟨1424786, by rfl⟩ : syracuseStep 1899715 = 2849573) B2849573
theorem B5414147 : Blo 1688044 5414147 := bstep (se 1 (by rfl) ⟨4060610, by rfl⟩ : syracuseStep 5414147 = 8121221) B8121221
theorem B2850113 : Blo 1688044 2850113 := bstep (se 2 (by rfl) ⟨1068792, by rfl⟩ : syracuseStep 2850113 = 2137585) B2137585
theorem B5700941 : Blo 1688044 5700941 := bstep (se 3 (by rfl) ⟨1068926, by rfl⟩ : syracuseStep 5700941 = 2137853) B2137853
theorem B1899859 : Blo 1688044 1899859 := bstep (se 1 (by rfl) ⟨1424894, by rfl⟩ : syracuseStep 1899859 = 2849789) B2849789
theorem B6413681 : Blo 1688044 6413681 := bstep (se 2 (by rfl) ⟨2405130, by rfl⟩ : syracuseStep 6413681 = 4810261) B4810261
theorem B5700995 : Blo 1688044 5700995 := bstep (se 1 (by rfl) ⟨4275746, by rfl⟩ : syracuseStep 5700995 = 8551493) B8551493
theorem B3800465 : Blo 1688044 3800465 := bstep (se 2 (by rfl) ⟨1425174, by rfl⟩ : syracuseStep 3800465 = 2850349) B2850349
theorem B3800483 : Blo 1688044 3800483 := bstep (se 1 (by rfl) ⟨2850362, by rfl⟩ : syracuseStep 3800483 = 5700725) B5700725
theorem B2850241 : Blo 1688044 2850241 := bstep (se 2 (by rfl) ⟨1068840, by rfl⟩ : syracuseStep 2850241 = 2137681) B2137681
theorem B11124173 : Blo 1688044 11124173 := bstep (se 3 (by rfl) ⟨2085782, by rfl⟩ : syracuseStep 11124173 = 4171565) B4171565
theorem B1900003 : Blo 1688044 1900003 := bstep (se 1 (by rfl) ⟨1425002, by rfl⟩ : syracuseStep 1900003 = 2850005) B2850005
theorem B2850275 : Blo 1688044 2850275 := bstep (se 1 (by rfl) ⟨2137706, by rfl⟩ : syracuseStep 2850275 = 4275413) B4275413
theorem B4111889 : Blo 1688044 4111889 := bstep (se 2 (by rfl) ⟨1541958, by rfl⟩ : syracuseStep 4111889 = 3083917) B3083917
theorem B2850403 : Blo 1688044 2850403 := bstep (se 1 (by rfl) ⟨2137802, by rfl⟩ : syracuseStep 2850403 = 4275605) B4275605
theorem B1900147 : Blo 1688044 1900147 := bstep (se 1 (by rfl) ⟨1425110, by rfl⟩ : syracuseStep 1900147 = 2850221) B2850221
theorem B5701265 : Blo 1688044 5701265 := bstep (se 2 (by rfl) ⟨2137974, by rfl⟩ : syracuseStep 5701265 = 4275949) B4275949
theorem B2137747 : Blo 1688044 2137747 := bstep (se 1 (by rfl) ⟨1603310, by rfl⟩ : syracuseStep 2137747 = 3206621) B3206621
theorem B3800753 : Blo 1688044 3800753 := bstep (se 2 (by rfl) ⟨1425282, by rfl⟩ : syracuseStep 3800753 = 2850565) B2850565
theorem B6504113 : Blo 1688044 6504113 := bstep (se 2 (by rfl) ⟨2439042, by rfl⟩ : syracuseStep 6504113 = 4878085) B4878085
theorem B3800771 : Blo 1688044 3800771 := bstep (se 1 (by rfl) ⟨2850578, by rfl⟩ : syracuseStep 3800771 = 5701157) B5701157
theorem B8552141 : Blo 1688044 8552141 := bstep (se 3 (by rfl) ⟨1603526, by rfl⟩ : syracuseStep 8552141 = 3207053) B3207053
theorem B2850545 : Blo 1688044 2850545 := bstep (se 2 (by rfl) ⟨1068954, by rfl⟩ : syracuseStep 2850545 = 2137909) B2137909
theorem B2137843 : Blo 1688044 2137843 := bstep (se 1 (by rfl) ⟨1603382, by rfl⟩ : syracuseStep 2137843 = 3206765) B3206765
theorem B1900291 : Blo 1688044 1900291 := bstep (se 1 (by rfl) ⟨1425218, by rfl⟩ : syracuseStep 1900291 = 2850437) B2850437
theorem B2850673 : Blo 1688044 2850673 := bstep (se 2 (by rfl) ⟨1069002, by rfl⟩ : syracuseStep 2850673 = 2138005) B2138005
theorem B1900435 : Blo 1688044 1900435 := bstep (se 1 (by rfl) ⟨1425326, by rfl⟩ : syracuseStep 1900435 = 2850653) B2850653
theorem B2850707 : Blo 1688044 2850707 := bstep (se 1 (by rfl) ⟨2138030, by rfl⟩ : syracuseStep 2850707 = 4276061) B4276061
theorem B4808621 : Blo 1688044 4808621 := bstep (se 3 (by rfl) ⟨901616, by rfl⟩ : syracuseStep 4808621 = 1803233) B1803233
theorem B3801041 : Blo 1688044 3801041 := bstep (se 2 (by rfl) ⟨1425390, by rfl⟩ : syracuseStep 3801041 = 2850781) B2850781
theorem B3801059 : Blo 1688044 3801059 := bstep (se 1 (by rfl) ⟨2850794, by rfl⟩ : syracuseStep 3801059 = 5701589) B5701589
theorem B8552465 : Blo 1688044 8552465 := bstep (se 2 (by rfl) ⟨3207174, by rfl⟩ : syracuseStep 8552465 = 6414349) B6414349
theorem B5775383 : Blo 1688044 5775383 := bstep (se 1 (by rfl) ⟨4331537, by rfl⟩ : syracuseStep 5775383 = 8663075) B8663075
theorem B4333591 : Blo 1688044 4333591 := bstep (se 1 (by rfl) ⟨3250193, by rfl⟩ : syracuseStep 4333591 = 6500387) B6500387
theorem B3801113 : Blo 1688044 3801113 := bstep (se 2 (by rfl) ⟨1425417, by rfl⟩ : syracuseStep 3801113 = 2850835) B2850835
theorem B5701697 : Blo 1688044 5701697 := bstep (se 2 (by rfl) ⟨2138136, by rfl⟩ : syracuseStep 5701697 = 4276273) B4276273
theorem B18268253 : Blo 1688044 18268253 := bstep (se 3 (by rfl) ⟨3425297, by rfl⟩ : syracuseStep 18268253 = 6850595) B6850595
theorem B1900651 : Blo 1688044 1900651 := bstep (se 1 (by rfl) ⟨1425488, by rfl⟩ : syracuseStep 1900651 = 2850977) B2850977
theorem B3801203 : Blo 1688044 3801203 := bstep (se 1 (by rfl) ⟨2850902, by rfl⟩ : syracuseStep 3801203 = 5701805) B5701805
theorem B3801239 : Blo 1688044 3801239 := bstep (se 1 (by rfl) ⟨2850929, by rfl⟩ : syracuseStep 3801239 = 5701859) B5701859
theorem B8552627 : Blo 1688044 8552627 := bstep (se 1 (by rfl) ⟨6414470, by rfl⟩ : syracuseStep 8552627 = 12828941) B12828941
theorem B43860149 : Blo 1688044 43860149 := bstep (se 5 (by rfl) ⟨2055944, by rfl⟩ : syracuseStep 43860149 = 4111889) B4111889
theorem B2851031 : Blo 1688044 2851031 := bstep (se 1 (by rfl) ⟨2138273, by rfl⟩ : syracuseStep 2851031 = 4276547) B4276547
theorem B1900759 : Blo 1688044 1900759 := bstep (se 1 (by rfl) ⟨1425569, by rfl⟩ : syracuseStep 1900759 = 2851139) B2851139
theorem B3801419 : Blo 1688044 3801419 := bstep (se 1 (by rfl) ⟨2851064, by rfl⟩ : syracuseStep 3801419 = 5702129) B5702129
theorem B2851159 : Blo 1688044 2851159 := bstep (se 1 (by rfl) ⟨2138369, by rfl⟩ : syracuseStep 2851159 = 4276739) B4276739
theorem B54804853 : Blo 1688044 54804853 := bstep (se 5 (by rfl) ⟨2568977, by rfl⟩ : syracuseStep 54804853 = 5137955) B5137955
theorem B3801473 : Blo 1688044 3801473 := bstep (se 2 (by rfl) ⟨1425552, by rfl⟩ : syracuseStep 3801473 = 2851105) B2851105
theorem B1900939 : Blo 1688044 1900939 := bstep (se 1 (by rfl) ⟨1425704, by rfl⟩ : syracuseStep 1900939 = 2851409) B2851409
theorem B14426545 : Blo 1688044 14426545 := bstep (se 2 (by rfl) ⟨5409954, by rfl⟩ : syracuseStep 14426545 = 10819909) B10819909
theorem B1688055 : Blo 1688044 1688055 := bstep (se 1 (by rfl) ⟨1266041, by rfl⟩ : syracuseStep 1688055 = 2532083) B2532083
theorem B1901047 : Blo 1688044 1901047 := bstep (se 1 (by rfl) ⟨1425785, by rfl⟩ : syracuseStep 1901047 = 2851571) B2851571
theorem B1688075 : Blo 1688044 1688075 := bstep (se 1 (by rfl) ⟨1266056, by rfl⟩ : syracuseStep 1688075 = 2532113) B2532113
theorem B1688087 : Blo 1688044 1688087 := bstep (se 1 (by rfl) ⟨1266065, by rfl⟩ : syracuseStep 1688087 = 2532131) B2532131
theorem B4276759 : Blo 1688044 4276759 := bstep (se 1 (by rfl) ⟨3207569, by rfl⟩ : syracuseStep 4276759 = 6415139) B6415139
theorem B1688107 : Blo 1688044 1688107 := bstep (se 1 (by rfl) ⟨1266080, by rfl⟩ : syracuseStep 1688107 = 2532161) B2532161
theorem B3811263029 : Blo 1688044 3811263029 := bstep (se 5 (by rfl) ⟨178652954, by rfl⟩ : syracuseStep 3811263029 = 357305909) B357305909
theorem B1688119 : Blo 1688044 1688119 := bstep (se 1 (by rfl) ⟨1266089, by rfl⟩ : syracuseStep 1688119 = 2532179) B2532179
theorem B1688139 : Blo 1688044 1688139 := bstep (se 1 (by rfl) ⟨1266104, by rfl⟩ : syracuseStep 1688139 = 2532209) B2532209
theorem B1688151 : Blo 1688044 1688151 := bstep (se 1 (by rfl) ⟨1266113, by rfl⟩ : syracuseStep 1688151 = 2532227) B2532227
theorem B3850841 : Blo 1688044 3850841 := bstep (se 2 (by rfl) ⟨1444065, by rfl⟩ : syracuseStep 3850841 = 2888131) B2888131
theorem B3801689 : Blo 1688044 3801689 := bstep (se 2 (by rfl) ⟨1425633, by rfl⟩ : syracuseStep 3801689 = 2851267) B2851267
theorem B5702237 : Blo 1688044 5702237 := bstep (se 3 (by rfl) ⟨1069169, by rfl⟩ : syracuseStep 5702237 = 2138339) B2138339
theorem B1688171 : Blo 1688044 1688171 := bstep (se 1 (by rfl) ⟨1266128, by rfl⟩ : syracuseStep 1688171 = 2532257) B2532257
theorem B1688183 : Blo 1688044 1688183 := bstep (se 1 (by rfl) ⟨1266137, by rfl⟩ : syracuseStep 1688183 = 2532275) B2532275
theorem B1688203 : Blo 1688044 1688203 := bstep (se 1 (by rfl) ⟨1266152, by rfl⟩ : syracuseStep 1688203 = 2532305) B2532305
theorem B1688215 : Blo 1688044 1688215 := bstep (se 1 (by rfl) ⟨1266161, by rfl⟩ : syracuseStep 1688215 = 2532323) B2532323
theorem B1688235 : Blo 1688044 1688235 := bstep (se 1 (by rfl) ⟨1266176, by rfl⟩ : syracuseStep 1688235 = 2532353) B2532353
theorem B1901227 : Blo 1688044 1901227 := bstep (se 1 (by rfl) ⟨1425920, by rfl⟩ : syracuseStep 1901227 = 2851841) B2851841
theorem B4809395 : Blo 1688044 4809395 := bstep (se 1 (by rfl) ⟨3607046, by rfl⟩ : syracuseStep 4809395 = 7214093) B7214093
theorem B3801779 : Blo 1688044 3801779 := bstep (se 1 (by rfl) ⟨2851334, by rfl⟩ : syracuseStep 3801779 = 5702669) B5702669
theorem B1688247 : Blo 1688044 1688247 := bstep (se 1 (by rfl) ⟨1266185, by rfl⟩ : syracuseStep 1688247 = 2532371) B2532371
theorem B1688267 : Blo 1688044 1688267 := bstep (se 1 (by rfl) ⟨1266200, by rfl⟩ : syracuseStep 1688267 = 2532401) B2532401
theorem B4809419 : Blo 1688044 4809419 := bstep (se 1 (by rfl) ⟨3607064, by rfl⟩ : syracuseStep 4809419 = 7214129) B7214129
theorem B1688279 : Blo 1688044 1688279 := bstep (se 1 (by rfl) ⟨1266209, by rfl⟩ : syracuseStep 1688279 = 2532419) B2532419
theorem B3801815 : Blo 1688044 3801815 := bstep (se 1 (by rfl) ⟨2851361, by rfl⟩ : syracuseStep 3801815 = 5702723) B5702723
theorem B1688299 : Blo 1688044 1688299 := bstep (se 1 (by rfl) ⟨1266224, by rfl⟩ : syracuseStep 1688299 = 2532449) B2532449
theorem B1688311 : Blo 1688044 1688311 := bstep (se 1 (by rfl) ⟨1266233, by rfl⟩ : syracuseStep 1688311 = 2532467) B2532467
theorem B2532107 : Blo 1688044 2532107 := bstep (se 1 (by rfl) ⟨1899080, by rfl⟩ : syracuseStep 2532107 = 3798161) B3798161
theorem B1688331 : Blo 1688044 1688331 := bstep (se 1 (by rfl) ⟨1266248, by rfl⟩ : syracuseStep 1688331 = 2532497) B2532497
theorem B2532119 : Blo 1688044 2532119 := bstep (se 1 (by rfl) ⟨1899089, by rfl⟩ : syracuseStep 2532119 = 3798179) B3798179
theorem B1688343 : Blo 1688044 1688343 := bstep (se 1 (by rfl) ⟨1266257, by rfl⟩ : syracuseStep 1688343 = 2532515) B2532515
theorem B1688363 : Blo 1688044 1688363 := bstep (se 1 (by rfl) ⟨1266272, by rfl⟩ : syracuseStep 1688363 = 2532545) B2532545
theorem B6087469 : Blo 1688044 6087469 := bstep (se 3 (by rfl) ⟨1141400, by rfl⟩ : syracuseStep 6087469 = 2282801) B2282801
theorem B1688375 : Blo 1688044 1688375 := bstep (se 1 (by rfl) ⟨1266281, by rfl⟩ : syracuseStep 1688375 = 2532563) B2532563
theorem B1688395 : Blo 1688044 1688395 := bstep (se 1 (by rfl) ⟨1266296, by rfl⟩ : syracuseStep 1688395 = 2532593) B2532593
theorem B1688407 : Blo 1688044 1688407 := bstep (se 1 (by rfl) ⟨1266305, by rfl⟩ : syracuseStep 1688407 = 2532611) B2532611
theorem B2532185 : Blo 1688044 2532185 := bstep (se 2 (by rfl) ⟨949569, by rfl⟩ : syracuseStep 2532185 = 1899139) B1899139
theorem B1688427 : Blo 1688044 1688427 := bstep (se 1 (by rfl) ⟨1266320, by rfl⟩ : syracuseStep 1688427 = 2532641) B2532641
theorem B1688439 : Blo 1688044 1688439 := bstep (se 1 (by rfl) ⟨1266329, by rfl⟩ : syracuseStep 1688439 = 2532659) B2532659
theorem B1688459 : Blo 1688044 1688459 := bstep (se 1 (by rfl) ⟨1266344, by rfl⟩ : syracuseStep 1688459 = 2532689) B2532689
theorem B3801995 : Blo 1688044 3801995 := bstep (se 1 (by rfl) ⟨2851496, by rfl⟩ : syracuseStep 3801995 = 5702993) B5702993
theorem B1688471 : Blo 1688044 1688471 := bstep (se 1 (by rfl) ⟨1266353, by rfl⟩ : syracuseStep 1688471 = 2532707) B2532707
theorem B1688491 : Blo 1688044 1688491 := bstep (se 1 (by rfl) ⟨1266368, by rfl⟩ : syracuseStep 1688491 = 2532737) B2532737
theorem B32474033 : Blo 1688044 32474033 := bstep (se 2 (by rfl) ⟨12177762, by rfl⟩ : syracuseStep 32474033 = 24355525) B24355525
theorem B1688503 : Blo 1688044 1688503 := bstep (se 1 (by rfl) ⟨1266377, by rfl⟩ : syracuseStep 1688503 = 2532755) B2532755
theorem B3802049 : Blo 1688044 3802049 := bstep (se 2 (by rfl) ⟨1425768, by rfl⟩ : syracuseStep 3802049 = 2851537) B2851537
theorem B2532299 : Blo 1688044 2532299 := bstep (se 1 (by rfl) ⟨1899224, by rfl⟩ : syracuseStep 2532299 = 3798449) B3798449
theorem B1688523 : Blo 1688044 1688523 := bstep (se 1 (by rfl) ⟨1266392, by rfl⟩ : syracuseStep 1688523 = 2532785) B2532785
theorem B6415307 : Blo 1688044 6415307 := bstep (se 1 (by rfl) ⟨4811480, by rfl⟩ : syracuseStep 6415307 = 9622961) B9622961
theorem B4277195 : Blo 1688044 4277195 := bstep (se 1 (by rfl) ⟨3207896, by rfl⟩ : syracuseStep 4277195 = 6415793) B6415793
theorem B2851787 : Blo 1688044 2851787 := bstep (se 1 (by rfl) ⟨2138840, by rfl⟩ : syracuseStep 2851787 = 4277681) B4277681
theorem B2532311 : Blo 1688044 2532311 := bstep (se 1 (by rfl) ⟨1899233, by rfl⟩ : syracuseStep 2532311 = 3798467) B3798467
theorem B1688535 : Blo 1688044 1688535 := bstep (se 1 (by rfl) ⟨1266401, by rfl⟩ : syracuseStep 1688535 = 2532803) B2532803
theorem B6415321 : Blo 1688044 6415321 := bstep (se 2 (by rfl) ⟨2405745, by rfl⟩ : syracuseStep 6415321 = 4811491) B4811491
theorem B1688555 : Blo 1688044 1688555 := bstep (se 1 (by rfl) ⟨1266416, by rfl⟩ : syracuseStep 1688555 = 2532833) B2532833
theorem B1688567 : Blo 1688044 1688567 := bstep (se 1 (by rfl) ⟨1266425, by rfl⟩ : syracuseStep 1688567 = 2532851) B2532851
theorem B7218179 : Blo 1688044 7218179 := bstep (se 1 (by rfl) ⟨5413634, by rfl⟩ : syracuseStep 7218179 = 10827269) B10827269
theorem B1688587 : Blo 1688044 1688587 := bstep (se 1 (by rfl) ⟨1266440, by rfl⟩ : syracuseStep 1688587 = 2532881) B2532881
theorem B1688599 : Blo 1688044 1688599 := bstep (se 1 (by rfl) ⟨1266449, by rfl⟩ : syracuseStep 1688599 = 2532899) B2532899
theorem B2532377 : Blo 1688044 2532377 := bstep (se 2 (by rfl) ⟨949641, by rfl⟩ : syracuseStep 2532377 = 1899283) B1899283
theorem B1688619 : Blo 1688044 1688619 := bstep (se 1 (by rfl) ⟨1266464, by rfl⟩ : syracuseStep 1688619 = 2532929) B2532929
theorem B1688631 : Blo 1688044 1688631 := bstep (se 1 (by rfl) ⟨1266473, by rfl⟩ : syracuseStep 1688631 = 2532947) B2532947
theorem B1688651 : Blo 1688044 1688651 := bstep (se 1 (by rfl) ⟨1266488, by rfl⟩ : syracuseStep 1688651 = 2532977) B2532977
theorem B7808075 : Blo 1688044 7808075 := bstep (se 1 (by rfl) ⟨5856056, by rfl⟩ : syracuseStep 7808075 = 11712113) B11712113
theorem B3294283 : Blo 1688044 3294283 := bstep (se 1 (by rfl) ⟨2470712, by rfl⟩ : syracuseStep 3294283 = 4941425) B4941425
theorem B2851915 : Blo 1688044 2851915 := bstep (se 1 (by rfl) ⟨2138936, by rfl⟩ : syracuseStep 2851915 = 4277873) B4277873
theorem B1688663 : Blo 1688044 1688663 := bstep (se 1 (by rfl) ⟨1266497, by rfl⟩ : syracuseStep 1688663 = 2532995) B2532995
theorem B11551837 : Blo 1688044 11551837 := bstep (se 3 (by rfl) ⟨2165969, by rfl⟩ : syracuseStep 11551837 = 4331939) B4331939
theorem B1688683 : Blo 1688044 1688683 := bstep (se 1 (by rfl) ⟨1266512, by rfl⟩ : syracuseStep 1688683 = 2533025) B2533025
theorem B1688695 : Blo 1688044 1688695 := bstep (se 1 (by rfl) ⟨1266521, by rfl⟩ : syracuseStep 1688695 = 2533043) B2533043
theorem B2532491 : Blo 1688044 2532491 := bstep (se 1 (by rfl) ⟨1899368, by rfl⟩ : syracuseStep 2532491 = 3798737) B3798737
theorem B1688715 : Blo 1688044 1688715 := bstep (se 1 (by rfl) ⟨1266536, by rfl⟩ : syracuseStep 1688715 = 2533073) B2533073
theorem B2532503 : Blo 1688044 2532503 := bstep (se 1 (by rfl) ⟨1899377, by rfl⟩ : syracuseStep 2532503 = 3798755) B3798755
theorem B1688727 : Blo 1688044 1688727 := bstep (se 1 (by rfl) ⟨1266545, by rfl⟩ : syracuseStep 1688727 = 2533091) B2533091
theorem B3802265 : Blo 1688044 3802265 := bstep (se 2 (by rfl) ⟨1425849, by rfl⟩ : syracuseStep 3802265 = 2851699) B2851699
theorem B1688747 : Blo 1688044 1688747 := bstep (se 1 (by rfl) ⟨1266560, by rfl⟩ : syracuseStep 1688747 = 2533121) B2533121
theorem B1688759 : Blo 1688044 1688759 := bstep (se 1 (by rfl) ⟨1266569, by rfl⟩ : syracuseStep 1688759 = 2533139) B2533139
theorem B1688779 : Blo 1688044 1688779 := bstep (se 1 (by rfl) ⟨1266584, by rfl⟩ : syracuseStep 1688779 = 2533169) B2533169
theorem B1828043 : Blo 1688044 1828043 := bstep (se 1 (by rfl) ⟨1371032, by rfl⟩ : syracuseStep 1828043 = 2742065) B2742065
theorem B29664461 : Blo 1688044 29664461 := bstep (se 3 (by rfl) ⟨5562086, by rfl⟩ : syracuseStep 29664461 = 11124173) B11124173
theorem B1688791 : Blo 1688044 1688791 := bstep (se 1 (by rfl) ⟨1266593, by rfl⟩ : syracuseStep 1688791 = 2533187) B2533187
theorem B2532569 : Blo 1688044 2532569 := bstep (se 2 (by rfl) ⟨949713, by rfl⟩ : syracuseStep 2532569 = 1899427) B1899427
theorem B12829913 : Blo 1688044 12829913 := bstep (se 2 (by rfl) ⟨4811217, by rfl⟩ : syracuseStep 12829913 = 9622435) B9622435
theorem B1688811 : Blo 1688044 1688811 := bstep (se 1 (by rfl) ⟨1266608, by rfl⟩ : syracuseStep 1688811 = 2533217) B2533217
theorem B3802355 : Blo 1688044 3802355 := bstep (se 1 (by rfl) ⟨2851766, by rfl⟩ : syracuseStep 3802355 = 5703533) B5703533
theorem B1688823 : Blo 1688044 1688823 := bstep (se 1 (by rfl) ⟨1266617, by rfl⟩ : syracuseStep 1688823 = 2533235) B2533235
theorem B1688843 : Blo 1688044 1688843 := bstep (se 1 (by rfl) ⟨1266632, by rfl⟩ : syracuseStep 1688843 = 2533265) B2533265
theorem B1688855 : Blo 1688044 1688855 := bstep (se 1 (by rfl) ⟨1266641, by rfl⟩ : syracuseStep 1688855 = 2533283) B2533283
theorem B3802391 : Blo 1688044 3802391 := bstep (se 1 (by rfl) ⟨2851793, by rfl⟩ : syracuseStep 3802391 = 5703587) B5703587
theorem B1688875 : Blo 1688044 1688875 := bstep (se 1 (by rfl) ⟨1266656, by rfl⟩ : syracuseStep 1688875 = 2533313) B2533313
theorem B1688887 : Blo 1688044 1688887 := bstep (se 1 (by rfl) ⟨1266665, by rfl⟩ : syracuseStep 1688887 = 2533331) B2533331
theorem B4277569 : Blo 1688044 4277569 := bstep (se 2 (by rfl) ⟨1604088, by rfl⟩ : syracuseStep 4277569 = 3208177) B3208177
theorem B2532683 : Blo 1688044 2532683 := bstep (se 1 (by rfl) ⟨1899512, by rfl⟩ : syracuseStep 2532683 = 3799025) B3799025
theorem B1688907 : Blo 1688044 1688907 := bstep (se 1 (by rfl) ⟨1266680, by rfl⟩ : syracuseStep 1688907 = 2533361) B2533361
theorem B2532695 : Blo 1688044 2532695 := bstep (se 1 (by rfl) ⟨1899521, by rfl⟩ : syracuseStep 2532695 = 3799043) B3799043
theorem B1688919 : Blo 1688044 1688919 := bstep (se 1 (by rfl) ⟨1266689, by rfl⟩ : syracuseStep 1688919 = 2533379) B2533379
theorem B1688939 : Blo 1688044 1688939 := bstep (se 1 (by rfl) ⟨1266704, by rfl⟩ : syracuseStep 1688939 = 2533409) B2533409
theorem B1688951 : Blo 1688044 1688951 := bstep (se 1 (by rfl) ⟨1266713, by rfl⟩ : syracuseStep 1688951 = 2533427) B2533427
theorem B1688971 : Blo 1688044 1688971 := bstep (se 1 (by rfl) ⟨1266728, by rfl⟩ : syracuseStep 1688971 = 2533457) B2533457
theorem B1688983 : Blo 1688044 1688983 := bstep (se 1 (by rfl) ⟨1266737, by rfl⟩ : syracuseStep 1688983 = 2533475) B2533475
theorem B2532761 : Blo 1688044 2532761 := bstep (se 2 (by rfl) ⟨949785, by rfl⟩ : syracuseStep 2532761 = 1899571) B1899571
theorem B12346775 : Blo 1688044 12346775 := bstep (se 1 (by rfl) ⟨9260081, by rfl⟩ : syracuseStep 12346775 = 18520163) B18520163
theorem B1689003 : Blo 1688044 1689003 := bstep (se 1 (by rfl) ⟨1266752, by rfl⟩ : syracuseStep 1689003 = 2533505) B2533505
theorem B1689015 : Blo 1688044 1689015 := bstep (se 1 (by rfl) ⟨1266761, by rfl⟩ : syracuseStep 1689015 = 2533523) B2533523
theorem B1803703 : Blo 1688044 1803703 := bstep (se 1 (by rfl) ⟨1352777, by rfl⟩ : syracuseStep 1803703 = 2705555) B2705555
theorem B3605953 : Blo 1688044 3605953 := bstep (se 2 (by rfl) ⟨1352232, by rfl⟩ : syracuseStep 3605953 = 2704465) B2704465
theorem B1689035 : Blo 1688044 1689035 := bstep (se 1 (by rfl) ⟨1266776, by rfl⟩ : syracuseStep 1689035 = 2533553) B2533553
theorem B3802571 : Blo 1688044 3802571 := bstep (se 1 (by rfl) ⟨2851928, by rfl⟩ : syracuseStep 3802571 = 5703857) B5703857
theorem B1689047 : Blo 1688044 1689047 := bstep (se 1 (by rfl) ⟨1266785, by rfl⟩ : syracuseStep 1689047 = 2533571) B2533571
theorem B4810205 : Blo 1688044 4810205 := bstep (se 3 (by rfl) ⟨901913, by rfl⟩ : syracuseStep 4810205 = 1803827) B1803827
theorem B1689067 : Blo 1688044 1689067 := bstep (se 1 (by rfl) ⟨1266800, by rfl⟩ : syracuseStep 1689067 = 2533601) B2533601
theorem B1689079 : Blo 1688044 1689079 := bstep (se 1 (by rfl) ⟨1266809, by rfl⟩ : syracuseStep 1689079 = 2533619) B2533619
theorem B2532875 : Blo 1688044 2532875 := bstep (se 1 (by rfl) ⟨1899656, by rfl⟩ : syracuseStep 2532875 = 3799313) B3799313
theorem B1689099 : Blo 1688044 1689099 := bstep (se 1 (by rfl) ⟨1266824, by rfl⟩ : syracuseStep 1689099 = 2533649) B2533649
theorem B2532887 : Blo 1688044 2532887 := bstep (se 1 (by rfl) ⟨1899665, by rfl⟩ : syracuseStep 2532887 = 3799331) B3799331
theorem B1689111 : Blo 1688044 1689111 := bstep (se 1 (by rfl) ⟨1266833, by rfl⟩ : syracuseStep 1689111 = 2533667) B2533667
theorem B1689131 : Blo 1688044 1689131 := bstep (se 1 (by rfl) ⟨1266848, by rfl⟩ : syracuseStep 1689131 = 2533697) B2533697
theorem B8119853 : Blo 1688044 8119853 := bstep (se 3 (by rfl) ⟨1522472, by rfl⟩ : syracuseStep 8119853 = 3044945) B3044945
theorem B1689143 : Blo 1688044 1689143 := bstep (se 1 (by rfl) ⟨1266857, by rfl⟩ : syracuseStep 1689143 = 2533715) B2533715
theorem B9619019 : Blo 1688044 9619019 := bstep (se 1 (by rfl) ⟨7214264, by rfl⟩ : syracuseStep 9619019 = 14428529) B14428529
theorem B1689163 : Blo 1688044 1689163 := bstep (se 1 (by rfl) ⟨1266872, by rfl⟩ : syracuseStep 1689163 = 2533745) B2533745
theorem B1689175 : Blo 1688044 1689175 := bstep (se 1 (by rfl) ⟨1266881, by rfl⟩ : syracuseStep 1689175 = 2533763) B2533763
theorem B2532953 : Blo 1688044 2532953 := bstep (se 2 (by rfl) ⟨949857, by rfl⟩ : syracuseStep 2532953 = 1899715) B1899715
theorem B1689195 : Blo 1688044 1689195 := bstep (se 1 (by rfl) ⟨1266896, by rfl⟩ : syracuseStep 1689195 = 2533793) B2533793
theorem B1689207 : Blo 1688044 1689207 := bstep (se 1 (by rfl) ⟨1266905, by rfl⟩ : syracuseStep 1689207 = 2533811) B2533811
theorem B1689227 : Blo 1688044 1689227 := bstep (se 1 (by rfl) ⟨1266920, by rfl⟩ : syracuseStep 1689227 = 2533841) B2533841
theorem B1689239 : Blo 1688044 1689239 := bstep (se 1 (by rfl) ⟨1266929, by rfl⟩ : syracuseStep 1689239 = 2533859) B2533859
theorem B1689259 : Blo 1688044 1689259 := bstep (se 1 (by rfl) ⟨1266944, by rfl⟩ : syracuseStep 1689259 = 2533889) B2533889
theorem B1689271 : Blo 1688044 1689271 := bstep (se 1 (by rfl) ⟨1266953, by rfl⟩ : syracuseStep 1689271 = 2533907) B2533907
theorem B52741829 : Blo 1688044 52741829 := bstep (se 4 (by rfl) ⟨4944546, by rfl⟩ : syracuseStep 52741829 = 9889093) B9889093
theorem B2533067 : Blo 1688044 2533067 := bstep (se 1 (by rfl) ⟨1899800, by rfl⟩ : syracuseStep 2533067 = 3799601) B3799601
theorem B1689291 : Blo 1688044 1689291 := bstep (se 1 (by rfl) ⟨1266968, by rfl⟩ : syracuseStep 1689291 = 2533937) B2533937
theorem B5703371 : Blo 1688044 5703371 := bstep (se 1 (by rfl) ⟨4277528, by rfl⟩ : syracuseStep 5703371 = 8555057) B8555057
theorem B2533079 : Blo 1688044 2533079 := bstep (se 1 (by rfl) ⟨1899809, by rfl⟩ : syracuseStep 2533079 = 3799619) B3799619
theorem B1689303 : Blo 1688044 1689303 := bstep (se 1 (by rfl) ⟨1266977, by rfl⟩ : syracuseStep 1689303 = 2533955) B2533955
theorem B1689323 : Blo 1688044 1689323 := bstep (se 1 (by rfl) ⟨1266992, by rfl⟩ : syracuseStep 1689323 = 2533985) B2533985
theorem B1689335 : Blo 1688044 1689335 := bstep (se 1 (by rfl) ⟨1267001, by rfl⟩ : syracuseStep 1689335 = 2534003) B2534003
theorem B1689355 : Blo 1688044 1689355 := bstep (se 1 (by rfl) ⟨1267016, by rfl⟩ : syracuseStep 1689355 = 2534033) B2534033
theorem B3606295 : Blo 1688044 3606295 := bstep (se 1 (by rfl) ⟨2704721, by rfl⟩ : syracuseStep 3606295 = 5409443) B5409443
theorem B1689367 : Blo 1688044 1689367 := bstep (se 1 (by rfl) ⟨1267025, by rfl⟩ : syracuseStep 1689367 = 2534051) B2534051
theorem B2533145 : Blo 1688044 2533145 := bstep (se 2 (by rfl) ⟨949929, by rfl⟩ : syracuseStep 2533145 = 1899859) B1899859
theorem B2705177 : Blo 1688044 2705177 := bstep (se 2 (by rfl) ⟨1014441, by rfl⟩ : syracuseStep 2705177 = 2028883) B2028883
theorem B4171543 : Blo 1688044 4171543 := bstep (se 1 (by rfl) ⟨3128657, by rfl⟩ : syracuseStep 4171543 = 6257315) B6257315
theorem B1689387 : Blo 1688044 1689387 := bstep (se 1 (by rfl) ⟨1267040, by rfl⟩ : syracuseStep 1689387 = 2534081) B2534081
theorem B1689399 : Blo 1688044 1689399 := bstep (se 1 (by rfl) ⟨1267049, by rfl⟩ : syracuseStep 1689399 = 2534099) B2534099
theorem B1689419 : Blo 1688044 1689419 := bstep (se 1 (by rfl) ⟨1267064, by rfl⟩ : syracuseStep 1689419 = 2534129) B2534129
theorem B1689431 : Blo 1688044 1689431 := bstep (se 1 (by rfl) ⟨1267073, by rfl⟩ : syracuseStep 1689431 = 2534147) B2534147
theorem B1689451 : Blo 1688044 1689451 := bstep (se 1 (by rfl) ⟨1267088, by rfl⟩ : syracuseStep 1689451 = 2534177) B2534177
theorem B1689463 : Blo 1688044 1689463 := bstep (se 1 (by rfl) ⟨1267097, by rfl⟩ : syracuseStep 1689463 = 2534195) B2534195
theorem B3205003 : Blo 1688044 3205003 := bstep (se 1 (by rfl) ⟨2403752, by rfl⟩ : syracuseStep 3205003 = 4807505) B4807505
theorem B2533259 : Blo 1688044 2533259 := bstep (se 1 (by rfl) ⟨1899944, by rfl⟩ : syracuseStep 2533259 = 3799889) B3799889
theorem B1689483 : Blo 1688044 1689483 := bstep (se 1 (by rfl) ⟨1267112, by rfl⟩ : syracuseStep 1689483 = 2534225) B2534225
theorem B2533271 : Blo 1688044 2533271 := bstep (se 1 (by rfl) ⟨1899953, by rfl⟩ : syracuseStep 2533271 = 3799907) B3799907
theorem B1689495 : Blo 1688044 1689495 := bstep (se 1 (by rfl) ⟨1267121, by rfl⟩ : syracuseStep 1689495 = 2534243) B2534243
theorem B6416279 : Blo 1688044 6416279 := bstep (se 1 (by rfl) ⟨4812209, by rfl⟩ : syracuseStep 6416279 = 9624419) B9624419
theorem B1689515 : Blo 1688044 1689515 := bstep (se 1 (by rfl) ⟨1267136, by rfl⟩ : syracuseStep 1689515 = 2534273) B2534273
theorem B1689527 : Blo 1688044 1689527 := bstep (se 1 (by rfl) ⟨1267145, by rfl⟩ : syracuseStep 1689527 = 2534291) B2534291
theorem B1689547 : Blo 1688044 1689547 := bstep (se 1 (by rfl) ⟨1267160, by rfl⟩ : syracuseStep 1689547 = 2534321) B2534321
theorem B3205079 : Blo 1688044 3205079 := bstep (se 1 (by rfl) ⟨2403809, by rfl⟩ : syracuseStep 3205079 = 4807619) B4807619
theorem B1689559 : Blo 1688044 1689559 := bstep (se 1 (by rfl) ⟨1267169, by rfl⟩ : syracuseStep 1689559 = 2534339) B2534339
theorem B8112089 : Blo 1688044 8112089 := bstep (se 2 (by rfl) ⟨3042033, by rfl⟩ : syracuseStep 8112089 = 6084067) B6084067
theorem B2533337 : Blo 1688044 2533337 := bstep (se 2 (by rfl) ⟨950001, by rfl⟩ : syracuseStep 2533337 = 1900003) B1900003
theorem B5703641 : Blo 1688044 5703641 := bstep (se 2 (by rfl) ⟨2138865, by rfl⟩ : syracuseStep 5703641 = 4277731) B4277731
theorem B1689579 : Blo 1688044 1689579 := bstep (se 1 (by rfl) ⟨1267184, by rfl⟩ : syracuseStep 1689579 = 2534369) B2534369
theorem B1689591 : Blo 1688044 1689591 := bstep (se 1 (by rfl) ⟨1267193, by rfl⟩ : syracuseStep 1689591 = 2534387) B2534387
theorem B1689611 : Blo 1688044 1689611 := bstep (se 1 (by rfl) ⟨1267208, by rfl⟩ : syracuseStep 1689611 = 2534417) B2534417
theorem B1689623 : Blo 1688044 1689623 := bstep (se 1 (by rfl) ⟨1267217, by rfl⟩ : syracuseStep 1689623 = 2534435) B2534435
theorem B1689643 : Blo 1688044 1689643 := bstep (se 1 (by rfl) ⟨1267232, by rfl⟩ : syracuseStep 1689643 = 2534465) B2534465
theorem B1689655 : Blo 1688044 1689655 := bstep (se 1 (by rfl) ⟨1267241, by rfl⟩ : syracuseStep 1689655 = 2534483) B2534483
theorem B6088769 : Blo 1688044 6088769 := bstep (se 2 (by rfl) ⟨2283288, by rfl⟩ : syracuseStep 6088769 = 4566577) B4566577
theorem B2533451 : Blo 1688044 2533451 := bstep (se 1 (by rfl) ⟨1900088, by rfl⟩ : syracuseStep 2533451 = 3800177) B3800177
theorem B1689675 : Blo 1688044 1689675 := bstep (se 1 (by rfl) ⟨1267256, by rfl⟩ : syracuseStep 1689675 = 2534513) B2534513
theorem B8554571 : Blo 1688044 8554571 := bstep (se 1 (by rfl) ⟨6415928, by rfl⟩ : syracuseStep 8554571 = 12831857) B12831857
theorem B2533463 : Blo 1688044 2533463 := bstep (se 1 (by rfl) ⟨1900097, by rfl⟩ : syracuseStep 2533463 = 3800195) B3800195
theorem B1689687 : Blo 1688044 1689687 := bstep (se 1 (by rfl) ⟨1267265, by rfl⟩ : syracuseStep 1689687 = 2534531) B2534531
theorem B1689707 : Blo 1688044 1689707 := bstep (se 1 (by rfl) ⟨1267280, by rfl⟩ : syracuseStep 1689707 = 2534561) B2534561
theorem B1689719 : Blo 1688044 1689719 := bstep (se 1 (by rfl) ⟨1267289, by rfl⟩ : syracuseStep 1689719 = 2534579) B2534579
theorem B1689739 : Blo 1688044 1689739 := bstep (se 1 (by rfl) ⟨1267304, by rfl⟩ : syracuseStep 1689739 = 2534609) B2534609
theorem B1689751 : Blo 1688044 1689751 := bstep (se 1 (by rfl) ⟨1267313, by rfl⟩ : syracuseStep 1689751 = 2534627) B2534627
theorem B2533529 : Blo 1688044 2533529 := bstep (se 2 (by rfl) ⟨950073, by rfl⟩ : syracuseStep 2533529 = 1900147) B1900147
theorem B1689771 : Blo 1688044 1689771 := bstep (se 1 (by rfl) ⟨1267328, by rfl⟩ : syracuseStep 1689771 = 2534657) B2534657
theorem B1689783 : Blo 1688044 1689783 := bstep (se 1 (by rfl) ⟨1267337, by rfl⟩ : syracuseStep 1689783 = 2534675) B2534675
theorem B1689803 : Blo 1688044 1689803 := bstep (se 1 (by rfl) ⟨1267352, by rfl⟩ : syracuseStep 1689803 = 2534705) B2534705
theorem B1689815 : Blo 1688044 1689815 := bstep (se 1 (by rfl) ⟨1267361, by rfl⟩ : syracuseStep 1689815 = 2534723) B2534723
theorem B1804523 : Blo 1688044 1804523 := bstep (se 1 (by rfl) ⟨1353392, by rfl⟩ : syracuseStep 1804523 = 2706785) B2706785
theorem B1689835 : Blo 1688044 1689835 := bstep (se 1 (by rfl) ⟨1267376, by rfl⟩ : syracuseStep 1689835 = 2534753) B2534753
theorem B1689847 : Blo 1688044 1689847 := bstep (se 1 (by rfl) ⟨1267385, by rfl⟩ : syracuseStep 1689847 = 2534771) B2534771
theorem B2533643 : Blo 1688044 2533643 := bstep (se 1 (by rfl) ⟨1900232, by rfl⟩ : syracuseStep 2533643 = 3800465) B3800465
theorem B1689867 : Blo 1688044 1689867 := bstep (se 1 (by rfl) ⟨1267400, by rfl⟩ : syracuseStep 1689867 = 2534801) B2534801
theorem B2533655 : Blo 1688044 2533655 := bstep (se 1 (by rfl) ⟨1900241, by rfl⟩ : syracuseStep 2533655 = 3800483) B3800483
theorem B1689879 : Blo 1688044 1689879 := bstep (se 1 (by rfl) ⟨1267409, by rfl⟩ : syracuseStep 1689879 = 2534819) B2534819
theorem B1689899 : Blo 1688044 1689899 := bstep (se 1 (by rfl) ⟨1267424, by rfl⟩ : syracuseStep 1689899 = 2534849) B2534849
theorem B1689911 : Blo 1688044 1689911 := bstep (se 1 (by rfl) ⟨1267433, by rfl⟩ : syracuseStep 1689911 = 2534867) B2534867
theorem B4057409 : Blo 1688044 4057409 := bstep (se 2 (by rfl) ⟨1521528, by rfl⟩ : syracuseStep 4057409 = 3043057) B3043057
theorem B3606859 : Blo 1688044 3606859 := bstep (se 1 (by rfl) ⟨2705144, by rfl⟩ : syracuseStep 3606859 = 5410289) B5410289
theorem B1689931 : Blo 1688044 1689931 := bstep (se 1 (by rfl) ⟨1267448, by rfl⟩ : syracuseStep 1689931 = 2534897) B2534897
theorem B1689943 : Blo 1688044 1689943 := bstep (se 1 (by rfl) ⟨1267457, by rfl⟩ : syracuseStep 1689943 = 2534915) B2534915
theorem B2533721 : Blo 1688044 2533721 := bstep (se 2 (by rfl) ⟨950145, by rfl⟩ : syracuseStep 2533721 = 1900291) B1900291
theorem B1689963 : Blo 1688044 1689963 := bstep (se 1 (by rfl) ⟨1267472, by rfl⟩ : syracuseStep 1689963 = 2534945) B2534945
theorem B1689975 : Blo 1688044 1689975 := bstep (se 1 (by rfl) ⟨1267481, by rfl⟩ : syracuseStep 1689975 = 2534963) B2534963
theorem B1689995 : Blo 1688044 1689995 := bstep (se 1 (by rfl) ⟨1267496, by rfl⟩ : syracuseStep 1689995 = 2534993) B2534993
theorem B1690007 : Blo 1688044 1690007 := bstep (se 1 (by rfl) ⟨1267505, by rfl⟩ : syracuseStep 1690007 = 2535011) B2535011
theorem B1690027 : Blo 1688044 1690027 := bstep (se 1 (by rfl) ⟨1267520, by rfl⟩ : syracuseStep 1690027 = 2535041) B2535041
theorem B1690039 : Blo 1688044 1690039 := bstep (se 1 (by rfl) ⟨1267529, by rfl⟩ : syracuseStep 1690039 = 2535059) B2535059
theorem B2533835 : Blo 1688044 2533835 := bstep (se 1 (by rfl) ⟨1900376, by rfl⟩ : syracuseStep 2533835 = 3800753) B3800753
theorem B4336075 : Blo 1688044 4336075 := bstep (se 1 (by rfl) ⟨3252056, by rfl⟩ : syracuseStep 4336075 = 6504113) B6504113
theorem B2533847 : Blo 1688044 2533847 := bstep (se 1 (by rfl) ⟨1900385, by rfl⟩ : syracuseStep 2533847 = 3800771) B3800771
theorem B2533913 : Blo 1688044 2533913 := bstep (se 2 (by rfl) ⟨950217, by rfl⟩ : syracuseStep 2533913 = 1900435) B1900435
theorem B5778013 : Blo 1688044 5778013 := bstep (se 3 (by rfl) ⟨1083377, by rfl⟩ : syracuseStep 5778013 = 2166755) B2166755
theorem B9751133 : Blo 1688044 9751133 := bstep (se 3 (by rfl) ⟨1828337, by rfl⟩ : syracuseStep 9751133 = 3656675) B3656675
theorem B3205747 : Blo 1688044 3205747 := bstep (se 1 (by rfl) ⟨2404310, by rfl⟩ : syracuseStep 3205747 = 4808621) B4808621
theorem B2534027 : Blo 1688044 2534027 := bstep (se 1 (by rfl) ⟨1900520, by rfl⟩ : syracuseStep 2534027 = 3801041) B3801041
theorem B2534039 : Blo 1688044 2534039 := bstep (se 1 (by rfl) ⟨1900529, by rfl⟩ : syracuseStep 2534039 = 3801059) B3801059
theorem B2534105 : Blo 1688044 2534105 := bstep (se 2 (by rfl) ⟨950289, by rfl⟩ : syracuseStep 2534105 = 1900579) B1900579
theorem B16239365 : Blo 1688044 16239365 := bstep (se 4 (by rfl) ⟨1522440, by rfl⟩ : syracuseStep 16239365 = 3044881) B3044881
theorem B43862849 : Blo 1688044 43862849 := bstep (se 2 (by rfl) ⟨16448568, by rfl⟩ : syracuseStep 43862849 = 32897137) B32897137
theorem B2534219 : Blo 1688044 2534219 := bstep (se 1 (by rfl) ⟨1900664, by rfl⟩ : syracuseStep 2534219 = 3801329) B3801329
theorem B3205975 : Blo 1688044 3205975 := bstep (se 1 (by rfl) ⟨2404481, by rfl⟩ : syracuseStep 3205975 = 4808963) B4808963
theorem B2534231 : Blo 1688044 2534231 := bstep (se 1 (by rfl) ⟨1900673, by rfl⟩ : syracuseStep 2534231 = 3801347) B3801347
theorem B2534297 : Blo 1688044 2534297 := bstep (se 2 (by rfl) ⟨950361, by rfl⟩ : syracuseStep 2534297 = 1900723) B1900723
theorem B3206081 : Blo 1688044 3206081 := bstep (se 2 (by rfl) ⟨1202280, by rfl⟩ : syracuseStep 3206081 = 2404561) B2404561
theorem B2534411 : Blo 1688044 2534411 := bstep (se 1 (by rfl) ⟨1900808, by rfl⟩ : syracuseStep 2534411 = 3801617) B3801617
theorem B2534423 : Blo 1688044 2534423 := bstep (se 1 (by rfl) ⟨1900817, by rfl⟩ : syracuseStep 2534423 = 3801635) B3801635
theorem B3042379 : Blo 1688044 3042379 := bstep (se 1 (by rfl) ⟨2281784, by rfl⟩ : syracuseStep 3042379 = 4563569) B4563569
theorem B6499403 : Blo 1688044 6499403 := bstep (se 1 (by rfl) ⟨4874552, by rfl⟩ : syracuseStep 6499403 = 9749105) B9749105
theorem B3206233 : Blo 1688044 3206233 := bstep (se 2 (by rfl) ⟨1202337, by rfl⟩ : syracuseStep 3206233 = 2404675) B2404675
theorem B2534489 : Blo 1688044 2534489 := bstep (se 2 (by rfl) ⟨950433, by rfl⟩ : syracuseStep 2534489 = 1900867) B1900867
theorem B7310429 : Blo 1688044 7310429 := bstep (se 3 (by rfl) ⟨1370705, by rfl⟩ : syracuseStep 7310429 = 2741411) B2741411
theorem B8342621 : Blo 1688044 8342621 := bstep (se 3 (by rfl) ⟨1564241, by rfl⟩ : syracuseStep 8342621 = 3128483) B3128483
theorem B7810199 : Blo 1688044 7810199 := bstep (se 1 (by rfl) ⟨5857649, by rfl⟩ : syracuseStep 7810199 = 11715299) B11715299
theorem B2534603 : Blo 1688044 2534603 := bstep (se 1 (by rfl) ⟨1900952, by rfl⟩ : syracuseStep 2534603 = 3801905) B3801905
theorem B2534615 : Blo 1688044 2534615 := bstep (se 1 (by rfl) ⟨1900961, by rfl⟩ : syracuseStep 2534615 = 3801923) B3801923
theorem B4811993 : Blo 1688044 4811993 := bstep (se 2 (by rfl) ⟨1804497, by rfl⟩ : syracuseStep 4811993 = 3608995) B3608995
theorem B6409475 : Blo 1688044 6409475 := bstep (se 1 (by rfl) ⟨4807106, by rfl⟩ : syracuseStep 6409475 = 9614213) B9614213
theorem B6409489 : Blo 1688044 6409489 := bstep (se 2 (by rfl) ⟨2403558, by rfl⟩ : syracuseStep 6409489 = 4807117) B4807117
theorem B2534681 : Blo 1688044 2534681 := bstep (se 2 (by rfl) ⟨950505, by rfl⟩ : syracuseStep 2534681 = 1901011) B1901011
theorem B2534795 : Blo 1688044 2534795 := bstep (se 1 (by rfl) ⟨1901096, by rfl⟩ : syracuseStep 2534795 = 3802193) B3802193
theorem B2534807 : Blo 1688044 2534807 := bstep (se 1 (by rfl) ⟨1901105, by rfl⟩ : syracuseStep 2534807 = 3802211) B3802211
theorem B2534873 : Blo 1688044 2534873 := bstep (se 2 (by rfl) ⟨950577, by rfl⟩ : syracuseStep 2534873 = 1901155) B1901155
theorem B24342029 : Blo 1688044 24342029 := bstep (se 3 (by rfl) ⟨4564130, by rfl⟩ : syracuseStep 24342029 = 9128261) B9128261
theorem B12824081 : Blo 1688044 12824081 := bstep (se 2 (by rfl) ⟨4809030, by rfl⟩ : syracuseStep 12824081 = 9618061) B9618061
theorem B4812311 : Blo 1688044 4812311 := bstep (se 1 (by rfl) ⟨3609233, by rfl⟩ : syracuseStep 4812311 = 7218467) B7218467
theorem B3042841 : Blo 1688044 3042841 := bstep (se 2 (by rfl) ⟨1141065, by rfl⟩ : syracuseStep 3042841 = 2282131) B2282131
theorem B6409793 : Blo 1688044 6409793 := bstep (se 2 (by rfl) ⟨2403672, by rfl⟩ : syracuseStep 6409793 = 4807345) B4807345
theorem B2534987 : Blo 1688044 2534987 := bstep (se 1 (by rfl) ⟨1901240, by rfl⟩ : syracuseStep 2534987 = 3802481) B3802481
theorem B2534999 : Blo 1688044 2534999 := bstep (se 1 (by rfl) ⟨1901249, by rfl⟩ : syracuseStep 2534999 = 3802499) B3802499
theorem B2535065 : Blo 1688044 2535065 := bstep (se 2 (by rfl) ⟨950649, by rfl⟩ : syracuseStep 2535065 = 1901299) B1901299
theorem B3608243 : Blo 1688044 3608243 := bstep (se 1 (by rfl) ⟨2706182, by rfl⟩ : syracuseStep 3608243 = 5412365) B5412365
theorem B3657431 : Blo 1688044 3657431 := bstep (se 1 (by rfl) ⟨2743073, by rfl⟩ : syracuseStep 3657431 = 5486147) B5486147
theorem B10817297 : Blo 1688044 10817297 := bstep (se 2 (by rfl) ⟨4056486, by rfl⟩ : syracuseStep 10817297 = 8112973) B8112973
theorem B3608345 : Blo 1688044 3608345 := bstep (se 2 (by rfl) ⟨1353129, by rfl⟩ : syracuseStep 3608345 = 2706259) B2706259
theorem B5697431 : Blo 1688044 5697431 := bstep (se 1 (by rfl) ⟨4273073, by rfl⟩ : syracuseStep 5697431 = 8546147) B8546147
theorem B7213121 : Blo 1688044 7213121 := bstep (se 2 (by rfl) ⟨2704920, by rfl⟩ : syracuseStep 7213121 = 5409841) B5409841
theorem B28872773 : Blo 1688044 28872773 := bstep (se 4 (by rfl) ⟨2706822, by rfl⟩ : syracuseStep 28872773 = 5413645) B5413645
theorem B3608705 : Blo 1688044 3608705 := bstep (se 2 (by rfl) ⟨1353264, by rfl⟩ : syracuseStep 3608705 = 2706529) B2706529
theorem B2314379 : Blo 1688044 2314379 := bstep (se 1 (by rfl) ⟨1735784, by rfl⟩ : syracuseStep 2314379 = 3471569) B3471569
theorem B5411033 : Blo 1688044 5411033 := bstep (se 2 (by rfl) ⟨2029137, by rfl⟩ : syracuseStep 5411033 = 4058275) B4058275
theorem B6410461 : Blo 1688044 6410461 := bstep (se 3 (by rfl) ⟨1201961, by rfl⟩ : syracuseStep 6410461 = 2403923) B2403923
theorem B3248407 : Blo 1688044 3248407 := bstep (se 1 (by rfl) ⟨2436305, by rfl⟩ : syracuseStep 3248407 = 4872611) B4872611
theorem B5779763 : Blo 1688044 5779763 := bstep (se 1 (by rfl) ⟨4334822, by rfl⟩ : syracuseStep 5779763 = 8669645) B8669645
theorem B3207539 : Blo 1688044 3207539 := bstep (se 1 (by rfl) ⟨2405654, by rfl⟩ : syracuseStep 3207539 = 4811309) B4811309
theorem B8548739 : Blo 1688044 8548739 := bstep (se 1 (by rfl) ⟨6411554, by rfl⟩ : syracuseStep 8548739 = 12823109) B12823109
theorem B5697971 : Blo 1688044 5697971 := bstep (se 1 (by rfl) ⟨4273478, by rfl⟩ : syracuseStep 5697971 = 8546957) B8546957
theorem B3207691 : Blo 1688044 3207691 := bstep (se 1 (by rfl) ⟨2405768, by rfl⟩ : syracuseStep 3207691 = 4811537) B4811537
theorem B12833315 : Blo 1688044 12833315 := bstep (se 1 (by rfl) ⟨9624986, by rfl⟩ : syracuseStep 12833315 = 19249973) B19249973
theorem B5698241 : Blo 1688044 5698241 := bstep (se 2 (by rfl) ⟨2136840, by rfl⟩ : syracuseStep 5698241 = 4273681) B4273681
theorem B2282251 : Blo 1688044 2282251 := bstep (se 1 (by rfl) ⟨1711688, by rfl⟩ : syracuseStep 2282251 = 3423377) B3423377
theorem B11711249 : Blo 1688044 11711249 := bstep (se 2 (by rfl) ⟨4391718, by rfl⟩ : syracuseStep 11711249 = 8783437) B8783437
theorem B24343361 : Blo 1688044 24343361 := bstep (se 2 (by rfl) ⟨9128760, by rfl⟩ : syracuseStep 24343361 = 18257521) B18257521
theorem B3208025 : Blo 1688044 3208025 := bstep (se 2 (by rfl) ⟨1203009, by rfl⟩ : syracuseStep 3208025 = 2406019) B2406019
theorem B3609431 : Blo 1688044 3609431 := bstep (se 1 (by rfl) ⟨2707073, by rfl⟩ : syracuseStep 3609431 = 5414147) B5414147
theorem B3044225 : Blo 1688044 3044225 := bstep (se 2 (by rfl) ⟨1141584, by rfl⟩ : syracuseStep 3044225 = 2283169) B2283169
theorem B14431193 : Blo 1688044 14431193 := bstep (se 2 (by rfl) ⟨5411697, by rfl⟩ : syracuseStep 14431193 = 10823395) B10823395
theorem B20542481 : Blo 1688044 20542481 := bstep (se 2 (by rfl) ⟨7703430, by rfl⟩ : syracuseStep 20542481 = 15406861) B15406861
theorem B4273175 : Blo 1688044 4273175 := bstep (se 1 (by rfl) ⟨3204881, by rfl⟩ : syracuseStep 4273175 = 6409763) B6409763
theorem B5411929 : Blo 1688044 5411929 := bstep (se 2 (by rfl) ⟨2029473, by rfl⟩ : syracuseStep 5411929 = 4058947) B4058947
theorem B3798233 : Blo 1688044 3798233 := bstep (se 2 (by rfl) ⟨1424337, by rfl⟩ : syracuseStep 3798233 = 2848675) B2848675
theorem B5698781 : Blo 1688044 5698781 := bstep (se 3 (by rfl) ⟨1068521, by rfl⟩ : syracuseStep 5698781 = 2137043) B2137043
theorem B3798323 : Blo 1688044 3798323 := bstep (se 1 (by rfl) ⟨2848742, by rfl⟩ : syracuseStep 3798323 = 5697485) B5697485
theorem B3798359 : Blo 1688044 3798359 := bstep (se 1 (by rfl) ⟨2848769, by rfl⟩ : syracuseStep 3798359 = 5697539) B5697539
theorem B24352177 : Blo 1688044 24352177 := bstep (se 2 (by rfl) ⟨9132066, by rfl⟩ : syracuseStep 24352177 = 18264133) B18264133
theorem B5133761 : Blo 1688044 5133761 := bstep (se 2 (by rfl) ⟨1925160, by rfl⟩ : syracuseStep 5133761 = 3850321) B3850321
theorem B4060619 : Blo 1688044 4060619 := bstep (se 1 (by rfl) ⟨3045464, by rfl⟩ : syracuseStep 4060619 = 6090929) B6090929
theorem B6411737 : Blo 1688044 6411737 := bstep (se 2 (by rfl) ⟨2404401, by rfl⟩ : syracuseStep 6411737 = 4808803) B4808803
theorem B3798539 : Blo 1688044 3798539 := bstep (se 1 (by rfl) ⟨2848904, by rfl⟩ : syracuseStep 3798539 = 5697809) B5697809
theorem B16234019 : Blo 1688044 16234019 := bstep (se 1 (by rfl) ⟨12175514, by rfl⟩ : syracuseStep 16234019 = 24351029) B24351029
theorem B3798593 : Blo 1688044 3798593 := bstep (se 2 (by rfl) ⟨1424472, by rfl⟩ : syracuseStep 3798593 = 2848945) B2848945
theorem B6084227 : Blo 1688044 6084227 := bstep (se 1 (by rfl) ⟨4563170, by rfl⟩ : syracuseStep 6084227 = 9126341) B9126341
theorem B4273843 : Blo 1688044 4273843 := bstep (se 1 (by rfl) ⟨3205382, by rfl⟩ : syracuseStep 4273843 = 6410765) B6410765
theorem B5412545 : Blo 1688044 5412545 := bstep (se 2 (by rfl) ⟨2029704, by rfl⟩ : syracuseStep 5412545 = 4059409) B4059409
theorem B9885401 : Blo 1688044 9885401 := bstep (se 2 (by rfl) ⟨3707025, by rfl⟩ : syracuseStep 9885401 = 7414051) B7414051
theorem B3798809 : Blo 1688044 3798809 := bstep (se 2 (by rfl) ⟨1424553, by rfl⟩ : syracuseStep 3798809 = 2849107) B2849107
theorem B4273985 : Blo 1688044 4273985 := bstep (se 2 (by rfl) ⟨1602744, by rfl⟩ : syracuseStep 4273985 = 3205489) B3205489
theorem B2848601 : Blo 1688044 2848601 := bstep (se 2 (by rfl) ⟨1068225, by rfl⟩ : syracuseStep 2848601 = 2136451) B2136451
theorem B3798899 : Blo 1688044 3798899 := bstep (se 1 (by rfl) ⟨2849174, by rfl⟩ : syracuseStep 3798899 = 5698349) B5698349
theorem B3798935 : Blo 1688044 3798935 := bstep (se 1 (by rfl) ⟨2849201, by rfl⟩ : syracuseStep 3798935 = 5698403) B5698403
theorem B6862795 : Blo 1688044 6862795 := bstep (se 1 (by rfl) ⟨5147096, by rfl⟩ : syracuseStep 6862795 = 10294193) B10294193
theorem B2848729 : Blo 1688044 2848729 := bstep (se 2 (by rfl) ⟨1068273, by rfl⟩ : syracuseStep 2848729 = 2136547) B2136547
theorem B3799115 : Blo 1688044 3799115 := bstep (se 1 (by rfl) ⟨2849336, by rfl⟩ : syracuseStep 3799115 = 5698673) B5698673
theorem B3799169 : Blo 1688044 3799169 := bstep (se 2 (by rfl) ⟨1424688, by rfl⟩ : syracuseStep 3799169 = 2849377) B2849377
theorem B5134553 : Blo 1688044 5134553 := bstep (se 2 (by rfl) ⟨1925457, by rfl⟩ : syracuseStep 5134553 = 3850915) B3850915
theorem B3422515 : Blo 1688044 3422515 := bstep (se 1 (by rfl) ⟨2566886, by rfl⟩ : syracuseStep 3422515 = 5133773) B5133773
theorem B1734967 : Blo 1688044 1734967 := bstep (se 1 (by rfl) ⟨1301225, by rfl⟩ : syracuseStep 1734967 = 2602451) B2602451
theorem B5699915 : Blo 1688044 5699915 := bstep (se 1 (by rfl) ⟨4274936, by rfl⟩ : syracuseStep 5699915 = 8549873) B8549873
theorem B3799385 : Blo 1688044 3799385 := bstep (se 2 (by rfl) ⟨1424769, by rfl⟩ : syracuseStep 3799385 = 2849539) B2849539
theorem B3422579 : Blo 1688044 3422579 := bstep (se 1 (by rfl) ⟨2566934, by rfl⟩ : syracuseStep 3422579 = 5133869) B5133869
theorem B3799475 : Blo 1688044 3799475 := bstep (se 1 (by rfl) ⟨2849606, by rfl⟩ : syracuseStep 3799475 = 5699213) B5699213
theorem B5487041 : Blo 1688044 5487041 := bstep (se 2 (by rfl) ⟨2057640, by rfl⟩ : syracuseStep 5487041 = 4115281) B4115281
theorem B3799511 : Blo 1688044 3799511 := bstep (se 1 (by rfl) ⟨2849633, by rfl⟩ : syracuseStep 3799511 = 5699267) B5699267
theorem B7215581 : Blo 1688044 7215581 := bstep (se 3 (by rfl) ⟨1352921, by rfl⟩ : syracuseStep 7215581 = 2705843) B2705843
theorem B4332055 : Blo 1688044 4332055 := bstep (se 1 (by rfl) ⟨3249041, by rfl⟩ : syracuseStep 4332055 = 6498083) B6498083
theorem B2849303 : Blo 1688044 2849303 := bstep (se 1 (by rfl) ⟨2136977, by rfl⟩ : syracuseStep 2849303 = 4273955) B4273955
theorem B5700185 : Blo 1688044 5700185 := bstep (se 2 (by rfl) ⟨2137569, by rfl⟩ : syracuseStep 5700185 = 4275139) B4275139
theorem B17324675 : Blo 1688044 17324675 := bstep (se 1 (by rfl) ⟨12993506, by rfl⟩ : syracuseStep 17324675 = 25987013) B25987013
theorem B3799691 : Blo 1688044 3799691 := bstep (se 1 (by rfl) ⟨2849768, by rfl⟩ : syracuseStep 3799691 = 5699537) B5699537
theorem B2742923 : Blo 1688044 2742923 := bstep (se 1 (by rfl) ⟨2057192, by rfl⟩ : syracuseStep 2742923 = 4114385) B4114385
theorem B2849431 : Blo 1688044 2849431 := bstep (se 1 (by rfl) ⟨2137073, by rfl⟩ : syracuseStep 2849431 = 4274147) B4274147
theorem B3799745 : Blo 1688044 3799745 := bstep (se 2 (by rfl) ⟨1424904, by rfl⟩ : syracuseStep 3799745 = 2849809) B2849809
theorem B1899211 : Blo 1688044 1899211 := bstep (se 1 (by rfl) ⟨1424408, by rfl⟩ : syracuseStep 1899211 = 2848817) B2848817
theorem B6503129 : Blo 1688044 6503129 := bstep (se 2 (by rfl) ⟨2438673, by rfl⟩ : syracuseStep 6503129 = 4877347) B4877347
theorem B1899319 : Blo 1688044 1899319 := bstep (se 1 (by rfl) ⟨1424489, by rfl⟩ : syracuseStep 1899319 = 2848979) B2848979
theorem B3799961 : Blo 1688044 3799961 := bstep (se 2 (by rfl) ⟨1424985, by rfl⟩ : syracuseStep 3799961 = 2849971) B2849971
theorem B1899499 : Blo 1688044 1899499 := bstep (se 1 (by rfl) ⟨1424624, by rfl⟩ : syracuseStep 1899499 = 2849249) B2849249
theorem B3800051 : Blo 1688044 3800051 := bstep (se 1 (by rfl) ⟨2850038, by rfl⟩ : syracuseStep 3800051 = 5700077) B5700077
theorem B2137099 : Blo 1688044 2137099 := bstep (se 1 (by rfl) ⟨1602824, by rfl⟩ : syracuseStep 2137099 = 3205649) B3205649
theorem B3800087 : Blo 1688044 3800087 := bstep (se 1 (by rfl) ⟨2850065, by rfl⟩ : syracuseStep 3800087 = 5700131) B5700131
theorem B4275251 : Blo 1688044 4275251 := bstep (se 1 (by rfl) ⟨3206438, by rfl⟩ : syracuseStep 4275251 = 6412877) B6412877
theorem B6413363 : Blo 1688044 6413363 := bstep (se 1 (by rfl) ⟨4810022, by rfl⟩ : syracuseStep 6413363 = 9620045) B9620045
theorem B4807745 : Blo 1688044 4807745 := bstep (se 2 (by rfl) ⟨1802904, by rfl⟩ : syracuseStep 4807745 = 3605809) B3605809
theorem B6413377 : Blo 1688044 6413377 := bstep (se 2 (by rfl) ⟨2405016, by rfl⟩ : syracuseStep 6413377 = 4810033) B4810033
theorem B1899607 : Blo 1688044 1899607 := bstep (se 1 (by rfl) ⟨1424705, by rfl⟩ : syracuseStep 1899607 = 2849411) B2849411
theorem B3800267 : Blo 1688044 3800267 := bstep (se 1 (by rfl) ⟨2850200, by rfl⟩ : syracuseStep 3800267 = 5700401) B5700401
theorem B3800321 : Blo 1688044 3800321 := bstep (se 2 (by rfl) ⟨1425120, by rfl⟩ : syracuseStep 3800321 = 2850241) B2850241
theorem B1899787 : Blo 1688044 1899787 := bstep (se 1 (by rfl) ⟨1424840, by rfl⟩ : syracuseStep 1899787 = 2849681) B2849681
theorem B2850059 : Blo 1688044 2850059 := bstep (se 1 (by rfl) ⟨2137544, by rfl⟩ : syracuseStep 2850059 = 4275089) B4275089
theorem B2137367 : Blo 1688044 2137367 := bstep (se 1 (by rfl) ⟨1603025, by rfl⟩ : syracuseStep 2137367 = 3206051) B3206051
theorem B5700887 : Blo 1688044 5700887 := bstep (se 1 (by rfl) ⟨4275665, by rfl⟩ : syracuseStep 5700887 = 8551331) B8551331
theorem B12827969 : Blo 1688044 12827969 := bstep (se 2 (by rfl) ⟨4810488, by rfl⟩ : syracuseStep 12827969 = 9620977) B9620977
theorem B1899895 : Blo 1688044 1899895 := bstep (se 1 (by rfl) ⟨1424921, by rfl⟩ : syracuseStep 1899895 = 2849843) B2849843
theorem B2850187 : Blo 1688044 2850187 := bstep (se 1 (by rfl) ⟨2137640, by rfl⟩ : syracuseStep 2850187 = 4275281) B4275281
theorem B3800537 : Blo 1688044 3800537 := bstep (se 2 (by rfl) ⟨1425201, by rfl⟩ : syracuseStep 3800537 = 2850403) B2850403
theorem B2850329 : Blo 1688044 2850329 := bstep (se 2 (by rfl) ⟨1068873, by rfl⟩ : syracuseStep 2850329 = 2137747) B2137747
theorem B1900075 : Blo 1688044 1900075 := bstep (se 1 (by rfl) ⟨1425056, by rfl⟩ : syracuseStep 1900075 = 2850113) B2850113
theorem B3800627 : Blo 1688044 3800627 := bstep (se 1 (by rfl) ⟨2850470, by rfl⟩ : syracuseStep 3800627 = 5700941) B5700941
theorem B4275787 : Blo 1688044 4275787 := bstep (se 1 (by rfl) ⟨3206840, by rfl⟩ : syracuseStep 4275787 = 6413681) B6413681
theorem B3800663 : Blo 1688044 3800663 := bstep (se 1 (by rfl) ⟨2850497, by rfl⟩ : syracuseStep 3800663 = 5700995) B5700995
theorem B1900183 : Blo 1688044 1900183 := bstep (se 1 (by rfl) ⟨1425137, by rfl⟩ : syracuseStep 1900183 = 2850275) B2850275
theorem B2850457 : Blo 1688044 2850457 := bstep (se 2 (by rfl) ⟨1068921, by rfl⟩ : syracuseStep 2850457 = 2137843) B2137843
theorem B4275929 : Blo 1688044 4275929 := bstep (se 2 (by rfl) ⟨1603473, by rfl⟩ : syracuseStep 4275929 = 3206947) B3206947
theorem B3800843 : Blo 1688044 3800843 := bstep (se 1 (by rfl) ⟨2850632, by rfl⟩ : syracuseStep 3800843 = 5701265) B5701265
theorem B5701427 : Blo 1688044 5701427 := bstep (se 1 (by rfl) ⟨4276070, by rfl⟩ : syracuseStep 5701427 = 8552141) B8552141
theorem B3800897 : Blo 1688044 3800897 := bstep (se 2 (by rfl) ⟨1425336, by rfl⟩ : syracuseStep 3800897 = 2850673) B2850673
theorem B1900363 : Blo 1688044 1900363 := bstep (se 1 (by rfl) ⟨1425272, by rfl⟩ : syracuseStep 1900363 = 2850545) B2850545
theorem B1900471 : Blo 1688044 1900471 := bstep (se 1 (by rfl) ⟨1425353, by rfl⟩ : syracuseStep 1900471 = 2850707) B2850707
theorem B2138071 : Blo 1688044 2138071 := bstep (se 1 (by rfl) ⟨1603553, by rfl⟩ : syracuseStep 2138071 = 3207107) B3207107
theorem B5701643 : Blo 1688044 5701643 := bstep (se 1 (by rfl) ⟨4276232, by rfl⟩ : syracuseStep 5701643 = 8552465) B8552465
theorem B4808747 : Blo 1688044 4808747 := bstep (se 1 (by rfl) ⟨3606560, by rfl⟩ : syracuseStep 4808747 = 7213121) B7213121
theorem B3801131 : Blo 1688044 3801131 := bstep (se 1 (by rfl) ⟨2850848, by rfl⟩ : syracuseStep 3801131 = 5701697) B5701697
theorem B15401021 : Blo 1688044 15401021 := bstep (se 3 (by rfl) ⟨2887691, by rfl⟩ : syracuseStep 15401021 = 5775383) B5775383
theorem B5701751 : Blo 1688044 5701751 := bstep (se 1 (by rfl) ⟨4276313, by rfl⟩ : syracuseStep 5701751 = 8552627) B8552627
theorem B1900687 : Blo 1688044 1900687 := bstep (se 1 (by rfl) ⟨1425515, by rfl⟩ : syracuseStep 1900687 = 2851031) B2851031
theorem B3801491 : Blo 1688044 3801491 := bstep (se 1 (by rfl) ⟨2851118, by rfl⟩ : syracuseStep 3801491 = 5702237) B5702237
theorem B4563353 : Blo 1688044 4563353 := bstep (se 2 (by rfl) ⟨1711257, by rfl⟩ : syracuseStep 4563353 = 3422515) B3422515
theorem B4809145 : Blo 1688044 4809145 := bstep (se 2 (by rfl) ⟨1803429, by rfl⟩ : syracuseStep 4809145 = 3606859) B3606859
theorem B3801545 : Blo 1688044 3801545 := bstep (se 2 (by rfl) ⟨1425579, by rfl⟩ : syracuseStep 3801545 = 2851159) B2851159
theorem B73073137 : Blo 1688044 73073137 := bstep (se 2 (by rfl) ⟨27402426, by rfl⟩ : syracuseStep 73073137 = 54804853) B54804853
theorem B1688071 : Blo 1688044 1688071 := bstep (se 1 (by rfl) ⟨1266053, by rfl⟩ : syracuseStep 1688071 = 2532107) B2532107
theorem B7807499 : Blo 1688044 7807499 := bstep (se 1 (by rfl) ⟨5855624, by rfl⟩ : syracuseStep 7807499 = 11711249) B11711249
theorem B1688079 : Blo 1688044 1688079 := bstep (se 1 (by rfl) ⟨1266059, by rfl⟩ : syracuseStep 1688079 = 2532119) B2532119
theorem B16228907 : Blo 1688044 16228907 := bstep (se 1 (by rfl) ⟨12171680, by rfl⟩ : syracuseStep 16228907 = 24343361) B24343361
theorem B1688123 : Blo 1688044 1688123 := bstep (se 1 (by rfl) ⟨1266092, by rfl⟩ : syracuseStep 1688123 = 2532185) B2532185
theorem B19235393 : Blo 1688044 19235393 := bstep (se 2 (by rfl) ⟨7213272, by rfl⟩ : syracuseStep 19235393 = 14426545) B14426545
theorem B1688199 : Blo 1688044 1688199 := bstep (se 1 (by rfl) ⟨1266149, by rfl⟩ : syracuseStep 1688199 = 2532299) B2532299
theorem B4276871 : Blo 1688044 4276871 := bstep (se 1 (by rfl) ⟨3207653, by rfl⟩ : syracuseStep 4276871 = 6415307) B6415307
theorem B2851463 : Blo 1688044 2851463 := bstep (se 1 (by rfl) ⟨2138597, by rfl⟩ : syracuseStep 2851463 = 4277195) B4277195
theorem B1901191 : Blo 1688044 1901191 := bstep (se 1 (by rfl) ⟨1425893, by rfl⟩ : syracuseStep 1901191 = 2851787) B2851787
theorem B1688207 : Blo 1688044 1688207 := bstep (se 1 (by rfl) ⟨1266155, by rfl⟩ : syracuseStep 1688207 = 2532311) B2532311
theorem B4276921 : Blo 1688044 4276921 := bstep (se 2 (by rfl) ⟨1603845, by rfl⟩ : syracuseStep 4276921 = 3207691) B3207691
theorem B1688251 : Blo 1688044 1688251 := bstep (se 1 (by rfl) ⟨1266188, by rfl⟩ : syracuseStep 1688251 = 2532377) B2532377
theorem B5776073 : Blo 1688044 5776073 := bstep (se 2 (by rfl) ⟨2166027, by rfl⟩ : syracuseStep 5776073 = 4332055) B4332055
theorem B5702345 : Blo 1688044 5702345 := bstep (se 2 (by rfl) ⟨2138379, by rfl⟩ : syracuseStep 5702345 = 4276759) B4276759
theorem B1688327 : Blo 1688044 1688327 := bstep (se 1 (by rfl) ⟨1266245, by rfl⟩ : syracuseStep 1688327 = 2532491) B2532491
theorem B1688335 : Blo 1688044 1688335 := bstep (se 1 (by rfl) ⟨1266251, by rfl⟩ : syracuseStep 1688335 = 2532503) B2532503
theorem B19776307 : Blo 1688044 19776307 := bstep (se 1 (by rfl) ⟨14832230, by rfl⟩ : syracuseStep 19776307 = 29664461) B29664461
theorem B2532155 : Blo 1688044 2532155 := bstep (se 1 (by rfl) ⟨1899116, by rfl⟩ : syracuseStep 2532155 = 3798233) B3798233
theorem B1688379 : Blo 1688044 1688379 := bstep (se 1 (by rfl) ⟨1266284, by rfl⟩ : syracuseStep 1688379 = 2532569) B2532569
theorem B8553275 : Blo 1688044 8553275 := bstep (se 1 (by rfl) ⟨6414956, by rfl⟩ : syracuseStep 8553275 = 12829913) B12829913
theorem B2532215 : Blo 1688044 2532215 := bstep (se 1 (by rfl) ⟨1899161, by rfl⟩ : syracuseStep 2532215 = 3798323) B3798323
theorem B1688455 : Blo 1688044 1688455 := bstep (se 1 (by rfl) ⟨1266341, by rfl⟩ : syracuseStep 1688455 = 2532683) B2532683
theorem B2532239 : Blo 1688044 2532239 := bstep (se 1 (by rfl) ⟨1899179, by rfl⟩ : syracuseStep 2532239 = 3798359) B3798359
theorem B1688463 : Blo 1688044 1688463 := bstep (se 1 (by rfl) ⟨1266347, by rfl⟩ : syracuseStep 1688463 = 2532695) B2532695
theorem B2532281 : Blo 1688044 2532281 := bstep (se 2 (by rfl) ⟨949605, by rfl⟩ : syracuseStep 2532281 = 1899211) B1899211
theorem B1688507 : Blo 1688044 1688507 := bstep (se 1 (by rfl) ⟨1266380, by rfl⟩ : syracuseStep 1688507 = 2532761) B2532761
theorem B8553437 : Blo 1688044 8553437 := bstep (se 3 (by rfl) ⟨1603769, by rfl⟩ : syracuseStep 8553437 = 3207539) B3207539
theorem B2532359 : Blo 1688044 2532359 := bstep (se 1 (by rfl) ⟨1899269, by rfl⟩ : syracuseStep 2532359 = 3798539) B3798539
theorem B1688583 : Blo 1688044 1688583 := bstep (se 1 (by rfl) ⟨1266437, by rfl⟩ : syracuseStep 1688583 = 2532875) B2532875
theorem B1688591 : Blo 1688044 1688591 := bstep (se 1 (by rfl) ⟨1266443, by rfl⟩ : syracuseStep 1688591 = 2532887) B2532887
theorem B10822679 : Blo 1688044 10822679 := bstep (se 1 (by rfl) ⟨8117009, by rfl⟩ : syracuseStep 10822679 = 16234019) B16234019
theorem B2532395 : Blo 1688044 2532395 := bstep (se 1 (by rfl) ⟨1899296, by rfl⟩ : syracuseStep 2532395 = 3798593) B3798593
theorem B1688635 : Blo 1688044 1688635 := bstep (se 1 (by rfl) ⟨1266476, by rfl⟩ : syracuseStep 1688635 = 2532953) B2532953
theorem B2532425 : Blo 1688044 2532425 := bstep (se 2 (by rfl) ⟨949659, by rfl⟩ : syracuseStep 2532425 = 1899319) B1899319
theorem B4056151 : Blo 1688044 4056151 := bstep (se 1 (by rfl) ⟨3042113, by rfl⟩ : syracuseStep 4056151 = 6084227) B6084227
theorem B35161219 : Blo 1688044 35161219 := bstep (se 1 (by rfl) ⟨26370914, by rfl⟩ : syracuseStep 35161219 = 52741829) B52741829
theorem B1688711 : Blo 1688044 1688711 := bstep (se 1 (by rfl) ⟨1266533, by rfl⟩ : syracuseStep 1688711 = 2533067) B2533067
theorem B3802247 : Blo 1688044 3802247 := bstep (se 1 (by rfl) ⟨2851685, by rfl⟩ : syracuseStep 3802247 = 5703371) B5703371
theorem B1688719 : Blo 1688044 1688719 := bstep (se 1 (by rfl) ⟨1266539, by rfl⟩ : syracuseStep 1688719 = 2533079) B2533079
theorem B14632109 : Blo 1688044 14632109 := bstep (se 3 (by rfl) ⟨2743520, by rfl⟩ : syracuseStep 14632109 = 5487041) B5487041
theorem B2532539 : Blo 1688044 2532539 := bstep (se 1 (by rfl) ⟨1899404, by rfl⟩ : syracuseStep 2532539 = 3798809) B3798809
theorem B1688763 : Blo 1688044 1688763 := bstep (se 1 (by rfl) ⟨1266572, by rfl⟩ : syracuseStep 1688763 = 2533145) B2533145
theorem B2532599 : Blo 1688044 2532599 := bstep (se 1 (by rfl) ⟨1899449, by rfl⟩ : syracuseStep 2532599 = 3798899) B3798899
theorem B1688839 : Blo 1688044 1688839 := bstep (se 1 (by rfl) ⟨1266629, by rfl⟩ : syracuseStep 1688839 = 2533259) B2533259
theorem B2532623 : Blo 1688044 2532623 := bstep (se 1 (by rfl) ⟨1899467, by rfl⟩ : syracuseStep 2532623 = 3798935) B3798935
theorem B1688847 : Blo 1688044 1688847 := bstep (se 1 (by rfl) ⟨1266635, by rfl⟩ : syracuseStep 1688847 = 2533271) B2533271
theorem B4277519 : Blo 1688044 4277519 := bstep (se 1 (by rfl) ⟨3208139, by rfl⟩ : syracuseStep 4277519 = 6416279) B6416279
theorem B8553761 : Blo 1688044 8553761 := bstep (se 2 (by rfl) ⟨3207660, by rfl⟩ : syracuseStep 8553761 = 6415321) B6415321
theorem B2532665 : Blo 1688044 2532665 := bstep (se 2 (by rfl) ⟨949749, by rfl⟩ : syracuseStep 2532665 = 1899499) B1899499
theorem B5408059 : Blo 1688044 5408059 := bstep (se 1 (by rfl) ⟨4056044, by rfl⟩ : syracuseStep 5408059 = 8112089) B8112089
theorem B1688891 : Blo 1688044 1688891 := bstep (se 1 (by rfl) ⟨1266668, by rfl⟩ : syracuseStep 1688891 = 2533337) B2533337
theorem B3802427 : Blo 1688044 3802427 := bstep (se 1 (by rfl) ⟨2851820, by rfl⟩ : syracuseStep 3802427 = 5703641) B5703641
theorem B2532743 : Blo 1688044 2532743 := bstep (se 1 (by rfl) ⟨1899557, by rfl⟩ : syracuseStep 2532743 = 3799115) B3799115
theorem B1688967 : Blo 1688044 1688967 := bstep (se 1 (by rfl) ⟨1266725, by rfl⟩ : syracuseStep 1688967 = 2533451) B2533451
theorem B5703047 : Blo 1688044 5703047 := bstep (se 1 (by rfl) ⟨4277285, by rfl⟩ : syracuseStep 5703047 = 8554571) B8554571
theorem B1688975 : Blo 1688044 1688975 := bstep (se 1 (by rfl) ⟨1266731, by rfl⟩ : syracuseStep 1688975 = 2533463) B2533463
theorem B2532779 : Blo 1688044 2532779 := bstep (se 1 (by rfl) ⟨1899584, by rfl⟩ : syracuseStep 2532779 = 3799169) B3799169
theorem B4392377 : Blo 1688044 4392377 := bstep (se 2 (by rfl) ⟨1647141, by rfl⟩ : syracuseStep 4392377 = 3294283) B3294283
theorem B1689019 : Blo 1688044 1689019 := bstep (se 1 (by rfl) ⟨1266764, by rfl⟩ : syracuseStep 1689019 = 2533529) B2533529
theorem B3802553 : Blo 1688044 3802553 := bstep (se 2 (by rfl) ⟨1425957, by rfl⟩ : syracuseStep 3802553 = 2851915) B2851915
theorem B2532809 : Blo 1688044 2532809 := bstep (se 2 (by rfl) ⟨949803, by rfl⟩ : syracuseStep 2532809 = 1899607) B1899607
theorem B15402449 : Blo 1688044 15402449 := bstep (se 2 (by rfl) ⟨5775918, by rfl⟩ : syracuseStep 15402449 = 11551837) B11551837
theorem B1689095 : Blo 1688044 1689095 := bstep (se 1 (by rfl) ⟨1266821, by rfl⟩ : syracuseStep 1689095 = 2533643) B2533643
theorem B1689103 : Blo 1688044 1689103 := bstep (se 1 (by rfl) ⟨1266827, by rfl⟩ : syracuseStep 1689103 = 2533655) B2533655
theorem B2532923 : Blo 1688044 2532923 := bstep (se 1 (by rfl) ⟨1899692, by rfl⟩ : syracuseStep 2532923 = 3799385) B3799385
theorem B1689147 : Blo 1688044 1689147 := bstep (se 1 (by rfl) ⟨1266860, by rfl⟩ : syracuseStep 1689147 = 2533721) B2533721
theorem B2532983 : Blo 1688044 2532983 := bstep (se 1 (by rfl) ⟨1899737, by rfl⟩ : syracuseStep 2532983 = 3799475) B3799475
theorem B1689223 : Blo 1688044 1689223 := bstep (se 1 (by rfl) ⟨1266917, by rfl⟩ : syracuseStep 1689223 = 2533835) B2533835
theorem B2533007 : Blo 1688044 2533007 := bstep (se 1 (by rfl) ⟨1899755, by rfl⟩ : syracuseStep 2533007 = 3799511) B3799511
theorem B1689231 : Blo 1688044 1689231 := bstep (se 1 (by rfl) ⟨1266923, by rfl⟩ : syracuseStep 1689231 = 2533847) B2533847
theorem B4810387 : Blo 1688044 4810387 := bstep (se 1 (by rfl) ⟨3607790, by rfl⟩ : syracuseStep 4810387 = 7215581) B7215581
theorem B2533049 : Blo 1688044 2533049 := bstep (se 2 (by rfl) ⟨949893, by rfl⟩ : syracuseStep 2533049 = 1899787) B1899787
theorem B1689275 : Blo 1688044 1689275 := bstep (se 1 (by rfl) ⟨1266956, by rfl⟩ : syracuseStep 1689275 = 2533913) B2533913
theorem B8545985 : Blo 1688044 8545985 := bstep (se 2 (by rfl) ⟨3204744, by rfl⟩ : syracuseStep 8545985 = 6409489) B6409489
theorem B5703425 : Blo 1688044 5703425 := bstep (se 2 (by rfl) ⟨2138784, by rfl⟩ : syracuseStep 5703425 = 4277569) B4277569
theorem B2533127 : Blo 1688044 2533127 := bstep (se 1 (by rfl) ⟨1899845, by rfl⟩ : syracuseStep 2533127 = 3799691) B3799691
theorem B1689351 : Blo 1688044 1689351 := bstep (se 1 (by rfl) ⟨1267013, by rfl⟩ : syracuseStep 1689351 = 2534027) B2534027
theorem B1689359 : Blo 1688044 1689359 := bstep (se 1 (by rfl) ⟨1267019, by rfl⟩ : syracuseStep 1689359 = 2534039) B2534039
theorem B2533163 : Blo 1688044 2533163 := bstep (se 1 (by rfl) ⟨1899872, by rfl⟩ : syracuseStep 2533163 = 3799745) B3799745
theorem B1689403 : Blo 1688044 1689403 := bstep (se 1 (by rfl) ⟨1267052, by rfl⟩ : syracuseStep 1689403 = 2534105) B2534105
theorem B4335419 : Blo 1688044 4335419 := bstep (se 1 (by rfl) ⟨3251564, by rfl⟩ : syracuseStep 4335419 = 6503129) B6503129
theorem B2533193 : Blo 1688044 2533193 := bstep (se 2 (by rfl) ⟨949947, by rfl⟩ : syracuseStep 2533193 = 1899895) B1899895
theorem B1689479 : Blo 1688044 1689479 := bstep (se 1 (by rfl) ⟨1267109, by rfl⟩ : syracuseStep 1689479 = 2534219) B2534219
theorem B1689487 : Blo 1688044 1689487 := bstep (se 1 (by rfl) ⟨1267115, by rfl⟩ : syracuseStep 1689487 = 2534231) B2534231
theorem B2533307 : Blo 1688044 2533307 := bstep (se 1 (by rfl) ⟨1899980, by rfl⟩ : syracuseStep 2533307 = 3799961) B3799961
theorem B1689531 : Blo 1688044 1689531 := bstep (se 1 (by rfl) ⟨1267148, by rfl⟩ : syracuseStep 1689531 = 2534297) B2534297
theorem B2533367 : Blo 1688044 2533367 := bstep (se 1 (by rfl) ⟨1900025, by rfl⟩ : syracuseStep 2533367 = 3800051) B3800051
theorem B1689607 : Blo 1688044 1689607 := bstep (se 1 (by rfl) ⟨1267205, by rfl⟩ : syracuseStep 1689607 = 2534411) B2534411
theorem B2533391 : Blo 1688044 2533391 := bstep (se 1 (by rfl) ⟨1900043, by rfl⟩ : syracuseStep 2533391 = 3800087) B3800087
theorem B1689615 : Blo 1688044 1689615 := bstep (se 1 (by rfl) ⟨1267211, by rfl⟩ : syracuseStep 1689615 = 2534423) B2534423
theorem B4057121 : Blo 1688044 4057121 := bstep (se 2 (by rfl) ⟨1521420, by rfl⟩ : syracuseStep 4057121 = 3042841) B3042841
theorem B3205163 : Blo 1688044 3205163 := bstep (se 1 (by rfl) ⟨2403872, by rfl⟩ : syracuseStep 3205163 = 4807745) B4807745
theorem B2533433 : Blo 1688044 2533433 := bstep (se 2 (by rfl) ⟨950037, by rfl⟩ : syracuseStep 2533433 = 1900075) B1900075
theorem B1689659 : Blo 1688044 1689659 := bstep (se 1 (by rfl) ⟨1267244, by rfl⟩ : syracuseStep 1689659 = 2534489) B2534489
theorem B19499125 : Blo 1688044 19499125 := bstep (se 5 (by rfl) ⟨914021, by rfl⟩ : syracuseStep 19499125 = 1828043) B1828043
theorem B2533511 : Blo 1688044 2533511 := bstep (se 1 (by rfl) ⟨1900133, by rfl⟩ : syracuseStep 2533511 = 3800267) B3800267
theorem B1689735 : Blo 1688044 1689735 := bstep (se 1 (by rfl) ⟨1267301, by rfl⟩ : syracuseStep 1689735 = 2534603) B2534603
theorem B1689743 : Blo 1688044 1689743 := bstep (se 1 (by rfl) ⟨1267307, by rfl⟩ : syracuseStep 1689743 = 2534615) B2534615
theorem B2533547 : Blo 1688044 2533547 := bstep (se 1 (by rfl) ⟨1900160, by rfl⟩ : syracuseStep 2533547 = 3800321) B3800321
theorem B1689787 : Blo 1688044 1689787 := bstep (se 1 (by rfl) ⟨1267340, by rfl⟩ : syracuseStep 1689787 = 2534681) B2534681
theorem B2533577 : Blo 1688044 2533577 := bstep (se 2 (by rfl) ⟨950091, by rfl⟩ : syracuseStep 2533577 = 1900183) B1900183
theorem B8554733 : Blo 1688044 8554733 := bstep (se 3 (by rfl) ⟨1604012, by rfl⟩ : syracuseStep 8554733 = 3208025) B3208025
theorem B1689863 : Blo 1688044 1689863 := bstep (se 1 (by rfl) ⟨1267397, by rfl⟩ : syracuseStep 1689863 = 2534795) B2534795
theorem B1689871 : Blo 1688044 1689871 := bstep (se 1 (by rfl) ⟨1267403, by rfl⟩ : syracuseStep 1689871 = 2534807) B2534807
theorem B2533691 : Blo 1688044 2533691 := bstep (se 1 (by rfl) ⟨1900268, by rfl⟩ : syracuseStep 2533691 = 3800537) B3800537
theorem B1689915 : Blo 1688044 1689915 := bstep (se 1 (by rfl) ⟨1267436, by rfl⟩ : syracuseStep 1689915 = 2534873) B2534873
theorem B2533751 : Blo 1688044 2533751 := bstep (se 1 (by rfl) ⟨1900313, by rfl⟩ : syracuseStep 2533751 = 3800627) B3800627
theorem B1689991 : Blo 1688044 1689991 := bstep (se 1 (by rfl) ⟨1267493, by rfl⟩ : syracuseStep 1689991 = 2534987) B2534987
theorem B2533775 : Blo 1688044 2533775 := bstep (se 1 (by rfl) ⟨1900331, by rfl⟩ : syracuseStep 2533775 = 3800663) B3800663
theorem B1689999 : Blo 1688044 1689999 := bstep (se 1 (by rfl) ⟨1267499, by rfl⟩ : syracuseStep 1689999 = 2534999) B2534999
theorem B2533817 : Blo 1688044 2533817 := bstep (se 2 (by rfl) ⟨950181, by rfl⟩ : syracuseStep 2533817 = 1900363) B1900363
theorem B1690043 : Blo 1688044 1690043 := bstep (se 1 (by rfl) ⟨1267532, by rfl⟩ : syracuseStep 1690043 = 2535065) B2535065
theorem B2533895 : Blo 1688044 2533895 := bstep (se 1 (by rfl) ⟨1900421, by rfl⟩ : syracuseStep 2533895 = 3800843) B3800843
theorem B7211531 : Blo 1688044 7211531 := bstep (se 1 (by rfl) ⟨5408648, by rfl⟩ : syracuseStep 7211531 = 10817297) B10817297
theorem B2533931 : Blo 1688044 2533931 := bstep (se 1 (by rfl) ⟨1900448, by rfl⟩ : syracuseStep 2533931 = 3800897) B3800897
theorem B2533961 : Blo 1688044 2533961 := bstep (se 2 (by rfl) ⟨950235, by rfl⟩ : syracuseStep 2533961 = 1900471) B1900471
theorem B2534075 : Blo 1688044 2534075 := bstep (se 1 (by rfl) ⟨1900556, by rfl⟩ : syracuseStep 2534075 = 3801113) B3801113
theorem B5778121 : Blo 1688044 5778121 := bstep (se 2 (by rfl) ⟨2166795, by rfl⟩ : syracuseStep 5778121 = 4333591) B4333591
theorem B2534135 : Blo 1688044 2534135 := bstep (se 1 (by rfl) ⟨1900601, by rfl⟩ : syracuseStep 2534135 = 3801203) B3801203
theorem B2534159 : Blo 1688044 2534159 := bstep (se 1 (by rfl) ⟨1900619, by rfl⟩ : syracuseStep 2534159 = 3801239) B3801239
theorem B29240099 : Blo 1688044 29240099 := bstep (se 1 (by rfl) ⟨21930074, by rfl⟩ : syracuseStep 29240099 = 43860149) B43860149
theorem B2534201 : Blo 1688044 2534201 := bstep (se 2 (by rfl) ⟨950325, by rfl⟩ : syracuseStep 2534201 = 1900651) B1900651
theorem B3607355 : Blo 1688044 3607355 := bstep (se 1 (by rfl) ⟨2705516, by rfl⟩ : syracuseStep 3607355 = 5411033) B5411033
theorem B3853175 : Blo 1688044 3853175 := bstep (se 1 (by rfl) ⟨2889881, by rfl⟩ : syracuseStep 3853175 = 5779763) B5779763
theorem B2534279 : Blo 1688044 2534279 := bstep (se 1 (by rfl) ⟨1900709, by rfl⟩ : syracuseStep 2534279 = 3801419) B3801419
theorem B2534315 : Blo 1688044 2534315 := bstep (se 1 (by rfl) ⟨1900736, by rfl⟩ : syracuseStep 2534315 = 3801473) B3801473
theorem B2534345 : Blo 1688044 2534345 := bstep (se 2 (by rfl) ⟨950379, by rfl⟩ : syracuseStep 2534345 = 1900759) B1900759
theorem B8547281 : Blo 1688044 8547281 := bstep (se 2 (by rfl) ⟨3205230, by rfl⟩ : syracuseStep 8547281 = 6410461) B6410461
theorem B8555543 : Blo 1688044 8555543 := bstep (se 1 (by rfl) ⟨6416657, by rfl⟩ : syracuseStep 8555543 = 12833315) B12833315
theorem B6171677 : Blo 1688044 6171677 := bstep (se 3 (by rfl) ⟨1157189, by rfl⟩ : syracuseStep 6171677 = 2314379) B2314379
theorem B2540842019 : Blo 1688044 2540842019 := bstep (se 1 (by rfl) ⟨1905631514, by rfl⟩ : syracuseStep 2540842019 = 3811263029) B3811263029
theorem B2567227 : Blo 1688044 2567227 := bstep (se 1 (by rfl) ⟨1925420, by rfl⟩ : syracuseStep 2567227 = 3850841) B3850841
theorem B2534459 : Blo 1688044 2534459 := bstep (se 1 (by rfl) ⟨1900844, by rfl⟩ : syracuseStep 2534459 = 3801689) B3801689
theorem B2313289 : Blo 1688044 2313289 := bstep (se 2 (by rfl) ⟨867483, by rfl⟩ : syracuseStep 2313289 = 1734967) B1734967
theorem B2534519 : Blo 1688044 2534519 := bstep (se 1 (by rfl) ⟨1900889, by rfl⟩ : syracuseStep 2534519 = 3801779) B3801779
theorem B3206279 : Blo 1688044 3206279 := bstep (se 1 (by rfl) ⟨2404709, by rfl⟩ : syracuseStep 3206279 = 4809419) B4809419
theorem B2534543 : Blo 1688044 2534543 := bstep (se 1 (by rfl) ⟨1900907, by rfl⟩ : syracuseStep 2534543 = 3801815) B3801815
theorem B2534585 : Blo 1688044 2534585 := bstep (se 2 (by rfl) ⟨950469, by rfl⟩ : syracuseStep 2534585 = 1900939) B1900939
theorem B2534663 : Blo 1688044 2534663 := bstep (se 1 (by rfl) ⟨1900997, by rfl⟩ : syracuseStep 2534663 = 3801995) B3801995
theorem B4812061 : Blo 1688044 4812061 := bstep (se 3 (by rfl) ⟨902261, by rfl⟩ : syracuseStep 4812061 = 1804523) B1804523
theorem B2534699 : Blo 1688044 2534699 := bstep (se 1 (by rfl) ⟨1901024, by rfl⟩ : syracuseStep 2534699 = 3802049) B3802049
theorem B9620795 : Blo 1688044 9620795 := bstep (se 1 (by rfl) ⟨7215596, by rfl⟩ : syracuseStep 9620795 = 14431193) B14431193
theorem B2534729 : Blo 1688044 2534729 := bstep (se 2 (by rfl) ⟨950523, by rfl⟩ : syracuseStep 2534729 = 1901047) B1901047
theorem B4812119 : Blo 1688044 4812119 := bstep (se 1 (by rfl) ⟨3609089, by rfl⟩ : syracuseStep 4812119 = 7218179) B7218179
theorem B5205383 : Blo 1688044 5205383 := bstep (se 1 (by rfl) ⟨3904037, by rfl⟩ : syracuseStep 5205383 = 7808075) B7808075
theorem B2534843 : Blo 1688044 2534843 := bstep (se 1 (by rfl) ⟨1901132, by rfl⟩ : syracuseStep 2534843 = 3802265) B3802265
theorem B7704017 : Blo 1688044 7704017 := bstep (se 2 (by rfl) ⟨2889006, by rfl⟩ : syracuseStep 7704017 = 5778013) B5778013
theorem B2534903 : Blo 1688044 2534903 := bstep (se 1 (by rfl) ⟨1901177, by rfl⟩ : syracuseStep 2534903 = 3802355) B3802355
theorem B2534927 : Blo 1688044 2534927 := bstep (se 1 (by rfl) ⟨1901195, by rfl⟩ : syracuseStep 2534927 = 3802391) B3802391
theorem B2534969 : Blo 1688044 2534969 := bstep (se 2 (by rfl) ⟨950613, by rfl⟩ : syracuseStep 2534969 = 1901227) B1901227
theorem B2707079 : Blo 1688044 2707079 := bstep (se 1 (by rfl) ⟨2030309, by rfl⟩ : syracuseStep 2707079 = 4060619) B4060619
theorem B2535047 : Blo 1688044 2535047 := bstep (se 1 (by rfl) ⟨1901285, by rfl⟩ : syracuseStep 2535047 = 3802571) B3802571
theorem B3206803 : Blo 1688044 3206803 := bstep (se 1 (by rfl) ⟨2405102, by rfl⟩ : syracuseStep 3206803 = 4810205) B4810205
theorem B3043001 : Blo 1688044 3043001 := bstep (se 2 (by rfl) ⟨1141125, by rfl⟩ : syracuseStep 3043001 = 2282251) B2282251
theorem B3608363 : Blo 1688044 3608363 := bstep (se 1 (by rfl) ⟨2706272, by rfl⟩ : syracuseStep 3608363 = 5412545) B5412545
theorem B6590267 : Blo 1688044 6590267 := bstep (se 1 (by rfl) ⟨4942700, by rfl⟩ : syracuseStep 6590267 = 9885401) B9885401
theorem B36507509 : Blo 1688044 36507509 := bstep (se 5 (by rfl) ⟨1711289, by rfl⟩ : syracuseStep 36507509 = 3422579) B3422579
theorem B4059179 : Blo 1688044 4059179 := bstep (se 1 (by rfl) ⟨3044384, by rfl⟩ : syracuseStep 4059179 = 6088769) B6088769
theorem B12832829 : Blo 1688044 12832829 := bstep (se 3 (by rfl) ⟨2406155, by rfl⟩ : syracuseStep 12832829 = 4812311) B4812311
theorem B6500755 : Blo 1688044 6500755 := bstep (se 1 (by rfl) ⟨4875566, by rfl⟩ : syracuseStep 6500755 = 9751133) B9751133
theorem B12825053 : Blo 1688044 12825053 := bstep (se 3 (by rfl) ⟨2404697, by rfl⟩ : syracuseStep 12825053 = 4809395) B4809395
theorem B10826243 : Blo 1688044 10826243 := bstep (se 1 (by rfl) ⟨8119682, by rfl⟩ : syracuseStep 10826243 = 16239365) B16239365
theorem B29241899 : Blo 1688044 29241899 := bstep (se 1 (by rfl) ⟨21931424, by rfl⟩ : syracuseStep 29241899 = 43862849) B43862849
theorem B9753149 : Blo 1688044 9753149 := bstep (se 3 (by rfl) ⟨1828715, by rfl⟩ : syracuseStep 9753149 = 3657431) B3657431
theorem B32469569 : Blo 1688044 32469569 := bstep (se 2 (by rfl) ⟨12176088, by rfl⟩ : syracuseStep 32469569 = 24352177) B24352177
theorem B2404937 : Blo 1688044 2404937 := bstep (se 2 (by rfl) ⟨901851, by rfl⟩ : syracuseStep 2404937 = 1803703) B1803703
theorem B7213805 : Blo 1688044 7213805 := bstep (se 3 (by rfl) ⟨1352588, by rfl⟩ : syracuseStep 7213805 = 2705177) B2705177
theorem B9622253 : Blo 1688044 9622253 := bstep (se 3 (by rfl) ⟨1804172, by rfl⟩ : syracuseStep 9622253 = 3608345) B3608345
theorem B5206799 : Blo 1688044 5206799 := bstep (se 1 (by rfl) ⟨3905099, by rfl⟩ : syracuseStep 5206799 = 7810199) B7810199
theorem B3207995 : Blo 1688044 3207995 := bstep (se 1 (by rfl) ⟨2405996, by rfl⟩ : syracuseStep 3207995 = 4811993) B4811993
theorem B4272983 : Blo 1688044 4272983 := bstep (se 1 (by rfl) ⟨3204737, by rfl⟩ : syracuseStep 4272983 = 6409475) B6409475
theorem B5698457 : Blo 1688044 5698457 := bstep (se 2 (by rfl) ⟨2136921, by rfl⟩ : syracuseStep 5698457 = 4273843) B4273843
theorem B8549387 : Blo 1688044 8549387 := bstep (se 1 (by rfl) ⟨6412040, by rfl⟩ : syracuseStep 8549387 = 12824081) B12824081
theorem B4273195 : Blo 1688044 4273195 := bstep (se 1 (by rfl) ⟨3204896, by rfl⟩ : syracuseStep 4273195 = 6409793) B6409793
theorem B2405495 : Blo 1688044 2405495 := bstep (se 1 (by rfl) ⟨1804121, by rfl⟩ : syracuseStep 2405495 = 3608243) B3608243
theorem B8549549 : Blo 1688044 8549549 := bstep (se 3 (by rfl) ⟨1603040, by rfl⟩ : syracuseStep 8549549 = 3206081) B3206081
theorem B4273337 : Blo 1688044 4273337 := bstep (se 2 (by rfl) ⟨1602501, by rfl⟩ : syracuseStep 4273337 = 3205003) B3205003
theorem B3798287 : Blo 1688044 3798287 := bstep (se 1 (by rfl) ⟨2848715, by rfl⟩ : syracuseStep 3798287 = 5697431) B5697431
theorem B3798305 : Blo 1688044 3798305 := bstep (se 2 (by rfl) ⟨1424364, by rfl⟩ : syracuseStep 3798305 = 2848729) B2848729
theorem B19248515 : Blo 1688044 19248515 := bstep (se 1 (by rfl) ⟨14436386, by rfl⟩ : syracuseStep 19248515 = 28872773) B28872773
theorem B12178835 : Blo 1688044 12178835 := bstep (se 1 (by rfl) ⟨9134126, by rfl⟩ : syracuseStep 12178835 = 18268253) B18268253
theorem B2405803 : Blo 1688044 2405803 := bstep (se 1 (by rfl) ⟨1804352, by rfl⟩ : syracuseStep 2405803 = 3608705) B3608705
theorem B5699159 : Blo 1688044 5699159 := bstep (se 1 (by rfl) ⟨4274369, by rfl⟩ : syracuseStep 5699159 = 8548739) B8548739
theorem B3798647 : Blo 1688044 3798647 := bstep (se 1 (by rfl) ⟨2848985, by rfl⟩ : syracuseStep 3798647 = 5697971) B5697971
theorem B16226021 : Blo 1688044 16226021 := bstep (se 4 (by rfl) ⟨1521189, by rfl⟩ : syracuseStep 16226021 = 3042379) B3042379
theorem B3798827 : Blo 1688044 3798827 := bstep (se 1 (by rfl) ⟨2849120, by rfl⟩ : syracuseStep 3798827 = 5698241) B5698241
theorem B2406287 : Blo 1688044 2406287 := bstep (se 1 (by rfl) ⟨1804715, by rfl⟩ : syracuseStep 2406287 = 3609431) B3609431
theorem B2029483 : Blo 1688044 2029483 := bstep (se 1 (by rfl) ⟨1522112, by rfl⟩ : syracuseStep 2029483 = 3044225) B3044225
theorem B21649355 : Blo 1688044 21649355 := bstep (se 1 (by rfl) ⟨16237016, by rfl⟩ : syracuseStep 21649355 = 32474033) B32474033
theorem B13694987 : Blo 1688044 13694987 := bstep (se 1 (by rfl) ⟨10271240, by rfl⟩ : syracuseStep 13694987 = 20542481) B20542481
theorem B2848783 : Blo 1688044 2848783 := bstep (se 1 (by rfl) ⟨2136587, by rfl⟩ : syracuseStep 2848783 = 4273175) B4273175
theorem B5699645 : Blo 1688044 5699645 := bstep (se 3 (by rfl) ⟨1068683, by rfl⟩ : syracuseStep 5699645 = 2137367) B2137367
theorem B3799187 : Blo 1688044 3799187 := bstep (se 1 (by rfl) ⟨2849390, by rfl⟩ : syracuseStep 3799187 = 5698781) B5698781
theorem B4274329 : Blo 1688044 4274329 := bstep (se 2 (by rfl) ⟨1602873, by rfl⟩ : syracuseStep 4274329 = 3205747) B3205747
theorem B10819757 : Blo 1688044 10819757 := bstep (se 3 (by rfl) ⟨2028704, by rfl⟩ : syracuseStep 10819757 = 4057409) B4057409
theorem B3799241 : Blo 1688044 3799241 := bstep (se 2 (by rfl) ⟨1424715, by rfl⟩ : syracuseStep 3799241 = 2849431) B2849431
theorem B8231183 : Blo 1688044 8231183 := bstep (se 1 (by rfl) ⟨6173387, by rfl⟩ : syracuseStep 8231183 = 12346775) B12346775
theorem B3422507 : Blo 1688044 3422507 := bstep (se 1 (by rfl) ⟨2566880, by rfl⟩ : syracuseStep 3422507 = 5133761) B5133761
theorem B4274491 : Blo 1688044 4274491 := bstep (se 1 (by rfl) ⟨3205868, by rfl⟩ : syracuseStep 4274491 = 6411737) B6411737
theorem B5413235 : Blo 1688044 5413235 := bstep (se 1 (by rfl) ⟨4059926, by rfl⟩ : syracuseStep 5413235 = 8119853) B8119853
theorem B6412679 : Blo 1688044 6412679 := bstep (se 1 (by rfl) ⟨4809509, by rfl⟩ : syracuseStep 6412679 = 9619019) B9619019
theorem B8116625 : Blo 1688044 8116625 := bstep (se 2 (by rfl) ⟨3043734, by rfl⟩ : syracuseStep 8116625 = 6087469) B6087469
theorem B4274633 : Blo 1688044 4274633 := bstep (se 2 (by rfl) ⟨1602987, by rfl⟩ : syracuseStep 4274633 = 3205975) B3205975
theorem B2849323 : Blo 1688044 2849323 := bstep (se 1 (by rfl) ⟨2136992, by rfl⟩ : syracuseStep 2849323 = 4273985) B4273985
theorem B1899067 : Blo 1688044 1899067 := bstep (se 1 (by rfl) ⟨1424300, by rfl⟩ : syracuseStep 1899067 = 2848601) B2848601
theorem B2136719 : Blo 1688044 2136719 := bstep (se 1 (by rfl) ⟨1602539, by rfl⟩ : syracuseStep 2136719 = 3205079) B3205079
theorem B2849465 : Blo 1688044 2849465 := bstep (se 2 (by rfl) ⟨1068549, by rfl⟩ : syracuseStep 2849465 = 2137099) B2137099
theorem B8551169 : Blo 1688044 8551169 := bstep (se 2 (by rfl) ⟨3206688, by rfl⟩ : syracuseStep 8551169 = 6413377) B6413377
theorem B4274977 : Blo 1688044 4274977 := bstep (se 2 (by rfl) ⟨1603116, by rfl⟩ : syracuseStep 4274977 = 3206233) B3206233
theorem B7215905 : Blo 1688044 7215905 := bstep (se 2 (by rfl) ⟨2705964, by rfl⟩ : syracuseStep 7215905 = 5411929) B5411929
theorem B17324837 : Blo 1688044 17324837 := bstep (se 4 (by rfl) ⟨1624203, by rfl⟩ : syracuseStep 17324837 = 3248407) B3248407
theorem B22248229 : Blo 1688044 22248229 := bstep (se 4 (by rfl) ⟨2085771, by rfl⟩ : syracuseStep 22248229 = 4171543) B4171543
theorem B3423035 : Blo 1688044 3423035 := bstep (se 1 (by rfl) ⟨2567276, by rfl⟩ : syracuseStep 3423035 = 5134553) B5134553
theorem B3799943 : Blo 1688044 3799943 := bstep (se 1 (by rfl) ⟨2849957, by rfl⟩ : syracuseStep 3799943 = 5699915) B5699915
theorem B1899535 : Blo 1688044 1899535 := bstep (se 1 (by rfl) ⟨1424651, by rfl⟩ : syracuseStep 1899535 = 2849303) B2849303
theorem B7314461 : Blo 1688044 7314461 := bstep (se 3 (by rfl) ⟨1371461, by rfl⟩ : syracuseStep 7314461 = 2742923) B2742923
theorem B3800123 : Blo 1688044 3800123 := bstep (se 1 (by rfl) ⟨2850092, by rfl⟩ : syracuseStep 3800123 = 5700185) B5700185
theorem B11549783 : Blo 1688044 11549783 := bstep (se 1 (by rfl) ⟨8662337, by rfl⟩ : syracuseStep 11549783 = 17324675) B17324675
theorem B3800249 : Blo 1688044 3800249 := bstep (se 2 (by rfl) ⟨1425093, by rfl⟩ : syracuseStep 3800249 = 2850187) B2850187
theorem B4807937 : Blo 1688044 4807937 := bstep (se 2 (by rfl) ⟨1802976, by rfl⟩ : syracuseStep 4807937 = 3605953) B3605953
theorem B2850167 : Blo 1688044 2850167 := bstep (se 1 (by rfl) ⟨2137625, by rfl⟩ : syracuseStep 2850167 = 4275251) B4275251
theorem B4275575 : Blo 1688044 4275575 := bstep (se 1 (by rfl) ⟨3206681, by rfl⟩ : syracuseStep 4275575 = 6413363) B6413363
theorem B4332935 : Blo 1688044 4332935 := bstep (se 1 (by rfl) ⟨3249701, by rfl⟩ : syracuseStep 4332935 = 6499403) B6499403
theorem B4873619 : Blo 1688044 4873619 := bstep (se 1 (by rfl) ⟨3655214, by rfl⟩ : syracuseStep 4873619 = 7310429) B7310429
theorem B5561747 : Blo 1688044 5561747 := bstep (se 1 (by rfl) ⟨4171310, by rfl⟩ : syracuseStep 5561747 = 8342621) B8342621
theorem B5701049 : Blo 1688044 5701049 := bstep (se 2 (by rfl) ⟨2137893, by rfl⟩ : syracuseStep 5701049 = 4275787) B4275787
theorem B1900039 : Blo 1688044 1900039 := bstep (se 1 (by rfl) ⟨1425029, by rfl⟩ : syracuseStep 1900039 = 2850059) B2850059
theorem B3800591 : Blo 1688044 3800591 := bstep (se 1 (by rfl) ⟨2850443, by rfl⟩ : syracuseStep 3800591 = 5700887) B5700887
theorem B3800609 : Blo 1688044 3800609 := bstep (se 2 (by rfl) ⟨1425228, by rfl⟩ : syracuseStep 3800609 = 2850457) B2850457
theorem B8551979 : Blo 1688044 8551979 := bstep (se 1 (by rfl) ⟨6413984, by rfl⟩ : syracuseStep 8551979 = 12827969) B12827969
theorem B16228019 : Blo 1688044 16228019 := bstep (se 1 (by rfl) ⟨12171014, by rfl⟩ : syracuseStep 16228019 = 24342029) B24342029
theorem B1900219 : Blo 1688044 1900219 := bstep (se 1 (by rfl) ⟨1425164, by rfl⟩ : syracuseStep 1900219 = 2850329) B2850329
theorem B4808393 : Blo 1688044 4808393 := bstep (se 2 (by rfl) ⟨1803147, by rfl⟩ : syracuseStep 4808393 = 3606295) B3606295
theorem B36601573 : Blo 1688044 36601573 := bstep (se 4 (by rfl) ⟨3431397, by rfl⟩ : syracuseStep 36601573 = 6862795) B6862795
theorem B23125733 : Blo 1688044 23125733 := bstep (se 4 (by rfl) ⟨2168037, by rfl⟩ : syracuseStep 23125733 = 4336075) B4336075
theorem B2850619 : Blo 1688044 2850619 := bstep (se 1 (by rfl) ⟨2137964, by rfl⟩ : syracuseStep 2850619 = 4275929) B4275929
theorem B3800951 : Blo 1688044 3800951 := bstep (se 1 (by rfl) ⟨2850713, by rfl⟩ : syracuseStep 3800951 = 5701427) B5701427
theorem B2850761 : Blo 1688044 2850761 := bstep (se 2 (by rfl) ⟨1069035, by rfl⟩ : syracuseStep 2850761 = 2138071) B2138071
theorem B3801095 : Blo 1688044 3801095 := bstep (se 1 (by rfl) ⟨2850821, by rfl⟩ : syracuseStep 3801095 = 5701643) B5701643
theorem B3801167 : Blo 1688044 3801167 := bstep (se 1 (by rfl) ⟨2850875, by rfl⟩ : syracuseStep 3801167 = 5701751) B5701751
theorem B6414653 : Blo 1688044 6414653 := bstep (se 3 (by rfl) ⟨1202747, by rfl⟩ : syracuseStep 6414653 = 2405495) B2405495
theorem B7217495 : Blo 1688044 7217495 := bstep (se 1 (by rfl) ⟨5413121, by rfl⟩ : syracuseStep 7217495 = 10826243) B10826243
theorem B12337541 : Blo 1688044 12337541 := bstep (se 4 (by rfl) ⟨1156644, by rfl⟩ : syracuseStep 12337541 = 2313289) B2313289
theorem B2851247 : Blo 1688044 2851247 := bstep (se 1 (by rfl) ⟨2138435, by rfl⟩ : syracuseStep 2851247 = 4276871) B4276871
theorem B1900975 : Blo 1688044 1900975 := bstep (se 1 (by rfl) ⟨1425731, by rfl⟩ : syracuseStep 1900975 = 2851463) B2851463
theorem B3850715 : Blo 1688044 3850715 := bstep (se 1 (by rfl) ⟨2888036, by rfl⟩ : syracuseStep 3850715 = 5776073) B5776073
theorem B3801563 : Blo 1688044 3801563 := bstep (se 1 (by rfl) ⟨2851172, by rfl⟩ : syracuseStep 3801563 = 5702345) B5702345
theorem B4809203 : Blo 1688044 4809203 := bstep (se 1 (by rfl) ⟨3606902, by rfl⟩ : syracuseStep 4809203 = 7213805) B7213805
theorem B6414835 : Blo 1688044 6414835 := bstep (se 1 (by rfl) ⟨4811126, by rfl⟩ : syracuseStep 6414835 = 9622253) B9622253
theorem B1688103 : Blo 1688044 1688103 := bstep (se 1 (by rfl) ⟨1266077, by rfl⟩ : syracuseStep 1688103 = 2532155) B2532155
theorem B5702183 : Blo 1688044 5702183 := bstep (se 1 (by rfl) ⟨4276637, by rfl⟩ : syracuseStep 5702183 = 8553275) B8553275
theorem B2138663 : Blo 1688044 2138663 := bstep (se 1 (by rfl) ⟨1603997, by rfl⟩ : syracuseStep 2138663 = 3207995) B3207995
theorem B1688143 : Blo 1688044 1688143 := bstep (se 1 (by rfl) ⟨1266107, by rfl⟩ : syracuseStep 1688143 = 2532215) B2532215
theorem B1688159 : Blo 1688044 1688159 := bstep (se 1 (by rfl) ⟨1266119, by rfl⟩ : syracuseStep 1688159 = 2532239) B2532239
theorem B1688187 : Blo 1688044 1688187 := bstep (se 1 (by rfl) ⟨1266140, by rfl⟩ : syracuseStep 1688187 = 2532281) B2532281
theorem B5702291 : Blo 1688044 5702291 := bstep (se 1 (by rfl) ⟨4276718, by rfl⟩ : syracuseStep 5702291 = 8553437) B8553437
theorem B12821165 : Blo 1688044 12821165 := bstep (se 3 (by rfl) ⟨2403968, by rfl⟩ : syracuseStep 12821165 = 4807937) B4807937
theorem B1688239 : Blo 1688044 1688239 := bstep (se 1 (by rfl) ⟨1266179, by rfl⟩ : syracuseStep 1688239 = 2532359) B2532359
theorem B1688263 : Blo 1688044 1688263 := bstep (se 1 (by rfl) ⟨1266197, by rfl⟩ : syracuseStep 1688263 = 2532395) B2532395
theorem B1688283 : Blo 1688044 1688283 := bstep (se 1 (by rfl) ⟨1266212, by rfl⟩ : syracuseStep 1688283 = 2532425) B2532425
theorem B2532089 : Blo 1688044 2532089 := bstep (se 2 (by rfl) ⟨949533, by rfl⟩ : syracuseStep 2532089 = 1899067) B1899067
theorem B9126685 : Blo 1688044 9126685 := bstep (se 3 (by rfl) ⟨1711253, by rfl⟩ : syracuseStep 9126685 = 3422507) B3422507
theorem B1688359 : Blo 1688044 1688359 := bstep (se 1 (by rfl) ⟨1266269, by rfl⟩ : syracuseStep 1688359 = 2532539) B2532539
theorem B1688399 : Blo 1688044 1688399 := bstep (se 1 (by rfl) ⟨1266299, by rfl⟩ : syracuseStep 1688399 = 2532599) B2532599
theorem B2532191 : Blo 1688044 2532191 := bstep (se 1 (by rfl) ⟨1899143, by rfl⟩ : syracuseStep 2532191 = 3798287) B3798287
theorem B1688415 : Blo 1688044 1688415 := bstep (se 1 (by rfl) ⟨1266311, by rfl⟩ : syracuseStep 1688415 = 2532623) B2532623
theorem B2851679 : Blo 1688044 2851679 := bstep (se 1 (by rfl) ⟨2138759, by rfl⟩ : syracuseStep 2851679 = 4277519) B4277519
theorem B2532203 : Blo 1688044 2532203 := bstep (se 1 (by rfl) ⟨1899152, by rfl⟩ : syracuseStep 2532203 = 3798305) B3798305
theorem B5702507 : Blo 1688044 5702507 := bstep (se 1 (by rfl) ⟨4276880, by rfl⟩ : syracuseStep 5702507 = 8553761) B8553761
theorem B1688443 : Blo 1688044 1688443 := bstep (se 1 (by rfl) ⟨1266332, by rfl⟩ : syracuseStep 1688443 = 2532665) B2532665
theorem B5702561 : Blo 1688044 5702561 := bstep (se 2 (by rfl) ⟨2138460, by rfl⟩ : syracuseStep 5702561 = 4276921) B4276921
theorem B1688495 : Blo 1688044 1688495 := bstep (se 1 (by rfl) ⟨1266371, by rfl⟩ : syracuseStep 1688495 = 2532743) B2532743
theorem B3802031 : Blo 1688044 3802031 := bstep (se 1 (by rfl) ⟨2851523, by rfl⟩ : syracuseStep 3802031 = 5703047) B5703047
theorem B8119223 : Blo 1688044 8119223 := bstep (se 1 (by rfl) ⟨6089417, by rfl⟩ : syracuseStep 8119223 = 12178835) B12178835
theorem B1688519 : Blo 1688044 1688519 := bstep (se 1 (by rfl) ⟨1266389, by rfl⟩ : syracuseStep 1688519 = 2532779) B2532779
theorem B1688539 : Blo 1688044 1688539 := bstep (se 1 (by rfl) ⟨1266404, by rfl⟩ : syracuseStep 1688539 = 2532809) B2532809
theorem B14435293 : Blo 1688044 14435293 := bstep (se 3 (by rfl) ⟨2706617, by rfl⟩ : syracuseStep 14435293 = 5413235) B5413235
theorem B1688615 : Blo 1688044 1688615 := bstep (se 1 (by rfl) ⟨1266461, by rfl⟩ : syracuseStep 1688615 = 2532923) B2532923
theorem B29664305 : Blo 1688044 29664305 := bstep (se 2 (by rfl) ⟨11124114, by rfl⟩ : syracuseStep 29664305 = 22248229) B22248229
theorem B2532431 : Blo 1688044 2532431 := bstep (se 1 (by rfl) ⟨1899323, by rfl⟩ : syracuseStep 2532431 = 3798647) B3798647
theorem B1688655 : Blo 1688044 1688655 := bstep (se 1 (by rfl) ⟨1266491, by rfl⟩ : syracuseStep 1688655 = 2532983) B2532983
theorem B1688671 : Blo 1688044 1688671 := bstep (se 1 (by rfl) ⟨1266503, by rfl⟩ : syracuseStep 1688671 = 2533007) B2533007
theorem B1688699 : Blo 1688044 1688699 := bstep (se 1 (by rfl) ⟨1266524, by rfl⟩ : syracuseStep 1688699 = 2533049) B2533049
theorem B3802283 : Blo 1688044 3802283 := bstep (se 1 (by rfl) ⟨2851712, by rfl⟩ : syracuseStep 3802283 = 5703425) B5703425
theorem B1688751 : Blo 1688044 1688751 := bstep (se 1 (by rfl) ⟨1266563, by rfl⟩ : syracuseStep 1688751 = 2533127) B2533127
theorem B2532551 : Blo 1688044 2532551 := bstep (se 1 (by rfl) ⟨1899413, by rfl⟩ : syracuseStep 2532551 = 3798827) B3798827
theorem B1688775 : Blo 1688044 1688775 := bstep (se 1 (by rfl) ⟨1266581, by rfl⟩ : syracuseStep 1688775 = 2533163) B2533163
theorem B1688795 : Blo 1688044 1688795 := bstep (se 1 (by rfl) ⟨1266596, by rfl⟩ : syracuseStep 1688795 = 2533193) B2533193
theorem B41100533 : Blo 1688044 41100533 := bstep (se 5 (by rfl) ⟨1926587, by rfl⟩ : syracuseStep 41100533 = 3853175) B3853175
theorem B1688871 : Blo 1688044 1688871 := bstep (se 1 (by rfl) ⟨1266653, by rfl⟩ : syracuseStep 1688871 = 2533307) B2533307
theorem B1688911 : Blo 1688044 1688911 := bstep (se 1 (by rfl) ⟨1266683, by rfl⟩ : syracuseStep 1688911 = 2533367) B2533367
theorem B1688927 : Blo 1688044 1688927 := bstep (se 1 (by rfl) ⟨1266695, by rfl⟩ : syracuseStep 1688927 = 2533391) B2533391
theorem B2532713 : Blo 1688044 2532713 := bstep (se 2 (by rfl) ⟨949767, by rfl⟩ : syracuseStep 2532713 = 1899535) B1899535
theorem B2704747 : Blo 1688044 2704747 := bstep (se 1 (by rfl) ⟨2028560, by rfl⟩ : syracuseStep 2704747 = 4057121) B4057121
theorem B1688955 : Blo 1688044 1688955 := bstep (se 1 (by rfl) ⟨1266716, by rfl⟩ : syracuseStep 1688955 = 2533433) B2533433
theorem B1689007 : Blo 1688044 1689007 := bstep (se 1 (by rfl) ⟨1266755, by rfl⟩ : syracuseStep 1689007 = 2533511) B2533511
theorem B2532791 : Blo 1688044 2532791 := bstep (se 1 (by rfl) ⟨1899593, by rfl⟩ : syracuseStep 2532791 = 3799187) B3799187
theorem B1689031 : Blo 1688044 1689031 := bstep (se 1 (by rfl) ⟨1266773, by rfl⟩ : syracuseStep 1689031 = 2533547) B2533547
theorem B5408201 : Blo 1688044 5408201 := bstep (se 2 (by rfl) ⟨2028075, by rfl⟩ : syracuseStep 5408201 = 4056151) B4056151
theorem B2532827 : Blo 1688044 2532827 := bstep (se 1 (by rfl) ⟨1899620, by rfl⟩ : syracuseStep 2532827 = 3799241) B3799241
theorem B1689051 : Blo 1688044 1689051 := bstep (se 1 (by rfl) ⟨1266788, by rfl⟩ : syracuseStep 1689051 = 2533577) B2533577
theorem B5703155 : Blo 1688044 5703155 := bstep (se 1 (by rfl) ⟨4277366, by rfl⟩ : syracuseStep 5703155 = 8554733) B8554733
theorem B1689127 : Blo 1688044 1689127 := bstep (se 1 (by rfl) ⟨1266845, by rfl⟩ : syracuseStep 1689127 = 2533691) B2533691
theorem B1689167 : Blo 1688044 1689167 := bstep (se 1 (by rfl) ⟨1266875, by rfl⟩ : syracuseStep 1689167 = 2533751) B2533751
theorem B1689183 : Blo 1688044 1689183 := bstep (se 1 (by rfl) ⟨1266887, by rfl⟩ : syracuseStep 1689183 = 2533775) B2533775
theorem B1689211 : Blo 1688044 1689211 := bstep (se 1 (by rfl) ⟨1266908, by rfl⟩ : syracuseStep 1689211 = 2533817) B2533817
theorem B1689263 : Blo 1688044 1689263 := bstep (se 1 (by rfl) ⟨1266947, by rfl⟩ : syracuseStep 1689263 = 2533895) B2533895
theorem B7218877 : Blo 1688044 7218877 := bstep (se 3 (by rfl) ⟨1353539, by rfl⟩ : syracuseStep 7218877 = 2707079) B2707079
theorem B1689287 : Blo 1688044 1689287 := bstep (se 1 (by rfl) ⟨1266965, by rfl⟩ : syracuseStep 1689287 = 2533931) B2533931
theorem B6416081 : Blo 1688044 6416081 := bstep (se 2 (by rfl) ⟨2406030, by rfl⟩ : syracuseStep 6416081 = 4812061) B4812061
theorem B1689307 : Blo 1688044 1689307 := bstep (se 1 (by rfl) ⟨1266980, by rfl⟩ : syracuseStep 1689307 = 2533961) B2533961
theorem B7210745 : Blo 1688044 7210745 := bstep (se 2 (by rfl) ⟨2704029, by rfl⟩ : syracuseStep 7210745 = 5408059) B5408059
theorem B1689383 : Blo 1688044 1689383 := bstep (se 1 (by rfl) ⟨1267037, by rfl⟩ : syracuseStep 1689383 = 2534075) B2534075
theorem B1689423 : Blo 1688044 1689423 := bstep (se 1 (by rfl) ⟨1267067, by rfl⟩ : syracuseStep 1689423 = 2534135) B2534135
theorem B1689439 : Blo 1688044 1689439 := bstep (se 1 (by rfl) ⟨1267079, by rfl⟩ : syracuseStep 1689439 = 2534159) B2534159
theorem B4810603 : Blo 1688044 4810603 := bstep (se 1 (by rfl) ⟨3607952, by rfl⟩ : syracuseStep 4810603 = 7215905) B7215905
theorem B1689467 : Blo 1688044 1689467 := bstep (se 1 (by rfl) ⟨1267100, by rfl⟩ : syracuseStep 1689467 = 2534201) B2534201
theorem B2533295 : Blo 1688044 2533295 := bstep (se 1 (by rfl) ⟨1899971, by rfl⟩ : syracuseStep 2533295 = 3799943) B3799943
theorem B1689519 : Blo 1688044 1689519 := bstep (se 1 (by rfl) ⟨1267139, by rfl⟩ : syracuseStep 1689519 = 2534279) B2534279
theorem B1689543 : Blo 1688044 1689543 := bstep (se 1 (by rfl) ⟨1267157, by rfl⟩ : syracuseStep 1689543 = 2534315) B2534315
theorem B1689563 : Blo 1688044 1689563 := bstep (se 1 (by rfl) ⟨1267172, by rfl⟩ : syracuseStep 1689563 = 2534345) B2534345
theorem B2533385 : Blo 1688044 2533385 := bstep (se 2 (by rfl) ⟨950019, by rfl⟩ : syracuseStep 2533385 = 1900039) B1900039
theorem B5703695 : Blo 1688044 5703695 := bstep (se 1 (by rfl) ⟨4277771, by rfl⟩ : syracuseStep 5703695 = 8555543) B8555543
theorem B4876307 : Blo 1688044 4876307 := bstep (se 1 (by rfl) ⟨3657230, by rfl⟩ : syracuseStep 4876307 = 7314461) B7314461
theorem B4114451 : Blo 1688044 4114451 := bstep (se 1 (by rfl) ⟨3085838, by rfl⟩ : syracuseStep 4114451 = 6171677) B6171677
theorem B1693894679 : Blo 1688044 1693894679 := bstep (se 1 (by rfl) ⟨1270421009, by rfl⟩ : syracuseStep 1693894679 = 2540842019) B2540842019
theorem B2533415 : Blo 1688044 2533415 := bstep (se 1 (by rfl) ⟨1900061, by rfl⟩ : syracuseStep 2533415 = 3800123) B3800123
theorem B1689639 : Blo 1688044 1689639 := bstep (se 1 (by rfl) ⟨1267229, by rfl⟩ : syracuseStep 1689639 = 2534459) B2534459
theorem B1689679 : Blo 1688044 1689679 := bstep (se 1 (by rfl) ⟨1267259, by rfl⟩ : syracuseStep 1689679 = 2534519) B2534519
theorem B1689695 : Blo 1688044 1689695 := bstep (se 1 (by rfl) ⟨1267271, by rfl⟩ : syracuseStep 1689695 = 2534543) B2534543
theorem B34670693 : Blo 1688044 34670693 := bstep (se 4 (by rfl) ⟨3250377, by rfl⟩ : syracuseStep 34670693 = 6500755) B6500755
theorem B2533499 : Blo 1688044 2533499 := bstep (se 1 (by rfl) ⟨1900124, by rfl⟩ : syracuseStep 2533499 = 3800249) B3800249
theorem B1689723 : Blo 1688044 1689723 := bstep (se 1 (by rfl) ⟨1267292, by rfl⟩ : syracuseStep 1689723 = 2534585) B2534585
theorem B1689775 : Blo 1688044 1689775 := bstep (se 1 (by rfl) ⟨1267331, by rfl⟩ : syracuseStep 1689775 = 2534663) B2534663
theorem B1689799 : Blo 1688044 1689799 := bstep (se 1 (by rfl) ⟨1267349, by rfl⟩ : syracuseStep 1689799 = 2534699) B2534699
theorem B1689819 : Blo 1688044 1689819 := bstep (se 1 (by rfl) ⟨1267364, by rfl⟩ : syracuseStep 1689819 = 2534729) B2534729
theorem B2533625 : Blo 1688044 2533625 := bstep (se 2 (by rfl) ⟨950109, by rfl⟩ : syracuseStep 2533625 = 1900219) B1900219
theorem B1689895 : Blo 1688044 1689895 := bstep (se 1 (by rfl) ⟨1267421, by rfl⟩ : syracuseStep 1689895 = 2534843) B2534843
theorem B48802097 : Blo 1688044 48802097 := bstep (se 2 (by rfl) ⟨18300786, by rfl⟩ : syracuseStep 48802097 = 36601573) B36601573
theorem B1689935 : Blo 1688044 1689935 := bstep (se 1 (by rfl) ⟨1267451, by rfl⟩ : syracuseStep 1689935 = 2534903) B2534903
theorem B2533727 : Blo 1688044 2533727 := bstep (se 1 (by rfl) ⟨1900295, by rfl⟩ : syracuseStep 2533727 = 3800591) B3800591
theorem B1689951 : Blo 1688044 1689951 := bstep (se 1 (by rfl) ⟨1267463, by rfl⟩ : syracuseStep 1689951 = 2534927) B2534927
theorem B2533739 : Blo 1688044 2533739 := bstep (se 1 (by rfl) ⟨1900304, by rfl⟩ : syracuseStep 2533739 = 3800609) B3800609
theorem B1689979 : Blo 1688044 1689979 := bstep (se 1 (by rfl) ⟨1267484, by rfl⟩ : syracuseStep 1689979 = 2534969) B2534969
theorem B6416765 : Blo 1688044 6416765 := bstep (se 3 (by rfl) ⟨1203143, by rfl⟩ : syracuseStep 6416765 = 2406287) B2406287
theorem B1690031 : Blo 1688044 1690031 := bstep (se 1 (by rfl) ⟨1267523, by rfl⟩ : syracuseStep 1690031 = 2535047) B2535047
theorem B3205595 : Blo 1688044 3205595 := bstep (se 1 (by rfl) ⟨2404196, by rfl⟩ : syracuseStep 3205595 = 4808393) B4808393
theorem B4393511 : Blo 1688044 4393511 := bstep (se 1 (by rfl) ⟨3295133, by rfl⟩ : syracuseStep 4393511 = 6590267) B6590267
theorem B2705977 : Blo 1688044 2705977 := bstep (se 2 (by rfl) ⟨1014741, by rfl⟩ : syracuseStep 2705977 = 2029483) B2029483
theorem B2533967 : Blo 1688044 2533967 := bstep (se 1 (by rfl) ⟨1900475, by rfl⟩ : syracuseStep 2533967 = 3800951) B3800951
theorem B3205831 : Blo 1688044 3205831 := bstep (se 1 (by rfl) ⟨2404373, by rfl⟩ : syracuseStep 3205831 = 4808747) B4808747
theorem B2534087 : Blo 1688044 2534087 := bstep (se 1 (by rfl) ⟨1900565, by rfl⟩ : syracuseStep 2534087 = 3801131) B3801131
theorem B2706119 : Blo 1688044 2706119 := bstep (se 1 (by rfl) ⟨2029589, by rfl⟩ : syracuseStep 2706119 = 4059179) B4059179
theorem B8555219 : Blo 1688044 8555219 := bstep (se 1 (by rfl) ⟨6416414, by rfl⟩ : syracuseStep 8555219 = 12832829) B12832829
theorem B41069389 : Blo 1688044 41069389 := bstep (se 3 (by rfl) ⟨7700510, by rfl⟩ : syracuseStep 41069389 = 15401021) B15401021
theorem B2534249 : Blo 1688044 2534249 := bstep (se 2 (by rfl) ⟨950343, by rfl⟩ : syracuseStep 2534249 = 1900687) B1900687
theorem B2534327 : Blo 1688044 2534327 := bstep (se 1 (by rfl) ⟨1900745, by rfl⟩ : syracuseStep 2534327 = 3801491) B3801491
theorem B3042235 : Blo 1688044 3042235 := bstep (se 1 (by rfl) ⟨2281676, by rfl⟩ : syracuseStep 3042235 = 4563353) B4563353
theorem B2534363 : Blo 1688044 2534363 := bstep (se 1 (by rfl) ⟨1900772, by rfl⟩ : syracuseStep 2534363 = 3801545) B3801545
theorem B5204999 : Blo 1688044 5204999 := bstep (se 1 (by rfl) ⟨3903749, by rfl⟩ : syracuseStep 5204999 = 7807499) B7807499
theorem B12823595 : Blo 1688044 12823595 := bstep (se 1 (by rfl) ⟨9617696, by rfl⟩ : syracuseStep 12823595 = 19235393) B19235393
theorem B21646379 : Blo 1688044 21646379 := bstep (se 1 (by rfl) ⟨16234784, by rfl⟩ : syracuseStep 21646379 = 32469569) B32469569
theorem B97430849 : Blo 1688044 97430849 := bstep (se 2 (by rfl) ⟨36536568, by rfl⟩ : syracuseStep 97430849 = 73073137) B73073137
theorem B2534831 : Blo 1688044 2534831 := bstep (se 1 (by rfl) ⟨1901123, by rfl⟩ : syracuseStep 2534831 = 3802247) B3802247
theorem B2534921 : Blo 1688044 2534921 := bstep (se 2 (by rfl) ⟨950595, by rfl⟩ : syracuseStep 2534921 = 1901191) B1901191
theorem B2534951 : Blo 1688044 2534951 := bstep (se 1 (by rfl) ⟨1901213, by rfl⟩ : syracuseStep 2534951 = 3802427) B3802427
theorem B12832343 : Blo 1688044 12832343 := bstep (se 1 (by rfl) ⟨9624257, by rfl⟩ : syracuseStep 12832343 = 19248515) B19248515
theorem B7704161 : Blo 1688044 7704161 := bstep (se 2 (by rfl) ⟨2889060, by rfl⟩ : syracuseStep 7704161 = 5778121) B5778121
theorem B2928251 : Blo 1688044 2928251 := bstep (se 1 (by rfl) ⟨2196188, by rfl⟩ : syracuseStep 2928251 = 4392377) B4392377
theorem B2535035 : Blo 1688044 2535035 := bstep (se 1 (by rfl) ⟨1901276, by rfl⟩ : syracuseStep 2535035 = 3802553) B3802553
theorem B10268299 : Blo 1688044 10268299 := bstep (se 1 (by rfl) ⟨7701224, by rfl⟩ : syracuseStep 10268299 = 15402449) B15402449
theorem B5697323 : Blo 1688044 5697323 := bstep (se 1 (by rfl) ⟨4272992, by rfl⟩ : syracuseStep 5697323 = 8545985) B8545985
theorem B10817347 : Blo 1688044 10817347 := bstep (se 1 (by rfl) ⟨8113010, by rfl⟩ : syracuseStep 10817347 = 16226021) B16226021
theorem B9129991 : Blo 1688044 9129991 := bstep (se 1 (by rfl) ⟨6847493, by rfl⟩ : syracuseStep 9129991 = 13694987) B13694987
theorem B5697593 : Blo 1688044 5697593 := bstep (se 2 (by rfl) ⟨2136597, by rfl⟩ : syracuseStep 5697593 = 4273195) B4273195
theorem B7213171 : Blo 1688044 7213171 := bstep (se 1 (by rfl) ⟨5409878, by rfl⟩ : syracuseStep 7213171 = 10819757) B10819757
theorem B5411083 : Blo 1688044 5411083 := bstep (se 1 (by rfl) ⟨4058312, by rfl⟩ : syracuseStep 5411083 = 8116625) B8116625
theorem B5697917 : Blo 1688044 5697917 := bstep (se 3 (by rfl) ⟨1068359, by rfl⟩ : syracuseStep 5697917 = 2136719) B2136719
theorem B19493399 : Blo 1688044 19493399 := bstep (se 1 (by rfl) ⟨14620049, by rfl⟩ : syracuseStep 19493399 = 29240099) B29240099
theorem B2282023 : Blo 1688044 2282023 := bstep (se 1 (by rfl) ⟨1711517, by rfl⟩ : syracuseStep 2282023 = 3423035) B3423035
theorem B2404903 : Blo 1688044 2404903 := bstep (se 1 (by rfl) ⟨1803677, by rfl⟩ : syracuseStep 2404903 = 3607355) B3607355
theorem B3207737 : Blo 1688044 3207737 := bstep (se 2 (by rfl) ⟨1202901, by rfl⟩ : syracuseStep 3207737 = 2405803) B2405803
theorem B5698187 : Blo 1688044 5698187 := bstep (se 1 (by rfl) ⟨4273640, by rfl⟩ : syracuseStep 5698187 = 8547281) B8547281
theorem B3208079 : Blo 1688044 3208079 := bstep (se 1 (by rfl) ⟨2406059, by rfl⟩ : syracuseStep 3208079 = 4812119) B4812119
theorem B3470255 : Blo 1688044 3470255 := bstep (se 1 (by rfl) ⟨2602691, by rfl⟩ : syracuseStep 3470255 = 5205383) B5205383
theorem B2888623 : Blo 1688044 2888623 := bstep (se 1 (by rfl) ⟨2166467, by rfl⟩ : syracuseStep 2888623 = 4332935) B4332935
theorem B3249079 : Blo 1688044 3249079 := bstep (se 1 (by rfl) ⟨2436809, by rfl⟩ : syracuseStep 3249079 = 4873619) B4873619
theorem B3707831 : Blo 1688044 3707831 := bstep (se 1 (by rfl) ⟨2780873, by rfl⟩ : syracuseStep 3707831 = 5561747) B5561747
theorem B10818679 : Blo 1688044 10818679 := bstep (se 1 (by rfl) ⟨8114009, by rfl⟩ : syracuseStep 10818679 = 16228019) B16228019
theorem B2028667 : Blo 1688044 2028667 := bstep (se 1 (by rfl) ⟨1521500, by rfl⟩ : syracuseStep 2028667 = 3043001) B3043001
theorem B2405575 : Blo 1688044 2405575 := bstep (se 1 (by rfl) ⟨1804181, by rfl⟩ : syracuseStep 2405575 = 3608363) B3608363
theorem B3798377 : Blo 1688044 3798377 := bstep (se 2 (by rfl) ⟨1424391, by rfl⟩ : syracuseStep 3798377 = 2848783) B2848783
theorem B25998833 : Blo 1688044 25998833 := bstep (se 2 (by rfl) ⟨9749562, by rfl⟩ : syracuseStep 25998833 = 19499125) B19499125
theorem B5699105 : Blo 1688044 5699105 := bstep (se 2 (by rfl) ⟨2137164, by rfl⟩ : syracuseStep 5699105 = 4274329) B4274329
theorem B8550035 : Blo 1688044 8550035 := bstep (se 1 (by rfl) ⟨6412526, by rfl⟩ : syracuseStep 8550035 = 12825053) B12825053
theorem B19494599 : Blo 1688044 19494599 := bstep (se 1 (by rfl) ⟨14620949, by rfl⟩ : syracuseStep 19494599 = 29241899) B29241899
theorem B10819271 : Blo 1688044 10819271 := bstep (se 1 (by rfl) ⟨8114453, by rfl⟩ : syracuseStep 10819271 = 16228907) B16228907
theorem B5699321 : Blo 1688044 5699321 := bstep (se 2 (by rfl) ⟨2137245, by rfl⟩ : syracuseStep 5699321 = 4274491) B4274491
theorem B2848655 : Blo 1688044 2848655 := bstep (se 1 (by rfl) ⟨2136491, by rfl⟩ : syracuseStep 2848655 = 4272983) B4272983
theorem B6412193 : Blo 1688044 6412193 := bstep (se 2 (by rfl) ⟨2404572, by rfl⟩ : syracuseStep 6412193 = 4809145) B4809145
theorem B3798971 : Blo 1688044 3798971 := bstep (se 1 (by rfl) ⟨2849228, by rfl⟩ : syracuseStep 3798971 = 5698457) B5698457
theorem B5699591 : Blo 1688044 5699591 := bstep (se 1 (by rfl) ⟨4274693, by rfl⟩ : syracuseStep 5699591 = 8549387) B8549387
theorem B7215119 : Blo 1688044 7215119 := bstep (se 1 (by rfl) ⟨5411339, by rfl⟩ : syracuseStep 7215119 = 10822679) B10822679
theorem B3799097 : Blo 1688044 3799097 := bstep (se 2 (by rfl) ⟨1424661, by rfl⟩ : syracuseStep 3799097 = 2849323) B2849323
theorem B5699699 : Blo 1688044 5699699 := bstep (se 1 (by rfl) ⟨4274774, by rfl⟩ : syracuseStep 5699699 = 8549549) B8549549
theorem B9754739 : Blo 1688044 9754739 := bstep (se 1 (by rfl) ⟨7316054, by rfl⟩ : syracuseStep 9754739 = 14632109) B14632109
theorem B2848891 : Blo 1688044 2848891 := bstep (se 1 (by rfl) ⟨2136668, by rfl⟩ : syracuseStep 2848891 = 4273337) B4273337
theorem B5699969 : Blo 1688044 5699969 := bstep (se 2 (by rfl) ⟨2137488, by rfl⟩ : syracuseStep 5699969 = 4274977) B4274977
theorem B3799439 : Blo 1688044 3799439 := bstep (se 1 (by rfl) ⟨2849579, by rfl⟩ : syracuseStep 3799439 = 5699159) B5699159
theorem B26368409 : Blo 1688044 26368409 := bstep (se 2 (by rfl) ⟨9888153, by rfl⟩ : syracuseStep 26368409 = 19776307) B19776307
theorem B2890279 : Blo 1688044 2890279 := bstep (se 1 (by rfl) ⟨2167709, by rfl⟩ : syracuseStep 2890279 = 4335419) B4335419
theorem B14432903 : Blo 1688044 14432903 := bstep (se 1 (by rfl) ⟨10824677, by rfl⟩ : syracuseStep 14432903 = 21649355) B21649355
theorem B2136775 : Blo 1688044 2136775 := bstep (se 1 (by rfl) ⟨1602581, by rfl⟩ : syracuseStep 2136775 = 3205163) B3205163
theorem B3799763 : Blo 1688044 3799763 := bstep (se 1 (by rfl) ⟨2849822, by rfl⟩ : syracuseStep 3799763 = 5699645) B5699645
theorem B3422969 : Blo 1688044 3422969 := bstep (se 2 (by rfl) ⟨1283613, by rfl⟩ : syracuseStep 3422969 = 2567227) B2567227
theorem B26008397 : Blo 1688044 26008397 := bstep (se 3 (by rfl) ⟨4876574, by rfl⟩ : syracuseStep 26008397 = 9753149) B9753149
theorem B46881625 : Blo 1688044 46881625 := bstep (se 2 (by rfl) ⟨17580609, by rfl⟩ : syracuseStep 46881625 = 35161219) B35161219
theorem B5487455 : Blo 1688044 5487455 := bstep (se 1 (by rfl) ⟨4115591, by rfl⟩ : syracuseStep 5487455 = 8231183) B8231183
theorem B6413165 : Blo 1688044 6413165 := bstep (se 3 (by rfl) ⟨1202468, by rfl⟩ : syracuseStep 6413165 = 2404937) B2404937
theorem B4275119 : Blo 1688044 4275119 := bstep (se 1 (by rfl) ⟨3206339, by rfl⟩ : syracuseStep 4275119 = 6412679) B6412679
theorem B2849755 : Blo 1688044 2849755 := bstep (se 1 (by rfl) ⟨2137316, by rfl⟩ : syracuseStep 2849755 = 4274633) B4274633
theorem B4807687 : Blo 1688044 4807687 := bstep (se 1 (by rfl) ⟨3605765, by rfl⟩ : syracuseStep 4807687 = 7211531) B7211531
theorem B1899643 : Blo 1688044 1899643 := bstep (se 1 (by rfl) ⟨1424732, by rfl⟩ : syracuseStep 1899643 = 2849465) B2849465
theorem B5700779 : Blo 1688044 5700779 := bstep (se 1 (by rfl) ⟨4275584, by rfl⟩ : syracuseStep 5700779 = 8551169) B8551169
theorem B11549891 : Blo 1688044 11549891 := bstep (se 1 (by rfl) ⟨8662418, by rfl⟩ : syracuseStep 11549891 = 17324837) B17324837
theorem B13884797 : Blo 1688044 13884797 := bstep (se 3 (by rfl) ⟨2603399, by rfl⟩ : syracuseStep 13884797 = 5206799) B5206799
theorem B7699855 : Blo 1688044 7699855 := bstep (se 1 (by rfl) ⟨5774891, by rfl⟩ : syracuseStep 7699855 = 11549783) B11549783
theorem B2137519 : Blo 1688044 2137519 := bstep (se 1 (by rfl) ⟨1603139, by rfl⟩ : syracuseStep 2137519 = 3206279) B3206279
theorem B4275737 : Blo 1688044 4275737 := bstep (se 2 (by rfl) ⟨1603401, by rfl⟩ : syracuseStep 4275737 = 3206803) B3206803
theorem B6413849 : Blo 1688044 6413849 := bstep (se 2 (by rfl) ⟨2405193, by rfl⟩ : syracuseStep 6413849 = 4810387) B4810387
theorem B6413863 : Blo 1688044 6413863 := bstep (se 1 (by rfl) ⟨4810397, by rfl⟩ : syracuseStep 6413863 = 9620795) B9620795
theorem B1900111 : Blo 1688044 1900111 := bstep (se 1 (by rfl) ⟨1425083, by rfl⟩ : syracuseStep 1900111 = 2850167) B2850167
theorem B2850383 : Blo 1688044 2850383 := bstep (se 1 (by rfl) ⟨2137787, by rfl⟩ : syracuseStep 2850383 = 4275575) B4275575
theorem B3800699 : Blo 1688044 3800699 := bstep (se 1 (by rfl) ⟨2850524, by rfl⟩ : syracuseStep 3800699 = 5701049) B5701049
theorem B5136011 : Blo 1688044 5136011 := bstep (se 1 (by rfl) ⟨3852008, by rfl⟩ : syracuseStep 5136011 = 7704017) B7704017
theorem B5701319 : Blo 1688044 5701319 := bstep (se 1 (by rfl) ⟨4275989, by rfl⟩ : syracuseStep 5701319 = 8551979) B8551979
theorem B3800825 : Blo 1688044 3800825 := bstep (se 2 (by rfl) ⟨1425309, by rfl⟩ : syracuseStep 3800825 = 2850619) B2850619
theorem B15417155 : Blo 1688044 15417155 := bstep (se 1 (by rfl) ⟨11562866, by rfl⟩ : syracuseStep 15417155 = 23125733) B23125733
theorem B24338339 : Blo 1688044 24338339 := bstep (se 1 (by rfl) ⟨18253754, by rfl⟩ : syracuseStep 24338339 = 36507509) B36507509
theorem B1900507 : Blo 1688044 1900507 := bstep (se 1 (by rfl) ⟨1425380, by rfl⟩ : syracuseStep 1900507 = 2850761) B2850761
theorem B12173321 : Blo 1688044 12173321 := bstep (se 2 (by rfl) ⟨4564995, by rfl⟩ : syracuseStep 12173321 = 9129991) B9129991
theorem B9617561 : Blo 1688044 9617561 := bstep (se 2 (by rfl) ⟨3606585, by rfl⟩ : syracuseStep 9617561 = 7213171) B7213171
theorem B4276435 : Blo 1688044 4276435 := bstep (se 1 (by rfl) ⟨3207326, by rfl⟩ : syracuseStep 4276435 = 6414653) B6414653
theorem B8225027 : Blo 1688044 8225027 := bstep (se 1 (by rfl) ⟨6168770, by rfl⟩ : syracuseStep 8225027 = 12337541) B12337541
theorem B1900831 : Blo 1688044 1900831 := bstep (se 1 (by rfl) ⟨1425623, by rfl⟩ : syracuseStep 1900831 = 2851247) B2851247
theorem B3801455 : Blo 1688044 3801455 := bstep (se 1 (by rfl) ⟨2851091, by rfl⟩ : syracuseStep 3801455 = 5702183) B5702183
theorem B2138491 : Blo 1688044 2138491 := bstep (se 1 (by rfl) ⟨1603868, by rfl⟩ : syracuseStep 2138491 = 3207737) B3207737
theorem B3801527 : Blo 1688044 3801527 := bstep (se 1 (by rfl) ⟨2851145, by rfl⟩ : syracuseStep 3801527 = 5702291) B5702291
theorem B1688059 : Blo 1688044 1688059 := bstep (se 1 (by rfl) ⟨1266044, by rfl⟩ : syracuseStep 1688059 = 2532089) B2532089
theorem B1688127 : Blo 1688044 1688127 := bstep (se 1 (by rfl) ⟨1266095, by rfl⟩ : syracuseStep 1688127 = 2532191) B2532191
theorem B1901119 : Blo 1688044 1901119 := bstep (se 1 (by rfl) ⟨1425839, by rfl⟩ : syracuseStep 1901119 = 2851679) B2851679
theorem B1688135 : Blo 1688044 1688135 := bstep (se 1 (by rfl) ⟨1266101, by rfl⟩ : syracuseStep 1688135 = 2532203) B2532203
theorem B3801671 : Blo 1688044 3801671 := bstep (se 1 (by rfl) ⟨2851253, by rfl⟩ : syracuseStep 3801671 = 5702507) B5702507
theorem B2138719 : Blo 1688044 2138719 := bstep (se 1 (by rfl) ⟨1604039, by rfl⟩ : syracuseStep 2138719 = 3208079) B3208079
theorem B3801707 : Blo 1688044 3801707 := bstep (se 1 (by rfl) ⟨2851280, by rfl⟩ : syracuseStep 3801707 = 5702561) B5702561
theorem B8553113 : Blo 1688044 8553113 := bstep (se 2 (by rfl) ⟨3207417, by rfl⟩ : syracuseStep 8553113 = 6414835) B6414835
theorem B19776203 : Blo 1688044 19776203 := bstep (se 1 (by rfl) ⟨14832152, by rfl⟩ : syracuseStep 19776203 = 29664305) B29664305
theorem B1688287 : Blo 1688044 1688287 := bstep (se 1 (by rfl) ⟨1266215, by rfl⟩ : syracuseStep 1688287 = 2532431) B2532431
theorem B1688367 : Blo 1688044 1688367 := bstep (se 1 (by rfl) ⟨1266275, by rfl⟩ : syracuseStep 1688367 = 2532551) B2532551
theorem B2532251 : Blo 1688044 2532251 := bstep (se 1 (by rfl) ⟨1899188, by rfl⟩ : syracuseStep 2532251 = 3798377) B3798377
theorem B1688475 : Blo 1688044 1688475 := bstep (se 1 (by rfl) ⟨1266356, by rfl⟩ : syracuseStep 1688475 = 2532713) B2532713
theorem B1688527 : Blo 1688044 1688527 := bstep (se 1 (by rfl) ⟨1266395, by rfl⟩ : syracuseStep 1688527 = 2532791) B2532791
theorem B3605467 : Blo 1688044 3605467 := bstep (se 1 (by rfl) ⟨2704100, by rfl⟩ : syracuseStep 3605467 = 5408201) B5408201
theorem B1688551 : Blo 1688044 1688551 := bstep (se 1 (by rfl) ⟨1266413, by rfl⟩ : syracuseStep 1688551 = 2532827) B2532827
theorem B3802103 : Blo 1688044 3802103 := bstep (se 1 (by rfl) ⟨2851577, by rfl⟩ : syracuseStep 3802103 = 5703155) B5703155
theorem B4277387 : Blo 1688044 4277387 := bstep (se 1 (by rfl) ⟨3208040, by rfl⟩ : syracuseStep 4277387 = 6416081) B6416081
theorem B3851497 : Blo 1688044 3851497 := bstep (se 2 (by rfl) ⟨1444311, by rfl⟩ : syracuseStep 3851497 = 2888623) B2888623
theorem B4056313 : Blo 1688044 4056313 := bstep (se 2 (by rfl) ⟨1521117, by rfl⟩ : syracuseStep 4056313 = 3042235) B3042235
theorem B1688863 : Blo 1688044 1688863 := bstep (se 1 (by rfl) ⟨1266647, by rfl⟩ : syracuseStep 1688863 = 2533295) B2533295
theorem B2532647 : Blo 1688044 2532647 := bstep (se 1 (by rfl) ⟨1899485, by rfl⟩ : syracuseStep 2532647 = 3798971) B3798971
theorem B1688923 : Blo 1688044 1688923 := bstep (se 1 (by rfl) ⟨1266692, by rfl⟩ : syracuseStep 1688923 = 2533385) B2533385
theorem B4810079 : Blo 1688044 4810079 := bstep (se 1 (by rfl) ⟨3607559, by rfl⟩ : syracuseStep 4810079 = 7215119) B7215119
theorem B3802463 : Blo 1688044 3802463 := bstep (se 1 (by rfl) ⟨2851847, by rfl⟩ : syracuseStep 3802463 = 5703695) B5703695
theorem B1688943 : Blo 1688044 1688943 := bstep (se 1 (by rfl) ⟨1266707, by rfl⟩ : syracuseStep 1688943 = 2533415) B2533415
theorem B2532731 : Blo 1688044 2532731 := bstep (se 1 (by rfl) ⟨1899548, by rfl⟩ : syracuseStep 2532731 = 3799097) B3799097
theorem B1688999 : Blo 1688044 1688999 := bstep (se 1 (by rfl) ⟨1266749, by rfl⟩ : syracuseStep 1688999 = 2533499) B2533499
theorem B5703101 : Blo 1688044 5703101 := bstep (se 3 (by rfl) ⟨1069331, by rfl⟩ : syracuseStep 5703101 = 2138663) B2138663
theorem B2532857 : Blo 1688044 2532857 := bstep (se 2 (by rfl) ⟨949821, by rfl⟩ : syracuseStep 2532857 = 1899643) B1899643
theorem B2704889 : Blo 1688044 2704889 := bstep (se 2 (by rfl) ⟨1014333, by rfl⟩ : syracuseStep 2704889 = 2028667) B2028667
theorem B1689083 : Blo 1688044 1689083 := bstep (se 1 (by rfl) ⟨1266812, by rfl⟩ : syracuseStep 1689083 = 2533625) B2533625
theorem B1689151 : Blo 1688044 1689151 := bstep (se 1 (by rfl) ⟨1266863, by rfl⟩ : syracuseStep 1689151 = 2533727) B2533727
theorem B1689159 : Blo 1688044 1689159 := bstep (se 1 (by rfl) ⟨1266869, by rfl⟩ : syracuseStep 1689159 = 2533739) B2533739
theorem B4277843 : Blo 1688044 4277843 := bstep (se 1 (by rfl) ⟨3208382, by rfl⟩ : syracuseStep 4277843 = 6416765) B6416765
theorem B2532959 : Blo 1688044 2532959 := bstep (se 1 (by rfl) ⟨1899719, by rfl⟩ : syracuseStep 2532959 = 3799439) B3799439
theorem B7808669 : Blo 1688044 7808669 := bstep (se 3 (by rfl) ⟨1464125, by rfl⟩ : syracuseStep 7808669 = 2928251) B2928251
theorem B1689311 : Blo 1688044 1689311 := bstep (se 1 (by rfl) ⟨1266983, by rfl⟩ : syracuseStep 1689311 = 2533967) B2533967
theorem B1689391 : Blo 1688044 1689391 := bstep (se 1 (by rfl) ⟨1267043, by rfl⟩ : syracuseStep 1689391 = 2534087) B2534087
theorem B1804079 : Blo 1688044 1804079 := bstep (se 1 (by rfl) ⟨1353059, by rfl⟩ : syracuseStep 1804079 = 2706119) B2706119
theorem B2533175 : Blo 1688044 2533175 := bstep (se 1 (by rfl) ⟨1899881, by rfl⟩ : syracuseStep 2533175 = 3799763) B3799763
theorem B3606329 : Blo 1688044 3606329 := bstep (se 2 (by rfl) ⟨1352373, by rfl⟩ : syracuseStep 3606329 = 2704747) B2704747
theorem B5703479 : Blo 1688044 5703479 := bstep (se 1 (by rfl) ⟨4277609, by rfl⟩ : syracuseStep 5703479 = 8555219) B8555219
theorem B10266473 : Blo 1688044 10266473 := bstep (se 2 (by rfl) ⟨3849927, by rfl⟩ : syracuseStep 10266473 = 7699855) B7699855
theorem B1689499 : Blo 1688044 1689499 := bstep (se 1 (by rfl) ⟨1267124, by rfl⟩ : syracuseStep 1689499 = 2534249) B2534249
theorem B1689551 : Blo 1688044 1689551 := bstep (se 1 (by rfl) ⟨1267163, by rfl⟩ : syracuseStep 1689551 = 2534327) B2534327
theorem B1689575 : Blo 1688044 1689575 := bstep (se 1 (by rfl) ⟨1267181, by rfl⟩ : syracuseStep 1689575 = 2534363) B2534363
theorem B2533481 : Blo 1688044 2533481 := bstep (se 2 (by rfl) ⟨950055, by rfl⟩ : syracuseStep 2533481 = 1900111) B1900111
theorem B13691065 : Blo 1688044 13691065 := bstep (se 2 (by rfl) ⟨5134149, by rfl⟩ : syracuseStep 13691065 = 10268299) B10268299
theorem B1689887 : Blo 1688044 1689887 := bstep (se 1 (by rfl) ⟨1267415, by rfl⟩ : syracuseStep 1689887 = 2534831) B2534831
theorem B17328421 : Blo 1688044 17328421 := bstep (se 4 (by rfl) ⟨1624539, by rfl⟩ : syracuseStep 17328421 = 3249079) B3249079
theorem B1689947 : Blo 1688044 1689947 := bstep (se 1 (by rfl) ⟨1267460, by rfl⟩ : syracuseStep 1689947 = 2534921) B2534921
theorem B1689967 : Blo 1688044 1689967 := bstep (se 1 (by rfl) ⟨1267475, by rfl⟩ : syracuseStep 1689967 = 2534951) B2534951
theorem B8554895 : Blo 1688044 8554895 := bstep (se 1 (by rfl) ⟨6416171, by rfl⟩ : syracuseStep 8554895 = 12832343) B12832343
theorem B2533799 : Blo 1688044 2533799 := bstep (se 1 (by rfl) ⟨1900349, by rfl⟩ : syracuseStep 2533799 = 3800699) B3800699
theorem B1690023 : Blo 1688044 1690023 := bstep (se 1 (by rfl) ⟨1267517, by rfl⟩ : syracuseStep 1690023 = 2535035) B2535035
theorem B2533883 : Blo 1688044 2533883 := bstep (se 1 (by rfl) ⟨1900412, by rfl⟩ : syracuseStep 2533883 = 3800825) B3800825
theorem B2534009 : Blo 1688044 2534009 := bstep (se 2 (by rfl) ⟨950253, by rfl⟩ : syracuseStep 2534009 = 1900507) B1900507
theorem B2534063 : Blo 1688044 2534063 := bstep (se 1 (by rfl) ⟨1900547, by rfl⟩ : syracuseStep 2534063 = 3801095) B3801095
theorem B13879997 : Blo 1688044 13879997 := bstep (se 3 (by rfl) ⟨2602499, by rfl⟩ : syracuseStep 13879997 = 5204999) B5204999
theorem B2534111 : Blo 1688044 2534111 := bstep (se 1 (by rfl) ⟨1900583, by rfl⟩ : syracuseStep 2534111 = 3801167) B3801167
theorem B4811663 : Blo 1688044 4811663 := bstep (se 1 (by rfl) ⟨3608747, by rfl⟩ : syracuseStep 4811663 = 7217495) B7217495
theorem B2567143 : Blo 1688044 2567143 := bstep (se 1 (by rfl) ⟨1925357, by rfl⟩ : syracuseStep 2567143 = 3850715) B3850715
theorem B2534375 : Blo 1688044 2534375 := bstep (se 1 (by rfl) ⟨1900781, by rfl⟩ : syracuseStep 2534375 = 3801563) B3801563
theorem B3206135 : Blo 1688044 3206135 := bstep (se 1 (by rfl) ⟨2404601, by rfl⟩ : syracuseStep 3206135 = 4809203) B4809203
theorem B12995599 : Blo 1688044 12995599 := bstep (se 1 (by rfl) ⟨9746699, by rfl⟩ : syracuseStep 12995599 = 19493399) B19493399
theorem B8547443 : Blo 1688044 8547443 := bstep (se 1 (by rfl) ⟨6410582, by rfl⟩ : syracuseStep 8547443 = 12821165) B12821165
theorem B2534633 : Blo 1688044 2534633 := bstep (se 2 (by rfl) ⟨950487, by rfl⟩ : syracuseStep 2534633 = 1900975) B1900975
theorem B2313503 : Blo 1688044 2313503 := bstep (se 1 (by rfl) ⟨1735127, by rfl⟩ : syracuseStep 2313503 = 3470255) B3470255
theorem B2534687 : Blo 1688044 2534687 := bstep (se 1 (by rfl) ⟨1901015, by rfl⟩ : syracuseStep 2534687 = 3802031) B3802031
theorem B3042697 : Blo 1688044 3042697 := bstep (se 2 (by rfl) ⟨1141011, by rfl⟩ : syracuseStep 3042697 = 2282023) B2282023
theorem B3206537 : Blo 1688044 3206537 := bstep (se 2 (by rfl) ⟨1202451, by rfl⟩ : syracuseStep 3206537 = 2404903) B2404903
theorem B3853705 : Blo 1688044 3853705 := bstep (se 2 (by rfl) ⟨1445139, by rfl⟩ : syracuseStep 3853705 = 2890279) B2890279
theorem B2534855 : Blo 1688044 2534855 := bstep (se 1 (by rfl) ⟨1901141, by rfl⟩ : syracuseStep 2534855 = 3802283) B3802283
theorem B12168913 : Blo 1688044 12168913 := bstep (se 2 (by rfl) ⟨4563342, by rfl⟩ : syracuseStep 12168913 = 9126685) B9126685
theorem B54759185 : Blo 1688044 54759185 := bstep (se 2 (by rfl) ⟨20534694, by rfl⟩ : syracuseStep 54759185 = 41069389) B41069389
theorem B62508833 : Blo 1688044 62508833 := bstep (se 2 (by rfl) ⟨23440812, by rfl⟩ : syracuseStep 62508833 = 46881625) B46881625
theorem B7212847 : Blo 1688044 7212847 := bstep (se 1 (by rfl) ⟨5409635, by rfl⟩ : syracuseStep 7212847 = 10819271) B10819271
theorem B8548253 : Blo 1688044 8548253 := bstep (se 3 (by rfl) ⟨1602797, by rfl⟩ : syracuseStep 8548253 = 3205595) B3205595
theorem B19247057 : Blo 1688044 19247057 := bstep (se 2 (by rfl) ⟨7217646, by rfl⟩ : syracuseStep 19247057 = 14435293) B14435293
theorem B6410249 : Blo 1688044 6410249 := bstep (se 2 (by rfl) ⟨2403843, by rfl⟩ : syracuseStep 6410249 = 4807687) B4807687
theorem B1129263119 : Blo 1688044 1129263119 := bstep (se 1 (by rfl) ⟨846947339, by rfl⟩ : syracuseStep 1129263119 = 1693894679) B1693894679
theorem B23113795 : Blo 1688044 23113795 := bstep (se 1 (by rfl) ⟨17335346, by rfl⟩ : syracuseStep 23113795 = 34670693) B34670693
theorem B32534731 : Blo 1688044 32534731 := bstep (se 1 (by rfl) ⟨24401048, by rfl⟩ : syracuseStep 32534731 = 48802097) B48802097
theorem B3207433 : Blo 1688044 3207433 := bstep (se 2 (by rfl) ⟨1202787, by rfl⟩ : syracuseStep 3207433 = 2405575) B2405575
theorem B2929007 : Blo 1688044 2929007 := bstep (se 1 (by rfl) ⟨2196755, by rfl⟩ : syracuseStep 2929007 = 4393511) B4393511
theorem B9621935 : Blo 1688044 9621935 := bstep (se 1 (by rfl) ⟨7216451, by rfl⟩ : syracuseStep 9621935 = 14432903) B14432903
theorem B2281979 : Blo 1688044 2281979 := bstep (se 1 (by rfl) ⟨1711484, by rfl⟩ : syracuseStep 2281979 = 3422969) B3422969
theorem B17338931 : Blo 1688044 17338931 := bstep (se 1 (by rfl) ⟨13004198, by rfl⟩ : syracuseStep 17338931 = 26008397) B26008397
theorem B3658303 : Blo 1688044 3658303 := bstep (se 1 (by rfl) ⟨2743727, by rfl⟩ : syracuseStep 3658303 = 5487455) B5487455
theorem B8549063 : Blo 1688044 8549063 := bstep (se 1 (by rfl) ⟨6411797, by rfl⟩ : syracuseStep 8549063 = 12823595) B12823595
theorem B14430919 : Blo 1688044 14430919 := bstep (se 1 (by rfl) ⟨10823189, by rfl⟩ : syracuseStep 14430919 = 21646379) B21646379
theorem B207942389 : Blo 1688044 207942389 := bstep (se 5 (by rfl) ⟨9747299, by rfl⟩ : syracuseStep 207942389 = 19494599) B19494599
theorem B14423129 : Blo 1688044 14423129 := bstep (se 2 (by rfl) ⟨5408673, by rfl⟩ : syracuseStep 14423129 = 10817347) B10817347
theorem B3798215 : Blo 1688044 3798215 := bstep (se 1 (by rfl) ⟨2848661, by rfl⟩ : syracuseStep 3798215 = 5697323) B5697323
theorem B10278103 : Blo 1688044 10278103 := bstep (se 1 (by rfl) ⟨7708577, by rfl⟩ : syracuseStep 10278103 = 15417155) B15417155
theorem B16225559 : Blo 1688044 16225559 := bstep (se 1 (by rfl) ⟨12169169, by rfl⟩ : syracuseStep 16225559 = 24338339) B24338339
theorem B3798395 : Blo 1688044 3798395 := bstep (se 1 (by rfl) ⟨2848796, by rfl⟩ : syracuseStep 3798395 = 5697593) B5697593
theorem B3798521 : Blo 1688044 3798521 := bstep (se 2 (by rfl) ⟨1424445, by rfl⟩ : syracuseStep 3798521 = 2848891) B2848891
theorem B3798611 : Blo 1688044 3798611 := bstep (se 1 (by rfl) ⟨2848958, by rfl⟩ : syracuseStep 3798611 = 5697917) B5697917
theorem B14431877 : Blo 1688044 14431877 := bstep (se 4 (by rfl) ⟨1352988, by rfl⟩ : syracuseStep 14431877 = 2705977) B2705977
theorem B7214777 : Blo 1688044 7214777 := bstep (se 2 (by rfl) ⟨2705541, by rfl⟩ : syracuseStep 7214777 = 5411083) B5411083
theorem B3798791 : Blo 1688044 3798791 := bstep (se 1 (by rfl) ⟨2849093, by rfl⟩ : syracuseStep 3798791 = 5698187) B5698187
theorem B702199637 : Blo 1688044 702199637 := bstep (se 9 (by rfl) ⟨2057225, by rfl⟩ : syracuseStep 702199637 = 4114451) B4114451
theorem B5412815 : Blo 1688044 5412815 := bstep (se 1 (by rfl) ⟨4059611, by rfl⟩ : syracuseStep 5412815 = 8119223) B8119223
theorem B2471887 : Blo 1688044 2471887 := bstep (se 1 (by rfl) ⟨1853915, by rfl⟩ : syracuseStep 2471887 = 3707831) B3707831
theorem B27400355 : Blo 1688044 27400355 := bstep (se 1 (by rfl) ⟨20550266, by rfl⟩ : syracuseStep 27400355 = 41100533) B41100533
theorem B2849033 : Blo 1688044 2849033 := bstep (se 2 (by rfl) ⟨1068387, by rfl⟩ : syracuseStep 2849033 = 2136775) B2136775
theorem B4274441 : Blo 1688044 4274441 := bstep (se 2 (by rfl) ⟨1602915, by rfl⟩ : syracuseStep 4274441 = 3205831) B3205831
theorem B17332555 : Blo 1688044 17332555 := bstep (se 1 (by rfl) ⟨12999416, by rfl⟩ : syracuseStep 17332555 = 25998833) B25998833
theorem B3799403 : Blo 1688044 3799403 := bstep (se 1 (by rfl) ⟨2849552, by rfl⟩ : syracuseStep 3799403 = 5699105) B5699105
theorem B5700023 : Blo 1688044 5700023 := bstep (se 1 (by rfl) ⟨4275017, by rfl⟩ : syracuseStep 5700023 = 8550035) B8550035
theorem B4807163 : Blo 1688044 4807163 := bstep (se 1 (by rfl) ⟨3605372, by rfl⟩ : syracuseStep 4807163 = 7210745) B7210745
theorem B3799547 : Blo 1688044 3799547 := bstep (se 1 (by rfl) ⟨2849660, by rfl⟩ : syracuseStep 3799547 = 5699321) B5699321
theorem B1899103 : Blo 1688044 1899103 := bstep (se 1 (by rfl) ⟨1424327, by rfl⟩ : syracuseStep 1899103 = 2848655) B2848655
theorem B4274795 : Blo 1688044 4274795 := bstep (se 1 (by rfl) ⟨3206096, by rfl⟩ : syracuseStep 4274795 = 6412193) B6412193
theorem B3799673 : Blo 1688044 3799673 := bstep (se 2 (by rfl) ⟨1424877, by rfl⟩ : syracuseStep 3799673 = 2849755) B2849755
theorem B3799727 : Blo 1688044 3799727 := bstep (se 1 (by rfl) ⟨2849795, by rfl⟩ : syracuseStep 3799727 = 5699591) B5699591
theorem B3250871 : Blo 1688044 3250871 := bstep (se 1 (by rfl) ⟨2438153, by rfl⟩ : syracuseStep 3250871 = 4876307) B4876307
theorem B3799799 : Blo 1688044 3799799 := bstep (se 1 (by rfl) ⟨2849849, by rfl⟩ : syracuseStep 3799799 = 5699699) B5699699
theorem B6503159 : Blo 1688044 6503159 := bstep (se 1 (by rfl) ⟨4877369, by rfl⟩ : syracuseStep 6503159 = 9754739) B9754739
theorem B14424905 : Blo 1688044 14424905 := bstep (se 2 (by rfl) ⟨5409339, by rfl⟩ : syracuseStep 14424905 = 10818679) B10818679
theorem B3799979 : Blo 1688044 3799979 := bstep (se 1 (by rfl) ⟨2849984, by rfl⟩ : syracuseStep 3799979 = 5699969) B5699969
theorem B17578939 : Blo 1688044 17578939 := bstep (se 1 (by rfl) ⟨13184204, by rfl⟩ : syracuseStep 17578939 = 26368409) B26368409
theorem B2850025 : Blo 1688044 2850025 := bstep (se 2 (by rfl) ⟨1068759, by rfl⟩ : syracuseStep 2850025 = 2137519) B2137519
theorem B4275443 : Blo 1688044 4275443 := bstep (se 1 (by rfl) ⟨3206582, by rfl⟩ : syracuseStep 4275443 = 6413165) B6413165
theorem B2850079 : Blo 1688044 2850079 := bstep (se 1 (by rfl) ⟨2137559, by rfl⟩ : syracuseStep 2850079 = 4275119) B4275119
theorem B8551817 : Blo 1688044 8551817 := bstep (se 2 (by rfl) ⟨3206931, by rfl⟩ : syracuseStep 8551817 = 6413863) B6413863
theorem B3800519 : Blo 1688044 3800519 := bstep (se 1 (by rfl) ⟨2850389, by rfl⟩ : syracuseStep 3800519 = 5700779) B5700779
theorem B7699927 : Blo 1688044 7699927 := bstep (se 1 (by rfl) ⟨5774945, by rfl⟩ : syracuseStep 7699927 = 11549891) B11549891
theorem B64953899 : Blo 1688044 64953899 := bstep (se 1 (by rfl) ⟨48715424, by rfl⟩ : syracuseStep 64953899 = 97430849) B97430849
theorem B9625169 : Blo 1688044 9625169 := bstep (se 2 (by rfl) ⟨3609438, by rfl⟩ : syracuseStep 9625169 = 7218877) B7218877
theorem B9256531 : Blo 1688044 9256531 := bstep (se 1 (by rfl) ⟨6942398, by rfl⟩ : syracuseStep 9256531 = 13884797) B13884797
theorem B2850491 : Blo 1688044 2850491 := bstep (se 1 (by rfl) ⟨2137868, by rfl⟩ : syracuseStep 2850491 = 4275737) B4275737
theorem B4275899 : Blo 1688044 4275899 := bstep (se 1 (by rfl) ⟨3206924, by rfl⟩ : syracuseStep 4275899 = 6413849) B6413849
theorem B1900255 : Blo 1688044 1900255 := bstep (se 1 (by rfl) ⟨1425191, by rfl⟩ : syracuseStep 1900255 = 2850383) B2850383
theorem B5136107 : Blo 1688044 5136107 := bstep (se 1 (by rfl) ⟨3852080, by rfl⟩ : syracuseStep 5136107 = 7704161) B7704161
theorem B3424007 : Blo 1688044 3424007 := bstep (se 1 (by rfl) ⟨2568005, by rfl⟩ : syracuseStep 3424007 = 5136011) B5136011
theorem B3800879 : Blo 1688044 3800879 := bstep (se 1 (by rfl) ⟨2850659, by rfl⟩ : syracuseStep 3800879 = 5701319) B5701319
theorem B6414137 : Blo 1688044 6414137 := bstep (se 2 (by rfl) ⟨2405301, by rfl⟩ : syracuseStep 6414137 = 4810603) B4810603
theorem B30818393 : Blo 1688044 30818393 := bstep (se 2 (by rfl) ⟨11556897, by rfl⟩ : syracuseStep 30818393 = 23113795) B23113795
theorem B5701913 : Blo 1688044 5701913 := bstep (se 2 (by rfl) ⟨2138217, by rfl⟩ : syracuseStep 5701913 = 4276435) B4276435
theorem B6414623 : Blo 1688044 6414623 := bstep (se 1 (by rfl) ⟨4810967, by rfl⟩ : syracuseStep 6414623 = 9621935) B9621935
theorem B4276577 : Blo 1688044 4276577 := bstep (se 2 (by rfl) ⟨1603716, by rfl⟩ : syracuseStep 4276577 = 3207433) B3207433
theorem B11559287 : Blo 1688044 11559287 := bstep (se 1 (by rfl) ⟨8669465, by rfl⟩ : syracuseStep 11559287 = 17338931) B17338931
theorem B23110073 : Blo 1688044 23110073 := bstep (se 2 (by rfl) ⟨8666277, by rfl⟩ : syracuseStep 23110073 = 17332555) B17332555
theorem B5702075 : Blo 1688044 5702075 := bstep (se 1 (by rfl) ⟨4276556, by rfl⟩ : syracuseStep 5702075 = 8553113) B8553113
theorem B2851321 : Blo 1688044 2851321 := bstep (se 2 (by rfl) ⟨1069245, by rfl⟩ : syracuseStep 2851321 = 2138491) B2138491
theorem B1688167 : Blo 1688044 1688167 := bstep (se 1 (by rfl) ⟨1266125, by rfl⟩ : syracuseStep 1688167 = 2532251) B2532251
theorem B2851591 : Blo 1688044 2851591 := bstep (se 1 (by rfl) ⟨2138693, by rfl⟩ : syracuseStep 2851591 = 4277387) B4277387
theorem B2532137 : Blo 1688044 2532137 := bstep (se 2 (by rfl) ⟨949551, by rfl⟩ : syracuseStep 2532137 = 1899103) B1899103
theorem B2851625 : Blo 1688044 2851625 := bstep (se 2 (by rfl) ⟨1069359, by rfl⟩ : syracuseStep 2851625 = 2138719) B2138719
theorem B2532143 : Blo 1688044 2532143 := bstep (se 1 (by rfl) ⟨1899107, by rfl⟩ : syracuseStep 2532143 = 3798215) B3798215
theorem B1688431 : Blo 1688044 1688431 := bstep (se 1 (by rfl) ⟨1266323, by rfl⟩ : syracuseStep 1688431 = 2532647) B2532647
theorem B2532263 : Blo 1688044 2532263 := bstep (se 1 (by rfl) ⟨1899197, by rfl⟩ : syracuseStep 2532263 = 3798395) B3798395
theorem B1688487 : Blo 1688044 1688487 := bstep (se 1 (by rfl) ⟨1266365, by rfl⟩ : syracuseStep 1688487 = 2532731) B2532731
theorem B3802067 : Blo 1688044 3802067 := bstep (se 1 (by rfl) ⟨2851550, by rfl⟩ : syracuseStep 3802067 = 5703101) B5703101
theorem B2532347 : Blo 1688044 2532347 := bstep (se 1 (by rfl) ⟨1899260, by rfl⟩ : syracuseStep 2532347 = 3798521) B3798521
theorem B1688571 : Blo 1688044 1688571 := bstep (se 1 (by rfl) ⟨1266428, by rfl⟩ : syracuseStep 1688571 = 2532857) B2532857
theorem B1803259 : Blo 1688044 1803259 := bstep (se 1 (by rfl) ⟨1352444, by rfl⟩ : syracuseStep 1803259 = 2704889) B2704889
theorem B2532407 : Blo 1688044 2532407 := bstep (se 1 (by rfl) ⟨1899305, by rfl⟩ : syracuseStep 2532407 = 3798611) B3798611
theorem B2851895 : Blo 1688044 2851895 := bstep (se 1 (by rfl) ⟨2138921, by rfl⟩ : syracuseStep 2851895 = 4277843) B4277843
theorem B1688639 : Blo 1688044 1688639 := bstep (se 1 (by rfl) ⟨1266479, by rfl⟩ : syracuseStep 1688639 = 2532959) B2532959
theorem B4809851 : Blo 1688044 4809851 := bstep (se 1 (by rfl) ⟨3607388, by rfl⟩ : syracuseStep 4809851 = 7214777) B7214777
theorem B2532527 : Blo 1688044 2532527 := bstep (se 1 (by rfl) ⟨1899395, by rfl⟩ : syracuseStep 2532527 = 3798791) B3798791
theorem B1688783 : Blo 1688044 1688783 := bstep (se 1 (by rfl) ⟨1266587, by rfl⟩ : syracuseStep 1688783 = 2533175) B2533175
theorem B3802319 : Blo 1688044 3802319 := bstep (se 1 (by rfl) ⟨2851739, by rfl⟩ : syracuseStep 3802319 = 5703479) B5703479
theorem B468133091 : Blo 1688044 468133091 := bstep (se 1 (by rfl) ⟨351099818, by rfl⟩ : syracuseStep 468133091 = 702199637) B702199637
theorem B23438585 : Blo 1688044 23438585 := bstep (se 2 (by rfl) ⟨8789469, by rfl⟩ : syracuseStep 23438585 = 17578939) B17578939
theorem B17327465 : Blo 1688044 17327465 := bstep (se 2 (by rfl) ⟨6497799, by rfl⟩ : syracuseStep 17327465 = 12995599) B12995599
theorem B1688987 : Blo 1688044 1688987 := bstep (se 1 (by rfl) ⟨1266740, by rfl⟩ : syracuseStep 1688987 = 2533481) B2533481
theorem B2532935 : Blo 1688044 2532935 := bstep (se 1 (by rfl) ⟨1899701, by rfl⟩ : syracuseStep 2532935 = 3799403) B3799403
theorem B5703263 : Blo 1688044 5703263 := bstep (se 1 (by rfl) ⟨4277447, by rfl⟩ : syracuseStep 5703263 = 8554895) B8554895
theorem B1689199 : Blo 1688044 1689199 := bstep (se 1 (by rfl) ⟨1266899, by rfl⟩ : syracuseStep 1689199 = 2533799) B2533799
theorem B5408417 : Blo 1688044 5408417 := bstep (se 2 (by rfl) ⟨2028156, by rfl⟩ : syracuseStep 5408417 = 4056313) B4056313
theorem B3204775 : Blo 1688044 3204775 := bstep (se 1 (by rfl) ⟨2403581, by rfl⟩ : syracuseStep 3204775 = 4807163) B4807163
theorem B2533031 : Blo 1688044 2533031 := bstep (se 1 (by rfl) ⟨1899773, by rfl⟩ : syracuseStep 2533031 = 3799547) B3799547
theorem B1689255 : Blo 1688044 1689255 := bstep (se 1 (by rfl) ⟨1266941, by rfl⟩ : syracuseStep 1689255 = 2533883) B2533883
theorem B2533115 : Blo 1688044 2533115 := bstep (se 1 (by rfl) ⟨1899836, by rfl⟩ : syracuseStep 2533115 = 3799673) B3799673
theorem B1689339 : Blo 1688044 1689339 := bstep (se 1 (by rfl) ⟨1267004, by rfl⟩ : syracuseStep 1689339 = 2534009) B2534009
theorem B2533151 : Blo 1688044 2533151 := bstep (se 1 (by rfl) ⟨1899863, by rfl⟩ : syracuseStep 2533151 = 3799727) B3799727
theorem B1689375 : Blo 1688044 1689375 := bstep (se 1 (by rfl) ⟨1267031, by rfl⟩ : syracuseStep 1689375 = 2534063) B2534063
theorem B1689407 : Blo 1688044 1689407 := bstep (se 1 (by rfl) ⟨1267055, by rfl⟩ : syracuseStep 1689407 = 2534111) B2534111
theorem B2533199 : Blo 1688044 2533199 := bstep (se 1 (by rfl) ⟨1899899, by rfl⟩ : syracuseStep 2533199 = 3799799) B3799799
theorem B4335439 : Blo 1688044 4335439 := bstep (se 1 (by rfl) ⟨3251579, by rfl⟩ : syracuseStep 4335439 = 6503159) B6503159
theorem B4056929 : Blo 1688044 4056929 := bstep (se 2 (by rfl) ⟨1521348, by rfl⟩ : syracuseStep 4056929 = 3042697) B3042697
theorem B5138273 : Blo 1688044 5138273 := bstep (se 2 (by rfl) ⟨1926852, by rfl⟩ : syracuseStep 5138273 = 3853705) B3853705
theorem B2533319 : Blo 1688044 2533319 := bstep (se 1 (by rfl) ⟨1899989, by rfl⟩ : syracuseStep 2533319 = 3799979) B3799979
theorem B10266569 : Blo 1688044 10266569 := bstep (se 2 (by rfl) ⟨3849963, by rfl⟩ : syracuseStep 10266569 = 7699927) B7699927
theorem B1689583 : Blo 1688044 1689583 := bstep (se 1 (by rfl) ⟨1267187, by rfl⟩ : syracuseStep 1689583 = 2534375) B2534375
theorem B4810877 : Blo 1688044 4810877 := bstep (se 3 (by rfl) ⟨902039, by rfl⟩ : syracuseStep 4810877 = 1804079) B1804079
theorem B1689755 : Blo 1688044 1689755 := bstep (se 1 (by rfl) ⟨1267316, by rfl⟩ : syracuseStep 1689755 = 2534633) B2534633
theorem B1689791 : Blo 1688044 1689791 := bstep (se 1 (by rfl) ⟨1267343, by rfl⟩ : syracuseStep 1689791 = 2534687) B2534687
theorem B2533673 : Blo 1688044 2533673 := bstep (se 2 (by rfl) ⟨950127, by rfl⟩ : syracuseStep 2533673 = 1900255) B1900255
theorem B2533679 : Blo 1688044 2533679 := bstep (se 1 (by rfl) ⟨1900259, by rfl⟩ : syracuseStep 2533679 = 3800519) B3800519
theorem B1689903 : Blo 1688044 1689903 := bstep (se 1 (by rfl) ⟨1267427, by rfl⟩ : syracuseStep 1689903 = 2534855) B2534855
theorem B6416779 : Blo 1688044 6416779 := bstep (se 1 (by rfl) ⟨4812584, by rfl⟩ : syracuseStep 6416779 = 9625169) B9625169
theorem B13183397 : Blo 1688044 13183397 := bstep (se 4 (by rfl) ⟨1235943, by rfl⟩ : syracuseStep 13183397 = 2471887) B2471887
theorem B36506123 : Blo 1688044 36506123 := bstep (se 1 (by rfl) ⟨27379592, by rfl⟩ : syracuseStep 36506123 = 54759185) B54759185
theorem B2533919 : Blo 1688044 2533919 := bstep (se 1 (by rfl) ⟨1900439, by rfl⟩ : syracuseStep 2533919 = 3800879) B3800879
theorem B12831371 : Blo 1688044 12831371 := bstep (se 1 (by rfl) ⟨9623528, by rfl⟩ : syracuseStep 12831371 = 19247057) B19247057
theorem B5483351 : Blo 1688044 5483351 := bstep (se 1 (by rfl) ⟨4112513, by rfl⟩ : syracuseStep 5483351 = 8225027) B8225027
theorem B1952671 : Blo 1688044 1952671 := bstep (se 1 (by rfl) ⟨1464503, by rfl⟩ : syracuseStep 1952671 = 2929007) B2929007
theorem B2534303 : Blo 1688044 2534303 := bstep (se 1 (by rfl) ⟨1900727, by rfl⟩ : syracuseStep 2534303 = 3801455) B3801455
theorem B18254753 : Blo 1688044 18254753 := bstep (se 2 (by rfl) ⟨6845532, by rfl⟩ : syracuseStep 18254753 = 13691065) B13691065
theorem B43379641 : Blo 1688044 43379641 := bstep (se 2 (by rfl) ⟨16267365, by rfl⟩ : syracuseStep 43379641 = 32534731) B32534731
theorem B2534351 : Blo 1688044 2534351 := bstep (se 1 (by rfl) ⟨1900763, by rfl⟩ : syracuseStep 2534351 = 3801527) B3801527
theorem B2534441 : Blo 1688044 2534441 := bstep (se 2 (by rfl) ⟨950415, by rfl⟩ : syracuseStep 2534441 = 1900831) B1900831
theorem B2534447 : Blo 1688044 2534447 := bstep (se 1 (by rfl) ⟨1900835, by rfl⟩ : syracuseStep 2534447 = 3801671) B3801671
theorem B23104561 : Blo 1688044 23104561 := bstep (se 2 (by rfl) ⟨8664210, by rfl⟩ : syracuseStep 23104561 = 17328421) B17328421
theorem B2534471 : Blo 1688044 2534471 := bstep (se 1 (by rfl) ⟨1900853, by rfl⟩ : syracuseStep 2534471 = 3801707) B3801707
theorem B13184135 : Blo 1688044 13184135 := bstep (se 1 (by rfl) ⟨9888101, by rfl⟩ : syracuseStep 13184135 = 19776203) B19776203
theorem B138628259 : Blo 1688044 138628259 := bstep (se 1 (by rfl) ⟨103971194, by rfl⟩ : syracuseStep 138628259 = 207942389) B207942389
theorem B2534735 : Blo 1688044 2534735 := bstep (se 1 (by rfl) ⟨1901051, by rfl⟩ : syracuseStep 2534735 = 3802103) B3802103
theorem B2534825 : Blo 1688044 2534825 := bstep (se 2 (by rfl) ⟨950559, by rfl⟩ : syracuseStep 2534825 = 1901119) B1901119
theorem B10817039 : Blo 1688044 10817039 := bstep (se 1 (by rfl) ⟨8112779, by rfl⟩ : syracuseStep 10817039 = 16225559) B16225559
theorem B3206719 : Blo 1688044 3206719 := bstep (se 1 (by rfl) ⟨2405039, by rfl⟩ : syracuseStep 3206719 = 4810079) B4810079
theorem B2534975 : Blo 1688044 2534975 := bstep (se 1 (by rfl) ⟨1901231, by rfl⟩ : syracuseStep 2534975 = 3802463) B3802463
theorem B9621251 : Blo 1688044 9621251 := bstep (se 1 (by rfl) ⟨7215938, by rfl⟩ : syracuseStep 9621251 = 14431877) B14431877
theorem B5205779 : Blo 1688044 5205779 := bstep (se 1 (by rfl) ⟨3904334, by rfl⟩ : syracuseStep 5205779 = 7808669) B7808669
theorem B98709461 : Blo 1688044 98709461 := bstep (se 7 (by rfl) ⟨1156751, by rfl⟩ : syracuseStep 98709461 = 2313503) B2313503
theorem B3608543 : Blo 1688044 3608543 := bstep (se 1 (by rfl) ⟨2706407, by rfl⟩ : syracuseStep 3608543 = 5412815) B5412815
theorem B2167247 : Blo 1688044 2167247 := bstep (se 1 (by rfl) ⟨1625435, by rfl⟩ : syracuseStep 2167247 = 3250871) B3250871
theorem B9253331 : Blo 1688044 9253331 := bstep (se 1 (by rfl) ⟨6939998, by rfl⟩ : syracuseStep 9253331 = 13879997) B13879997
theorem B3207775 : Blo 1688044 3207775 := bstep (se 1 (by rfl) ⟨2405831, by rfl⟩ : syracuseStep 3207775 = 4811663) B4811663
theorem B5698295 : Blo 1688044 5698295 := bstep (se 1 (by rfl) ⟨4273721, by rfl⟩ : syracuseStep 5698295 = 8547443) B8547443
theorem B12342041 : Blo 1688044 12342041 := bstep (se 2 (by rfl) ⟨4628265, by rfl⟩ : syracuseStep 12342041 = 9256531) B9256531
theorem B16225217 : Blo 1688044 16225217 := bstep (se 2 (by rfl) ⟨6084456, by rfl⟩ : syracuseStep 16225217 = 12168913) B12168913
theorem B2282671 : Blo 1688044 2282671 := bstep (se 1 (by rfl) ⟨1712003, by rfl⟩ : syracuseStep 2282671 = 3424007) B3424007
theorem B5698835 : Blo 1688044 5698835 := bstep (se 1 (by rfl) ⟨4274126, by rfl⟩ : syracuseStep 5698835 = 8548253) B8548253
theorem B4273499 : Blo 1688044 4273499 := bstep (se 1 (by rfl) ⟨3205124, by rfl⟩ : syracuseStep 4273499 = 6410249) B6410249
theorem B8115547 : Blo 1688044 8115547 := bstep (se 1 (by rfl) ⟨6086660, by rfl⟩ : syracuseStep 8115547 = 12173321) B12173321
theorem B752842079 : Blo 1688044 752842079 := bstep (se 1 (by rfl) ⟨564631559, by rfl⟩ : syracuseStep 752842079 = 1129263119) B1129263119
theorem B6411707 : Blo 1688044 6411707 := bstep (se 1 (by rfl) ⟨4808780, by rfl⟩ : syracuseStep 6411707 = 9617561) B9617561
theorem B19510949 : Blo 1688044 19510949 := bstep (se 4 (by rfl) ⟨1829151, by rfl⟩ : syracuseStep 19510949 = 3658303) B3658303
theorem B5699375 : Blo 1688044 5699375 := bstep (se 1 (by rfl) ⟨4274531, by rfl⟩ : syracuseStep 5699375 = 8549063) B8549063
theorem B9615419 : Blo 1688044 9615419 := bstep (se 1 (by rfl) ⟨7211564, by rfl⟩ : syracuseStep 9615419 = 14423129) B14423129
theorem B19241225 : Blo 1688044 19241225 := bstep (se 2 (by rfl) ⟨7215459, by rfl⟩ : syracuseStep 19241225 = 14430919) B14430919
theorem B4807289 : Blo 1688044 4807289 := bstep (se 2 (by rfl) ⟨1802733, by rfl⟩ : syracuseStep 4807289 = 3605467) B3605467
theorem B3422857 : Blo 1688044 3422857 := bstep (se 2 (by rfl) ⟨1283571, by rfl⟩ : syracuseStep 3422857 = 2567143) B2567143
theorem B6085277 : Blo 1688044 6085277 := bstep (se 3 (by rfl) ⟨1140989, by rfl⟩ : syracuseStep 6085277 = 2281979) B2281979
theorem B18266903 : Blo 1688044 18266903 := bstep (se 1 (by rfl) ⟨13700177, by rfl⟩ : syracuseStep 18266903 = 27400355) B27400355
theorem B1899355 : Blo 1688044 1899355 := bstep (se 1 (by rfl) ⟨1424516, by rfl⟩ : syracuseStep 1899355 = 2849033) B2849033
theorem B2849627 : Blo 1688044 2849627 := bstep (se 1 (by rfl) ⟨2137220, by rfl⟩ : syracuseStep 2849627 = 4274441) B4274441
theorem B13704137 : Blo 1688044 13704137 := bstep (se 2 (by rfl) ⟨5139051, by rfl⟩ : syracuseStep 13704137 = 10278103) B10278103
theorem B3800015 : Blo 1688044 3800015 := bstep (se 1 (by rfl) ⟨2850011, by rfl⟩ : syracuseStep 3800015 = 5700023) B5700023
theorem B5135329 : Blo 1688044 5135329 := bstep (se 2 (by rfl) ⟨1925748, by rfl⟩ : syracuseStep 5135329 = 3851497) B3851497
theorem B3800033 : Blo 1688044 3800033 := bstep (se 2 (by rfl) ⟨1425012, by rfl⟩ : syracuseStep 3800033 = 2850025) B2850025
theorem B3800105 : Blo 1688044 3800105 := bstep (se 2 (by rfl) ⟨1425039, by rfl⟩ : syracuseStep 3800105 = 2850079) B2850079
theorem B2849863 : Blo 1688044 2849863 := bstep (se 1 (by rfl) ⟨2137397, by rfl⟩ : syracuseStep 2849863 = 4274795) B4274795
theorem B9616603 : Blo 1688044 9616603 := bstep (se 1 (by rfl) ⟨7212452, by rfl⟩ : syracuseStep 9616603 = 14424905) B14424905
theorem B13696285 : Blo 1688044 13696285 := bstep (se 3 (by rfl) ⟨2568053, by rfl⟩ : syracuseStep 13696285 = 5136107) B5136107
theorem B2137423 : Blo 1688044 2137423 := bstep (se 1 (by rfl) ⟨1603067, by rfl⟩ : syracuseStep 2137423 = 3206135) B3206135
theorem B9616877 : Blo 1688044 9616877 := bstep (se 3 (by rfl) ⟨1803164, by rfl⟩ : syracuseStep 9616877 = 3606329) B3606329
theorem B2850295 : Blo 1688044 2850295 := bstep (se 1 (by rfl) ⟨2137721, by rfl⟩ : syracuseStep 2850295 = 4275443) B4275443
theorem B2137691 : Blo 1688044 2137691 := bstep (se 1 (by rfl) ⟨1603268, by rfl⟩ : syracuseStep 2137691 = 3206537) B3206537
theorem B5701211 : Blo 1688044 5701211 := bstep (se 1 (by rfl) ⟨4275908, by rfl⟩ : syracuseStep 5701211 = 8551817) B8551817
theorem B27377261 : Blo 1688044 27377261 := bstep (se 3 (by rfl) ⟨5133236, by rfl⟩ : syracuseStep 27377261 = 10266473) B10266473
theorem B43302599 : Blo 1688044 43302599 := bstep (se 1 (by rfl) ⟨32476949, by rfl⟩ : syracuseStep 43302599 = 64953899) B64953899
theorem B9617129 : Blo 1688044 9617129 := bstep (se 2 (by rfl) ⟨3606423, by rfl⟩ : syracuseStep 9617129 = 7212847) B7212847
theorem B1900327 : Blo 1688044 1900327 := bstep (se 1 (by rfl) ⟨1425245, by rfl⟩ : syracuseStep 1900327 = 2850491) B2850491
theorem B2850599 : Blo 1688044 2850599 := bstep (se 1 (by rfl) ⟨2137949, by rfl⟩ : syracuseStep 2850599 = 4275899) B4275899
theorem B41672555 : Blo 1688044 41672555 := bstep (se 1 (by rfl) ⟨31254416, by rfl⟩ : syracuseStep 41672555 = 62508833) B62508833
theorem B4276091 : Blo 1688044 4276091 := bstep (se 1 (by rfl) ⟨3207068, by rfl⟩ : syracuseStep 4276091 = 6414137) B6414137
theorem B20545595 : Blo 1688044 20545595 := bstep (se 1 (by rfl) ⟨15409196, by rfl⟩ : syracuseStep 20545595 = 30818393) B30818393
theorem B3801275 : Blo 1688044 3801275 := bstep (se 1 (by rfl) ⟨2850956, by rfl⟩ : syracuseStep 3801275 = 5701913) B5701913
theorem B4276415 : Blo 1688044 4276415 := bstep (se 1 (by rfl) ⟨3207311, by rfl⟩ : syracuseStep 4276415 = 6414623) B6414623
theorem B2851051 : Blo 1688044 2851051 := bstep (se 1 (by rfl) ⟨2138288, by rfl⟩ : syracuseStep 2851051 = 4276577) B4276577
theorem B3801383 : Blo 1688044 3801383 := bstep (se 1 (by rfl) ⟨2851037, by rfl⟩ : syracuseStep 3801383 = 5702075) B5702075
theorem B6168887 : Blo 1688044 6168887 := bstep (se 1 (by rfl) ⟨4626665, by rfl⟩ : syracuseStep 6168887 = 9253331) B9253331
theorem B1688091 : Blo 1688044 1688091 := bstep (se 1 (by rfl) ⟨1266068, by rfl⟩ : syracuseStep 1688091 = 2532137) B2532137
theorem B1901083 : Blo 1688044 1901083 := bstep (se 1 (by rfl) ⟨1425812, by rfl⟩ : syracuseStep 1901083 = 2851625) B2851625
theorem B1688095 : Blo 1688044 1688095 := bstep (se 1 (by rfl) ⟨1266071, by rfl⟩ : syracuseStep 1688095 = 2532143) B2532143
theorem B1688175 : Blo 1688044 1688175 := bstep (se 1 (by rfl) ⟨1266131, by rfl⟩ : syracuseStep 1688175 = 2532263) B2532263
theorem B3801761 : Blo 1688044 3801761 := bstep (se 2 (by rfl) ⟨1425660, by rfl⟩ : syracuseStep 3801761 = 2851321) B2851321
theorem B1688231 : Blo 1688044 1688231 := bstep (se 1 (by rfl) ⟨1266173, by rfl⟩ : syracuseStep 1688231 = 2532347) B2532347
theorem B1688271 : Blo 1688044 1688271 := bstep (se 1 (by rfl) ⟨1266203, by rfl⟩ : syracuseStep 1688271 = 2532407) B2532407
theorem B1901263 : Blo 1688044 1901263 := bstep (se 1 (by rfl) ⟨1425947, by rfl⟩ : syracuseStep 1901263 = 2851895) B2851895
theorem B1688351 : Blo 1688044 1688351 := bstep (se 1 (by rfl) ⟨1266263, by rfl⟩ : syracuseStep 1688351 = 2532527) B2532527
theorem B4277033 : Blo 1688044 4277033 := bstep (se 2 (by rfl) ⟨1603887, by rfl⟩ : syracuseStep 4277033 = 3207775) B3207775
theorem B4563809 : Blo 1688044 4563809 := bstep (se 2 (by rfl) ⟨1711428, by rfl⟩ : syracuseStep 4563809 = 3422857) B3422857
theorem B11551643 : Blo 1688044 11551643 := bstep (se 1 (by rfl) ⟨8663732, by rfl⟩ : syracuseStep 11551643 = 17327465) B17327465
theorem B12174245 : Blo 1688044 12174245 := bstep (se 4 (by rfl) ⟨1141335, by rfl⟩ : syracuseStep 12174245 = 2282671) B2282671
theorem B3802121 : Blo 1688044 3802121 := bstep (se 2 (by rfl) ⟨1425795, by rfl⟩ : syracuseStep 3802121 = 2851591) B2851591
theorem B1688623 : Blo 1688044 1688623 := bstep (se 1 (by rfl) ⟨1266467, by rfl⟩ : syracuseStep 1688623 = 2532935) B2532935
theorem B3802175 : Blo 1688044 3802175 := bstep (se 1 (by rfl) ⟨2851631, by rfl⟩ : syracuseStep 3802175 = 5703263) B5703263
theorem B1688687 : Blo 1688044 1688687 := bstep (se 1 (by rfl) ⟨1266515, by rfl⟩ : syracuseStep 1688687 = 2533031) B2533031
theorem B2532473 : Blo 1688044 2532473 := bstep (se 2 (by rfl) ⟨949677, by rfl⟩ : syracuseStep 2532473 = 1899355) B1899355
theorem B1688743 : Blo 1688044 1688743 := bstep (se 1 (by rfl) ⟨1266557, by rfl⟩ : syracuseStep 1688743 = 2533115) B2533115
theorem B1688767 : Blo 1688044 1688767 := bstep (se 1 (by rfl) ⟨1266575, by rfl⟩ : syracuseStep 1688767 = 2533151) B2533151
theorem B1688799 : Blo 1688044 1688799 := bstep (se 1 (by rfl) ⟨1266599, by rfl⟩ : syracuseStep 1688799 = 2533199) B2533199
theorem B2704619 : Blo 1688044 2704619 := bstep (se 1 (by rfl) ⟨2028464, by rfl⟩ : syracuseStep 2704619 = 4056929) B4056929
theorem B1688879 : Blo 1688044 1688879 := bstep (se 1 (by rfl) ⟨1266659, by rfl⟩ : syracuseStep 1688879 = 2533319) B2533319
theorem B1689115 : Blo 1688044 1689115 := bstep (se 1 (by rfl) ⟨1266836, by rfl⟩ : syracuseStep 1689115 = 2533673) B2533673
theorem B1689119 : Blo 1688044 1689119 := bstep (se 1 (by rfl) ⟨1266839, by rfl⟩ : syracuseStep 1689119 = 2533679) B2533679
theorem B12822137 : Blo 1688044 12822137 := bstep (se 2 (by rfl) ⟨4808301, by rfl⟩ : syracuseStep 12822137 = 9616603) B9616603
theorem B1689279 : Blo 1688044 1689279 := bstep (se 1 (by rfl) ⟨1266959, by rfl⟩ : syracuseStep 1689279 = 2533919) B2533919
theorem B18261713 : Blo 1688044 18261713 := bstep (se 2 (by rfl) ⟨6848142, by rfl⟩ : syracuseStep 18261713 = 13696285) B13696285
theorem B3204859 : Blo 1688044 3204859 := bstep (se 1 (by rfl) ⟨2403644, by rfl⟩ : syracuseStep 3204859 = 4807289) B4807289
theorem B8554247 : Blo 1688044 8554247 := bstep (se 1 (by rfl) ⟨6415685, by rfl⟩ : syracuseStep 8554247 = 12831371) B12831371
theorem B4056851 : Blo 1688044 4056851 := bstep (se 1 (by rfl) ⟨3042638, by rfl⟩ : syracuseStep 4056851 = 6085277) B6085277
theorem B3655567 : Blo 1688044 3655567 := bstep (se 1 (by rfl) ⟨2741675, by rfl⟩ : syracuseStep 3655567 = 5483351) B5483351
theorem B1689535 : Blo 1688044 1689535 := bstep (se 1 (by rfl) ⟨1267151, by rfl⟩ : syracuseStep 1689535 = 2534303) B2534303
theorem B9136091 : Blo 1688044 9136091 := bstep (se 1 (by rfl) ⟨6852068, by rfl⟩ : syracuseStep 9136091 = 13704137) B13704137
theorem B2533343 : Blo 1688044 2533343 := bstep (se 1 (by rfl) ⟨1900007, by rfl⟩ : syracuseStep 2533343 = 3800015) B3800015
theorem B1689567 : Blo 1688044 1689567 := bstep (se 1 (by rfl) ⟨1267175, by rfl⟩ : syracuseStep 1689567 = 2534351) B2534351
theorem B2533355 : Blo 1688044 2533355 := bstep (se 1 (by rfl) ⟨1900016, by rfl⟩ : syracuseStep 2533355 = 3800033) B3800033
theorem B2533403 : Blo 1688044 2533403 := bstep (se 1 (by rfl) ⟨1900052, by rfl⟩ : syracuseStep 2533403 = 3800105) B3800105
theorem B1689627 : Blo 1688044 1689627 := bstep (se 1 (by rfl) ⟨1267220, by rfl⟩ : syracuseStep 1689627 = 2534441) B2534441
theorem B1689631 : Blo 1688044 1689631 := bstep (se 1 (by rfl) ⟨1267223, by rfl⟩ : syracuseStep 1689631 = 2534447) B2534447
theorem B1689647 : Blo 1688044 1689647 := bstep (se 1 (by rfl) ⟨1267235, by rfl⟩ : syracuseStep 1689647 = 2534471) B2534471
theorem B1689823 : Blo 1688044 1689823 := bstep (se 1 (by rfl) ⟨1267367, by rfl⟩ : syracuseStep 1689823 = 2534735) B2534735
theorem B1689883 : Blo 1688044 1689883 := bstep (se 1 (by rfl) ⟨1267412, by rfl⟩ : syracuseStep 1689883 = 2534825) B2534825
theorem B7211359 : Blo 1688044 7211359 := bstep (se 1 (by rfl) ⟨5408519, by rfl⟩ : syracuseStep 7211359 = 10817039) B10817039
theorem B1689983 : Blo 1688044 1689983 := bstep (se 1 (by rfl) ⟨1267487, by rfl⟩ : syracuseStep 1689983 = 2534975) B2534975
theorem B2533769 : Blo 1688044 2533769 := bstep (se 2 (by rfl) ⟨950163, by rfl⟩ : syracuseStep 2533769 = 1900327) B1900327
theorem B27781703 : Blo 1688044 27781703 := bstep (se 1 (by rfl) ⟨20836277, by rfl⟩ : syracuseStep 27781703 = 41672555) B41672555
theorem B562523093 : Blo 1688044 562523093 := bstep (se 7 (by rfl) ⟨6592067, by rfl⟩ : syracuseStep 562523093 = 13184135) B13184135
theorem B8555705 : Blo 1688044 8555705 := bstep (se 2 (by rfl) ⟨3208389, by rfl⟩ : syracuseStep 8555705 = 6416779) B6416779
theorem B8228027 : Blo 1688044 8228027 := bstep (se 1 (by rfl) ⟨6171020, by rfl⟩ : syracuseStep 8228027 = 12342041) B12342041
theorem B10816811 : Blo 1688044 10816811 := bstep (se 1 (by rfl) ⟨8112608, by rfl⟩ : syracuseStep 10816811 = 16225217) B16225217
theorem B2534711 : Blo 1688044 2534711 := bstep (se 1 (by rfl) ⟨1901033, by rfl⟩ : syracuseStep 2534711 = 3802067) B3802067
theorem B3206567 : Blo 1688044 3206567 := bstep (se 1 (by rfl) ⟨2404925, by rfl⟩ : syracuseStep 3206567 = 4809851) B4809851
theorem B2534879 : Blo 1688044 2534879 := bstep (se 1 (by rfl) ⟨1901159, by rfl⟩ : syracuseStep 2534879 = 3802319) B3802319
theorem B15625723 : Blo 1688044 15625723 := bstep (se 1 (by rfl) ⟨11719292, by rfl⟩ : syracuseStep 15625723 = 23438585) B23438585
theorem B501894719 : Blo 1688044 501894719 := bstep (se 1 (by rfl) ⟨376421039, by rfl⟩ : syracuseStep 501894719 = 752842079) B752842079
theorem B5779325 : Blo 1688044 5779325 := bstep (se 3 (by rfl) ⟨1083623, by rfl⟩ : syracuseStep 5779325 = 2167247) B2167247
theorem B57839521 : Blo 1688044 57839521 := bstep (se 2 (by rfl) ⟨21689820, by rfl⟩ : syracuseStep 57839521 = 43379641) B43379641
theorem B6844379 : Blo 1688044 6844379 := bstep (se 1 (by rfl) ⟨5133284, by rfl⟩ : syracuseStep 6844379 = 10266569) B10266569
theorem B2404345 : Blo 1688044 2404345 := bstep (se 2 (by rfl) ⟨901629, by rfl⟩ : syracuseStep 2404345 = 1803259) B1803259
theorem B6410279 : Blo 1688044 6410279 := bstep (se 1 (by rfl) ⟨4807709, by rfl⟩ : syracuseStep 6410279 = 9615419) B9615419
theorem B30806081 : Blo 1688044 30806081 := bstep (se 2 (by rfl) ⟨11552280, by rfl⟩ : syracuseStep 30806081 = 23104561) B23104561
theorem B3207251 : Blo 1688044 3207251 := bstep (se 1 (by rfl) ⟨2405438, by rfl⟩ : syracuseStep 3207251 = 4810877) B4810877
theorem B14422445 : Blo 1688044 14422445 := bstep (se 3 (by rfl) ⟨2704208, by rfl⟩ : syracuseStep 14422445 = 5408417) B5408417
theorem B12177935 : Blo 1688044 12177935 := bstep (se 1 (by rfl) ⟨9133451, by rfl⟩ : syracuseStep 12177935 = 18266903) B18266903
theorem B12169835 : Blo 1688044 12169835 := bstep (se 1 (by rfl) ⟨9127376, by rfl⟩ : syracuseStep 12169835 = 18254753) B18254753
theorem B92418839 : Blo 1688044 92418839 := bstep (se 1 (by rfl) ⟨69314129, by rfl⟩ : syracuseStep 92418839 = 138628259) B138628259
theorem B4273033 : Blo 1688044 4273033 := bstep (se 2 (by rfl) ⟨1602387, by rfl⟩ : syracuseStep 4273033 = 3204775) B3204775
theorem B13702061 : Blo 1688044 13702061 := bstep (se 3 (by rfl) ⟨2569136, by rfl⟩ : syracuseStep 13702061 = 5138273) B5138273
theorem B6411251 : Blo 1688044 6411251 := bstep (se 1 (by rfl) ⟨4808438, by rfl⟩ : syracuseStep 6411251 = 9616877) B9616877
theorem B5780585 : Blo 1688044 5780585 := bstep (se 2 (by rfl) ⟨2167719, by rfl⟩ : syracuseStep 5780585 = 4335439) B4335439
theorem B6411419 : Blo 1688044 6411419 := bstep (se 1 (by rfl) ⟨4808564, by rfl⟩ : syracuseStep 6411419 = 9617129) B9617129
theorem B3470519 : Blo 1688044 3470519 := bstep (se 1 (by rfl) ⟨2602889, by rfl⟩ : syracuseStep 3470519 = 5205779) B5205779
theorem B2405695 : Blo 1688044 2405695 := bstep (se 1 (by rfl) ⟨1804271, by rfl⟩ : syracuseStep 2405695 = 3608543) B3608543
theorem B7706191 : Blo 1688044 7706191 := bstep (se 1 (by rfl) ⟨5779643, by rfl⟩ : syracuseStep 7706191 = 11559287) B11559287
theorem B15406715 : Blo 1688044 15406715 := bstep (se 1 (by rfl) ⟨11555036, by rfl⟩ : syracuseStep 15406715 = 23110073) B23110073
theorem B3798863 : Blo 1688044 3798863 := bstep (se 1 (by rfl) ⟨2849147, by rfl⟩ : syracuseStep 3798863 = 5698295) B5698295
theorem B312088727 : Blo 1688044 312088727 := bstep (se 1 (by rfl) ⟨234066545, by rfl⟩ : syracuseStep 312088727 = 468133091) B468133091
theorem B3799223 : Blo 1688044 3799223 := bstep (se 1 (by rfl) ⟨2849417, by rfl⟩ : syracuseStep 3799223 = 5698835) B5698835
theorem B2848999 : Blo 1688044 2848999 := bstep (se 1 (by rfl) ⟨2136749, by rfl⟩ : syracuseStep 2848999 = 4273499) B4273499
theorem B4274471 : Blo 1688044 4274471 := bstep (se 1 (by rfl) ⟨3205853, by rfl⟩ : syracuseStep 4274471 = 6411707) B6411707
theorem B13007299 : Blo 1688044 13007299 := bstep (se 1 (by rfl) ⟨9755474, by rfl⟩ : syracuseStep 13007299 = 19510949) B19510949
theorem B3799583 : Blo 1688044 3799583 := bstep (se 1 (by rfl) ⟨2849687, by rfl⟩ : syracuseStep 3799583 = 5699375) B5699375
theorem B2603561 : Blo 1688044 2603561 := bstep (se 2 (by rfl) ⟨976335, by rfl⟩ : syracuseStep 2603561 = 1952671) B1952671
theorem B6847105 : Blo 1688044 6847105 := bstep (se 2 (by rfl) ⟨2567664, by rfl⟩ : syracuseStep 6847105 = 5135329) B5135329
theorem B3799817 : Blo 1688044 3799817 := bstep (se 2 (by rfl) ⟨1424931, by rfl⟩ : syracuseStep 3799817 = 2849863) B2849863
theorem B12827483 : Blo 1688044 12827483 := bstep (se 1 (by rfl) ⟨9620612, by rfl⟩ : syracuseStep 12827483 = 19241225) B19241225
theorem B5700509 : Blo 1688044 5700509 := bstep (se 3 (by rfl) ⟨1068845, by rfl⟩ : syracuseStep 5700509 = 2137691) B2137691
theorem B8788931 : Blo 1688044 8788931 := bstep (se 1 (by rfl) ⟨6591698, by rfl⟩ : syracuseStep 8788931 = 13183397) B13183397
theorem B24337415 : Blo 1688044 24337415 := bstep (se 1 (by rfl) ⟨18253061, by rfl⟩ : syracuseStep 24337415 = 36506123) B36506123
theorem B2849897 : Blo 1688044 2849897 := bstep (se 2 (by rfl) ⟨1068711, by rfl⟩ : syracuseStep 2849897 = 2137423) B2137423
theorem B10820729 : Blo 1688044 10820729 := bstep (se 2 (by rfl) ⟨4057773, by rfl⟩ : syracuseStep 10820729 = 8115547) B8115547
theorem B1899751 : Blo 1688044 1899751 := bstep (se 1 (by rfl) ⟨1424813, by rfl⟩ : syracuseStep 1899751 = 2849627) B2849627
theorem B3800393 : Blo 1688044 3800393 := bstep (se 2 (by rfl) ⟨1425147, by rfl⟩ : syracuseStep 3800393 = 2850295) B2850295
theorem B4275625 : Blo 1688044 4275625 := bstep (se 2 (by rfl) ⟨1603359, by rfl⟩ : syracuseStep 4275625 = 3206719) B3206719
theorem B3800807 : Blo 1688044 3800807 := bstep (se 1 (by rfl) ⟨2850605, by rfl⟩ : syracuseStep 3800807 = 5701211) B5701211
theorem B18251507 : Blo 1688044 18251507 := bstep (se 1 (by rfl) ⟨13688630, by rfl⟩ : syracuseStep 18251507 = 27377261) B27377261
theorem B28868399 : Blo 1688044 28868399 := bstep (se 1 (by rfl) ⟨21651299, by rfl⟩ : syracuseStep 28868399 = 43302599) B43302599
theorem B6414167 : Blo 1688044 6414167 := bstep (se 1 (by rfl) ⟨4810625, by rfl⟩ : syracuseStep 6414167 = 9621251) B9621251
theorem B1900399 : Blo 1688044 1900399 := bstep (se 1 (by rfl) ⟨1425299, by rfl⟩ : syracuseStep 1900399 = 2850599) B2850599
theorem B2850727 : Blo 1688044 2850727 := bstep (se 1 (by rfl) ⟨2138045, by rfl⟩ : syracuseStep 2850727 = 4276091) B4276091
theorem B65806307 : Blo 1688044 65806307 := bstep (se 1 (by rfl) ⟨49354730, by rfl⟩ : syracuseStep 65806307 = 98709461) B98709461
theorem B13697063 : Blo 1688044 13697063 := bstep (se 1 (by rfl) ⟨10272797, by rfl⟩ : syracuseStep 13697063 = 20545595) B20545595
theorem B20537387 : Blo 1688044 20537387 := bstep (se 1 (by rfl) ⟨15403040, by rfl⟩ : syracuseStep 20537387 = 30806081) B30806081
theorem B2138167 : Blo 1688044 2138167 := bstep (se 1 (by rfl) ⟨1603625, by rfl⟩ : syracuseStep 2138167 = 3207251) B3207251
theorem B2850943 : Blo 1688044 2850943 := bstep (se 1 (by rfl) ⟨2138207, by rfl⟩ : syracuseStep 2850943 = 4276415) B4276415
theorem B4112591 : Blo 1688044 4112591 := bstep (se 1 (by rfl) ⟨3084443, by rfl⟩ : syracuseStep 4112591 = 6168887) B6168887
theorem B3801401 : Blo 1688044 3801401 := bstep (se 2 (by rfl) ⟨1425525, by rfl⟩ : syracuseStep 3801401 = 2851051) B2851051
theorem B8118623 : Blo 1688044 8118623 := bstep (se 1 (by rfl) ⟨6088967, by rfl⟩ : syracuseStep 8118623 = 12177935) B12177935
theorem B61612559 : Blo 1688044 61612559 := bstep (se 1 (by rfl) ⟨46209419, by rfl⟩ : syracuseStep 61612559 = 92418839) B92418839
theorem B2851355 : Blo 1688044 2851355 := bstep (se 1 (by rfl) ⟨2138516, by rfl⟩ : syracuseStep 2851355 = 4277033) B4277033
theorem B17343065 : Blo 1688044 17343065 := bstep (se 2 (by rfl) ⟨6503649, by rfl⟩ : syracuseStep 17343065 = 13007299) B13007299
theorem B7701095 : Blo 1688044 7701095 := bstep (se 1 (by rfl) ⟨5775821, by rfl⟩ : syracuseStep 7701095 = 11551643) B11551643
theorem B9134707 : Blo 1688044 9134707 := bstep (se 1 (by rfl) ⟨6851030, by rfl⟩ : syracuseStep 9134707 = 13702061) B13702061
theorem B1688315 : Blo 1688044 1688315 := bstep (se 1 (by rfl) ⟨1266236, by rfl⟩ : syracuseStep 1688315 = 2532473) B2532473
theorem B1803079 : Blo 1688044 1803079 := bstep (se 1 (by rfl) ⟨1352309, by rfl⟩ : syracuseStep 1803079 = 2704619) B2704619
theorem B12174475 : Blo 1688044 12174475 := bstep (se 1 (by rfl) ⟨9130856, by rfl⟩ : syracuseStep 12174475 = 18261713) B18261713
theorem B5702831 : Blo 1688044 5702831 := bstep (se 1 (by rfl) ⟨4277123, by rfl⟩ : syracuseStep 5702831 = 8554247) B8554247
theorem B2532575 : Blo 1688044 2532575 := bstep (se 1 (by rfl) ⟨1899431, by rfl⟩ : syracuseStep 2532575 = 3798863) B3798863
theorem B1688895 : Blo 1688044 1688895 := bstep (se 1 (by rfl) ⟨1266671, by rfl⟩ : syracuseStep 1688895 = 2533343) B2533343
theorem B1688903 : Blo 1688044 1688903 := bstep (se 1 (by rfl) ⟨1266677, by rfl⟩ : syracuseStep 1688903 = 2533355) B2533355
theorem B1688935 : Blo 1688044 1688935 := bstep (se 1 (by rfl) ⟨1266701, by rfl⟩ : syracuseStep 1688935 = 2533403) B2533403
theorem B2532815 : Blo 1688044 2532815 := bstep (se 1 (by rfl) ⟨1899611, by rfl⟩ : syracuseStep 2532815 = 3799223) B3799223
theorem B1689179 : Blo 1688044 1689179 := bstep (se 1 (by rfl) ⟨1266884, by rfl⟩ : syracuseStep 1689179 = 2533769) B2533769
theorem B2533001 : Blo 1688044 2533001 := bstep (se 2 (by rfl) ⟨949875, by rfl⟩ : syracuseStep 2533001 = 1899751) B1899751
theorem B2533055 : Blo 1688044 2533055 := bstep (se 1 (by rfl) ⟨1899791, by rfl⟩ : syracuseStep 2533055 = 3799583) B3799583
theorem B2533211 : Blo 1688044 2533211 := bstep (se 1 (by rfl) ⟨1899908, by rfl⟩ : syracuseStep 2533211 = 3799817) B3799817
theorem B5859287 : Blo 1688044 5859287 := bstep (se 1 (by rfl) ⟨4394465, by rfl⟩ : syracuseStep 5859287 = 8788931) B8788931
theorem B375015395 : Blo 1688044 375015395 := bstep (se 1 (by rfl) ⟨281261546, by rfl⟩ : syracuseStep 375015395 = 562523093) B562523093
theorem B20834297 : Blo 1688044 20834297 := bstep (se 2 (by rfl) ⟨7812861, by rfl⟩ : syracuseStep 20834297 = 15625723) B15625723
theorem B10274921 : Blo 1688044 10274921 := bstep (se 2 (by rfl) ⟨3853095, by rfl⟩ : syracuseStep 10274921 = 7706191) B7706191
theorem B5703803 : Blo 1688044 5703803 := bstep (se 1 (by rfl) ⟨4277852, by rfl⟩ : syracuseStep 5703803 = 8555705) B8555705
theorem B7211207 : Blo 1688044 7211207 := bstep (se 1 (by rfl) ⟨5408405, by rfl⟩ : syracuseStep 7211207 = 10816811) B10816811
theorem B1689807 : Blo 1688044 1689807 := bstep (se 1 (by rfl) ⟨1267355, by rfl⟩ : syracuseStep 1689807 = 2534711) B2534711
theorem B2533595 : Blo 1688044 2533595 := bstep (se 1 (by rfl) ⟨1900196, by rfl⟩ : syracuseStep 2533595 = 3800393) B3800393
theorem B1689919 : Blo 1688044 1689919 := bstep (se 1 (by rfl) ⟨1267439, by rfl⟩ : syracuseStep 1689919 = 2534879) B2534879
theorem B334596479 : Blo 1688044 334596479 := bstep (se 1 (by rfl) ⟨250947359, by rfl⟩ : syracuseStep 334596479 = 501894719) B501894719
theorem B2533865 : Blo 1688044 2533865 := bstep (se 2 (by rfl) ⟨950199, by rfl⟩ : syracuseStep 2533865 = 1900399) B1900399
theorem B2533871 : Blo 1688044 2533871 := bstep (se 1 (by rfl) ⟨1900403, by rfl⟩ : syracuseStep 2533871 = 3800807) B3800807
theorem B12167671 : Blo 1688044 12167671 := bstep (se 1 (by rfl) ⟨9125753, by rfl⟩ : syracuseStep 12167671 = 18251507) B18251507
theorem B19245599 : Blo 1688044 19245599 := bstep (se 1 (by rfl) ⟨14434199, by rfl⟩ : syracuseStep 19245599 = 28868399) B28868399
theorem B3852883 : Blo 1688044 3852883 := bstep (se 1 (by rfl) ⟨2889662, by rfl⟩ : syracuseStep 3852883 = 5779325) B5779325
theorem B43870871 : Blo 1688044 43870871 := bstep (se 1 (by rfl) ⟨32903153, by rfl⟩ : syracuseStep 43870871 = 65806307) B65806307
theorem B3205793 : Blo 1688044 3205793 := bstep (se 2 (by rfl) ⟨1202172, by rfl⟩ : syracuseStep 3205793 = 2404345) B2404345
theorem B2534183 : Blo 1688044 2534183 := bstep (se 1 (by rfl) ⟨1900637, by rfl⟩ : syracuseStep 2534183 = 3801275) B3801275
theorem B2534255 : Blo 1688044 2534255 := bstep (se 1 (by rfl) ⟨1900691, by rfl⟩ : syracuseStep 2534255 = 3801383) B3801383
theorem B28855277 : Blo 1688044 28855277 := bstep (se 3 (by rfl) ⟨5410364, by rfl⟩ : syracuseStep 28855277 = 10820729) B10820729
theorem B832236605 : Blo 1688044 832236605 := bstep (se 3 (by rfl) ⟨156044363, by rfl⟩ : syracuseStep 832236605 = 312088727) B312088727
theorem B8113223 : Blo 1688044 8113223 := bstep (se 1 (by rfl) ⟨6084917, by rfl⟩ : syracuseStep 8113223 = 12169835) B12169835
theorem B2534507 : Blo 1688044 2534507 := bstep (se 1 (by rfl) ⟨1900880, by rfl⟩ : syracuseStep 2534507 = 3801761) B3801761
theorem B21941405 : Blo 1688044 21941405 := bstep (se 3 (by rfl) ⟨4114013, by rfl⟩ : syracuseStep 21941405 = 8228027) B8228027
theorem B3042539 : Blo 1688044 3042539 := bstep (se 1 (by rfl) ⟨2281904, by rfl⟩ : syracuseStep 3042539 = 4563809) B4563809
theorem B2534747 : Blo 1688044 2534747 := bstep (se 1 (by rfl) ⟨1901060, by rfl⟩ : syracuseStep 2534747 = 3802121) B3802121
theorem B2534777 : Blo 1688044 2534777 := bstep (se 2 (by rfl) ⟨950541, by rfl⟩ : syracuseStep 2534777 = 1901083) B1901083
theorem B2534783 : Blo 1688044 2534783 := bstep (se 1 (by rfl) ⟨1901087, by rfl⟩ : syracuseStep 2534783 = 3802175) B3802175
theorem B2313679 : Blo 1688044 2313679 := bstep (se 1 (by rfl) ⟨1735259, by rfl⟩ : syracuseStep 2313679 = 3470519) B3470519
theorem B9129473 : Blo 1688044 9129473 := bstep (se 2 (by rfl) ⟨3423552, by rfl⟩ : syracuseStep 9129473 = 6847105) B6847105
theorem B2535017 : Blo 1688044 2535017 := bstep (se 2 (by rfl) ⟨950631, by rfl⟩ : syracuseStep 2535017 = 1901263) B1901263
theorem B8548091 : Blo 1688044 8548091 := bstep (se 1 (by rfl) ⟨6411068, by rfl⟩ : syracuseStep 8548091 = 12822137) B12822137
theorem B5697377 : Blo 1688044 5697377 := bstep (se 2 (by rfl) ⟨2136516, by rfl⟩ : syracuseStep 5697377 = 4273033) B4273033
theorem B6090727 : Blo 1688044 6090727 := bstep (se 1 (by rfl) ⟨4568045, by rfl⟩ : syracuseStep 6090727 = 9136091) B9136091
theorem B6942829 : Blo 1688044 6942829 := bstep (se 3 (by rfl) ⟨1301780, by rfl⟩ : syracuseStep 6942829 = 2603561) B2603561
theorem B3207593 : Blo 1688044 3207593 := bstep (se 2 (by rfl) ⟨1202847, by rfl⟩ : syracuseStep 3207593 = 2405695) B2405695
theorem B16224943 : Blo 1688044 16224943 := bstep (se 1 (by rfl) ⟨12168707, by rfl⟩ : syracuseStep 16224943 = 24337415) B24337415
theorem B10818269 : Blo 1688044 10818269 := bstep (se 3 (by rfl) ⟨2028425, by rfl⟩ : syracuseStep 10818269 = 4056851) B4056851
theorem B4273145 : Blo 1688044 4273145 := bstep (se 2 (by rfl) ⟨1602429, by rfl⟩ : syracuseStep 4273145 = 3204859) B3204859
theorem B4273519 : Blo 1688044 4273519 := bstep (se 1 (by rfl) ⟨3205139, by rfl⟩ : syracuseStep 4273519 = 6410279) B6410279
theorem B15414893 : Blo 1688044 15414893 := bstep (se 3 (by rfl) ⟨2890292, by rfl⟩ : syracuseStep 15414893 = 5780585) B5780585
theorem B9614963 : Blo 1688044 9614963 := bstep (se 1 (by rfl) ⟨7211222, by rfl⟩ : syracuseStep 9614963 = 14422445) B14422445
theorem B3798665 : Blo 1688044 3798665 := bstep (se 2 (by rfl) ⟨1424499, by rfl⟩ : syracuseStep 3798665 = 2848999) B2848999
theorem B9615145 : Blo 1688044 9615145 := bstep (se 2 (by rfl) ⟨3605679, by rfl⟩ : syracuseStep 9615145 = 7211359) B7211359
theorem B8116163 : Blo 1688044 8116163 := bstep (se 1 (by rfl) ⟨6087122, by rfl⟩ : syracuseStep 8116163 = 12174245) B12174245
theorem B4274167 : Blo 1688044 4274167 := bstep (se 1 (by rfl) ⟨3205625, by rfl⟩ : syracuseStep 4274167 = 6411251) B6411251
theorem B4274279 : Blo 1688044 4274279 := bstep (se 1 (by rfl) ⟨3205709, by rfl⟩ : syracuseStep 4274279 = 6411419) B6411419
theorem B10271143 : Blo 1688044 10271143 := bstep (se 1 (by rfl) ⟨7703357, by rfl⟩ : syracuseStep 10271143 = 15406715) B15406715
theorem B8550845 : Blo 1688044 8550845 := bstep (se 3 (by rfl) ⟨1603283, by rfl⟩ : syracuseStep 8550845 = 3206567) B3206567
theorem B2849647 : Blo 1688044 2849647 := bstep (se 1 (by rfl) ⟨2137235, by rfl⟩ : syracuseStep 2849647 = 4274471) B4274471
theorem B18521135 : Blo 1688044 18521135 := bstep (se 1 (by rfl) ⟨13890851, by rfl⟩ : syracuseStep 18521135 = 27781703) B27781703
theorem B5700833 : Blo 1688044 5700833 := bstep (se 2 (by rfl) ⟨2137812, by rfl⟩ : syracuseStep 5700833 = 4275625) B4275625
theorem B8551655 : Blo 1688044 8551655 := bstep (se 1 (by rfl) ⟨6413741, by rfl⟩ : syracuseStep 8551655 = 12827483) B12827483
theorem B3800339 : Blo 1688044 3800339 := bstep (se 1 (by rfl) ⟨2850254, by rfl⟩ : syracuseStep 3800339 = 5700509) B5700509
theorem B1899931 : Blo 1688044 1899931 := bstep (se 1 (by rfl) ⟨1424948, by rfl⟩ : syracuseStep 1899931 = 2849897) B2849897
theorem B4874089 : Blo 1688044 4874089 := bstep (se 2 (by rfl) ⟨1827783, by rfl⟩ : syracuseStep 4874089 = 3655567) B3655567
theorem B77119361 : Blo 1688044 77119361 := bstep (se 2 (by rfl) ⟨28919760, by rfl⟩ : syracuseStep 77119361 = 57839521) B57839521
theorem B3800969 : Blo 1688044 3800969 := bstep (se 2 (by rfl) ⟨1425363, by rfl⟩ : syracuseStep 3800969 = 2850727) B2850727
theorem B4276111 : Blo 1688044 4276111 := bstep (se 1 (by rfl) ⟨3207083, by rfl⟩ : syracuseStep 4276111 = 6414167) B6414167
theorem B18251677 : Blo 1688044 18251677 := bstep (se 3 (by rfl) ⟨3422189, by rfl⟩ : syracuseStep 18251677 = 6844379) B6844379
theorem B2850889 : Blo 1688044 2850889 := bstep (se 2 (by rfl) ⟨1069083, by rfl⟩ : syracuseStep 2850889 = 2138167) B2138167
theorem B9257105 : Blo 1688044 9257105 := bstep (se 2 (by rfl) ⟨3471414, by rfl⟩ : syracuseStep 9257105 = 6942829) B6942829
theorem B3801257 : Blo 1688044 3801257 := bstep (se 2 (by rfl) ⟨1425471, by rfl⟩ : syracuseStep 3801257 = 2850943) B2850943
theorem B21635261 : Blo 1688044 21635261 := bstep (se 3 (by rfl) ⟨4056611, by rfl⟩ : syracuseStep 21635261 = 8113223) B8113223
theorem B2138395 : Blo 1688044 2138395 := bstep (se 1 (by rfl) ⟨1603796, by rfl⟩ : syracuseStep 2138395 = 3207593) B3207593
theorem B41075039 : Blo 1688044 41075039 := bstep (se 1 (by rfl) ⟨30806279, by rfl⟩ : syracuseStep 41075039 = 61612559) B61612559
theorem B1900903 : Blo 1688044 1900903 := bstep (se 1 (by rfl) ⟨1425677, by rfl⟩ : syracuseStep 1900903 = 2851355) B2851355
theorem B5137177 : Blo 1688044 5137177 := bstep (se 2 (by rfl) ⟨1926441, by rfl⟩ : syracuseStep 5137177 = 3852883) B3852883
theorem B3801887 : Blo 1688044 3801887 := bstep (se 1 (by rfl) ⟨2851415, by rfl⟩ : syracuseStep 3801887 = 5702831) B5702831
theorem B1688383 : Blo 1688044 1688383 := bstep (se 1 (by rfl) ⟨1266287, by rfl⟩ : syracuseStep 1688383 = 2532575) B2532575
theorem B1688543 : Blo 1688044 1688543 := bstep (se 1 (by rfl) ⟨1266407, by rfl⟩ : syracuseStep 1688543 = 2532815) B2532815
theorem B892257277 : Blo 1688044 892257277 := bstep (se 3 (by rfl) ⟨167298239, by rfl⟩ : syracuseStep 892257277 = 334596479) B334596479
theorem B2532443 : Blo 1688044 2532443 := bstep (se 1 (by rfl) ⟨1899332, by rfl⟩ : syracuseStep 2532443 = 3798665) B3798665
theorem B1688667 : Blo 1688044 1688667 := bstep (se 1 (by rfl) ⟨1266500, by rfl⟩ : syracuseStep 1688667 = 2533001) B2533001
theorem B1688703 : Blo 1688044 1688703 := bstep (se 1 (by rfl) ⟨1266527, by rfl⟩ : syracuseStep 1688703 = 2533055) B2533055
theorem B1688807 : Blo 1688044 1688807 := bstep (se 1 (by rfl) ⟨1266605, by rfl⟩ : syracuseStep 1688807 = 2533211) B2533211
theorem B6849947 : Blo 1688044 6849947 := bstep (se 1 (by rfl) ⟨5137460, by rfl⟩ : syracuseStep 6849947 = 10274921) B10274921
theorem B3802535 : Blo 1688044 3802535 := bstep (se 1 (by rfl) ⟨2851901, by rfl⟩ : syracuseStep 3802535 = 5703803) B5703803
theorem B1689063 : Blo 1688044 1689063 := bstep (se 1 (by rfl) ⟨1266797, by rfl⟩ : syracuseStep 1689063 = 2533595) B2533595
theorem B1689243 : Blo 1688044 1689243 := bstep (se 1 (by rfl) ⟨1266932, by rfl⟩ : syracuseStep 1689243 = 2533865) B2533865
theorem B1689247 : Blo 1688044 1689247 := bstep (se 1 (by rfl) ⟨1266935, by rfl⟩ : syracuseStep 1689247 = 2533871) B2533871
theorem B12830399 : Blo 1688044 12830399 := bstep (se 1 (by rfl) ⟨9622799, by rfl⟩ : syracuseStep 12830399 = 19245599) B19245599
theorem B29247247 : Blo 1688044 29247247 := bstep (se 1 (by rfl) ⟨21935435, by rfl⟩ : syracuseStep 29247247 = 43870871) B43870871
theorem B1689455 : Blo 1688044 1689455 := bstep (se 1 (by rfl) ⟨1267091, by rfl⟩ : syracuseStep 1689455 = 2534183) B2534183
theorem B2533241 : Blo 1688044 2533241 := bstep (se 2 (by rfl) ⟨949965, by rfl⟩ : syracuseStep 2533241 = 1899931) B1899931
theorem B1689503 : Blo 1688044 1689503 := bstep (se 1 (by rfl) ⟨1267127, by rfl⟩ : syracuseStep 1689503 = 2534255) B2534255
theorem B19236851 : Blo 1688044 19236851 := bstep (se 1 (by rfl) ⟨14427638, by rfl⟩ : syracuseStep 19236851 = 28855277) B28855277
theorem B12347423 : Blo 1688044 12347423 := bstep (se 1 (by rfl) ⟨9260567, by rfl⟩ : syracuseStep 12347423 = 18521135) B18521135
theorem B1689671 : Blo 1688044 1689671 := bstep (se 1 (by rfl) ⟨1267253, by rfl⟩ : syracuseStep 1689671 = 2534507) B2534507
theorem B2533559 : Blo 1688044 2533559 := bstep (se 1 (by rfl) ⟨1900169, by rfl⟩ : syracuseStep 2533559 = 3800339) B3800339
theorem B1689831 : Blo 1688044 1689831 := bstep (se 1 (by rfl) ⟨1267373, by rfl⟩ : syracuseStep 1689831 = 2534747) B2534747
theorem B1689851 : Blo 1688044 1689851 := bstep (se 1 (by rfl) ⟨1267388, by rfl⟩ : syracuseStep 1689851 = 2534777) B2534777
theorem B1689855 : Blo 1688044 1689855 := bstep (se 1 (by rfl) ⟨1267391, by rfl⟩ : syracuseStep 1689855 = 2534783) B2534783
theorem B1690011 : Blo 1688044 1690011 := bstep (se 1 (by rfl) ⟨1267508, by rfl⟩ : syracuseStep 1690011 = 2535017) B2535017
theorem B6498785 : Blo 1688044 6498785 := bstep (se 2 (by rfl) ⟨2437044, by rfl⟩ : syracuseStep 6498785 = 4874089) B4874089
theorem B2533979 : Blo 1688044 2533979 := bstep (se 1 (by rfl) ⟨1900484, by rfl⟩ : syracuseStep 2533979 = 3800969) B3800969
theorem B8120969 : Blo 1688044 8120969 := bstep (se 2 (by rfl) ⟨3045363, by rfl⟩ : syracuseStep 8120969 = 6090727) B6090727
theorem B13691591 : Blo 1688044 13691591 := bstep (se 1 (by rfl) ⟨10268693, by rfl⟩ : syracuseStep 13691591 = 20537387) B20537387
theorem B2534267 : Blo 1688044 2534267 := bstep (se 1 (by rfl) ⟨1900700, by rfl⟩ : syracuseStep 2534267 = 3801401) B3801401
theorem B11562043 : Blo 1688044 11562043 := bstep (se 1 (by rfl) ⟨8671532, by rfl⟩ : syracuseStep 11562043 = 17343065) B17343065
theorem B7212179 : Blo 1688044 7212179 := bstep (se 1 (by rfl) ⟨5409134, by rfl⟩ : syracuseStep 7212179 = 10818269) B10818269
theorem B16223561 : Blo 1688044 16223561 := bstep (se 2 (by rfl) ⟨6083835, by rfl⟩ : syracuseStep 16223561 = 12167671) B12167671
theorem B10276595 : Blo 1688044 10276595 := bstep (se 1 (by rfl) ⟨7707446, by rfl⟩ : syracuseStep 10276595 = 15414893) B15414893
theorem B6409975 : Blo 1688044 6409975 := bstep (se 1 (by rfl) ⟨4807481, by rfl⟩ : syracuseStep 6409975 = 9614963) B9614963
theorem B5410775 : Blo 1688044 5410775 := bstep (se 1 (by rfl) ⟨4058081, by rfl⟩ : syracuseStep 5410775 = 8116163) B8116163
theorem B13889531 : Blo 1688044 13889531 := bstep (se 1 (by rfl) ⟨10417148, by rfl⟩ : syracuseStep 13889531 = 20834297) B20834297
theorem B16232633 : Blo 1688044 16232633 := bstep (se 2 (by rfl) ⟨6087237, by rfl⟩ : syracuseStep 16232633 = 12174475) B12174475
theorem B5698025 : Blo 1688044 5698025 := bstep (se 2 (by rfl) ⟨2136759, by rfl⟩ : syracuseStep 5698025 = 4273519) B4273519
theorem B3084905 : Blo 1688044 3084905 := bstep (se 2 (by rfl) ⟨1156839, by rfl⟩ : syracuseStep 3084905 = 2313679) B2313679
theorem B554824403 : Blo 1688044 554824403 := bstep (se 1 (by rfl) ⟨416118302, by rfl⟩ : syracuseStep 554824403 = 832236605) B832236605
theorem B14627603 : Blo 1688044 14627603 := bstep (se 1 (by rfl) ⟨10970702, by rfl⟩ : syracuseStep 14627603 = 21941405) B21941405
theorem B2028359 : Blo 1688044 2028359 := bstep (se 1 (by rfl) ⟨1521269, by rfl⟩ : syracuseStep 2028359 = 3042539) B3042539
theorem B5698727 : Blo 1688044 5698727 := bstep (se 1 (by rfl) ⟨4274045, by rfl⟩ : syracuseStep 5698727 = 8548091) B8548091
theorem B24335569 : Blo 1688044 24335569 := bstep (se 2 (by rfl) ⟨9125838, by rfl⟩ : syracuseStep 24335569 = 18251677) B18251677
theorem B3798251 : Blo 1688044 3798251 := bstep (se 1 (by rfl) ⟨2848688, by rfl⟩ : syracuseStep 3798251 = 5697377) B5697377
theorem B5698889 : Blo 1688044 5698889 := bstep (se 2 (by rfl) ⟨2137083, by rfl⟩ : syracuseStep 5698889 = 4274167) B4274167
theorem B9131375 : Blo 1688044 9131375 := bstep (se 1 (by rfl) ⟨6848531, by rfl⟩ : syracuseStep 9131375 = 13697063) B13697063
theorem B5412415 : Blo 1688044 5412415 := bstep (se 1 (by rfl) ⟨4059311, by rfl⟩ : syracuseStep 5412415 = 8118623) B8118623
theorem B10966909 : Blo 1688044 10966909 := bstep (se 3 (by rfl) ⟨2056295, by rfl⟩ : syracuseStep 10966909 = 4112591) B4112591
theorem B2848763 : Blo 1688044 2848763 := bstep (se 1 (by rfl) ⟨2136572, by rfl⟩ : syracuseStep 2848763 = 4273145) B4273145
theorem B12179609 : Blo 1688044 12179609 := bstep (se 2 (by rfl) ⟨4567353, by rfl⟩ : syracuseStep 12179609 = 9134707) B9134707
theorem B21633257 : Blo 1688044 21633257 := bstep (se 2 (by rfl) ⟨8112471, by rfl⟩ : syracuseStep 21633257 = 16224943) B16224943
theorem B3799529 : Blo 1688044 3799529 := bstep (se 2 (by rfl) ⟨1424823, by rfl⟩ : syracuseStep 3799529 = 2849647) B2849647
theorem B3906191 : Blo 1688044 3906191 := bstep (se 1 (by rfl) ⟨2929643, by rfl⟩ : syracuseStep 3906191 = 5859287) B5859287
theorem B250010263 : Blo 1688044 250010263 := bstep (se 1 (by rfl) ⟨187507697, by rfl⟩ : syracuseStep 250010263 = 375015395) B375015395
theorem B2849519 : Blo 1688044 2849519 := bstep (se 1 (by rfl) ⟨2137139, by rfl⟩ : syracuseStep 2849519 = 4274279) B4274279
theorem B4807471 : Blo 1688044 4807471 := bstep (se 1 (by rfl) ⟨3605603, by rfl⟩ : syracuseStep 4807471 = 7211207) B7211207
theorem B20536253 : Blo 1688044 20536253 := bstep (se 3 (by rfl) ⟨3850547, by rfl⟩ : syracuseStep 20536253 = 7701095) B7701095
theorem B5700563 : Blo 1688044 5700563 := bstep (se 1 (by rfl) ⟨4275422, by rfl⟩ : syracuseStep 5700563 = 8550845) B8550845
theorem B9616421 : Blo 1688044 9616421 := bstep (se 4 (by rfl) ⟨901539, by rfl⟩ : syracuseStep 9616421 = 1803079) B1803079
theorem B2137195 : Blo 1688044 2137195 := bstep (se 1 (by rfl) ⟨1602896, by rfl⟩ : syracuseStep 2137195 = 3205793) B3205793
theorem B3800555 : Blo 1688044 3800555 := bstep (se 1 (by rfl) ⟨2850416, by rfl⟩ : syracuseStep 3800555 = 5700833) B5700833
theorem B5701103 : Blo 1688044 5701103 := bstep (se 1 (by rfl) ⟨4275827, by rfl⟩ : syracuseStep 5701103 = 8551655) B8551655
theorem B54779429 : Blo 1688044 54779429 := bstep (se 4 (by rfl) ⟨5135571, by rfl⟩ : syracuseStep 54779429 = 10271143) B10271143
theorem B6086315 : Blo 1688044 6086315 := bstep (se 1 (by rfl) ⟨4564736, by rfl⟩ : syracuseStep 6086315 = 9129473) B9129473
theorem B12820193 : Blo 1688044 12820193 := bstep (se 2 (by rfl) ⟨4807572, by rfl⟩ : syracuseStep 12820193 = 9615145) B9615145
theorem B5701481 : Blo 1688044 5701481 := bstep (se 2 (by rfl) ⟨2138055, by rfl⟩ : syracuseStep 5701481 = 4276111) B4276111
theorem B51412907 : Blo 1688044 51412907 := bstep (se 1 (by rfl) ⟨38559680, by rfl⟩ : syracuseStep 51412907 = 77119361) B77119361
theorem B3801185 : Blo 1688044 3801185 := bstep (se 2 (by rfl) ⟨1425444, by rfl⟩ : syracuseStep 3801185 = 2850889) B2850889
theorem B10821755 : Blo 1688044 10821755 := bstep (se 1 (by rfl) ⟨8116316, by rfl⟩ : syracuseStep 10821755 = 16232633) B16232633
theorem B2851193 : Blo 1688044 2851193 := bstep (se 2 (by rfl) ⟨1069197, by rfl⟩ : syracuseStep 2851193 = 2138395) B2138395
theorem B2056603 : Blo 1688044 2056603 := bstep (se 1 (by rfl) ⟨1542452, by rfl⟩ : syracuseStep 2056603 = 3084905) B3084905
theorem B1688295 : Blo 1688044 1688295 := bstep (se 1 (by rfl) ⟨1266221, by rfl⟩ : syracuseStep 1688295 = 2532443) B2532443
theorem B2532167 : Blo 1688044 2532167 := bstep (se 1 (by rfl) ⟨1899125, by rfl⟩ : syracuseStep 2532167 = 3798251) B3798251
theorem B6087583 : Blo 1688044 6087583 := bstep (se 1 (by rfl) ⟨4565687, by rfl⟩ : syracuseStep 6087583 = 9131375) B9131375
theorem B6849569 : Blo 1688044 6849569 := bstep (se 2 (by rfl) ⟨2568588, by rfl⟩ : syracuseStep 6849569 = 5137177) B5137177
theorem B8553599 : Blo 1688044 8553599 := bstep (se 1 (by rfl) ⟨6415199, by rfl⟩ : syracuseStep 8553599 = 12830399) B12830399
theorem B1688827 : Blo 1688044 1688827 := bstep (se 1 (by rfl) ⟨1266620, by rfl⟩ : syracuseStep 1688827 = 2533241) B2533241
theorem B1189676369 : Blo 1688044 1189676369 := bstep (se 2 (by rfl) ⟨446128638, by rfl⟩ : syracuseStep 1189676369 = 892257277) B892257277
theorem B8119739 : Blo 1688044 8119739 := bstep (se 1 (by rfl) ⟨6089804, by rfl⟩ : syracuseStep 8119739 = 12179609) B12179609
theorem B1689039 : Blo 1688044 1689039 := bstep (se 1 (by rfl) ⟨1266779, by rfl⟩ : syracuseStep 1689039 = 2533559) B2533559
theorem B2533019 : Blo 1688044 2533019 := bstep (se 1 (by rfl) ⟨1899764, by rfl⟩ : syracuseStep 2533019 = 3799529) B3799529
theorem B1689319 : Blo 1688044 1689319 := bstep (se 1 (by rfl) ⟨1266989, by rfl⟩ : syracuseStep 1689319 = 2533979) B2533979
theorem B9127727 : Blo 1688044 9127727 := bstep (se 1 (by rfl) ⟨6845795, by rfl⟩ : syracuseStep 9127727 = 13691591) B13691591
theorem B1689511 : Blo 1688044 1689511 := bstep (se 1 (by rfl) ⟨1267133, by rfl⟩ : syracuseStep 1689511 = 2534267) B2534267
theorem B13690835 : Blo 1688044 13690835 := bstep (se 1 (by rfl) ⟨10268126, by rfl⟩ : syracuseStep 13690835 = 20536253) B20536253
theorem B5408957 : Blo 1688044 5408957 := bstep (se 3 (by rfl) ⟨1014179, by rfl⟩ : syracuseStep 5408957 = 2028359) B2028359
theorem B10815707 : Blo 1688044 10815707 := bstep (se 1 (by rfl) ⟨8111780, by rfl⟩ : syracuseStep 10815707 = 16223561) B16223561
theorem B2533703 : Blo 1688044 2533703 := bstep (se 1 (by rfl) ⟨1900277, by rfl⟩ : syracuseStep 2533703 = 3800555) B3800555
theorem B8546633 : Blo 1688044 8546633 := bstep (se 2 (by rfl) ⟨3204987, by rfl⟩ : syracuseStep 8546633 = 6409975) B6409975
theorem B38996329 : Blo 1688044 38996329 := bstep (se 2 (by rfl) ⟨14623623, by rfl⟩ : syracuseStep 38996329 = 29247247) B29247247
theorem B4057543 : Blo 1688044 4057543 := bstep (se 1 (by rfl) ⟨3043157, by rfl⟩ : syracuseStep 4057543 = 6086315) B6086315
theorem B8546795 : Blo 1688044 8546795 := bstep (se 1 (by rfl) ⟨6410096, by rfl⟩ : syracuseStep 8546795 = 12820193) B12820193
theorem B6851063 : Blo 1688044 6851063 := bstep (se 1 (by rfl) ⟨5138297, by rfl⟩ : syracuseStep 6851063 = 10276595) B10276595
theorem B3607183 : Blo 1688044 3607183 := bstep (se 1 (by rfl) ⟨2705387, by rfl⟩ : syracuseStep 3607183 = 5410775) B5410775
theorem B9259687 : Blo 1688044 9259687 := bstep (se 1 (by rfl) ⟨6944765, by rfl⟩ : syracuseStep 9259687 = 13889531) B13889531
theorem B6171403 : Blo 1688044 6171403 := bstep (se 1 (by rfl) ⟨4628552, by rfl⟩ : syracuseStep 6171403 = 9257105) B9257105
theorem B2534171 : Blo 1688044 2534171 := bstep (se 1 (by rfl) ⟨1900628, by rfl⟩ : syracuseStep 2534171 = 3801257) B3801257
theorem B2534537 : Blo 1688044 2534537 := bstep (se 2 (by rfl) ⟨950451, by rfl⟩ : syracuseStep 2534537 = 1900903) B1900903
theorem B9751735 : Blo 1688044 9751735 := bstep (se 1 (by rfl) ⟨7313801, by rfl⟩ : syracuseStep 9751735 = 14627603) B14627603
theorem B2534591 : Blo 1688044 2534591 := bstep (se 1 (by rfl) ⟨1900943, by rfl⟩ : syracuseStep 2534591 = 3801887) B3801887
theorem B4566631 : Blo 1688044 4566631 := bstep (se 1 (by rfl) ⟨3424973, by rfl⟩ : syracuseStep 4566631 = 6849947) B6849947
theorem B2535023 : Blo 1688044 2535023 := bstep (se 1 (by rfl) ⟨1901267, by rfl⟩ : syracuseStep 2535023 = 3802535) B3802535
theorem B6409961 : Blo 1688044 6409961 := bstep (se 2 (by rfl) ⟨2403735, by rfl⟩ : syracuseStep 6409961 = 4807471) B4807471
theorem B12824567 : Blo 1688044 12824567 := bstep (se 1 (by rfl) ⟨9618425, by rfl⟩ : syracuseStep 12824567 = 19236851) B19236851
theorem B14422171 : Blo 1688044 14422171 := bstep (se 1 (by rfl) ⟨10816628, by rfl⟩ : syracuseStep 14422171 = 21633257) B21633257
theorem B10416509 : Blo 1688044 10416509 := bstep (se 3 (by rfl) ⟨1953095, by rfl⟩ : syracuseStep 10416509 = 3906191) B3906191
theorem B6410947 : Blo 1688044 6410947 := bstep (se 1 (by rfl) ⟨4808210, by rfl⟩ : syracuseStep 6410947 = 9616421) B9616421
theorem B14423507 : Blo 1688044 14423507 := bstep (se 1 (by rfl) ⟨10817630, by rfl⟩ : syracuseStep 14423507 = 21635261) B21635261
theorem B27383359 : Blo 1688044 27383359 := bstep (se 1 (by rfl) ⟨20537519, by rfl⟩ : syracuseStep 27383359 = 41075039) B41075039
theorem B3798683 : Blo 1688044 3798683 := bstep (se 1 (by rfl) ⟨2849012, by rfl⟩ : syracuseStep 3798683 = 5698025) B5698025
theorem B19232477 : Blo 1688044 19232477 := bstep (se 3 (by rfl) ⟨3606089, by rfl⟩ : syracuseStep 19232477 = 7212179) B7212179
theorem B369882935 : Blo 1688044 369882935 := bstep (se 1 (by rfl) ⟨277412201, by rfl⟩ : syracuseStep 369882935 = 554824403) B554824403
theorem B3799151 : Blo 1688044 3799151 := bstep (se 1 (by rfl) ⟨2849363, by rfl⟩ : syracuseStep 3799151 = 5698727) B5698727
theorem B333347017 : Blo 1688044 333347017 := bstep (se 2 (by rfl) ⟨125005131, by rfl⟩ : syracuseStep 333347017 = 250010263) B250010263
theorem B3799259 : Blo 1688044 3799259 := bstep (se 1 (by rfl) ⟨2849444, by rfl⟩ : syracuseStep 3799259 = 5698889) B5698889
theorem B1899175 : Blo 1688044 1899175 := bstep (se 1 (by rfl) ⟨1424381, by rfl⟩ : syracuseStep 1899175 = 2848763) B2848763
theorem B8231615 : Blo 1688044 8231615 := bstep (se 1 (by rfl) ⟨6173711, by rfl⟩ : syracuseStep 8231615 = 12347423) B12347423
theorem B15416057 : Blo 1688044 15416057 := bstep (se 2 (by rfl) ⟨5781021, by rfl⟩ : syracuseStep 15416057 = 11562043) B11562043
theorem B2849593 : Blo 1688044 2849593 := bstep (se 2 (by rfl) ⟨1068597, by rfl⟩ : syracuseStep 2849593 = 2137195) B2137195
theorem B32447425 : Blo 1688044 32447425 := bstep (se 2 (by rfl) ⟨12167784, by rfl⟩ : syracuseStep 32447425 = 24335569) B24335569
theorem B4332523 : Blo 1688044 4332523 := bstep (se 1 (by rfl) ⟨3249392, by rfl⟩ : syracuseStep 4332523 = 6498785) B6498785
theorem B5413979 : Blo 1688044 5413979 := bstep (se 1 (by rfl) ⟨4060484, by rfl⟩ : syracuseStep 5413979 = 8120969) B8120969
theorem B1899679 : Blo 1688044 1899679 := bstep (se 1 (by rfl) ⟨1424759, by rfl⟩ : syracuseStep 1899679 = 2849519) B2849519
theorem B3800375 : Blo 1688044 3800375 := bstep (se 1 (by rfl) ⟨2850281, by rfl⟩ : syracuseStep 3800375 = 5700563) B5700563
theorem B7216553 : Blo 1688044 7216553 := bstep (se 2 (by rfl) ⟨2706207, by rfl⟩ : syracuseStep 7216553 = 5412415) B5412415
theorem B3800735 : Blo 1688044 3800735 := bstep (se 1 (by rfl) ⟨2850551, by rfl⟩ : syracuseStep 3800735 = 5701103) B5701103
theorem B36519619 : Blo 1688044 36519619 := bstep (se 1 (by rfl) ⟨27389714, by rfl⟩ : syracuseStep 36519619 = 54779429) B54779429
theorem B137101085 : Blo 1688044 137101085 := bstep (se 3 (by rfl) ⟨25706453, by rfl⟩ : syracuseStep 137101085 = 51412907) B51412907
theorem B14622545 : Blo 1688044 14622545 := bstep (se 2 (by rfl) ⟨5483454, by rfl⟩ : syracuseStep 14622545 = 10966909) B10966909
theorem B3800987 : Blo 1688044 3800987 := bstep (se 1 (by rfl) ⟨2850740, by rfl⟩ : syracuseStep 3800987 = 5701481) B5701481
theorem B1900795 : Blo 1688044 1900795 := bstep (se 1 (by rfl) ⟨1425596, by rfl⟩ : syracuseStep 1900795 = 2851193) B2851193
theorem B51995105 : Blo 1688044 51995105 := bstep (se 2 (by rfl) ⟨19498164, by rfl⟩ : syracuseStep 51995105 = 38996329) B38996329
theorem B1688111 : Blo 1688044 1688111 := bstep (se 1 (by rfl) ⟨1266083, by rfl⟩ : syracuseStep 1688111 = 2532167) B2532167
theorem B5702399 : Blo 1688044 5702399 := bstep (se 1 (by rfl) ⟨4276799, by rfl⟩ : syracuseStep 5702399 = 8553599) B8553599
theorem B2532233 : Blo 1688044 2532233 := bstep (se 2 (by rfl) ⟨949587, by rfl⟩ : syracuseStep 2532233 = 1899175) B1899175
theorem B2532455 : Blo 1688044 2532455 := bstep (se 1 (by rfl) ⟨1899341, by rfl⟩ : syracuseStep 2532455 = 3798683) B3798683
theorem B1688679 : Blo 1688044 1688679 := bstep (se 1 (by rfl) ⟨1266509, by rfl⟩ : syracuseStep 1688679 = 2533019) B2533019
theorem B19244141 : Blo 1688044 19244141 := bstep (se 3 (by rfl) ⟨3608276, by rfl⟩ : syracuseStep 19244141 = 7216553) B7216553
theorem B12821651 : Blo 1688044 12821651 := bstep (se 1 (by rfl) ⟨9616238, by rfl⟩ : syracuseStep 12821651 = 19232477) B19232477
theorem B246588623 : Blo 1688044 246588623 := bstep (se 1 (by rfl) ⟨184941467, by rfl⟩ : syracuseStep 246588623 = 369882935) B369882935
theorem B43263233 : Blo 1688044 43263233 := bstep (se 2 (by rfl) ⟨16223712, by rfl⟩ : syracuseStep 43263233 = 32447425) B32447425
theorem B9127223 : Blo 1688044 9127223 := bstep (se 1 (by rfl) ⟨6845417, by rfl⟩ : syracuseStep 9127223 = 13690835) B13690835
theorem B5776697 : Blo 1688044 5776697 := bstep (se 2 (by rfl) ⟨2166261, by rfl⟩ : syracuseStep 5776697 = 4332523) B4332523
theorem B2532767 : Blo 1688044 2532767 := bstep (se 1 (by rfl) ⟨1899575, by rfl⟩ : syracuseStep 2532767 = 3799151) B3799151
theorem B3605971 : Blo 1688044 3605971 := bstep (se 1 (by rfl) ⟨2704478, by rfl⟩ : syracuseStep 3605971 = 5408957) B5408957
theorem B7210471 : Blo 1688044 7210471 := bstep (se 1 (by rfl) ⟨5407853, by rfl⟩ : syracuseStep 7210471 = 10815707) B10815707
theorem B2532839 : Blo 1688044 2532839 := bstep (se 1 (by rfl) ⟨1899629, by rfl⟩ : syracuseStep 2532839 = 3799259) B3799259
theorem B2532905 : Blo 1688044 2532905 := bstep (se 2 (by rfl) ⟨949839, by rfl⟩ : syracuseStep 2532905 = 1899679) B1899679
theorem B1689135 : Blo 1688044 1689135 := bstep (se 1 (by rfl) ⟨1266851, by rfl⟩ : syracuseStep 1689135 = 2533703) B2533703
theorem B1689447 : Blo 1688044 1689447 := bstep (se 1 (by rfl) ⟨1267085, by rfl⟩ : syracuseStep 1689447 = 2534171) B2534171
theorem B1689691 : Blo 1688044 1689691 := bstep (se 1 (by rfl) ⟨1267268, by rfl⟩ : syracuseStep 1689691 = 2534537) B2534537
theorem B1689727 : Blo 1688044 1689727 := bstep (se 1 (by rfl) ⟨1267295, by rfl⟩ : syracuseStep 1689727 = 2534591) B2534591
theorem B6088841 : Blo 1688044 6088841 := bstep (se 2 (by rfl) ⟨2283315, by rfl⟩ : syracuseStep 6088841 = 4566631) B4566631
theorem B2533583 : Blo 1688044 2533583 := bstep (se 1 (by rfl) ⟨1900187, by rfl⟩ : syracuseStep 2533583 = 3800375) B3800375
theorem B1690015 : Blo 1688044 1690015 := bstep (se 1 (by rfl) ⟨1267511, by rfl⟩ : syracuseStep 1690015 = 2535023) B2535023
theorem B2533823 : Blo 1688044 2533823 := bstep (se 1 (by rfl) ⟨1900367, by rfl⟩ : syracuseStep 2533823 = 3800735) B3800735
theorem B91400723 : Blo 1688044 91400723 := bstep (se 1 (by rfl) ⟨68550542, by rfl⟩ : syracuseStep 91400723 = 137101085) B137101085
theorem B2533991 : Blo 1688044 2533991 := bstep (se 1 (by rfl) ⟨1900493, by rfl⟩ : syracuseStep 2533991 = 3800987) B3800987
theorem B2534123 : Blo 1688044 2534123 := bstep (se 1 (by rfl) ⟨1900592, by rfl⟩ : syracuseStep 2534123 = 3801185) B3801185
theorem B19229561 : Blo 1688044 19229561 := bstep (se 2 (by rfl) ⟨7211085, by rfl⟩ : syracuseStep 19229561 = 14422171) B14422171
theorem B14437277 : Blo 1688044 14437277 := bstep (se 3 (by rfl) ⟨2706989, by rfl⟩ : syracuseStep 14437277 = 5413979) B5413979
theorem B19238309 : Blo 1688044 19238309 := bstep (se 4 (by rfl) ⟨1803591, by rfl⟩ : syracuseStep 19238309 = 3607183) B3607183
theorem B49384997 : Blo 1688044 49384997 := bstep (se 4 (by rfl) ⟨4629843, by rfl⟩ : syracuseStep 49384997 = 9259687) B9259687
theorem B3172470317 : Blo 1688044 3172470317 := bstep (se 3 (by rfl) ⟨594838184, by rfl⟩ : syracuseStep 3172470317 = 1189676369) B1189676369
theorem B8547929 : Blo 1688044 8547929 := bstep (se 2 (by rfl) ⟨3205473, by rfl⟩ : syracuseStep 8547929 = 6410947) B6410947
theorem B8228537 : Blo 1688044 8228537 := bstep (se 2 (by rfl) ⟨3085701, by rfl⟩ : syracuseStep 8228537 = 6171403) B6171403
theorem B5697755 : Blo 1688044 5697755 := bstep (se 1 (by rfl) ⟨4273316, by rfl⟩ : syracuseStep 5697755 = 8546633) B8546633
theorem B5697863 : Blo 1688044 5697863 := bstep (se 1 (by rfl) ⟨4273397, by rfl⟩ : syracuseStep 5697863 = 8546795) B8546795
theorem B4567375 : Blo 1688044 4567375 := bstep (se 1 (by rfl) ⟨3425531, by rfl⟩ : syracuseStep 4567375 = 6851063) B6851063
theorem B10277371 : Blo 1688044 10277371 := bstep (se 1 (by rfl) ⟨7708028, by rfl⟩ : syracuseStep 10277371 = 15416057) B15416057
theorem B21640229 : Blo 1688044 21640229 := bstep (se 4 (by rfl) ⟨2028771, by rfl⟩ : syracuseStep 21640229 = 4057543) B4057543
theorem B4273307 : Blo 1688044 4273307 := bstep (se 1 (by rfl) ⟨3204980, by rfl⟩ : syracuseStep 4273307 = 6409961) B6409961
theorem B8549711 : Blo 1688044 8549711 := bstep (se 1 (by rfl) ⟨6412283, by rfl⟩ : syracuseStep 8549711 = 12824567) B12824567
theorem B7214503 : Blo 1688044 7214503 := bstep (se 1 (by rfl) ⟨5410877, by rfl⟩ : syracuseStep 7214503 = 10821755) B10821755
theorem B18265517 : Blo 1688044 18265517 := bstep (se 3 (by rfl) ⟨3424784, by rfl⟩ : syracuseStep 18265517 = 6849569) B6849569
theorem B6944339 : Blo 1688044 6944339 := bstep (se 1 (by rfl) ⟨5208254, by rfl⟩ : syracuseStep 6944339 = 10416509) B10416509
theorem B444462689 : Blo 1688044 444462689 := bstep (se 2 (by rfl) ⟨166673508, by rfl⟩ : syracuseStep 444462689 = 333347017) B333347017
theorem B2742137 : Blo 1688044 2742137 := bstep (se 2 (by rfl) ⟨1028301, by rfl⟩ : syracuseStep 2742137 = 2056603) B2056603
theorem B52009253 : Blo 1688044 52009253 := bstep (se 4 (by rfl) ⟨4875867, by rfl⟩ : syracuseStep 52009253 = 9751735) B9751735
theorem B5413159 : Blo 1688044 5413159 := bstep (se 1 (by rfl) ⟨4059869, by rfl⟩ : syracuseStep 5413159 = 8119739) B8119739
theorem B9615671 : Blo 1688044 9615671 := bstep (se 1 (by rfl) ⟨7211753, by rfl⟩ : syracuseStep 9615671 = 14423507) B14423507
theorem B3799457 : Blo 1688044 3799457 := bstep (se 2 (by rfl) ⟨1424796, by rfl⟩ : syracuseStep 3799457 = 2849593) B2849593
theorem B6085151 : Blo 1688044 6085151 := bstep (se 1 (by rfl) ⟨4563863, by rfl⟩ : syracuseStep 6085151 = 9127727) B9127727
theorem B8116777 : Blo 1688044 8116777 := bstep (se 2 (by rfl) ⟨3043791, by rfl⟩ : syracuseStep 8116777 = 6087583) B6087583
theorem B5487743 : Blo 1688044 5487743 := bstep (se 1 (by rfl) ⟨4115807, by rfl⟩ : syracuseStep 5487743 = 8231615) B8231615
theorem B36511145 : Blo 1688044 36511145 := bstep (se 2 (by rfl) ⟨13691679, by rfl⟩ : syracuseStep 36511145 = 27383359) B27383359
theorem B48692825 : Blo 1688044 48692825 := bstep (se 2 (by rfl) ⟨18259809, by rfl⟩ : syracuseStep 48692825 = 36519619) B36519619
theorem B9748363 : Blo 1688044 9748363 := bstep (se 1 (by rfl) ⟨7311272, by rfl⟩ : syracuseStep 9748363 = 14622545) B14622545
theorem B7217545 : Blo 1688044 7217545 := bstep (se 2 (by rfl) ⟨2706579, by rfl⟩ : syracuseStep 7217545 = 5413159) B5413159
theorem B3801599 : Blo 1688044 3801599 := bstep (se 1 (by rfl) ⟨2851199, by rfl⟩ : syracuseStep 3801599 = 5702399) B5702399
theorem B1688155 : Blo 1688044 1688155 := bstep (se 1 (by rfl) ⟨1266116, by rfl⟩ : syracuseStep 1688155 = 2532233) B2532233
theorem B14426819 : Blo 1688044 14426819 := bstep (se 1 (by rfl) ⟨10820114, by rfl⟩ : syracuseStep 14426819 = 21640229) B21640229
theorem B1688303 : Blo 1688044 1688303 := bstep (se 1 (by rfl) ⟨1266227, by rfl⟩ : syracuseStep 1688303 = 2532455) B2532455
theorem B12829427 : Blo 1688044 12829427 := bstep (se 1 (by rfl) ⟨9622070, by rfl⟩ : syracuseStep 12829427 = 19244141) B19244141
theorem B1688511 : Blo 1688044 1688511 := bstep (se 1 (by rfl) ⟨1266383, by rfl⟩ : syracuseStep 1688511 = 2532767) B2532767
theorem B1688559 : Blo 1688044 1688559 := bstep (se 1 (by rfl) ⟨1266419, by rfl⟩ : syracuseStep 1688559 = 2532839) B2532839
theorem B1688603 : Blo 1688044 1688603 := bstep (se 1 (by rfl) ⟨1266452, by rfl⟩ : syracuseStep 1688603 = 2532905) B2532905
theorem B4629559 : Blo 1688044 4629559 := bstep (se 1 (by rfl) ⟨3472169, by rfl⟩ : syracuseStep 4629559 = 6944339) B6944339
theorem B1828091 : Blo 1688044 1828091 := bstep (se 1 (by rfl) ⟨1371068, by rfl⟩ : syracuseStep 1828091 = 2742137) B2742137
theorem B1689055 : Blo 1688044 1689055 := bstep (se 1 (by rfl) ⟨1266791, by rfl⟩ : syracuseStep 1689055 = 2533583) B2533583
theorem B2532971 : Blo 1688044 2532971 := bstep (se 1 (by rfl) ⟨1899728, by rfl⟩ : syracuseStep 2532971 = 3799457) B3799457
theorem B1689215 : Blo 1688044 1689215 := bstep (se 1 (by rfl) ⟨1266911, by rfl⟩ : syracuseStep 1689215 = 2533823) B2533823
theorem B60933815 : Blo 1688044 60933815 := bstep (se 1 (by rfl) ⟨45700361, by rfl⟩ : syracuseStep 60933815 = 91400723) B91400723
theorem B4056767 : Blo 1688044 4056767 := bstep (se 1 (by rfl) ⟨3042575, by rfl⟩ : syracuseStep 4056767 = 6085151) B6085151
theorem B1689327 : Blo 1688044 1689327 := bstep (se 1 (by rfl) ⟨1266995, by rfl⟩ : syracuseStep 1689327 = 2533991) B2533991
theorem B1689415 : Blo 1688044 1689415 := bstep (se 1 (by rfl) ⟨1267061, by rfl⟩ : syracuseStep 1689415 = 2534123) B2534123
theorem B9619337 : Blo 1688044 9619337 := bstep (se 2 (by rfl) ⟨3607251, by rfl⟩ : syracuseStep 9619337 = 7214503) B7214503
theorem B24340763 : Blo 1688044 24340763 := bstep (se 1 (by rfl) ⟨18255572, by rfl⟩ : syracuseStep 24340763 = 36511145) B36511145
theorem B2114980211 : Blo 1688044 2114980211 := bstep (se 1 (by rfl) ⟨1586235158, by rfl⟩ : syracuseStep 2114980211 = 3172470317) B3172470317
theorem B43289477 : Blo 1688044 43289477 := bstep (se 4 (by rfl) ⟨4058388, by rfl⟩ : syracuseStep 43289477 = 8116777) B8116777
theorem B34663403 : Blo 1688044 34663403 := bstep (se 1 (by rfl) ⟨25997552, by rfl⟩ : syracuseStep 34663403 = 51995105) B51995105
theorem B2534393 : Blo 1688044 2534393 := bstep (se 2 (by rfl) ⟨950397, by rfl⟩ : syracuseStep 2534393 = 1900795) B1900795
theorem B6089833 : Blo 1688044 6089833 := bstep (se 2 (by rfl) ⟨2283687, by rfl⟩ : syracuseStep 6089833 = 4567375) B4567375
theorem B8547767 : Blo 1688044 8547767 := bstep (se 1 (by rfl) ⟨6410825, by rfl⟩ : syracuseStep 8547767 = 12821651) B12821651
theorem B164392415 : Blo 1688044 164392415 := bstep (se 1 (by rfl) ⟨123294311, by rfl⟩ : syracuseStep 164392415 = 246588623) B246588623
theorem B15404525 : Blo 1688044 15404525 := bstep (se 3 (by rfl) ⟨2888348, by rfl⟩ : syracuseStep 15404525 = 5776697) B5776697
theorem B12177011 : Blo 1688044 12177011 := bstep (se 1 (by rfl) ⟨9132758, by rfl⟩ : syracuseStep 12177011 = 18265517) B18265517
theorem B296308459 : Blo 1688044 296308459 := bstep (se 1 (by rfl) ⟨222231344, by rfl⟩ : syracuseStep 296308459 = 444462689) B444462689
theorem B4059227 : Blo 1688044 4059227 := bstep (se 1 (by rfl) ⟨3044420, by rfl⟩ : syracuseStep 4059227 = 6088841) B6088841
theorem B34672835 : Blo 1688044 34672835 := bstep (se 1 (by rfl) ⟨26004626, by rfl⟩ : syracuseStep 34672835 = 52009253) B52009253
theorem B6410447 : Blo 1688044 6410447 := bstep (se 1 (by rfl) ⟨4807835, by rfl⟩ : syracuseStep 6410447 = 9615671) B9615671
theorem B9613961 : Blo 1688044 9613961 := bstep (se 2 (by rfl) ⟨3605235, by rfl⟩ : syracuseStep 9613961 = 7210471) B7210471
theorem B3658495 : Blo 1688044 3658495 := bstep (se 1 (by rfl) ⟨2743871, by rfl⟩ : syracuseStep 3658495 = 5487743) B5487743
theorem B12825539 : Blo 1688044 12825539 := bstep (se 1 (by rfl) ⟨9619154, by rfl⟩ : syracuseStep 12825539 = 19238309) B19238309
theorem B5698619 : Blo 1688044 5698619 := bstep (se 1 (by rfl) ⟨4273964, by rfl⟩ : syracuseStep 5698619 = 8547929) B8547929
theorem B32461883 : Blo 1688044 32461883 := bstep (se 1 (by rfl) ⟨24346412, by rfl⟩ : syracuseStep 32461883 = 48692825) B48692825
theorem B5485691 : Blo 1688044 5485691 := bstep (se 1 (by rfl) ⟨4114268, by rfl⟩ : syracuseStep 5485691 = 8228537) B8228537
theorem B12997817 : Blo 1688044 12997817 := bstep (se 2 (by rfl) ⟨4874181, by rfl⟩ : syracuseStep 12997817 = 9748363) B9748363
theorem B3798503 : Blo 1688044 3798503 := bstep (se 1 (by rfl) ⟨2848877, by rfl⟩ : syracuseStep 3798503 = 5697755) B5697755
theorem B3798575 : Blo 1688044 3798575 := bstep (se 1 (by rfl) ⟨2848931, by rfl⟩ : syracuseStep 3798575 = 5697863) B5697863
theorem B2848871 : Blo 1688044 2848871 := bstep (se 1 (by rfl) ⟨2136653, by rfl⟩ : syracuseStep 2848871 = 4273307) B4273307
theorem B28842155 : Blo 1688044 28842155 := bstep (se 1 (by rfl) ⟨21631616, by rfl⟩ : syracuseStep 28842155 = 43263233) B43263233
theorem B6084815 : Blo 1688044 6084815 := bstep (se 1 (by rfl) ⟨4563611, by rfl⟩ : syracuseStep 6084815 = 9127223) B9127223
theorem B5699807 : Blo 1688044 5699807 := bstep (se 1 (by rfl) ⟨4274855, by rfl⟩ : syracuseStep 5699807 = 8549711) B8549711
theorem B12819707 : Blo 1688044 12819707 := bstep (se 1 (by rfl) ⟨9614780, by rfl⟩ : syracuseStep 12819707 = 19229561) B19229561
theorem B9624851 : Blo 1688044 9624851 := bstep (se 1 (by rfl) ⟨7218638, by rfl⟩ : syracuseStep 9624851 = 14437277) B14437277
theorem B4807961 : Blo 1688044 4807961 := bstep (se 2 (by rfl) ⟨1802985, by rfl⟩ : syracuseStep 4807961 = 3605971) B3605971
theorem B32923331 : Blo 1688044 32923331 := bstep (se 1 (by rfl) ⟨24692498, by rfl⟩ : syracuseStep 32923331 = 49384997) B49384997
theorem B54812645 : Blo 1688044 54812645 := bstep (se 4 (by rfl) ⟨5138685, by rfl⟩ : syracuseStep 54812645 = 10277371) B10277371
theorem B9617879 : Blo 1688044 9617879 := bstep (se 1 (by rfl) ⟨7213409, by rfl⟩ : syracuseStep 9617879 = 14426819) B14426819
theorem B8552951 : Blo 1688044 8552951 := bstep (se 1 (by rfl) ⟨6414713, by rfl⟩ : syracuseStep 8552951 = 12829427) B12829427
theorem B4874909 : Blo 1688044 4874909 := bstep (se 3 (by rfl) ⟨914045, by rfl⟩ : syracuseStep 4874909 = 1828091) B1828091
theorem B2532335 : Blo 1688044 2532335 := bstep (se 1 (by rfl) ⟨1899251, by rfl⟩ : syracuseStep 2532335 = 3798503) B3798503
theorem B2532383 : Blo 1688044 2532383 := bstep (se 1 (by rfl) ⟨1899287, by rfl⟩ : syracuseStep 2532383 = 3798575) B3798575
theorem B1688647 : Blo 1688044 1688647 := bstep (se 1 (by rfl) ⟨1266485, by rfl⟩ : syracuseStep 1688647 = 2532971) B2532971
theorem B2704511 : Blo 1688044 2704511 := bstep (se 1 (by rfl) ⟨2028383, by rfl⟩ : syracuseStep 2704511 = 4056767) B4056767
theorem B1580311781 : Blo 1688044 1580311781 := bstep (se 4 (by rfl) ⟨148154229, by rfl⟩ : syracuseStep 1580311781 = 296308459) B296308459
theorem B19228103 : Blo 1688044 19228103 := bstep (se 1 (by rfl) ⟨14421077, by rfl⟩ : syracuseStep 19228103 = 28842155) B28842155
theorem B8119777 : Blo 1688044 8119777 := bstep (se 2 (by rfl) ⟨3044916, by rfl⟩ : syracuseStep 8119777 = 6089833) B6089833
theorem B1689595 : Blo 1688044 1689595 := bstep (se 1 (by rfl) ⟨1267196, by rfl⟩ : syracuseStep 1689595 = 2534393) B2534393
theorem B8546471 : Blo 1688044 8546471 := bstep (se 1 (by rfl) ⟨6409853, by rfl⟩ : syracuseStep 8546471 = 12819707) B12819707
theorem B6416567 : Blo 1688044 6416567 := bstep (se 1 (by rfl) ⟨4812425, by rfl⟩ : syracuseStep 6416567 = 9624851) B9624851
theorem B3205307 : Blo 1688044 3205307 := bstep (se 1 (by rfl) ⟨2403980, by rfl⟩ : syracuseStep 3205307 = 4807961) B4807961
theorem B109594943 : Blo 1688044 109594943 := bstep (se 1 (by rfl) ⟨82196207, by rfl⟩ : syracuseStep 109594943 = 164392415) B164392415
theorem B21948887 : Blo 1688044 21948887 := bstep (se 1 (by rfl) ⟨16461665, by rfl⟩ : syracuseStep 21948887 = 32923331) B32923331
theorem B2706151 : Blo 1688044 2706151 := bstep (se 1 (by rfl) ⟨2029613, by rfl⟩ : syracuseStep 2706151 = 4059227) B4059227
theorem B2534399 : Blo 1688044 2534399 := bstep (se 1 (by rfl) ⟨1900799, by rfl⟩ : syracuseStep 2534399 = 3801599) B3801599
theorem B6409307 : Blo 1688044 6409307 := bstep (se 1 (by rfl) ⟨4806980, by rfl⟩ : syracuseStep 6409307 = 9613961) B9613961
theorem B4877993 : Blo 1688044 4877993 := bstep (se 2 (by rfl) ⟨1829247, by rfl⟩ : syracuseStep 4877993 = 3658495) B3658495
theorem B6172745 : Blo 1688044 6172745 := bstep (se 2 (by rfl) ⟨2314779, by rfl⟩ : syracuseStep 6172745 = 4629559) B4629559
theorem B1409986807 : Blo 1688044 1409986807 := bstep (se 1 (by rfl) ⟨1057490105, by rfl⟩ : syracuseStep 1409986807 = 2114980211) B2114980211
theorem B5698511 : Blo 1688044 5698511 := bstep (se 1 (by rfl) ⟨4273883, by rfl⟩ : syracuseStep 5698511 = 8547767) B8547767
theorem B10269683 : Blo 1688044 10269683 := bstep (se 1 (by rfl) ⟨7702262, by rfl⟩ : syracuseStep 10269683 = 15404525) B15404525
theorem B36541763 : Blo 1688044 36541763 := bstep (se 1 (by rfl) ⟨27406322, by rfl⟩ : syracuseStep 36541763 = 54812645) B54812645
theorem B23115223 : Blo 1688044 23115223 := bstep (se 1 (by rfl) ⟨17336417, by rfl⟩ : syracuseStep 23115223 = 34672835) B34672835
theorem B4273631 : Blo 1688044 4273631 := bstep (se 1 (by rfl) ⟨3205223, by rfl⟩ : syracuseStep 4273631 = 6410447) B6410447
theorem B14628509 : Blo 1688044 14628509 := bstep (se 3 (by rfl) ⟨2742845, by rfl⟩ : syracuseStep 14628509 = 5485691) B5485691
theorem B9623393 : Blo 1688044 9623393 := bstep (se 2 (by rfl) ⟨3608772, by rfl⟩ : syracuseStep 9623393 = 7217545) B7217545
theorem B16226173 : Blo 1688044 16226173 := bstep (se 3 (by rfl) ⟨3042407, by rfl⟩ : syracuseStep 16226173 = 6084815) B6084815
theorem B8550359 : Blo 1688044 8550359 := bstep (se 1 (by rfl) ⟨6412769, by rfl⟩ : syracuseStep 8550359 = 12825539) B12825539
theorem B3799079 : Blo 1688044 3799079 := bstep (se 1 (by rfl) ⟨2849309, by rfl⟩ : syracuseStep 3799079 = 5698619) B5698619
theorem B21641255 : Blo 1688044 21641255 := bstep (se 1 (by rfl) ⟨16230941, by rfl⟩ : syracuseStep 21641255 = 32461883) B32461883
theorem B8665211 : Blo 1688044 8665211 := bstep (se 1 (by rfl) ⟨6498908, by rfl⟩ : syracuseStep 8665211 = 12997817) B12997817
theorem B40622543 : Blo 1688044 40622543 := bstep (se 1 (by rfl) ⟨30466907, by rfl⟩ : syracuseStep 40622543 = 60933815) B60933815
theorem B6412891 : Blo 1688044 6412891 := bstep (se 1 (by rfl) ⟨4809668, by rfl⟩ : syracuseStep 6412891 = 9619337) B9619337
theorem B1899247 : Blo 1688044 1899247 := bstep (se 1 (by rfl) ⟨1424435, by rfl⟩ : syracuseStep 1899247 = 2848871) B2848871
theorem B3799871 : Blo 1688044 3799871 := bstep (se 1 (by rfl) ⟨2849903, by rfl⟩ : syracuseStep 3799871 = 5699807) B5699807
theorem B16227175 : Blo 1688044 16227175 := bstep (se 1 (by rfl) ⟨12170381, by rfl⟩ : syracuseStep 16227175 = 24340763) B24340763
theorem B32472029 : Blo 1688044 32472029 := bstep (se 3 (by rfl) ⟨6088505, by rfl⟩ : syracuseStep 32472029 = 12177011) B12177011
theorem B28859651 : Blo 1688044 28859651 := bstep (se 1 (by rfl) ⟨21644738, by rfl⟩ : syracuseStep 28859651 = 43289477) B43289477
theorem B23108935 : Blo 1688044 23108935 := bstep (se 1 (by rfl) ⟨17331701, by rfl⟩ : syracuseStep 23108935 = 34663403) B34663403
theorem B5701967 : Blo 1688044 5701967 := bstep (se 1 (by rfl) ⟨4276475, by rfl⟩ : syracuseStep 5701967 = 8552951) B8552951
theorem B1688223 : Blo 1688044 1688223 := bstep (se 1 (by rfl) ⟨1266167, by rfl⟩ : syracuseStep 1688223 = 2532335) B2532335
theorem B1688255 : Blo 1688044 1688255 := bstep (se 1 (by rfl) ⟨1266191, by rfl⟩ : syracuseStep 1688255 = 2532383) B2532383
theorem B1803007 : Blo 1688044 1803007 := bstep (se 1 (by rfl) ⟨1352255, by rfl⟩ : syracuseStep 1803007 = 2704511) B2704511
theorem B1053541187 : Blo 1688044 1053541187 := bstep (se 1 (by rfl) ⟨790155890, by rfl⟩ : syracuseStep 1053541187 = 1580311781) B1580311781
theorem B2532329 : Blo 1688044 2532329 := bstep (se 2 (by rfl) ⟨949623, by rfl⟩ : syracuseStep 2532329 = 1899247) B1899247
theorem B21636233 : Blo 1688044 21636233 := bstep (se 2 (by rfl) ⟨8113587, by rfl⟩ : syracuseStep 21636233 = 16227175) B16227175
theorem B6415595 : Blo 1688044 6415595 := bstep (se 1 (by rfl) ⟨4811696, by rfl⟩ : syracuseStep 6415595 = 9623393) B9623393
theorem B2532719 : Blo 1688044 2532719 := bstep (se 1 (by rfl) ⟨1899539, by rfl⟩ : syracuseStep 2532719 = 3799079) B3799079
theorem B14427503 : Blo 1688044 14427503 := bstep (se 1 (by rfl) ⟨10820627, by rfl⟩ : syracuseStep 14427503 = 21641255) B21641255
theorem B5776807 : Blo 1688044 5776807 := bstep (se 1 (by rfl) ⟨4332605, by rfl⟩ : syracuseStep 5776807 = 8665211) B8665211
theorem B4277711 : Blo 1688044 4277711 := bstep (se 1 (by rfl) ⟨3208283, by rfl⟩ : syracuseStep 4277711 = 6416567) B6416567
theorem B14632591 : Blo 1688044 14632591 := bstep (se 1 (by rfl) ⟨10974443, by rfl⟩ : syracuseStep 14632591 = 21948887) B21948887
theorem B30811913 : Blo 1688044 30811913 := bstep (se 2 (by rfl) ⟨11554467, by rfl⟩ : syracuseStep 30811913 = 23108935) B23108935
theorem B2533247 : Blo 1688044 2533247 := bstep (se 1 (by rfl) ⟨1899935, by rfl⟩ : syracuseStep 2533247 = 3799871) B3799871
theorem B30820297 : Blo 1688044 30820297 := bstep (se 2 (by rfl) ⟨11557611, by rfl⟩ : syracuseStep 30820297 = 23115223) B23115223
theorem B1689599 : Blo 1688044 1689599 := bstep (se 1 (by rfl) ⟨1267199, by rfl⟩ : syracuseStep 1689599 = 2534399) B2534399
theorem B16460653 : Blo 1688044 16460653 := bstep (se 3 (by rfl) ⟨3086372, by rfl⟩ : syracuseStep 16460653 = 6172745) B6172745
theorem B3608201 : Blo 1688044 3608201 := bstep (se 2 (by rfl) ⟨1353075, by rfl⟩ : syracuseStep 3608201 = 2706151) B2706151
theorem B9752339 : Blo 1688044 9752339 := bstep (se 1 (by rfl) ⟨7314254, by rfl⟩ : syracuseStep 9752339 = 14628509) B14628509
theorem B5697647 : Blo 1688044 5697647 := bstep (se 1 (by rfl) ⟨4273235, by rfl⟩ : syracuseStep 5697647 = 8546471) B8546471
theorem B51999029 : Blo 1688044 51999029 := bstep (se 5 (by rfl) ⟨2437454, by rfl⟩ : syracuseStep 51999029 = 4874909) B4874909
theorem B10826369 : Blo 1688044 10826369 := bstep (se 2 (by rfl) ⟨4059888, by rfl⟩ : syracuseStep 10826369 = 8119777) B8119777
theorem B21648019 : Blo 1688044 21648019 := bstep (se 1 (by rfl) ⟨16236014, by rfl⟩ : syracuseStep 21648019 = 32472029) B32472029
theorem B4272871 : Blo 1688044 4272871 := bstep (se 1 (by rfl) ⟨3204653, by rfl⟩ : syracuseStep 4272871 = 6409307) B6409307
theorem B19239767 : Blo 1688044 19239767 := bstep (se 1 (by rfl) ⟨14429825, by rfl⟩ : syracuseStep 19239767 = 28859651) B28859651
theorem B30079718549 : Blo 1688044 30079718549 := bstep (se 6 (by rfl) ⟨704993403, by rfl⟩ : syracuseStep 30079718549 = 1409986807) B1409986807
theorem B6411919 : Blo 1688044 6411919 := bstep (se 1 (by rfl) ⟨4808939, by rfl⟩ : syracuseStep 6411919 = 9617879) B9617879
theorem B3799007 : Blo 1688044 3799007 := bstep (se 1 (by rfl) ⟨2849255, by rfl⟩ : syracuseStep 3799007 = 5698511) B5698511
theorem B6846455 : Blo 1688044 6846455 := bstep (se 1 (by rfl) ⟨5134841, by rfl⟩ : syracuseStep 6846455 = 10269683) B10269683
theorem B8550521 : Blo 1688044 8550521 := bstep (se 2 (by rfl) ⟨3206445, by rfl⟩ : syracuseStep 8550521 = 6412891) B6412891
theorem B24361175 : Blo 1688044 24361175 := bstep (se 1 (by rfl) ⟨18270881, by rfl⟩ : syracuseStep 24361175 = 36541763) B36541763
theorem B12818735 : Blo 1688044 12818735 := bstep (se 1 (by rfl) ⟨9614051, by rfl⟩ : syracuseStep 12818735 = 19228103) B19228103
theorem B2849087 : Blo 1688044 2849087 := bstep (se 1 (by rfl) ⟨2136815, by rfl⟩ : syracuseStep 2849087 = 4273631) B4273631
theorem B5700239 : Blo 1688044 5700239 := bstep (se 1 (by rfl) ⟨4275179, by rfl⟩ : syracuseStep 5700239 = 8550359) B8550359
theorem B2136871 : Blo 1688044 2136871 := bstep (se 1 (by rfl) ⟨1602653, by rfl⟩ : syracuseStep 2136871 = 3205307) B3205307
theorem B73063295 : Blo 1688044 73063295 := bstep (se 1 (by rfl) ⟨54797471, by rfl⟩ : syracuseStep 73063295 = 109594943) B109594943
theorem B27081695 : Blo 1688044 27081695 := bstep (se 1 (by rfl) ⟨20311271, by rfl⟩ : syracuseStep 27081695 = 40622543) B40622543
theorem B3251995 : Blo 1688044 3251995 := bstep (se 1 (by rfl) ⟨2438996, by rfl⟩ : syracuseStep 3251995 = 4877993) B4877993
theorem B21634897 : Blo 1688044 21634897 := bstep (se 2 (by rfl) ⟨8113086, by rfl⟩ : syracuseStep 21634897 = 16226173) B16226173
theorem B3801311 : Blo 1688044 3801311 := bstep (se 1 (by rfl) ⟨2850983, by rfl⟩ : syracuseStep 3801311 = 5701967) B5701967
theorem B7217579 : Blo 1688044 7217579 := bstep (se 1 (by rfl) ⟨5413184, by rfl⟩ : syracuseStep 7217579 = 10826369) B10826369
theorem B1688219 : Blo 1688044 1688219 := bstep (se 1 (by rfl) ⟨1266164, by rfl⟩ : syracuseStep 1688219 = 2532329) B2532329
theorem B4277063 : Blo 1688044 4277063 := bstep (se 1 (by rfl) ⟨3207797, by rfl⟩ : syracuseStep 4277063 = 6415595) B6415595
theorem B1688479 : Blo 1688044 1688479 := bstep (se 1 (by rfl) ⟨1266359, by rfl⟩ : syracuseStep 1688479 = 2532719) B2532719
theorem B9618335 : Blo 1688044 9618335 := bstep (se 1 (by rfl) ⟨7213751, by rfl⟩ : syracuseStep 9618335 = 14427503) B14427503
theorem B2851807 : Blo 1688044 2851807 := bstep (se 1 (by rfl) ⟨2138855, by rfl⟩ : syracuseStep 2851807 = 4277711) B4277711
theorem B21947537 : Blo 1688044 21947537 := bstep (se 2 (by rfl) ⟨8230326, by rfl⟩ : syracuseStep 21947537 = 16460653) B16460653
theorem B1688831 : Blo 1688044 1688831 := bstep (se 1 (by rfl) ⟨1266623, by rfl⟩ : syracuseStep 1688831 = 2533247) B2533247
theorem B2532671 : Blo 1688044 2532671 := bstep (se 1 (by rfl) ⟨1899503, by rfl⟩ : syracuseStep 2532671 = 3799007) B3799007
theorem B17343973 : Blo 1688044 17343973 := bstep (se 4 (by rfl) ⟨1625997, by rfl⟩ : syracuseStep 17343973 = 3251995) B3251995
theorem B8545823 : Blo 1688044 8545823 := bstep (se 1 (by rfl) ⟨6409367, by rfl⟩ : syracuseStep 8545823 = 12818735) B12818735
theorem B7702409 : Blo 1688044 7702409 := bstep (se 2 (by rfl) ⟨2888403, by rfl⟩ : syracuseStep 7702409 = 5776807) B5776807
theorem B28846529 : Blo 1688044 28846529 := bstep (se 2 (by rfl) ⟨10817448, by rfl⟩ : syracuseStep 28846529 = 21634897) B21634897
theorem B41093729 : Blo 1688044 41093729 := bstep (se 2 (by rfl) ⟨15410148, by rfl⟩ : syracuseStep 41093729 = 30820297) B30820297
theorem B702360791 : Blo 1688044 702360791 := bstep (se 1 (by rfl) ⟨526770593, by rfl⟩ : syracuseStep 702360791 = 1053541187) B1053541187
theorem B28864025 : Blo 1688044 28864025 := bstep (se 2 (by rfl) ⟨10824009, by rfl⟩ : syracuseStep 28864025 = 21648019) B21648019
theorem B5697161 : Blo 1688044 5697161 := bstep (se 2 (by rfl) ⟨2136435, by rfl⟩ : syracuseStep 5697161 = 4272871) B4272871
theorem B2404009 : Blo 1688044 2404009 := bstep (se 2 (by rfl) ⟨901503, by rfl⟩ : syracuseStep 2404009 = 1803007) B1803007
theorem B20541275 : Blo 1688044 20541275 := bstep (se 1 (by rfl) ⟨15405956, by rfl⟩ : syracuseStep 20541275 = 30811913) B30811913
theorem B16240783 : Blo 1688044 16240783 := bstep (se 1 (by rfl) ⟨12180587, by rfl⟩ : syracuseStep 16240783 = 24361175) B24361175
theorem B8549225 : Blo 1688044 8549225 := bstep (se 2 (by rfl) ⟨3205959, by rfl⟩ : syracuseStep 8549225 = 6411919) B6411919
theorem B19510121 : Blo 1688044 19510121 := bstep (se 2 (by rfl) ⟨7316295, by rfl⟩ : syracuseStep 19510121 = 14632591) B14632591
theorem B2405467 : Blo 1688044 2405467 := bstep (se 1 (by rfl) ⟨1804100, by rfl⟩ : syracuseStep 2405467 = 3608201) B3608201
theorem B6501559 : Blo 1688044 6501559 := bstep (se 1 (by rfl) ⟨4876169, by rfl⟩ : syracuseStep 6501559 = 9752339) B9752339
theorem B18257213 : Blo 1688044 18257213 := bstep (se 3 (by rfl) ⟨3423227, by rfl⟩ : syracuseStep 18257213 = 6846455) B6846455
theorem B3798431 : Blo 1688044 3798431 := bstep (se 1 (by rfl) ⟨2848823, by rfl⟩ : syracuseStep 3798431 = 5697647) B5697647
theorem B34666019 : Blo 1688044 34666019 := bstep (se 1 (by rfl) ⟨25999514, by rfl⟩ : syracuseStep 34666019 = 51999029) B51999029
theorem B12826511 : Blo 1688044 12826511 := bstep (se 1 (by rfl) ⟨9619883, by rfl⟩ : syracuseStep 12826511 = 19239767) B19239767
theorem B14424155 : Blo 1688044 14424155 := bstep (se 1 (by rfl) ⟨10818116, by rfl⟩ : syracuseStep 14424155 = 21636233) B21636233
theorem B20053145699 : Blo 1688044 20053145699 := bstep (se 1 (by rfl) ⟨15039859274, by rfl⟩ : syracuseStep 20053145699 = 30079718549) B30079718549
theorem B2849161 : Blo 1688044 2849161 := bstep (se 2 (by rfl) ⟨1068435, by rfl⟩ : syracuseStep 2849161 = 2136871) B2136871
theorem B5700347 : Blo 1688044 5700347 := bstep (se 1 (by rfl) ⟨4275260, by rfl⟩ : syracuseStep 5700347 = 8550521) B8550521
theorem B1899391 : Blo 1688044 1899391 := bstep (se 1 (by rfl) ⟨1424543, by rfl⟩ : syracuseStep 1899391 = 2849087) B2849087
theorem B3800159 : Blo 1688044 3800159 := bstep (se 1 (by rfl) ⟨2850119, by rfl⟩ : syracuseStep 3800159 = 5700239) B5700239
theorem B48708863 : Blo 1688044 48708863 := bstep (se 1 (by rfl) ⟨36531647, by rfl⟩ : syracuseStep 48708863 = 73063295) B73063295
theorem B18054463 : Blo 1688044 18054463 := bstep (se 1 (by rfl) ⟨13540847, by rfl⟩ : syracuseStep 18054463 = 27081695) B27081695
theorem B2851375 : Blo 1688044 2851375 := bstep (se 1 (by rfl) ⟨2138531, by rfl⟩ : syracuseStep 2851375 = 4277063) B4277063
theorem B14631691 : Blo 1688044 14631691 := bstep (se 1 (by rfl) ⟨10973768, by rfl⟩ : syracuseStep 14631691 = 21947537) B21947537
theorem B1688447 : Blo 1688044 1688447 := bstep (se 1 (by rfl) ⟨1266335, by rfl⟩ : syracuseStep 1688447 = 2532671) B2532671
theorem B2532287 : Blo 1688044 2532287 := bstep (se 1 (by rfl) ⟨1899215, by rfl⟩ : syracuseStep 2532287 = 3798431) B3798431
theorem B23110679 : Blo 1688044 23110679 := bstep (se 1 (by rfl) ⟨17333009, by rfl⟩ : syracuseStep 23110679 = 34666019) B34666019
theorem B2532521 : Blo 1688044 2532521 := bstep (se 2 (by rfl) ⟨949695, by rfl⟩ : syracuseStep 2532521 = 1899391) B1899391
theorem B3802409 : Blo 1688044 3802409 := bstep (se 2 (by rfl) ⟨1425903, by rfl⟩ : syracuseStep 3802409 = 2851807) B2851807
theorem B13368763799 : Blo 1688044 13368763799 := bstep (se 1 (by rfl) ⟨10026572849, by rfl⟩ : syracuseStep 13368763799 = 20053145699) B20053145699
theorem B8668745 : Blo 1688044 8668745 := bstep (se 2 (by rfl) ⟨3250779, by rfl⟩ : syracuseStep 8668745 = 6501559) B6501559
theorem B27395819 : Blo 1688044 27395819 := bstep (se 1 (by rfl) ⟨20546864, by rfl⟩ : syracuseStep 27395819 = 41093729) B41093729
theorem B2533439 : Blo 1688044 2533439 := bstep (se 1 (by rfl) ⟨1900079, by rfl⟩ : syracuseStep 2533439 = 3800159) B3800159
theorem B468240527 : Blo 1688044 468240527 := bstep (se 1 (by rfl) ⟨351180395, by rfl⟩ : syracuseStep 468240527 = 702360791) B702360791
theorem B3205345 : Blo 1688044 3205345 := bstep (se 2 (by rfl) ⟨1202004, by rfl⟩ : syracuseStep 3205345 = 2404009) B2404009
theorem B20539757 : Blo 1688044 20539757 := bstep (se 3 (by rfl) ⟨3851204, by rfl⟩ : syracuseStep 20539757 = 7702409) B7702409
theorem B2534207 : Blo 1688044 2534207 := bstep (se 1 (by rfl) ⟨1900655, by rfl⟩ : syracuseStep 2534207 = 3801311) B3801311
theorem B21654377 : Blo 1688044 21654377 := bstep (se 2 (by rfl) ⟨8120391, by rfl⟩ : syracuseStep 21654377 = 16240783) B16240783
theorem B4811719 : Blo 1688044 4811719 := bstep (se 1 (by rfl) ⟨3608789, by rfl⟩ : syracuseStep 4811719 = 7217579) B7217579
theorem B5697215 : Blo 1688044 5697215 := bstep (se 1 (by rfl) ⟨4272911, by rfl⟩ : syracuseStep 5697215 = 8545823) B8545823
theorem B3207289 : Blo 1688044 3207289 := bstep (se 2 (by rfl) ⟨1202733, by rfl⟩ : syracuseStep 3207289 = 2405467) B2405467
theorem B19231019 : Blo 1688044 19231019 := bstep (se 1 (by rfl) ⟨14423264, by rfl⟩ : syracuseStep 19231019 = 28846529) B28846529
theorem B24072617 : Blo 1688044 24072617 := bstep (se 2 (by rfl) ⟨9027231, by rfl⟩ : syracuseStep 24072617 = 18054463) B18054463
theorem B3798107 : Blo 1688044 3798107 := bstep (se 1 (by rfl) ⟨2848580, by rfl⟩ : syracuseStep 3798107 = 5697161) B5697161
theorem B13694183 : Blo 1688044 13694183 := bstep (se 1 (by rfl) ⟨10270637, by rfl⟩ : syracuseStep 13694183 = 20541275) B20541275
theorem B3798881 : Blo 1688044 3798881 := bstep (se 2 (by rfl) ⟨1424580, by rfl⟩ : syracuseStep 3798881 = 2849161) B2849161
theorem B5699483 : Blo 1688044 5699483 := bstep (se 1 (by rfl) ⟨4274612, by rfl⟩ : syracuseStep 5699483 = 8549225) B8549225
theorem B13006747 : Blo 1688044 13006747 := bstep (se 1 (by rfl) ⟨9755060, by rfl⟩ : syracuseStep 13006747 = 19510121) B19510121
theorem B6412223 : Blo 1688044 6412223 := bstep (se 1 (by rfl) ⟨4809167, by rfl⟩ : syracuseStep 6412223 = 9618335) B9618335
theorem B12171475 : Blo 1688044 12171475 := bstep (se 1 (by rfl) ⟨9128606, by rfl⟩ : syracuseStep 12171475 = 18257213) B18257213
theorem B8551007 : Blo 1688044 8551007 := bstep (se 1 (by rfl) ⟨6413255, by rfl⟩ : syracuseStep 8551007 = 12826511) B12826511
theorem B9616103 : Blo 1688044 9616103 := bstep (se 1 (by rfl) ⟨7212077, by rfl⟩ : syracuseStep 9616103 = 14424155) B14424155
theorem B3800231 : Blo 1688044 3800231 := bstep (se 1 (by rfl) ⟨2850173, by rfl⟩ : syracuseStep 3800231 = 5700347) B5700347
theorem B23125297 : Blo 1688044 23125297 := bstep (se 2 (by rfl) ⟨8671986, by rfl⟩ : syracuseStep 23125297 = 17343973) B17343973
theorem B32472575 : Blo 1688044 32472575 := bstep (se 1 (by rfl) ⟨24354431, by rfl⟩ : syracuseStep 32472575 = 48708863) B48708863
theorem B19242683 : Blo 1688044 19242683 := bstep (se 1 (by rfl) ⟨14432012, by rfl⟩ : syracuseStep 19242683 = 28864025) B28864025
theorem B4276385 : Blo 1688044 4276385 := bstep (se 2 (by rfl) ⟨1603644, by rfl⟩ : syracuseStep 4276385 = 3207289) B3207289
theorem B12820679 : Blo 1688044 12820679 := bstep (se 1 (by rfl) ⟨9615509, by rfl⟩ : syracuseStep 12820679 = 19231019) B19231019
theorem B16048411 : Blo 1688044 16048411 := bstep (se 1 (by rfl) ⟨12036308, by rfl⟩ : syracuseStep 16048411 = 24072617) B24072617
theorem B1688191 : Blo 1688044 1688191 := bstep (se 1 (by rfl) ⟨1266143, by rfl⟩ : syracuseStep 1688191 = 2532287) B2532287
theorem B2532071 : Blo 1688044 2532071 := bstep (se 1 (by rfl) ⟨1899053, by rfl⟩ : syracuseStep 2532071 = 3798107) B3798107
theorem B3801833 : Blo 1688044 3801833 := bstep (se 2 (by rfl) ⟨1425687, by rfl⟩ : syracuseStep 3801833 = 2851375) B2851375
theorem B1688347 : Blo 1688044 1688347 := bstep (se 1 (by rfl) ⟨1266260, by rfl⟩ : syracuseStep 1688347 = 2532521) B2532521
theorem B54772685 : Blo 1688044 54772685 := bstep (se 3 (by rfl) ⟨10269878, by rfl⟩ : syracuseStep 54772685 = 20539757) B20539757
theorem B64914533 : Blo 1688044 64914533 := bstep (se 4 (by rfl) ⟨6085737, by rfl⟩ : syracuseStep 64914533 = 12171475) B12171475
theorem B2532587 : Blo 1688044 2532587 := bstep (se 1 (by rfl) ⟨1899440, by rfl⟩ : syracuseStep 2532587 = 3798881) B3798881
theorem B6415625 : Blo 1688044 6415625 := bstep (se 2 (by rfl) ⟨2405859, by rfl⟩ : syracuseStep 6415625 = 4811719) B4811719
theorem B1688959 : Blo 1688044 1688959 := bstep (se 1 (by rfl) ⟨1266719, by rfl⟩ : syracuseStep 1688959 = 2533439) B2533439
theorem B1689471 : Blo 1688044 1689471 := bstep (se 1 (by rfl) ⟨1267103, by rfl⟩ : syracuseStep 1689471 = 2534207) B2534207
theorem B14436251 : Blo 1688044 14436251 := bstep (se 1 (by rfl) ⟨10827188, by rfl⟩ : syracuseStep 14436251 = 21654377) B21654377
theorem B2533487 : Blo 1688044 2533487 := bstep (se 1 (by rfl) ⟨1900115, by rfl⟩ : syracuseStep 2533487 = 3800231) B3800231
theorem B9129455 : Blo 1688044 9129455 := bstep (se 1 (by rfl) ⟨6847091, by rfl⟩ : syracuseStep 9129455 = 13694183) B13694183
theorem B2534939 : Blo 1688044 2534939 := bstep (se 1 (by rfl) ⟨1901204, by rfl⟩ : syracuseStep 2534939 = 3802409) B3802409
theorem B19508921 : Blo 1688044 19508921 := bstep (se 2 (by rfl) ⟨7315845, by rfl⟩ : syracuseStep 19508921 = 14631691) B14631691
theorem B5779163 : Blo 1688044 5779163 := bstep (se 1 (by rfl) ⟨4334372, by rfl⟩ : syracuseStep 5779163 = 8668745) B8668745
theorem B18263879 : Blo 1688044 18263879 := bstep (se 1 (by rfl) ⟨13697909, by rfl⟩ : syracuseStep 18263879 = 27395819) B27395819
theorem B312160351 : Blo 1688044 312160351 := bstep (se 1 (by rfl) ⟨234120263, by rfl⟩ : syracuseStep 312160351 = 468240527) B468240527
theorem B6410735 : Blo 1688044 6410735 := bstep (se 1 (by rfl) ⟨4808051, by rfl⟩ : syracuseStep 6410735 = 9616103) B9616103
theorem B21648383 : Blo 1688044 21648383 := bstep (se 1 (by rfl) ⟨16236287, by rfl⟩ : syracuseStep 21648383 = 32472575) B32472575
theorem B3798143 : Blo 1688044 3798143 := bstep (se 1 (by rfl) ⟨2848607, by rfl⟩ : syracuseStep 3798143 = 5697215) B5697215
theorem B4273793 : Blo 1688044 4273793 := bstep (se 2 (by rfl) ⟨1602672, by rfl⟩ : syracuseStep 4273793 = 3205345) B3205345
theorem B15407119 : Blo 1688044 15407119 := bstep (se 1 (by rfl) ⟨11555339, by rfl⟩ : syracuseStep 15407119 = 23110679) B23110679
theorem B8912509199 : Blo 1688044 8912509199 := bstep (se 1 (by rfl) ⟨6684381899, by rfl⟩ : syracuseStep 8912509199 = 13368763799) B13368763799
theorem B3799655 : Blo 1688044 3799655 := bstep (se 1 (by rfl) ⟨2849741, by rfl⟩ : syracuseStep 3799655 = 5699483) B5699483
theorem B4274815 : Blo 1688044 4274815 := bstep (se 1 (by rfl) ⟨3206111, by rfl⟩ : syracuseStep 4274815 = 6412223) B6412223
theorem B5700671 : Blo 1688044 5700671 := bstep (se 1 (by rfl) ⟨4275503, by rfl⟩ : syracuseStep 5700671 = 8551007) B8551007
theorem B30833729 : Blo 1688044 30833729 := bstep (se 2 (by rfl) ⟨11562648, by rfl⟩ : syracuseStep 30833729 = 23125297) B23125297
theorem B69369317 : Blo 1688044 69369317 := bstep (se 4 (by rfl) ⟨6503373, by rfl⟩ : syracuseStep 69369317 = 13006747) B13006747
theorem B12828455 : Blo 1688044 12828455 := bstep (se 1 (by rfl) ⟨9621341, by rfl⟩ : syracuseStep 12828455 = 19242683) B19242683
theorem B2850923 : Blo 1688044 2850923 := bstep (se 1 (by rfl) ⟨2138192, by rfl⟩ : syracuseStep 2850923 = 4276385) B4276385
theorem B1688047 : Blo 1688044 1688047 := bstep (se 1 (by rfl) ⟨1266035, by rfl⟩ : syracuseStep 1688047 = 2532071) B2532071
theorem B2532095 : Blo 1688044 2532095 := bstep (se 1 (by rfl) ⟨1899071, by rfl⟩ : syracuseStep 2532095 = 3798143) B3798143
theorem B1688391 : Blo 1688044 1688391 := bstep (se 1 (by rfl) ⟨1266293, by rfl⟩ : syracuseStep 1688391 = 2532587) B2532587
theorem B4277083 : Blo 1688044 4277083 := bstep (se 1 (by rfl) ⟨3207812, by rfl⟩ : syracuseStep 4277083 = 6415625) B6415625
theorem B1688991 : Blo 1688044 1688991 := bstep (se 1 (by rfl) ⟨1266743, by rfl⟩ : syracuseStep 1688991 = 2533487) B2533487
theorem B2533103 : Blo 1688044 2533103 := bstep (se 1 (by rfl) ⟨1899827, by rfl⟩ : syracuseStep 2533103 = 3799655) B3799655
theorem B20555819 : Blo 1688044 20555819 := bstep (se 1 (by rfl) ⟨15416864, by rfl⟩ : syracuseStep 20555819 = 30833729) B30833729
theorem B46246211 : Blo 1688044 46246211 := bstep (se 1 (by rfl) ⟨34684658, by rfl⟩ : syracuseStep 46246211 = 69369317) B69369317
theorem B1689959 : Blo 1688044 1689959 := bstep (se 1 (by rfl) ⟨1267469, by rfl⟩ : syracuseStep 1689959 = 2534939) B2534939
theorem B3852775 : Blo 1688044 3852775 := bstep (se 1 (by rfl) ⟨2889581, by rfl⟩ : syracuseStep 3852775 = 5779163) B5779163
theorem B12175919 : Blo 1688044 12175919 := bstep (se 1 (by rfl) ⟨9131939, by rfl⟩ : syracuseStep 12175919 = 18263879) B18263879
theorem B416213801 : Blo 1688044 416213801 := bstep (se 2 (by rfl) ⟨156080175, by rfl⟩ : syracuseStep 416213801 = 312160351) B312160351
theorem B8547119 : Blo 1688044 8547119 := bstep (se 1 (by rfl) ⟨6410339, by rfl⟩ : syracuseStep 8547119 = 12820679) B12820679
theorem B2534555 : Blo 1688044 2534555 := bstep (se 1 (by rfl) ⟨1900916, by rfl⟩ : syracuseStep 2534555 = 3801833) B3801833
theorem B36515123 : Blo 1688044 36515123 := bstep (se 1 (by rfl) ⟨27386342, by rfl⟩ : syracuseStep 36515123 = 54772685) B54772685
theorem B13005947 : Blo 1688044 13005947 := bstep (se 1 (by rfl) ⟨9754460, by rfl⟩ : syracuseStep 13005947 = 19508921) B19508921
theorem B20542825 : Blo 1688044 20542825 := bstep (se 2 (by rfl) ⟨7703559, by rfl⟩ : syracuseStep 20542825 = 15407119) B15407119
theorem B4273823 : Blo 1688044 4273823 := bstep (se 1 (by rfl) ⟨3205367, by rfl⟩ : syracuseStep 4273823 = 6410735) B6410735
theorem B342366101 : Blo 1688044 342366101 := bstep (se 6 (by rfl) ⟨8024205, by rfl⟩ : syracuseStep 342366101 = 16048411) B16048411
theorem B14432255 : Blo 1688044 14432255 := bstep (se 1 (by rfl) ⟨10824191, by rfl⟩ : syracuseStep 14432255 = 21648383) B21648383
theorem B43276355 : Blo 1688044 43276355 := bstep (se 1 (by rfl) ⟨32457266, by rfl⟩ : syracuseStep 43276355 = 64914533) B64914533
theorem B5699753 : Blo 1688044 5699753 := bstep (se 2 (by rfl) ⟨2137407, by rfl⟩ : syracuseStep 5699753 = 4274815) B4274815
theorem B2849195 : Blo 1688044 2849195 := bstep (se 1 (by rfl) ⟨2136896, by rfl⟩ : syracuseStep 2849195 = 4273793) B4273793
theorem B9624167 : Blo 1688044 9624167 := bstep (se 1 (by rfl) ⟨7218125, by rfl⟩ : syracuseStep 9624167 = 14436251) B14436251
theorem B5941672799 : Blo 1688044 5941672799 := bstep (se 1 (by rfl) ⟨4456254599, by rfl⟩ : syracuseStep 5941672799 = 8912509199) B8912509199
theorem B3800447 : Blo 1688044 3800447 := bstep (se 1 (by rfl) ⟨2850335, by rfl⟩ : syracuseStep 3800447 = 5700671) B5700671
theorem B6086303 : Blo 1688044 6086303 := bstep (se 1 (by rfl) ⟨4564727, by rfl⟩ : syracuseStep 6086303 = 9129455) B9129455
theorem B8552303 : Blo 1688044 8552303 := bstep (se 1 (by rfl) ⟨6414227, by rfl⟩ : syracuseStep 8552303 = 12828455) B12828455
theorem B1900615 : Blo 1688044 1900615 := bstep (se 1 (by rfl) ⟨1425461, by rfl⟩ : syracuseStep 1900615 = 2850923) B2850923
theorem B1688063 : Blo 1688044 1688063 := bstep (se 1 (by rfl) ⟨1266047, by rfl⟩ : syracuseStep 1688063 = 2532095) B2532095
theorem B5137033 : Blo 1688044 5137033 := bstep (se 2 (by rfl) ⟨1926387, by rfl⟩ : syracuseStep 5137033 = 3852775) B3852775
theorem B5702777 : Blo 1688044 5702777 := bstep (se 2 (by rfl) ⟨2138541, by rfl⟩ : syracuseStep 5702777 = 4277083) B4277083
theorem B1688735 : Blo 1688044 1688735 := bstep (se 1 (by rfl) ⟨1266551, by rfl⟩ : syracuseStep 1688735 = 2533103) B2533103
theorem B6416111 : Blo 1688044 6416111 := bstep (se 1 (by rfl) ⟨4812083, by rfl⟩ : syracuseStep 6416111 = 9624167) B9624167
theorem B1689703 : Blo 1688044 1689703 := bstep (se 1 (by rfl) ⟨1267277, by rfl⟩ : syracuseStep 1689703 = 2534555) B2534555
theorem B15844460797 : Blo 1688044 15844460797 := bstep (se 3 (by rfl) ⟨2970836399, by rfl⟩ : syracuseStep 15844460797 = 5941672799) B5941672799
theorem B2533631 : Blo 1688044 2533631 := bstep (se 1 (by rfl) ⟨1900223, by rfl⟩ : syracuseStep 2533631 = 3800447) B3800447
theorem B4057535 : Blo 1688044 4057535 := bstep (se 1 (by rfl) ⟨3043151, by rfl⟩ : syracuseStep 4057535 = 6086303) B6086303
theorem B9621503 : Blo 1688044 9621503 := bstep (se 1 (by rfl) ⟨7216127, by rfl⟩ : syracuseStep 9621503 = 14432255) B14432255
theorem B30830807 : Blo 1688044 30830807 := bstep (se 1 (by rfl) ⟨23123105, by rfl⟩ : syracuseStep 30830807 = 46246211) B46246211
theorem B27390433 : Blo 1688044 27390433 := bstep (se 2 (by rfl) ⟨10271412, by rfl⟩ : syracuseStep 27390433 = 20542825) B20542825
theorem B277475867 : Blo 1688044 277475867 := bstep (se 1 (by rfl) ⟨208106900, by rfl⟩ : syracuseStep 277475867 = 416213801) B416213801
theorem B5698079 : Blo 1688044 5698079 := bstep (se 1 (by rfl) ⟨4273559, by rfl⟩ : syracuseStep 5698079 = 8547119) B8547119
theorem B24343415 : Blo 1688044 24343415 := bstep (se 1 (by rfl) ⟨18257561, by rfl⟩ : syracuseStep 24343415 = 36515123) B36515123
theorem B34682525 : Blo 1688044 34682525 := bstep (se 3 (by rfl) ⟨6502973, by rfl⟩ : syracuseStep 34682525 = 13005947) B13005947
theorem B2849215 : Blo 1688044 2849215 := bstep (se 1 (by rfl) ⟨2136911, by rfl⟩ : syracuseStep 2849215 = 4273823) B4273823
theorem B228244067 : Blo 1688044 228244067 := bstep (se 1 (by rfl) ⟨171183050, by rfl⟩ : syracuseStep 228244067 = 342366101) B342366101
theorem B13703879 : Blo 1688044 13703879 := bstep (se 1 (by rfl) ⟨10277909, by rfl⟩ : syracuseStep 13703879 = 20555819) B20555819
theorem B28850903 : Blo 1688044 28850903 := bstep (se 1 (by rfl) ⟨21638177, by rfl⟩ : syracuseStep 28850903 = 43276355) B43276355
theorem B3799835 : Blo 1688044 3799835 := bstep (se 1 (by rfl) ⟨2849876, by rfl⟩ : syracuseStep 3799835 = 5699753) B5699753
theorem B1899463 : Blo 1688044 1899463 := bstep (se 1 (by rfl) ⟨1424597, by rfl⟩ : syracuseStep 1899463 = 2849195) B2849195
theorem B8117279 : Blo 1688044 8117279 := bstep (se 1 (by rfl) ⟨6087959, by rfl⟩ : syracuseStep 8117279 = 12175919) B12175919
theorem B5701535 : Blo 1688044 5701535 := bstep (se 1 (by rfl) ⟨4276151, by rfl⟩ : syracuseStep 5701535 = 8552303) B8552303
theorem B20553871 : Blo 1688044 20553871 := bstep (se 1 (by rfl) ⟨15415403, by rfl⟩ : syracuseStep 20553871 = 30830807) B30830807
theorem B21125947729 : Blo 1688044 21125947729 := bstep (se 2 (by rfl) ⟨7922230398, by rfl⟩ : syracuseStep 21125947729 = 15844460797) B15844460797
theorem B184983911 : Blo 1688044 184983911 := bstep (se 1 (by rfl) ⟨138737933, by rfl⟩ : syracuseStep 184983911 = 277475867) B277475867
theorem B16228943 : Blo 1688044 16228943 := bstep (se 1 (by rfl) ⟨12171707, by rfl⟩ : syracuseStep 16228943 = 24343415) B24343415
theorem B36520577 : Blo 1688044 36520577 := bstep (se 2 (by rfl) ⟨13695216, by rfl⟩ : syracuseStep 36520577 = 27390433) B27390433
theorem B3801851 : Blo 1688044 3801851 := bstep (se 1 (by rfl) ⟨2851388, by rfl⟩ : syracuseStep 3801851 = 5702777) B5702777
theorem B6849377 : Blo 1688044 6849377 := bstep (se 2 (by rfl) ⟨2568516, by rfl⟩ : syracuseStep 6849377 = 5137033) B5137033
theorem B4277407 : Blo 1688044 4277407 := bstep (se 1 (by rfl) ⟨3208055, by rfl⟩ : syracuseStep 4277407 = 6416111) B6416111
theorem B2532617 : Blo 1688044 2532617 := bstep (se 2 (by rfl) ⟨949731, by rfl⟩ : syracuseStep 2532617 = 1899463) B1899463
theorem B1689087 : Blo 1688044 1689087 := bstep (se 1 (by rfl) ⟨1266815, by rfl⟩ : syracuseStep 1689087 = 2533631) B2533631
theorem B2705023 : Blo 1688044 2705023 := bstep (se 1 (by rfl) ⟨2028767, by rfl⟩ : syracuseStep 2705023 = 4057535) B4057535
theorem B9135919 : Blo 1688044 9135919 := bstep (se 1 (by rfl) ⟨6851939, by rfl⟩ : syracuseStep 9135919 = 13703879) B13703879
theorem B2533223 : Blo 1688044 2533223 := bstep (se 1 (by rfl) ⟨1899917, by rfl⟩ : syracuseStep 2533223 = 3799835) B3799835
theorem B2534153 : Blo 1688044 2534153 := bstep (se 2 (by rfl) ⟨950307, by rfl⟩ : syracuseStep 2534153 = 1900615) B1900615
theorem B6414335 : Blo 1688044 6414335 := bstep (se 1 (by rfl) ⟨4810751, by rfl⟩ : syracuseStep 6414335 = 9621503) B9621503
theorem B23121683 : Blo 1688044 23121683 := bstep (se 1 (by rfl) ⟨17341262, by rfl⟩ : syracuseStep 23121683 = 34682525) B34682525
theorem B152162711 : Blo 1688044 152162711 := bstep (se 1 (by rfl) ⟨114122033, by rfl⟩ : syracuseStep 152162711 = 228244067) B228244067
theorem B5411519 : Blo 1688044 5411519 := bstep (se 1 (by rfl) ⟨4058639, by rfl⟩ : syracuseStep 5411519 = 8117279) B8117279
theorem B3798719 : Blo 1688044 3798719 := bstep (se 1 (by rfl) ⟨2849039, by rfl⟩ : syracuseStep 3798719 = 5698079) B5698079
theorem B3798953 : Blo 1688044 3798953 := bstep (se 2 (by rfl) ⟨1424607, by rfl⟩ : syracuseStep 3798953 = 2849215) B2849215
theorem B19233935 : Blo 1688044 19233935 := bstep (se 1 (by rfl) ⟨14425451, by rfl⟩ : syracuseStep 19233935 = 28850903) B28850903
theorem B3801023 : Blo 1688044 3801023 := bstep (se 1 (by rfl) ⟨2850767, by rfl⟩ : syracuseStep 3801023 = 5701535) B5701535
theorem B123322607 : Blo 1688044 123322607 := bstep (se 1 (by rfl) ⟨92491955, by rfl⟩ : syracuseStep 123322607 = 184983911) B184983911
theorem B101441807 : Blo 1688044 101441807 := bstep (se 1 (by rfl) ⟨76081355, by rfl⟩ : syracuseStep 101441807 = 152162711) B152162711
theorem B24347051 : Blo 1688044 24347051 := bstep (se 1 (by rfl) ⟨18260288, by rfl⟩ : syracuseStep 24347051 = 36520577) B36520577
theorem B28167930305 : Blo 1688044 28167930305 := bstep (se 2 (by rfl) ⟨10562973864, by rfl⟩ : syracuseStep 28167930305 = 21125947729) B21125947729
theorem B1688411 : Blo 1688044 1688411 := bstep (se 1 (by rfl) ⟨1266308, by rfl⟩ : syracuseStep 1688411 = 2532617) B2532617
theorem B2532479 : Blo 1688044 2532479 := bstep (se 1 (by rfl) ⟨1899359, by rfl⟩ : syracuseStep 2532479 = 3798719) B3798719
theorem B1688815 : Blo 1688044 1688815 := bstep (se 1 (by rfl) ⟨1266611, by rfl⟩ : syracuseStep 1688815 = 2533223) B2533223
theorem B2532635 : Blo 1688044 2532635 := bstep (se 1 (by rfl) ⟨1899476, by rfl⟩ : syracuseStep 2532635 = 3798953) B3798953
theorem B5703209 : Blo 1688044 5703209 := bstep (se 2 (by rfl) ⟨2138703, by rfl⟩ : syracuseStep 5703209 = 4277407) B4277407
theorem B1689435 : Blo 1688044 1689435 := bstep (se 1 (by rfl) ⟨1267076, by rfl⟩ : syracuseStep 1689435 = 2534153) B2534153
theorem B12822623 : Blo 1688044 12822623 := bstep (se 1 (by rfl) ⟨9616967, by rfl⟩ : syracuseStep 12822623 = 19233935) B19233935
theorem B3606697 : Blo 1688044 3606697 := bstep (se 2 (by rfl) ⟨1352511, by rfl⟩ : syracuseStep 3606697 = 2705023) B2705023
theorem B4276223 : Blo 1688044 4276223 := bstep (se 1 (by rfl) ⟨3207167, by rfl⟩ : syracuseStep 4276223 = 6414335) B6414335
theorem B2534015 : Blo 1688044 2534015 := bstep (se 1 (by rfl) ⟨1900511, by rfl⟩ : syracuseStep 2534015 = 3801023) B3801023
theorem B27405161 : Blo 1688044 27405161 := bstep (se 2 (by rfl) ⟨10276935, by rfl⟩ : syracuseStep 27405161 = 20553871) B20553871
theorem B3607679 : Blo 1688044 3607679 := bstep (se 1 (by rfl) ⟨2705759, by rfl⟩ : syracuseStep 3607679 = 5411519) B5411519
theorem B2534567 : Blo 1688044 2534567 := bstep (se 1 (by rfl) ⟨1900925, by rfl⟩ : syracuseStep 2534567 = 3801851) B3801851
theorem B4566251 : Blo 1688044 4566251 := bstep (se 1 (by rfl) ⟨3424688, by rfl⟩ : syracuseStep 4566251 = 6849377) B6849377
theorem B15414455 : Blo 1688044 15414455 := bstep (se 1 (by rfl) ⟨11560841, by rfl⟩ : syracuseStep 15414455 = 23121683) B23121683
theorem B10819295 : Blo 1688044 10819295 := bstep (se 1 (by rfl) ⟨8114471, by rfl⟩ : syracuseStep 10819295 = 16228943) B16228943
theorem B12181225 : Blo 1688044 12181225 := bstep (se 2 (by rfl) ⟨4567959, by rfl⟩ : syracuseStep 12181225 = 9135919) B9135919
theorem B82215071 : Blo 1688044 82215071 := bstep (se 1 (by rfl) ⟨61661303, by rfl⟩ : syracuseStep 82215071 = 123322607) B123322607
theorem B4808929 : Blo 1688044 4808929 := bstep (se 2 (by rfl) ⟨1803348, by rfl⟩ : syracuseStep 4808929 = 3606697) B3606697
theorem B18778620203 : Blo 1688044 18778620203 := bstep (se 1 (by rfl) ⟨14083965152, by rfl⟩ : syracuseStep 18778620203 = 28167930305) B28167930305
theorem B1688319 : Blo 1688044 1688319 := bstep (se 1 (by rfl) ⟨1266239, by rfl⟩ : syracuseStep 1688319 = 2532479) B2532479
theorem B1688423 : Blo 1688044 1688423 := bstep (se 1 (by rfl) ⟨1266317, by rfl⟩ : syracuseStep 1688423 = 2532635) B2532635
theorem B3802139 : Blo 1688044 3802139 := bstep (se 1 (by rfl) ⟨2851604, by rfl⟩ : syracuseStep 3802139 = 5703209) B5703209
theorem B1689343 : Blo 1688044 1689343 := bstep (se 1 (by rfl) ⟨1267007, by rfl⟩ : syracuseStep 1689343 = 2534015) B2534015
theorem B18270107 : Blo 1688044 18270107 := bstep (se 1 (by rfl) ⟨13702580, by rfl⟩ : syracuseStep 18270107 = 27405161) B27405161
theorem B1689711 : Blo 1688044 1689711 := bstep (se 1 (by rfl) ⟨1267283, by rfl⟩ : syracuseStep 1689711 = 2534567) B2534567
theorem B67627871 : Blo 1688044 67627871 := bstep (se 1 (by rfl) ⟨50720903, by rfl⟩ : syracuseStep 67627871 = 101441807) B101441807
theorem B16231367 : Blo 1688044 16231367 := bstep (se 1 (by rfl) ⟨12173525, by rfl⟩ : syracuseStep 16231367 = 24347051) B24347051
theorem B9620477 : Blo 1688044 9620477 := bstep (se 3 (by rfl) ⟨1803839, by rfl⟩ : syracuseStep 9620477 = 3607679) B3607679
theorem B12176669 : Blo 1688044 12176669 := bstep (se 3 (by rfl) ⟨2283125, by rfl⟩ : syracuseStep 12176669 = 4566251) B4566251
theorem B10276303 : Blo 1688044 10276303 := bstep (se 1 (by rfl) ⟨7707227, by rfl⟩ : syracuseStep 10276303 = 15414455) B15414455
theorem B7212863 : Blo 1688044 7212863 := bstep (se 1 (by rfl) ⟨5409647, by rfl⟩ : syracuseStep 7212863 = 10819295) B10819295
theorem B8548415 : Blo 1688044 8548415 := bstep (se 1 (by rfl) ⟨6411311, by rfl⟩ : syracuseStep 8548415 = 12822623) B12822623
theorem B16241633 : Blo 1688044 16241633 := bstep (se 2 (by rfl) ⟨6090612, by rfl⟩ : syracuseStep 16241633 = 12181225) B12181225
theorem B2850815 : Blo 1688044 2850815 := bstep (se 1 (by rfl) ⟨2138111, by rfl⟩ : syracuseStep 2850815 = 4276223) B4276223
theorem B12519080135 : Blo 1688044 12519080135 := bstep (se 1 (by rfl) ⟨9389310101, by rfl⟩ : syracuseStep 12519080135 = 18778620203) B18778620203
theorem B2534759 : Blo 1688044 2534759 := bstep (se 1 (by rfl) ⟨1901069, by rfl⟩ : syracuseStep 2534759 = 3802139) B3802139
theorem B45085247 : Blo 1688044 45085247 := bstep (se 1 (by rfl) ⟨33813935, by rfl⟩ : syracuseStep 45085247 = 67627871) B67627871
theorem B13701737 : Blo 1688044 13701737 := bstep (se 2 (by rfl) ⟨5138151, by rfl⟩ : syracuseStep 13701737 = 10276303) B10276303
theorem B5698943 : Blo 1688044 5698943 := bstep (se 1 (by rfl) ⟨4274207, by rfl⟩ : syracuseStep 5698943 = 8548415) B8548415
theorem B54810047 : Blo 1688044 54810047 := bstep (se 1 (by rfl) ⟨41107535, by rfl⟩ : syracuseStep 54810047 = 82215071) B82215071
theorem B6411905 : Blo 1688044 6411905 := bstep (se 2 (by rfl) ⟨2404464, by rfl⟩ : syracuseStep 6411905 = 4808929) B4808929
theorem B10827755 : Blo 1688044 10827755 := bstep (se 1 (by rfl) ⟨8120816, by rfl⟩ : syracuseStep 10827755 = 16241633) B16241633
theorem B12180071 : Blo 1688044 12180071 := bstep (se 1 (by rfl) ⟨9135053, by rfl⟩ : syracuseStep 12180071 = 18270107) B18270107
theorem B10820911 : Blo 1688044 10820911 := bstep (se 1 (by rfl) ⟨8115683, by rfl⟩ : syracuseStep 10820911 = 16231367) B16231367
theorem B6413651 : Blo 1688044 6413651 := bstep (se 1 (by rfl) ⟨4810238, by rfl⟩ : syracuseStep 6413651 = 9620477) B9620477
theorem B8117779 : Blo 1688044 8117779 := bstep (se 1 (by rfl) ⟨6088334, by rfl⟩ : syracuseStep 8117779 = 12176669) B12176669
theorem B4808575 : Blo 1688044 4808575 := bstep (se 1 (by rfl) ⟨3606431, by rfl⟩ : syracuseStep 4808575 = 7212863) B7212863
theorem B1900543 : Blo 1688044 1900543 := bstep (se 1 (by rfl) ⟨1425407, by rfl⟩ : syracuseStep 1900543 = 2850815) B2850815
theorem B30056831 : Blo 1688044 30056831 := bstep (se 1 (by rfl) ⟨22542623, by rfl⟩ : syracuseStep 30056831 = 45085247) B45085247
theorem B9134491 : Blo 1688044 9134491 := bstep (se 1 (by rfl) ⟨6850868, by rfl⟩ : syracuseStep 9134491 = 13701737) B13701737
theorem B7218503 : Blo 1688044 7218503 := bstep (se 1 (by rfl) ⟨5413877, by rfl⟩ : syracuseStep 7218503 = 10827755) B10827755
theorem B14427881 : Blo 1688044 14427881 := bstep (se 2 (by rfl) ⟨5410455, by rfl⟩ : syracuseStep 14427881 = 10820911) B10820911
theorem B8120047 : Blo 1688044 8120047 := bstep (se 1 (by rfl) ⟨6090035, by rfl⟩ : syracuseStep 8120047 = 12180071) B12180071
theorem B10823705 : Blo 1688044 10823705 := bstep (se 2 (by rfl) ⟨4058889, by rfl⟩ : syracuseStep 10823705 = 8117779) B8117779
theorem B1689839 : Blo 1688044 1689839 := bstep (se 1 (by rfl) ⟨1267379, by rfl⟩ : syracuseStep 1689839 = 2534759) B2534759
theorem B2534057 : Blo 1688044 2534057 := bstep (se 2 (by rfl) ⟨950271, by rfl⟩ : syracuseStep 2534057 = 1900543) B1900543
theorem B8346053423 : Blo 1688044 8346053423 := bstep (se 1 (by rfl) ⟨6259540067, by rfl⟩ : syracuseStep 8346053423 = 12519080135) B12519080135
theorem B36540031 : Blo 1688044 36540031 := bstep (se 1 (by rfl) ⟨27405023, by rfl⟩ : syracuseStep 36540031 = 54810047) B54810047
theorem B6411433 : Blo 1688044 6411433 := bstep (se 2 (by rfl) ⟨2404287, by rfl⟩ : syracuseStep 6411433 = 4808575) B4808575
theorem B3799295 : Blo 1688044 3799295 := bstep (se 1 (by rfl) ⟨2849471, by rfl⟩ : syracuseStep 3799295 = 5698943) B5698943
theorem B4274603 : Blo 1688044 4274603 := bstep (se 1 (by rfl) ⟨3205952, by rfl⟩ : syracuseStep 4274603 = 6411905) B6411905
theorem B4275767 : Blo 1688044 4275767 := bstep (se 1 (by rfl) ⟨3206825, by rfl⟩ : syracuseStep 4275767 = 6413651) B6413651
theorem B20037887 : Blo 1688044 20037887 := bstep (se 1 (by rfl) ⟨15028415, by rfl⟩ : syracuseStep 20037887 = 30056831) B30056831
theorem B9618587 : Blo 1688044 9618587 := bstep (se 1 (by rfl) ⟨7213940, by rfl⟩ : syracuseStep 9618587 = 14427881) B14427881
theorem B2532863 : Blo 1688044 2532863 := bstep (se 1 (by rfl) ⟨1899647, by rfl⟩ : syracuseStep 2532863 = 3799295) B3799295
theorem B1689371 : Blo 1688044 1689371 := bstep (se 1 (by rfl) ⟨1267028, by rfl⟩ : syracuseStep 1689371 = 2534057) B2534057
theorem B22256142461 : Blo 1688044 22256142461 := bstep (se 3 (by rfl) ⟨4173026711, by rfl⟩ : syracuseStep 22256142461 = 8346053423) B8346053423
theorem B48720041 : Blo 1688044 48720041 := bstep (se 2 (by rfl) ⟨18270015, by rfl⟩ : syracuseStep 48720041 = 36540031) B36540031
theorem B4812335 : Blo 1688044 4812335 := bstep (se 1 (by rfl) ⟨3609251, by rfl⟩ : syracuseStep 4812335 = 7218503) B7218503
theorem B8548577 : Blo 1688044 8548577 := bstep (se 2 (by rfl) ⟨3205716, by rfl⟩ : syracuseStep 8548577 = 6411433) B6411433
theorem B10826729 : Blo 1688044 10826729 := bstep (se 2 (by rfl) ⟨4060023, by rfl⟩ : syracuseStep 10826729 = 8120047) B8120047
theorem B12179321 : Blo 1688044 12179321 := bstep (se 2 (by rfl) ⟨4567245, by rfl⟩ : syracuseStep 12179321 = 9134491) B9134491
theorem B7215803 : Blo 1688044 7215803 := bstep (se 1 (by rfl) ⟨5411852, by rfl⟩ : syracuseStep 7215803 = 10823705) B10823705
theorem B2849735 : Blo 1688044 2849735 := bstep (se 1 (by rfl) ⟨2137301, by rfl⟩ : syracuseStep 2849735 = 4274603) B4274603
theorem B2850511 : Blo 1688044 2850511 := bstep (se 1 (by rfl) ⟨2137883, by rfl⟩ : syracuseStep 2850511 = 4275767) B4275767
theorem B7217819 : Blo 1688044 7217819 := bstep (se 1 (by rfl) ⟨5413364, by rfl⟩ : syracuseStep 7217819 = 10826729) B10826729
theorem B1688575 : Blo 1688044 1688575 := bstep (se 1 (by rfl) ⟨1266431, by rfl⟩ : syracuseStep 1688575 = 2532863) B2532863
theorem B8119547 : Blo 1688044 8119547 := bstep (se 1 (by rfl) ⟨6089660, by rfl⟩ : syracuseStep 8119547 = 12179321) B12179321
theorem B4810535 : Blo 1688044 4810535 := bstep (se 1 (by rfl) ⟨3607901, by rfl⟩ : syracuseStep 4810535 = 7215803) B7215803
theorem B14837428307 : Blo 1688044 14837428307 := bstep (se 1 (by rfl) ⟨11128071230, by rfl⟩ : syracuseStep 14837428307 = 22256142461) B22256142461
theorem B3208223 : Blo 1688044 3208223 := bstep (se 1 (by rfl) ⟨2406167, by rfl⟩ : syracuseStep 3208223 = 4812335) B4812335
theorem B5699051 : Blo 1688044 5699051 := bstep (se 1 (by rfl) ⟨4274288, by rfl⟩ : syracuseStep 5699051 = 8548577) B8548577
theorem B13358591 : Blo 1688044 13358591 := bstep (se 1 (by rfl) ⟨10018943, by rfl⟩ : syracuseStep 13358591 = 20037887) B20037887
theorem B6412391 : Blo 1688044 6412391 := bstep (se 1 (by rfl) ⟨4809293, by rfl⟩ : syracuseStep 6412391 = 9618587) B9618587
theorem B32480027 : Blo 1688044 32480027 := bstep (se 1 (by rfl) ⟨24360020, by rfl⟩ : syracuseStep 32480027 = 48720041) B48720041
theorem B1899823 : Blo 1688044 1899823 := bstep (se 1 (by rfl) ⟨1424867, by rfl⟩ : syracuseStep 1899823 = 2849735) B2849735
theorem B3800681 : Blo 1688044 3800681 := bstep (se 2 (by rfl) ⟨1425255, by rfl⟩ : syracuseStep 3800681 = 2850511) B2850511
theorem B9891618871 : Blo 1688044 9891618871 := bstep (se 1 (by rfl) ⟨7418714153, by rfl⟩ : syracuseStep 9891618871 = 14837428307) B14837428307
theorem B2138815 : Blo 1688044 2138815 := bstep (se 1 (by rfl) ⟨1604111, by rfl⟩ : syracuseStep 2138815 = 3208223) B3208223
theorem B8905727 : Blo 1688044 8905727 := bstep (se 1 (by rfl) ⟨6679295, by rfl⟩ : syracuseStep 8905727 = 13358591) B13358591
theorem B2533097 : Blo 1688044 2533097 := bstep (se 2 (by rfl) ⟨949911, by rfl⟩ : syracuseStep 2533097 = 1899823) B1899823
theorem B21653351 : Blo 1688044 21653351 := bstep (se 1 (by rfl) ⟨16240013, by rfl⟩ : syracuseStep 21653351 = 32480027) B32480027
theorem B2533787 : Blo 1688044 2533787 := bstep (se 1 (by rfl) ⟨1900340, by rfl⟩ : syracuseStep 2533787 = 3800681) B3800681
theorem B4811879 : Blo 1688044 4811879 := bstep (se 1 (by rfl) ⟨3608909, by rfl⟩ : syracuseStep 4811879 = 7217819) B7217819
theorem B3207023 : Blo 1688044 3207023 := bstep (se 1 (by rfl) ⟨2405267, by rfl⟩ : syracuseStep 3207023 = 4810535) B4810535
theorem B5413031 : Blo 1688044 5413031 := bstep (se 1 (by rfl) ⟨4059773, by rfl⟩ : syracuseStep 5413031 = 8119547) B8119547
theorem B3799367 : Blo 1688044 3799367 := bstep (se 1 (by rfl) ⟨2849525, by rfl⟩ : syracuseStep 3799367 = 5699051) B5699051
theorem B4274927 : Blo 1688044 4274927 := bstep (se 1 (by rfl) ⟨3206195, by rfl⟩ : syracuseStep 4274927 = 6412391) B6412391
theorem B13188825161 : Blo 1688044 13188825161 := bstep (se 2 (by rfl) ⟨4945809435, by rfl⟩ : syracuseStep 13188825161 = 9891618871) B9891618871
theorem B2851753 : Blo 1688044 2851753 := bstep (se 2 (by rfl) ⟨1069407, by rfl⟩ : syracuseStep 2851753 = 2138815) B2138815
theorem B1688731 : Blo 1688044 1688731 := bstep (se 1 (by rfl) ⟨1266548, by rfl⟩ : syracuseStep 1688731 = 2533097) B2533097
theorem B14435567 : Blo 1688044 14435567 := bstep (se 1 (by rfl) ⟨10826675, by rfl⟩ : syracuseStep 14435567 = 21653351) B21653351
theorem B2532911 : Blo 1688044 2532911 := bstep (se 1 (by rfl) ⟨1899683, by rfl⟩ : syracuseStep 2532911 = 3799367) B3799367
theorem B1689191 : Blo 1688044 1689191 := bstep (se 1 (by rfl) ⟨1266893, by rfl⟩ : syracuseStep 1689191 = 2533787) B2533787
theorem B3608687 : Blo 1688044 3608687 := bstep (se 1 (by rfl) ⟨2706515, by rfl⟩ : syracuseStep 3608687 = 5413031) B5413031
theorem B3207919 : Blo 1688044 3207919 := bstep (se 1 (by rfl) ⟨2405939, by rfl⟩ : syracuseStep 3207919 = 4811879) B4811879
theorem B5937151 : Blo 1688044 5937151 := bstep (se 1 (by rfl) ⟨4452863, by rfl⟩ : syracuseStep 5937151 = 8905727) B8905727
theorem B2849951 : Blo 1688044 2849951 := bstep (se 1 (by rfl) ⟨2137463, by rfl⟩ : syracuseStep 2849951 = 4274927) B4274927
theorem B2138015 : Blo 1688044 2138015 := bstep (se 1 (by rfl) ⟨1603511, by rfl⟩ : syracuseStep 2138015 = 3207023) B3207023
theorem B4277225 : Blo 1688044 4277225 := bstep (se 2 (by rfl) ⟨1603959, by rfl⟩ : syracuseStep 4277225 = 3207919) B3207919
theorem B1688607 : Blo 1688044 1688607 := bstep (se 1 (by rfl) ⟨1266455, by rfl⟩ : syracuseStep 1688607 = 2532911) B2532911
theorem B3802337 : Blo 1688044 3802337 := bstep (se 2 (by rfl) ⟨1425876, by rfl⟩ : syracuseStep 3802337 = 2851753) B2851753
theorem B7916201 : Blo 1688044 7916201 := bstep (se 2 (by rfl) ⟨2968575, by rfl⟩ : syracuseStep 7916201 = 5937151) B5937151
theorem B8792550107 : Blo 1688044 8792550107 := bstep (se 1 (by rfl) ⟨6594412580, by rfl⟩ : syracuseStep 8792550107 = 13188825161) B13188825161
theorem B2405791 : Blo 1688044 2405791 := bstep (se 1 (by rfl) ⟨1804343, by rfl⟩ : syracuseStep 2405791 = 3608687) B3608687
theorem B9623711 : Blo 1688044 9623711 := bstep (se 1 (by rfl) ⟨7217783, by rfl⟩ : syracuseStep 9623711 = 14435567) B14435567
theorem B1899967 : Blo 1688044 1899967 := bstep (se 1 (by rfl) ⟨1424975, by rfl⟩ : syracuseStep 1899967 = 2849951) B2849951
theorem B5701373 : Blo 1688044 5701373 := bstep (se 3 (by rfl) ⟨1069007, by rfl⟩ : syracuseStep 5701373 = 2138015) B2138015
theorem B2851483 : Blo 1688044 2851483 := bstep (se 1 (by rfl) ⟨2138612, by rfl⟩ : syracuseStep 2851483 = 4277225) B4277225
theorem B6415807 : Blo 1688044 6415807 := bstep (se 1 (by rfl) ⟨4811855, by rfl⟩ : syracuseStep 6415807 = 9623711) B9623711
theorem B5277467 : Blo 1688044 5277467 := bstep (se 1 (by rfl) ⟨3958100, by rfl⟩ : syracuseStep 5277467 = 7916201) B7916201
theorem B2533289 : Blo 1688044 2533289 := bstep (se 2 (by rfl) ⟨949983, by rfl⟩ : syracuseStep 2533289 = 1899967) B1899967
theorem B12830885 : Blo 1688044 12830885 := bstep (se 4 (by rfl) ⟨1202895, by rfl⟩ : syracuseStep 12830885 = 2405791) B2405791
theorem B2534891 : Blo 1688044 2534891 := bstep (se 1 (by rfl) ⟨1901168, by rfl⟩ : syracuseStep 2534891 = 3802337) B3802337
theorem B5861700071 : Blo 1688044 5861700071 := bstep (se 1 (by rfl) ⟨4396275053, by rfl⟩ : syracuseStep 5861700071 = 8792550107) B8792550107
theorem B3800915 : Blo 1688044 3800915 := bstep (se 1 (by rfl) ⟨2850686, by rfl⟩ : syracuseStep 3800915 = 5701373) B5701373
theorem B3801977 : Blo 1688044 3801977 := bstep (se 2 (by rfl) ⟨1425741, by rfl⟩ : syracuseStep 3801977 = 2851483) B2851483
theorem B1688859 : Blo 1688044 1688859 := bstep (se 1 (by rfl) ⟨1266644, by rfl⟩ : syracuseStep 1688859 = 2533289) B2533289
theorem B8553923 : Blo 1688044 8553923 := bstep (se 1 (by rfl) ⟨6415442, by rfl⟩ : syracuseStep 8553923 = 12830885) B12830885
theorem B8554409 : Blo 1688044 8554409 := bstep (se 2 (by rfl) ⟨3207903, by rfl⟩ : syracuseStep 8554409 = 6415807) B6415807
theorem B1689927 : Blo 1688044 1689927 := bstep (se 1 (by rfl) ⟨1267445, by rfl⟩ : syracuseStep 1689927 = 2534891) B2534891
theorem B2533943 : Blo 1688044 2533943 := bstep (se 1 (by rfl) ⟨1900457, by rfl⟩ : syracuseStep 2533943 = 3800915) B3800915
theorem B3907800047 : Blo 1688044 3907800047 := bstep (se 1 (by rfl) ⟨2930850035, by rfl⟩ : syracuseStep 3907800047 = 5861700071) B5861700071
theorem B3518311 : Blo 1688044 3518311 := bstep (se 1 (by rfl) ⟨2638733, by rfl⟩ : syracuseStep 3518311 = 5277467) B5277467
theorem B5702615 : Blo 1688044 5702615 := bstep (se 1 (by rfl) ⟨4276961, by rfl⟩ : syracuseStep 5702615 = 8553923) B8553923
theorem B5702939 : Blo 1688044 5702939 := bstep (se 1 (by rfl) ⟨4277204, by rfl⟩ : syracuseStep 5702939 = 8554409) B8554409
theorem B1689295 : Blo 1688044 1689295 := bstep (se 1 (by rfl) ⟨1266971, by rfl⟩ : syracuseStep 1689295 = 2533943) B2533943
theorem B2534651 : Blo 1688044 2534651 := bstep (se 1 (by rfl) ⟨1900988, by rfl⟩ : syracuseStep 2534651 = 3801977) B3801977
theorem B2605200031 : Blo 1688044 2605200031 := bstep (se 1 (by rfl) ⟨1953900023, by rfl⟩ : syracuseStep 2605200031 = 3907800047) B3907800047
theorem B4691081 : Blo 1688044 4691081 := bstep (se 2 (by rfl) ⟨1759155, by rfl⟩ : syracuseStep 4691081 = 3518311) B3518311
theorem B12509549 : Blo 1688044 12509549 := bstep (se 3 (by rfl) ⟨2345540, by rfl⟩ : syracuseStep 12509549 = 4691081) B4691081
theorem B3801743 : Blo 1688044 3801743 := bstep (se 1 (by rfl) ⟨2851307, by rfl⟩ : syracuseStep 3801743 = 5702615) B5702615
theorem B3801959 : Blo 1688044 3801959 := bstep (se 1 (by rfl) ⟨2851469, by rfl⟩ : syracuseStep 3801959 = 5702939) B5702939
theorem B1689767 : Blo 1688044 1689767 := bstep (se 1 (by rfl) ⟨1267325, by rfl⟩ : syracuseStep 1689767 = 2534651) B2534651
theorem B3473600041 : Blo 1688044 3473600041 := bstep (se 2 (by rfl) ⟨1302600015, by rfl⟩ : syracuseStep 3473600041 = 2605200031) B2605200031
theorem B8339699 : Blo 1688044 8339699 := bstep (se 1 (by rfl) ⟨6254774, by rfl⟩ : syracuseStep 8339699 = 12509549) B12509549
theorem B2534495 : Blo 1688044 2534495 := bstep (se 1 (by rfl) ⟨1900871, by rfl⟩ : syracuseStep 2534495 = 3801743) B3801743
theorem B2534639 : Blo 1688044 2534639 := bstep (se 1 (by rfl) ⟨1900979, by rfl⟩ : syracuseStep 2534639 = 3801959) B3801959
theorem B4631466721 : Blo 1688044 4631466721 := bstep (se 2 (by rfl) ⟨1736800020, by rfl⟩ : syracuseStep 4631466721 = 3473600041) B3473600041
theorem B1689663 : Blo 1688044 1689663 := bstep (se 1 (by rfl) ⟨1267247, by rfl⟩ : syracuseStep 1689663 = 2534495) B2534495
theorem B1689759 : Blo 1688044 1689759 := bstep (se 1 (by rfl) ⟨1267319, by rfl⟩ : syracuseStep 1689759 = 2534639) B2534639
theorem B6175288961 : Blo 1688044 6175288961 := bstep (se 2 (by rfl) ⟨2315733360, by rfl⟩ : syracuseStep 6175288961 = 4631466721) B4631466721
theorem B5559799 : Blo 1688044 5559799 := bstep (se 1 (by rfl) ⟨4169849, by rfl⟩ : syracuseStep 5559799 = 8339699) B8339699
theorem B4116859307 : Blo 1688044 4116859307 := bstep (se 1 (by rfl) ⟨3087644480, by rfl⟩ : syracuseStep 4116859307 = 6175288961) B6175288961
theorem B7413065 : Blo 1688044 7413065 := bstep (se 2 (by rfl) ⟨2779899, by rfl⟩ : syracuseStep 7413065 = 5559799) B5559799
theorem B4942043 : Blo 1688044 4942043 := bstep (se 1 (by rfl) ⟨3706532, by rfl⟩ : syracuseStep 4942043 = 7413065) B7413065
theorem B2744572871 : Blo 1688044 2744572871 := bstep (se 1 (by rfl) ⟨2058429653, by rfl⟩ : syracuseStep 2744572871 = 4116859307) B4116859307
theorem B3294695 : Blo 1688044 3294695 := bstep (se 1 (by rfl) ⟨2471021, by rfl⟩ : syracuseStep 3294695 = 4942043) B4942043
theorem B1829715247 : Blo 1688044 1829715247 := bstep (se 1 (by rfl) ⟨1372286435, by rfl⟩ : syracuseStep 1829715247 = 2744572871) B2744572871
theorem B2196463 : Blo 1688044 2196463 := bstep (se 1 (by rfl) ⟨1647347, by rfl⟩ : syracuseStep 2196463 = 3294695) B3294695
theorem B2439620329 : Blo 1688044 2439620329 := bstep (se 2 (by rfl) ⟨914857623, by rfl⟩ : syracuseStep 2439620329 = 1829715247) B1829715247
theorem B2928617 : Blo 1688044 2928617 := bstep (se 2 (by rfl) ⟨1098231, by rfl⟩ : syracuseStep 2928617 = 2196463) B2196463
theorem B3252827105 : Blo 1688044 3252827105 := bstep (se 2 (by rfl) ⟨1219810164, by rfl⟩ : syracuseStep 3252827105 = 2439620329) B2439620329
theorem B1952411 : Blo 1688044 1952411 := bstep (se 1 (by rfl) ⟨1464308, by rfl⟩ : syracuseStep 1952411 = 2928617) B2928617
theorem B2168551403 : Blo 1688044 2168551403 := bstep (se 1 (by rfl) ⟨1626413552, by rfl⟩ : syracuseStep 2168551403 = 3252827105) B3252827105
theorem B1445700935 : Blo 1688044 1445700935 := bstep (se 1 (by rfl) ⟨1084275701, by rfl⟩ : syracuseStep 1445700935 = 2168551403) B2168551403
theorem B5206429 : Blo 1688044 5206429 := bstep (se 3 (by rfl) ⟨976205, by rfl⟩ : syracuseStep 5206429 = 1952411) B1952411
theorem B6941905 : Blo 1688044 6941905 := bstep (se 2 (by rfl) ⟨2603214, by rfl⟩ : syracuseStep 6941905 = 5206429) B5206429
theorem B963800623 : Blo 1688044 963800623 := bstep (se 1 (by rfl) ⟨722850467, by rfl⟩ : syracuseStep 963800623 = 1445700935) B1445700935
theorem B5140269989 : Blo 1688044 5140269989 := bstep (se 4 (by rfl) ⟨481900311, by rfl⟩ : syracuseStep 5140269989 = 963800623) B963800623
theorem B37023493 : Blo 1688044 37023493 := bstep (se 4 (by rfl) ⟨3470952, by rfl⟩ : syracuseStep 37023493 = 6941905) B6941905
theorem B3426846659 : Blo 1688044 3426846659 := bstep (se 1 (by rfl) ⟨2570134994, by rfl⟩ : syracuseStep 3426846659 = 5140269989) B5140269989
theorem B49364657 : Blo 1688044 49364657 := bstep (se 2 (by rfl) ⟨18511746, by rfl⟩ : syracuseStep 49364657 = 37023493) B37023493
theorem B32909771 : Blo 1688044 32909771 := bstep (se 1 (by rfl) ⟨24682328, by rfl⟩ : syracuseStep 32909771 = 49364657) B49364657
theorem B2284564439 : Blo 1688044 2284564439 := bstep (se 1 (by rfl) ⟨1713423329, by rfl⟩ : syracuseStep 2284564439 = 3426846659) B3426846659
theorem B1523042959 : Blo 1688044 1523042959 := bstep (se 1 (by rfl) ⟨1142282219, by rfl⟩ : syracuseStep 1523042959 = 2284564439) B2284564439
theorem B87759389 : Blo 1688044 87759389 := bstep (se 3 (by rfl) ⟨16454885, by rfl⟩ : syracuseStep 87759389 = 32909771) B32909771
theorem B2030723945 : Blo 1688044 2030723945 := bstep (se 2 (by rfl) ⟨761521479, by rfl⟩ : syracuseStep 2030723945 = 1523042959) B1523042959
theorem B58506259 : Blo 1688044 58506259 := bstep (se 1 (by rfl) ⟨43879694, by rfl⟩ : syracuseStep 58506259 = 87759389) B87759389
theorem B78008345 : Blo 1688044 78008345 := bstep (se 2 (by rfl) ⟨29253129, by rfl⟩ : syracuseStep 78008345 = 58506259) B58506259
theorem B1353815963 : Blo 1688044 1353815963 := bstep (se 1 (by rfl) ⟨1015361972, by rfl⟩ : syracuseStep 1353815963 = 2030723945) B2030723945
theorem B52005563 : Blo 1688044 52005563 := bstep (se 1 (by rfl) ⟨39004172, by rfl⟩ : syracuseStep 52005563 = 78008345) B78008345
theorem B902543975 : Blo 1688044 902543975 := bstep (se 1 (by rfl) ⟨676907981, by rfl⟩ : syracuseStep 902543975 = 1353815963) B1353815963
theorem B601695983 : Blo 1688044 601695983 := bstep (se 1 (by rfl) ⟨451271987, by rfl⟩ : syracuseStep 601695983 = 902543975) B902543975
theorem B34670375 : Blo 1688044 34670375 := bstep (se 1 (by rfl) ⟨26002781, by rfl⟩ : syracuseStep 34670375 = 52005563) B52005563
theorem B23113583 : Blo 1688044 23113583 := bstep (se 1 (by rfl) ⟨17335187, by rfl⟩ : syracuseStep 23113583 = 34670375) B34670375
theorem B1604522621 : Blo 1688044 1604522621 := bstep (se 3 (by rfl) ⟨300847991, by rfl⟩ : syracuseStep 1604522621 = 601695983) B601695983
theorem B4278726989 : Blo 1688044 4278726989 := bstep (se 3 (by rfl) ⟨802261310, by rfl⟩ : syracuseStep 4278726989 = 1604522621) B1604522621
theorem B15409055 : Blo 1688044 15409055 := bstep (se 1 (by rfl) ⟨11556791, by rfl⟩ : syracuseStep 15409055 = 23113583) B23113583
theorem B2852484659 : Blo 1688044 2852484659 := bstep (se 1 (by rfl) ⟨2139363494, by rfl⟩ : syracuseStep 2852484659 = 4278726989) B4278726989
theorem B10272703 : Blo 1688044 10272703 := bstep (se 1 (by rfl) ⟨7704527, by rfl⟩ : syracuseStep 10272703 = 15409055) B15409055
theorem B1901656439 : Blo 1688044 1901656439 := bstep (se 1 (by rfl) ⟨1426242329, by rfl⟩ : syracuseStep 1901656439 = 2852484659) B2852484659
theorem B13696937 : Blo 1688044 13696937 := bstep (se 2 (by rfl) ⟨5136351, by rfl⟩ : syracuseStep 13696937 = 10272703) B10272703
theorem B1267770959 : Blo 1688044 1267770959 := bstep (se 1 (by rfl) ⟨950828219, by rfl⟩ : syracuseStep 1267770959 = 1901656439) B1901656439
theorem B9131291 : Blo 1688044 9131291 := bstep (se 1 (by rfl) ⟨6848468, by rfl⟩ : syracuseStep 9131291 = 13696937) B13696937
theorem B6087527 : Blo 1688044 6087527 := bstep (se 1 (by rfl) ⟨4565645, by rfl⟩ : syracuseStep 6087527 = 9131291) B9131291
theorem B845180639 : Blo 1688044 845180639 := bstep (se 1 (by rfl) ⟨633885479, by rfl⟩ : syracuseStep 845180639 = 1267770959) B1267770959
theorem B4058351 : Blo 1688044 4058351 := bstep (se 1 (by rfl) ⟨3043763, by rfl⟩ : syracuseStep 4058351 = 6087527) B6087527
theorem B563453759 : Blo 1688044 563453759 := bstep (se 1 (by rfl) ⟨422590319, by rfl⟩ : syracuseStep 563453759 = 845180639) B845180639
theorem B2705567 : Blo 1688044 2705567 := bstep (se 1 (by rfl) ⟨2029175, by rfl⟩ : syracuseStep 2705567 = 4058351) B4058351
theorem B1502543357 : Blo 1688044 1502543357 := bstep (se 3 (by rfl) ⟨281726879, by rfl⟩ : syracuseStep 1502543357 = 563453759) B563453759
theorem B1001695571 : Blo 1688044 1001695571 := bstep (se 1 (by rfl) ⟨751271678, by rfl⟩ : syracuseStep 1001695571 = 1502543357) B1502543357
theorem B7214845 : Blo 1688044 7214845 := bstep (se 3 (by rfl) ⟨1352783, by rfl⟩ : syracuseStep 7214845 = 2705567) B2705567
theorem B667797047 : Blo 1688044 667797047 := bstep (se 1 (by rfl) ⟨500847785, by rfl⟩ : syracuseStep 667797047 = 1001695571) B1001695571
theorem B9619793 : Blo 1688044 9619793 := bstep (se 2 (by rfl) ⟨3607422, by rfl⟩ : syracuseStep 9619793 = 7214845) B7214845
theorem B445198031 : Blo 1688044 445198031 := bstep (se 1 (by rfl) ⟨333898523, by rfl⟩ : syracuseStep 445198031 = 667797047) B667797047
theorem B6413195 : Blo 1688044 6413195 := bstep (se 1 (by rfl) ⟨4809896, by rfl⟩ : syracuseStep 6413195 = 9619793) B9619793
theorem B296798687 : Blo 1688044 296798687 := bstep (se 1 (by rfl) ⟨222599015, by rfl⟩ : syracuseStep 296798687 = 445198031) B445198031
theorem B4275463 : Blo 1688044 4275463 := bstep (se 1 (by rfl) ⟨3206597, by rfl⟩ : syracuseStep 4275463 = 6413195) B6413195
theorem B197865791 : Blo 1688044 197865791 := bstep (se 1 (by rfl) ⟨148399343, by rfl⟩ : syracuseStep 197865791 = 296798687) B296798687
theorem B5700617 : Blo 1688044 5700617 := bstep (se 2 (by rfl) ⟨2137731, by rfl⟩ : syracuseStep 5700617 = 4275463) B4275463
theorem B131910527 : Blo 1688044 131910527 := bstep (se 1 (by rfl) ⟨98932895, by rfl⟩ : syracuseStep 131910527 = 197865791) B197865791
theorem B3800411 : Blo 1688044 3800411 := bstep (se 1 (by rfl) ⟨2850308, by rfl⟩ : syracuseStep 3800411 = 5700617) B5700617
theorem B2533607 : Blo 1688044 2533607 := bstep (se 1 (by rfl) ⟨1900205, by rfl⟩ : syracuseStep 2533607 = 3800411) B3800411
theorem B87940351 : Blo 1688044 87940351 := bstep (se 1 (by rfl) ⟨65955263, by rfl⟩ : syracuseStep 87940351 = 131910527) B131910527
theorem B1689071 : Blo 1688044 1689071 := bstep (se 1 (by rfl) ⟨1266803, by rfl⟩ : syracuseStep 1689071 = 2533607) B2533607
theorem B117253801 : Blo 1688044 117253801 := bstep (se 2 (by rfl) ⟨43970175, by rfl⟩ : syracuseStep 117253801 = 87940351) B87940351
theorem B625353605 : Blo 1688044 625353605 := bstep (se 4 (by rfl) ⟨58626900, by rfl⟩ : syracuseStep 625353605 = 117253801) B117253801
theorem B416902403 : Blo 1688044 416902403 := bstep (se 1 (by rfl) ⟨312676802, by rfl⟩ : syracuseStep 416902403 = 625353605) B625353605
theorem B1111739741 : Blo 1688044 1111739741 := bstep (se 3 (by rfl) ⟨208451201, by rfl⟩ : syracuseStep 1111739741 = 416902403) B416902403
theorem B741159827 : Blo 1688044 741159827 := bstep (se 1 (by rfl) ⟨555869870, by rfl⟩ : syracuseStep 741159827 = 1111739741) B1111739741
theorem B494106551 : Blo 1688044 494106551 := bstep (se 1 (by rfl) ⟨370579913, by rfl⟩ : syracuseStep 494106551 = 741159827) B741159827
theorem B329404367 : Blo 1688044 329404367 := bstep (se 1 (by rfl) ⟨247053275, by rfl⟩ : syracuseStep 329404367 = 494106551) B494106551
theorem B219602911 : Blo 1688044 219602911 := bstep (se 1 (by rfl) ⟨164702183, by rfl⟩ : syracuseStep 219602911 = 329404367) B329404367
theorem B292803881 : Blo 1688044 292803881 := bstep (se 2 (by rfl) ⟨109801455, by rfl⟩ : syracuseStep 292803881 = 219602911) B219602911
theorem B780810349 : Blo 1688044 780810349 := bstep (se 3 (by rfl) ⟨146401940, by rfl⟩ : syracuseStep 780810349 = 292803881) B292803881
theorem B1041080465 : Blo 1688044 1041080465 := bstep (se 2 (by rfl) ⟨390405174, by rfl⟩ : syracuseStep 1041080465 = 780810349) B780810349
theorem B694053643 : Blo 1688044 694053643 := bstep (se 1 (by rfl) ⟨520540232, by rfl⟩ : syracuseStep 694053643 = 1041080465) B1041080465
theorem B925404857 : Blo 1688044 925404857 := bstep (se 2 (by rfl) ⟨347026821, by rfl⟩ : syracuseStep 925404857 = 694053643) B694053643
theorem B616936571 : Blo 1688044 616936571 := bstep (se 1 (by rfl) ⟨462702428, by rfl⟩ : syracuseStep 616936571 = 925404857) B925404857
theorem B411291047 : Blo 1688044 411291047 := bstep (se 1 (by rfl) ⟨308468285, by rfl⟩ : syracuseStep 411291047 = 616936571) B616936571
theorem B1096776125 : Blo 1688044 1096776125 := bstep (se 3 (by rfl) ⟨205645523, by rfl⟩ : syracuseStep 1096776125 = 411291047) B411291047
theorem B731184083 : Blo 1688044 731184083 := bstep (se 1 (by rfl) ⟨548388062, by rfl⟩ : syracuseStep 731184083 = 1096776125) B1096776125
theorem B487456055 : Blo 1688044 487456055 := bstep (se 1 (by rfl) ⟨365592041, by rfl⟩ : syracuseStep 487456055 = 731184083) B731184083
theorem B324970703 : Blo 1688044 324970703 := bstep (se 1 (by rfl) ⟨243728027, by rfl⟩ : syracuseStep 324970703 = 487456055) B487456055
theorem B216647135 : Blo 1688044 216647135 := bstep (se 1 (by rfl) ⟨162485351, by rfl⟩ : syracuseStep 216647135 = 324970703) B324970703
theorem B144431423 : Blo 1688044 144431423 := bstep (se 1 (by rfl) ⟨108323567, by rfl⟩ : syracuseStep 144431423 = 216647135) B216647135
theorem B96287615 : Blo 1688044 96287615 := bstep (se 1 (by rfl) ⟨72215711, by rfl⟩ : syracuseStep 96287615 = 144431423) B144431423
theorem B64191743 : Blo 1688044 64191743 := bstep (se 1 (by rfl) ⟨48143807, by rfl⟩ : syracuseStep 64191743 = 96287615) B96287615
theorem B42794495 : Blo 1688044 42794495 := bstep (se 1 (by rfl) ⟨32095871, by rfl⟩ : syracuseStep 42794495 = 64191743) B64191743
theorem B28529663 : Blo 1688044 28529663 := bstep (se 1 (by rfl) ⟨21397247, by rfl⟩ : syracuseStep 28529663 = 42794495) B42794495
theorem B76079101 : Blo 1688044 76079101 := bstep (se 3 (by rfl) ⟨14264831, by rfl⟩ : syracuseStep 76079101 = 28529663) B28529663
theorem B101438801 : Blo 1688044 101438801 := bstep (se 2 (by rfl) ⟨38039550, by rfl⟩ : syracuseStep 101438801 = 76079101) B76079101
theorem B67625867 : Blo 1688044 67625867 := bstep (se 1 (by rfl) ⟨50719400, by rfl⟩ : syracuseStep 67625867 = 101438801) B101438801
theorem B180335645 : Blo 1688044 180335645 := bstep (se 3 (by rfl) ⟨33812933, by rfl⟩ : syracuseStep 180335645 = 67625867) B67625867
theorem B120223763 : Blo 1688044 120223763 := bstep (se 1 (by rfl) ⟨90167822, by rfl⟩ : syracuseStep 120223763 = 180335645) B180335645
theorem B80149175 : Blo 1688044 80149175 := bstep (se 1 (by rfl) ⟨60111881, by rfl⟩ : syracuseStep 80149175 = 120223763) B120223763
theorem B53432783 : Blo 1688044 53432783 := bstep (se 1 (by rfl) ⟨40074587, by rfl⟩ : syracuseStep 53432783 = 80149175) B80149175
theorem B35621855 : Blo 1688044 35621855 := bstep (se 1 (by rfl) ⟨26716391, by rfl⟩ : syracuseStep 35621855 = 53432783) B53432783
theorem B23747903 : Blo 1688044 23747903 := bstep (se 1 (by rfl) ⟨17810927, by rfl⟩ : syracuseStep 23747903 = 35621855) B35621855
theorem B15831935 : Blo 1688044 15831935 := bstep (se 1 (by rfl) ⟨11873951, by rfl⟩ : syracuseStep 15831935 = 23747903) B23747903
theorem B10554623 : Blo 1688044 10554623 := bstep (se 1 (by rfl) ⟨7915967, by rfl⟩ : syracuseStep 10554623 = 15831935) B15831935
theorem B7036415 : Blo 1688044 7036415 := bstep (se 1 (by rfl) ⟨5277311, by rfl⟩ : syracuseStep 7036415 = 10554623) B10554623
theorem B4690943 : Blo 1688044 4690943 := bstep (se 1 (by rfl) ⟨3518207, by rfl⟩ : syracuseStep 4690943 = 7036415) B7036415
theorem B3127295 : Blo 1688044 3127295 := bstep (se 1 (by rfl) ⟨2345471, by rfl⟩ : syracuseStep 3127295 = 4690943) B4690943
theorem B8339453 : Blo 1688044 8339453 := bstep (se 3 (by rfl) ⟨1563647, by rfl⟩ : syracuseStep 8339453 = 3127295) B3127295
theorem B5559635 : Blo 1688044 5559635 := bstep (se 1 (by rfl) ⟨4169726, by rfl⟩ : syracuseStep 5559635 = 8339453) B8339453
theorem B14825693 : Blo 1688044 14825693 := bstep (se 3 (by rfl) ⟨2779817, by rfl⟩ : syracuseStep 14825693 = 5559635) B5559635
theorem B39535181 : Blo 1688044 39535181 := bstep (se 3 (by rfl) ⟨7412846, by rfl⟩ : syracuseStep 39535181 = 14825693) B14825693
theorem B26356787 : Blo 1688044 26356787 := bstep (se 1 (by rfl) ⟨19767590, by rfl⟩ : syracuseStep 26356787 = 39535181) B39535181
theorem B17571191 : Blo 1688044 17571191 := bstep (se 1 (by rfl) ⟨13178393, by rfl⟩ : syracuseStep 17571191 = 26356787) B26356787
theorem B187426037 : Blo 1688044 187426037 := bstep (se 5 (by rfl) ⟨8785595, by rfl⟩ : syracuseStep 187426037 = 17571191) B17571191
theorem B124950691 : Blo 1688044 124950691 := bstep (se 1 (by rfl) ⟨93713018, by rfl⟩ : syracuseStep 124950691 = 187426037) B187426037
theorem B166600921 : Blo 1688044 166600921 := bstep (se 2 (by rfl) ⟨62475345, by rfl⟩ : syracuseStep 166600921 = 124950691) B124950691
theorem B222134561 : Blo 1688044 222134561 := bstep (se 2 (by rfl) ⟨83300460, by rfl⟩ : syracuseStep 222134561 = 166600921) B166600921
theorem B148089707 : Blo 1688044 148089707 := bstep (se 1 (by rfl) ⟨111067280, by rfl⟩ : syracuseStep 148089707 = 222134561) B222134561
theorem B98726471 : Blo 1688044 98726471 := bstep (se 1 (by rfl) ⟨74044853, by rfl⟩ : syracuseStep 98726471 = 148089707) B148089707
theorem B65817647 : Blo 1688044 65817647 := bstep (se 1 (by rfl) ⟨49363235, by rfl⟩ : syracuseStep 65817647 = 98726471) B98726471
theorem B43878431 : Blo 1688044 43878431 := bstep (se 1 (by rfl) ⟨32908823, by rfl⟩ : syracuseStep 43878431 = 65817647) B65817647
theorem B29252287 : Blo 1688044 29252287 := bstep (se 1 (by rfl) ⟨21939215, by rfl⟩ : syracuseStep 29252287 = 43878431) B43878431
theorem B39003049 : Blo 1688044 39003049 := bstep (se 2 (by rfl) ⟨14626143, by rfl⟩ : syracuseStep 39003049 = 29252287) B29252287
theorem B52004065 : Blo 1688044 52004065 := bstep (se 2 (by rfl) ⟨19501524, by rfl⟩ : syracuseStep 52004065 = 39003049) B39003049
theorem B69338753 : Blo 1688044 69338753 := bstep (se 2 (by rfl) ⟨26002032, by rfl⟩ : syracuseStep 69338753 = 52004065) B52004065
theorem B46225835 : Blo 1688044 46225835 := bstep (se 1 (by rfl) ⟨34669376, by rfl⟩ : syracuseStep 46225835 = 69338753) B69338753
theorem B30817223 : Blo 1688044 30817223 := bstep (se 1 (by rfl) ⟨23112917, by rfl⟩ : syracuseStep 30817223 = 46225835) B46225835
theorem B20544815 : Blo 1688044 20544815 := bstep (se 1 (by rfl) ⟨15408611, by rfl⟩ : syracuseStep 20544815 = 30817223) B30817223
theorem B13696543 : Blo 1688044 13696543 := bstep (se 1 (by rfl) ⟨10272407, by rfl⟩ : syracuseStep 13696543 = 20544815) B20544815
theorem B73048229 : Blo 1688044 73048229 := bstep (se 4 (by rfl) ⟨6848271, by rfl⟩ : syracuseStep 73048229 = 13696543) B13696543
theorem B48698819 : Blo 1688044 48698819 := bstep (se 1 (by rfl) ⟨36524114, by rfl⟩ : syracuseStep 48698819 = 73048229) B73048229
theorem B32465879 : Blo 1688044 32465879 := bstep (se 1 (by rfl) ⟨24349409, by rfl⟩ : syracuseStep 32465879 = 48698819) B48698819
theorem B21643919 : Blo 1688044 21643919 := bstep (se 1 (by rfl) ⟨16232939, by rfl⟩ : syracuseStep 21643919 = 32465879) B32465879
theorem B14429279 : Blo 1688044 14429279 := bstep (se 1 (by rfl) ⟨10821959, by rfl⟩ : syracuseStep 14429279 = 21643919) B21643919
theorem B9619519 : Blo 1688044 9619519 := bstep (se 1 (by rfl) ⟨7214639, by rfl⟩ : syracuseStep 9619519 = 14429279) B14429279
theorem B12826025 : Blo 1688044 12826025 := bstep (se 2 (by rfl) ⟨4809759, by rfl⟩ : syracuseStep 12826025 = 9619519) B9619519
theorem B8550683 : Blo 1688044 8550683 := bstep (se 1 (by rfl) ⟨6413012, by rfl⟩ : syracuseStep 8550683 = 12826025) B12826025
theorem B5700455 : Blo 1688044 5700455 := bstep (se 1 (by rfl) ⟨4275341, by rfl⟩ : syracuseStep 5700455 = 8550683) B8550683
theorem B3800303 : Blo 1688044 3800303 := bstep (se 1 (by rfl) ⟨2850227, by rfl⟩ : syracuseStep 3800303 = 5700455) B5700455
theorem B2533535 : Blo 1688044 2533535 := bstep (se 1 (by rfl) ⟨1900151, by rfl⟩ : syracuseStep 2533535 = 3800303) B3800303
theorem B1689023 : Blo 1688044 1689023 := bstep (se 1 (by rfl) ⟨1266767, by rfl⟩ : syracuseStep 1689023 = 2533535) B2533535

theorem C0 (j : ℕ) (h1 : 422011 ≤ j) (h2 : j ≤ 422510) : Blo 1688044 (4 * j + 3) := by
  interval_cases j
  · exact B1688047
  · exact B1688051
  · exact B1688055
  · exact B1688059
  · exact B1688063
  · exact B1688067
  · exact B1688071
  · exact B1688075
  · exact B1688079
  · exact B1688083
  · exact B1688087
  · exact B1688091
  · exact B1688095
  · exact B1688099
  · exact B1688103
  · exact B1688107
  · exact B1688111
  · exact B1688115
  · exact B1688119
  · exact B1688123
  · exact B1688127
  · exact B1688131
  · exact B1688135
  · exact B1688139
  · exact B1688143
  · exact B1688147
  · exact B1688151
  · exact B1688155
  · exact B1688159
  · exact B1688163
  · exact B1688167
  · exact B1688171
  · exact B1688175
  · exact B1688179
  · exact B1688183
  · exact B1688187
  · exact B1688191
  · exact B1688195
  · exact B1688199
  · exact B1688203
  · exact B1688207
  · exact B1688211
  · exact B1688215
  · exact B1688219
  · exact B1688223
  · exact B1688227
  · exact B1688231
  · exact B1688235
  · exact B1688239
  · exact B1688243
  · exact B1688247
  · exact B1688251
  · exact B1688255
  · exact B1688259
  · exact B1688263
  · exact B1688267
  · exact B1688271
  · exact B1688275
  · exact B1688279
  · exact B1688283
  · exact B1688287
  · exact B1688291
  · exact B1688295
  · exact B1688299
  · exact B1688303
  · exact B1688307
  · exact B1688311
  · exact B1688315
  · exact B1688319
  · exact B1688323
  · exact B1688327
  · exact B1688331
  · exact B1688335
  · exact B1688339
  · exact B1688343
  · exact B1688347
  · exact B1688351
  · exact B1688355
  · exact B1688359
  · exact B1688363
  · exact B1688367
  · exact B1688371
  · exact B1688375
  · exact B1688379
  · exact B1688383
  · exact B1688387
  · exact B1688391
  · exact B1688395
  · exact B1688399
  · exact B1688403
  · exact B1688407
  · exact B1688411
  · exact B1688415
  · exact B1688419
  · exact B1688423
  · exact B1688427
  · exact B1688431
  · exact B1688435
  · exact B1688439
  · exact B1688443
  · exact B1688447
  · exact B1688451
  · exact B1688455
  · exact B1688459
  · exact B1688463
  · exact B1688467
  · exact B1688471
  · exact B1688475
  · exact B1688479
  · exact B1688483
  · exact B1688487
  · exact B1688491
  · exact B1688495
  · exact B1688499
  · exact B1688503
  · exact B1688507
  · exact B1688511
  · exact B1688515
  · exact B1688519
  · exact B1688523
  · exact B1688527
  · exact B1688531
  · exact B1688535
  · exact B1688539
  · exact B1688543
  · exact B1688547
  · exact B1688551
  · exact B1688555
  · exact B1688559
  · exact B1688563
  · exact B1688567
  · exact B1688571
  · exact B1688575
  · exact B1688579
  · exact B1688583
  · exact B1688587
  · exact B1688591
  · exact B1688595
  · exact B1688599
  · exact B1688603
  · exact B1688607
  · exact B1688611
  · exact B1688615
  · exact B1688619
  · exact B1688623
  · exact B1688627
  · exact B1688631
  · exact B1688635
  · exact B1688639
  · exact B1688643
  · exact B1688647
  · exact B1688651
  · exact B1688655
  · exact B1688659
  · exact B1688663
  · exact B1688667
  · exact B1688671
  · exact B1688675
  · exact B1688679
  · exact B1688683
  · exact B1688687
  · exact B1688691
  · exact B1688695
  · exact B1688699
  · exact B1688703
  · exact B1688707
  · exact B1688711
  · exact B1688715
  · exact B1688719
  · exact B1688723
  · exact B1688727
  · exact B1688731
  · exact B1688735
  · exact B1688739
  · exact B1688743
  · exact B1688747
  · exact B1688751
  · exact B1688755
  · exact B1688759
  · exact B1688763
  · exact B1688767
  · exact B1688771
  · exact B1688775
  · exact B1688779
  · exact B1688783
  · exact B1688787
  · exact B1688791
  · exact B1688795
  · exact B1688799
  · exact B1688803
  · exact B1688807
  · exact B1688811
  · exact B1688815
  · exact B1688819
  · exact B1688823
  · exact B1688827
  · exact B1688831
  · exact B1688835
  · exact B1688839
  · exact B1688843
  · exact B1688847
  · exact B1688851
  · exact B1688855
  · exact B1688859
  · exact B1688863
  · exact B1688867
  · exact B1688871
  · exact B1688875
  · exact B1688879
  · exact B1688883
  · exact B1688887
  · exact B1688891
  · exact B1688895
  · exact B1688899
  · exact B1688903
  · exact B1688907
  · exact B1688911
  · exact B1688915
  · exact B1688919
  · exact B1688923
  · exact B1688927
  · exact B1688931
  · exact B1688935
  · exact B1688939
  · exact B1688943
  · exact B1688947
  · exact B1688951
  · exact B1688955
  · exact B1688959
  · exact B1688963
  · exact B1688967
  · exact B1688971
  · exact B1688975
  · exact B1688979
  · exact B1688983
  · exact B1688987
  · exact B1688991
  · exact B1688995
  · exact B1688999
  · exact B1689003
  · exact B1689007
  · exact B1689011
  · exact B1689015
  · exact B1689019
  · exact B1689023
  · exact B1689027
  · exact B1689031
  · exact B1689035
  · exact B1689039
  · exact B1689043
  · exact B1689047
  · exact B1689051
  · exact B1689055
  · exact B1689059
  · exact B1689063
  · exact B1689067
  · exact B1689071
  · exact B1689075
  · exact B1689079
  · exact B1689083
  · exact B1689087
  · exact B1689091
  · exact B1689095
  · exact B1689099
  · exact B1689103
  · exact B1689107
  · exact B1689111
  · exact B1689115
  · exact B1689119
  · exact B1689123
  · exact B1689127
  · exact B1689131
  · exact B1689135
  · exact B1689139
  · exact B1689143
  · exact B1689147
  · exact B1689151
  · exact B1689155
  · exact B1689159
  · exact B1689163
  · exact B1689167
  · exact B1689171
  · exact B1689175
  · exact B1689179
  · exact B1689183
  · exact B1689187
  · exact B1689191
  · exact B1689195
  · exact B1689199
  · exact B1689203
  · exact B1689207
  · exact B1689211
  · exact B1689215
  · exact B1689219
  · exact B1689223
  · exact B1689227
  · exact B1689231
  · exact B1689235
  · exact B1689239
  · exact B1689243
  · exact B1689247
  · exact B1689251
  · exact B1689255
  · exact B1689259
  · exact B1689263
  · exact B1689267
  · exact B1689271
  · exact B1689275
  · exact B1689279
  · exact B1689283
  · exact B1689287
  · exact B1689291
  · exact B1689295
  · exact B1689299
  · exact B1689303
  · exact B1689307
  · exact B1689311
  · exact B1689315
  · exact B1689319
  · exact B1689323
  · exact B1689327
  · exact B1689331
  · exact B1689335
  · exact B1689339
  · exact B1689343
  · exact B1689347
  · exact B1689351
  · exact B1689355
  · exact B1689359
  · exact B1689363
  · exact B1689367
  · exact B1689371
  · exact B1689375
  · exact B1689379
  · exact B1689383
  · exact B1689387
  · exact B1689391
  · exact B1689395
  · exact B1689399
  · exact B1689403
  · exact B1689407
  · exact B1689411
  · exact B1689415
  · exact B1689419
  · exact B1689423
  · exact B1689427
  · exact B1689431
  · exact B1689435
  · exact B1689439
  · exact B1689443
  · exact B1689447
  · exact B1689451
  · exact B1689455
  · exact B1689459
  · exact B1689463
  · exact B1689467
  · exact B1689471
  · exact B1689475
  · exact B1689479
  · exact B1689483
  · exact B1689487
  · exact B1689491
  · exact B1689495
  · exact B1689499
  · exact B1689503
  · exact B1689507
  · exact B1689511
  · exact B1689515
  · exact B1689519
  · exact B1689523
  · exact B1689527
  · exact B1689531
  · exact B1689535
  · exact B1689539
  · exact B1689543
  · exact B1689547
  · exact B1689551
  · exact B1689555
  · exact B1689559
  · exact B1689563
  · exact B1689567
  · exact B1689571
  · exact B1689575
  · exact B1689579
  · exact B1689583
  · exact B1689587
  · exact B1689591
  · exact B1689595
  · exact B1689599
  · exact B1689603
  · exact B1689607
  · exact B1689611
  · exact B1689615
  · exact B1689619
  · exact B1689623
  · exact B1689627
  · exact B1689631
  · exact B1689635
  · exact B1689639
  · exact B1689643
  · exact B1689647
  · exact B1689651
  · exact B1689655
  · exact B1689659
  · exact B1689663
  · exact B1689667
  · exact B1689671
  · exact B1689675
  · exact B1689679
  · exact B1689683
  · exact B1689687
  · exact B1689691
  · exact B1689695
  · exact B1689699
  · exact B1689703
  · exact B1689707
  · exact B1689711
  · exact B1689715
  · exact B1689719
  · exact B1689723
  · exact B1689727
  · exact B1689731
  · exact B1689735
  · exact B1689739
  · exact B1689743
  · exact B1689747
  · exact B1689751
  · exact B1689755
  · exact B1689759
  · exact B1689763
  · exact B1689767
  · exact B1689771
  · exact B1689775
  · exact B1689779
  · exact B1689783
  · exact B1689787
  · exact B1689791
  · exact B1689795
  · exact B1689799
  · exact B1689803
  · exact B1689807
  · exact B1689811
  · exact B1689815
  · exact B1689819
  · exact B1689823
  · exact B1689827
  · exact B1689831
  · exact B1689835
  · exact B1689839
  · exact B1689843
  · exact B1689847
  · exact B1689851
  · exact B1689855
  · exact B1689859
  · exact B1689863
  · exact B1689867
  · exact B1689871
  · exact B1689875
  · exact B1689879
  · exact B1689883
  · exact B1689887
  · exact B1689891
  · exact B1689895
  · exact B1689899
  · exact B1689903
  · exact B1689907
  · exact B1689911
  · exact B1689915
  · exact B1689919
  · exact B1689923
  · exact B1689927
  · exact B1689931
  · exact B1689935
  · exact B1689939
  · exact B1689943
  · exact B1689947
  · exact B1689951
  · exact B1689955
  · exact B1689959
  · exact B1689963
  · exact B1689967
  · exact B1689971
  · exact B1689975
  · exact B1689979
  · exact B1689983
  · exact B1689987
  · exact B1689991
  · exact B1689995
  · exact B1689999
  · exact B1690003
  · exact B1690007
  · exact B1690011
  · exact B1690015
  · exact B1690019
  · exact B1690023
  · exact B1690027
  · exact B1690031
  · exact B1690035
  · exact B1690039
  · exact B1690043

theorem solution (m : ℕ) (hlo : 1688044 ≤ m) (hhi : m ≤ 1690044) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 422011 ≤ j := by omega
    have hj2 : j ≤ 422510 := by omega
    have hb : Blo 1688044 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
